module

public import RequestProject.Beurling.Noise.KRNormFix
public import RequestProject.Beurling.Noise.LemSEuler

/-!
# Lemma 5.20 (`τ`-near energy): hypotheses and the localisation step

The standing hypotheses of the proof of Lemma 5.20 (`TNP.Hyp`):

* (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸`, and the paper's width hypotheses `PaperWidth`
  (`(RH)` with `ε ≤ 4·10⁻⁶`, `H` `θ`-Lipschitz with `θ ≤ 10⁻²`, `H(y) ≤ y/10` on `[X₀⁻/2, ∞)`);
* the decision order (§3, §5.1): `|t(p) - p| ≤ H(p)` for the primes `p ≥ X₀⁻/2`, and `t(p) = p`
  for the (rational) primes `p < X₀⁻/2`;
* `count` : **the local count of Corollary 6.3(ii)** in the form used in the "Counting" step of
  the paper's proof: for `p₀ ≥ X₀⁻/2`, the window `|p - p₀| ≤ 1.71 H(p₀)` holds at most
  `46 H(p₀)` primes of the system.

The localisation (`loc_real`, the paper's first paragraph): if `w = p m` is `τ`-near at `y`,
`p` the prime of `w` largest in decision order, `c = y/w ≥ X₀⁻`, then `p ≥ X₀⁻/2`,
`|p - p₀| ≤ 1.71 H(p₀)` with `p₀ = √(y/m) = √(cp) ≥ X₀⁻/2`, and every prime `q ∣ m` has
`q ≤ 1.5 p₀` (`smooth_real`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

/-- The hypotheses of the proof of Lemma 5.20 (see the module docstring). -/
structure Hyp (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m Z η1 η2 : ℝ)
    (ε1 : ℝ → ℝ) (ε θ : ℝ) : Prop where
  hbs : P.HBS X0m Z η1 η2 ε1
  hXm : 100000000 ≤ Real.log X0m
  width : PaperWidth H X0m ε θ
  dec_hi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j)
  dec_lo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j
  count : ∀ p0, X0m / 2 ≤ p0 →
    ((((P.primesLe (p0 + 1.71 * H p0)).filter
      (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0

/-! ## The real inequalities of the localisation -/

section real

variable {H : ℝ → ℝ} {X0m ε θ : ℝ}

/-- **Localisation** (Lemma 5.20, proof, first paragraph): from `|t - c| ≤ 2H(c)`, `c ≥ X₀⁻` and
the decision order at `p`, `p ≥ X₀⁻/2`, `p₀ = √(cp) ≥ X₀⁻/2`, `|p - p₀| ≤ 1.71 H(p₀)` and
`t ≤ 1.1 p`. -/
theorem loc_real (hP : PaperWidth H X0m ε θ) {p c t : ℝ} (hp : 0 < p) (hc : X0m ≤ c)
    (htc : |t - c| ≤ 2 * H c) (hhi : X0m / 2 ≤ p → |t - p| ≤ H p)
    (hlo : p < X0m / 2 → t = p) :
    X0m / 2 ≤ p ∧ X0m / 2 ≤ √(c * p) ∧ |p - √(c * p)| ≤ 1.71 * H (√(c * p)) ∧ t ≤ 1.1 * p := by
  have hX := hP.X0m_pos
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hcH := hP.small c (by linarith)
  have hHc0 := hP.reg.pos c
  -- `p ≥ X₀⁻/2`
  have hp2 : X0m / 2 ≤ p := by
    by_contra hcon
    push_neg at hcon
    have := hlo hcon
    rw [this] at htc
    have := (abs_le.mp htc).1
    linarith
  have hpH := hP.small p hp2
  have hHp0 := hP.reg.pos p
  have htp := hhi hp2
  -- `|p - c| ≤ 3.07 H(p)`
  have hlipc : H c ≤ H p + θ * |c - p| := by
    have := hP.lip c p (by linarith) hp2
    have := (abs_le.mp this).2
    linarith
  have hpc : |p - c| ≤ 3.07 * H p := by
    have h1 : |p - c| ≤ |t - p| + |t - c| := by
      calc |p - c| = |(t - c) - (t - p)| := by ring_nf
        _ ≤ |t - c| + |t - p| := abs_sub _ _
        _ = |t - p| + |t - c| := add_comm _ _
    have h2 : |c - p| = |p - c| := abs_sub_comm _ _
    have h3 : |p - c| ≤ 3 * H p + 2 * θ * |p - c| := by nlinarith
    have h4 : |p - c| * (1 - 2 * θ) ≤ 3 * H p := by nlinarith
    have h5 : 0.98 ≤ 1 - 2 * θ := by linarith
    have h6 : |p - c| * 0.98 ≤ 3 * H p := by
      have := abs_nonneg (p - c); nlinarith
    linarith
  -- `c ∈ [0.693p, 1.307p]`
  have hc1 : 0.693 * p ≤ c := by have := (abs_le.mp hpc).2; linarith
  have hc2 : c ≤ 1.307 * p := by have := (abs_le.mp hpc).1; linarith
  set p0 := √(c * p) with hp0
  have hcp : 0 < c * p := by nlinarith
  have hp0sq : p0 * p0 = c * p := Real.mul_self_sqrt hcp.le
  have hp00 : 0 < p0 := Real.sqrt_pos.mpr hcp
  -- `p₀ ≥ 0.832 p` and `p₀ ≥ X₀⁻/2`
  have hp0p : 0.832 * p ≤ p0 := by
    by_contra hcon; push_neg at hcon; nlinarith
  have hp0X : X0m / 2 ≤ p0 := by
    by_contra hcon; push_neg at hcon
    have : p0 * p0 < X0m / 2 * (X0m / 2) := by nlinarith
    nlinarith
  -- `|p - p₀| ≤ 1.676 H(p)`
  have hpp0 : |p - p0| ≤ 1.676 * H p := by
    have hprod : (p - p0) * (p + p0) = p * (p - c) := by nlinarith
    have habs : |p - p0| * (p + p0) = p * |p - c| := by
      rw [← abs_of_pos (show 0 < p + p0 by linarith), ← abs_mul, hprod, abs_mul,
        abs_of_pos hp]
    have : |p - p0| * (p + p0) ≤ p * (3.07 * H p) := by
      rw [habs]; exact mul_le_mul_of_nonneg_left hpc hp.le
    have h1 : |p - p0| * (1.832 * p) ≤ p * (3.07 * H p) := by
      have := abs_nonneg (p - p0)
      nlinarith
    have h2 : |p - p0| * 1.832 ≤ 3.07 * H p := by
      have := abs_nonneg (p - p0)
      nlinarith
    linarith
  -- `H(p) ≤ H(p₀) + θ |p - p₀|`
  have hlip0 : H p ≤ H p0 + θ * |p - p0| := by
    have := hP.lip p p0 hp2 hp0X
    have := (abs_le.mp this).2
    linarith
  refine ⟨hp2, hp0X, ?_, ?_⟩
  · have h1 : |p - p0| ≤ 1.676 * H p0 + 1.676 * θ * |p - p0| := by
      have := mul_le_mul_of_nonneg_left hlip0 (show (0 : ℝ) ≤ 1.676 by norm_num)
      linarith
    have h2 : |p - p0| * (1 - 1.676 * θ) ≤ 1.676 * H p0 := by linarith
    have h3 : 0.9832 ≤ 1 - 1.676 * θ := by linarith
    have hab := abs_nonneg (p - p0)
    have h4 : |p - p0| * 0.9832 ≤ |p - p0| * (1 - 1.676 * θ) :=
      mul_le_mul_of_nonneg_left h3 hab
    have hHp00 := hP.reg.pos p0
    linarith
  · have := (abs_le.mp htp).2
    linarith

/-- The cofactor primes: `t(q) ≤ t ≤ 1.1 p` and `p ≤ 1.171 p₀` give `q ≤ 1.5 p₀`. -/
theorem smooth_real (hP : PaperWidth H X0m ε θ) {q tq t p p0 : ℝ} (hq : 0 < q)
    (hqt : tq ≤ t) (ht : t ≤ 1.1 * p) (hpp0 : p ≤ 1.171 * p0) (hp0 : X0m / 2 ≤ p0)
    (hhi : X0m / 2 ≤ q → |tq - q| ≤ H q) : q ≤ 1.5 * p0 := by
  rcases lt_or_ge q (X0m / 2) with h | h
  · have := hP.X0m_pos; nlinarith
  · have h1 := (abs_le.mp (hhi h)).1
    have h2 := hP.small q h
    nlinarith

/-- In the window `|p - p₀| ≤ 1.71 H(p₀)`: `0.829 p₀ ≤ p ≤ 1.171 p₀`. -/
theorem window_bounds (hP : PaperWidth H X0m ε θ) {p p0 : ℝ} (hp0 : X0m / 2 ≤ p0)
    (hw : |p - p0| ≤ 1.71 * H p0) : 0.829 * p0 ≤ p ∧ p ≤ 1.171 * p0 := by
  have h := hP.small p0 hp0
  constructor <;> [have := (abs_le.mp hw).1; have := (abs_le.mp hw).2] <;> linarith

end real

end KR.TNP

end
