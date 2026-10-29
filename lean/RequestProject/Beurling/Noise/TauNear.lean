module

public import RequestProject.Beurling.Noise.KRTrueTerm

/-!
# Lemma 5.20 (`τ`-near energy): the statement used, and its numerical consequence

Lemma 5.20 bounds, on `Good(<x)`, the `τ`-near energies by `10⁴ H(X₀) log²X₀/X₀`, which for the
standard width `H(X₀) = e^{8(log Λ)²}`, `Λ = log X₀ ≥ 10⁸`, is `≤ e^{-0.99Λ}`; consequently
`λ₀ C_N E_η ≤ ½` (the hypothesis of Proposition 5.18).

* `energy_numeric` : `10⁴ Λ² e^{8(log Λ)² - Λ} ≤ e^{-0.99Λ}` for every `Λ ≥ 10⁸`;
* `energy_eq` : `10⁴ H(X₀) log²X₀/X₀ = 10⁴ Λ² e^{8(log Λ)² - Λ}`;
* `TauNearEnergy` : **Lemma 5.20** for `E_η` at the scales of Proposition 5.18, as a named
  hypothesis: scale bounds `s_v ≥ η̃` on `[v, 2v)` with `∑_v log(2v) s_v ≤ 10⁴ H(X₀) log²X₀/X₀`
  (its proof needs Corollary 6.3(ii) (local counts of the realised primes), Lemma 5.1 and
  Lemma 5.3 for the cofactors, which the paper applies on `Good(<x)`);
* `hE_of_energy` : the consequence `λ₀ C_N E_η ≤ ½` for `λ₀ ≤ 2`, `0 ≤ C_N ≤ 158`.
-/

@[expose] public section

open Finset Real

namespace KR

/-- `x² ≤ 8! eˣ/x⁶`-type bound: `x⁸ ≤ 8! eˣ` for `x ≥ 0`. -/
lemma pow_eight_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 8 / 40320 ≤ Real.exp x := by
  have := Real.pow_div_factorial_le_exp (x := x) hx 8
  norm_num [Nat.factorial] at this
  linarith

/-- **The numerics of Lemma 5.20**: `10⁴ Λ² e^{8(log Λ)² - Λ} ≤ e^{-0.99Λ}` for `Λ ≥ 10⁸`. -/
theorem energy_numeric {Λ : ℝ} (hΛ : 100000000 ≤ Λ) :
    10000 * Λ ^ 2 * Real.exp (8 * Real.log Λ ^ 2 - Λ) ≤ Real.exp (-(0.99 * Λ)) := by
  have hΛ0 : 0 < Λ := by linarith
  set L := Real.log Λ
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hΛL : Λ = Real.exp L := (Real.exp_log hΛ0).symm
  -- it suffices: `log 10⁴ + 2L + 8L² ≤ 0.01 Λ`
  have key : 9.3 + 2 * L + 8 * L ^ 2 ≤ 0.01 * Λ := by
    rcases le_or_gt L 18.5 with h | h
    · nlinarith
    · have h8 := pow_eight_le_exp hL0
      rw [← hΛL] at h8
      have hL6 : (18.5 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) h.le 6
      nlinarith [sq_nonneg L, pow_pos (show (0 : ℝ) < L by linarith) 2]
  have h10 : Real.log 10000 ≤ 9.3 := by
    have : (10000 : ℝ) ≤ Real.exp 9.3 := by
      have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := (Real.exp_one_gt_d9).le
      have h9 : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he 9
      have h03 : (1.3 : ℝ) ≤ Real.exp 0.3 := by linarith [Real.add_one_le_exp (0.3 : ℝ)]
      have e : Real.exp 9.3 = Real.exp 1 ^ 9 * Real.exp 0.3 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      nlinarith [Real.exp_pos 1, pow_pos (Real.exp_pos 1) 9]
    calc Real.log 10000 ≤ Real.log (Real.exp 9.3) := Real.log_le_log (by norm_num) this
      _ = 9.3 := Real.log_exp _
  have hlhs : Real.exp (Real.log 10000 + 2 * L + 8 * L ^ 2 - Λ) =
      10000 * Λ ^ 2 * Real.exp (8 * L ^ 2 - Λ) := by
    rw [show Real.log 10000 + 2 * L + 8 * L ^ 2 - Λ =
        Real.log 10000 + L + L + (8 * L ^ 2 - Λ) by ring, Real.exp_add, Real.exp_add,
      Real.exp_add, Real.exp_log (by norm_num), ← hΛL]
    ring
  rw [← hlhs]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `10⁴ H(X₀) log²X₀/X₀ = 10⁴ Λ² e^{8(log Λ)² - Λ}` for `H(X₀) = e^{8(log log X₀)²}`. -/
lemma energy_eq {H : ℝ → ℝ} {X0 : ℝ} (hX0 : 0 < X0)
    (hH : H X0 = Real.exp (8 * Real.log (Real.log X0) ^ 2)) :
    10000 * H X0 * Real.log X0 ^ 2 / X0 =
      10000 * Real.log X0 ^ 2 * Real.exp (8 * Real.log (Real.log X0) ^ 2 - Real.log X0) := by
  rw [hH, Real.exp_sub, Real.exp_log hX0]
  field_simp

variable (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m : ℝ)

/-- **Lemma 5.20 (`τ`-near energy)**, the bound on `E_η` used in Proposition 5.18, at the scales
`Sc`: there are scale bounds `s_v ≥ η̃` on `[v, 2v)` with
`E_η = ∑_v log(2v) s_v ≤ 10⁴ H(X₀) log²X₀/X₀`. -/
def TauNearEnergy (X0 : ℝ) (Sc : Finset ℝ) (s : ℝ → ℝ) : Prop :=
  EtaBound P H tw X0m Sc s ∧
    ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 10000 * H X0 * Real.log X0 ^ 2 / X0

variable {P H tw X0m}

/-- **Consequence of Lemma 5.20**: `λ₀ C_N E_η ≤ ½` (for `Λ = log X₀ ≥ 10⁸`,
`H(X₀) = e^{8(log Λ)²}`, `0 ≤ λ₀ ≤ 2`, `0 ≤ C_N ≤ 158`). -/
theorem hE_of_energy {X0 lam0 CN : ℝ} {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hT : TauNearEnergy P H tw X0m X0 Sc s) (hΛ : 100000000 ≤ Real.log X0) (hX0 : 0 < X0)
    (hH : H X0 = Real.exp (8 * Real.log (Real.log X0) ^ 2)) (hlam0 : 0 ≤ lam0)
    (hlam : lam0 ≤ 2) (hCN0 : 0 ≤ CN) (hCN : CN ≤ 158) :
    lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2 := by
  have h1 := hT.2
  rw [energy_eq hX0 hH] at h1
  have h2 := energy_numeric hΛ
  have h3 : Real.exp (-(0.99 * Real.log X0)) ≤ 1 / 1000 := by
    have := Real.add_one_le_exp (0.99 * Real.log X0)
    rw [Real.exp_neg, inv_eq_one_div]
    rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    nlinarith
  have hE := h1.trans (h2.trans h3)
  have hE0 : 0 ≤ ∑ v ∈ Sc, Real.log (2 * v) * s v ∨ ∑ v ∈ Sc, Real.log (2 * v) * s v < 0 :=
    le_or_gt 0 _
  rcases hE0 with h0 | h0
  · have : lam0 * CN ≤ 316 := by nlinarith
    nlinarith
  · have : 0 ≤ lam0 * CN := mul_nonneg hlam0 hCN0
    nlinarith

end KR

end
