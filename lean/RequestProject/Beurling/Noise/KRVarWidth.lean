module

public import RequestProject.Beurling.Noise.KRVar

/-!
# Theorem 5.15 for the nominal filters, from the paper's hypotheses on `H`

`PaperWidth H X₀⁻ ε θ` collects what the paper uses about the jitter width `H` on `[X₀⁻/2, ∞)`:

* `WidthReg H` (positive, `1`-Lipschitz, differentiable off a countable set);
* (R_H) `H(vw) ≤ w^ε H(v)` for `v ≥ X₀⁻/2`, `w ≥ 1`, with `0 ≤ ε ≤ 4·10⁻⁶` (eq. (RH));
* the width variation: `H` is `θ`-Lipschitz on `[X₀⁻/2, ∞)` (paper: `H' ≤ ϑ_u ≤ 10⁻⁵ H(u)/u`,
  §5.9.1 "Width variation"), `0 ≤ θ ≤ 10⁻²`;
* `H(y) ≤ y/10` for `y ≥ X₀⁻/2` (paper: `H(v)/v < 10⁻¹⁰`).

With `λ₀ ≥ 1 + 2θ` (paper: `λ₀ = exp(2.1 H(X₀)/X₀)`, and `2θ ≤ 2·10⁻⁵ H(X₀⁻)/X₀⁻` is far
smaller than `2.1 H(X₀)/X₀`), and generalized primes of value `≥ 2`, these give the radius
condition (with `ρ = 1.02`, as in the paper's `R_n ≤ 1.02 H(x/n)`) and the width condition for
the nominal filters `κ_{d→n} = 1[τ_{n/d} < x/n] 1[x/n ≥ X₀⁻]` (`radiusCond_nominal`,
`widthCond_nominal`), hence **Theorem 5.15** for them (`theorem_5_15_nominal`).
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped ENNReal

namespace KR

/-- The paper's hypotheses on the jitter width (see the module docstring). -/
structure PaperWidth (H : ℝ → ℝ) (X0m ε θ : ℝ) : Prop where
  reg : WidthReg H
  X0m_pos : 0 < X0m
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ 4 / 1000000
  RH : ∀ v w, X0m / 2 ≤ v → 1 ≤ w → H (v * w) ≤ w ^ ε * H v
  theta_nonneg : 0 ≤ θ
  theta_le : θ ≤ 1 / 100
  lip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ θ * |y - z|
  small : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ}

lemma two_rpow_le {ε : ℝ} (_h0 : 0 ≤ ε) (h1 : ε ≤ 4 / 1000000) : (2 : ℝ) ^ ε ≤ 1.001 := by
  have hb : (2 : ℝ) ≤ 1.001 ^ (1000 : ℕ) := by
    set_option exponentiation.threshold 1000 in
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 0.001 by norm_num) 1000
    norm_num at this ⊢
  calc (2 : ℝ) ^ ε ≤ 2 ^ ((1 : ℝ) / 1000) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ (1.001 ^ (1000 : ℕ)) ^ ((1 : ℝ) / 1000) :=
        Real.rpow_le_rpow (by norm_num) hb (by norm_num)
    _ = 1.001 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `H(v w)/w ≤ 0.5005 H(v)` for `v ≥ X₀⁻/2`, `w ≥ 2`. -/
lemma PaperWidth.step_le {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {v w : ℝ}
    (hv : X0m / 2 ≤ v) (hw : 2 ≤ w) : H (v * w) / w ≤ 0.5005 * H v := by
  have h1 := hP.RH v w hv (by linarith)
  have hHv := hP.reg.pos v
  have hw0 : 0 < w := by linarith
  have hε := hP.eps_le
  have hrp : w ^ ε / w ≤ (2 : ℝ) ^ ε / 2 := by
    have e1 : w ^ ε / w = w ^ (ε - 1) := by
      rw [Real.rpow_sub hw0, Real.rpow_one]
    have e2 : (2 : ℝ) ^ ε / 2 = 2 ^ (ε - 1) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    rw [e1, e2]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hw (by linarith)
  have h2 := two_rpow_le hP.eps_nonneg hP.eps_le
  calc H (v * w) / w ≤ w ^ ε * H v / w := div_le_div_of_nonneg_right h1 hw0.le
    _ = w ^ ε / w * H v := by ring
    _ ≤ (2 : ℝ) ^ ε / 2 * H v := mul_le_mul_of_nonneg_right hrp hHv.le
    _ ≤ 0.5005 * H v := by nlinarith

lemma valN_prime (val : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : LemmaM.valN val p = val p := by
  unfold LemmaM.valN
  rw [hp.factorization]
  simp [Finsupp.prod_single_index]

lemma two_le_valN (hval2 : ∀ p, p.Prime → 2 ≤ val p) {m : ℕ} (hm : 2 ≤ m) :
    2 ≤ LemmaM.valN val m := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  calc (2 : ℝ) ≤ val p := hval2 p hp
    _ = LemmaM.valN val p := (valN_prime val hp).symm
    _ ≤ LemmaM.valN val m := LemmaM.valN_le_of_dvd val hval hpm (by omega)

lemma two_le_div_of_mem {d n : ℕ} (hd : d ∈ n.properDivisors) : 2 ≤ n / d := by
  obtain ⟨hdn, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hdn; omega)
  obtain ⟨k, rfl⟩ := hdn
  rw [Nat.mul_div_cancel_left k hd0]
  by_contra h
  push_neg at h
  interval_cases k <;> simp_all

lemma posn_mul (hval : ∀ p, p.Prime → 1 ≤ val p) {d n : ℕ} (hdn : d ∣ n) (hn : n ≠ 0) :
    posn val x d = posn val x n * LemmaM.valN val (n / d) := by
  have h := posn_div (x := x) hval hdn hn
  have hw := LemmaM.valN_pos val hval (n := n / d)
  rw [← h]; field_simp

/-- The local estimates near a nominal landing point `p = x/n ≥ X₀⁻`. -/
lemma PaperWidth.near {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {p y : ℝ} (hp : X0m ≤ p)
    (hy : |y - p| ≤ 0.5106 * H p) :
    X0m / 2 < y ∧ |H y - H p| ≤ θ * (0.5106 * H p) := by
  have hX := hP.X0m_pos
  have hs := hP.small p (by linarith)
  have hHp := hP.reg.pos p
  have hy' := abs_le.mp hy
  have hy2 : X0m / 2 < y := by nlinarith [hy'.1]
  refine ⟨hy2, ?_⟩
  calc |H y - H p| ≤ θ * |y - p| := hP.lip y p hy2.le (by linarith)
    _ ≤ θ * (0.5106 * H p) := mul_le_mul_of_nonneg_left hy hP.theta_nonneg

variable {tw : ℕ → ℝ} {X0m : ℝ}

lemma nomFilter_ne_zero {d n : ℕ} (h : nomFilter val x tw X0m d n ≠ 0) :
    X0m ≤ posn val x n := by
  unfold nomFilter at h
  split_ifs at h with hc
  · exact hc.2
  · exact absurd rfl h

/-- The radius condition (`ρ = 1.02`) for the nominal filters. -/
theorem radiusCond_nominal {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) :
    RadiusCond val x H (nomFilter val x tw X0m) 1.02 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  intro n hn d hd hk y hy
  have hn0 : n ≠ 0 := by omega
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hpn := nomFilter_ne_zero hk
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hX := hP.X0m_pos
  unfold Hlev at *
  rw [posn_mul hval hdn hn0] at hy ⊢
  have hst := hP.step_le (v := posn val x n) (by linarith) hw
  have hHn := hP.reg.pos (posn val x n)
  have hr : 1.02 * H (posn val x n * LemmaM.valN val (n / d)) / LemmaM.valN val (n / d) ≤
      0.5106 * H (posn val x n) := by
    rw [mul_div_assoc]; nlinarith
  obtain ⟨-, hlip⟩ := hP.near hpn (hy.trans hr)
  have := (abs_le.mp hlip).2
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  nlinarith

/-- The width condition (`ρ = 1.02`) for the nominal filters, with `λ₀ ≥ 1 + 2θ`. -/
theorem widthCond_nominal {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) (hlam : 1 + 2 * θ ≤ lam0) :
    WidthCond val x H (nomFilter val x tw X0m) 1.02 lam0 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  intro n hn d hd hk v hv
  have hn0 : n ≠ 0 := by omega
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hpn := nomFilter_ne_zero hk
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
  have hX := hP.X0m_pos
  unfold Hlev at *
  rw [posn_mul hval hdn hn0] at hv
  set w := LemmaM.valN val (n / d)
  set p := posn val x n
  have hst := hP.step_le (v := p) (by linarith) hw
  have hHn := hP.reg.pos p
  have hy : |v / w - p| ≤ 0.5106 * H p := by
    have h3 : 1.02 * H (p * w) ≤ 0.5106 * H p * w := by
      have := (div_le_iff₀ hw0).mp hst; nlinarith
    have h4 : |v - p * w| ≤ 0.5106 * H p * w := hv.trans h3
    have e : v / w - p = (v - p * w) / w := by field_simp
    rw [e, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    exact h4
  obtain ⟨hy2, hlip⟩ := hP.near hpn hy
  have hd' : |deriv H (v / w)| ≤ θ := by
    have hlo : LipschitzOnWith ⟨θ, hP.theta_nonneg⟩ H (Ioi (X0m / 2)) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      simp only [Real.dist_eq, NNReal.coe_mk]
      exact hP.lip a b (le_of_lt ha) (le_of_lt hb)
    have := norm_deriv_le_of_lipschitzOn (Ioi_mem_nhds hy2) hlo
    rw [Real.norm_eq_abs] at this
    exact this
  have hHy := hP.reg.pos (v / w)
  have hlow := (abs_le.mp hlip).1
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  rw [div_le_div_iff₀ hHy hHn]
  have h1 : (2 + |deriv H (v / w)|) * H p ≤ (2 + θ) * H p := by nlinarith
  have h2 : (2 + θ) * H p ≤ 2 * lam0 * H (v / w) := by
    have e1 : 0 ≤ (lam0 - (1 + 2 * θ)) * H (v / w) :=
      mul_nonneg (by linarith) hHy.le
    have e2 : 0 ≤ (H (v / w) - H p + θ * (0.5106 * H p)) * (1 + 2 * θ) :=
      mul_nonneg (by linarith) (by linarith)
    have e3 : 0 ≤ θ * (1 / 100 - θ) * H p :=
      mul_nonneg (mul_nonneg hθ0 (by linarith)) hHn.le
    nlinarith
  linarith

open scoped Classical in
/-- **Theorem 5.15 for the nominal filters**: with the paper's hypotheses on `H`, generalized
primes of value `≥ 2`, a positive decision order and `λ₀ ≥ 1 + 2θ`, for every start
`x ≥ X₀⁻` and every `n ≥ 2` the nominal kernels with varying widths satisfy the TV and KR bounds
of Theorem 5.15, and their masses are `c_e = μ(e) χ^t_x(e) 1[x/e ≥ X₀⁻]` (Lemma 5.5). -/
theorem theorem_5_15_nominal {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) {n : ℕ} (hn : 2 ≤ n) :
    (eVariationOn (kerV val x H (nomFilter val x tw X0m) n) univ ≤
      ENNReal.ofReal (|mass (nomFilter val x tw X0m) n| + 1 / 2 * lam0 *
        ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e < n),
          |mass (nomFilter val x tw X0m) e| * (Hlev val x H e / Hlev val x H n) *
            (BSCert.X0Band.Hord (n / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val n)) ∧
    KRn (DkerV val x H (nomFilter val x tw X0m) n) ≤ ENNReal.ofReal (1 / 4 * lam0 *
      ∑ e ∈ n.divisors.filter (1 < ·), |mass (nomFilter val x tw X0m) e| * Hlev val x H e *
        (BSCert.X0Band.Hord (n / e) : ℝ) * (LemmaM.valN val e / LemmaM.valN val n))) ∧
    ∀ e, 1 ≤ e → mass (nomFilter val x tw X0m) e =
      ((ArithmeticFunction.moebius e : ℤ) : ℝ) * (if LemmaM.chi tw val x e then 1 else 0) *
        (if X0m ≤ x / LemmaM.valN val e then 1 else 0) := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  have hX := hP.X0m_pos
  refine ⟨theorem_5_15 hval hP.reg (abs_nomFilter_le val x tw X0m) (by norm_num)
    (by linarith [hP.theta_nonneg]) (radiusCond_nominal hP hval2)
    (widthCond_nominal hP hval2 hlam) hn, fun e he => ?_⟩
  exact mass_eq_moebius val x ht hval hX.le hx he

end KR

end
