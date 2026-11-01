module

public import Mathlib

/-!
# Lemma 4.2 (The base factor): the bounds on `Z_∞`

`Z_∞(s) = ∏_{p < X₀} (1 - p^{-s})^{-1}` is a finite Euler product. For `σ = Re s > 0`:

* `|Z_∞(s)| ≤ Z_∞(σ)` (`norm_Zinf_le`);
* `|Z_∞'(s)| ≤ Z_∞(σ) · S(σ)`, `S(σ) = ∑_{p<X₀} log p/(p^σ - 1)` (`norm_deriv_Zinf_le`);
* `Z_∞(σ) ≤ Z_∞(1) e^{(1-σ) S(σ)}` for `σ ≤ 1`, and `Z_∞(σ) ≤ Z_∞(1)` for `σ ≥ 1`;
* `S(σ) ≤ S(1)/0.98` for `σ ≥ 1 - δ`, `δ log X₀ ≤ 0.01`.

With the Mertens estimates `Z_∞(1) ≤ 1.8 log X₀` (Mertens' product theorem, `e^γ = 1.781…`) and
`∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀` (not in Mathlib, so taken as hypotheses), this gives the bounds of Lemma 4.2 on `σ ≥ 1 - δ`:
`|Z_∞| ≤ 1.9 log X₀` and `|Z_∞'| ≤ 4 log² X₀` (`lemma_4_2_Zinf`). Then, if `Z_B` is
holomorphic and within `e^{-X₀²/4}` of `Z_∞` on the region `1/2 ≤ σ ≤ 2`, `|t| ≥ T` (the first
statement of Lemma 4.2), Cauchy's estimate gives `|Z_B| ≤ 2 log X₀` and `|Z_B'| ≤ 4.01 log² X₀`
near `σ = 1` (`lemma_4_2_ZB`).
-/

@[expose] public section

open Complex Metric Set Finset

namespace BaseFactor

/-- The finite Euler product `Z_∞(s) = ∏_{p < X₀} (1 - p^{-s})^{-1}`. -/
noncomputable def Zinf (X₀ : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ X₀.primesBelow, (1 - ((p : ℝ) : ℂ) ^ (-s))⁻¹

/-- `Z_∞(σ)` on the real axis. -/
noncomputable def ZinfR (X₀ : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- `S(σ) = ∑_{p<X₀} log p/(p^σ - 1) = -(log Z_∞)'(σ)`. -/
noncomputable def logSum (X₀ : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ X₀.primesBelow, Real.log p / ((p : ℝ) ^ σ - 1)

section prime

variable {p : ℕ} (hp : p.Prime)
include hp

lemma two_le_cast : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le

lemma cast_pos : (0 : ℝ) < p := by linarith [two_le_cast hp]

lemma rpow_neg_lt_one {σ : ℝ} (hσ : 0 < σ) : (p : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_cast hp]) (by linarith)

lemma norm_cpow_neg (s : ℂ) : ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (cast_pos hp), Complex.neg_re]

lemma one_sub_le_norm {s : ℂ} : 1 - (p : ℝ) ^ (-s.re) ≤ ‖1 - ((p : ℝ) : ℂ) ^ (-s)‖ := by
  have := norm_sub_norm_le (1 : ℂ) (((p : ℝ) : ℂ) ^ (-s))
  rw [norm_one, norm_cpow_neg hp] at this
  exact this

lemma one_sub_ne_zero {s : ℂ} (hσ : 0 < s.re) : 1 - ((p : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 := one_sub_le_norm hp (s := s)
  rw [h, norm_zero] at h1
  linarith [rpow_neg_lt_one hp hσ]

lemma norm_factor_le {s : ℂ} (hσ : 0 < s.re) :
    ‖(1 - ((p : ℝ) : ℂ) ^ (-s))⁻¹‖ ≤ (1 - (p : ℝ) ^ (-s.re))⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (by linarith [rpow_neg_lt_one hp hσ]) (one_sub_le_norm hp)

lemma factor_pos {σ : ℝ} (hσ : 0 < σ) : 0 < (1 - (p : ℝ) ^ (-σ))⁻¹ :=
  inv_pos.mpr (by linarith [rpow_neg_lt_one hp hσ])

lemma rpow_sub_one_pos {σ : ℝ} (hσ : 0 < σ) : 0 < (p : ℝ) ^ σ - 1 := by
  have := Real.one_lt_rpow (show (1 : ℝ) < p by linarith [two_le_cast hp]) hσ
  linarith

end prime

lemma norm_Zinf_le (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) : ‖Zinf X₀ s‖ ≤ ZinfR X₀ s.re := by
  unfold Zinf ZinfR
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
  intro p hp
  exact norm_factor_le (Nat.mem_primesBelow.mp hp).2 hσ

lemma ZinfR_pos (X₀ : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < ZinfR X₀ σ :=
  Finset.prod_pos fun _ hp => factor_pos (Nat.mem_primesBelow.mp hp).2 hσ

lemma logSum_nonneg (X₀ : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ logSum X₀ σ :=
  Finset.sum_nonneg fun p hp => by
    have hpp := (Nat.mem_primesBelow.mp hp).2
    exact div_nonneg (Real.log_nonneg (by linarith [two_le_cast hpp]))
      (rpow_sub_one_pos hpp hσ).le

/-- The derivative of `Z_∞`. -/
lemma hasDerivAt_Zinf (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) :
    HasDerivAt (Zinf X₀) (∑ p ∈ X₀.primesBelow,
      (∏ q ∈ X₀.primesBelow.erase p, (1 - ((q : ℝ) : ℂ) ^ (-s))⁻¹) •
        (-(Complex.log (p : ℝ) * ((p : ℝ) : ℂ) ^ (-s)) / (1 - ((p : ℝ) : ℂ) ^ (-s)) ^ 2)) s := by
  have : Zinf X₀ = ∏ p ∈ X₀.primesBelow, fun s : ℂ => (1 - ((p : ℝ) : ℂ) ^ (-s))⁻¹ := by
    ext z; simp [Zinf, Finset.prod_apply]
  rw [this]
  apply HasDerivAt.finset_prod
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  have hc : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (cast_pos hpp).ne'
  have h1 : HasDerivAt (fun z : ℂ => ((p : ℝ) : ℂ) ^ (-z))
      (((p : ℝ) : ℂ) ^ (-s) * Complex.log (p : ℝ) * (-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - ((p : ℝ) : ℂ) ^ (-z))
      (Complex.log (p : ℝ) * ((p : ℝ) : ℂ) ^ (-s)) s := by
    convert! (hasDerivAt_const s (1 : ℂ)).sub h1 using 1; ring
  exact h2.inv (one_sub_ne_zero hpp hσ)

lemma differentiableAt_Zinf (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) : DifferentiableAt ℂ (Zinf X₀) s :=
  (hasDerivAt_Zinf X₀ hσ).differentiableAt

/-- `|Z_∞'(s)| ≤ Z_∞(σ) S(σ)`. -/
lemma norm_deriv_Zinf_le (X₀ : ℕ) {s : ℂ} (hσ : 0 < s.re) :
    ‖deriv (Zinf X₀) s‖ ≤ ZinfR X₀ s.re * logSum X₀ s.re := by
  rw [(hasDerivAt_Zinf X₀ hσ).deriv]
  refine (norm_sum_le _ _).trans ?_
  unfold ZinfR logSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  rw [← Finset.mul_prod_erase _ _ hp, smul_eq_mul, norm_mul]
  have hprod : ‖∏ q ∈ X₀.primesBelow.erase p, (1 - ((q : ℝ) : ℂ) ^ (-s))⁻¹‖ ≤
      ∏ q ∈ X₀.primesBelow.erase p, (1 - (q : ℝ) ^ (-s.re))⁻¹ := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun q _ => norm_nonneg _)
    intro q hq
    exact norm_factor_le (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hq)).2 hσ
  have hP0 : 0 ≤ ∏ q ∈ X₀.primesBelow.erase p, (1 - (q : ℝ) ^ (-s.re))⁻¹ :=
    Finset.prod_nonneg fun q hq =>
      (factor_pos (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hq)).2 hσ).le
  have hp0 := cast_pos hpp
  have hlt := rpow_neg_lt_one hpp hσ
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith [two_le_cast hpp])
  have hderiv : ‖-(Complex.log (p : ℝ) * ((p : ℝ) : ℂ) ^ (-s)) /
      (1 - ((p : ℝ) : ℂ) ^ (-s)) ^ 2‖ ≤
      (1 - (p : ℝ) ^ (-s.re))⁻¹ * (Real.log p / ((p : ℝ) ^ s.re - 1)) := by
    rw [norm_div, norm_neg, norm_mul, norm_pow, norm_cpow_neg hpp,
      ← Complex.ofReal_log hp0.le, Complex.norm_real, Real.norm_of_nonneg hlog]
    have hn := one_sub_le_norm hpp (s := s)
    have hpq : (p : ℝ) ^ s.re = ((p : ℝ) ^ (-s.re))⁻¹ := by rw [Real.rpow_neg hp0.le, inv_inv]
    rw [hpq]
    set q := (p : ℝ) ^ (-s.re)
    have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
    have h1q : 0 < 1 - q := by linarith
    have hq1 : q⁻¹ - 1 ≠ 0 := by
      have : 1 < q⁻¹ := one_lt_inv_iff₀.mpr ⟨hq0, hlt⟩
      linarith
    have e : (1 - q)⁻¹ * (Real.log p / (q⁻¹ - 1)) = Real.log p * q / (1 - q) ^ 2 := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ h1q.le hn 2
  calc ‖∏ q ∈ X₀.primesBelow.erase p, (1 - ((q : ℝ) : ℂ) ^ (-s))⁻¹‖ *
        ‖-(Complex.log (p : ℝ) * ((p : ℝ) : ℂ) ^ (-s)) / (1 - ((p : ℝ) : ℂ) ^ (-s)) ^ 2‖ ≤
      (∏ q ∈ X₀.primesBelow.erase p, (1 - (q : ℝ) ^ (-s.re))⁻¹) *
        ((1 - (p : ℝ) ^ (-s.re))⁻¹ * (Real.log p / ((p : ℝ) ^ s.re - 1))) :=
        mul_le_mul hprod hderiv (norm_nonneg _) hP0
    _ = _ := by ring

lemma factor_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ0 : 0 < σ) :
    (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ (1 - (p : ℝ) ^ (-(1:ℝ)))⁻¹ *
      Real.exp ((1 - σ) * (Real.log p / ((p : ℝ) ^ σ - 1))) := by
  have hp0 := cast_pos hp
  have hp2 := two_le_cast hp
  have hq1 := rpow_neg_lt_one hp hσ0
  have hr1 := rpow_neg_lt_one hp one_pos
  set q := (p : ℝ) ^ (-σ) with hq
  set r := (p : ℝ) ^ (-(1:ℝ)) with hr
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  have hpσ : (p : ℝ) ^ σ = q⁻¹ := by rw [hq, Real.rpow_neg hp0.le, inv_inv]
  have hpσ1 : 0 < (p : ℝ) ^ σ - 1 := rpow_sub_one_pos hp hσ0
  have hrq : r = q * (p : ℝ) ^ (σ - 1) := by
    rw [hr, hq, ← Real.rpow_add hp0]; ring_nf
  have hexp : 1 + (σ - 1) * Real.log p ≤ (p : ℝ) ^ (σ - 1) := by
    rw [Real.rpow_def_of_pos hp0]
    have := Real.add_one_le_exp (Real.log p * (σ - 1)); linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hqr : q - r ≤ q * ((1 - σ) * Real.log p) := by
    rw [hrq]; nlinarith
  have key : (q - r) / (1 - q) ≤ (1 - σ) * (Real.log p / ((p : ℝ) ^ σ - 1)) := by
    rw [div_le_iff₀ (by linarith)]
    have e : (1 - σ) * (Real.log p / ((p : ℝ) ^ σ - 1)) * (1 - q) =
        q * ((1 - σ) * Real.log p) := by
      rw [hpσ] at hpσ1 ⊢
      have h1 : 1 - q ≠ 0 := by linarith
      have h3 : q⁻¹ - 1 = (1 - q) / q := by field_simp
      rw [h3]
      field_simp
    rw [e]; exact hqr
  have hexp2 := Real.add_one_le_exp ((q - r) / (1 - q))
  have e2 : (1 - q)⁻¹ = (1 - r)⁻¹ * ((q - r) / (1 - q) + 1) := by
    have : 1 - q ≠ 0 := by linarith
    have : 1 - r ≠ 0 := by linarith
    field_simp; ring
  rw [e2]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (by linarith)).le
  exact hexp2.trans (Real.exp_le_exp.mpr key)

/-- `Z_∞(σ) ≤ Z_∞(1) e^{(1-σ) S(σ)}` for `σ > 0`. -/
lemma ZinfR_le_exp (X₀ : ℕ) {σ : ℝ} (hσ0 : 0 < σ) :
    ZinfR X₀ σ ≤ ZinfR X₀ 1 * Real.exp ((1 - σ) * logSum X₀ σ) := by
  unfold ZinfR logSum
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀ (fun p hp => (factor_pos (Nat.mem_primesBelow.mp hp).2 hσ0).le)
  intro p hp
  exact factor_le (Nat.mem_primesBelow.mp hp).2 hσ0

/-- `Z_∞(σ) ≤ Z_∞(1)` for `σ ≥ 1`. -/
lemma ZinfR_le_of_one_le (X₀ : ℕ) {σ : ℝ} (hσ1 : 1 ≤ σ) : ZinfR X₀ σ ≤ ZinfR X₀ 1 := by
  unfold ZinfR
  apply Finset.prod_le_prod₀ (fun p hp => (factor_pos (Nat.mem_primesBelow.mp hp).2
    (by linarith)).le)
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  have h1 := rpow_neg_lt_one hpp (show (0:ℝ) < 1 by norm_num)
  apply inv_anti₀ (by linarith)
  have : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [two_le_cast hpp]) (by linarith)
  linarith

/-- `S(σ) ≤ S(1)/0.98` for `σ ≥ 1 - δ`, `δ log X₀ ≤ 0.01`. -/
lemma logSum_le (X₀ : ℕ) (hX : 2 ≤ X₀) {δ σ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ * Real.log X₀ ≤ 1 / 100) (hσ : 1 - δ ≤ σ) :
    logSum X₀ σ ≤ logSum X₀ 1 / 0.98 := by
  unfold logSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpX, hpp⟩ := Nat.mem_primesBelow.mp hp
  have hp0 := cast_pos hpp
  have hp2 := two_le_cast hpp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hlogX : Real.log p ≤ Real.log X₀ :=
    Real.log_le_log hp0 (by exact_mod_cast hpX.le)
  have hσ0 : 0 < σ := by
    have : δ < 1 := by
      have hX0 : Real.log 2 ≤ Real.log X₀ := Real.log_le_log (by norm_num) (by exact_mod_cast hX)
      have := Real.log_two_gt_d9
      nlinarith
    linarith
  -- `p^σ ≥ 0.99 p`
  have h1 : 0.99 * (p : ℝ) ≤ (p : ℝ) ^ σ := by
    have hpd : (p : ℝ) ^ (1 - δ) ≤ (p : ℝ) ^ σ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hσ
    have e : (p : ℝ) ^ (1 - δ) = p * Real.exp (-(δ * Real.log p)) := by
      rw [Real.rpow_sub hp0, Real.rpow_one, Real.rpow_def_of_pos hp0, Real.exp_neg,
        div_eq_mul_inv, mul_comm (Real.log p)]
    have h2 : 0.99 ≤ Real.exp (-(δ * Real.log p)) := by
      have := Real.add_one_le_exp (-(δ * Real.log p))
      have : δ * Real.log p ≤ δ * Real.log X₀ := mul_le_mul_of_nonneg_left hlogX hδ0
      linarith
    rw [e] at hpd
    nlinarith
  rw [div_div, Real.rpow_one]
  apply div_le_div_of_nonneg_left hlog (by nlinarith)
  linarith

lemma exp_small_le {x : ℝ} (hx : x ≤ 0.0105) : Real.exp x ≤ 1.0107 := by
  have h := Real.add_one_le_exp (-x)
  have hpos := Real.exp_pos x
  have : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

/-- **Lemma 4.2, bounds on `Z_∞`.** Assume the Mertens estimates `Z_∞(1) ≤ 1.8 log X₀`
(Mertens' product theorem, `e^γ = 1.781…`) and `∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀`. On
`σ ≥ 1 - δ` with `δ log X₀ ≤ 0.01`: `|Z_∞(s)| ≤ 1.9 log X₀` and `|Z_∞'(s)| ≤ 4 log² X₀`. -/
theorem lemma_4_2_Zinf {X₀ : ℕ} (hX : 2 ≤ X₀) (hM1 : ZinfR X₀ 1 ≤ 1.8 * Real.log X₀)
    (hM2 : logSum X₀ 1 ≤ 1.01 * Real.log X₀) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ * Real.log X₀ ≤ 1 / 100) {s : ℂ} (hσ : 1 - δ ≤ s.re) :
    ‖Zinf X₀ s‖ ≤ 1.9 * Real.log X₀ ∧ ‖deriv (Zinf X₀) s‖ ≤ 4 * Real.log X₀ ^ 2 := by
  have hΛ : 0 < Real.log X₀ := Real.log_pos (by exact_mod_cast hX)
  have hσ0 : 0 < s.re := by
    have : δ < 1 := by
      have hX0 : Real.log 2 ≤ Real.log X₀ := Real.log_le_log (by norm_num) (by exact_mod_cast hX)
      have := Real.log_two_gt_d9
      nlinarith
    linarith
  have hS := logSum_le X₀ hX hδ0 hδ hσ
  have hS0 := logSum_nonneg X₀ hσ0
  have hS1 : logSum X₀ s.re ≤ 1.031 * Real.log X₀ := by
    have : logSum X₀ 1 / 0.98 ≤ 1.031 * Real.log X₀ := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hexp : (1 - s.re) * logSum X₀ s.re ≤ 0.0105 := by
    have h1 : (1 - s.re) * logSum X₀ s.re ≤ δ * logSum X₀ s.re :=
      mul_le_mul_of_nonneg_right (by linarith) hS0
    have h2 : δ * logSum X₀ s.re ≤ δ * (1.031 * Real.log X₀) := mul_le_mul_of_nonneg_left hS1 hδ0
    nlinarith
  have hZ : ZinfR X₀ s.re ≤ 1.82 * Real.log X₀ := by
    have h1 := ZinfR_le_exp X₀ hσ0
    have hZ10 : 0 ≤ ZinfR X₀ 1 := (ZinfR_pos X₀ one_pos).le
    have h2 : Real.exp ((1 - s.re) * logSum X₀ s.re) ≤ 1.0107 := exp_small_le hexp
    calc ZinfR X₀ s.re ≤ ZinfR X₀ 1 * Real.exp ((1 - s.re) * logSum X₀ s.re) := h1
      _ ≤ (1.8 * Real.log X₀) * 1.0107 :=
          mul_le_mul hM1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ 1.82 * Real.log X₀ := by nlinarith
  refine ⟨(norm_Zinf_le X₀ hσ0).trans (by linarith), (norm_deriv_Zinf_le X₀ hσ0).trans ?_⟩
  have hZ0 := (ZinfR_pos X₀ hσ0).le
  calc ZinfR X₀ s.re * logSum X₀ s.re ≤ (1.82 * Real.log X₀) * (1.031 * Real.log X₀) :=
        mul_le_mul hZ hS1 hS0 (by positivity)
    _ ≤ 4 * Real.log X₀ ^ 2 := by nlinarith

/-- **Lemma 4.2, bounds on `Z_B`.** Suppose `Z_B` is holomorphic on the region
`1/2 ≤ σ ≤ 2`, `|t| ≥ T`, and `|Z_B - Z_∞| ≤ e^{-X₀²/4}` there (the first statement of
Lemma 4.2), and the Mertens estimates hold, with `log X₀ ≥ 10`. Then at every `s` with
`1 - δ ≤ σ ≤ 7/4`, `|t| ≥ T + 1/4`, `δ log X₀ ≤ 0.01`: `Z_B` is differentiable at `s`,
`|Z_B(s)| ≤ 2 log X₀` and `|Z_B'(s)| ≤ 4.01 log² X₀` (Cauchy's estimate on the disc of radius
`1/4`). -/
theorem lemma_4_2_ZB {X₀ : ℕ} (hX : 2 ≤ X₀) (hΛ : 10 ≤ Real.log X₀)
    (hM1 : ZinfR X₀ 1 ≤ 1.8 * Real.log X₀) (hM2 : logSum X₀ 1 ≤ 1.01 * Real.log X₀)
    {ZB : ℂ → ℂ} {T : ℝ}
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| → DifferentiableAt ℂ ZB z)
    (hclose : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → T ≤ |z.im| →
      ‖ZB z - Zinf X₀ z‖ ≤ Real.exp (-((X₀ : ℝ) ^ 2 / 4)))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ * Real.log X₀ ≤ 1 / 100) {s : ℂ} (hσ1 : 1 - δ ≤ s.re)
    (hσ2 : s.re ≤ 7 / 4) (ht : T + 1 / 4 ≤ |s.im|) :
    DifferentiableAt ℂ ZB s ∧ ‖ZB s‖ ≤ 2 * Real.log X₀ ∧
      ‖deriv ZB s‖ ≤ 4.01 * Real.log X₀ ^ 2 := by
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hδ1 : δ ≤ 1 / 1000 := by nlinarith
  have hσ3 : 3 / 4 ≤ s.re := by linarith
  obtain ⟨hZ, hZ'⟩ := lemma_4_2_Zinf hX hM1 hM2 hδ0 hδ hσ1
  -- the size of `e^{-X₀²/4}`
  have hX3 : (3 : ℝ) ≤ X₀ := by
    have h1 : Real.exp 10 ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (show (0:ℝ) < X₀ by exact_mod_cast (by omega : 0 < X₀))]
      exact Real.exp_le_exp.mpr hΛ
    have h2 := Real.add_one_le_exp 10
    linarith
  have hε : Real.exp (-((X₀ : ℝ) ^ 2 / 4)) ≤ 1 / 4 := by
    have h1 : Real.exp (-((X₀ : ℝ) ^ 2 / 4)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-2) ≤ 1 / 4 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp 2
      have h3 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)
      linarith
    linarith
  -- points of the closed disc of radius `1/4` lie in the region
  have hreg : ∀ z ∈ closedBall s (1 / 4), 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ T ≤ |z.im| := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    have h2 := Complex.abs_im_le_norm (z - s)
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    have h3 := abs_sub_abs_le_abs_sub s.im z.im
    rw [abs_sub_comm] at h3
    refine ⟨by linarith [(abs_le.mp (h1.trans hz)).1], by linarith [(abs_le.mp (h1.trans hz)).2],
      by linarith⟩
  have hsr := hreg s (mem_closedBall_self (by norm_num))
  have hdZB : DifferentiableAt ℂ ZB s := hdiff s hsr.1 hsr.2.1 hsr.2.2
  have hdZ : DifferentiableAt ℂ (Zinf X₀) s := differentiableAt_Zinf X₀ (by linarith)
  refine ⟨hdZB, ?_, ?_⟩
  · have h1 := hclose s hsr.1 hsr.2.1 hsr.2.2
    have h2 := norm_le_norm_add_norm_sub' (ZB s) (Zinf X₀ s)
    linarith
  · set f : ℂ → ℂ := fun z => ZB z - Zinf X₀ z
    have hfd : DiffContOnCl ℂ f (ball s (1 / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s (by norm_num)]
      intro z hz
      obtain ⟨h1, h2, h3⟩ := hreg z hz
      exact ((hdiff z h1 h2 h3).sub (differentiableAt_Zinf X₀ (by linarith))).differentiableWithinAt
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1 / 4)
      hfd (fun z hz => by
        obtain ⟨h1, h2, h3⟩ := hreg z (sphere_subset_closedBall hz)
        exact hclose z h1 h2 h3)
    have hderiv : deriv ZB s = deriv f s + deriv (Zinf X₀) s := by
      have : deriv f s = deriv ZB s - deriv (Zinf X₀) s := deriv_sub hdZB hdZ
      rw [this]; ring
    rw [hderiv]
    have h4 := norm_add_le (deriv f s) (deriv (Zinf X₀) s)
    have h5 : Real.exp (-((X₀ : ℝ) ^ 2 / 4)) / (1 / 4) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    nlinarith

end BaseFactor

end
