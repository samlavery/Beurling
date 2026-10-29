module

public import Mathlib

/-!
# Lemma 4.3: the function `Ein`

`Ein(a) = ∫_0^a (e^t - 1)/t dt` (Lemma 4.3, `lem:ZBlow`). We prove that the integrand
`einDens t = (e^t - 1)/t` is non-negative and monotone on `[0, ∞)` (in Lean `einDens 0 = 0`),
hence interval integrable, and the numerical bound `Ein 8 ≤ 437.73` (true value `437.7232…`), from
the Taylor bound `|e^t - ∑_{m<30} t^m/m!| ≤ 2 t^{30}/30!` on `[0, 8]` (`Complex.exp_bound'`).
-/

@[expose] public section

open Real Finset

namespace LocalPNT

open scoped Nat

/-- The integrand `(e^t - 1)/t` of `Ein`. -/
noncomputable def einDens (t : ℝ) : ℝ := (Real.exp t - 1) / t

/-- `Ein(a) = ∫_0^a (e^t - 1)/t dt` (Lemma 4.3). -/
noncomputable def Ein (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..a, (Real.exp t - 1) / t

lemma Ein_eq (a : ℝ) : Ein a = ∫ t in (0 : ℝ)..a, einDens t := rfl

lemma einDens_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ einDens t :=
  div_nonneg (by linarith [Real.add_one_le_exp t]) ht

/-- `(e^x - 1)/x ≤ (e^y - 1)/y` for `0 < x ≤ y`, by convexity of `exp`. -/
lemma einDens_le_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : einDens x ≤ einDens y := by
  have hy : 0 < y := hx.trans_le hxy
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ y)
    (show 0 ≤ 1 - x / y by rw [sub_nonneg, div_le_one hy]; exact hxy)
    (show 0 ≤ x / y by positivity) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [div_mul_cancel₀ x hy.ne'] at h
  unfold einDens
  rw [div_le_div_iff₀ hx hy]
  have : (Real.exp x - 1) ≤ x / y * (Real.exp y - 1) := by linarith
  calc (Real.exp x - 1) * y ≤ x / y * (Real.exp y - 1) * y := by gcongr
    _ = (Real.exp y - 1) * x := by field_simp

lemma einDens_monotoneOn : MonotoneOn einDens (Set.Ici 0) := by
  intro x hx y hy hxy
  rcases (Set.mem_Ici.mp hx).lt_or_eq with hx0 | rfl
  · exact einDens_le_of_le hx0 hxy
  · simp only [einDens, Real.exp_zero, sub_self, div_zero]
    exact einDens_nonneg hy

lemma intervalIntegrable_einDens {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable einDens MeasureTheory.volume a b :=
  MonotoneOn.intervalIntegrable (einDens_monotoneOn.mono fun x hx => by
    rcases Set.mem_uIcc.mp hx with h | h <;> exact le_trans (by simp [*]) h.1)

lemma Ein_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Ein a :=
  intervalIntegral.integral_nonneg ha fun _ ht => einDens_nonneg ht.1

/-- The Taylor upper bound for `(e^t - 1)/t` on `(0, 8]`. -/
lemma einDens_le_poly {t : ℝ} (h0 : 0 < t) (h8 : t ≤ 8) :
    einDens t ≤ ∑ m ∈ range 29, t ^ m / ((m + 1)! : ℝ) + 2 * t ^ 29 / (30 ! : ℝ) := by
  have hb := Complex.exp_bound' (x := (t : ℂ)) (n := 30) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; push_cast; linarith)
  have e : Complex.exp (t : ℂ) - ∑ m ∈ range 30, (t : ℂ) ^ m / (m ! : ℂ) =
      ((Real.exp t - ∑ m ∈ range 30, t ^ m / (m ! : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h0] at hb
  have h1 := (abs_le.mp hb).2
  rw [Finset.sum_range_succ'] at h1
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h1
  unfold einDens
  rw [div_le_iff₀ h0]
  have e2 : (∑ m ∈ range 29, t ^ m / ((m + 1)! : ℝ) + 2 * t ^ 29 / (30 ! : ℝ)) * t =
      ∑ m ∈ range 29, t ^ (m + 1) / ((m + 1)! : ℝ) + t ^ 30 / (30 ! : ℝ) * 2 := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by rw [pow_succ]; ring
    · rw [pow_succ]; ring
  rw [e2]; linarith

lemma integral_poly_eight :
    ∫ t in (0 : ℝ)..8, (∑ m ∈ range 29, t ^ m / ((m + 1)! : ℝ) + 2 * t ^ 29 / (30 ! : ℝ)) =
      ∑ m ∈ range 29, (8 : ℝ) ^ (m + 1) / ((m + 1) * ((m + 1)! : ℝ)) +
        2 * 8 ^ 30 / (30 * (30 ! : ℝ)) := by
  have h1 : IntervalIntegrable (fun t : ℝ => ∑ m ∈ range 29, t ^ m / ((m + 1)! : ℝ))
      MeasureTheory.volume 0 8 :=
    (continuous_finset_sum _ fun m _ => (continuous_pow m).div_const _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => 2 * t ^ 29 / (30 ! : ℝ)) MeasureTheory.volume 0 8 :=
    ((continuous_const.mul (continuous_pow 29)).div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_finset_sum (fun m _ =>
      ((continuous_pow m).div_const _).intervalIntegrable _ _)]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_div, integral_pow, div_div, zero_pow (by omega), sub_zero]
  · rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    norm_num

/-- `Ein(8) ≤ 437.73` (Lemma 4.3: `Ein(8) = 437.7…`). -/
theorem Ein_eight_le : Ein 8 ≤ 437.73 := by
  rw [Ein_eq]
  have hP : Continuous fun t : ℝ =>
      ∑ m ∈ range 29, t ^ m / ((m + 1)! : ℝ) + 2 * t ^ 29 / (30 ! : ℝ) :=
    (continuous_finset_sum _ fun m _ => (continuous_pow m).div_const _).add
      ((continuous_const.mul (continuous_pow 29)).div_const _)
  refine (intervalIntegral.integral_mono_on (by norm_num)
    (intervalIntegrable_einDens le_rfl (by norm_num)) (hP.intervalIntegrable _ _)
    fun t ht => ?_).trans ?_
  · rcases ht.1.lt_or_eq with h0 | rfl
    · exact einDens_le_poly h0 ht.2
    · simp only [einDens, Real.exp_zero, sub_self, div_zero]
      positivity
  · rw [integral_poly_eight]
    norm_num [Finset.sum_range_succ, Nat.factorial]

end LocalPNT

end
