module

public import Mathlib

/-!
# Lemma 6.22(b): row weights of high degree

For a row of degree `k ≥ 1` in `π` labels, the count of Lemma 6.22(a) with `Ψ(Y, X₀) ≤ Y` gives
the terms `C(π + k' - 1, k') (2 + 1/z) (X₀⁻)^{-k'}`, `k' ≥ k`. If `e(π + k)/(k X₀⁻) ≤ 1/3`, their
consecutive ratio is at most `1/(3e)`, and the sum is at most `3 (e(π + k)/k)^k (X₀⁻)^{-k}`.

We prove this bound for every partial sum `k ≤ k' ≤ K` (so for the full series), for `z ≥ 2`.
-/

@[expose] public section

open Finset

namespace RowWeights

/-- `C(n, k) ≤ (e n / k)^k`. -/
lemma choose_le_exp_mul_div_pow (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
  have h2 : (k : ℝ) ^ k / k.factorial ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  calc (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := h1
    _ = ((n : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
        rw [div_pow]; field_simp
    _ ≤ ((n : ℝ) / k) ^ k * Real.exp k := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Real.exp 1 * n / k) ^ k := by
        rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by rw [← Real.exp_nat_mul]; ring_nf]
        rw [← mul_pow]; ring_nf

/-- The terms `a(k') = C(π + k' - 1, k') X^{-k'}`. -/
noncomputable def term (pi : ℕ) (X : ℝ) (k' : ℕ) : ℝ := ((pi + k' - 1).choose k' : ℝ) * X⁻¹ ^ k'

lemma term_nonneg (pi : ℕ) {X : ℝ} (hX : 0 < X) (k' : ℕ) : 0 ≤ term pi X k' := by
  unfold term; positivity

lemma term_succ_le {pi k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 0 < X)
    (hcond : Real.exp 1 * (pi + k) / (k * X) ≤ 1 / 3) {k' : ℕ} (hk' : k ≤ k') :
    term pi X (k' + 1) ≤ (1 / 6) * term pi X k' := by
  have hk'1 : 1 ≤ k' := le_trans hk hk'
  have hid := Nat.add_one_mul_choose_eq (pi + k' - 1) k'
  have e1 : pi + k' - 1 + 1 = pi + (k' + 1) - 1 := by omega
  rw [e1] at hid
  have hcast : ((pi + (k' + 1) - 1).choose (k' + 1) : ℝ) =
      ((pi + k' : ℕ) : ℝ) / (k' + 1) * ((pi + k' - 1).choose k' : ℝ) := by
    have : ((pi + (k' + 1) - 1 : ℕ) : ℝ) * ((pi + k' - 1).choose k' : ℝ) =
        ((pi + (k' + 1) - 1).choose (k' + 1) : ℝ) * ((k' : ℝ) + 1) := by exact_mod_cast hid
    have e2 : ((pi + (k' + 1) - 1 : ℕ) : ℝ) = ((pi + k' : ℕ) : ℝ) := by congr 1
    rw [e2] at this
    field_simp
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : ((pi + k' : ℕ) : ℝ) / (k' + 1) * X⁻¹ ≤ 1 / 6 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h1 : ((pi + k' : ℕ) : ℝ) / (k' + 1) ≤ ((pi : ℝ) + k) / k := by
      rw [div_le_div_iff₀ (by positivity) hk0]
      have : (k : ℝ) ≤ k' := by exact_mod_cast hk'
      push_cast
      nlinarith [(Nat.cast_nonneg pi : (0:ℝ) ≤ pi)]
    have h2 : ((pi : ℝ) + k) / k * X⁻¹ ≤ 1 / 6 := by
      have : ((pi : ℝ) + k) / k * X⁻¹ = (Real.exp 1 * (pi + k) / (k * X)) / Real.exp 1 := by
        field_simp
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    calc ((pi + k' : ℕ) : ℝ) / (k' + 1) * X⁻¹ ≤ ((pi : ℝ) + k) / k * X⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 / 6 := h2
  unfold term
  rw [hcast, pow_succ]
  have hc : (0 : ℝ) ≤ ((pi + k' - 1).choose k' : ℝ) * X⁻¹ ^ k' := by positivity
  calc ((pi + k' : ℕ) : ℝ) / (k' + 1) * ((pi + k' - 1).choose k' : ℝ) * (X⁻¹ ^ k' * X⁻¹)
      = (((pi + k' : ℕ) : ℝ) / (k' + 1) * X⁻¹) * (((pi + k' - 1).choose k' : ℝ) * X⁻¹ ^ k') := by
        ring
    _ ≤ (1 / 6) * (((pi + k' - 1).choose k' : ℝ) * X⁻¹ ^ k') :=
        mul_le_mul_of_nonneg_right hratio hc

lemma term_le_geom {pi k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 0 < X)
    (hcond : Real.exp 1 * (pi + k) / (k * X) ≤ 1 / 3) (i : ℕ) :
    term pi X (k + i) ≤ (1 / 6) ^ i * term pi X k := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc term pi X (k + (i + 1)) = term pi X (k + i + 1) := by rw [add_assoc]
      _ ≤ (1 / 6) * term pi X (k + i) := term_succ_le hk hX hcond (Nat.le_add_right k i)
      _ ≤ (1 / 6) * ((1 / 6) ^ i * term pi X k) := by gcongr
      _ = (1 / 6) ^ (i + 1) * term pi X k := by ring

/-- **Lemma 6.22(b)** (high degree): if `e(π + k)/(k X) ≤ 1/3` and `z ≥ 2`, then for every `K`,
`∑_{k ≤ k' ≤ K} C(π + k' - 1, k') (2 + 1/z) X^{-k'} ≤ 3 (e(π + k)/k)^k X^{-k}`. -/
theorem row_weight_high {pi k : ℕ} (hk : 1 ≤ k) {X z : ℝ} (hX : 0 < X) (hz : 2 ≤ z)
    (hcond : Real.exp 1 * (pi + k) / (k * X) ≤ 1 / 3) (K : ℕ) :
    ∑ k' ∈ Icc k K, ((pi + k' - 1).choose k' : ℝ) * (2 + 1 / z) * X⁻¹ ^ k' ≤
      3 * (Real.exp 1 * (pi + k) / k) ^ k * X⁻¹ ^ k := by
  have hz' : 2 + 1 / z ≤ 5 / 2 := by
    have : 1 / z ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hz
    linarith
  have hsum : ∑ k' ∈ Icc k K, term pi X k' ≤ (6 / 5) * term pi X k := by
    rcases Nat.lt_or_ge K k with hK | hK
    · rw [Finset.Icc_eq_empty (by omega)]; simp [term_nonneg pi hX]
    · have : Icc k K = Ico k (K + 1) := rfl
      rw [this, Finset.sum_Ico_eq_sum_range]
      calc ∑ i ∈ range (K + 1 - k), term pi X (k + i)
          ≤ ∑ i ∈ range (K + 1 - k), (1 / 6 : ℝ) ^ i * term pi X k :=
            Finset.sum_le_sum (fun i _ => term_le_geom hk hX hcond i)
        _ = (∑ i ∈ range (K + 1 - k), (1 / 6 : ℝ) ^ i) * term pi X k := by
            rw [Finset.sum_mul]
        _ ≤ (6 / 5) * term pi X k := by
            apply mul_le_mul_of_nonneg_right _ (term_nonneg pi hX k)
            rw [geom_sum_eq (by norm_num)]
            have : 0 ≤ (1 / 6 : ℝ) ^ (K + 1 - k) := by positivity
            rw [div_le_iff_of_neg (by norm_num)]
            linarith
  have hchoose : term pi X k ≤ (Real.exp 1 * (pi + k) / k) ^ k * X⁻¹ ^ k := by
    unfold term
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc ((pi + k - 1).choose k : ℝ) ≤ (Real.exp 1 * ((pi + k - 1 : ℕ) : ℝ) / k) ^ k :=
          choose_le_exp_mul_div_pow _ k hk
      _ ≤ (Real.exp 1 * (pi + k) / k) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : ((pi + k - 1 : ℕ) : ℝ) ≤ ((pi + k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
          simpa using this
  calc ∑ k' ∈ Icc k K, ((pi + k' - 1).choose k' : ℝ) * (2 + 1 / z) * X⁻¹ ^ k'
      = (2 + 1 / z) * ∑ k' ∈ Icc k K, term pi X k' := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k' _; unfold term; ring
    _ ≤ (5 / 2) * ((6 / 5) * term pi X k) := by
        apply mul_le_mul hz' hsum (Finset.sum_nonneg (fun i _ => term_nonneg pi hX i))
          (by norm_num)
    _ = 3 * term pi X k := by ring
    _ ≤ 3 * ((Real.exp 1 * (pi + k) / k) ^ k * X⁻¹ ^ k) := by gcongr
    _ = 3 * (Real.exp 1 * (pi + k) / k) ^ k * X⁻¹ ^ k := by ring

end RowWeights
