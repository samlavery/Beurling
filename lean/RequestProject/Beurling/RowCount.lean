module

public import RequestProject.Beurling.RowWeights

/-!
# Lemma 6.22(a): counting rows of a given degree

A row of degree `k` in `π` labels is an exponent vector `v : Fin π → ℕ` with `∑ v_i = k`
(Mathlib's `Finset.Nat.antidiagonalTuple π k`). We prove:

* `RowWeights.card_rows_of_degree` : there are exactly `C(π + k - 1, k)` such rows
  (stars and bars);
* `RowWeights.row_monomial_le` : if every label value satisfies `p_i ≥ X > 0`, the monomial
  weight `∏ p_i^{-v_i}` of a row of degree `k` is at most `X^{-k}`;
* `RowWeights.sum_rows_of_degree_le` : the total monomial weight of the rows of degree `k` is at
  most `C(π + k - 1, k) X^{-k}`;
* `RowWeights.row_weight_high_total` : combined with Lemma 6.22(b) (`row_weight_high`), if each
  row carries a weight at most `(2 + 1/z) ∏ p_i^{-v_i}` and `e(π + k)/(k X) ≤ 1/3`, then the total
  weight of all rows of degree in `[k, K]` is at most `3 (e(π + k)/k)^k X^{-k}`, for every `K`.
-/

@[expose] public section

open Finset

namespace RowWeights

/-- **Stars and bars**: the number of exponent vectors on `π` labels of degree `k` is
`C(π + k - 1, k)`. -/
theorem card_rows_of_degree (pi k : ℕ) :
    (Finset.Nat.antidiagonalTuple pi k).card = (pi + k - 1).choose k := by
  classical
  have e : Sym (Fin pi) k ≃ {x // x ∈ Finset.Nat.antidiagonalTuple pi k} :=
    (Sym.equivNatSumOfFintype (Fin pi) k).trans
      (Equiv.subtypeEquivRight fun x => by simp [Finset.Nat.mem_antidiagonalTuple])
  rw [← Fintype.card_coe, ← Fintype.card_congr e, Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The monomial weight `∏ p_i^{-v_i}` of a row of degree `k` is at most `X^{-k}` when all
label values are at least `X > 0`. -/
theorem row_monomial_le {pi k : ℕ} {X : ℝ} (hX : 0 < X) {p : Fin pi → ℝ} (hp : ∀ i, X ≤ p i)
    {v : Fin pi → ℕ} (hv : ∑ i, v i = k) :
    ∏ i, (p i)⁻¹ ^ v i ≤ X⁻¹ ^ k := by
  rw [← hv, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun i _ => pow_nonneg (inv_nonneg.mpr (hX.trans_le (hp i)).le) _)
  intro i _
  apply pow_le_pow_left₀ (inv_nonneg.mpr (hX.trans_le (hp i)).le)
  exact inv_anti₀ hX (hp i)

/-- **Lemma 6.22(a)** (monomial count): the rows of degree `k` have total monomial weight at most
`C(π + k - 1, k) X^{-k}`. -/
theorem sum_rows_of_degree_le {pi k : ℕ} {X : ℝ} (hX : 0 < X) {p : Fin pi → ℝ}
    (hp : ∀ i, X ≤ p i) :
    ∑ v ∈ Finset.Nat.antidiagonalTuple pi k, ∏ i, (p i)⁻¹ ^ v i ≤
      ((pi + k - 1).choose k : ℝ) * X⁻¹ ^ k := by
  calc ∑ v ∈ Finset.Nat.antidiagonalTuple pi k, ∏ i, (p i)⁻¹ ^ v i
      ≤ ∑ _v ∈ Finset.Nat.antidiagonalTuple pi k, X⁻¹ ^ k :=
        Finset.sum_le_sum fun v hv =>
          row_monomial_le hX hp (Finset.Nat.mem_antidiagonalTuple.mp hv)
    _ = ((pi + k - 1).choose k : ℝ) * X⁻¹ ^ k := by
        rw [Finset.sum_const, card_rows_of_degree, nsmul_eq_mul]

/-- **Lemma 6.22, high-degree rows, total weight**: if every row `v` carries a weight
`W v ≤ (2 + 1/z) ∏ p_i^{-v_i}`, all label values are `≥ X > 0`, `z ≥ 2`, `k ≥ 1` and
`e(π + k)/(k X) ≤ 1/3`, then for every `K` the total weight of the rows of degree in `[k, K]` is
at most `3 (e(π + k)/k)^k X^{-k}`. -/
theorem row_weight_high_total {pi k : ℕ} (hk : 1 ≤ k) {X z : ℝ} (hX : 0 < X) (hz : 2 ≤ z)
    (hcond : Real.exp 1 * (pi + k) / (k * X) ≤ 1 / 3) {p : Fin pi → ℝ} (hp : ∀ i, X ≤ p i)
    (W : (Fin pi → ℕ) → ℝ) (hW : ∀ v, W v ≤ (2 + 1 / z) * ∏ i, (p i)⁻¹ ^ v i) (K : ℕ) :
    ∑ k' ∈ Icc k K, ∑ v ∈ Finset.Nat.antidiagonalTuple pi k', W v ≤
      3 * (Real.exp 1 * (pi + k) / k) ^ k * X⁻¹ ^ k := by
  refine le_trans ?_ (row_weight_high hk hX hz hcond K)
  apply Finset.sum_le_sum
  intro k' _
  have hz0 : 0 ≤ 2 + 1 / z := by
    have : 0 ≤ 1 / z := by apply div_nonneg <;> linarith
    linarith
  calc ∑ v ∈ Finset.Nat.antidiagonalTuple pi k', W v
      ≤ ∑ v ∈ Finset.Nat.antidiagonalTuple pi k', (2 + 1 / z) * ∏ i, (p i)⁻¹ ^ v i :=
        Finset.sum_le_sum fun v _ => hW v
    _ = (2 + 1 / z) * ∑ v ∈ Finset.Nat.antidiagonalTuple pi k', ∏ i, (p i)⁻¹ ^ v i := by
        rw [Finset.mul_sum]
    _ ≤ (2 + 1 / z) * (((pi + k' - 1).choose k' : ℝ) * X⁻¹ ^ k') :=
        mul_le_mul_of_nonneg_left (sum_rows_of_degree_le hX hp) hz0
    _ = ((pi + k' - 1).choose k' : ℝ) * (2 + 1 / z) * X⁻¹ ^ k' := by ring

end RowWeights
