module

public import RequestProject.Beurling.RowCount

/-!
# Lemma 6.22(a),(b): the admissible (s4) data of a high-degree row

The skeleton datum (s4) of a row `y ∈ R` is its monomial `M_y` in the labels and its tail `d_y`,
subject to `M_y(τ) d_y ≤ 2z + 1` (the `j`-th label evaluated at `τ_j`). For the rows of degree
in `[k, K]`, `admHigh` is the set of these pairs (tails are not required to be `X₀`-smooth; this
only enlarges the set, i.e. uses `Ψ(Y, X₀) ≤ Y`).

* `RankFull.card_admHigh_le` : **Lemma 6.22(a)+(b)**: if all label values `τ_j ≥ Xm > 0`,
  `z ≥ 2` and `e(π + k)/(k Xm) ≤ 1/3`, then `#admHigh ≤ z · 3 (e(π + k)/k)^k Xm^{-k}`, i.e.
  `w_y ≤ 3 (e(π + k)/k)^k Xm^{-k}`.
-/

@[expose] public section

open Finset

namespace RankFull

/-- The monomial value `M_v(τ) = ∏_j τ_j^{v_j}`. -/
noncomputable def monoVal {π : ℕ} (τl : Fin π → ℝ) (v : Fin π → ℕ) : ℝ := ∏ i, τl i ^ v i

/-- The admissible (s4) data of a row of degree in `[k, K]`: pairs `(v, d)`, `d ≥ 1`, with
`M_v(τ) d ≤ Y` (`Y = 2z + 1`). -/
noncomputable def admHigh (π k K : ℕ) (τl : Fin π → ℝ) (Y : ℝ) :
    Finset ((Fin π → ℕ) × ℕ) := by
  classical exact (((Icc k K).biUnion (Finset.Nat.antidiagonalTuple π)) ×ˢ
    Finset.Icc 1 ⌊Y⌋₊).filter fun p => monoVal τl p.1 * p.2 ≤ Y

lemma card_tails_le {M Y : ℝ} (hM : 0 < M) (hY : 0 ≤ Y) :
    (((Finset.Icc 1 ⌊Y⌋₊).filter fun d : ℕ => M * d ≤ Y).card : ℝ) ≤ Y / M := by
  have hsub : (Finset.Icc 1 ⌊Y⌋₊).filter (fun d : ℕ => M * d ≤ Y) ⊆ Finset.Icc 1 ⌊Y / M⌋₊ := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd1).1, ?_⟩
    apply Nat.le_floor
    rw [le_div_iff₀ hM]; linarith
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  calc (((Finset.Icc 1 ⌊Y⌋₊).filter fun d : ℕ => M * d ≤ Y).card : ℝ) ≤ (⌊Y / M⌋₊ : ℝ) := by
        exact_mod_cast this
    _ ≤ Y / M := Nat.floor_le (div_nonneg hY hM.le)

/-- **Lemma 6.22(a)+(b)** for the (s4) data of the rows of degree in `[k, K]`. -/
theorem card_admHigh_le {π k K : ℕ} (hk : 1 ≤ k) {Xm z : ℝ} (hXm : 0 < Xm) (hz : 2 ≤ z)
    (hcond : Real.exp 1 * (π + k) / (k * Xm) ≤ 1 / 3) {τl : Fin π → ℝ} (hτl : ∀ i, Xm ≤ τl i) :
    ((admHigh π k K τl (2 * z + 1)).card : ℝ) ≤
      z * (3 * (Real.exp 1 * (π + k) / k) ^ k * Xm⁻¹ ^ k) := by
  classical
  set V := (Icc k K).biUnion (Finset.Nat.antidiagonalTuple π) with hV
  have hz0 : 0 < z := by linarith
  have hM : ∀ v, 0 < monoVal τl v := fun v =>
    Finset.prod_pos fun i _ => pow_pos (hXm.trans_le (hτl i)) _
  have hY : (0 : ℝ) ≤ 2 * z + 1 := by linarith
  -- fibre over `v`
  have hfib : (admHigh π k K τl (2 * z + 1)).card ≤
      ∑ v ∈ V, ((Finset.Icc 1 ⌊2 * z + 1⌋₊).filter fun d : ℕ =>
        monoVal τl v * d ≤ 2 * z + 1).card := by
    unfold admHigh
    rw [Finset.card_filter, Finset.sum_product]
    exact le_of_eq (Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm)
  have hfib' : ((admHigh π k K τl (2 * z + 1)).card : ℝ) ≤
      ∑ v ∈ V, (2 * z + 1) / monoVal τl v := by
    refine (Nat.cast_le.mpr hfib).trans ?_
    push_cast
    exact Finset.sum_le_sum fun v _ => card_tails_le (hM v) hY
  have hval : ∀ v, (2 * z + 1) / monoVal τl v = z * ((2 + 1 / z) * ∏ i, (τl i)⁻¹ ^ v i) := by
    intro v
    unfold monoVal
    rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
    simp_rw [inv_pow]
    field_simp
  have htot := RowWeights.row_weight_high_total hk hXm hz hcond hτl
    (fun v => (2 + 1 / z) * ∏ i, (τl i)⁻¹ ^ v i) (fun v => le_rfl) K
  have hVsum : ∑ v ∈ V, (2 + 1 / z) * ∏ i, (τl i)⁻¹ ^ v i ≤
      ∑ k' ∈ Icc k K, ∑ v ∈ Finset.Nat.antidiagonalTuple π k',
        (2 + 1 / z) * ∏ i, (τl i)⁻¹ ^ v i := by
    rw [hV, Finset.sum_biUnion]
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hva hvb
    rw [Finset.Nat.mem_antidiagonalTuple] at hva hvb
    exact hab (hva.symm.trans hvb)
  calc ((admHigh π k K τl (2 * z + 1)).card : ℝ) ≤ ∑ v ∈ V, (2 * z + 1) / monoVal τl v := hfib'
    _ = z * ∑ v ∈ V, (2 + 1 / z) * ∏ i, (τl i)⁻¹ ^ v i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => hval v
    _ ≤ z * (3 * (Real.exp 1 * (π + k) / k) ^ k * Xm⁻¹ ^ k) :=
        mul_le_mul_of_nonneg_left (hVsum.trans htot) hz0.le

end RankFull
