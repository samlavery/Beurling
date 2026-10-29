module

public import RequestProject.Beurling.RankFull.PatternSum

/-!
# Lemma 6.21(ii): the sum over the exponents (s3)

In the proof of Lemma 6.21(ii), the skeleton datum (s3) is the matrix of exponents of the `r`
pivots in the `κ` rows of the cover `C` (rows are indexed by their pivots; the `i`-th pivot is
matched to the `i`-th row). The constraints (`ExOK`): the exponent of the `i`-th pivot in its own
row is `≥ 1` if that row is in `C`, and every pivot occurs in some row of `C` (`C` is a cover);
entries in rows outside `C` are not part of (s3) and are set to `0`. The weight of the pivot
exponents in `Σ̄_𝔰` is `∏_i τ_i^{-e_i}`, `e_i = (column sum over C) - 1`. The paper:

"if the `i`-th pivot is matched to a row of `C` … the sum of `τ_i^{-e_i}` over its exponents in the
`κ` rows of `C` is `(1 - 1/τ_i)^{-κ}`. If it is matched to a row of `R` … the sum is
`τ_i((1 - 1/τ_i)^{-κ} - 1) ≤ κ (1 - 1/τ_i)^{-κ-1}`."

* `RankFull.sum_s3_le` : `∑_{(s3)} ∏_i τ_i^{-e_i} ≤ κ^{|R|} ∏_i (1 - 1/τ_i)^{-(κ+1)}`.
-/

@[expose] public section

open Finset
open scoped ENNReal Classical

namespace RankFull

variable {r : ℕ}

/-- The constraints on the `i`-th column `v` of the (s3) exponent matrix. -/
def ColOK (C : Finset (Fin r)) (i : Fin r) (v : Fin r → ℕ) : Prop :=
  (∀ y, y ∉ C → v y = 0) ∧ (i ∈ C → 1 ≤ v i) ∧ (∃ y ∈ C, 1 ≤ v y)

/-- The constraints of (s3) on the exponent matrix `ex y i` (row `y`, pivot `i`). -/
def ExOK (C : Finset (Fin r)) (ex : Fin r → Fin r → ℕ) : Prop :=
  ∀ i, ColOK C i (fun y => ex y i)

lemma tsum_shift_geom (x : ℝ≥0∞) :
    ∑' n : ℕ, (if 1 ≤ n then x ^ (n - 1) else 0) = (1 - x)⁻¹ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h : ∀ n : ℕ, (if 1 ≤ n + 1 then x ^ (n + 1 - 1) else 0) = x ^ n := fun n => by
    rw [if_pos (by omega), Nat.add_sub_cancel]
  rw [if_neg (by omega), zero_add]
  simp_rw [h]
  exact ENNReal.tsum_geometric x

lemma tsum_indicator_zero : ∑' n : ℕ, (if n = 0 then (1 : ℝ≥0∞) else 0) = 1 := by
  rw [tsum_ite_eq]

/-- The column sum for a pivot matched to a row of `C`: at most `(1 - x)^{-κ}`. -/
lemma col_in {C : Finset (Fin r)} {i : Fin r} (hi : i ∈ C) (x : ℝ≥0∞) :
    ∑' v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0) ≤ (1 - x)⁻¹ ^ C.card := by
  classical
  let φ : Fin r → ℕ → ℝ≥0∞ := fun y n =>
    if y = i then (if 1 ≤ n then x ^ (n - 1) else 0)
    else if y ∈ C then x ^ n else (if n = 0 then 1 else 0)
  have hpt : ∀ v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0) ≤
      ∏ y, φ y (v y) := by
    intro v
    split_ifs with hv
    · obtain ⟨hz, hd, -⟩ := hv
      have hvi := hd hi
      rw [← Finset.mul_prod_erase univ (fun y => φ y (v y)) (Finset.mem_univ i)]
      have h1 : φ i (v i) = x ^ (v i - 1) := by simp [φ, hvi]
      have h2 : ∀ y ∈ univ.erase i, φ y (v y) = x ^ v y := by
        intro y hy
        have hyi : y ≠ i := (Finset.mem_erase.mp hy).1
        by_cases hyC : y ∈ C
        · simp [φ, hyi, hyC]
        · simp [φ, hyi, hyC, hz y hyC]
      rw [h1, Finset.prod_congr rfl h2, Finset.prod_pow_eq_pow_sum, ← pow_add]
      apply le_of_eq
      congr 1
      rw [← Finset.add_sum_erase univ v (Finset.mem_univ i)]
      omega
    · exact zero_le _
  calc ∑' v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0)
      ≤ ∑' v : Fin r → ℕ, ∏ y, φ y (v y) := ENNReal.tsum_le_tsum hpt
    _ = ∏ y, ∑' n, φ y n := tsum_fin_pi_prod r φ
    _ = ∏ y, (if y ∈ C then (1 - x)⁻¹ else 1) := by
        refine Finset.prod_congr rfl fun y _ => ?_
        by_cases hyi : y = i
        · subst hyi; simp only [φ, if_true, hi]; exact tsum_shift_geom x
        · by_cases hyC : y ∈ C
          · simp only [φ, hyi, hyC, if_false, if_true]; exact ENNReal.tsum_geometric x
          · simp only [φ, hyi, hyC, if_false]; exact tsum_indicator_zero
    _ = (1 - x)⁻¹ ^ C.card := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- `x^{n-1} = x⁻¹ x^n` for `n ≥ 1`, `0 < x < ∞`. -/
lemma pow_pred_eq {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxt : x ≠ ⊤) {n : ℕ} (hn : 1 ≤ n) :
    x ^ (n - 1) = x⁻¹ * x ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, pow_one, ← mul_assoc, ENNReal.inv_mul_cancel hx0 hxt,
    one_mul]

/-- The column sum for a pivot matched to a row of `R`: at most `x⁻¹((1 - x)^{-κ} - 1)`. -/
lemma col_out {C : Finset (Fin r)} {i : Fin r} {x : ℝ≥0∞} (hx0 : x ≠ 0) (hxt : x ≠ ⊤) :
    ∑' v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0) ≤
      x⁻¹ * ((1 - x)⁻¹ ^ C.card - 1) := by
  classical
  let ψ : Fin r → ℕ → ℝ≥0∞ := fun y n => if y ∈ C then x ^ n else (if n = 0 then 1 else 0)
  let Ψ : (Fin r → ℕ) → ℝ≥0∞ := fun v => ∏ y, ψ y (v y)
  have hpt : ∀ v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0) ≤
      x⁻¹ * (if v = 0 then 0 else Ψ v) := by
    intro v
    split_ifs with hv hv0
    · obtain ⟨-, -, ⟨y, hyC, hy⟩⟩ := hv
      rw [hv0] at hy; simp at hy
    · obtain ⟨hz, -, ⟨y0, hy0C, hy0⟩⟩ := hv
      have hsum : 1 ≤ ∑ y, v y :=
        le_trans hy0 (Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ y0))
      rw [pow_pred_eq hx0 hxt hsum]
      apply le_of_eq
      congr 1
      simp only [Ψ, ψ]
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y _ => ?_
      by_cases hyC : y ∈ C
      · simp [hyC]
      · simp [hyC, hz y hyC]
    · exact zero_le _
    · exact zero_le _
  have hΨ : ∑' v, Ψ v = (1 - x)⁻¹ ^ C.card := by
    simp only [Ψ]
    rw [tsum_fin_pi_prod r ψ]
    have : ∀ y, ∑' n, ψ y n = if y ∈ C then (1 - x)⁻¹ else 1 := by
      intro y
      by_cases hyC : y ∈ C
      · simp only [ψ, hyC, if_true]; exact ENNReal.tsum_geometric x
      · simp only [ψ, hyC, if_false]; exact tsum_indicator_zero
    simp_rw [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hΨ0 : Ψ 0 = 1 := by
    simp only [Ψ, ψ, Pi.zero_apply, pow_zero, if_true]
    exact Finset.prod_eq_one fun y _ => by split_ifs <;> rfl
  have hsplit := ENNReal.tsum_eq_add_tsum_ite (f := Ψ) 0
  rw [hΨ0, hΨ] at hsplit
  calc ∑' v : Fin r → ℕ, (if ColOK C i v then x ^ ((∑ y, v y) - 1) else 0)
      ≤ ∑' v : Fin r → ℕ, x⁻¹ * (if v = 0 then 0 else Ψ v) := ENNReal.tsum_le_tsum hpt
    _ = x⁻¹ * ∑' v : Fin r → ℕ, (if v = 0 then 0 else Ψ v) := ENNReal.tsum_mul_left
    _ = x⁻¹ * ((1 - x)⁻¹ ^ C.card - 1) := by
        congr 1
        rw [hsplit, ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
        exact tsum_congr fun v => by by_cases h : v = 0 <;> simp [h]

/-- `u^κ - 1 ≤ κ (u - 1) u^κ` for `u ≥ 1`. -/
lemma pow_sub_one_le {u : ℝ} (hu : 1 ≤ u) : ∀ κ : ℕ, u ^ κ - 1 ≤ κ * (u - 1) * u ^ κ
  | 0 => by simp
  | κ + 1 => by
    have ih := pow_sub_one_le hu κ
    have h1 : 1 ≤ u ^ (κ + 1) := one_le_pow₀ hu
    have h2 : u ^ (κ + 1) = u * u ^ κ := by ring
    have hu0 : 0 ≤ u - 1 := by linarith
    push_cast
    have h3 : u * (u ^ κ - 1) ≤ u * (κ * (u - 1) * u ^ κ) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h4 : u - 1 ≤ (u - 1) * u ^ (κ + 1) := by nlinarith
    calc u ^ (κ + 1) - 1 = u * (u ^ κ - 1) + (u - 1) := by ring
      _ ≤ u * (κ * (u - 1) * u ^ κ) + (u - 1) * u ^ (κ + 1) := add_le_add h3 h4
      _ = (κ + 1) * (u - 1) * u ^ (κ + 1) := by rw [h2]; ring

/-- **The (s3) sum** of the proof of Lemma 6.21(ii): for `τ_i > 1`,
`∑_{(s3)} ∏_i τ_i^{-e_i} ≤ κ^{r-κ} ∏_i (1 - 1/τ_i)^{-(κ+1)}`, `κ = |C|`. -/
theorem sum_s3_le (C : Finset (Fin r)) (τ : Fin r → ℝ) (hτ : ∀ i, 1 < τ i) :
    ∑' ex : Fin r → Fin r → ℕ, (if ExOK C ex then
        ∏ i, ENNReal.ofReal ((τ i)⁻¹ ^ ((∑ y, ex y i) - 1)) else 0) ≤
      ENNReal.ofReal ((C.card : ℝ) ^ (r - C.card) *
        ∏ i, (1 - (τ i)⁻¹)⁻¹ ^ (C.card + 1)) := by
  classical
  set κ := C.card
  have hτ0 : ∀ i, 0 < (τ i)⁻¹ := fun i => inv_pos.mpr (by linarith [hτ i])
  have hτ1 : ∀ i, (τ i)⁻¹ < 1 := fun i => inv_lt_one_of_one_lt₀ (hτ i)
  set x : Fin r → ℝ≥0∞ := fun i => ENNReal.ofReal (τ i)⁻¹ with hx
  have hx0 : ∀ i, x i ≠ 0 := fun i => (ENNReal.ofReal_pos.mpr (hτ0 i)).ne'
  have hxt : ∀ i, x i ≠ ⊤ := fun i => ENNReal.ofReal_ne_top
  set u : Fin r → ℝ := fun i => (1 - (τ i)⁻¹)⁻¹ with hu
  have hu1 : ∀ i, 1 ≤ u i := fun i => one_le_inv₀ (by linarith [hτ1 i]) |>.mpr
    (by linarith [hτ0 i])
  have hgeo : ∀ i, (1 - x i)⁻¹ = ENNReal.ofReal (u i) := by
    intro i
    rw [hx, hu, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (hτ0 i).le,
      ENNReal.ofReal_inv_of_pos (by linarith [hτ1 i])]
  let g : Fin r → (Fin r → ℕ) → ℝ≥0∞ := fun i v =>
    if ColOK C i v then x i ^ ((∑ y, v y) - 1) else 0
  -- the summand is a product of column weights
  have hprod : ∀ ex : Fin r → Fin r → ℕ, (if ExOK C ex then
      ∏ i, ENNReal.ofReal ((τ i)⁻¹ ^ ((∑ y, ex y i) - 1)) else 0) =
      ∏ i, g i (fun y => ex y i) := by
    intro ex
    by_cases h : ExOK C ex
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [g, if_pos (h i), hx, ENNReal.ofReal_pow (hτ0 i).le]
    · rw [if_neg h]
      unfold ExOK at h
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hi])).symm
  have hcols : ∑' ex : Fin r → Fin r → ℕ, ∏ i, g i (fun y => ex y i) =
      ∏ i, ∑' v, g i v := by
    rw [← (Equiv.piComm (fun (_ : Fin r) (_ : Fin r) => ℕ)).symm.tsum_eq]
    exact tsum_fin_pi_prod (β := Fin r → ℕ) r g
  -- per-column bounds
  have hcol : ∀ i, ∑' v, g i v ≤
      ENNReal.ofReal ((if i ∈ C then 1 else (κ : ℝ)) * u i ^ (κ + 1)) := by
    intro i
    by_cases hi : i ∈ C
    · refine (col_in hi (x i)).trans ?_
      rw [hgeo i, ← ENNReal.ofReal_pow (by linarith [hu1 i]), if_pos hi, one_mul]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (hu1 i) (by omega))
    · refine (col_out (hx0 i) (hxt i)).trans ?_
      rw [hgeo i, if_neg hi, ← ENNReal.ofReal_pow (by linarith [hu1 i]),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ zero_le_one, hx]
      beta_reduce
      rw [← ENNReal.ofReal_inv_of_pos (hτ0 i), inv_inv, ← ENNReal.ofReal_mul (by linarith [hτ i])]
      apply ENNReal.ofReal_le_ofReal
      -- `τ (u^κ - 1) ≤ κ u^{κ+1}`
      have hτu : τ i * (u i - 1) = u i := by
        simp only [hu]
        have h1 : 1 - (τ i)⁻¹ ≠ 0 := by linarith [hτ1 i]
        have h2 : τ i ≠ 0 := by linarith [hτ i]
        have h3 : τ i - 1 ≠ 0 := by linarith [hτ i]
        rw [show 1 - (τ i)⁻¹ = (τ i - 1) / τ i by field_simp, inv_div]
        field_simp
        ring
      have hk := pow_sub_one_le (hu1 i) κ
      have hτp : 0 < τ i := by linarith [hτ i]
      calc τ i * (u i ^ κ - 1) ≤ τ i * (κ * (u i - 1) * u i ^ κ) :=
            mul_le_mul_of_nonneg_left hk hτp.le
        _ = κ * (τ i * (u i - 1)) * u i ^ κ := by ring
        _ = κ * u i ^ (κ + 1) := by rw [hτu, pow_succ]; ring
  calc ∑' ex : Fin r → Fin r → ℕ, (if ExOK C ex then
        ∏ i, ENNReal.ofReal ((τ i)⁻¹ ^ ((∑ y, ex y i) - 1)) else 0)
      = ∏ i, ∑' v, g i v := by rw [tsum_congr hprod, hcols]
    _ ≤ ∏ i, ENNReal.ofReal ((if i ∈ C then 1 else (κ : ℝ)) * u i ^ (κ + 1)) :=
        Finset.prod_le_prod' fun i _ => hcol i
    _ = ENNReal.ofReal (∏ i, ((if i ∈ C then 1 else (κ : ℝ)) * u i ^ (κ + 1))) := by
        rw [ENNReal.ofReal_prod_of_nonneg]
        intro i _
        have := hu1 i
        split_ifs <;> positivity
    _ = ENNReal.ofReal ((κ : ℝ) ^ (r - κ) * ∏ i, u i ^ (κ + 1)) := by
        congr 1
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
        congr 1
        rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
          Finset.card_univ, Fintype.card_fin, Finset.filter_mem_eq_inter, Finset.univ_inter]

end RankFull
