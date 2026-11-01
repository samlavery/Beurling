module

public import RequestProject.Beurling.Covers

/-!
# Lemma 6.21(ii): the numerical bookkeeping of the type union

In the proof of Lemma 6.21(ii), with `L = log z ≥ 60`, `Λ ≥ 10⁸`, `θ = 1 + 1/Λ` and the window
length `δ = 2 δ₁ = 4 L^{-6}`, the factors of `Σ̄_s` are distributed over the rows:

* `TypeUnion.cover_row_const_le` : a row of `C` costs at most `θ δ C'` with
  `C' = 2 · eD · e · Ch · B² ≤ 6 L^{5.1}`, given `D ≤ L`, `Ch ≤ 2L`, `B ≤ 2.1 L^{1.02}`;
* `TypeUnion.R_row_cost_le` : a row of `R` costs at most
  `θ δ · 2 · eD · κ (1 + κλ) · w_y ≤ 8 e θ L^{-3} w_y ≤ w_y`, given `D, κ, 1 + κλ ≤ L`;
* `TypeUnion.type_union_bound` : `(2z/δ + 1)(θ δ C')^κ ∏ w_y ≤ 13 L^{5.1} z ∏ w_y` for `κ ≥ 1`.

and the proof of Lemma 6.21(iii):

* `TypeUnion.prod_weights_le` : `∏_{y∈R} w_y ≤ w^{1+j}` when all `w_y ≤ w ≤ 1` and `|R| ≥ 1 + j`;
* `TypeUnion.consequence` : under (80), `r₀ · 13 L^{5.1} z ∏_{y∈R} w_y ≤ L^{-3}`.
-/

@[expose] public section

open Real

namespace TypeUnion

lemma exp_two_le : Real.exp 2 ≤ 7.39 := by
  have := Real.exp_one_lt_d9
  have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (by positivity) this.le 2
    _ ≤ 7.39 := by norm_num

/-- `C' = 2 · eD · e · Ch · B² ≤ 6 L^{5.1}` for `L ≥ 60`, when `D ≤ L`, `0 ≤ Ch ≤ 2L` and
`0 ≤ B ≤ 2.1 L^{1.02}`. -/
theorem cover_row_const_le {L D Ch B : ℝ} (hL : 60 ≤ L) (hD : D ≤ L)
    (hCh0 : 0 ≤ Ch) (hCh : Ch ≤ 2 * L) (hB0 : 0 ≤ B) (hB : B ≤ 2.1 * L ^ (1.02 : ℝ)) :
    2 * (Real.exp 1 * D) * Real.exp 1 * Ch * B ^ 2 ≤ 6 * L ^ (5.1 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have he := exp_two_le
  have hee : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hB2 : B ^ 2 ≤ 4.41 * L ^ (2.04 : ℝ) := by
    have : B ^ 2 ≤ (2.1 * L ^ (1.02 : ℝ)) ^ 2 := pow_le_pow_left₀ hB0 hB 2
    have e : (2.1 * L ^ (1.02 : ℝ)) ^ 2 = 4.41 * L ^ (2.04 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1.02 : ℝ)), ← Real.rpow_mul hL0.le]; norm_num
    linarith
  have hsplit : L ^ (5.1 : ℝ) = L * L * L ^ (2.04 : ℝ) * L ^ (1.06 : ℝ) := by
    have h2 : L * L = L ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    rw [h2, ← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
  have h106 : L ≤ L ^ (1.06 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one L]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hp : 0 ≤ L ^ (2.04 : ℝ) := by positivity
  have hp' : 0 ≤ Real.exp 2 := (Real.exp_pos _).le
  calc 2 * (Real.exp 1 * D) * Real.exp 1 * Ch * B ^ 2
      = 2 * Real.exp 2 * D * Ch * B ^ 2 := by rw [← hee]; ring
    _ ≤ 2 * Real.exp 2 * L * (2 * L) * (4.41 * L ^ (2.04 : ℝ)) := by
        apply mul_le_mul _ hB2 (by positivity) (by positivity)
        apply mul_le_mul _ hCh hCh0 (by positivity)
        exact mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ 2 * 7.39 * L * (2 * L) * (4.41 * L ^ (2.04 : ℝ)) := by
        have : 0 ≤ L * (2 * L) * (4.41 * L ^ (2.04 : ℝ)) := by positivity
        nlinarith
    _ = 130.3596 * (L * L * L ^ (2.04 : ℝ)) := by ring
    _ ≤ 6 * L ^ (5.1 : ℝ) := by
        rw [hsplit]
        have : 0 ≤ L * L * L ^ (2.04 : ℝ) := by positivity
        nlinarith

/-- A row of `R` costs at most `θ δ · 2 · eD · κ (1 + κλ) ≤ 8 e θ L^{-3} ≤ 1` (times `w_y`), for
`L ≥ 60`, `θ = 1 + 1/Λ` with `Λ ≥ 10⁸`, `δ = 4 L^{-6}`, and `0 ≤ D, κ, 1 + κλ ≤ L`. -/
theorem R_row_cost_le {L Λ D κ μ : ℝ} (hL : 60 ≤ L) (hΛ : 10 ^ 8 ≤ Λ) (hD0 : 0 ≤ D)
    (hD : D ≤ L) (hκ0 : 0 ≤ κ) (hκ : κ ≤ L) (hμ0 : 0 ≤ μ) (hμ : μ ≤ L) :
    (1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) * 2 * (Real.exp 1 * D) * κ * μ ≤ 1 := by
  have hL0 : 0 < L := by linarith
  have hθ : 1 + 1 / Λ ≤ 2 := by
    have : 1 / Λ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hL6 : L ^ (-6 : ℝ) = (L ^ 6)⁻¹ := by
    rw [Real.rpow_neg hL0.le]; norm_cast
  rw [hL6]
  have hDκμ : D * κ * μ ≤ L * L * L := by
    apply mul_le_mul (mul_le_mul hD hκ hκ0 (by linarith)) hμ hμ0 (by positivity)
  have h6 : (0 : ℝ) < L ^ 6 := by positivity
  have hθ0 : 0 ≤ 1 + 1 / Λ := by
    have : 0 ≤ 1 / Λ := by positivity
    linarith
  calc (1 + 1 / Λ) * (4 * (L ^ 6)⁻¹) * 2 * (Real.exp 1 * D) * κ * μ
      = (1 + 1 / Λ) * Real.exp 1 * 8 * (D * κ * μ) / L ^ 6 := by field_simp; ring
    _ ≤ 2 * 3 * 8 * (L * L * L) / L ^ 6 := by
        apply div_le_div_of_nonneg_right _ h6.le
        have : 0 ≤ D * κ * μ := by positivity
        have h1 : (1 + 1 / Λ) * Real.exp 1 ≤ 2 * 3 :=
          mul_le_mul hθ he (Real.exp_pos 1).le (by norm_num)
        have : 0 ≤ (1 + 1 / Λ) * Real.exp 1 := by positivity
        calc (1 + 1 / Λ) * Real.exp 1 * 8 * (D * κ * μ)
            ≤ (2 * 3) * 8 * (L * L * L) := by
              apply mul_le_mul (by linarith) hDκμ (by positivity) (by norm_num)
          _ = 2 * 3 * 8 * (L * L * L) := by ring
    _ ≤ 1 := by
        rw [div_le_one h6]
        have : 216000 ≤ L * L * L := by
          have := mul_le_mul (mul_le_mul hL hL (by norm_num) hL0.le) hL (by norm_num)
            (by positivity)
          linarith
        have : L ^ 6 = (L * L * L) * (L * L * L) := by ring
        nlinarith

/-- **Lemma 6.21(ii)**, the final step: with `L ≥ 60`, `z = e^L`, `δ = 4 L^{-6}`,
`θ = 1 + 1/Λ` (`Λ ≥ 10⁸`), `0 ≤ C' ≤ 6 L^{5.1}`, `κ ≥ 1` and `W = ∏_{y∈R} w_y ≥ 0`,
`(2z/δ + 1)(θ δ C')^κ W ≤ 13 L^{5.1} z W`. -/
theorem type_union_bound {L Λ C' W : ℝ} (hL : 60 ≤ L) (hΛ : 10 ^ 8 ≤ Λ) (hC0 : 0 ≤ C')
    (hC : C' ≤ 6 * L ^ (5.1 : ℝ)) {κ : ℕ} (hκ : 1 ≤ κ) (hW : 0 ≤ W) :
    (2 * Real.exp L / (4 * L ^ (-6 : ℝ)) + 1) *
        ((1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) * C') ^ κ * W ≤
      13 * L ^ (5.1 : ℝ) * Real.exp L * W := by
  have hL0 : 0 < L := by linarith
  set δ := 4 * L ^ (-6 : ℝ) with hδ
  set θ := 1 + 1 / Λ with hθdef
  have hδ0 : 0 < δ := by positivity
  have hθ0 : 1 ≤ θ := by
    have : 0 ≤ 1 / Λ := by positivity
    linarith
  have hθ1 : θ ≤ 1.00000001 := by
    have : 1 / Λ ≤ 1 / 10 ^ 8 := one_div_le_one_div_of_le (by norm_num) hΛ
    have : (1 : ℝ) / 10 ^ 8 = 0.00000001 := by norm_num
    linarith
  -- `x := θ δ C' ≤ 1`
  have h59 : L ^ (5.1 : ℝ) * L ^ (-6 : ℝ) = L ^ (-0.9 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h09 : 25 ≤ L ^ (0.9 : ℝ) := by
    have h1 : (L ^ (0.9 : ℝ)) ^ (10 : ℕ) = L ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast]; norm_num
    have h2 : (25 : ℝ) ^ (10 : ℕ) ≤ (L ^ (0.9 : ℝ)) ^ (10 : ℕ) := by
      rw [h1]
      calc (25 : ℝ) ^ (10 : ℕ) ≤ 60 ^ 9 := by norm_num
        _ ≤ L ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp h2
  have hneg : L ^ (-0.9 : ℝ) = (L ^ (0.9 : ℝ))⁻¹ := Real.rpow_neg hL0.le _
  have hx0 : 0 ≤ θ * δ * C' := by positivity
  have hx1 : θ * δ * C' ≤ 1 := by
    calc θ * δ * C' ≤ θ * δ * (6 * L ^ (5.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = 24 * θ * L ^ (-0.9 : ℝ) := by rw [hδ, ← h59]; ring
      _ ≤ 1 := by
          rw [hneg]
          have hp : 0 < L ^ (0.9 : ℝ) := by positivity
          rw [← div_eq_mul_inv, div_le_one hp]
          linarith
  have hxk : (θ * δ * C') ^ κ ≤ θ * δ * C' := by
    calc (θ * δ * C') ^ κ ≤ (θ * δ * C') ^ 1 := pow_le_pow_of_le_one hx0 hx1 hκ
      _ = θ * δ * C' := pow_one _
  -- `δ ≤ 0.001 ≤ 0.001 z`
  have hz : 1 ≤ Real.exp L := Real.one_le_exp hL0.le
  have hδs : δ ≤ 0.001 * Real.exp L := by
    have hL6 : L ^ (-6 : ℝ) = (L ^ 6)⁻¹ := by rw [Real.rpow_neg hL0.le]; norm_cast
    have : (60 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
    have h1 : (L ^ 6)⁻¹ ≤ ((60 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by norm_num) this
    have : δ ≤ 0.001 := by rw [hδ, hL6]; norm_num at h1 ⊢; linarith
    linarith
  have hpow : 0 ≤ L ^ (5.1 : ℝ) := by positivity
  calc (2 * Real.exp L / δ + 1) * (θ * δ * C') ^ κ * W
      ≤ (2 * Real.exp L / δ + 1) * (θ * δ * C') * W := by
        apply mul_le_mul_of_nonneg_right _ hW
        exact mul_le_mul_of_nonneg_left hxk (by positivity)
    _ = (2 * Real.exp L + δ) * θ * C' * W := by field_simp
    _ ≤ (2 * Real.exp L + 0.001 * Real.exp L) * 1.00000001 * (6 * L ^ (5.1 : ℝ)) * W := by
        apply mul_le_mul_of_nonneg_right _ hW
        apply mul_le_mul _ hC hC0 (by positivity)
        apply mul_le_mul (by linarith) hθ1 (by linarith) (by positivity)
    _ ≤ 13 * L ^ (5.1 : ℝ) * Real.exp L * W := by
        apply mul_le_mul_of_nonneg_right _ hW
        have : 0 ≤ L ^ (5.1 : ℝ) * Real.exp L := by positivity
        nlinarith

/-- `∏_{y∈R} w_y ≤ w^{|R|} ≤ w^{1+j}` when `0 ≤ w_y ≤ w ≤ 1` on `R` and `|R| ≥ 1 + j`. -/
theorem prod_weights_le {α : Type*} {R : Finset α} (wy : α → ℝ) {w : ℝ} {j : ℕ}
    (h0 : ∀ y ∈ R, 0 ≤ wy y) (hw : ∀ y ∈ R, wy y ≤ w) (hw1 : w ≤ 1) (hR : j + 1 ≤ R.card) :
    ∏ y ∈ R, wy y ≤ w ^ (1 + j) := by
  obtain ⟨y0, hy0⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
  have hw0 : 0 ≤ w := (h0 y0 hy0).trans (hw y0 hy0)
  calc ∏ y ∈ R, wy y ≤ ∏ _y ∈ R, w := Finset.prod_le_prod₀ h0 hw
    _ = w ^ R.card := Finset.prod_const w
    _ ≤ w ^ (1 + j) := pow_le_pow_of_le_one hw0 hw1 (by omega)

/-- **Lemma 6.21(iii)** (consequence): with `L ≥ 60`, `z = e^L`, `r₀ ≤ L`, `0 < w ≤ 1`, a
configuration with `|R| ≥ 1 + j` rows, all of weight `w_y ≤ w`, has
`r₀ · 13 L^{5.1} z ∏_{y∈R} w_y ≤ L^{-3}` as soon as (80) `(1 + j) log(1/w) ≥ L + 10ℓ + 10`. -/
theorem consequence {α : Type*} {R : Finset α} (wy : α → ℝ) {L w r0 : ℝ} {j : ℕ}
    (hL : 60 ≤ L) (hr00 : 0 ≤ r0) (hr0 : r0 ≤ L) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (h0 : ∀ y ∈ R, 0 ≤ wy y) (hw : ∀ y ∈ R, wy y ≤ w) (hR : j + 1 ≤ R.card)
    (h80 : L + 10 * Real.log L + 10 ≤ (1 + j) * Real.log (1 / w)) :
    r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) * ∏ y ∈ R, wy y ≤ L ^ (-3 : ℝ) := by
  have hp := prod_weights_le wy h0 hw hw1 hR
  have hc : 0 ≤ r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) := by positivity
  calc r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) * ∏ y ∈ R, wy y
      ≤ r0 * (13 * L ^ (5.1 : ℝ) * Real.exp L) * w ^ (1 + j) :=
        mul_le_mul_of_nonneg_left hp hc
    _ ≤ L ^ (-3 : ℝ) := Covers.union_bound_le hL hw0 hr0 j h80

end TypeUnion
