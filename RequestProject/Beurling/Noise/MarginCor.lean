module

public import Mathlib

/-!
# Corollary 5.40 (R1′ on every window), deterministic form

The pointwise margin density `m` of §5.3 (`m = T' - K^pt ρ̃ - NT_pt`) enters through two facts:

* **Proposition 5.38** in the form used by Corollary 5.40 (`PointwiseMargin m X₀`):
  `m(t) log t ≥ 0.399` for every `t ≥ X₀` (parts (a)–(c): `≥ 0.959` beyond `X₀^{1.01}`,
  `≥ 0.399` on `[2X₀, X₀^{1.01}]`, `≥ 0.73` on `[X₀, 2X₀)`), and `m = 0` on `[1, X₀)` (no slots
  below `X₀`);
* the **bookkeeping identity** of §5.3 for a window `I = [a, b)`:
  `ℓ_jit(I) - Comp(I) = ∫_I m ± 2` (`|ℓ - Comp - ∫_a^b m| ≤ 2`).

From these, for `L ≥ log t` on `I ∩ [X₀, ∞)`:

* `cor_5_40` : `ℓ_jit(I) - Comp(I) ≥ 0.399 |I ∩ [X₀, ∞)|/L - 2`;
* `cor_5_40_queue` : with `ℓ_jit(I) ≤ 1.01 |I ∩ [X₀, ∞)| + 1` and `L ≥ 1`,
  `Comp(I) ≤ ℓ_jit(I)(1 - c'/L) + K_d`, `c' = 0.15`, `K_d = 3` (the form of Theorem 6.6).

The windows are arbitrary: `I` may start below `X₀` and be of any length.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace Margin

/-- **Proposition 5.38 in the form used by Corollary 5.40**: `m(t) log t ≥ 0.399` for `t ≥ X₀`
(Proposition 5.38(a)–(c)), and `m = 0` below `X₀`. -/
structure PointwiseMargin (m : ℝ → ℝ) (X0 : ℝ) : Prop where
  ge : ∀ t, X0 ≤ t → 0.399 ≤ m t * Real.log t
  zero : ∀ t, t < X0 → m t = 0

lemma PointwiseMargin.nonneg {m : ℝ → ℝ} {X0 : ℝ} (h : PointwiseMargin m X0) (hX : 1 < X0)
    (t : ℝ) : 0 ≤ m t := by
  rcases lt_or_ge t X0 with ht | ht
  · rw [h.zero t ht]
  · have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have := h.ge t ht
    by_contra hneg
    push_neg at hneg
    nlinarith

lemma PointwiseMargin.ge_div {m : ℝ → ℝ} {X0 : ℝ} (h : PointwiseMargin m X0) (hX : 1 < X0)
    {L t : ℝ} (ht : X0 ≤ t) (hL : Real.log t ≤ L) : 0.399 / L ≤ m t := by
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hL0 : 0 < L := lt_of_lt_of_le hl hL
  have h1 := h.ge t ht
  have hm := h.nonneg hX t
  rw [div_le_iff₀ hL0]
  nlinarith

/-- The integral of the margin density over a window: `∫_a^b m ≥ 0.399 |[a,b) ∩ [X₀,∞)|/L`. -/
theorem integral_ge {m : ℝ → ℝ} {X0 : ℝ} (h : PointwiseMargin m X0) (hX : 1 < X0)
    {a b L : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, X0 ≤ t → t ≤ b → Real.log t ≤ L) (_hL0 : 0 < L) :
    0.399 * max (b - max a X0) 0 / L ≤ ∫ t in a..b, m t := by
  have hnn : ∀ x y, x ≤ y → IntervalIntegrable m volume x y → 0 ≤ ∫ t in x..y, m t :=
    fun x y hxy _ => intervalIntegral.integral_nonneg hxy fun t _ => h.nonneg hX t
  rcases le_or_gt b (max a X0) with hb | hb
  · rw [max_eq_right (by linarith), mul_zero, zero_div]
    exact hnn a b hab hm
  set c := max a X0
  have hac : a ≤ c := le_max_left _ _
  have hi1 : IntervalIntegrable m volume a c := hm.mono_set (by
    rw [Set.uIcc_of_le hac, Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc le_rfl hb.le)
  have hi2 : IntervalIntegrable m volume c b := hm.mono_set (by
    rw [Set.uIcc_of_le hb.le, Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc hac le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    max_eq_left (by linarith)]
  have h1 := hnn a c hac hi1
  have h2 : ∫ t in c..b, (0.399 / L) ≤ ∫ t in c..b, m t :=
    intervalIntegral.integral_mono_on hb.le _root_.intervalIntegrable_const hi2 fun t ht =>
      h.ge_div hX ((le_max_right a X0).trans ht.1) (hL t ((le_max_right a X0).trans ht.1) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have e : 0.399 * (b - c) / L = (b - c) * (0.399 / L) := by ring
  linarith

/-- **Corollary 5.40 (R1′ on every window)**, first inequality: for a window `[a, b)` with the
bookkeeping identity `ℓ_jit - Comp = ∫ m ± 2` and `L ≥ log t` on `[a,b) ∩ [X₀, ∞)`,
`ℓ_jit(I) - Comp(I) ≥ 0.399 |I ∩ [X₀, ∞)|/L - 2`. -/
theorem cor_5_40 {m : ℝ → ℝ} {X0 : ℝ} (h : PointwiseMargin m X0) (hX : 1 < X0)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, X0 ≤ t → t ≤ b → Real.log t ≤ L) (hL0 : 0 < L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2) :
    0.399 * max (b - max a X0) 0 / L - 2 ≤ ell - comp := by
  have := integral_ge h hX hab hm hL hL0
  have := (abs_le.mp hbook).1
  linarith

/-- **Corollary 5.40 in the form used in Theorem 6.6**: with moreover
`ℓ_jit(I) ≤ 1.01 |I ∩ [X₀, ∞)| + 1` and `L ≥ 1`, `Comp(I) ≤ ℓ_jit(I) (1 - c'/L) + K_d` with
`c' = 0.15`, `K_d = 3`. -/
theorem cor_5_40_queue {m : ℝ → ℝ} {X0 : ℝ} (h : PointwiseMargin m X0) (hX : 1 < X0)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, X0 ≤ t → t ≤ b → Real.log t ≤ L) (hL1 : 1 ≤ L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2)
    (hell : ell ≤ 1.01 * max (b - max a X0) 0 + 1) :
    comp ≤ ell * (1 - 0.15 / L) + 3 := by
  have hL0 : 0 < L := by linarith
  have hc := cor_5_40 h hX hab hm hL hL0 hbook
  set x := max (b - max a X0) 0
  have hx : 0 ≤ x := le_max_right _ _
  have hinv : 0.15 / L ≤ 0.15 := div_le_self (by norm_num) hL1
  have hinv0 : 0 ≤ 0.15 / L := by positivity
  -- `0.15 ℓ / L ≤ 0.15 (1.01 x + 1)/L ≤ 0.399 x / L + 0.15`
  have h1 : ell * (0.15 / L) ≤ (1.01 * x + 1) * (0.15 / L) :=
    mul_le_mul_of_nonneg_right hell hinv0
  have h2 : (1.01 * x + 1) * (0.15 / L) ≤ 0.399 * x / L + 0.15 := by
    have e : (1.01 * x + 1) * (0.15 / L) = 0.1515 * x / L + 0.15 / L := by ring
    have h3 : 0.1515 * x / L ≤ 0.399 * x / L :=
      div_le_div_of_nonneg_right (by nlinarith) hL0.le
    linarith
  nlinarith

end Margin

end
