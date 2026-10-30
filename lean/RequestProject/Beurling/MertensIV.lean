module

public import Mathlib

/-!
# Lemma 5.1(iv): Mertens' second estimate from the first, by partial summation

Let `P` be any finite family of (Beurling) primes `p_i > 1`, and
`S_p(v) = ∑_{p_i ≤ v} log p_i / p_i`. If `E_p(v) := S_p(v) - log v ∈ [m, M']` for
`v ∈ [y, x]`, with `2 ≤ y ≤ x`, then

  `|∑_{y < p_i ≤ x} 1/p_i - log (log x / log y)| ≤ (M' - m) / log y`.

With `m = -1.77`, `M' = 0.43` (Lemma 5.1(iii)) this is Lemma 5.1(iv), with `K' = 2.20`.

The proof is the paper's: partial summation
`∑_{y<p≤x} 1/p = S_p(x)/log x - S_p(y)/log y + ∫_y^x S_p(v) dv/(v log² v)`, then
`S_p = log + E_p`.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral Finset

namespace MertensIV

/-- The kernel `1/(v log² v)`. -/
noncomputable def g (v : ℝ) : ℝ := 1 / (v * (Real.log v) ^ 2)

lemma g_nonneg {v : ℝ} (hv : 1 < v) : 0 ≤ g v := by
  unfold g; have := Real.log_pos hv; have : 0 < v := by linarith
  positivity

lemma continuousOn_g {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : ContinuousOn g (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  unfold g
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun v hv => by simp; linarith [hv.1])
  · intro v hv
    have : 0 < Real.log v := Real.log_pos (by linarith [hv.1])
    have : 0 < v := by linarith [hv.1]
    positivity

lemma hasDerivAt_neg_inv_log {v : ℝ} (hv : 1 < v) :
    HasDerivAt (fun w => -(Real.log w)⁻¹) (g v) v := by
  have h1 : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log (by linarith)
  have hl : Real.log v ≠ 0 := (Real.log_pos hv).ne'
  have h2 := (h1.inv hl).neg
  convert! h2 using 1
  unfold g; field_simp

lemma integral_g {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ v in a..b, g v = 1 / Real.log a - 1 / Real.log b := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun w => -(Real.log w)⁻¹)]
  · ring
  · intro v hv
    rw [Set.uIcc_of_le hab] at hv
    exact hasDerivAt_neg_inv_log (by linarith [hv.1])
  · exact (continuousOn_g ha hab).intervalIntegrable

lemma continuousOn_log_mul_g {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun v => Real.log v * g v) (Set.uIcc a b) := by
  apply ContinuousOn.mul _ (continuousOn_g ha hab)
  rw [Set.uIcc_of_le hab]
  exact Real.continuousOn_log.mono (fun v hv => by simp; linarith [hv.1])

lemma integral_log_mul_g {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ v in a..b, Real.log v * g v = Real.log (Real.log b) - Real.log (Real.log a) := by
  rw [integral_eq_sub_of_hasDerivAt (f := fun w => Real.log (Real.log w))]
  · intro v hv
    rw [Set.uIcc_of_le hab] at hv
    have hv1 : 1 < v := by linarith [hv.1]
    have hl : Real.log v ≠ 0 := (Real.log_pos hv1).ne'
    have h1 : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log (by linarith)
    have h2 := h1.log hl
    convert! h2 using 1
    unfold g; field_simp
  · exact (continuousOn_log_mul_g ha hab).intervalIntegrable

lemma intervalIntegrable_indicator_g (p : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable ((Set.Ici p).indicator g) volume a b := by
  rw [intervalIntegrable_iff]
  exact ((intervalIntegrable_iff.mp (continuousOn_g ha hab).intervalIntegrable)).indicator
    measurableSet_Ici

lemma integral_indicator_g (p : ℝ) {y x : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    ∫ v in y..x, (Set.Ici p).indicator g v =
      if p ≤ y then 1 / Real.log y - 1 / Real.log x
      else if p ≤ x then 1 / Real.log p - 1 / Real.log x else 0 := by
  by_cases h1 : p ≤ y
  · rw [if_pos h1, ← integral_g hy hyx]
    apply integral_congr
    intro v hv
    rw [Set.uIcc_of_le hyx] at hv
    simp [show p ≤ v by linarith [hv.1]]
  · rw [if_neg h1]
    push_neg at h1
    by_cases h2 : p ≤ x
    · rw [if_pos h2]
      rw [← integral_add_adjacent_intervals (b := p)
        (intervalIntegrable_indicator_g p hy h1.le)
        (intervalIntegrable_indicator_g p (by linarith) h2)]
      have e1 : ∫ v in y..p, (Set.Ici p).indicator g v = 0 := by
        rw [← intervalIntegral.integral_zero (a := y) (b := p) (μ := volume)]
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ p := by rw [ae_iff]; simp
        filter_upwards [hne] with v hv hmem
        rw [Set.uIoc_of_le h1.le] at hmem
        have : v < p := lt_of_le_of_ne hmem.2 hv
        simp [not_le.mpr this]
      have e2 : ∫ v in p..x, (Set.Ici p).indicator g v = ∫ v in p..x, g v := by
        apply integral_congr
        intro v hv
        rw [Set.uIcc_of_le h2] at hv
        simp [hv.1]
      rw [e1, e2, integral_g (by linarith) h2]; ring
    · rw [if_neg h2]
      push_neg at h2
      rw [← intervalIntegral.integral_zero (a := y) (b := x) (μ := volume)]
      apply integral_congr
      intro v hv
      rw [Set.uIcc_of_le hyx] at hv
      simp [not_le.mpr (show v < p by linarith [hv.2])]

variable {ι : Type*} (P : Finset ι) (pv : ι → ℝ)

/-- `S_p(v) = ∑_{p ≤ v} log p / p`. -/
noncomputable def Sp (v : ℝ) : ℝ :=
  ∑ i ∈ P, if pv i ≤ v then Real.log (pv i) / pv i else 0

lemma Sp_mul_g (v : ℝ) :
    Sp P pv v * g v = ∑ i ∈ P, Real.log (pv i) / pv i * (Set.Ici (pv i)).indicator g v := by
  unfold Sp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : pv i ≤ v <;> simp [h]

lemma intervalIntegrable_Sp_g {y x : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    IntervalIntegrable (fun v => Sp P pv v * g v) volume y x := by
  have : (fun v => Sp P pv v * g v) =
      ∑ i ∈ P, fun v => Real.log (pv i) / pv i * (Set.Ici (pv i)).indicator g v := by
    funext v; rw [Sp_mul_g]; simp
  rw [this]
  exact IntervalIntegrable.sum P (fun i _ =>
    (intervalIntegrable_indicator_g (pv i) hy hyx).const_mul _)

/-- Partial summation. -/
lemma partial_summation (hp : ∀ i ∈ P, 1 < pv i) {y x : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    ∑ i ∈ P.filter (fun i => y < pv i ∧ pv i ≤ x), 1 / pv i =
      Sp P pv x / Real.log x - Sp P pv y / Real.log y + ∫ v in y..x, Sp P pv v * g v := by
  have hI : ∫ v in y..x, Sp P pv v * g v =
      ∑ i ∈ P, Real.log (pv i) / pv i * (if pv i ≤ y then 1 / Real.log y - 1 / Real.log x
        else if pv i ≤ x then 1 / Real.log (pv i) - 1 / Real.log x else 0) := by
    simp_rw [Sp_mul_g]
    rw [intervalIntegral.integral_finset_sum (fun i _ =>
      (intervalIntegrable_indicator_g (pv i) hy hyx).const_mul _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul, integral_indicator_g (pv i) hy hyx]
  rw [hI, Finset.sum_filter]
  unfold Sp
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hpi := hp i hi
  have hlog : 0 < Real.log (pv i) := Real.log_pos hpi
  by_cases h1 : pv i ≤ y
  · have h2 : pv i ≤ x := le_trans h1 hyx
    rw [if_neg (fun h => absurd h.1 (not_lt.mpr h1)), if_pos h2, if_pos h1, if_pos h1]
    ring
  · push_neg at h1
    by_cases h2 : pv i ≤ x
    · rw [if_pos ⟨h1, h2⟩, if_pos h2, if_neg (not_le.mpr h1), if_neg (not_le.mpr h1),
        if_pos h2]
      field_simp
      ring
    · rw [if_neg (fun h => h2 h.2), if_neg h2, if_neg (not_le.mpr h1), if_neg (not_le.mpr h1),
        if_neg h2]
      ring

/-- **Lemma 5.1(iv)** (abstract form): if `E_p = S_p - log ∈ [m, M']` on `[y, x]`, then
`|∑_{y<p≤x} 1/p - log(log x / log y)| ≤ (M' - m)/log y`. -/
theorem mertens_iv (hp : ∀ i ∈ P, 1 < pv i) {m M y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (hE : ∀ v ∈ Set.Icc y x, m ≤ Sp P pv v - Real.log v ∧ Sp P pv v - Real.log v ≤ M) :
    |∑ i ∈ P.filter (fun i => y < pv i ∧ pv i ≤ x), 1 / pv i -
      Real.log (Real.log x / Real.log y)| ≤ (M - m) / Real.log y := by
  have hy1 : 1 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlxy : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
  set a := 1 / Real.log y with ha
  set b := 1 / Real.log x with hb
  have hb0 : 0 < b := by positivity
  have hba : b ≤ a := one_div_le_one_div_of_le hly hlxy
  set E : ℝ → ℝ := fun v => Sp P pv v - Real.log v with hEdef
  -- the integral of `E g`
  have hint1 := intervalIntegrable_Sp_g P pv hy1 hyx
  have hint2 := (continuousOn_log_mul_g hy1 hyx).intervalIntegrable (μ := volume)
  have hintE : IntervalIntegrable (fun v => E v * g v) volume y x := by
    have : (fun v => E v * g v) = fun v => Sp P pv v * g v - Real.log v * g v := by
      funext v; simp only [hEdef]; ring
    rw [this]; exact hint1.sub hint2
  have hJ : ∫ v in y..x, Sp P pv v * g v =
      (∫ v in y..x, E v * g v) + (Real.log (Real.log x) - Real.log (Real.log y)) := by
    rw [← integral_log_mul_g hy1 hyx, ← intervalIntegral.integral_add hintE hint2]
    apply integral_congr
    intro v _
    simp only [hEdef]; ring
  have hgint : IntervalIntegrable g volume y x := (continuousOn_g hy1 hyx).intervalIntegrable
  have hJlo : m * (a - b) ≤ ∫ v in y..x, E v * g v := by
    have : ∫ v in y..x, m * g v = m * (a - b) := by
      rw [intervalIntegral.integral_const_mul, integral_g hy1 hyx]
    rw [← this]
    apply intervalIntegral.integral_mono_on hyx (hgint.const_mul m) hintE
    intro v hv
    exact mul_le_mul_of_nonneg_right (hE v hv).1 (g_nonneg (by linarith [hv.1]))
  have hJhi : ∫ v in y..x, E v * g v ≤ M * (a - b) := by
    have : ∫ v in y..x, M * g v = M * (a - b) := by
      rw [intervalIntegral.integral_const_mul, integral_g hy1 hyx]
    rw [← this]
    apply intervalIntegral.integral_mono_on hyx hintE (hgint.const_mul M)
    intro v hv
    exact mul_le_mul_of_nonneg_right (hE v hv).2 (g_nonneg (by linarith [hv.1]))
  rw [partial_summation P pv hp hy1 hyx, hJ,
    Real.log_div hlx.ne' hly.ne']
  have hx := hE x ⟨hyx, le_rfl⟩
  have hyy := hE y ⟨le_rfl, hyx⟩
  have e1 : Sp P pv x / Real.log x = E x * b + 1 := by
    simp only [hEdef, hb]; field_simp; ring
  have e2 : Sp P pv y / Real.log y = E y * a + 1 := by
    simp only [hEdef, ha]; field_simp; ring
  rw [e1, e2]
  have k1 : m * b ≤ E x * b := mul_le_mul_of_nonneg_right hx.1 hb0.le
  have k2 : E x * b ≤ M * b := mul_le_mul_of_nonneg_right hx.2 hb0.le
  have k3 : m * a ≤ E y * a := mul_le_mul_of_nonneg_right hyy.1 (by positivity)
  have k4 : E y * a ≤ M * a := mul_le_mul_of_nonneg_right hyy.2 (by positivity)
  rw [show (M - m) / Real.log y = (M - m) * a by rw [ha]; ring]
  rw [abs_le]
  constructor <;> nlinarith

/-- Lemma 5.1(iv) with the constants of Lemma 5.1(iii): if `-1.77 ≤ S_p(v) - log v ≤ 0.43` on
`[y, x]`, then `|∑_{y<p≤x} 1/p - log(log x / log y)| ≤ 2.20 / log y`. -/
theorem mertens_iv_explicit (hp : ∀ i ∈ P, 1 < pv i) {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (hE : ∀ v ∈ Set.Icc y x, -1.77 ≤ Sp P pv v - Real.log v ∧ Sp P pv v - Real.log v ≤ 0.43) :
    |∑ i ∈ P.filter (fun i => y < pv i ∧ pv i ≤ x), 1 / pv i -
      Real.log (Real.log x / Real.log y)| ≤ 2.20 / Real.log y := by
  have := mertens_iv P pv hp hy hyx hE
  norm_num at this ⊢
  exact this

end MertensIV
