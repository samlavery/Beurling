module

public import Mathlib

/-!
# Partial summation for weighted counting functions

For a countable family of points `t i ≥ 1` with weights `w i ≥ 0`, let
`W(x) = ∑_{t i ≤ x} w i` be the weighted counting function. If `W(x) ≤ K x^c`, then for
`Re s > max(c, 0)`

  `∑ᵢ w i * t i ^ (-s) = s * ∫_1^∞ W(x) x^(-s-1) dx`,

with absolute convergence. This is the partial summation step used for both `ζ_P` (with `W = N_P`)
and `-ζ_P'/ζ_P` (with `W = ψ_P`) in Remark 1.2 of the paper.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace AbelMellin

variable {ι : Type*}

/-- The weighted counting function `W(x) = ∑_{t i ≤ x} w i`. -/
noncomputable def cnt (t w : ι → ℝ) (x : ℝ) : ℝ := ∑' i, if t i ≤ x then w i else 0

/-- Standing hypotheses for partial summation with growth exponent `c`. -/
structure Hyp (t w : ι → ℝ) (c : ℝ) : Prop where
  one_le : ∀ i, 1 ≤ t i
  nonneg : ∀ i, 0 ≤ w i
  summable : ∀ x, Summable fun i => if t i ≤ x then w i else 0
  bound : ∃ K, ∀ x ≥ 1, cnt t w x ≤ K * x ^ c

variable {t w : ι → ℝ} {c : ℝ}

lemma cnt_nonneg (h : Hyp t w c) (x : ℝ) : 0 ≤ cnt t w x :=
  tsum_nonneg fun i => by split_ifs <;> simp [h.nonneg i]

lemma cnt_mono (h : Hyp t w c) : Monotone (cnt t w) := by
  intro x y hxy
  refine Summable.tsum_le_tsum (fun i => ?_) (h.summable x) (h.summable y)
  by_cases h1 : t i ≤ x
  · simp [h1, h1.trans hxy]
  · split_ifs <;> simp [h.nonneg i]

/-- Over `Ioi 1`, the integral of `g` restricted to `x ≥ T` (`T ≥ 1`) is the integral over
`Ioi T`. -/
lemma setIntegral_Ioi_one_ite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) {T : ℝ} (hT : 1 ≤ T) :
    ∫ x in Ioi 1, (if T ≤ x then g x else 0) = ∫ x in Ioi T, g x := by
  have : (fun x => if T ≤ x then g x else 0) = (Ici T).indicator g := by
    ext x; simp [Set.indicator, mem_Ici]
  rw [this, setIntegral_indicator measurableSet_Ici]
  rcases hT.lt_or_eq with h | h
  · rw [show Ioi 1 ∩ Ici T = Ici T by ext x; simp; intro hx; linarith]
    exact integral_Ici_eq_integral_Ioi
  · subst h
    rw [show Ioi 1 ∩ Ici 1 = Ioi (1:ℝ) by ext x; simp; intro hx; linarith]

lemma integral_ite_cpow {T : ℝ} (hT : 1 ≤ T) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi 1, (if T ≤ x then (x : ℂ) ^ (-s - 1) else 0) = (T : ℂ) ^ (-s) / s := by
  rw [setIntegral_Ioi_one_ite _ hT,
    integral_Ioi_cpow_of_lt (by simp; linarith) (by linarith)]
  rw [show -s - 1 + 1 = -s by ring, div_neg, neg_div, neg_neg]

lemma integral_ite_rpow {T : ℝ} (hT : 1 ≤ T) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi 1, (if T ≤ x then x ^ (-σ - 1) else 0) = T ^ (-σ) / σ := by
  rw [setIntegral_Ioi_one_ite _ hT, integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
  rw [show -σ - 1 + 1 = -σ by ring, div_neg, neg_div, neg_neg]

lemma lintegral_ite_rpow {T w σ : ℝ} (hT : 1 ≤ T) (hw : 0 ≤ w) (hσ : 0 < σ) :
    ∫⁻ x in Ioi 1, ENNReal.ofReal ((if T ≤ x then w else 0) * x ^ (-σ - 1)) =
      ENNReal.ofReal (w * T ^ (-σ) / σ) := by
  have e : ∀ x : ℝ, (if T ≤ x then w else 0) * x ^ (-σ - 1) =
      w * (if T ≤ x then x ^ (-σ - 1) else 0) := by
    intro x; split_ifs <;> simp
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul, integral_ite_rpow hT hσ,
    mul_div_assoc]
  · refine Integrable.const_mul ?_ w
    refine Integrable.mono' (g := fun x => x ^ (-σ - 1))
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
      ((Measurable.ite measurableSet_Ici (by fun_prop) measurable_const).aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) < x := hx
    have hx0 : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
    split_ifs <;> simp [abs_of_nonneg hx0, hx0]
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : (1:ℝ) < x := hx
    have hx0 : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
    simp only [Pi.zero_apply]
    split_ifs <;> positivity

lemma lintegral_cnt_lt_top (h : Hyp t w c) {σ : ℝ} (hσ : c < σ) :
    ∫⁻ x in Ioi 1, ENNReal.ofReal (cnt t w x * x ^ (-σ - 1)) < ⊤ := by
  obtain ⟨K, hb⟩ := h.bound
  have hint : IntegrableOn (fun x : ℝ => K * x ^ (c - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul K
  refine lt_of_le_of_lt ?_ hint.lintegral_lt_top
  refine setLIntegral_mono (by fun_prop) (fun x hx => ?_)
  apply ENNReal.ofReal_le_ofReal
  have hx1 : (1:ℝ) < x := hx
  have hx0 : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
  calc cnt t w x * x ^ (-σ - 1) ≤ K * x ^ c * x ^ (-σ - 1) :=
        mul_le_mul_of_nonneg_right (hb x hx1.le) hx0
    _ = K * x ^ (c - σ - 1) := by
        rw [mul_assoc, ← Real.rpow_add (by linarith)]; ring_nf

lemma tsum_lintegral_eq [Countable ι] (h : Hyp t w c) (σ : ℝ) :
    ∑' i, ∫⁻ x in Ioi 1, ENNReal.ofReal ((if t i ≤ x then w i else 0) * x ^ (-σ - 1)) =
      ∫⁻ x in Ioi 1, ENNReal.ofReal (cnt t w x * x ^ (-σ - 1)) := by
  rw [← lintegral_tsum]
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (le_of_lt (lt_trans one_pos hx)) _
    rw [cnt, ← tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg]
    · intro i; split_ifs <;> simp [h.nonneg i, hx0, mul_nonneg]
    · exact (h.summable x).mul_right _
  · intro i
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact Measurable.ite measurableSet_Ici measurable_const measurable_const
    · exact measurable_id.pow_const _

/-- Absolute convergence: `∑ w i t i ^ (-σ) < ∞` for `σ > max(c, 0)`. -/
lemma summable_rpow [Countable ι] (h : Hyp t w c) {σ : ℝ} (hσ0 : 0 < σ) (hσ : c < σ) :
    Summable fun i => w i * t i ^ (-σ) := by
  have H := lintegral_cnt_lt_top h hσ
  rw [← tsum_lintegral_eq h σ] at H
  simp_rw [lintegral_ite_rpow (h.one_le _) (h.nonneg _) hσ0] at H
  have := ENNReal.summable_toReal H.ne
  have hnn : ∀ i, 0 ≤ w i * t i ^ (-σ) / σ := fun i =>
    div_nonneg (mul_nonneg (h.nonneg i)
      (Real.rpow_nonneg (le_trans zero_le_one (h.one_le i)) _)) hσ0.le
  simp_rw [ENNReal.toReal_ofReal (hnn _)] at this
  refine (this.mul_right σ).congr fun i => ?_
  field_simp

/-- **Partial summation**: `∑ w i t i ^ (-s) = s ∫_1^∞ W(x) x^(-s-1) dx` for
`Re s > max(c, 0)`. -/
lemma hasSum_cpow [Countable ι] (h : Hyp t w c) {s : ℂ} (hs0 : 0 < s.re) (hs : c < s.re) :
    HasSum (fun i => (w i : ℂ) * (t i : ℂ) ^ (-s))
      (s * ∫ x in Ioi 1, (cnt t w x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
  have hsne : s ≠ 0 := fun e => by simp [e] at hs0
  set F : ι → ℝ → ℂ := fun i x => (if t i ≤ x then (w i : ℂ) else 0) * (x : ℂ) ^ (-s - 1)
  have hF : ∀ i, Measurable (F i) := fun i => by
    apply Measurable.mul
    · exact Measurable.ite measurableSet_Ici measurable_const measurable_const
    · fun_prop
  have hnorm : ∀ i, ∫⁻ x in Ioi 1, ‖F i x‖ₑ =
      ∫⁻ x in Ioi 1, ENNReal.ofReal ((if t i ≤ x then w i else 0) * x ^ (-s.re - 1)) := by
    intro i
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only [F]
    rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    congr 1
    split_ifs <;> simp [abs_of_nonneg (h.nonneg i)]
  have hfin : ∑' i, ∫⁻ x in Ioi 1, ‖F i x‖ₑ ≠ ⊤ := by
    simp_rw [hnorm]
    rw [tsum_lintegral_eq h]
    have := lintegral_cnt_lt_top h (σ := s.re) hs
    simpa using this.ne
  have hswap := integral_tsum (μ := volume.restrict (Ioi 1)) (fun i => (hF i).aestronglyMeasurable)
    hfin
  have hint : ∀ i, ∫ x in Ioi 1, F i x = (w i : ℂ) * (t i : ℂ) ^ (-s) / s := by
    intro i
    have e : ∀ x : ℝ, F i x = (w i : ℂ) * (if t i ≤ x then (x : ℂ) ^ (-s - 1) else 0) := by
      intro x; simp only [F]; split_ifs <;> simp
    simp_rw [e]
    rw [integral_const_mul, integral_ite_cpow (h.one_le i) hs0, mul_div_assoc]
  have hpt : ∀ x, ∑' i, F i x = (cnt t w x : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x
    simp only [F]
    rw [tsum_mul_right, cnt, Complex.ofReal_tsum]
    congr 1
    refine tsum_congr fun i => ?_
    split_ifs <;> simp
  simp_rw [hpt, hint] at hswap
  rw [hswap, tsum_div_const, mul_div_cancel₀ _ hsne]
  refine Summable.hasSum (Summable.of_norm ?_)
  refine (summable_rpow h hs0 hs).congr fun i => ?_
  have ht0 : (0:ℝ) < t i := lt_of_lt_of_le one_pos (h.one_le i)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (h.nonneg i)]
  simp

end AbelMellin

end
