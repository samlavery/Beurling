module

public import RequestProject.Beurling.LocalPNT.WindowBounds
public import RequestProject.Beurling.LocalPNT.Hpart
public import RequestProject.Beurling.LocalPNT.InversionAux

/-!
# Step 10 of the proof of Theorem 5.24: the contour estimate

With `Φ = PhiW a b ω k`, `E' = e^{c'(b+2ω)}`, `E = e^{c(b+2ω)}`, `D = b - a + 2ω`,
`q = k/(T₁ω)`, `Gb ≥ 190 Y(T₁)`:

  `‖∫_ℝ Φ(c+it) Gright(c+it) dt‖ ≤ Gb E' · 8 log(1 + DT₁/2) + 2(c - c') Gb E (2/T₁) q^k
      + (1.5 log(1/(c-1)) + 8) E (4/k) q^k`

(`contour_estimate`): the line `σ = c` is moved to `σ = c'` on `|t| ≤ T₁` (rectangle `[c', c] ×
[-T₁, T₁]` inside `U`, where `Gright = 𝔊₁`), and the pieces (A), (B), (C) are bounded with
Step 8.
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LocalPNT

/-- `∫_{-T}^{T} 4D/(2 + D|t|) dt = 8 log(1 + DT/2)`. -/
lemma integral_four_div_le {D T : ℝ} (hD : 0 < D) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, 4 * D / (2 + D * |t|) = 8 * Real.log (1 + D * T / 2) := by
  have hc : Continuous fun t : ℝ => 4 * D / (2 + D * |t|) :=
    continuous_const.div (continuous_const.add (continuous_const.mul continuous_abs))
      (fun t => by positivity)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => 4 * D / (2 + D * |t|)) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hsplit := integral_add_adjacent_intervals (hint (-T) 0) (hint 0 T)
  have hneg : ∫ t in (-T)..0, 4 * D / (2 + D * |t|) = ∫ t in (0 : ℝ)..T, 4 * D / (2 + D * |t|) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
      (f := fun t : ℝ => 4 * D / (2 + D * |t|))
    simp only [abs_neg, neg_zero] at this
    rw [← this]
  have hpos : ∫ t in (0 : ℝ)..T, 4 * D / (2 + D * |t|) = 4 * Real.log (1 + D * T / 2) := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun t => 4 * Real.log (2 + D * t))
        (4 * D / (2 + D * |t|)) t := by
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have h2 : 0 < 2 + D * t := by nlinarith [ht.1]
      have := ((hasDerivAt_id t).const_mul D).const_add 2 |>.log h2.ne'
      convert! this.const_mul 4 using 1
      rw [abs_of_nonneg ht.1]; simp only [id]; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint 0 T)]
    simp only [mul_zero, add_zero]
    rw [← mul_sub, ← Real.log_div (by positivity) (by norm_num)]
    congr 2; field_simp
  rw [← hsplit, hneg, hpos]; ring

/-- `min(D, 2/|t|) ≤ 4D/(2 + D|t|)`. -/
lemma min_le_four_div {D t : ℝ} (hD : 0 < D) {m : ℝ} (hm1 : m ≤ D) (hm2 : t ≠ 0 → m ≤ 2 / |t|) :
    m ≤ 4 * D / (2 + D * |t|) := by
  have hpos : 0 < 2 + D * |t| := by positivity
  rw [le_div_iff₀ hpos]
  by_cases ht : D * |t| ≤ 2
  · nlinarith [abs_nonneg t]
  · push_neg at ht
    have ht0 : t ≠ 0 := by intro e; rw [e] at ht; simp at ht; linarith
    have h2 := hm2 ht0
    have hta : 0 < |t| := abs_pos.mpr ht0
    have : m * |t| ≤ 2 := by rw [le_div_iff₀ hta] at h2; linarith
    nlinarith

/-- `∫_{Ioi T} (2/t)(k/(tω))^k dt = (2/k) (k/(Tω))^k`. -/
lemma integral_tail_le {T ω : ℝ} {k : ℕ} (hT : 0 < T) (hω : 0 < ω) (hk : 1 ≤ k) :
    IntegrableOn (fun t : ℝ => 2 / t * (k / (t * ω)) ^ k) (Ioi T) ∧
    ∫ t in Ioi T, 2 / t * (k / (t * ω)) ^ k = 2 / k * (k / (T * ω)) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : -((k : ℝ) + 1) < -1 := by linarith
  have hrw : ∀ t ∈ Ioi T, 2 / t * (k / (t * ω)) ^ k = 2 * (k / ω) ^ k * t ^ (-((k : ℝ) + 1)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hT ht
    rw [Real.rpow_neg ht0.le, Real.rpow_add ht0, Real.rpow_one, Real.rpow_natCast, div_pow,
      div_pow, mul_pow]
    field_simp
  have hint := integrableOn_Ioi_rpow_of_lt hexp hT
  refine ⟨IntegrableOn.congr_fun (hint.const_mul (2 * (k / ω) ^ k))
    (fun t ht => (hrw t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hrw, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt hexp hT]
  have e : -((k : ℝ) + 1) + 1 = -(k : ℝ) := by ring
  rw [e, Real.rpow_neg hT.le, Real.rpow_natCast, div_pow, div_pow, mul_pow]
  field_simp

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

set_option maxHeartbeats 2000000 in
/-- **The contour estimate of Step 10.** -/
theorem contour_estimate {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s)
    {a b ω : ℝ} {k : ℕ} (hab : a ≤ b) (hω : 0 < ω) (hk : 1 ≤ k) (hb0 : 0 ≤ b + 2 * ω)
    {c : ℝ} (hc1 : c1 y < c) (hc98 : c ≤ 9 / 8) {Gb : ℝ} (hGb : 190 * Yt (Real.log X₀) T₁ ≤ Gb)
    (hI : Integrable (fun t : ℝ => PhiW a b ω k (c + t * I) *
      Gright P θ X₀ α γ xp y (c + t * I))) :
    ‖∫ t : ℝ, PhiW a b ω k (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)‖ ≤
      Gb * Real.exp ((1 - 0.9 * etat (Real.log X₀) T₁ / 3.79) * (b + 2 * ω)) *
          (8 * Real.log (1 + (b - a + 2 * ω) * T₁ / 2)) +
        2 * (c - (1 - 0.9 * etat (Real.log X₀) T₁ / 3.79)) * Gb *
          Real.exp (c * (b + 2 * ω)) * (2 / T₁) * (k / (T₁ * ω)) ^ k +
        (1.5 * Real.log (1 / (c - 1)) + 8) * Real.exp (c * (b + 2 * ω)) * (4 / k) *
          (k / (T₁ * ω)) ^ k := by
  set Λ := Real.log X₀
  set L := Real.log y
  set c' := 1 - 0.9 * etat Λ T₁ / 3.79 with hc'def
  set Φ := PhiW a b ω k
  set E' := Real.exp (c' * (b + 2 * ω))
  set E := Real.exp (c * (b + 2 * ω))
  set D := b - a + 2 * ω
  set q := (k : ℝ) / (T₁ * ω)
  have hX := h.logX
  have hL := h.logy_ge
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hηT0 := etat_pos hΛ1 T₁
  have hηTs := etat_le hX T₁
  have hc1' : 1 < c1 y := h.c1_gt
  have hc0 : 1 < c := by linarith
  have hc'1 : c' ≤ 1 := by
    simp only [c']; have : 0 ≤ 0.9 * etat Λ T₁ / 3.79 := by positivity
    linarith
  have hc'0 : 0 < c' := by
    simp only [c']
    have : 0.9 * etat Λ T₁ / 3.79 ≤ 1 / 10 ^ 10 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hD : 0 < D := by simp only [D]; linarith
  have hT0 : 0 < T₁ := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨hA_G, hB_G⟩ := h.G1_contour_bound hT hyr hTy hGd hGe hGr
  -- the rectangle lies in `U`
  have hc0U : c0 Λ T₁ < c' := by
    have hηT1 := etat_ge_near (Λ := Λ) (t := T₁) (t' := T₁ + 1) hΛ1
      (by rw [abs_of_pos hT0, abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_pos hT0, abs_of_pos (by linarith)])
    simp only [c0, c']
    have : 0.9 * etat Λ T₁ / 3.79 < 0.99 * etat Λ (T₁ + 1) / 3.79 := by
      apply div_lt_div_of_pos_right _ (by norm_num); nlinarith
    linarith
  have hRU : [[c', c]] ×ℂ [[-T₁, T₁]] ⊆ rectU Λ T₁ := by
    rintro z ⟨h1, h2⟩
    rw [Set.uIcc_of_le (by linarith)] at h1
    rw [Set.uIcc_of_le (by linarith)] at h2
    exact ⟨⟨lt_of_lt_of_le hc0U h1.1, by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  have hΦd := differentiableOn_PhiW hab hω hk
  have hFgd : DifferentiableOn ℂ (fun s => Φ s * G s) ([[c', c]] ×ℂ [[-T₁, T₁]]) := by
    refine DifferentiableOn.mul (hΦd.mono fun z hz => ?_) (hGd.mono hRU)
    have := hz.1; rw [Set.uIcc_of_le (by linarith)] at this
    show 0 < z.re; linarith [this.1]
  have hshift := integral_rect_shift_left hFgd
  -- on the line `σ = c`, `G = Gright`
  have hline : ∫ t in (-T₁)..T₁, Φ (c + t * I) * G (c + t * I) =
      ∫ t in (-T₁)..T₁, Φ (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    have hmem : ((c : ℂ) + t * I) ∈ Set.uIcc c' c ×ℂ Set.uIcc (-T₁) T₁ := by
      rw [Complex.mem_reProdIm]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨Set.right_mem_uIcc, by rw [Set.uIcc_of_le (by linarith)]; exact ht⟩
    rw [hGr _ (hRU hmem) (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
        rw [← c1_def]; exact hc1)]
  -- splitting `ℝ = (-∞, -T₁] ∪ (-T₁, T₁] ∪ (T₁, ∞)`
  set F : ℝ → ℂ := fun t => Φ (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)
  have hsplit1 := integral_Iic_add_Ioi (hI.integrableOn (s := Iic (-T₁)))
    (hI.integrableOn (s := Ioi (-T₁)))
  have hsplit2 := integral_interval_add_Ioi' (hI.intervalIntegrable (a := -T₁) (b := T₁))
    (hI.integrableOn (s := Ioi T₁))
  have hdecomp : ∫ t : ℝ, F t = (∫ t in Iic (-T₁), F t) + ((∫ t in (-T₁)..T₁, F t) +
      ∫ t in Ioi T₁, F t) := by rw [hsplit2, hsplit1]
  rw [hdecomp]
  -- (A)
  have hA : ‖∫ t in (-T₁)..T₁, Φ (c' + t * I) * G (c' + t * I)‖ ≤
      Gb * E' * (8 * Real.log (1 + D * T₁ / 2)) := by
    rw [← integral_four_div_le hD hT0.le, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun t ht => ?_)
      ((continuous_const.mul (continuous_const.div (continuous_const.add
        (continuous_const.mul continuous_abs)) (fun t => (by
          have := mul_nonneg hD.le (abs_nonneg t); linarith : (0 : ℝ) < 2 + D * |t|).ne'))
        ).intervalIntegrable _ _)
    have htT : |t| ≤ T₁ := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hs : 0 < ((c' : ℂ) + t * I).re := by simpa using hc'0
    obtain ⟨p1, p2, -⟩ := norm_PhiW_le hab hω hk hs
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at p1 p2
    have hm := min_le_four_div (m := ‖Φ (c' + t * I)‖ / E') (t := t) hD
      (by rw [div_le_iff₀ (Real.exp_pos _)]; linarith)
      (fun ht0 => by rw [div_le_iff₀ (Real.exp_pos _)]; linarith [p2 ht0])
    rw [div_le_iff₀ (Real.exp_pos _)] at hm
    have hG := (hA_G t htT).trans hGb
    rw [norm_mul]
    calc ‖Φ (c' + t * I)‖ * ‖G (c' + t * I)‖ ≤ (4 * D / (2 + D * |t|) * E') * Gb :=
          mul_le_mul hm hG (norm_nonneg _) (by positivity)
      _ = Gb * E' * (4 * D / (2 + D * |t|)) := by ring
  -- (B)
  have hBseg : ∀ t : ℝ, |t| = T₁ →
      ‖∫ σ in c'..c, Φ (σ + t * I) * G (σ + t * I)‖ ≤ (Gb * (E * (2 / T₁) * q ^ k)) * (c - c') := by
    intro t ht
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c') (b := c)
      (f := fun σ : ℝ => Φ (σ + t * I) * G (σ + t * I)) (C := Gb * (E * (2 / T₁) * q ^ k)) (by
        intro σ hσ
        rw [Set.uIoc_of_le (by linarith)] at hσ
        have hs : 0 < ((σ : ℂ) + t * I).re := by simp; linarith [hσ.1]
        obtain ⟨-, -, p3⟩ := norm_PhiW_le hab hω hk hs
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
          Complex.mul_im, zero_add] at p3
        have ht0 : t ≠ 0 := by intro e; rw [e] at ht; simp at ht; linarith
        have hp := p3 ht0
        rw [ht] at hp
        have hmono : Real.exp (σ * (b + 2 * ω)) ≤ E :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hb0)
        have hG := (hB_G σ (by linarith [hσ.1]) (by linarith [hσ.2]) t ht).trans hGb
        rw [norm_mul]
        calc ‖Φ (σ + t * I)‖ * ‖G (σ + t * I)‖ ≤ (E * (2 / T₁) * q ^ k) * Gb := by
              apply mul_le_mul _ hG (norm_nonneg _) (by positivity)
              refine hp.trans ?_
              gcongr
          _ = _ := by ring)
    rw [abs_of_nonneg (by linarith)] at this
    exact this
  have hB1 := hBseg T₁ (abs_of_pos hT0)
  have hB2 := hBseg (-T₁) (by rw [abs_neg, abs_of_pos hT0])
  -- (C)
  have hCbound : ∀ t : ℝ, T₁ ≤ |t| → ‖F t‖ ≤
      (1.5 * Real.log (1 / (c - 1)) + 8) * E * (2 / |t| * (k / (|t| * ω)) ^ k) := by
    intro t ht
    have hs : 0 < ((c : ℂ) + t * I).re := by simp; linarith
    obtain ⟨-, -, p3⟩ := norm_PhiW_le hab hω hk hs
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at p3
    have ht0 : t ≠ 0 := by intro e; rw [e] at ht; simp at ht; linarith
    have hGr' := h.norm_Gright_le (s := (c : ℂ) + t * I)
      (by simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
          rw [← c1_def]; exact hc1.le)
      (by simpa using hc98) (by simp; linarith)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero] at hGr'
    simp only [F]
    rw [norm_mul]
    have hpos : 0 ≤ 1.5 * Real.log (1 / (c - 1)) + 8 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / (c - 1) by
        rw [le_div_iff₀ (by linarith)]; linarith)
      linarith
    calc ‖Φ (c + t * I)‖ * ‖Gright P θ X₀ α γ xp y (c + t * I)‖ ≤
          (E * (2 / |t|) * (k / (|t| * ω)) ^ k) * (1.5 * Real.log (1 / (c - 1)) + 8) :=
          mul_le_mul (p3 ht0) hGr' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨hTi, hTv⟩ := integral_tail_le (k := k) hT0 hω hk
  have hC1 : ‖∫ t in Ioi T₁, F t‖ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * E * (2 / k * q ^ k) := by
    rw [← hTv, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.norm_integral_le_of_norm_le (hTi.const_mul _) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht' : T₁ ≤ |t| := by rw [abs_of_pos (lt_trans hT0 ht)]; exact ht.out.le
    have := hCbound t ht'
    rwa [abs_of_pos (lt_trans hT0 ht)] at this
  have hC2 : ‖∫ t in Iic (-T₁), F t‖ ≤
      (1.5 * Real.log (1 / (c - 1)) + 8) * E * (2 / k * q ^ k) := by
    have e := integral_comp_neg_Iic (-T₁) (fun t => F (-t))
    simp only [neg_neg] at e
    rw [e, ← hTv, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.norm_integral_le_of_norm_le (hTi.const_mul _) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht' : T₁ ≤ |-t| := by rw [abs_neg, abs_of_pos (lt_trans hT0 ht)]; exact ht.out.le
    have := hCbound (-t) ht'
    rwa [abs_neg, abs_of_pos (lt_trans hT0 ht)] at this
  -- assemble
  have hmid : ∫ t in (-T₁)..T₁, F t = (∫ t in (-T₁)..T₁, Φ (c' + t * I) * G (c' + t * I)) +
      I⁻¹ * ((∫ σ in c'..c, Φ (σ + T₁ * I) * G (σ + T₁ * I)) -
        ∫ σ in c'..c, Φ (σ - T₁ * I) * G (σ - T₁ * I)) := by
    rw [← hshift]; exact hline.symm
  have hB2' : ‖∫ σ in c'..c, Φ (σ - T₁ * I) * G (σ - T₁ * I)‖ ≤
      (Gb * (E * (2 / T₁) * q ^ k)) * (c - c') := by
    have e : (fun σ : ℝ => Φ (σ - T₁ * I) * G (σ - T₁ * I)) =
        fun σ : ℝ => Φ (σ + ((-T₁ : ℝ) : ℂ) * I) * G (σ + ((-T₁ : ℝ) : ℂ) * I) := by
      funext σ; push_cast; ring_nf
    rw [e]; exact hB2
  have hB1' : ‖∫ σ in c'..c, Φ (σ + T₁ * I) * G (σ + T₁ * I)‖ ≤
      (Gb * (E * (2 / T₁) * q ^ k)) * (c - c') := hB1
  rw [hmid]
  have hI1 : ‖(I : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Complex.norm_I, inv_one]
  calc ‖(∫ t in Iic (-T₁), F t) + ((∫ t in (-T₁)..T₁, Φ (c' + t * I) * G (c' + t * I)) +
        I⁻¹ * ((∫ σ in c'..c, Φ (σ + T₁ * I) * G (σ + T₁ * I)) -
          ∫ σ in c'..c, Φ (σ - T₁ * I) * G (σ - T₁ * I)) + ∫ t in Ioi T₁, F t)‖
      ≤ ‖∫ t in Iic (-T₁), F t‖ + (‖∫ t in (-T₁)..T₁, Φ (c' + t * I) * G (c' + t * I)‖ +
          (‖∫ σ in c'..c, Φ (σ + T₁ * I) * G (σ + T₁ * I)‖ +
            ‖∫ σ in c'..c, Φ (σ - T₁ * I) * G (σ - T₁ * I)‖) + ‖∫ t in Ioi T₁, F t‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, hI1, one_mul]
        exact norm_sub_le _ _
    _ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * E * (2 / k * q ^ k) +
          (Gb * E' * (8 * Real.log (1 + D * T₁ / 2)) +
            ((Gb * (E * (2 / T₁) * q ^ k)) * (c - c') + (Gb * (E * (2 / T₁) * q ^ k)) * (c - c')) +
            (1.5 * Real.log (1 / (c - 1)) + 8) * E * (2 / k * q ^ k)) :=
        add_le_add hC2 (add_le_add (add_le_add hA (add_le_add hB1' hB2')) hC1)
    _ = _ := by ring

end LPHyp

end LocalPNT

end
