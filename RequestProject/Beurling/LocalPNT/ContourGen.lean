module

public import RequestProject.Beurling.LocalPNT.Step10

/-!
# Steps 9–10 of the proof of Theorem 5.24: the contour estimate for a general transform

For `F` holomorphic on the rectangle `[c', c] × [-T₁, T₁]`, with
(A) `‖F(c' + it)‖ ≤ g_A(t)` on `|t| ≤ T₁`, (B) `‖F(σ ± iT₁)‖ ≤ I_B` on `[c', c]`,
(C) `‖F(c + it)‖ ≤ g_C(|t|)` on `|t| ≥ T₁`:

  `‖∫_ℝ F(c+it) Gright(c+it) dt‖ ≤ Gb ∫ g_A + 2(c - c') Gb I_B`
  `+ (1.5 log(1/(c-1)) + 8) · 2∫_{T₁}^∞ g_C`.
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

set_option maxHeartbeats 2000000 in
/-- **The contour estimate**, general transform `F`. -/
theorem contour_estimate_gen {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s)
    {c : ℝ} (hc1 : c1 y < c) (hc98 : c ≤ 9 / 8)
    {F : ℂ → ℂ} {Q : ℂ → ℂ}
    (hQd : DifferentiableOn ℂ Q ([[1 - 0.9 * etat (Real.log X₀) T₁ / 3.79, c]] ×ℂ [[-T₁, T₁]]))
    (hQ : ∀ s ∈ rectU (Real.log X₀) T₁, s ≠ 1 → Q s = F s * G s) {Gb : ℝ}
    (hGb : 190 * Yt (Real.log X₀) T₁ ≤ Gb)
    (hI : Integrable (fun t : ℝ => F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)))
    {gA : ℝ → ℝ} {IA IB IC : ℝ} {gC : ℝ → ℝ}
    (hgA : IntervalIntegrable gA volume (-T₁) T₁)
    (hA : ∀ t : ℝ, |t| ≤ T₁ →
      ‖F (((1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 : ℝ) : ℂ) + t * I)‖ ≤ gA t)
    (hIA : ∫ t in (-T₁)..T₁, gA t ≤ IA)
    (hB : ∀ σ : ℝ, 1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 ≤ σ → σ ≤ c → ∀ t : ℝ, |t| = T₁ →
      ‖F (σ + t * I)‖ ≤ IB)
    (hgC : IntegrableOn gC (Ioi T₁)) (hgC0 : ∀ t, 0 ≤ gC t)
    (hC : ∀ t : ℝ, T₁ ≤ |t| → ‖F (c + t * I)‖ ≤ gC |t|) (hIC : ∫ t in Ioi T₁, gC t ≤ IC) :
    ‖∫ t : ℝ, F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)‖ ≤
      Gb * IA + 2 * (c - (1 - 0.9 * etat (Real.log X₀) T₁ / 3.79)) * Gb * IB +
        (1.5 * Real.log (1 / (c - 1)) + 8) * (2 * IC) := by
  set Λ := Real.log X₀
  set c' := 1 - 0.9 * etat Λ T₁ / 3.79 with hc'def
  have hX := h.logX
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
  have hT0 : 0 < T₁ := by linarith
  have hc'lt : c' < 1 := by
    simp only [c']
    have : 0 < 0.9 * etat Λ T₁ / 3.79 := by positivity
    linarith
  obtain ⟨hA_G, hB_G⟩ := h.G1_contour_bound hT hyr hTy hGd hGe hGr
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
  have hshift0 := integral_rect_shift_left hQd
  -- on the four sides `Q = F G` (they avoid `s = 1`)
  have hside : ∀ σ t : ℝ, σ ∈ Set.uIcc c' c → t ∈ Set.uIcc (-T₁) T₁ → (σ ≠ 1 ∨ t ≠ 0) →
      Q (σ + t * I) = F (σ + t * I) * G (σ + t * I) := by
    intro σ t hσ ht hne
    refine hQ _ (hRU ⟨by simpa using hσ, by simpa using ht⟩) ?_
    intro e
    have h1 := congrArg Complex.re e
    have h2 := congrArg Complex.im e
    simp at h1 h2
    rcases hne with hne | hne
    · exact hne h1
    · exact hne h2
  have hshift : ∫ t in (-T₁)..T₁, F (c + t * I) * G (c + t * I) =
      (∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)) +
        I⁻¹ * ((∫ σ in c'..c, F (σ + T₁ * I) * G (σ + T₁ * I)) -
          ∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I)) := by
    have e1 : ∫ t in (-T₁)..T₁, Q (c + t * I) = ∫ t in (-T₁)..T₁, F (c + t * I) * G (c + t * I) :=
      intervalIntegral.integral_congr fun t ht =>
        hside c t Set.right_mem_uIcc ht (Or.inl (by linarith))
    have e2 : ∫ t in (-T₁)..T₁, Q (c' + t * I) =
        ∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I) :=
      intervalIntegral.integral_congr fun t ht =>
        hside c' t Set.left_mem_uIcc ht (Or.inl hc'lt.ne)
    have e3 : ∫ σ in c'..c, Q (σ + T₁ * I) = ∫ σ in c'..c, F (σ + T₁ * I) * G (σ + T₁ * I) :=
      intervalIntegral.integral_congr fun σ hσ =>
        hside σ T₁ hσ Set.right_mem_uIcc (Or.inr (by linarith))
    have e4 : ∫ σ in c'..c, Q (σ - T₁ * I) = ∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have := hside σ (-T₁) hσ Set.left_mem_uIcc (Or.inr (by linarith))
      simp only [Complex.ofReal_neg, neg_mul] at this
      simpa [sub_eq_add_neg] using this
    rw [← e1, ← e2, ← e3, ← e4]; exact hshift0
  have hline : ∫ t in (-T₁)..T₁, F (c + t * I) * G (c + t * I) =
      ∫ t in (-T₁)..T₁, F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I) := by
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
  set Fl : ℝ → ℂ := fun t => F (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)
  have hsplit1 := integral_Iic_add_Ioi (hI.integrableOn (s := Iic (-T₁)))
    (hI.integrableOn (s := Ioi (-T₁)))
  have hsplit2 := integral_interval_add_Ioi' (hI.intervalIntegrable (a := -T₁) (b := T₁))
    (hI.integrableOn (s := Ioi T₁))
  have hdecomp : ∫ t : ℝ, Fl t = (∫ t in Iic (-T₁), Fl t) + ((∫ t in (-T₁)..T₁, Fl t) +
      ∫ t in Ioi T₁, Fl t) := by rw [hsplit2, hsplit1]
  rw [hdecomp]
  -- (A)
  have hA' : ‖∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)‖ ≤ Gb * IA := by
    have hle : ‖∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)‖ ≤
        ∫ t in (-T₁)..T₁, Gb * gA t := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Eventually.of_forall fun t ht => ?_) (hgA.const_mul Gb)
      have htT : |t| ≤ T₁ := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hG := (hA_G t htT).trans hGb
      have hGb0 : 0 ≤ Gb := (norm_nonneg _).trans hG
      rw [norm_mul]
      calc ‖F (c' + t * I)‖ * ‖G (c' + t * I)‖ ≤ gA t * Gb :=
            mul_le_mul (hA t htT) hG (norm_nonneg _) ((norm_nonneg _).trans (hA t htT))
        _ = Gb * gA t := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    have hGb0 : 0 ≤ Gb := le_trans (by have := Yt_ge hΛ1 T₁; linarith) hGb
    exact hle.trans (mul_le_mul_of_nonneg_left hIA hGb0)
  -- (B)
  have hBseg : ∀ t : ℝ, |t| = T₁ →
      ‖∫ σ in c'..c, F (σ + t * I) * G (σ + t * I)‖ ≤ (Gb * IB) * (c - c') := by
    intro t ht
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c') (b := c)
      (f := fun σ : ℝ => F (σ + t * I) * G (σ + t * I)) (C := Gb * IB) (by
        intro σ hσ
        rw [Set.uIoc_of_le (by linarith)] at hσ
        have hG := (hB_G σ (by linarith [hσ.1]) (by linarith [hσ.2]) t ht).trans hGb
        have hF := hB σ hσ.1.le hσ.2 t ht
        rw [norm_mul]
        calc ‖F (σ + t * I)‖ * ‖G (σ + t * I)‖ ≤ IB * Gb :=
              mul_le_mul hF hG (norm_nonneg _) ((norm_nonneg _).trans hF)
          _ = Gb * IB := by ring)
    rw [abs_of_nonneg (by linarith)] at this
    exact this
  have hB1 := hBseg T₁ (abs_of_pos hT0)
  have hB2 := hBseg (-T₁) (by rw [abs_neg, abs_of_pos hT0])
  -- (C)
  have hlogc : 0 ≤ 1.5 * Real.log (1 / (c - 1)) + 8 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / (c - 1) by
      rw [le_div_iff₀ (by linarith)]; linarith)
    linarith
  have hCbound : ∀ t : ℝ, T₁ ≤ |t| → ‖Fl t‖ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * gC |t| := by
    intro t ht
    have hGr' := h.norm_Gright_le (s := (c : ℂ) + t * I)
      (by simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
          rw [← c1_def]; exact hc1.le)
      (by simpa using hc98) (by simp; linarith)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero] at hGr'
    simp only [Fl]
    rw [norm_mul]
    calc ‖F (c + t * I)‖ * ‖Gright P θ X₀ α γ xp y (c + t * I)‖ ≤
          gC |t| * (1.5 * Real.log (1 / (c - 1)) + 8) :=
          mul_le_mul (hC t ht) hGr' (norm_nonneg _) (hgC0 _)
      _ = _ := by ring
  have hC1 : ‖∫ t in Ioi T₁, Fl t‖ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * IC := by
    have hle : ‖∫ t in Ioi T₁, Fl t‖ ≤
        ∫ t in Ioi T₁, (1.5 * Real.log (1 / (c - 1)) + 8) * gC t := by
      refine MeasureTheory.norm_integral_le_of_norm_le (hgC.const_mul _) ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : T₁ ≤ |t| := by rw [abs_of_pos (lt_trans hT0 ht)]; exact ht.out.le
      have := hCbound t ht'
      rwa [abs_of_pos (lt_trans hT0 ht)] at this
    rw [MeasureTheory.integral_const_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left hIC hlogc)
  have hC2 : ‖∫ t in Iic (-T₁), Fl t‖ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * IC := by
    have e := integral_comp_neg_Iic (-T₁) (fun t => Fl (-t))
    simp only [neg_neg] at e
    rw [e]
    have hle : ‖∫ t in Ioi T₁, Fl (-t)‖ ≤
        ∫ t in Ioi T₁, (1.5 * Real.log (1 / (c - 1)) + 8) * gC t := by
      refine MeasureTheory.norm_integral_le_of_norm_le (hgC.const_mul _) ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : T₁ ≤ |-t| := by rw [abs_neg, abs_of_pos (lt_trans hT0 ht)]; exact ht.out.le
      have := hCbound (-t) ht'
      rwa [abs_neg, abs_of_pos (lt_trans hT0 ht)] at this
    rw [MeasureTheory.integral_const_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left hIC hlogc)
  have hmid : ∫ t in (-T₁)..T₁, Fl t = (∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)) +
      I⁻¹ * ((∫ σ in c'..c, F (σ + T₁ * I) * G (σ + T₁ * I)) -
        ∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I)) := by
    rw [← hshift]; exact hline.symm
  have hB2' : ‖∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I)‖ ≤ (Gb * IB) * (c - c') := by
    have e : (fun σ : ℝ => F (σ - T₁ * I) * G (σ - T₁ * I)) =
        fun σ : ℝ => F (σ + ((-T₁ : ℝ) : ℂ) * I) * G (σ + ((-T₁ : ℝ) : ℂ) * I) := by
      funext σ; push_cast; ring_nf
    rw [e]; exact hB2
  rw [hmid]
  have hI1 : ‖(I : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Complex.norm_I, inv_one]
  calc ‖(∫ t in Iic (-T₁), Fl t) + ((∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)) +
        I⁻¹ * ((∫ σ in c'..c, F (σ + T₁ * I) * G (σ + T₁ * I)) -
          ∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I)) + ∫ t in Ioi T₁, Fl t)‖
      ≤ ‖∫ t in Iic (-T₁), Fl t‖ + (‖∫ t in (-T₁)..T₁, F (c' + t * I) * G (c' + t * I)‖ +
          (‖∫ σ in c'..c, F (σ + T₁ * I) * G (σ + T₁ * I)‖ +
            ‖∫ σ in c'..c, F (σ - T₁ * I) * G (σ - T₁ * I)‖) + ‖∫ t in Ioi T₁, Fl t‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, hI1, one_mul]
        exact norm_sub_le _ _
    _ ≤ (1.5 * Real.log (1 / (c - 1)) + 8) * IC + (Gb * IA + ((Gb * IB) * (c - c') +
          (Gb * IB) * (c - c')) + (1.5 * Real.log (1 / (c - 1)) + 8) * IC) :=
        add_le_add hC2 (add_le_add (add_le_add hA' (add_le_add hB1 hB2')) hC1)
    _ = _ := by ring

end LPHyp

end LocalPNT

end
