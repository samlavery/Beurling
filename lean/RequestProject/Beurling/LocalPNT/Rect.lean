module

public import RequestProject.Beurling.LocalPNT.Branch

/-!
# Step 8 of the proof of Theorem 5.24: `𝔊₁` on a rectangle

For a height `T₁ ≥ 1` with `log(T₁ + 4) ≤ log T_y + 1` and (eq. lp-yrange), `gfun` is holomorphic
and zero-free on the open rectangle
`U = (c₀, 2) × (-(T₁+1), T₁+1)`, `c₀ = 1 - 0.99 η_{T₁+1}/3.79`
(Steps 6 and 7), so it has a holomorphic logarithm `𝔊₁` on `U`, which equals `Gright` on the part
of `U` with `σ > 1 + 8 log log y/log y` (`exists_G1`).
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology

namespace LocalPNT

lemma Lt_mono {t t' : ℝ} (h : |t| ≤ |t'|) : Lt t ≤ Lt t' :=
  Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)

lemma Yt_mono {Λ t t' : ℝ} (hΛ : 1 ≤ Λ) (h : |t| ≤ |t'|) : Yt Λ t ≤ Yt Λ t' := by
  unfold Yt
  have h1 := Lt_mono h
  have h0 := Lt_nonneg t
  have hl := Real.log_nonneg hΛ
  have := Real.log_le_log (by linarith) (show Lt t + 442 + 2 * Real.log Λ ≤
    Lt t' + 442 + 2 * Real.log Λ by linarith)
  linarith

lemma etat_anti {Λ t t' : ℝ} (hΛ : 1 ≤ Λ) (h : |t| ≤ |t'|) : etat Λ t' ≤ etat Λ t := by
  unfold etat
  have hm := Yt_mono hΛ h
  have hg := Yt_ge hΛ t
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left hm (by linarith)

/-- The left edge `c₀ = 1 - 0.99 η_{T₁+1}/3.79`. -/
noncomputable def c0 (Λ T₁ : ℝ) : ℝ := 1 - 0.99 * etat Λ (T₁ + 1) / 3.79

/-- The rectangle `U = (c₀, 2) × (-(T₁+1), T₁+1)`. -/
def rectU (Λ T₁ : ℝ) : Set ℂ := Ioo (c0 Λ T₁) 2 ×ℂ Ioo (-(T₁ + 1)) (T₁ + 1)

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `gfun` is holomorphic and zero-free on `U`. -/
theorem gfun_rect {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1) :
    DifferentiableOn ℂ (gfun P θ X₀ α γ xp y) (rectU (Real.log X₀) T₁) ∧
    ∀ s ∈ rectU (Real.log X₀) T₁, gfun P θ X₀ α γ xp y s ≠ 0 := by
  set Λ := Real.log X₀
  set L := Real.log y
  have hX := h.logX
  have hL := h.logy_ge
  have hΛ0 : 0 < Λ := by linarith
  have hηT := etat_le hX (T₁ + 1)
  have hηT0 := etat_pos (by linarith : (1 : ℝ) ≤ Λ) (T₁ + 1)
  have hc0 : 1 - 1 / Λ < c0 Λ T₁ := by
    unfold c0
    have hηΛ : etat Λ (T₁ + 1) * Λ ≤ 0.33769 / 442 := by
      unfold etat
      have hY := Yt_ge (Λ := Λ) (by linarith) (T₁ + 1)
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : 0.99 * etat Λ (T₁ + 1) / 3.79 < 1 / Λ := by
      rw [lt_div_iff₀ hΛ0]
      have e : 0.99 * etat Λ (T₁ + 1) / 3.79 * Λ = 0.99 / 3.79 * (etat Λ (T₁ + 1) * Λ) := by ring
      rw [e]; nlinarith
    linarith
  have h1Λ : 1 / Λ ≤ 1 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
  have h8Λ : 1 / Λ ≤ 8 / Λ := div_le_div_of_nonneg_right (by norm_num) hΛ0.le
  have hmem : ∀ s ∈ rectU Λ T₁, c0 Λ T₁ < s.re ∧ s.re < 2 ∧ |s.im| < T₁ + 1 := by
    intro s hs
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hs
    exact ⟨h1, h2, abs_lt.mpr ⟨h3, h4⟩⟩
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨h1, -, -⟩ := hmem s hs
    by_cases hs1 : s = 1
    · subst hs1
      have := h.differentiableOn_gfun_ball
      exact (this.differentiableAt (ball_mem_nhds 1 (by positivity))).differentiableWithinAt
    · exact (h.differentiableAt_gfun (by linarith [h.theta_mem.2]) hs1).differentiableWithinAt
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hmem s hs
    by_cases hs1 : s = 1
    · subst hs1; simp [gfun]
    have hs0 : s ≠ 0 := by intro e; rw [e] at h1; simp at h1; linarith
    simp only [gfun, Function.update_of_ne hs1]
    refine div_ne_zero ?_ hs0
    have hz : zetaSharp P θ X₀ α γ xp y s ≠ 0 := by
      by_cases hr : 1 + 8 * Real.log L / L ≤ s.re
      · exact h.zetaSharp_ne_zero_right hr h2.le
      push_neg at hr
      have h8 : 8 * Real.log L / L ≤ 1 / 100 := by
        have hl := Real.log_le_rpow_div (x := L) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
        rw [div_le_iff₀ (by linarith)]
        have h2' : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
          rw [← Real.rpow_add (by linarith)]; norm_num
        have h4 : (10 : ℝ) ^ 4 ≤ L ^ (1 / 2 : ℝ) := by
          have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) hL (by norm_num)
          rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
            rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num,
              ← Real.rpow_mul (by norm_num)]
            norm_num] at this
        have h5 : 0 ≤ L ^ (1 / 2 : ℝ) := by positivity
        rw [div_div_eq_mul_div] at hl
        nlinarith
      by_cases ht : 1 / 16 ≤ |s.im|
      · -- Step 7
        have hht : Lt s.im ≤ logTy Λ L + 1 := by
          refine le_trans (Lt_mono ?_) hTy
          rw [abs_of_pos (by linarith : (0 : ℝ) < T₁ + 1)]; exact h3.le
        have hη := etat_ge_of_height hX hL hyr hht
        have hmono := etat_anti (Λ := Λ) (by linarith) (show |s.im| ≤ |T₁ + 1| by
          rw [abs_of_pos (by linarith : (0 : ℝ) < T₁ + 1)]; exact h3.le)
        have hσ : 1 - etat Λ s.im / 3.79 ≤ s.re := by
          unfold c0 at h1
          have : 0 ≤ etat Λ (T₁ + 1) := hηT0.le
          have := etat_pos (by linarith : (1 : ℝ) ≤ Λ) s.im
          have hh : 0.99 * etat Λ (T₁ + 1) / 3.79 ≤ etat Λ s.im / 3.79 :=
            div_le_div_of_nonneg_right (by linarith) (by norm_num)
          have h1' : c0 Λ T₁ < s.re := h1
          unfold c0 at h1'
          linarith
        have := h.zeroFree_width (t := s.im) ht hη (σ := s.re) hσ h2.le
        rwa [Complex.re_add_im] at this
      · -- Step 6
        push_neg at ht
        have hn : ‖s - 1‖ ≤ 1 / 8 := by
          have := Complex.norm_le_abs_re_add_abs_im (s - 1)
          simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
            sub_zero] at this
          have : |s.re - 1| ≤ 1 / 100 + 1 / 10 ^ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
        have hnp := h.near_pole (s := s) (by linarith) hn hs1
        intro hz0
        rw [hz0, mul_zero, zero_sub, norm_neg, norm_one] at hnp
        norm_num at hnp
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hz

omit h in
lemma convex_rect (a b c d : ℝ) : Convex ℝ (Ioo a b ×ℂ Ioo c d) :=
  ((convex_Ioo a b).linear_preimage Complex.reLm).inter
    ((convex_Ioo c d).linear_preimage Complex.imLm)

/-- **`𝔊₁` on the rectangle** (Step 8): a holomorphic logarithm of `gfun` on `U`, equal to
`Gright` where `σ > 1 + 8 log log y/log y`. -/
theorem exists_G1 {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (rectU (Real.log X₀) T₁) ∧
      (∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s) ∧
      ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
        G s = Gright P θ X₀ α γ xp y s := by
  set Λ := Real.log X₀
  set L := Real.log y
  obtain ⟨hd, hne⟩ := h.gfun_rect hT hyr hTy
  obtain ⟨G0, hG0d, hG0e⟩ := exists_log_rect hd hne
  have hL := h.logy_ge
  have hX := h.logX
  -- the base point `3/2`
  have h8 : 8 * Real.log L / L ≤ 1 / 100 := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < L by linarith)
    rw [div_le_iff₀ (by linarith)]
    have hl2 : Real.log L ≤ L / 1000 := by
      have := Real.log_le_rpow_div (x := L) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
      have h2' : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
        rw [← Real.rpow_add (by linarith)]; norm_num
      have h4 : (10 : ℝ) ^ 4 ≤ L ^ (1 / 2 : ℝ) := by
        have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hL (by norm_num)
        rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
          rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num] at this
      have h5 : 0 ≤ L ^ (1 / 2 : ℝ) := by positivity
      rw [div_div_eq_mul_div] at this
      nlinarith
    nlinarith
  have hηT := etat_le hX (T₁ + 1)
  have hηT0 := etat_pos (by linarith : (1 : ℝ) ≤ Λ) (T₁ + 1)
  have hc0 : c0 Λ T₁ < 3 / 2 := by
    calc c0 Λ T₁ ≤ 1 := by
          simp only [c0]
          exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) hηT0.le) (by norm_num))
      _ < 3 / 2 := by norm_num
  have hs0 : ((3 / 2 : ℝ) : ℂ) ∈ rectU Λ T₁ := by
    refine ⟨⟨by simpa using hc0, by norm_num⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
  have hs0r : 1 + 8 * Real.log L / L < (((3 / 2 : ℝ) : ℂ)).re := by simp; linarith
  set c := Gright P θ X₀ α γ xp y ((3 / 2 : ℝ) : ℂ) - G0 ((3 / 2 : ℝ) : ℂ)
  have hc : Complex.exp c = 1 := by
    have h1 := h.exp_Gright (s := ((3 / 2 : ℝ) : ℂ)) hs0r.le (by simp; norm_num)
    have h2 := hG0e _ hs0
    have hne0 := hne _ hs0
    simp only [c, Complex.exp_sub, h1, h2]
    exact div_self hne0
  refine ⟨fun s => G0 s + c, hG0d.add_const c, fun s hs => by
    rw [Complex.exp_add, hG0e s hs, hc, mul_one], ?_⟩
  -- uniqueness on the right part of `U`
  set V : Set ℂ := Ioo (max (c0 Λ T₁) (1 + 8 * Real.log L / L)) 2 ×ℂ Ioo (-(T₁ + 1)) (T₁ + 1)
  have hVU : V ⊆ rectU Λ T₁ := by
    rintro z ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) h1, h2⟩, h3⟩
  have hVr : ∀ z ∈ V, 1 + 8 * Real.log L / L < z.re := fun z hz =>
    lt_of_le_of_lt (le_max_right _ _) hz.1.1
  have hs0V : ((3 / 2 : ℝ) : ℂ) ∈ V := by
    refine ⟨⟨?_, by simp; norm_num⟩, hs0.2⟩
    simp only [Complex.ofReal_re]
    exact max_lt hc0 (by linarith)
  have heq := log_eq_of_exp_eq (convex_rect _ _ _ _).isPreconnected
    (L₁ := fun s => G0 s + c) (L₂ := Gright P θ X₀ α γ xp y)
    ((hG0d.add_const c).continuousOn.mono hVU)
    (fun z hz => (h.differentiableAt_Gright (hVr z hz) hz.1.2).continuousAt.continuousWithinAt)
    (fun z hz => by
      rw [Complex.exp_add, hG0e z (hVU hz), hc, mul_one,
        h.exp_Gright (hVr z hz).le hz.1.2.le])
    hs0V (by simp only [c]; ring)
  intro s hs hsr
  exact heq s ⟨⟨max_lt hs.1.1 hsr, hs.1.2⟩, hs.2⟩

end LPHyp

end LocalPNT

end
