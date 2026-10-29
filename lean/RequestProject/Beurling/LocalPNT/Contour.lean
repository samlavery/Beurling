module

public import RequestProject.Beurling.LocalPNT.Step8

/-!
# Step 8 of the proof of Theorem 5.24: `|𝔊₁| ≤ 190 Y(T₁)` on the contour

* `zetaSharp_im_zero`: `ζ^♯` is real on `(1, ∞)`; hence `Gright` is real on
  `(1 + 8 log log y/log y, 2]`;
* near the pole, `𝔊₁ = log gfun` and `|𝔊₁| ≤ 0.6` (`G1_near_pole`);
* on the right, `|𝔊₁(s)| ≤ 1.5 log(1/(σ-1)) + 8` (`G1_right_bound`).
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology MeasureTheory

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `ζ^♯` is real on `(1, ∞)`. -/
theorem zetaSharp_im_zero {σ : ℝ} (hσ : 1 < σ) : (zetaSharp P θ X₀ α γ xp y σ).im = 0 := by
  obtain ⟨-, hZ⟩ := h.zetaSharp_eq (s := (σ : ℂ)) (by simpa using hσ)
  rw [hZ]
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have e1 : ∑ e ∈ P.elems y, ((P.val e : ℝ) : ℂ) ^ (-(σ : ℂ)) =
      ((∑ e ∈ P.elems y, P.val e ^ (-σ) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow (P.val_pos e).le]
  have e2 : ∫ x in Ioi y, ((T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y : ℝ) : ℂ) *
      (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ x in Ioi y, (T0 θ X₀ α γ xp x - T0 θ X₀ α γ xp y) * x ^ (-σ - 1) : ℝ) : ℂ) := by
    refine Eq.trans ?_ (integral_ofReal (𝕜 := ℂ))
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans hy0 hx
    rw [show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx0.le]
    exact (Complex.ofReal_mul _ _).symm
  rw [e1, e2, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- `Gright` is real on `(1 + 8 log log y/log y, 2]`. -/
theorem Gright_im_zero {σ : ℝ} (hσ1 : 1 + 8 * Real.log (Real.log y) / Real.log y < σ)
    (hσ2 : σ ≤ 2) : (Gright P θ X₀ α γ xp y σ).im = 0 := by
  have hL := h.logy_ge
  have h8 : 0 < 8 * Real.log (Real.log y) / Real.log y :=
    div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
  have hσ : 1 < σ := by linarith
  -- `LJ` is real
  have hLJ : (LJ P y σ).im = 0 := by
    unfold LJ
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hp := P.p_pos j
    have e : (1 : ℂ) - ((P.p j : ℝ) : ℂ) ^ (-(σ : ℂ)) = ((1 - P.p j ^ (-σ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hp.le, Complex.ofReal_sub, Complex.ofReal_one]
    rw [e, ← Complex.ofReal_log (by linarith [p_rpow_neg_lt_one P j (by linarith : 0 < σ)])]
    simp
  -- `ζ_J(σ)` and `ζ^♯(σ)` are real, so `g(σ)` is real
  have hJ : (zetaF P (P.primesLe y) σ).im = 0 := by rw [zetaF_ofReal]; simp
  have hS := h.zetaSharp_im_zero hσ
  have hgre : (gJ P θ X₀ α γ xp y σ).im = 0 := by
    unfold gJ
    set a := zetaSharp P θ X₀ α γ xp y σ
    set b := zetaF P (P.primesLe y) σ
    have ha : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [hS])
    have hb : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hJ])
    rw [ha, hb, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_im]
  have hg := h.norm_g_le (s := (σ : ℂ)) (by simpa using hσ1.le) (by simpa using hσ2)
  have hL4 : (10 : ℝ) ^ 32 ≤ Real.log y ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg' : ‖gJ P θ X₀ α γ xp y σ‖ ≤ 1 / 2 := by
    by_contra hc; push_neg at hc; nlinarith
  have hg1 : (1 + gJ P θ X₀ α γ xp y σ) = ((1 + (gJ P θ X₀ α γ xp y σ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hgre]
  have hgpos : 0 < 1 + (gJ P θ X₀ α γ xp y σ).re := by
    have := Complex.abs_re_le_norm (gJ P θ X₀ α γ xp y σ)
    linarith [(abs_le.mp this).1]
  have hw : ((σ : ℂ) - 1) / σ = (((σ - 1) / σ : ℝ) : ℂ) := by push_cast; ring
  unfold Gright
  rw [Complex.add_im, Complex.add_im, hLJ, hg1, hw, ← Complex.ofReal_log hgpos.le,
    ← Complex.ofReal_log (div_nonneg (by linarith) (by linarith))]
  simp

/-- **Near the pole**: on `U ∩ ball 1 (1/14)`, `𝔊₁ = log gfun` and `|𝔊₁| ≤ 0.6`. -/
theorem G1_near_pole {T₁ : ℝ} (hT : 1 ≤ T₁)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s)
    {s : ℂ} (hsU : s ∈ rectU (Real.log X₀) T₁) (hs1 : ‖s - 1‖ < 1 / 14) :
    G s = Complex.log (gfun P θ X₀ α γ xp y s) ∧ ‖G s‖ ≤ 0.6 := by
  set Λ := Real.log X₀
  have hX := h.logX
  have hL := h.logy_ge
  have hΛ0 : 0 < Λ := by linarith
  -- `gfun` stays in `ball 1 (0.4)` on `V`
  have hc0 : ∀ w ∈ rectU Λ T₁, 1 - 8 / Λ ≤ w.re := by
    intro w hw
    have h1 := hw.1.1
    have hη := etat_le hX (T₁ + 1)
    have hη0 := etat_pos (by linarith : (1 : ℝ) ≤ Λ) (T₁ + 1)
    have hηΛ : etat Λ (T₁ + 1) * Λ ≤ 0.33769 / 442 := by
      unfold etat
      have hY := Yt_ge (Λ := Λ) (by linarith) (T₁ + 1)
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : 0.99 * etat Λ (T₁ + 1) / 3.79 ≤ 8 / Λ := by
      rw [div_le_div_iff₀ (by norm_num) hΛ0]; nlinarith
    simp only [c0] at h1
    linarith
  have hgb : ∀ w ∈ rectU Λ T₁, ‖w - 1‖ < 1 / 14 → ‖gfun P θ X₀ α γ xp y w - 1‖ ≤ 0.4 := by
    intro w hw hw1
    by_cases he : w = 1
    · subst he; simp [gfun]; norm_num
    have hwn : 13 / 14 ≤ ‖w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - w)
      rw [norm_sub_rev] at hw1; simp at this; linarith
    have hw0 : w ≠ 0 := by intro e; rw [e] at hwn; simp at hwn; linarith
    have hnp := h.near_pole' (s := w) (hc0 w hw) (by linarith) he
    simp only [gfun, Function.update_of_ne he]
    have e : (w - 1) * zetaSharp P θ X₀ α γ xp y w / w - 1 =
        ((w - 1) * zetaSharp P θ X₀ α γ xp y w - 1) / w + (1 - w) / w := by
      field_simp; ring
    rw [e]
    calc _ ≤ ‖((w - 1) * zetaSharp P θ X₀ α γ xp y w - 1) / w‖ + ‖(1 - w) / w‖ :=
          norm_add_le _ _
      _ = ‖(w - 1) * zetaSharp P θ X₀ α γ xp y w - 1‖ / ‖w‖ + ‖w - 1‖ / ‖w‖ := by
          rw [norm_div, norm_div, norm_sub_rev 1 w]
      _ ≤ (4 * (1 / 14)) / (13 / 14) + (1 / 14) / (13 / 14) := by gcongr <;> linarith
      _ ≤ 0.4 := by norm_num
  -- `G = log gfun` on `V = U ∩ ball 1 (1/14)`
  set V := rectU Λ T₁ ∩ ball (1 : ℂ) (1 / 14)
  have hVc : IsPreconnected V :=
    ((convex_rect _ _ _ _).inter (convex_ball _ _)).isPreconnected
  have hslit : ∀ w ∈ V, gfun P θ X₀ α γ xp y w ∈ Complex.slitPlane := by
    intro w hw
    have hw1 : ‖w - 1‖ < 1 / 14 := by have := hw.2; rwa [mem_ball, dist_eq_norm] at this
    have := hgb w hw.1 hw1
    apply Complex.mem_slitPlane_iff.mpr; left
    have h2 := Complex.abs_re_le_norm (gfun P θ X₀ α γ xp y w - 1)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith [(abs_le.mp h2).1]
  have hdg : DifferentiableOn ℂ (gfun P θ X₀ α γ xp y) (rectU Λ T₁) := by
    -- from `gfun_rect` we only need differentiability, which does not use `hyr`
    intro w hw
    by_cases hw1 : w = 1
    · subst hw1
      have := h.differentiableOn_gfun_ball
      exact (this.differentiableAt (ball_mem_nhds 1 (by positivity))).differentiableWithinAt
    · refine (h.differentiableAt_gfun ?_ hw1).differentiableWithinAt
      have := hc0 w hw
      have : 8 / Λ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      linarith [h.theta_mem.2]
  -- the base point `1 + 1/20`
  set s₀ : ℂ := ((1 + 1 / 20 : ℝ) : ℂ)
  have hs₀re : s₀.re = 1 + 1 / 20 := by simp [s₀]
  have h8 : 8 * Real.log (Real.log y) / Real.log y < 1 / 20 := by
    have hl := Real.log_le_rpow_div (x := Real.log y) (by linarith)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [div_lt_iff₀ (by linarith)]
    have h2' : Real.log y ^ (1 / 2 : ℝ) * Real.log y ^ (1 / 2 : ℝ) = Real.log y := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h4 : (10 : ℝ) ^ 4 ≤ Real.log y ^ (1 / 2 : ℝ) := by
      have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ Real.log y ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hL (by norm_num)
      rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
        rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num] at this
    have h5 : 0 ≤ Real.log y ^ (1 / 2 : ℝ) := by positivity
    rw [div_div_eq_mul_div] at hl
    nlinarith
  have hs₀U : s₀ ∈ rectU Λ T₁ := by
    refine ⟨⟨?_, by rw [hs₀re]; norm_num⟩, ⟨by simp [s₀]; linarith, by simp [s₀]; linarith⟩⟩
    have hη0 := etat_pos (by linarith : (1 : ℝ) ≤ Λ) (T₁ + 1)
    have : c0 Λ T₁ ≤ 1 := by
      simp only [c0]
      exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) hη0.le) (by norm_num))
    rw [hs₀re]; linarith
  have hs₀V : s₀ ∈ V := ⟨hs₀U, by
    have e : s₀ - 1 = ((1 / 20 : ℝ) : ℂ) := by simp only [s₀]; push_cast; ring
    rw [mem_ball, dist_eq_norm, e, Complex.norm_real, Real.norm_eq_abs]
    norm_num⟩
  have hGs₀ : G s₀ = Complex.log (gfun P θ X₀ α γ xp y s₀) := by
    rw [hGr s₀ hs₀U (by rw [hs₀re]; linarith), ← h.exp_Gright (by rw [hs₀re]; linarith)
      (by rw [hs₀re]; norm_num), Complex.log_exp]
    · have := h.Gright_im_zero (σ := 1 + 1 / 20) (by linarith) (by norm_num)
      rw [this]; linarith [Real.pi_pos]
    · have := h.Gright_im_zero (σ := 1 + 1 / 20) (by linarith) (by norm_num)
      rw [this]; exact Real.pi_pos.le
  have hrel := log_eq_of_exp_eq hVc (L₁ := G) (L₂ := fun w => Complex.log (gfun P θ X₀ α γ xp y w))
    (hGd.continuousOn.mono Set.inter_subset_left)
    (fun w hw => ((hdg.differentiableAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hw.1)
      ).continuousAt.clog (hslit w hw)).continuousWithinAt)
    (fun w hw => by
      rw [hGe w hw.1, Complex.exp_log]
      intro e; have := hslit w hw; rw [e] at this; simp at this)
    hs₀V hGs₀
  have hsV : s ∈ V := ⟨hsU, by rw [mem_ball, dist_eq_norm]; exact hs1⟩
  refine ⟨hrel s hsV, ?_⟩
  rw [hrel s hsV]
  have hb := hgb s hsU hs1
  have := Complex.norm_log_one_add_half_le_self (z := gfun P θ X₀ α γ xp y s - 1)
    (by linarith)
  rw [add_sub_cancel] at this
  linarith

/-- `|log ζ_J(s)| ≤ 1.5 log ζ_J(σ)` for `σ > 1`. -/
theorem norm_LJ_le {s : ℂ} (hs : 1 < s.re) :
    ‖LJ P y s‖ ≤ 1.5 * Real.log (zetaFR P (P.primesLe y) s.re) := by
  unfold LJ zetaFR
  rw [Real.log_prod (fun j _ => (factorR_pos P j (by linarith)).ne')]
  calc ‖∑ j ∈ P.primesLe y, -Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s))‖
      ≤ ∑ j ∈ P.primesLe y, ‖-Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ P.primesLe y, 1.5 * Real.log (1 - P.p j ^ (-s.re))⁻¹ := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hp2 := h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)
        have hq : ‖-((P.p j : ℝ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
          rw [norm_neg, norm_p_cpow_neg]
          calc P.p j ^ (-s.re) ≤ P.p j ^ (-(1 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = 1 / P.p j := by rw [Real.rpow_neg_one, one_div]
            _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
        have h1 := Complex.norm_log_one_add_half_le_self hq
        rw [← sub_eq_add_neg, norm_neg] at h1
        rw [norm_neg]
        refine h1.trans ?_
        rw [norm_p_cpow_neg]
        have hx0 : 0 < P.p j ^ (-s.re) := Real.rpow_pos_of_pos (P.p_pos j) _
        have hx1 : P.p j ^ (-s.re) < 1 := p_rpow_neg_lt_one P j (by linarith)
        have := Real.log_le_sub_one_of_pos (show 0 < 1 - P.p j ^ (-s.re) by linarith)
        rw [Real.log_inv]
        nlinarith
    _ = 1.5 * ∑ j ∈ P.primesLe y, Real.log (1 - P.p j ^ (-s.re))⁻¹ := by rw [Finset.mul_sum]

/-- `log ζ_J(σ) ≤ log(1/(σ-1)) + 2.3` for `1 + 8 log log y/log y ≤ σ ≤ 9/8`. -/
theorem log_zetaFR_le {σ : ℝ} (hσ1 : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ σ)
    (hσ2 : σ ≤ 9 / 8) :
    Real.log (zetaFR P (P.primesLe y) σ) ≤ Real.log (1 / (σ - 1)) + 2.3 := by
  have hL := h.logy_ge
  set L := Real.log y
  have h8 : 0 < 8 * Real.log L / L :=
    div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
  have hσ : 1 < σ := by linarith
  have hZ := h.zetaFR_le hσ (by linarith)
  have hE := h.rpow_mul_log_pow_le hσ1
  have hEL : y ^ (1 - σ) * (Real.exp 11 * Real.log y ^ (2 : ℝ)) ≤ 1 := by
    have he11 : Real.exp 11 ≤ 60000 := by
      have e : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
        _ ≤ 60000 := by norm_num
    rw [Real.rpow_two]
    have hyp : 0 ≤ y ^ (1 - σ) := Real.rpow_nonneg (lt_of_lt_of_le h.X0_pos h.y_ge).le _
    have hL6 : (10 : ℝ) ^ 48 ≤ L ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hL 6; norm_num at this ⊢; linarith
    have h2 : y ^ (1 - σ) * L ^ 2 ≤ 1 / 10 ^ 48 := by
      rw [le_div_iff₀ (by norm_num)]
      have : y ^ (1 - σ) * L ^ 8 = y ^ (1 - σ) * L ^ 2 * L ^ 6 := by ring
      nlinarith [mul_nonneg hyp (sq_nonneg L)]
    calc y ^ (1 - σ) * (Real.exp 11 * L ^ 2) = Real.exp 11 * (y ^ (1 - σ) * L ^ 2) := by ring
      _ ≤ 60000 * (1 / 10 ^ 48) := mul_le_mul he11 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hκ := (kap_facts h.logX).2.2.2.1
  have hη0 : 0 < σ - 1 := by linarith
  have hZ' : zetaFR P (P.primesLe y) σ ≤ 9.9 / (σ - 1) := by
    have h1 : (1 + 2 * kap X₀) / (σ - 1) ≤ 1.02 / (σ - 1) :=
      div_le_div_of_nonneg_right (by linarith) hη0.le
    have h71 : 71 ≤ 8.88 / (σ - 1) := by rw [le_div_iff₀ hη0]; nlinarith
    have : (9.9 : ℝ) / (σ - 1) = 1.02 / (σ - 1) + 8.88 / (σ - 1) := by ring
    linarith
  have hZpos := zetaFR_pos P (P.primesLe y) (by linarith : (0 : ℝ) < σ)
  calc Real.log (zetaFR P (P.primesLe y) σ) ≤ Real.log (9.9 / (σ - 1)) :=
        Real.log_le_log hZpos hZ'
    _ = Real.log 9.9 + Real.log (1 / (σ - 1)) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
    _ ≤ Real.log (1 / (σ - 1)) + 2.3 := by
        have : Real.log 9.9 ≤ 2.3 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2.3 by norm_num) 8
          norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
        linarith

/-- `|log((s-1)/s)| ≤ 4.2` for `|Im s| ≥ 1`, `|Re s - 1| ≤ 1/8`. -/
lemma norm_log_sub_one_div_le' {s : ℂ} (hi : 1 ≤ |s.im|) (hr : |s.re - 1| ≤ 1 / 8) :
    ‖Complex.log ((s - 1) / s)‖ ≤ 4.2 := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at hi; simp at hi; linarith
  have hn1 : |s.im| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa using this
  have hn2 : ‖s - 1‖ ≤ |s.im| + 1 / 8 := by
    have := Complex.norm_le_abs_re_add_abs_im (s - 1); simp at this; linarith
  have hn3 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hn4 : ‖s‖ ≤ |s.im| + 1.125 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have : |s.re| ≤ 1.125 := by rw [abs_le]; constructor <;> linarith [(abs_le.mp hr).1,
      (abs_le.mp hr).2]
    linarith
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set w := ‖s - 1‖ / ‖s‖
  have hw : ‖(s - 1) / s‖ = w := norm_div _ _
  have hwlo : 1 / 2.125 ≤ w := by
    simp only [w]; rw [le_div_iff₀ hpos]
    have : ‖s‖ / 2.125 ≤ |s.im| := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hwhi : w ≤ 1.125 := by
    simp only [w]; rw [div_le_iff₀ hpos]; nlinarith
  have hlog : |Real.log w| ≤ 1 := by
    rw [abs_le]; constructor
    · have := Real.log_le_log (by norm_num) hwlo
      have h20 : Real.log (1 / 2.125) ≥ -1 := by
        rw [one_div, Real.log_inv, ge_iff_le, neg_le_neg_iff]
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.exp_one_gt_d9; linarith
      linarith
    · have := Real.log_le_sub_one_of_pos (by linarith : 0 < w); linarith
  have h5 := norm_log_le_abs_log_add_pi ((s - 1) / s)
  rw [hw] at h5
  linarith [Real.pi_lt_d2]

/-- **The right part** (Steps 8, 10): `|Gright(s)| ≤ 1.5 log(1/(σ-1)) + 8` for
`1 + 8 log log y/log y ≤ σ ≤ 9/8`, `|t| ≥ 1`. -/
theorem norm_Gright_le {s : ℂ} (hs1 : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ s.re)
    (hs2 : s.re ≤ 9 / 8) (hi : 1 ≤ |s.im|) :
    ‖Gright P θ X₀ α γ xp y s‖ ≤ 1.5 * Real.log (1 / (s.re - 1)) + 8 := by
  have hL := h.logy_ge
  have h8 : 0 < 8 * Real.log (Real.log y) / Real.log y :=
    div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
  have hσ : 1 < s.re := by linarith
  have hLJ := h.norm_LJ_le hσ
  have hZ := h.log_zetaFR_le hs1 hs2
  have hg := h.norm_g_le hs1 (by linarith)
  have hL4 : (10 : ℝ) ^ 32 ≤ Real.log y ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg' : ‖gJ P θ X₀ α γ xp y s‖ ≤ 1 / 10 ^ 32 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [norm_nonneg (gJ P θ X₀ α γ xp y s)]
  have hlg : ‖Complex.log (1 + gJ P θ X₀ α γ xp y s)‖ ≤ 3 / 2 * (1 / 10 ^ 32) :=
    (Complex.norm_log_one_add_half_le_self (hg'.trans (by norm_num))).trans (by linarith)
  have hlw := h.norm_log_sub_one_div_le' hi (by rw [abs_le]; constructor <;> linarith)
  unfold Gright
  calc _ ≤ ‖LJ P y s‖ + ‖Complex.log (1 + gJ P θ X₀ α γ xp y s)‖ +
        ‖Complex.log ((s - 1) / s)‖ := norm_add₃_le
    _ ≤ _ := by nlinarith

/-- **`|𝔊₁| ≤ 190 Y(T₁)` on the contour** (Step 8): on the segment `σ = c' = 1 - 0.9 δ(T₁)`,
`|t| ≤ T₁`, and on the horizontal segments `t = ±T₁`, `c' ≤ σ ≤ 9/8`. -/
theorem G1_contour_bound {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s) :
    (∀ t : ℝ, |t| ≤ T₁ →
      ‖G (((1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 : ℝ) : ℂ) + t * I)‖ ≤
        190 * Yt (Real.log X₀) T₁) ∧
    (∀ σ : ℝ, 1 - 0.9 * etat (Real.log X₀) T₁ / 3.79 ≤ σ → σ ≤ 9 / 8 → ∀ t : ℝ, |t| = T₁ →
      ‖G ((σ : ℂ) + t * I)‖ ≤ 190 * Yt (Real.log X₀) T₁) := by
  set Λ := Real.log X₀
  set L := Real.log y
  have hX := h.logX
  have hL := h.logy_ge
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  set ηT := etat Λ T₁
  have hηT0 : 0 < ηT := etat_pos hΛ1 T₁
  have hηTs : ηT ≤ 1 / 10 ^ 10 := etat_le hX T₁
  have hηT1 := etat_ge_near (Λ := Λ) (t := T₁) (t' := T₁ + 1) hΛ1
    (by rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_pos (by linarith), abs_of_pos (by linarith)])
  have hY1 := Yt_ge hΛ1 T₁
  set c' := 1 - 0.9 * ηT / 3.79 with hc'def
  have hc'U : c0 Λ T₁ < c' := by
    simp only [c0, c']
    have : 0.9 * ηT / 3.79 < 0.99 * etat Λ (T₁ + 1) / 3.79 := by
      apply div_lt_div_of_pos_right _ (by norm_num); nlinarith
    linarith
  have hc'1 : |c' - 1| ≤ 1 / 10 ^ 10 := by
    simp only [c']
    rw [abs_le]; constructor
    · have : 0.9 * ηT / 3.79 ≤ 1 / 10 ^ 10 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    · have : 0 ≤ 0.9 * ηT / 3.79 := by positivity
      linarith
  have hmemU : ∀ σ t : ℝ, c' ≤ σ → σ ≤ 9 / 8 → |t| ≤ T₁ → ((σ : ℂ) + t * I) ∈ rectU Λ T₁ := by
    intro σ t h1 h2 h3
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp; linarith
    · simp; linarith
    · simp; linarith [(abs_le.mp h3).1]
    · simp; linarith [(abs_le.mp h3).2]
  -- the disc bound at a height `t` with `1/16 ≤ |t| ≤ T₁`
  have hdisc : ∀ σ t : ℝ, 1 / 16 ≤ |t| → |t| ≤ T₁ → c' ≤ σ → σ ≤ 9 / 8 →
      |σ - (1 + etat Λ t)| ≤ etat Λ t + 0.9 * (etat Λ t / 3.79) →
      ‖G ((σ : ℂ) + t * I)‖ ≤ 190 * Yt Λ T₁ := by
    intro σ t h1 h2 h3 h4 h5
    have hb := h.G1_disc_bound hT hyr hTy hGd hGe hGr (t := t) h1 h2
      (s := (σ : ℂ) + t * I) (by
        have e : (σ : ℂ) + t * I - (((1 + etat Λ t : ℝ) : ℂ) + t * I) =
            ((σ - (1 + etat Λ t) : ℝ) : ℂ) := by push_cast; ring
        rw [e, Complex.norm_real, Real.norm_eq_abs]; exact h5) (hmemU σ t h3 h4 h2)
    have hYm := Yt_mono (Λ := Λ) hΛ1 (show |t| ≤ |T₁| by
      rw [abs_of_pos (show (0 : ℝ) < T₁ by linarith)]; exact h2)
    linarith
  refine ⟨fun t ht => ?_, fun σ hσ1 hσ2 t ht => ?_⟩
  · by_cases ht16 : 1 / 16 ≤ |t|
    · apply hdisc c' t ht16 ht le_rfl (by linarith [(abs_le.mp hc'1).2])
      have hmono := etat_anti (Λ := Λ) hΛ1 (show |t| ≤ |T₁| by
        rw [abs_of_pos (show (0 : ℝ) < T₁ by linarith)]; exact ht)
      have hηt0 := etat_pos hΛ1 t
      simp only [c']
      rw [abs_le]; constructor
      · have : 0.9 * ηT / 3.79 ≤ 0.9 * (etat Λ t / 3.79) := by
          rw [mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right hmono (by norm_num)
        linarith
      · have : 0 ≤ 0.9 * ηT / 3.79 := by positivity
        have : 0 ≤ 0.9 * (etat Λ t / 3.79) := by positivity
        linarith
    · push_neg at ht16
      have hn : ‖(c' : ℂ) + t * I - 1‖ < 1 / 14 := by
        have := Complex.norm_le_abs_re_add_abs_im ((c' : ℂ) + t * I - 1)
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.sub_im,
          Complex.add_im, Complex.mul_im, Complex.one_im] at this
        norm_num at this
        linarith [(abs_le.mp hc'1).1, (abs_le.mp hc'1).2]
      have := (h.G1_near_pole hT hGd hGe hGr (hmemU c' t le_rfl (by linarith
        [(abs_le.mp hc'1).2]) ht) hn).2
      linarith
  · have htT : |t| ≤ T₁ := ht.le
    have ht16 : 1 / 16 ≤ |t| := by rw [ht]; linarith
    have hLtt : Lt t = Lt T₁ := by
      unfold Lt; rw [ht, abs_of_pos (show (0 : ℝ) < T₁ by linarith)]
    have hηt : etat Λ t = ηT := by
      simp only [ηT, etat, Yt, hLtt]
    by_cases hσr : σ ≤ 1 + ηT + (ηT + 0.9 * (ηT / 3.79))
    · apply hdisc σ t ht16 htT hσ1 hσ2
      rw [hηt, abs_le]; constructor
      · simp only [c'] at hσ1
        have : 0.9 * ηT / 3.79 = 0.9 * (ηT / 3.79) := by ring
        linarith
      · linarith
    · push_neg at hσr
      have hη16 : 16 * Real.log L / L ≤ ηT := by
        refine etat_ge_of_height hX hL hyr (le_trans (Lt_mono ?_) hTy)
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      have hσr' : 1 + 8 * Real.log L / L < σ := by
        have hLL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
        have : 8 * Real.log L / L ≤ 16 * Real.log L / L :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        have : 0 ≤ 0.9 * (ηT / 3.79) := by positivity
        linarith
      have hmem := hmemU σ t hσ1 hσ2 htT
      rw [hGr _ hmem (by simpa using hσr')]
      have hb := h.norm_Gright_le (s := (σ : ℂ) + t * I) (by simpa using hσr'.le)
        (by simpa using hσ2) (by simpa using (show (1 : ℝ) ≤ |t| by rw [ht]; exact hT))
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero] at hb
      have hpos9 : 0 ≤ 0.9 * (ηT / 3.79) := by positivity
      have hlog : Real.log (1 / (σ - 1)) ≤ Real.log (1 / ηT) := by
        apply Real.log_le_log (by apply div_pos one_pos; linarith)
        apply one_div_le_one_div_of_le hηT0; linarith
      have hQ := Q_le_Y (Λ := Λ) (t := T₁) hX
      have hLt := Lt_nonneg T₁
      have hlΛ := Real.log_nonneg hΛ1
      linarith

/-- `𝔊₁(1) = 0`. -/
theorem G1_one {T₁ : ℝ} (hT : 1 ≤ T₁)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s) : G 1 = 0 := by
  have hX := h.logX
  have hΛ1 : (1 : ℝ) ≤ Real.log X₀ := by linarith
  have hη0 := etat_pos hΛ1 (T₁ + 1)
  have h1U : (1 : ℂ) ∈ rectU (Real.log X₀) T₁ := by
    refine ⟨⟨?_, by norm_num⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
    simp only [Complex.one_re, c0]
    have : 0 < 0.99 * etat (Real.log X₀) (T₁ + 1) / 3.79 := by positivity
    linarith
  have := (h.G1_near_pole hT hGd hGe hGr h1U (by simp)).1
  rw [this]; simp [gfun]

end LPHyp

end LocalPNT

end
