module

public import RequestProject.Beurling.LocalPNT.Identity
public import RequestProject.Beurling.LocalPNT.Step10
public import RequestProject.Beurling.LocalPNT.Num10
public import RequestProject.Beurling.LocalPNT.MainTerm

/-!
# Theorem 5.24(iii): short windows

`∫ φ dΠ ≤ (1 + Rel) ∫ φ dΠ₀` for the window `φ = lpWindow v η` of Step 10, with `Rel` bounded by
(eq. lpplus) (`lp_iii`). Mellin inversion (`identity_Gright`) writes `∫ φ d(Π - Π₀)` as
`(1/2π) ∫ Φ(c+it) 𝔊₁(c+it) dt`, `c = 1 + 17 log Λ_p/Λ_p`; the contour estimate of Step 10 and the
numerics (`Num10`) bound it by `Rel · ηv/(1.0001 Λ_p) ≤ Rel ∫ φ dΠ₀`.
-/

@[expose] public section

open Set Real Complex MeasureTheory Construction

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `c₁(y) < 1 + 17 log Λ_p/Λ_p` for `e^e ≤ v ≤ y`. -/
lemma c1_lt_c {v : ℝ} (hv : Real.exp 1 ≤ Real.log v) (hvy : v ≤ y) (hv0 : 0 < v) :
    c1 y < 1 + 17 * Real.log (Real.log v) / Real.log v := by
  have hL := h.logy_ge
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hlv : Real.log v ≤ Real.log y := Real.log_le_log hv0 hvy
  have hanti := Real.log_div_self_antitoneOn (show Real.log v ∈ {x : ℝ | Real.exp 1 ≤ x} from hv)
    (show Real.log y ∈ {x : ℝ | Real.exp 1 ≤ x} from hv.trans hlv) hlv
  simp only at hanti
  have hpos : 0 < Real.log (Real.log v) / Real.log v := by
    apply div_pos (Real.log_pos (lt_of_lt_of_le (by
      have := Real.exp_one_gt_d9; linarith) hv)) (lt_of_lt_of_le (Real.exp_pos 1) hv)
  rw [c1_def]
  have e1 : 8 * Real.log (Real.log y) / Real.log y = 8 * (Real.log (Real.log y) / Real.log y) := by
    ring
  have e2 : 17 * Real.log (Real.log v) / Real.log v =
      17 * (Real.log (Real.log v) / Real.log v) := by ring
  rw [e1, e2]
  linarith

set_option maxHeartbeats 4000000 in
/-- **Theorem 5.24(iii)** (short windows). -/
theorem lp_iii {v η : ℝ} (hv1 : 1 < v) (hP : 76 * Real.log X₀ ^ 3 ≤ Real.log v)
    (hη1 : Real.exp (-(2 * Real.log X₀)) ≤ η) (hη2 : η ≤ 1 / 2) (hy : v * (1 + 2 * η) ≤ y) :
    piInt P (lpWindow v η) ≤ (1 + relBound (Real.log X₀) v η) * pi0Int (lpWindow v η) := by
  set Λ := Real.log X₀ with hΛdef
  have hX := h.logX
  have hyp : Num10.Hyp Λ v η := ⟨hX, hv1, hP, hη1, hη2⟩
  have hv0 : 0 < v := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hη1
  have hPpos := hyp.P_pos
  have hPbig : 10 ^ 25 ≤ Real.log v := by
    have : (10 ^ 8 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    nlinarith
  have hlv1 : 1 ≤ Real.log v := by linarith
  have hvy : v ≤ y := le_trans (by nlinarith) hy
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hlvy : Real.log v ≤ Real.log y := Real.log_le_log hv0 hvy
  -- the height `T₁` and the logarithm `𝔊₁`
  set L₁ := lpL1 v η
  set T₁ := Real.exp L₁
  have hT1 : 1 ≤ T₁ := Real.one_le_exp (by linarith [Num10.five_le_L1 hyp])
  have hyr := Num10.yrange hyp hlvy
  have hTy := Num10.Lt_le_logTy hyp hlvy
  have hGb := Num10.Yt_le_Gb hyp
  have hEA := Num10.exp_c'_le hyp
  have hEC := Num10.exp_c_le hyp
  have hR := Num10.contour_le_relBound_mul hyp
  have hcs1 := Num10.c_sub_one_le hyp
  have hp54 := hyp.p_ge
  obtain ⟨hMi, hM⟩ := pi0Int_lpWindow_ge hv1 (by linarith) hη0 hη2
  simp only at hR
  obtain ⟨G, hGd, hGe, hGr⟩ := h.exists_G1 hT1 hyr hTy
  -- the window and its transform
  set a := Real.log v
  set b := Real.log (v * (1 + η))
  set ω := lpW v η / 4
  set k := lpK v η
  have hω : 0 < ω := by have := lpW_pos hlv1 hη0; positivity
  have hk : 1 ≤ k := one_le_lpK hlv1 hη0 hη2
  have hab : a ≤ b := Real.log_le_log hv0 (by nlinarith)
  have hb0 : 0 ≤ b + 2 * ω := by
    have : 0 ≤ b := Real.log_nonneg (by nlinarith)
    linarith
  set ψ := windowLog a b ω k
  obtain ⟨hψ01, hψ1, hψsupp, hψc⟩ := windowLog_props hab hω hk
  set c := 1 + 17 * Real.log (Real.log v) / Real.log v
  have hc1 : c1 y < c := h.c1_lt_c (by
    have := Real.exp_one_lt_d9; linarith) hvy hv0
  have hc98 : c ≤ 9 / 8 := by
    have hl := Real.log_le_rpow_div (x := Real.log v) (by linarith)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2' : Real.log v ^ (1 / 2 : ℝ) * Real.log v ^ (1 / 2 : ℝ) = Real.log v := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h4 : (10 : ℝ) ^ 4 ≤ Real.log v ^ (1 / 2 : ℝ) := by
      have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ Real.log v ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
      rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
        rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num] at this
    have h5 : 0 ≤ Real.log v ^ (1 / 2 : ℝ) := by positivity
    rw [div_div_eq_mul_div] at hl
    simp only [c]
    have : 17 * Real.log (Real.log v) / Real.log v ≤ 1 / 8 := by
      rw [div_le_iff₀ hPpos]; nlinarith
    linarith
  have hc1' : 1 < c1 y := h.c1_gt
  -- the support of `ψ` lies below `log y`
  have hwη : lpW v η ≤ η / 10 ^ 16 := by
    unfold lpW
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (10 : ℝ) ^ 16 ≤ Real.log v ^ 2 := by nlinarith
    nlinarith
  have hD : b - a + 2 * ω ≤ 1.0001 * η := by
    have h1 : b - a = Real.log (1 + η) := by
      simp only [a, b]; rw [Real.log_mul hv0.ne' (by linarith)]; ring
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + η by linarith)
    simp only [ω]; linarith
  have hx₀ : b + 2 * ω < Real.log y := by
    have hq : 0 < y / (v * (1 + η)) := by positivity
    have hl := Real.one_sub_inv_le_log_of_pos hq
    rw [Real.log_div hy0.ne' (by positivity)] at hl
    have hinv : (y / (v * (1 + η)))⁻¹ ≤ (1 + η) / (1 + 2 * η) := by
      rw [inv_div, div_le_div_iff₀ hy0 (by linarith)]
      nlinarith
    have h2 : 1 - (1 + η) / (1 + 2 * η) = η / (1 + 2 * η) := by field_simp; ring
    have h3 : η / 2 ≤ η / (1 + 2 * η) := div_le_div_of_nonneg_left hη0.le (by linarith)
      (by linarith)
    simp only [ω, b]; linarith
  have hfsupp : ∀ x, b + 2 * ω < x → ψ x = 0 := by
    intro x hx
    by_contra hc
    have := (hψsupp x hc).2
    linarith
  have hcs : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a - 2 * ω) (b := b + 2 * ω)) ?_
    intro x hx; by_contra hc; exact hx (hψsupp x hc)
  have hfint : ∀ σ : ℝ, c ≤ σ → Integrable (fun x : ℝ => ψ x * Real.exp (σ * x)) := by
    intro σ _
    exact (hψc.mul (by fun_prop)).integrable_of_hasCompactSupport (hcs.mul_right)
  set c₀ := (c1 y + c) / 2
  have hFd : DifferentiableOn ℂ (PhiW a b ω k) {s : ℂ | c₀ < s.re} :=
    (differentiableOn_PhiW hab hω hk).mono fun s hs => by
      show 0 < s.re; have : c₀ < s.re := hs; simp only [c₀] at this; linarith
  have hFb : ∀ σ : ℝ, c ≤ σ → ∀ t : ℝ, ‖PhiW a b ω k (σ + t * I)‖ ≤
      (2 * (b - a + 2 * ω) + 4 * k / ω) * Real.exp (σ * (b + 2 * ω)) * (1 + σ) / (1 + t ^ 2) := by
    intro σ hσ t
    have := norm_PhiW_le_sq hab hω hk (σ := σ) (by linarith) t
    refine this.trans ?_
    have hK : 0 ≤ (2 * (b - a + 2 * ω) + 4 * k / ω) * Real.exp (σ * (b + 2 * ω)) := by
      have : 0 ≤ b - a := by linarith
      positivity
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  obtain ⟨hI, hid⟩ := h.identity_Gright (f := ψ) hψc hx₀ hfsupp (c₀ := c₀) (c := c)
    (by simp only [c₀]; linarith) (by simp only [c₀]; linarith) (by linarith) hFd
    (fun s _ => rfl) hfint hFb
  -- the identity in terms of `Π` and `Π₀`
  have hS : piInt P (lpWindow v η) = ∑ jk ∈ P.pps y,
      ψ (Real.log (P.p jk.1 ^ (jk.2 + 1))) / ((jk.2 : ℝ) + 1) := by
    unfold piInt
    rw [finsum_eq_sum_of_support_subset _ (s := P.pps y) ?_]
    · refine Finset.sum_congr rfl fun jk _ => ?_
      simp only [lpWindow, if_pos (⟨P.pp_pos jk, hv0⟩ : 0 < P.p jk.1 ^ (jk.2 + 1) ∧ 0 < v)]; rfl
    · intro jk hjk
      simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hjk
      rw [Finset.mem_coe, BeurlingSystem.mem_pps]
      have hpos := P.pp_pos jk
      simp only [lpWindow, if_pos (⟨hpos, hv0⟩ : 0 < P.p jk.1 ^ (jk.2 + 1) ∧ 0 < v)] at hjk
      have := (hψsupp _ hjk.1).2
      have hlt : Real.log (P.p jk.1 ^ (jk.2 + 1)) < Real.log y := by
        simp only [ψ, a, b, ω, k] at *; linarith
      exact ((Real.log_lt_log_iff hpos hy0).mp hlt).le
  have hS0 : pi0Int (lpWindow v η) = ∫ u in Ioi (1 : ℝ), ψ (Real.log u) * pi0Dens u := by
    unfold pi0Int
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have : (0 : ℝ) < u := lt_trans one_pos hu
    simp only [lpWindow, if_pos (⟨this, hv0⟩ : 0 < u ∧ 0 < v)]; rfl
  have hdiff : piInt P (lpWindow v η) - pi0Int (lpWindow v η) ≤
      (1 / (2 * π)) * ‖∫ t : ℝ, PhiW a b ω k (c + t * I) * Gright P θ X₀ α γ xp y (c + t * I)‖ := by
    rw [hS, hS0]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ← hid, norm_mul]
    apply le_of_eq; congr 1
    rw [norm_div, norm_mul]; simp [abs_of_pos Real.pi_pos]
  have hCE := h.contour_estimate hT1 hyr hTy hGd hGe hGr hab hω hk hb0 hc1 hc98 hGb hI
  rw [show T₁ = Real.exp (lpL1 v η) from rfl, show Real.log (X₀ : ℝ) = Λ from rfl,
    mul_div_assoc] at hCE
  set δ := etat Λ (Real.exp (lpL1 v η)) / 3.79 with hδdef
  set Gb := GLam Λ (lpL1 v η)
  set T := Real.exp (lpL1 v η)
  set q := (k : ℝ) / (T * ω)
  have hGb0 : 0 < Gb := Num10.Gb_pos hyp
  have hδ0 : 0 ≤ δ := div_nonneg (etat_pos (by linarith) _).le (by norm_num)
  have hT0 : 0 < T := Real.exp_pos _
  have hq0 : 0 ≤ q := by positivity
  have hc1'' : 1 < c := by linarith
  have hcc : 0 ≤ c - (1 - 0.9 * δ) := by linarith
  have hlogc : 0 ≤ Real.log (1 / (c - 1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    simp only [c]; linarith
  have hD0 : 0 ≤ b - a + 2 * ω := by linarith
  have key : Gb * Real.exp ((1 - 0.9 * δ) * (b + 2 * ω)) *
          (8 * Real.log (1 + (b - a + 2 * ω) * T / 2)) +
        2 * (c - (1 - 0.9 * δ)) * Gb * Real.exp (c * (b + 2 * ω)) * (2 / T) * q ^ k +
      (1.5 * Real.log (1 / (c - 1)) + 8) * Real.exp (c * (b + 2 * ω)) * (4 / k) * q ^ k ≤
      Gb * (1.51 * v ^ (1 - 0.9 * δ)) * (8 * Real.log (1 + 1.0001 * η * T / 2)) +
        2 * (c - (1 - 0.9 * δ)) * Gb * (1.6 * v ^ c) * (2 / T) * q ^ k +
      (1.5 * Real.log (1 / (c - 1)) + 8) * (1.6 * v ^ c) * (4 / k) * q ^ k := by
    have hl0 : 0 ≤ Real.log (1 + (b - a + 2 * ω) * T / 2) :=
      Real.log_nonneg (by have : 0 ≤ (b - a + 2 * ω) * T / 2 := by positivity
                          linarith)
    gcongr
  have hrel0 : 0 ≤ relBound Λ v η := by
    unfold relBound
    have := Num10.Gb_pos hyp
    positivity
  have hfin : piInt P (lpWindow v η) - pi0Int (lpWindow v η) ≤
      relBound Λ v η * pi0Int (lpWindow v η) := by
    refine hdiff.trans ?_
    refine le_trans ?_ (hR.trans (mul_le_mul_of_nonneg_left hM hrel0))
    have hpi : 0 < 1 / (2 * π) := by positivity
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hCE.trans key) hpi.le
  linarith

end LPHyp

end LocalPNT

end
