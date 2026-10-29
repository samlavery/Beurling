module

public import RequestProject.Beurling.Noise.Lemma53Abel
public import RequestProject.Beurling.Noise.Lemma53Cert

/-!
# Lemma 5.3: the main terms `p^k ≤ z`

For `L ≥ 100`, `L < ℓ ≤ L²` and `u = ℓ/L`, the weight `F(σ) = G_V(ℓ - σ) = C₀ ρ(s) e^{φ(s)}`,
`s = (ℓ - σ)/L`, is unimodal on `[0, L]` (increasing while `s > 1`, where
`d log G_V/ds = -r(s) + φ'(s) ≤ -1 + φ'(s) < 0`, decreasing while `s < 1`), so the Abel summation
`BSaias.abel_unimodal` against `S = log + E`, `|E| ≤ K_M = 1.01` (Lemma 5.1(ii)), gives
(`main_terms_le`)

  `∑ a_i F(σ_i) ≤ L C₀ ∫_{u-1}^u ρ(s) e^{φ(s)} ds + 2 K_M C₀ ρ(u-1) e^{φ(u)}`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Dickman

namespace BSaias

/-- `G_V(s) = C₀ ρ(s) e^{φ(s)}` (the profile of Lemma 5.3 in the variable `s = ℓ'/L`). -/
noncomputable def GV (L s : ℝ) : ℝ := C0 * rho s * Real.exp (phiV L s)

/-- The derivative of `G_V` off `s = 1`. -/
noncomputable def GVd (L s : ℝ) : ℝ :=
  C0 * Real.exp (phiV L s) * ((if 1 ≤ s then -(rho (s - 1) / s) else 0) + rho s * phiV' L s)

lemma C0_pos : 0 < C0 := by unfold C0; norm_num

lemma GV_pos (L s : ℝ) : 0 < GV L s := by
  unfold GV; have := C0_pos; have := rho_pos s; positivity

lemma hasDerivAt_GV {L s : ℝ} (hs0 : -2 < s) (hs1 : s ≠ 1) :
    HasDerivAt (GV L) (GVd L s) s := by
  have hφ := (hasDerivAt_phiV L hs0).exp
  rcases lt_or_gt_of_ne hs1 with h | h
  · have hρ := hasDerivAt_rho_of_lt h
    have := ((hρ.const_mul C0).mul hφ)
    unfold GV GVd
    convert this using 1
    rw [if_neg (by linarith)]; ring
  · have hρ := hasDerivAt_rho h
    have := ((hρ.const_mul C0).mul hφ)
    unfold GV GVd
    convert this using 1
    rw [if_pos h.le]; ring

lemma continuousAt_GV {L s : ℝ} (hs0 : -2 < s) : ContinuousAt (GV L) s :=
  ((continuous_const.mul continuous_rho).continuousAt).mul
    (Real.continuous_exp.continuousAt.comp (hasDerivAt_phiV L hs0).continuousAt)

/-- `φ'(s) ≤ 1` for `0 ≤ s ≤ L`, `L ≥ 100`. -/
lemma phiV'_le_one {L s : ℝ} (hL : 100 ≤ L) (hs0 : 0 ≤ s) (hsL : s ≤ L) : phiV' L s ≤ 1 := by
  unfold phiV'
  have hL0 : 0 < L := by linarith
  rw [div_le_one hL0]
  have h1 : Real.log (s + 2) ≤ Real.log (L + 2) := Real.log_le_log (by linarith) (by linarith)
  have h2 : s / (s + 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h4 : (54 : ℝ) ≤ Real.exp 4 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (54 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this.le 4
  have h3 : Real.log (L + 2) ≤ 3 + (L + 2) / 54 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (L + 2) / Real.exp 4 by positivity)
    rw [Real.log_div (by linarith) (Real.exp_pos 4).ne', Real.log_exp] at this
    have : (L + 2) / Real.exp 4 ≤ (L + 2) / 54 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h4
    linarith
  nlinarith

/-- The sign of `G_V'`: `G_V' ≤ 0` for `1 < s ≤ L`. -/
lemma GVd_nonpos {L s : ℝ} (hL : 100 ≤ L) (hs1 : 1 < s) (hsL : s ≤ L) : GVd L s ≤ 0 := by
  unfold GVd
  rw [if_pos hs1.le]
  have hr : 1 ≤ ratio s := BSCert.dickmanRatioFacts.one_le hs1.le
  have e : rho (s - 1) / s = ratio s * rho s := by
    unfold ratio; field_simp [(rho_pos s).ne']
  rw [e]
  have h1 := phiV'_le_one hL (by linarith) hsL
  have := rho_pos s
  have : 0 < C0 * Real.exp (phiV L s) := mul_pos C0_pos (Real.exp_pos _)
  apply mul_nonpos_of_nonneg_of_nonpos this.le
  nlinarith

/-- The sign of `G_V'`: `G_V' ≥ 0` for `0 ≤ s < 1`. -/
lemma GVd_nonneg {L s : ℝ} (hL : 0 < L) (hs0 : 0 ≤ s) (hs1 : s < 1) : 0 ≤ GVd L s := by
  unfold GVd
  rw [if_neg (by linarith)]
  have := phiV'_nonneg hL hs0
  have := rho_pos s
  have := C0_pos
  positivity

/-- **The main terms** (proof of Lemma 5.3). -/
theorem main_terms_le {ι : Type*} (s : Finset ι) (a σ : ι → ℝ) {L ℓ : ℝ} (hL : 100 ≤ L)
    (hℓ1 : L < ℓ) (hℓ2 : ℓ ≤ L ^ 2) (hσ : ∀ i ∈ s, 0 ≤ σ i ∧ σ i ≤ L)
    (hE : ∀ x ∈ Icc 0 L, |∑ i ∈ s.filter (fun i => σ i ≤ x), a i - x| ≤ 1.01) :
    ∑ i ∈ s, a i * GV L ((ℓ - σ i) / L) ≤
      L * (C0 * ∫ t in (ℓ / L - 1)..(ℓ / L), rho t * Real.exp (phiV L t)) +
        2 * 1.01 * (C0 * rho (ℓ / L - 1) * Real.exp (phiV L (ℓ / L))) := by
  have hL0 : 0 < L := by linarith
  set u := ℓ / L with hu
  have hu1 : 1 < u := by rw [hu, lt_div_iff₀ hL0]; linarith
  have huL : u ≤ L := by rw [hu, div_le_iff₀ hL0]; nlinarith
  set F : ℝ → ℝ := fun x => GV L ((ℓ - x) / L)
  set F' : ℝ → ℝ := fun x => -(1 / L) * GVd L ((ℓ - x) / L)
  have hsx : ∀ x, (ℓ - x) / L = u - x / L := by intro x; rw [hu]; field_simp
  set c := min (ℓ - L) L
  have hc : c ∈ Icc 0 L := ⟨le_min (by linarith) hL0.le, min_le_right _ _⟩
  -- range of `s`
  have hsr : ∀ x ∈ Icc 0 L, u - 1 ≤ (ℓ - x) / L ∧ (ℓ - x) / L ≤ u := by
    intro x hx
    rw [hsx]
    have h1 : x / L ≤ 1 := by rw [div_le_one hL0]; exact hx.2
    have h2 : 0 ≤ x / L := div_nonneg hx.1 hL0.le
    constructor <;> linarith
  have hderF : ∀ x, (ℓ - x) / L ≠ 1 → -2 < (ℓ - x) / L → HasDerivAt F (F' x) x := by
    intro x h1 h2
    have hin : HasDerivAt (fun x => (ℓ - x) / L) (-(1 / L)) x := by
      have := ((hasDerivAt_const x ℓ).sub (hasDerivAt_id x)).div_const L
      convert this using 1; simp; ring
    have := (hasDerivAt_GV (L := L) h2 h1).comp x hin
    convert this using 1
    simp only [F']; ring
  have hs_ne : ∀ x ∈ Ioo 0 L, x ≠ c → (ℓ - x) / L ≠ 1 := by
    intro x hx hxc heq
    have : x = ℓ - L := by field_simp at heq; linarith
    apply hxc
    rw [this]; symm; apply min_eq_left
    linarith [hx.2]
  have hFc : ContinuousOn F (Icc 0 L) := by
    intro x hx
    have h := (hsr x hx).1
    have hin : Continuous (fun x => (ℓ - x) / L) := by fun_prop
    exact ((continuousAt_GV (L := L) (by linarith)).comp hin.continuousAt).continuousWithinAt
  -- integrability of `F'` on `[0, c]` and `[c, L]`
  have hF'1 : IntervalIntegrable F' volume 0 c := by
    have hcont : ContinuousOn (fun x => -(1 / L) * (C0 * Real.exp (phiV L ((ℓ - x) / L)) *
        (-(rho ((ℓ - x) / L - 1) / ((ℓ - x) / L)) + rho ((ℓ - x) / L) * phiV' L ((ℓ - x) / L))))
        (uIcc 0 c) := by
      rw [uIcc_of_le hc.1]
      intro x hx
      have hxL : x ∈ Icc 0 L := ⟨hx.1, hx.2.trans hc.2⟩
      have hs := (hsr x hxL).1
      have hs1 : 1 ≤ (ℓ - x) / L := by
        rw [le_div_iff₀ hL0]; linarith [hx.2, min_le_left (ℓ - L) L]
      have hin : Continuous (fun x => (ℓ - x) / L) := by fun_prop
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.mul
      · exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
          ((hasDerivAt_phiV L (by linarith)).continuousAt.comp hin.continuousAt))
      · apply ContinuousAt.add
        · apply ContinuousAt.neg
          apply ContinuousAt.div
          · exact (continuous_rho.comp (hin.sub continuous_const)).continuousAt
          · exact hin.continuousAt
          · linarith
        · apply ContinuousAt.mul (continuous_rho.comp hin).continuousAt
          unfold phiV'
          apply ContinuousAt.div_const
          apply ContinuousAt.mul continuousAt_const
          apply ContinuousAt.add
          · exact (Real.continuousAt_log (by linarith)).comp (hin.add continuous_const).continuousAt
          · exact (hin.continuousAt).div ((hin.add continuous_const).continuousAt) (by linarith)
    refine (hcont.intervalIntegrable).congr ?_
    intro x hx
    rw [uIoc_of_le hc.1] at hx
    have hs1 : 1 ≤ (ℓ - x) / L := by
      rw [le_div_iff₀ hL0]; linarith [hx.2, min_le_left (ℓ - L) L]
    simp only [F', GVd]
    rw [if_pos hs1]
  have hF'2 : IntervalIntegrable F' volume c L := by
    rcases eq_or_lt_of_le hc.2 with hcL | hcL
    · rw [hcL]
    have hcl : c = ℓ - L := by
      by_contra hne
      have : c = L := min_eq_right (by
        by_contra h'; push_neg at h'; exact hne (min_eq_left h'.le))
      linarith
    have hcont : ContinuousOn (fun x => -(1 / L) * (C0 * Real.exp (phiV L ((ℓ - x) / L)) *
        (0 + rho ((ℓ - x) / L) * phiV' L ((ℓ - x) / L)))) (uIcc c L) := by
      rw [uIcc_of_le hc.2]
      intro x hx
      have hxL : x ∈ Icc 0 L := ⟨hc.1.trans hx.1, hx.2⟩
      have hs := (hsr x hxL).1
      have hin : Continuous (fun x => (ℓ - x) / L) := by fun_prop
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.mul
      · exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
          ((hasDerivAt_phiV L (by linarith)).continuousAt.comp hin.continuousAt))
      · apply ContinuousAt.add continuousAt_const
        apply ContinuousAt.mul (continuous_rho.comp hin).continuousAt
        unfold phiV'
        apply ContinuousAt.div_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.add
        · exact (Real.continuousAt_log (by linarith)).comp (hin.add continuous_const).continuousAt
        · exact (hin.continuousAt).div ((hin.add continuous_const).continuousAt) (by linarith)
    refine (hcont.intervalIntegrable).congr ?_
    intro x hx
    rw [uIoc_of_le hc.2] at hx
    have hs1 : ¬ 1 ≤ (ℓ - x) / L := by
      rw [not_le, div_lt_one hL0]; linarith [hx.1]
    simp only [F', GVd]
    rw [if_neg hs1]
  have hF'i : IntervalIntegrable F' volume 0 L := hF'1.trans hF'2
  -- the signs
  have hup : ∀ x ∈ Ioo 0 c, 0 ≤ F' x := by
    intro x hx
    have hxL : x ∈ Icc 0 L := ⟨hx.1.le, (hx.2.trans_le hc.2).le⟩
    have hs1 : 1 < (ℓ - x) / L := by
      rw [lt_div_iff₀ hL0]; linarith [hx.2, min_le_left (ℓ - L) L]
    have := GVd_nonpos hL hs1 ((hsr x hxL).2.trans huL)
    simp only [F']
    have : 0 < 1 / L := by positivity
    nlinarith
  have hdown : ∀ x ∈ Ioo c L, F' x ≤ 0 := by
    intro x hx
    have hxL : x ∈ Icc 0 L := ⟨(hc.1.trans_lt hx.1).le, hx.2.le⟩
    have hcl : c = ℓ - L := by
      by_contra hne
      have : c = L := min_eq_right (by
        by_contra h'; push_neg at h'; exact hne (min_eq_left h'.le))
      linarith [hx.1, hx.2]
    have hs1 : (ℓ - x) / L < 1 := by rw [div_lt_one hL0]; linarith [hx.1]
    have := GVd_nonneg hL0 (by linarith [(hsr x hxL).1]) hs1
    simp only [F']
    have : 0 < 1 / L := by positivity
    nlinarith
  have hab := abel_unimodal s a σ hσ (by norm_num) hE hc hFc
    (fun x hx hxc => hderF x (hs_ne x hx hxc) (by linarith [(hsr x ⟨hx.1.le, hx.2.le⟩).1]))
    hF'i hup hdown (GV_pos L _).le (GV_pos L _).le
  -- `∫_0^L F = L ∫_{u-1}^u G_V`
  have hint : ∫ x in (0 : ℝ)..L, F x = L * ∫ t in (u - 1)..u, GV L t := by
    have h1 : ∫ x in (0 : ℝ)..L, F x = ∫ x in (ℓ - L)..ℓ, GV L (x / L) := by
      simp only [F]
      rw [intervalIntegral.integral_comp_sub_left (fun x => GV L (x / L)) ℓ]
      simp
    rw [h1, intervalIntegral.integral_comp_div (fun t => GV L t) hL0.ne', smul_eq_mul]
    congr 2
    rw [hu]; field_simp
  have hGint : ∫ t in (u - 1)..u, GV L t = C0 * ∫ t in (u - 1)..u, rho t * Real.exp (phiV L t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; unfold GV; ring
  -- `F(c) ≤ C₀ ρ(u-1) e^{φ(u)}`
  have hFc' : F c ≤ C0 * rho (u - 1) * Real.exp (phiV L u) := by
    have hcs := hsr c hc
    simp only [F, GV]
    have hρ : rho ((ℓ - c) / L) ≤ rho (u - 1) := rho_antitone hcs.1
    have hφ : phiV L ((ℓ - c) / L) ≤ phiV L u := phiV_mono hL0 (by linarith [hcs.1]) hcs.2
    have := C0_pos
    have := Real.exp_le_exp.mpr hφ
    have := rho_pos ((ℓ - c) / L)
    have := Real.exp_pos (phiV L ((ℓ - c) / L))
    calc C0 * rho ((ℓ - c) / L) * Real.exp (phiV L ((ℓ - c) / L)) ≤
        C0 * rho (u - 1) * Real.exp (phiV L ((ℓ - c) / L)) := by gcongr
      _ ≤ C0 * rho (u - 1) * Real.exp (phiV L u) := by
        have := rho_pos (u - 1); gcongr
  rw [hint, hGint] at hab
  calc _ ≤ _ := hab
    _ ≤ _ := by nlinarith

end BSaias

end
