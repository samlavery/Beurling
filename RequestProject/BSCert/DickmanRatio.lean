module

public import RequestProject.BSCert.DickmanFn

/-!
# The Dickman ratio `r = -ρ'/ρ`: facts (R2)–(R4)

`r(v) := ρ(v-1)/(v ρ(v))`, which is `-ρ'(v)/ρ(v)` for `v > 1`. We prove the facts of the paper
(Section 5.2, "Facts on Dickman's function"):

* `ratio_one_two` : `r(v) = 1/(v(1 - log v))` on `[1, 2]`;
* `ratio_strictMonoOn` : (R2) `r` is strictly increasing on `[1, ∞)`;
* `ratio_recursion` : (R3) `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})` for `v ≥ 2`;
* `ratio_upper` : (R4) `r(x) ≤ log((x+1)/δ)/(1-δ)` for `x ≥ 1`, `0 < δ < 1`.

The proof of (R2) follows the paper: with `I(v) := v ρ(v)/ρ(v-1) = 1/r(v)` one has, for `v > 2`,
`I'(v) ρ(v-1) = J(v) := r(v-1) v ρ(v) + ρ(v) - ρ(v-1) = ∫_{v-1}^v ρ(t) (r(v-1) - r(t)) dt`,
which is negative as long as `r` is strictly increasing on `[v-1, v]`; a continuity
("first failure") argument then propagates strict monotonicity from `[1, 2]` to `[1, ∞)`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace Dickman

/-- The Dickman ratio `r(v) = ρ(v-1)/(v ρ(v))` (`= -ρ'(v)/ρ(v)` for `v > 1`). -/
noncomputable def ratio (v : ℝ) : ℝ := rho (v - 1) / (v * rho v)

/-- `I(v) = v ρ(v)/ρ(v-1) = 1/r(v)`. -/
noncomputable def invRatio (v : ℝ) : ℝ := v * rho v / rho (v - 1)

/-- `J(v) = r(v-1) v ρ(v) + ρ(v) - ρ(v-1)`. -/
noncomputable def Jfun (v : ℝ) : ℝ := ratio (v - 1) * (v * rho v) + rho v - rho (v - 1)

lemma ratio_pos {v : ℝ} (hv : 0 < v) : 0 < ratio v := by
  unfold ratio; have := rho_pos v; have := rho_pos (v - 1); positivity

lemma invRatio_pos {v : ℝ} (hv : 0 < v) : 0 < invRatio v := by
  unfold invRatio; have := rho_pos v; have := rho_pos (v - 1); positivity

lemma ratio_eq_inv {v : ℝ} : ratio v = 1 / invRatio v := by
  unfold ratio invRatio; rw [one_div_div]

lemma continuousAt_ratio {v : ℝ} (hv : 0 < v) : ContinuousAt ratio v := by
  unfold ratio
  apply ContinuousAt.div (continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt
    (continuous_id.mul continuous_rho).continuousAt
  exact (mul_pos hv (rho_pos v)).ne'

lemma continuousAt_invRatio (v : ℝ) : ContinuousAt invRatio v := by
  unfold invRatio
  exact ((continuous_id.mul continuous_rho).continuousAt).div
    (continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt (rho_pos _).ne'

lemma continuousAt_Jfun {v : ℝ} (hv : 1 < v) : ContinuousAt Jfun v := by
  unfold Jfun
  have h1 : ContinuousAt (fun v => ratio (v - 1)) v :=
    ContinuousAt.comp (g := ratio) (f := fun v : ℝ => v - 1)
      (continuousAt_ratio (by linarith : (0 : ℝ) < v - 1))
      (continuous_id.sub continuous_const).continuousAt
  exact ((h1.mul (continuous_id.mul continuous_rho).continuousAt).add
    continuous_rho.continuousAt).sub
    (continuous_rho.comp (continuous_id.sub continuous_const)).continuousAt

/-- `r(t) ρ(t) = ρ(t-1)/t`. -/
lemma ratio_mul_rho {t : ℝ} (ht : 0 < t) : ratio t * rho t = rho (t - 1) / t := by
  unfold ratio; have := (rho_pos t).ne'; field_simp

/-- The derivative of `I` for `v > 2`. -/
lemma hasDerivAt_invRatio {v : ℝ} (hv : 2 < v) :
    HasDerivAt invRatio (Jfun v / rho (v - 1)) v := by
  have h1 : HasDerivAt (fun v => v * rho v) (1 * rho v + v * (-(rho (v - 1) / v))) v :=
    (hasDerivAt_id v).mul (hasDerivAt_rho (by linarith))
  have h2 : HasDerivAt (fun v => rho (v - 1)) (-(rho (v - 1 - 1) / (v - 1)) * 1) v :=
    HasDerivAt.comp (h₂ := rho) (h := fun v : ℝ => v - 1) v
      (hasDerivAt_rho (by linarith)) ((hasDerivAt_id v).sub_const 1)
  have h := h1.div h2 (rho_pos _).ne'
  convert! h using 1
  unfold Jfun ratio
  have hv0 : v ≠ 0 := by linarith
  have hv1 : v - 1 ≠ 0 := by linarith
  have := (rho_pos (v - 1)).ne'
  have := (rho_pos v).ne'
  field_simp
  ring

/-- `J(v) = ∫_{v-1}^v ρ(t) (r(v-1) - r(t)) dt` for `v ≥ 2`. -/
lemma Jfun_eq_integral {v : ℝ} (hv : 2 ≤ v) :
    Jfun v = ∫ t in (v - 1)..v, rho t * (ratio (v - 1) - ratio t) := by
  have hcont : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b →
      IntervalIntegrable (fun t => rho (t - 1) / t) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuous_rho.comp (continuous_id.sub continuous_const)).continuousOn
      continuousOn_id
    intro t ht
    have : 1 ≤ t := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; linarith [ht.1]
      · rw [uIcc_of_ge h] at ht; linarith [ht.1]
    simp only [id]; linarith
  have hcongr : ∫ t in (v - 1)..v, rho t * (ratio (v - 1) - ratio t) =
      ∫ t in (v - 1)..v, (ratio (v - 1) * rho t - rho (t - 1) / t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    simp only
    rw [← ratio_mul_rho (by linarith [ht.1])]
    ring
  rw [hcongr, intervalIntegral.integral_sub ((continuous_rho.intervalIntegrable _ _).const_mul _)
    (hcont _ _ (by linarith) (by linarith)), intervalIntegral.integral_const_mul,
    ← mul_rho_eq_integral (by linarith)]
  have e1 := rho_eq (u := v) (by linarith)
  have e2 := rho_eq (u := v - 1) (by linarith)
  have e3 := intervalIntegral.integral_interval_sub_left (hcont 1 v le_rfl (by linarith))
    (hcont 1 (v - 1) le_rfl (by linarith))
  unfold Jfun
  linarith

lemma Jfun_neg {v : ℝ} (hv : 2 ≤ v) (hmono : StrictMonoOn ratio (Icc (v - 1) v)) :
    Jfun v < 0 := by
  rw [Jfun_eq_integral hv]
  have hint : IntervalIntegrable (fun t => rho t * (ratio t - ratio (v - 1))) volume (v - 1) v := by
    apply ContinuousOn.intervalIntegrable
    apply continuous_rho.continuousOn.mul (ContinuousOn.sub ?_ continuousOn_const)
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact (continuousAt_ratio (by linarith [ht.1])).continuousWithinAt
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun t ht => by
    have h1 : ratio (v - 1) < ratio t :=
      hmono ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    have := rho_pos t
    nlinarith) (by linarith : v - 1 < v)
  have e : (∫ t in (v - 1)..v, rho t * (ratio (v - 1) - ratio t)) =
      -∫ t in (v - 1)..v, rho t * (ratio t - ratio (v - 1)) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; ext t; ring
  rw [e]; linarith

/-- `r(v) = 1/(v(1 - log v))` on `[1, 2]`. -/
theorem ratio_one_two {v : ℝ} (h1 : 1 ≤ v) (h2 : v ≤ 2) :
    ratio v = 1 / (v * (1 - Real.log v)) := by
  unfold ratio
  rw [rho_of_le_one (by linarith), rho_one_two h1 h2]

lemma ratio_strictMonoOn_one_two : StrictMonoOn ratio (Icc 1 2) := by
  set g : ℝ → ℝ := fun v => v * (1 - Real.log v)
  have hg : StrictAntiOn g (Icc 1 2) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 2)
    · apply ContinuousOn.mul continuousOn_id (continuousOn_const.sub ?_)
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1])
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have hd : HasDerivAt g (1 * (1 - Real.log x) + x * (0 - x⁻¹)) x :=
        (hasDerivAt_id x).mul ((hasDerivAt_const x 1).sub (Real.hasDerivAt_log hx0))
      rw [hd.deriv]
      have := Real.log_pos hx.1
      field_simp
      linarith
  have hgpos : ∀ v ∈ Icc (1 : ℝ) 2, 0 < g v := by
    intro v hv
    have h1 : Real.log v ≤ Real.log 2 := Real.log_le_log (by linarith [hv.1]) hv.2
    have h2 := Real.log_two_lt_d9
    have : 0 < 1 - Real.log v := by linarith
    simp only [g]; nlinarith [hv.1]
  intro a ha b hb hab
  rw [ratio_one_two ha.1 ha.2, ratio_one_two hb.1 hb.2]
  exact one_div_lt_one_div_of_lt (hgpos b hb) (hg ha hb hab)

/-- **(R2)**: `r` is strictly increasing on `[1, ∞)`. -/
theorem ratio_strictMonoOn : StrictMonoOn ratio (Ici 1) := by
  set S : Set ℝ := {V | 2 ≤ V ∧ StrictMonoOn ratio (Icc 1 V)}
  have h2S : (2 : ℝ) ∈ S := ⟨le_rfl, ratio_strictMonoOn_one_two⟩
  have hunb : ∀ b, ∃ V ∈ S, b ≤ V := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨b, hb⟩ := hcon
    have hbdd : BddAbove S := ⟨b, fun V hV => (hb V hV).le⟩
    set V := sSup S with hVdef
    have hV2 : 2 ≤ V := le_csSup hbdd h2S
    have hIco : ∀ x y, 1 ≤ x → x < y → y < V → ratio x < ratio y := by
      intro x y hx hxy hyV
      obtain ⟨W, hW, hyW⟩ := exists_lt_of_lt_csSup ⟨2, h2S⟩ hyV
      exact hW.2 ⟨hx, by linarith⟩ ⟨by linarith, hyW.le⟩ hxy
    have hle : ∀ x, 1 ≤ x → x < V → ratio x ≤ ratio V := by
      intro x hx hxV
      have hc : Tendsto ratio (𝓝[<] V) (𝓝 (ratio V)) :=
        (continuousAt_ratio (by linarith)).continuousWithinAt.tendsto
      apply ge_of_tendsto hc
      filter_upwards [Ioo_mem_nhdsLT hxV] with y hy
      exact (hIco x y hx hy.1 hy.2).le
    have hIcc : StrictMonoOn ratio (Icc 1 V) := by
      intro x hx y hy hxy
      rcases lt_or_eq_of_le hy.2 with hyV | hyV
      · exact hIco x y hx.1 hxy hyV
      · have h1 := hIco x ((x + y) / 2) hx.1 (by linarith) (by linarith)
        have h2 := hle ((x + y) / 2) (by linarith [hx.1]) (by linarith)
        rw [hyV]; linarith
    have hJ : Jfun V < 0 := Jfun_neg hV2 (hIcc.mono (Icc_subset_Icc (by linarith) le_rfl))
    obtain ⟨δ, hδ, hJδ⟩ : ∃ δ > 0, ∀ v ∈ Icc V (V + δ), Jfun v < 0 := by
      have := (continuousAt_Jfun (by linarith : 1 < V)).eventually (gt_mem_nhds hJ)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp this
      refine ⟨ε / 2, by linarith, fun v hv => hball ?_⟩
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2]
    have hI : StrictAntiOn invRatio (Icc V (V + δ)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact fun v _ => (continuousAt_invRatio v).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_invRatio (by linarith [hx.1])).deriv]
        exact div_neg_of_neg_of_pos (hJδ x ⟨hx.1.le, hx.2.le⟩) (rho_pos _)
    have hR : StrictMonoOn ratio (Icc V (V + δ)) := by
      intro x hx y hy hxy
      rw [ratio_eq_inv, ratio_eq_inv]
      exact one_div_lt_one_div_of_lt (invRatio_pos (by linarith [hy.1])) (hI hx hy hxy)
    have hS' : V + δ ∈ S := by
      refine ⟨by linarith, ?_⟩
      intro x hx y hy hxy
      rcases le_total y V with hyV | hyV
      · exact hIcc ⟨hx.1, by linarith⟩ ⟨hy.1, hyV⟩ hxy
      rcases le_total V x with hVx | hVx
      · exact hR ⟨hVx, hx.2⟩ ⟨hyV, hy.2⟩ hxy
      rcases eq_or_lt_of_le hVx with h | h
      · rw [h]; exact hR ⟨le_rfl, by linarith⟩ ⟨hyV, hy.2⟩ (by rw [← h]; exact hxy)
      · have h1 := hIcc ⟨hx.1, hVx⟩ ⟨by linarith, le_rfl⟩ h
        rcases eq_or_lt_of_le hyV with h' | h'
        · rw [← h']; exact h1
        · have h2 := hR ⟨le_rfl, by linarith⟩ ⟨hyV, hy.2⟩ h'
          linarith
    have := le_csSup hbdd hS'
    linarith
  intro x hx y hy hxy
  obtain ⟨V, hV, hyV⟩ := hunb y
  exact hV.2 ⟨hx, by linarith⟩ ⟨by linarith [mem_Ici.mp hy], hyV⟩ hxy

theorem ratio_monotoneOn : MonotoneOn ratio (Ici 1) := ratio_strictMonoOn.monotoneOn

/-- Decay: for `1 ≤ w ≤ t`, `ρ(t) ≤ ρ(w) e^{-r(w)(t-w)}`. -/
theorem rho_le_exp {w t : ℝ} (hw : 1 ≤ w) (hwt : w ≤ t) :
    rho t ≤ rho w * Real.exp (-(ratio w * (t - w))) := by
  set g : ℝ → ℝ := fun s => Real.log (rho s) + ratio w * s
  have hg : AntitoneOn g (Icc w t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc w t)
    · apply Continuous.continuousOn
      exact (continuous_rho.log fun s => (rho_pos s).ne').add (continuous_const.mul continuous_id)
    · intro x hx
      rw [interior_Icc] at hx
      exact (((hasDerivAt_rho (by linarith [hx.1])).log (rho_pos x).ne').add
        ((hasDerivAt_id x).const_mul (ratio w))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt g (-(rho (x - 1) / x) / rho x + ratio w * 1) x :=
        ((hasDerivAt_rho (by linarith [hx.1])).log (rho_pos x).ne').add
          ((hasDerivAt_id x).const_mul (ratio w))
      rw [hd.deriv]
      have hr : ratio w ≤ ratio x :=
        ratio_monotoneOn (mem_Ici.mpr hw) (mem_Ici.mpr (by linarith [hx.1])) hx.1.le
      have e : -(rho (x - 1) / x) / rho x = -ratio x := by
        unfold ratio; rw [neg_div, div_div]
      rw [e]; simp only [mul_one]; linarith
  have h := hg ⟨le_rfl, hwt⟩ ⟨hwt, le_rfl⟩ hwt
  simp only [g] at h
  have hlog : Real.log (rho t) ≤ Real.log (rho w) + -(ratio w * (t - w)) := by linarith
  calc rho t = Real.exp (Real.log (rho t)) := (Real.exp_log (rho_pos t)).symm
    _ ≤ Real.exp (Real.log (rho w) + -(ratio w * (t - w))) := Real.exp_le_exp.mpr hlog
    _ = rho w * Real.exp (-(ratio w * (t - w))) := by
      rw [Real.exp_add, Real.exp_log (rho_pos w)]

/-- **(R3)**: `r(v) ≥ r(v-1)/(1 - e^{-r(v-1)})` for `v ≥ 2`. -/
theorem ratio_recursion {v : ℝ} (hv : 2 ≤ v) :
    ratio (v - 1) / (1 - Real.exp (-ratio (v - 1))) ≤ ratio v := by
  set a := ratio (v - 1) with ha
  have ha0 : 0 < a := ratio_pos (by linarith)
  have hE : 0 < 1 - Real.exp (-a) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha0); linarith
  have hcont : Continuous (fun t => rho (v - 1) * Real.exp (-(a * (t - (v - 1))))) := by
    fun_prop
  have hmono : ∫ t in (v - 1)..v, rho t ≤
      ∫ t in (v - 1)..v, rho (v - 1) * Real.exp (-(a * (t - (v - 1)))) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (continuous_rho.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    intro t ht
    exact rho_le_exp (by linarith) ht.1
  have hcalc : ∫ t in (v - 1)..v, rho (v - 1) * Real.exp (-(a * (t - (v - 1)))) =
      rho (v - 1) * ((1 - Real.exp (-a)) / a) := by
    have hF : ∀ t ∈ uIcc (v - 1) v, HasDerivAt
        (fun t => -(rho (v - 1) * Real.exp (-(a * (t - (v - 1))))) / a)
        (rho (v - 1) * Real.exp (-(a * (t - (v - 1))))) t := by
      intro t _
      have h1 : HasDerivAt (fun t => -(a * (t - (v - 1)))) (-(a * 1)) t :=
        (((hasDerivAt_id t).sub_const (v - 1)).const_mul a).neg
      have h2 := ((h1.exp).const_mul (rho (v - 1))).neg.div_const a
      convert! h2 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]
    have e : -(a * (v - (v - 1))) = -a := by ring
    simp only [e, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    field_simp
    ring
  rw [← mul_rho_eq_integral (by linarith)] at hmono
  rw [hcalc] at hmono
  have hv0 : 0 < v := by linarith
  have hr := rho_pos v
  have hr1 := rho_pos (v - 1)
  show a / (1 - Real.exp (-a)) ≤ rho (v - 1) / (v * rho v)
  rw [div_le_div_iff₀ hE (by positivity)]
  have : v * rho v * a ≤ rho (v - 1) * (1 - Real.exp (-a)) := by
    have h := mul_le_mul_of_nonneg_right hmono ha0.le
    have e : rho (v - 1) * ((1 - Real.exp (-a)) / a) * a = rho (v - 1) * (1 - Real.exp (-a)) := by
      field_simp
    linarith
  linarith

/-- **(R4)**: `r(x) ≤ log((x+1)/δ)/(1-δ)` for `x ≥ 1`, `0 < δ < 1`. -/
theorem ratio_upper {x δ : ℝ} (hx : 1 ≤ x) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ratio x ≤ Real.log ((x + 1) / δ) / (1 - δ) := by
  set v := x + 1 - δ with hv
  have hv1 : 1 ≤ v := by linarith
  have hint : δ * rho x ≤ v * rho v := by
    rw [mul_rho_eq_integral hv1,
      ← intervalIntegral.integral_add_adjacent_intervals (b := x)
        (continuous_rho.intervalIntegrable _ _) (continuous_rho.intervalIntegrable _ _)]
    have h1 : ∫ t in (v - 1)..x, rho x ≤ ∫ t in (v - 1)..x, rho t :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (continuous_rho.intervalIntegrable _ _) (fun t ht => rho_antitone ht.2)
    have h2 : 0 ≤ ∫ t in x..v, rho t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => (rho_pos t).le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have e : x - (v - 1) = δ := by rw [hv]; ring
    rw [e] at h1
    linarith
  have hdec := rho_le_exp hx (by linarith : x ≤ v)
  have e : v - x = 1 - δ := by rw [hv]; ring
  rw [e] at hdec
  set c := ratio x * (1 - δ)
  have hrx := rho_pos x
  have hv0 : 0 < v := by linarith
  have h3 : δ ≤ v * Real.exp (-c) := by
    have := mul_le_mul_of_nonneg_left hdec hv0.le
    have h4 : δ * rho x ≤ v * Real.exp (-c) * rho x := by nlinarith
    exact le_of_mul_le_mul_right h4 hrx
  have h5 : Real.exp c * δ ≤ v := by
    have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos c).le
    rwa [← mul_assoc, mul_comm (Real.exp c) v, mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one] at this
  have h6 : c ≤ Real.log ((x + 1) / δ) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hδ0]
    linarith
  rw [le_div_iff₀ (by linarith)]
  exact h6

end Dickman
