module

public import RequestProject.Beurling.Noise.BSLargeRatio
public import RequestProject.Beurling.Noise.BSLargeShift
meta import RequestProject.BSCert.AuxCert

/-!
# Lemma 5.7: the slack `s_a` (`lemma57Slack`; 04c-saias.tex, lines 336-337 and 424-433)

* `u ≥ u₀ - 2`: `s_a ≥ 0.67 a'(ℓ,u) - 0.54/√ℓ`. From (P2) (`aQ_mOf_le`) and the convexity of
  `φ(x) = (x - u₀)₊²/(2√ℓ)`, `a(m,w) - a(ℓ,u) ≤ a' s + s²/(2√ℓ) + 0.2502 (a' + s₊/√ℓ) +
  0.0314/√ℓ` (`s = w - u`); integrating against `π` with `E_π(u-w)₊ = 1 - 1/r(u)` (R1),
  `r(u) ≥ 12.82` and the moment bound for `w ≥ u` gives the claim.
* `u < u₀ - 2`: `a(ℓ,u) = 0` and `a(m,w) ≥ 0`, so `s_a ≤ 0`; `a(m,w) = 0` for
  `w ≤ u₀ - 0.26`, and beyond the decay of `ρ` gives `ℓ|s_a| ≤ 0.01` (with `r(x) ≥ log x` for
  `u ≥ u₀/2`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace BSaias.Large

/-- `∫_b^∞ (c₀ + c₁ t + c₂ t²) e^{-rt} dw = c₀/r + c₁/r² + 2c₂/r³`, `t = w - b`. -/
lemma integral_Ioi_quad {r b c0 c1 c2 : ℝ} (hr : 0 < r) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1)
    (h2 : 0 ≤ c2) :
    IntegrableOn (fun w => (c0 + c1 * (w - b) + c2 * (w - b) ^ 2) * Real.exp (-(r * (w - b))))
      (Ioi b) ∧
    ∫ w in Ioi b, (c0 + c1 * (w - b) + c2 * (w - b) ^ 2) * Real.exp (-(r * (w - b))) =
      c0 / r + c1 / r ^ 2 + 2 * c2 / r ^ 3 := by
  set a0 := c0 / r + c1 / r ^ 2 + 2 * c2 / r ^ 3 with ha0
  set a1 := c1 / r + 2 * c2 / r ^ 2 with ha1
  set a2 := c2 / r with ha2
  set P : ℝ → ℝ := fun s => a0 + a1 * s + a2 * s ^ 2 with hP
  have hPd : ∀ s, HasDerivAt P (a1 + a2 * (2 * s)) s := by
    intro s
    have hs := hasDerivAt_id s
    have := (((hasDerivAt_const s a0).add (hs.const_mul a1)).add ((hs.pow 2).const_mul a2))
    convert this using 1
    simp only [id]; push_cast; ring
  have hderiv : ∀ x ∈ Ici b, HasDerivAt (fun w => -(Real.exp (-(r * (w - b))) * P (w - b)))
      ((c0 + c1 * (x - b) + c2 * (x - b) ^ 2) * Real.exp (-(r * (x - b)))) x := by
    intro x _
    have he := (((hasDerivAt_id x).sub_const b).const_mul r).neg.exp
    have hp := (hPd (x - b)).comp x ((hasDerivAt_id x).sub_const b)
    have h := (he.mul hp).neg
    convert h using 1
    simp only [hP, id, Function.comp_apply, Pi.neg_apply, Pi.mul_apply, ha0, ha1, ha2]
    field_simp
    ring
  have hpos : ∀ x ∈ Ioi b, 0 ≤ (c0 + c1 * (x - b) + c2 * (x - b) ^ 2) *
      Real.exp (-(r * (x - b))) := by
    intro x hx
    have : 0 ≤ x - b := by linarith [mem_Ioi.mp hx]
    positivity
  have hlim : Tendsto (fun w => -(Real.exp (-(r * (w - b))) * P (w - b))) atTop (𝓝 0) := by
    have t := fun k => tendsto_pow_mul_exp_shift k hr (u := b)
    have hsum := ((((t 0).const_mul a0).add ((t 1).const_mul a1)).add ((t 2).const_mul a2)).neg
    simp only [mul_zero, add_zero, neg_zero] at hsum
    refine hsum.congr fun w => ?_
    simp only [hP]
    ring
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [hP, sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- `(a + t)₊² ≤ (a₊ + t)²` (convexity of `x ↦ x₊²`). -/
lemma sq_pos_add_le (a t : ℝ) : (max (a + t) 0) ^ 2 ≤ (max a 0 + t) ^ 2 := by
  rcases le_total (a + t) 0 with h | h
  · rw [max_eq_right h]
    calc (0 : ℝ) ^ 2 = 0 := by norm_num
      _ ≤ _ := sq_nonneg _
  · rw [max_eq_left h]
    have := le_max_left a 0
    apply pow_le_pow_left₀ h (by linarith)

lemma aQ_nonneg (m w : ℝ) : 0 ≤ aQ m w := by unfold aQ; positivity

lemma continuousOn_aQ_mOf {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    ContinuousOn (fun w => aQ (mOf ℓ w) w) (Ici a) := by
  intro w hw
  have hw0 : 0 < w := lt_of_lt_of_le ha hw
  apply ContinuousAt.continuousWithinAt
  have hm : ContinuousAt (fun w => mOf ℓ w) w := by
    unfold mOf
    exact (continuousAt_const.mul continuousAt_id).div (continuousAt_const.add continuousAt_id)
      (by linarith)
  have hmpos : 0 < mOf ℓ w := by unfold mOf; positivity
  unfold aQ u0 BSCert.Z2.u0
  apply ContinuousAt.div
  · exact ((continuousAt_id.sub (Real.continuous_sqrt.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.comp hm))).max continuousAt_const).pow 2
  · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hm)
  · have : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hmpos
    positivity

/-- `0 ≤ a(m, w) ≤ w²` for `w ≥ 0`, `ℓ ≥ 2`. -/
lemma aQ_mOf_le_sq {ℓ w : ℝ} (hℓ : 2 ≤ ℓ) (hw : 1 ≤ w) : aQ (mOf ℓ w) w ≤ w ^ 2 := by
  have hm1 : 1 ≤ mOf ℓ w := by
    unfold mOf; rw [le_div_iff₀ (by linarith)]; nlinarith
  have hs : 1 ≤ √(mOf ℓ w) := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  unfold aQ
  have hd : max (w - u0 (mOf ℓ w)) 0 ≤ w :=
    max_le (by have : 0 ≤ u0 (mOf ℓ w) := Real.sqrt_nonneg _; linarith) (by linarith)
  have hd0 : 0 ≤ max (w - u0 (mOf ℓ w)) 0 := le_max_right _ _
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_le_pow_left₀ hd0 hd 2]

lemma integrableOn_aQ {ℓ u : ℝ} (hℓ : 2 ≤ ℓ) (hu : 2 ≤ u) (c : ℝ) :
    IntegrableOn (fun w => (aQ (mOf ℓ w) w - c) * Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
  apply integrableOn_mul_rho (C := 1 + |c|) hu
  · exact (continuousOn_aQ_mOf (by linarith) (by linarith)).sub continuousOn_const
  · intro w hw
    have hw1 : 1 ≤ w := by linarith
    have h1 := aQ_mOf_le_sq hℓ hw1
    have h0 := aQ_nonneg (mOf ℓ w) w
    have hp : w ^ 2 ≤ (1 + w) ^ 5 := by
      have : w ^ 2 ≤ (1 + w) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      exact this.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
    have hp1 : 1 ≤ (1 + w) ^ 5 := one_le_pow₀ (by linarith)
    have hc := abs_nonneg c
    have hc5 : |c| ≤ |c| * (1 + w) ^ 5 := le_mul_of_one_le_right hc hp1
    have e : (1 + |c|) * (1 + w) ^ 5 = (1 + w) ^ 5 + |c| * (1 + w) ^ 5 := by ring
    rw [abs_le, e]
    constructor
    · linarith [le_abs_self c]
    · linarith [neg_abs_le c]

/-- `∫_{(u-1, ∞)} = ∫_{(u-1, b]} + ∫_{(b, ∞)}` for `b ≥ u - 1`. -/
lemma integral_Ioi_split' {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi a)) :
    ∫ w in Ioi a, f w = (∫ w in Ioc a b, f w) + ∫ w in Ioi b, f w := by
  rw [← Ioc_union_Ioi_eq_Ioi hab] at hf ⊢
  exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
    exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi
    (hf.mono_set subset_union_left) (hf.mono_set subset_union_right)

/-! ## `u ≥ u₀ - 2` -/

set_option maxHeartbeats 1000000 in
lemma slack_big {ℓ u : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) (hu : u0 ℓ - 2 ≤ u) :
    0.67 * aprime ℓ u - 0.54 / √ℓ ≤ sA ℓ u := by
  have hu0 := u0_ge_of hℓ
  have hu2 : 2 ≤ u := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hsℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  have hρ1 := Dickman.rho_pos (u - 1)
  have hρu := Dickman.rho_pos u
  have hupos : 0 < u := by linarith
  set ap := aprime ℓ u with hap
  set v := u - u0 ℓ with hv
  have hap0 : 0 ≤ ap := by rw [hap]; unfold aprime; positivity
  have hapv : ap = max v 0 / √ℓ := rfl
  set K1 := 0.2502 * ap + 0.0314 / √ℓ with hK1
  set r := Dickman.ratio u with hrdef
  set r0 := Dickman.ratio (u - 1) with hr0def
  have hr : 12.82 ≤ r := ratio_ge_12_82 (by linarith)
  have hr0 : 2 ≤ r0 := ratio_ge_two (by linarith)
  set M := momM r0 with hMdef
  have hM : M ≤ 4.5 := by
    have := momM_le (r := r0) (by linarith)
    have : 144 / r0 ^ 2 ≤ 36 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hM0 : 0 ≤ M := by
    simp only [M]; unfold momM; have : 0 < r0 := by linarith
    positivity
  -- the pointwise bound
  have hpt : ∀ w, u - 1 < w → aQ (mOf ℓ w) w - aQ ℓ u ≤
      ap * (w - u) + (w - u) ^ 2 / (2 * √ℓ) + 0.2502 * max (w - u) 0 / √ℓ + K1 := by
    intro w hw
    have h := aQ_mOf_le hℓ (w := w) (by linarith)
    have e1 : w - u0 ℓ = v + (w - u) := by rw [hv]; ring
    have hA2 : (max (w - u0 ℓ) 0) ^ 2 ≤ (max v 0 + (w - u)) ^ 2 := by
      rw [e1]; exact sq_pos_add_le v (w - u)
    have hA1 : max (w - u0 ℓ) 0 ≤ max v 0 + max (w - u) 0 := by
      rw [e1]
      apply max_le _ (by positivity)
      linarith [le_max_left v 0, le_max_left (w - u) 0]
    have haQ : aQ ℓ u = (max v 0) ^ 2 / (2 * √ℓ) := rfl
    have hex : (max v 0 + (w - u)) ^ 2 / (2 * √ℓ) =
        (max v 0) ^ 2 / (2 * √ℓ) + ap * (w - u) + (w - u) ^ 2 / (2 * √ℓ) := by
      rw [hapv]; field_simp; ring
    have t1 : (max (w - u0 ℓ) 0) ^ 2 / (2 * √ℓ) ≤ (max v 0 + (w - u)) ^ 2 / (2 * √ℓ) :=
      div_le_div_of_nonneg_right hA2 (by positivity)
    have t2 : 0.2502 * max (w - u0 ℓ) 0 / √ℓ ≤ 0.2502 * ap + 0.2502 * max (w - u) 0 / √ℓ := by
      rw [hapv]
      have := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA1 (by norm_num : (0:ℝ) ≤ 0.2502)) hsℓ.le
      rw [mul_add, add_div] at this
      linarith [show 0.2502 * (max v 0 / √ℓ) = 0.2502 * max v 0 / √ℓ by ring]
    rw [haQ]
    linarith
  clear_value K1 M r0 r ap v
  -- integrability
  have hint := integrableOn_aQ (ℓ := ℓ) (by linarith) hu2 (aQ ℓ u)
  set F := fun w => (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w
  have hd0 : ∀ w, u - 1 < w → 0 ≤ Dickman.rho (w - 1) / w := fun w hw =>
    div_nonneg (Dickman.rho_pos _).le (by linarith)
  -- Part I: `(u-1, u]`
  have hIoc_int : IntegrableOn (fun w => (K1 + 1 / (2 * √ℓ)) * (Dickman.rho (w - 1) / w) -
      ap * (Dickman.rho (w - 1) * (u - w) / w)) (Ioc (u - 1) u) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    apply ContinuousOn.sub
    · exact continuousOn_const.mul ((continuousOn_rho_div (a := u - 1) (by linarith)).mono
        Icc_subset_Ici_self)
    · refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul (Dickman.continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn (by fun_prop)) continuousOn_id ?_)
      intro x hx; exact (by linarith [hx.1] : (0:ℝ) < x).ne'
  have hI : ∫ w in Ioc (u - 1) u, F w ≤ (K1 + 1 / (2 * √ℓ)) * (Dickman.rho (u - 1) - Dickman.rho u)
      - ap * (Dickman.rho (u - 1) - u * Dickman.rho u) := by
    calc ∫ w in Ioc (u - 1) u, F w ≤ ∫ w in Ioc (u - 1) u, ((K1 + 1 / (2 * √ℓ)) *
          (Dickman.rho (w - 1) / w) - ap * (Dickman.rho (w - 1) * (u - w) / w)) := by
          apply setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) hIoc_int measurableSet_Ioc
          intro w hw
          have hw0 : 0 < w := by linarith [hw.1]
          have hb := hpt w hw.1
          have hs : max (w - u) 0 = 0 := max_eq_right (by linarith [hw.2])
          have hsq : (w - u) ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
          rw [hs, mul_zero, zero_div, add_zero] at hb
          have hb' : aQ (mOf ℓ w) w - aQ ℓ u ≤ (K1 + 1 / (2 * √ℓ)) - ap * (u - w) := by
            have : (w - u) ^ 2 / (2 * √ℓ) ≤ 1 / (2 * √ℓ) :=
              div_le_div_of_nonneg_right hsq (by positivity)
            linarith
          have := mul_le_mul_of_nonneg_right hb' (hd0 w hw.1)
          simp only [F]
          calc (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w
              = (aQ (mOf ℓ w) w - aQ ℓ u) * (Dickman.rho (w - 1) / w) := by ring
            _ ≤ ((K1 + 1 / (2 * √ℓ)) - ap * (u - w)) * (Dickman.rho (w - 1) / w) := this
            _ = _ := by ring
      _ = _ := by
          rw [integral_sub (((continuousOn_rho_div (a := u - 1) (by linarith)).mono
              Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self |>.const_mul _)
            ?_, integral_const_mul, integral_const_mul,
            ← intervalIntegral.integral_of_le (by linarith),
            ← intervalIntegral.integral_of_le (by linarith),
            Dickman.integral_shift_div (by linarith) (by linarith),
            Dickman.integral_shift_mul_div hu2]
          refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
          refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul
            (Dickman.continuous_rho.comp (continuous_id.sub continuous_const)).continuousOn
            (by fun_prop)) continuousOn_id ?_)
          intro x hx; exact (by linarith [hx.1] : (0:ℝ) < x).ne'
  -- Part II: `(u, ∞)`
  obtain ⟨hI1, hE1⟩ := integral_Ioi_shift_div (a := u) (by linarith)
  obtain ⟨hMi, hMv⟩ := integral_Ioi_moment (r := r0) (u := u) (by linarith)
  set B := ap + 0.7502 / √ℓ with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hII : ∫ w in Ioi u, F w ≤ K1 * Dickman.rho u + B * Dickman.rho (u - 1) / u * M := by
    calc ∫ w in Ioi u, F w ≤ ∫ w in Ioi u, (K1 * (Dickman.rho (w - 1) / w) +
          B * Dickman.rho (u - 1) / u *
            ((w - u) * (1 + (w - u)) ^ 3 * Real.exp (-(r0 * (w - u))))) := by
          apply setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi (by linarith)))
            ((hI1.const_mul K1).add (hMi.const_mul _)) measurableSet_Ioi
          intro w hw
          have huw : u < w := hw
          have hb := hpt w (by linarith)
          have hs0 : 0 ≤ w - u := by linarith
          have hs : max (w - u) 0 = w - u := max_eq_left hs0
          rw [hs] at hb
          have hq : 1 ≤ (1 + (w - u)) ^ 3 := one_le_pow₀ (by linarith)
          have hq3 : w - u ≤ (1 + (w - u)) ^ 3 :=
            le_trans (by linarith)
              (le_self_pow₀ (by linarith : (1 : ℝ) ≤ 1 + (w - u)) (by norm_num))
          have hq2 : (w - u) ^ 2 ≤ (w - u) * (1 + (w - u)) ^ 3 := by
            rw [sq]; exact mul_le_mul_of_nonneg_left hq3 hs0
          have hq1 : w - u ≤ (w - u) * (1 + (w - u)) ^ 3 := by
            have := mul_le_mul_of_nonneg_left hq hs0
            linarith
          have hb' : aQ (mOf ℓ w) w - aQ ℓ u ≤ K1 + B * ((w - u) * (1 + (w - u)) ^ 3) := by
            have e1 : ap * (w - u) ≤ ap * ((w - u) * (1 + (w - u)) ^ 3) :=
              mul_le_mul_of_nonneg_left hq1 hap0
            have e2 : (w - u) ^ 2 / (2 * √ℓ) ≤ 0.5 / √ℓ * ((w - u) * (1 + (w - u)) ^ 3) := by
              calc (w - u) ^ 2 / (2 * √ℓ) ≤ ((w - u) * (1 + (w - u)) ^ 3) / (2 * √ℓ) :=
                    div_le_div_of_nonneg_right hq2 (by positivity)
                _ = 0.5 / √ℓ * ((w - u) * (1 + (w - u)) ^ 3) := by field_simp; ring
            have e3 : 0.2502 * (w - u) / √ℓ ≤ 0.2502 / √ℓ * ((w - u) * (1 + (w - u)) ^ 3) := by
              rw [div_mul_eq_mul_div]
              exact div_le_div_of_nonneg_right
                (by linarith [mul_le_mul_of_nonneg_left hq1 (by norm_num : (0:ℝ) ≤ 0.2502)]) hsℓ.le
            have e4 : B = ap + 0.5 / √ℓ + 0.2502 / √ℓ := by
              simp only [B]; ring
            rw [e4]
            have e5 : (ap + 0.5 / √ℓ + 0.2502 / √ℓ) * ((w - u) * (1 + (w - u)) ^ 3) =
                ap * ((w - u) * (1 + (w - u)) ^ 3) + 0.5 / √ℓ * ((w - u) * (1 + (w - u)) ^ 3)
                + 0.2502 / √ℓ * ((w - u) * (1 + (w - u)) ^ 3) := by ring
            rw [e5]
            linarith
          have htail := rho_tail hu2 huw.le
          rw [← hr0def] at htail
          have hq0 : 0 ≤ (w - u) * (1 + (w - u)) ^ 3 := by positivity
          simp only [F]
          calc (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w
              = (aQ (mOf ℓ w) w - aQ ℓ u) * (Dickman.rho (w - 1) / w) := by ring
            _ ≤ (K1 + B * ((w - u) * (1 + (w - u)) ^ 3)) * (Dickman.rho (w - 1) / w) :=
                mul_le_mul_of_nonneg_right hb' (hd0 w (by linarith))
            _ = K1 * (Dickman.rho (w - 1) / w) + B * ((w - u) * (1 + (w - u)) ^ 3) *
                (Dickman.rho (w - 1) / w) := by ring
            _ ≤ K1 * (Dickman.rho (w - 1) / w) + B * ((w - u) * (1 + (w - u)) ^ 3) *
                (Dickman.rho (u - 1) * Real.exp (-(r0 * (w - u))) / u) := by
                gcongr
            _ = _ := by simp only [Pi.add_apply]; ring
      _ = K1 * Dickman.rho u + B * Dickman.rho (u - 1) / u * M := by
          rw [integral_add (hI1.const_mul K1) (hMi.const_mul _), integral_const_mul,
            integral_const_mul, hE1, hMv, hMdef]
          rfl
  have hmass := rho_div_rho hu2
  rw [← hrdef] at hmass
  have hsplit := integral_Ioi_split hint
  have hsum : ∫ w in Ioi (u - 1), F w ≤ Dickman.rho (u - 1) *
      (K1 + 1 / (2 * √ℓ) - ap * (1 - 1 / r) + B * M / u) := by
    rw [hsplit]
    have hk : ap * (Dickman.rho (u - 1) - u * Dickman.rho u) =
        ap * (1 - 1 / r) * Dickman.rho (u - 1) := by
      rw [← hmass]; field_simp
    have hρneg : 0 ≤ Dickman.rho u / (2 * √ℓ) := by positivity
    have : (K1 + 1 / (2 * √ℓ)) * (Dickman.rho (u - 1) - Dickman.rho u) + K1 * Dickman.rho u
        ≤ Dickman.rho (u - 1) * (K1 + 1 / (2 * √ℓ)) := by
      have : (K1 + 1 / (2 * √ℓ)) * (Dickman.rho (u - 1) - Dickman.rho u) + K1 * Dickman.rho u
          = Dickman.rho (u - 1) * (K1 + 1 / (2 * √ℓ)) - Dickman.rho u / (2 * √ℓ) := by ring
      linarith
    have e : B * Dickman.rho (u - 1) / u * M = Dickman.rho (u - 1) * (B * M / u) := by ring
    have e2 : Dickman.rho (u - 1) * (K1 + 1 / (2 * √ℓ) - ap * (1 - 1 / r) + B * M / u) =
        Dickman.rho (u - 1) * (K1 + 1 / (2 * √ℓ)) - ap * (1 - 1 / r) * Dickman.rho (u - 1)
          + Dickman.rho (u - 1) * (B * M / u) := by ring
    rw [e2]
    linarith only [hI, hII, this, hk, e]
  -- conclude
  have hsA : sA ℓ u = -((∫ w in Ioi (u - 1), F w) / Dickman.rho (u - 1)) := rfl
  have hE : (∫ w in Ioi (u - 1), F w) / Dickman.rho (u - 1) ≤
      K1 + 1 / (2 * √ℓ) - ap * (1 - 1 / r) + B * M / u := by
    rw [div_le_iff₀ hρ1]; linarith
  have h1r : 0.92199 ≤ 1 - 1 / r := by
    have : 1 / r ≤ 1 / 12.82 := one_div_le_one_div_of_le (by norm_num) hr
    have : (1 : ℝ) / 12.82 ≤ 0.07801 := by norm_num
    linarith
  have hMu : M / u ≤ 0.000143 := by
    rw [div_le_iff₀ hupos]; linarith
  have hBMu : B * M / u = B * (M / u) := by ring
  have hBM : B * (M / u) ≤ 0.000143 * ap + 0.000143 * (0.7502 / √ℓ) := by
    have := mul_le_mul_of_nonneg_left hMu hB0
    rw [show B * 0.000143 = 0.000143 * ap + 0.000143 * (0.7502 / √ℓ) by rw [hBdef]; ring] at this
    exact this
  have hapr : 0.92199 * ap ≤ ap * (1 - 1 / r) := by
    have := mul_le_mul_of_nonneg_left h1r hap0
    linarith
  rw [hsA]
  have hinv : 0 < 1 / √ℓ := by positivity
  have e1 : 0.0314 / √ℓ = 0.0314 * (1 / √ℓ) := by ring
  have e2 : 1 / (2 * √ℓ) = 0.5 * (1 / √ℓ) := by field_simp; norm_num
  have e3 : 0.7502 / √ℓ = 0.7502 * (1 / √ℓ) := by ring
  have e4 : 0.54 / √ℓ = 0.54 * (1 / √ℓ) := by ring
  rw [hK1] at hE
  rw [e1, e2, hBMu] at hE
  rw [e3] at hBM
  rw [e4]
  linarith

/-! ## `u < u₀ - 2` -/

lemma rLow_15810 : (9 : ℚ) ≤ BSCert.rLow BSCert.auxTable 15810 := by native_decide

lemma ratio_ge_nine {v : ℝ} (hv : 15810 ≤ v) : 9 ≤ Dickman.ratio v := by
  have h := ratio_ge_table (x := 15810) (by norm_num) (by exact_mod_cast hv)
  have h2 : ((9 : ℚ) : ℝ) ≤ ((BSCert.rLow BSCert.auxTable 15810 : ℚ) : ℝ) := by
    exact_mod_cast rLow_15810
  push_cast at h2; linarith

set_option maxHeartbeats 1000000 in
lemma slack_small {ℓ u : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) (hu2 : 2 ≤ u)
    (hu : u < u0 ℓ - 2) : -0.01 ≤ ℓ * sA ℓ u ∧ ℓ * sA ℓ u ≤ 0 := by
  have hu0 := u0_ge_of hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hsℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  have hρ1 := Dickman.rho_pos (u - 1)
  have hupos : 0 < u := by linarith
  have haQ : aQ ℓ u = 0 := aQ_eq_zero (by linarith)
  set r0 := Dickman.ratio (u - 1) with hr0def
  have hr0 : 1 ≤ r0 := ratio_ge_one (by linarith)
  set b := u0 ℓ - 0.26 with hb
  set d := b - u with hd
  have hd1 : 1.74 ≤ d := by rw [hd, hb]; linarith
  set F := fun w => (aQ (mOf ℓ w) w - aQ ℓ u) * Dickman.rho (w - 1) / w with hF
  have hint : IntegrableOn F (Ioi (u - 1)) := integrableOn_aQ (ℓ := ℓ) (by linarith) hu2 _
  have hFnn : ∀ w ∈ Ioi (u - 1), 0 ≤ F w := by
    intro w hw
    have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
    simp only [hF, haQ, sub_zero]
    exact div_nonneg (mul_nonneg (aQ_nonneg _ _) (Dickman.rho_pos _).le) hw0.le
  have hsA : sA ℓ u = -((∫ w in Ioi (u - 1), F w) / Dickman.rho (u - 1)) := rfl
  have hI0 : 0 ≤ ∫ w in Ioi (u - 1), F w := setIntegral_nonneg measurableSet_Ioi hFnn
  -- the bound on the integral
  set Q := 0.0314 / r0 + 0.2502 / r0 ^ 2 + 2 * 0.5 / r0 ^ 3 with hQ
  obtain ⟨hqi, hqv⟩ := integral_Ioi_quad (r := r0) (b := b) (c0 := 0.0314) (c1 := 0.2502)
    (c2 := 0.5) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  set K := Dickman.rho (u - 1) * Real.exp (-(r0 * d)) / (u * √ℓ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hbig : ∫ w in Ioi (u - 1), F w ≤ K * Q := by
    rw [integral_Ioi_split' (show u - 1 ≤ b by rw [hb]; linarith) hint]
    have hzero : ∫ w in Ioc (u - 1) b, F w = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro w hw
      have hw1 : 1 ≤ w := by linarith [hw.1]
      have h0 : aQ (mOf ℓ w) w = 0 := by
        rcases le_or_gt w (u0 ℓ - 3) with h3 | h3
        · exact aQ_mOf_eq_zero_low hℓ0 hw1 h3
        · exact aQ_mOf_eq_zero_mid hℓ h3.le (by rw [hb] at hw; exact hw.2)
      simp only [hF, h0, haQ, sub_zero, zero_mul, zero_div]
    rw [hzero, zero_add]
    calc ∫ w in Ioi b, F w ≤ ∫ w in Ioi b, K * ((0.0314 + 0.2502 * (w - b) + 0.5 * (w - b) ^ 2) *
          Real.exp (-(r0 * (w - b)))) := by
          apply setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi (by rw [hb]; linarith)))
            (hqi.const_mul K) measurableSet_Ioi
          intro w hw
          have hwb : b < w := hw
          have hwu : u ≤ w := by linarith
          have hw0 : 0 < w := by linarith
          have h1 := aQ_mOf_le hℓ (w := w) (by rw [hb] at hwb; linarith)
          have hA : max (w - u0 ℓ) 0 ≤ w - b := max_le (by rw [hb]; linarith) (by linarith)
          have hA0 : 0 ≤ max (w - u0 ℓ) 0 := le_max_right _ _
          have hq : aQ (mOf ℓ w) w ≤ (0.0314 + 0.2502 * (w - b) + 0.5 * (w - b) ^ 2) / √ℓ := by
            have t1 : (max (w - u0 ℓ) 0) ^ 2 / (2 * √ℓ) ≤ 0.5 * (w - b) ^ 2 / √ℓ := by
              rw [div_le_div_iff₀ (by positivity) hsℓ]
              nlinarith [pow_le_pow_left₀ hA0 hA 2]
            have t2 : 0.2502 * max (w - u0 ℓ) 0 / √ℓ ≤ 0.2502 * (w - b) / √ℓ :=
              div_le_div_of_nonneg_right (by linarith) hsℓ.le
            have e : (0.0314 + 0.2502 * (w - b) + 0.5 * (w - b) ^ 2) / √ℓ =
                0.5 * (w - b) ^ 2 / √ℓ + 0.2502 * (w - b) / √ℓ + 0.0314 / √ℓ := by ring
            rw [e]; linarith
          have htail := rho_tail hu2 hwu
          rw [← hr0def] at htail
          have hexp : Real.exp (-(r0 * (w - u))) =
              Real.exp (-(r0 * d)) * Real.exp (-(r0 * (w - b))) := by
            rw [← Real.exp_add]; congr 1; rw [hd]; ring
          rw [hexp] at htail
          have hq0 : 0 ≤ (0.0314 + 0.2502 * (w - b) + 0.5 * (w - b) ^ 2) := by
            have : 0 ≤ w - b := by linarith
            positivity
          simp only [hF, haQ, sub_zero]
          calc aQ (mOf ℓ w) w * Dickman.rho (w - 1) / w
              = aQ (mOf ℓ w) w * (Dickman.rho (w - 1) / w) := by ring
            _ ≤ (0.0314 + 0.2502 * (w - b) + 0.5 * (w - b) ^ 2) / √ℓ *
                (Dickman.rho (u - 1) * (Real.exp (-(r0 * d)) * Real.exp (-(r0 * (w - b)))) / u) :=
                mul_le_mul hq htail (div_nonneg (Dickman.rho_pos _).le hw0.le) (by positivity)
            _ = _ := by rw [hK]; field_simp
      _ = K * Q := by rw [integral_const_mul, hqv]
  have hQle : Q ≤ 1.2816 / r0 := by
    have h2 : 0.2502 / r0 ^ 2 ≤ 0.2502 / r0 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
    have h3 : 2 * 0.5 / r0 ^ 3 ≤ 1 / r0 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_le_pow_right₀ hr0 (by norm_num : 1 ≤ 3)]
    rw [hQ]
    have : 1.2816 / r0 = 0.0314 / r0 + 0.2502 / r0 + 1 / r0 := by ring
    linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  -- `ℓ K Q ≤ 0.01`
  have hsq := (show u0 ℓ ^ 2 = √ℓ from Real.sq_sqrt (Real.sqrt_nonneg ℓ))
  have hℓs : ℓ / √ℓ = √ℓ := by
    rw [div_eq_iff hsℓ.ne']; exact (Real.mul_self_sqrt hℓ0.le).symm
  have hmain : ℓ * (K * Q) / Dickman.rho (u - 1) ≤ 0.01 := by
    have e : ℓ * (K * Q) / Dickman.rho (u - 1) = √ℓ * 1 * Real.exp (-(r0 * d)) * Q / u := by
      have hs := Real.mul_self_sqrt hℓ0.le
      rw [hK]
      field_simp
      nlinarith [hs]
    rw [e, div_le_iff₀ hupos]
    rcases le_or_gt (u0 ℓ / 2) u with hbig' | hsmall
    · -- `r₀ ≥ log(u-1)`, `r₀ ≥ 9`
      have hr9 : 9 ≤ r0 := ratio_ge_nine (by linarith)
      have hlog := ratio_ge_log (x := u - 1) (by linarith)
      rw [← hr0def] at hlog
      have he1 : Real.exp (-r0) ≤ 1 / (u - 1) := by
        calc Real.exp (-r0) ≤ Real.exp (-Real.log (u - 1)) := Real.exp_le_exp.mpr (by linarith)
          _ = 1 / (u - 1) := by rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
      have he2 : Real.exp (-(0.74 * r0)) ≤ 1 / 81 := by
        have h := Real.pow_div_factorial_le_exp (x := 0.74 * r0) (by positivity) 4
        have : (81 : ℝ) ≤ (0.74 * r0) ^ 4 / (Nat.factorial 4 : ℝ) := by
          norm_num [Nat.factorial]
          have : (6.66 : ℝ) ≤ 0.74 * r0 := by linarith
          have := pow_le_pow_left₀ (by norm_num) this 4
          norm_num at this; linarith
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (this.trans h)
      have hed : Real.exp (-(r0 * d)) ≤ Real.exp (-r0) * Real.exp (-(0.74 * r0)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have hρ1le : Dickman.rho (u - 1) ≤ 1 := Dickman.rho_le_one _
      have hs4 : √ℓ ≤ 4 * u ^ 2 := by rw [← hsq]; nlinarith
      have hQ9 : Q ≤ 0.1424 := by
        have : 1.2816 / r0 ≤ 1.2816 / 9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr9
        have : (1.2816 : ℝ) / 9 ≤ 0.1424 := by norm_num
        linarith
      have hexp0 := Real.exp_pos (-(r0 * d))
      calc √ℓ * 1 * Real.exp (-(r0 * d)) * Q
          ≤ (4 * u ^ 2) * 1 * (1 / (u - 1) * (1 / 81)) * 0.1424 := by
            have hp1 : 0 ≤ 1 / (u - 1) := div_nonneg zero_le_one (by linarith)
            have hp2 : 0 ≤ 1 / (u - 1) * (1 / 81) := mul_nonneg hp1 (by norm_num)
            apply mul_le_mul _ hQ9 hQ0 (mul_nonneg (by positivity) hp2)
            apply mul_le_mul _ (hed.trans (mul_le_mul he1 he2 (Real.exp_pos _).le hp1))
              hexp0.le (by positivity)
            exact mul_le_mul hs4 le_rfl zero_le_one (by positivity)
        _ ≤ 0.01 * u := by
            rw [show (4 * u ^ 2) * 1 * (1 / (u - 1) * (1 / 81)) * 0.1424 =
              0.5696 / 81 * u ^ 2 / (u - 1) by field_simp; ring]
            rw [div_le_iff₀ (by linarith)]
            nlinarith
    · -- `d ≥ u₀/2 - 0.26`, `r₀ ≥ 1`
      have hdD : u0 ℓ / 2 - 0.26 ≤ d := by rw [hd, hb]; linarith
      have hD : 15000 ≤ d := by linarith
      have hed : Real.exp (-(r0 * d)) ≤ Real.exp (-d) := Real.exp_le_exp.mpr (by nlinarith)
      have hρ1le : Dickman.rho (u - 1) ≤ 1 := Dickman.rho_le_one _
      have hs9 : √ℓ ≤ 9 * d ^ 2 := by rw [← hsq]; nlinarith
      have hQ1 : Q ≤ 1.2816 := by
        have : 1.2816 / r0 ≤ 1.2816 := div_le_self (by norm_num) hr0
        linarith
      have h5 := Real.pow_div_factorial_le_exp (x := d) (by linarith) 5
      have hexpd : Real.exp (-d) ≤ 120 / d ^ 5 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos d) (by positivity)]
        norm_num [Nat.factorial] at h5
        nlinarith
      calc √ℓ * 1 * Real.exp (-(r0 * d)) * Q
          ≤ (9 * d ^ 2) * 1 * (120 / d ^ 5) * 1.2816 := by
            apply mul_le_mul _ hQ1 hQ0 (by positivity)
            apply mul_le_mul _ (hed.trans hexpd) (Real.exp_pos _).le (by positivity)
            exact mul_le_mul hs9 le_rfl zero_le_one (by positivity)
        _ ≤ 0.01 * u := by
            rw [show (9 * d ^ 2) * 1 * (120 / d ^ 5) * 1.2816 = 1384.128 / d ^ 3 by
              field_simp; ring]
            rw [div_le_iff₀ (by positivity)]
            nlinarith [pow_le_pow_left₀ (by norm_num) hD 3]
  rw [hsA]
  have hdiv : ℓ * ((∫ w in Ioi (u - 1), F w) / Dickman.rho (u - 1)) ≤
      ℓ * (K * Q) / Dickman.rho (u - 1) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbig hρ1.le) hℓ0.le
  have hfin := hdiv.trans hmain
  have hnn : 0 ≤ ℓ * ((∫ w in Ioi (u - 1), F w) / Dickman.rho (u - 1)) :=
    mul_nonneg hℓ0.le (div_nonneg hI0 hρ1.le)
  rw [mul_neg]
  constructor
  · linarith only [hfin]
  · linarith only [hnn]

/-- **Lemma 5.7, the slack `s_a`.** -/
theorem lemma57Slack : Lemma57Slack := by
  intro τ ℓ u hR
  obtain ⟨-, -, hℓ, hu2, -⟩ := hR
  exact ⟨fun h => slack_big hℓ h, fun h => slack_small hℓ hu2 h⟩

end BSaias.Large

end
