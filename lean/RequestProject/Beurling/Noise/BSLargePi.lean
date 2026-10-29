module

public import RequestProject.Beurling.Noise.BSLargeInt

/-!
# The quantities `e₁`, `e₂`, `j_A`, `Φ_ben` of `c(u)` (Theorem 5.6, Step 7(ii))

For `u ≥ 2`, with `r = r(u)`, `r₀ = r(u-1)`:

* `e1_eq`: `e₁ = u² r(u-1)`;
* `e2_le`: `e₂ ≤ u + 1`;
* `jA_le`: `j_A ≤ (1+u)³ log(2+u)/u - k(u)(1 - 1/r) + 8Λ(u) M(r₀)/u`, with
  `k(u) = u³(3u-4) log(1+u)/(u-1)²` (the chord bound on `[u-1, u]`) and
  `M(r) = 1/r² + 6/r³ + 18/r⁴ + 24/r⁵ = ∫₀^∞ s(1+s)³ e^{-rs} ds` (the part `w ≥ u`, by (R3));
* `PhiBen_nonneg`, `PhiBen_ge`: `0 ≤ Φ_ben` and `Φ_ben ≥ (1 - e^{-κ_Φ/(uℓ)})(1 - 1/(ur))`.

These are the bounds used in "Positivity of `c(u)`" (04c-saias.tex, lines 505-529).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace BSaias.Large

lemma e1_eq (u : ℝ) : e1 u = u ^ 2 * Dickman.ratio (u - 1) := by
  unfold e1 Dickman.ratio
  have : (1 + (u - 1)) = u := by ring
  rw [this]; ring

lemma rho_div_rho {u : ℝ} (hu : 2 ≤ u) :
    u * Dickman.rho u / Dickman.rho (u - 1) = 1 / Dickman.ratio u := by
  unfold Dickman.ratio
  have h1 := Dickman.rho_pos u
  have h2 := Dickman.rho_pos (u - 1)
  have hu0 : 0 < u := by linarith
  field_simp

/-- Splitting `(u-1, ∞) = (u-1, u] ∪ (u, ∞)`. -/
lemma integral_Ioi_split {u : ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (u - 1))) :
    ∫ w in Ioi (u - 1), f w = (∫ w in Ioc (u - 1) u, f w) + ∫ w in Ioi u, f w := by
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : u - 1 ≤ u)] at hf ⊢
  exact setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
    exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi
    (hf.mono_set subset_union_left) (hf.mono_set subset_union_right)

lemma continuousOn_rho_div {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun w => Dickman.rho (w - 1) / w) (Ici a) := by
  apply ContinuousOn.div (Dickman.continuous_rho.comp
    (continuous_id.sub continuous_const)).continuousOn continuousOn_id
  intro x hx; simp only [id]; linarith [mem_Ici.mp hx]

lemma one_add_le_pow_five {w : ℝ} (hw : 0 ≤ w) : 1 + w ≤ (1 + w) ^ 5 := by
  have h1 : 1 ≤ 1 + w := by linarith
  calc 1 + w = (1 + w) ^ 1 := (pow_one _).symm
    _ ≤ (1 + w) ^ 5 := pow_le_pow_right₀ h1 (by norm_num)

/-! ## `e₂` -/

lemma e2_le {u : ℝ} (hu : 2 ≤ u) : e2 u ≤ u + 1 := by
  have hρ1 := Dickman.rho_pos (u - 1)
  have hr0 := ratio_ge_one (v := u - 1) (by linarith)
  have hint : IntegrableOn (fun w => (1 + w) * Dickman.rho (w - 1) / w) (Ioi (u - 1)) := by
    apply integrableOn_mul_rho (C := 1) (φ := fun w => 1 + w) hu
      (by fun_prop : Continuous (fun w : ℝ => 1 + w)).continuousOn
    intro w hw
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + w), one_mul]
    exact one_add_le_pow_five (by linarith)
  obtain ⟨hI1, hE1⟩ := integral_Ioi_shift_div (a := u - 1) (by linarith)
  -- the integral splits as `∫ ρ(w-1)/w + ∫ ρ(w-1)`
  have hρint : IntegrableOn (fun w => Dickman.rho (w - 1)) (Ioi (u - 1)) := by
    refine IntegrableOn.congr_fun (Integrable.sub hint hI1) (fun w hw => ?_) measurableSet_Ioi
    have : w ≠ 0 := by have := mem_Ioi.mp hw; linarith
    simp only [Pi.sub_apply]
    field_simp; ring
  have hsplit : ∫ w in Ioi (u - 1), (1 + w) * Dickman.rho (w - 1) / w =
      (∫ w in Ioi (u - 1), Dickman.rho (w - 1) / w) + ∫ w in Ioi (u - 1), Dickman.rho (w - 1) := by
    rw [← integral_add hI1 hρint]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have : w ≠ 0 := by have := mem_Ioi.mp hw; linarith
    field_simp
  -- `∫_{(u-1,u]} ρ(w-1) = (u-1) ρ(u-1)`
  have hIoc : ∫ w in Ioc (u - 1) u, Dickman.rho (w - 1) = (u - 1) * Dickman.rho (u - 1) := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_right (fun t => Dickman.rho t) 1,
      Dickman.mul_rho_eq_integral (u := u - 1) (by linarith)]
  -- `∫_{(u,∞)} ρ(w-1) ≤ ρ(u-1)/r₀ ≤ ρ(u-1)`
  obtain ⟨hEi, hEv⟩ := integral_Ioi_exp (r := Dickman.ratio (u - 1)) (u := u) (by linarith)
  have hIoi : ∫ w in Ioi u, Dickman.rho (w - 1) ≤ Dickman.rho (u - 1) := by
    calc ∫ w in Ioi u, Dickman.rho (w - 1)
        ≤ ∫ w in Ioi u, Dickman.rho (u - 1) * Real.exp (-(Dickman.ratio (u - 1) * (w - u))) := by
          apply setIntegral_mono_on (hρint.mono_set (Ioi_subset_Ioi (by linarith)))
            (hEi.const_mul _) measurableSet_Ioi
          intro w hw
          have h := Dickman.rho_le_exp (w := u - 1) (t := w - 1) (by linarith)
            (by linarith [mem_Ioi.mp hw])
          have e : w - 1 - (u - 1) = w - u := by ring
          rwa [e] at h
      _ = Dickman.rho (u - 1) / Dickman.ratio (u - 1) := by
          rw [integral_const_mul, hEv]; ring
      _ ≤ Dickman.rho (u - 1) := div_le_self hρ1.le hr0
  unfold e2 Epi
  rw [div_le_iff₀ hρ1, hsplit, hE1, integral_Ioi_split hρint, hIoc]
  nlinarith

/-! ## `Φ_ben` -/

lemma integrableOn_phiBen {τ ℓ u : ℝ} (hu : 2 ≤ u) (hκ : 0 ≤ kappa τ) (hℓ : 0 < ℓ) :
    IntegrableOn (fun w => (1 - Real.exp (-(kappa τ / (w * ℓ)))) * Dickman.rho (w - 1) / w)
      (Ioi (u - 1)) := by
  apply integrableOn_mul_rho (C := 1) hu
  · intro w hw
    have hw0 : w ≠ 0 := by have := mem_Ici.mp hw; linarith
    apply ContinuousAt.continuousWithinAt
    have : ContinuousAt (fun w : ℝ => kappa τ / (w * ℓ)) w :=
      continuousAt_const.div (continuousAt_id.mul continuousAt_const) (mul_ne_zero hw0 hℓ.ne')
    exact continuousAt_const.sub (this.neg.rexp)
  · intro w hw
    have hw0 : 0 < w := by linarith
    have hy : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (by positivity)
    have h1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 := Real.exp_pos (-(kappa τ / (w * ℓ)))
    rw [abs_of_nonneg (by linarith), one_mul]
    exact le_trans (by linarith) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + w))

lemma PhiBen_nonneg {τ ℓ u : ℝ} (hu : 2 ≤ u) (hκ : 0 ≤ kappa τ) (hℓ : 0 < ℓ) :
    0 ≤ PhiBen τ ℓ u := by
  unfold PhiBen Epi
  apply div_nonneg _ (Dickman.rho_pos _).le
  apply setIntegral_nonneg measurableSet_Ioi
  intro w hw
  have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
  have hy : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (by positivity)
  have h1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact div_nonneg (mul_nonneg (by linarith) (Dickman.rho_pos _).le) hw0.le

/-- `Φ_ben ≥ (1 - e^{-κ_Φ/(uℓ)})(1 - 1/(u r(u)))`: restrict to `w ∈ (u-1, u]`, where
`κ_Φ/(wℓ) ≥ κ_Φ/(uℓ)`, and use `π((u-1, u]) = 1 - 1/(u r(u))` (R1). -/
lemma PhiBen_ge {τ ℓ u : ℝ} (hu : 2 ≤ u) (hκ : 0 ≤ kappa τ) (hℓ : 0 < ℓ) :
    (1 - Real.exp (-(kappa τ / (u * ℓ)))) * (1 - 1 / (u * Dickman.ratio u)) ≤ PhiBen τ ℓ u := by
  have hρ1 := Dickman.rho_pos (u - 1)
  have hu0 : 0 < u := by linarith
  set F := fun w => (1 - Real.exp (-(kappa τ / (w * ℓ)))) * Dickman.rho (w - 1) / w
  have hint : IntegrableOn F (Ioi (u - 1)) := integrableOn_phiBen hu hκ hℓ
  have hFnn : ∀ w ∈ Ioi (u - 1), 0 ≤ F w := by
    intro w hw
    have hw0 : 0 < w := by have := mem_Ioi.mp hw; linarith
    have hy : 0 ≤ kappa τ / (w * ℓ) := div_nonneg hκ (by positivity)
    have h1 : Real.exp (-(kappa τ / (w * ℓ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact div_nonneg (mul_nonneg (by linarith) (Dickman.rho_pos _).le) hw0.le
  have hsub : ∫ w in Ioc (u - 1) u, F w ≤ ∫ w in Ioi (u - 1), F w :=
    setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Ioi hFnn)
      (Eventually.of_forall fun w hw => Ioc_subset_Ioi_self hw)
  set c := 1 - Real.exp (-(kappa τ / (u * ℓ)))
  have hlow : ∫ w in Ioc (u - 1) u, c * (Dickman.rho (w - 1) / w) ≤ ∫ w in Ioc (u - 1) u, F w := by
    apply setIntegral_mono_on _ (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
    · intro w hw
      have hw0 : 0 < w := by linarith [hw.1]
      have hmono : kappa τ / (u * ℓ) ≤ kappa τ / (w * ℓ) :=
        div_le_div_of_nonneg_left hκ (by positivity) (mul_le_mul_of_nonneg_right hw.2 hℓ.le)
      have : c ≤ 1 - Real.exp (-(kappa τ / (w * ℓ))) := by
        simp only [c]; linarith [Real.exp_le_exp.mpr (neg_le_neg hmono)]
      simp only [F]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right this (div_nonneg (Dickman.rho_pos _).le hw0.le)
    · exact (((continuousOn_rho_div (a := u - 1) (by linarith)).mono Icc_subset_Ici_self
        ).integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul c
  have hval : ∫ w in Ioc (u - 1) u, c * (Dickman.rho (w - 1) / w) =
      c * (Dickman.rho (u - 1) - Dickman.rho u) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith),
      Dickman.integral_shift_div (by linarith) (by linarith)]
  have hmass : (Dickman.rho (u - 1) - Dickman.rho u) / Dickman.rho (u - 1) =
      1 - 1 / (u * Dickman.ratio u) := by
    unfold Dickman.ratio
    have := Dickman.rho_pos u
    field_simp
  unfold PhiBen Epi
  rw [← hmass, ← mul_div_assoc, ← hval]
  exact div_le_div_of_nonneg_right (hlow.trans hsub) hρ1.le


/-! ## `j_A` -/

/-- `M(r) = 1/r² + 6/r³ + 18/r⁴ + 24/r⁵`. -/
noncomputable def momM (r : ℝ) : ℝ := 1 / r ^ 2 + 6 / r ^ 3 + 18 / r ^ 4 + 24 / r ^ 5

/-- `Λ(w) ≤ Λ(u)(1+s)³` for `s = w - u ≥ 0`, `u ≥ 2`. -/
lemma Lam_shift_le {u w : ℝ} (hu : 2 ≤ u) (huw : u ≤ w) :
    (1 + w) ^ 2 * Real.log (2 + w) ≤ Lam u * (1 + (w - u)) ^ 3 := by
  set s := w - u with hs
  have hs0 : 0 ≤ s := by linarith
  have h1 : 1 + w ≤ (1 + u) * (1 + s) := by nlinarith
  have hL : Real.log (2 + u) ≥ 1 / (2 + u) := by
    have : Real.log 4 ≤ Real.log (2 + u) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : (1 : ℝ) / 4 ≤ Real.log 4 := by
      have := Real.log_two_gt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have : 1 / (2 + u) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h2 : Real.log (2 + w) ≤ Real.log (2 + u) * (1 + s) := by
    have hw : 2 + w = (2 + u) * (1 + s / (2 + u)) := by field_simp; ring
    rw [hw, Real.log_mul (by linarith) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + s / (2 + u) by positivity)
    have h3 : s / (2 + u) ≤ Real.log (2 + u) * s := by
      calc s / (2 + u) = (1 / (2 + u)) * s := by ring
        _ ≤ Real.log (2 + u) * s := mul_le_mul_of_nonneg_right hL hs0
    nlinarith
  have hL0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hLu : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  unfold Lam
  calc (1 + w) ^ 2 * Real.log (2 + w) ≤ ((1 + u) * (1 + s)) ^ 2 * (Real.log (2 + u) * (1 + s)) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) h1 2) h2 hL0 (by positivity)
    _ = (1 + u) ^ 2 * Real.log (2 + u) * (1 + s) ^ 3 := by ring

lemma hfun_le_pow_five {w : ℝ} (hw : 1 ≤ w) : hfun w ≤ (1 + w) ^ 5 := by
  unfold hfun
  have hw0 : 0 < w := by linarith
  have hl : Real.log (2 + w) ≤ 1 + w := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + w by linarith); linarith
  rw [div_le_iff₀ hw0]
  have hl0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hp : 0 ≤ (1 + w) ^ 4 := by positivity
  calc (1 + w) ^ 4 * Real.log (2 + w) ≤ (1 + w) ^ 4 * (1 + w) := mul_le_mul_of_nonneg_left hl hp
    _ = (1 + w) ^ 5 * 1 := by ring
    _ ≤ (1 + w) ^ 5 * w := mul_le_mul_of_nonneg_left hw (by positivity)

/-- `j_A ≤ (1+u)³ log(2+u)/u - k(u)(1 - 1/r(u)) + 8Λ(u) M(r(u-1))/u` for `u ≥ 2`. -/
lemma jA_le {u : ℝ} (hu : 2 ≤ u) :
    jA u ≤ (1 + u) ^ 3 * Real.log (2 + u) / u
      - u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 * (1 - 1 / Dickman.ratio u)
      + 8 * Lam u * momM (Dickman.ratio (u - 1)) / u := by
  have hρ1 := Dickman.rho_pos (u - 1)
  have hρu := Dickman.rho_pos u
  have hu0 : 0 < u := by linarith
  have hr0 := ratio_ge_one (v := u - 1) (by linarith)
  set cc := (1 + u) ^ 3 * Real.log (2 + u)
  set kc := u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2
  set H := hA u u
  set g := fun w => hA u w * Dickman.rho (w - 1) / w
  have hcc0 : 0 ≤ cc := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + u); positivity
  have hint : IntegrableOn g (Ioi (u - 1)) := by
    apply integrableOn_mul_rho (C := 1 + cc) hu
    · intro w hw
      have hw0 : 0 < w := by have := mem_Ici.mp hw; linarith
      exact ((hasDerivAt_hfun hw0).continuousAt.sub continuousAt_const).continuousWithinAt
    · intro w hw
      have hw1 : 1 ≤ w := by linarith
      have h5 := hfun_le_pow_five hw1
      have hh0 : 0 ≤ hfun w := by
        unfold hfun; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + w); positivity
      have hp : 1 ≤ (1 + w) ^ 5 := one_le_pow₀ (by linarith)
      unfold hA
      rw [abs_le]; constructor <;> nlinarith
  have hIoc_int : IntegrableOn (fun w => (H - kc * (u - w)) * Dickman.rho (w - 1) / w)
      (Ioc (u - 1) u) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    apply ContinuousOn.div (ContinuousOn.mul (by fun_prop) (Dickman.continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn) continuousOn_id
    intro x hx; simp only [id]; linarith [hx.1]
  -- Part I, `(u-1, u]`
  have hI : ∫ w in Ioc (u - 1) u, g w ≤
      H * (Dickman.rho (u - 1) - Dickman.rho u) -
        kc * (Dickman.rho (u - 1) - u * Dickman.rho u) := by
    calc ∫ w in Ioc (u - 1) u, g w
        ≤ ∫ w in Ioc (u - 1) u, (H - kc * (u - w)) * Dickman.rho (w - 1) / w := by
          apply setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) hIoc_int measurableSet_Ioc
          intro w hw
          have hw0 : 0 < w := by linarith [hw.1]
          have h := h_sub_ge hu hw.1.le hw.2
          simp only [g]
          rw [mul_div_assoc, mul_div_assoc]
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (Dickman.rho_pos _).le hw0.le)
          simp only [H, hA]; linarith
      _ = H * (Dickman.rho (u - 1) - Dickman.rho u) -
          kc * (Dickman.rho (u - 1) - u * Dickman.rho u) := by
          rw [← intervalIntegral.integral_of_le (by linarith)]
          have e : ∀ w, (H - kc * (u - w)) * Dickman.rho (w - 1) / w =
              H * (Dickman.rho (w - 1) / w) - kc * (Dickman.rho (w - 1) * (u - w) / w) := by
            intro w; ring
          simp_rw [e]
          rw [intervalIntegral.integral_sub
            ((Dickman.intervalIntegrable_shift_div (by linarith) (by linarith)).const_mul H) ?_,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            Dickman.integral_shift_div (by linarith) (by linarith),
            Dickman.integral_shift_mul_div hu]
          apply IntervalIntegrable.const_mul
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div (ContinuousOn.mul (Dickman.continuous_rho.comp
            (continuous_id.sub continuous_const)).continuousOn (by fun_prop)) continuousOn_id
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          simp only [id]; linarith [hx.1]
  -- Part II, `(u, ∞)`
  obtain ⟨hI1, hE1⟩ := integral_Ioi_shift_div (a := u) (by linarith)
  obtain ⟨hMi, hMv⟩ := integral_Ioi_moment (r := Dickman.ratio (u - 1)) (u := u) (by linarith)
  have hII : ∫ w in Ioi u, g w ≤ H * Dickman.rho u +
      8 * Lam u * Dickman.rho (u - 1) / u * momM (Dickman.ratio (u - 1)) := by
    calc ∫ w in Ioi u, g w ≤ ∫ w in Ioi u, (H * (Dickman.rho (w - 1) / w) +
          8 * Lam u * Dickman.rho (u - 1) / u *
            ((w - u) * (1 + (w - u)) ^ 3 * Real.exp (-(Dickman.ratio (u - 1) * (w - u))))) := by
          apply setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi (by linarith)))
            ((hI1.const_mul H).add (hMi.const_mul _)) measurableSet_Ioi
          intro w hw
          have huw : u ≤ w := (mem_Ioi.mp hw).le
          have hw0 : 0 < w := by linarith
          have hsub := h_sub_le (by linarith : (1 : ℝ) ≤ u) huw
          have hLs := Lam_shift_le hu huw
          have htail := rho_tail hu huw
          have hd0 : 0 ≤ Dickman.rho (w - 1) / w := div_nonneg (Dickman.rho_pos _).le hw0.le
          have hs0 : 0 ≤ w - u := by linarith
          have hlog0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
          -- `h(w) - h(u) ≤ 8Λ(u)(1+s)³ s`
          have hdiff : hfun w - hfun u ≤ 8 * Lam u * ((w - u) * (1 + (w - u)) ^ 3) := by
            calc hfun w - hfun u ≤ 8 * (1 + w) ^ 2 * Real.log (2 + w) * (w - u) := hsub
              _ = 8 * ((1 + w) ^ 2 * Real.log (2 + w)) * (w - u) := by ring
              _ ≤ 8 * (Lam u * (1 + (w - u)) ^ 3) * (w - u) := by
                apply mul_le_mul_of_nonneg_right _ hs0; linarith
              _ = _ := by ring
          have hLam0 : 0 ≤ Lam u := by
            unfold Lam; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + u); positivity
          have hq0 : 0 ≤ 8 * Lam u * ((w - u) * (1 + (w - u)) ^ 3) := by positivity
          simp only [g]
          have e : hA u w = H + (hfun w - hfun u) := by simp only [H, hA]; ring
          rw [e, add_mul, add_div, mul_div_assoc]
          apply add_le_add le_rfl
          calc (hfun w - hfun u) * Dickman.rho (w - 1) / w
              = (hfun w - hfun u) * (Dickman.rho (w - 1) / w) := by ring
            _ ≤ 8 * Lam u * ((w - u) * (1 + (w - u)) ^ 3) * (Dickman.rho (w - 1) / w) :=
                mul_le_mul_of_nonneg_right hdiff hd0
            _ ≤ 8 * Lam u * ((w - u) * (1 + (w - u)) ^ 3) * (Dickman.rho (u - 1) *
                  Real.exp (-(Dickman.ratio (u - 1) * (w - u))) / u) :=
                mul_le_mul_of_nonneg_left htail hq0
            _ = _ := by ring
      _ = H * Dickman.rho u +
          8 * Lam u * Dickman.rho (u - 1) / u * momM (Dickman.ratio (u - 1)) := by
          rw [integral_add (hI1.const_mul H) (hMi.const_mul _), integral_const_mul,
            integral_const_mul, hE1, hMv]
          rfl
  have hH : H = cc / u := by
    simp only [H, hA, hfun, cc]; field_simp; ring
  unfold jA Epi
  rw [div_le_iff₀ hρ1, integral_Ioi_split hint]
  have hmass := rho_div_rho hu
  have hk : kc * (Dickman.rho (u - 1) - u * Dickman.rho u) =
      kc * (1 - 1 / Dickman.ratio u) * Dickman.rho (u - 1) := by
    rw [← hmass]; field_simp
  have hsum := add_le_add hI hII
  rw [hk] at hsum
  have : H * (Dickman.rho (u - 1) - Dickman.rho u) + H * Dickman.rho u =
      H * Dickman.rho (u - 1) := by
    ring
  calc (∫ w in Ioc (u - 1) u, g w) + ∫ w in Ioi u, g w ≤ _ := hsum
    _ = (cc / u - kc * (1 - 1 / Dickman.ratio u) + 8 * Lam u * momM (Dickman.ratio (u - 1)) / u) *
          Dickman.rho (u - 1) := by rw [← hH]; ring

end BSaias.Large

end
