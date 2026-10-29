module

public import RequestProject.Beurling.Noise.BSZ1Int
public import RequestProject.Beurling.Noise.BSZ2Integrable

/-!
# Region Z1 of Theorem 5.6 (Step 7(i)): `Σ(ℓ, u) ≥ 0` for `u < 2`

**`BSaias.regionZ1 : RegionZ1`**: for `τ ≥ 10⁸`, `ℓ > 30τ` and `0 ≤ u < 2`,
`0 ≤ Σ(ℓ, u)`. Quantitatively (`ell_Sigma_ge`),

  `ℓ Σ(ℓ, u) ≥ 0.5639 (4τ + 1500) - 2.0345 (τ + log 2) - 17280055 ≥ 0.22 τ - 1.73·10⁷ > 0`,

to compare with the paper's `ℓΣ ≥ 0.265τ - 2714`.

The proof follows Step 7(i): `ρ(u-1) = 1`, `w_lo ∈ [w₁, 1)`, the main term is split as
`∫ π e^{D_Φ} + ∫ π e^{D_Φ}(e^{D'} - 1)` with `D' = Q(m, w)`; the first is at most
`1 + μ₀ - Φ_ben` with the exact excess mass `μ₀ ≤ log(1/w₁)` from (R1), and the `Φ`-benefit beats
`μ₀` at the order `τ/ℓ` (`0.5639·4 = 2.2556 > 2.0345`). All the remaining terms (the `A`- and
`a`-parts of `D'`, `E₁`, `E₂`, `E₃`, `T`) are `O(1/ℓ)` with an absolute constant; we bound them
more crudely than the paper (one majorant `F(w) = ρ(w-1)(1+w)⁶e^{(1+w)/2}/w` for all of them,
`∫F ≤ 480000`), which the margin `0.22τ ≥ 2.2·10⁷` absorbs. In particular no bound on `ρ(39)`,
`r(39)`, `J₂` or the other moments of Step 7(i) is needed.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral Set

namespace BSaias

namespace Z1

variable {τ ℓ u : ℝ}

lemma wlo_ge (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 0.9 ≤ wlo τ ℓ u :=
  (w1_ge hτ hℓ).trans (le_max_right _ _)

lemma wlo_le_one (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu2 : u < 2) : wlo τ ℓ u ≤ 1 :=
  max_le (by linarith) (w1_lt_one hτ hℓ).le

lemma U_ge_three (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) : 3 ≤ Uf τ ℓ := by
  have := u0_ge hτ hℓ; have := u0_le_U τ ℓ; linarith

lemma hyp_of_mem (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu0 : 0 ≤ u) (hu2 : u < 2) {w : ℝ}
    (hw : w ∈ Icc (wlo τ ℓ u) (Uf τ ℓ)) : Hyp τ ℓ u w :=
  ⟨hτ, hℓ, hu0, hu2, hw.1, hw.2⟩

lemma wlo_le_U (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu2 : u < 2) :
    wlo τ ℓ u ≤ Uf τ ℓ := by
  have := wlo_le_one (u := u) hτ hℓ hu2; have := U_ge_three hτ hℓ; linarith

/-! ## The tail `T` -/

lemma PhiInf_ge_C0 {τ : ℝ} (hτ : 0 < τ) : C0 ≤ PhiInf τ := by
  unfold PhiInf
  have h1 : 1 ≤ Real.exp (kappa τ / τ) := Real.one_le_exp (by unfold kappa; positivity)
  have hmax : Real.exp (kappa τ / τ) ≤ max (Real.exp (kappa τ / τ))
      (30 * Real.exp (kappa τ / (30 * τ))) := le_max_left _ _
  unfold C0
  nlinarith

/-- `ℓ T ≤ 1`. -/
lemma ell_T_le (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu2 : u < 2) (hu0 : 0 ≤ u) :
    ℓ * Tterm τ ℓ u ≤ 1 := by
  have hℓ0 := ell_pos hτ hℓ
  have hτ0 : 0 < τ := by linarith
  set U := Uf τ ℓ
  set us := ustar τ ℓ
  have hus : us = U + 1 / 2 := rfl
  have hv := u0_ge hτ hℓ
  have hvU := u0_le_U τ ℓ
  have hsize := (U_size_both hτ hℓ).1
  -- `G ≥ C₀ e^{-k}`
  have hk := kappa_div_le hτ hℓ
  have hQ : 0 ≤ Qf ℓ u := by
    unfold Qf BSCert.Z2.A aQ
    have : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    positivity
  have hG : C0 * Real.exp (-(kappa τ / ℓ)) ≤ Gf τ ℓ u := by
    unfold Gf Phi
    rw [Dickman.rho_of_le_one (by linarith), mul_one]
    have h1 := PhiInf_ge_C0 hτ0
    have h2 := Real.one_le_exp hQ
    have h3 := Real.exp_pos (-(kappa τ / ℓ))
    have h4 : C0 * Real.exp (-(kappa τ / ℓ)) ≤ PhiInf τ * Real.exp (-(kappa τ / ℓ)) :=
      mul_le_mul_of_nonneg_right h1 h3.le
    have h5 : 0 ≤ PhiInf τ * Real.exp (-(kappa τ / ℓ)) :=
      le_trans (by unfold C0; positivity) h4
    nlinarith
  have hC0 : (0 : ℝ) < C0 := by unfold C0; norm_num
  have hGpos : 0 < Gf τ ℓ u := lt_of_lt_of_le (by positivity) hG
  -- `ρ(u*) ≤ e^{-(u* - 1)}`
  have hρ : Dickman.rho us ≤ Real.exp (-(us - 1)) := by
    have := Dickman.rho_le_exp (w := 1) (t := us) le_rfl (by rw [hus]; linarith)
    rw [Dickman.rho_of_le_one le_rfl, Dickman.ratio_one_two le_rfl (by norm_num)] at this
    simpa using this
  -- `a_V(u*) ≤ 0.186`
  have haV : aV ℓ us ≤ 0.186 := by
    unfold aV
    rw [div_le_iff₀ hℓ0]
    have h1 : us ^ 2 ≤ (1 + U) ^ 2 := pow_le_pow_left₀ (by linarith) (by rw [hus]; linarith) 2
    have h2 : Real.log (us + 2) ≤ Real.log (3 + U) :=
      Real.log_le_log (by linarith) (by rw [hus]; linarith)
    have h3 : 0 ≤ Real.log (us + 2) := Real.log_nonneg (by linarith)
    have := mul_le_mul h1 h2 h3 (by positivity)
    nlinarith
  -- assemble
  have hT : Tterm τ ℓ u ≤ ℓ / τ * Real.exp (-(us - 1)) * Real.exp 0.186 *
      Real.exp 0.13334 := by
    unfold Tterm
    rw [div_le_iff₀ hGpos]
    have hρ0 := (Dickman.rho_pos us).le
    have e1 : Real.exp (aV ℓ us) ≤ Real.exp 0.186 := Real.exp_le_exp.mpr haV
    have e2 : Real.exp 0.13334 * Real.exp (-(kappa τ / ℓ)) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have hlt : 0 ≤ ℓ / τ := by positivity
    calc ℓ / τ * C0 * Dickman.rho us * Real.exp (aV ℓ us)
        ≤ ℓ / τ * C0 * Real.exp (-(us - 1)) * Real.exp 0.186 := by gcongr
      _ ≤ ℓ / τ * C0 * Real.exp (-(us - 1)) * Real.exp 0.186 *
          (Real.exp 0.13334 * Real.exp (-(kappa τ / ℓ))) := by
          have : 0 ≤ ℓ / τ * C0 * Real.exp (-(us - 1)) * Real.exp 0.186 := by positivity
          nlinarith
      _ = ℓ / τ * Real.exp (-(us - 1)) * Real.exp 0.186 * Real.exp 0.13334 *
          (C0 * Real.exp (-(kappa τ / ℓ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hG (by positivity)
  -- `ℓ²/τ · e^{1.32 - u*} ≤ 1`
  have hexp : Real.exp (-(us - 1)) * Real.exp 0.186 * Real.exp 0.13334 ≤
      Real.exp 2 * Real.exp (-u0 ℓ) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; rw [hus]; linarith
  set v := u0 ℓ
  have hℓv : ℓ = v ^ 4 := (u0_pow4 hℓ0.le).symm
  have hfact : v ^ 9 / 362880 ≤ Real.exp v := by
    have := Real.pow_div_factorial_le_exp v (by linarith) 9
    rwa [show (Nat.factorial 9 : ℝ) = 362880 by norm_num [Nat.factorial]] at this
  have hv8 : v ^ 8 * Real.exp (-v) ≤ 1551 := by
    have he : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
    have hev := Real.exp_pos (-v)
    have h1 : v ^ 9 * Real.exp (-v) ≤ 362880 := by
      rw [div_le_iff₀ (by norm_num)] at hfact
      nlinarith
    have : v ^ 9 = v * v ^ 8 := by ring
    rw [this] at h1
    have h2 : 234 * (v ^ 8 * Real.exp (-v)) ≤ v * (v ^ 8 * Real.exp (-v)) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    nlinarith
  have he2 := exp_two_le
  calc ℓ * Tterm τ ℓ u ≤ ℓ * (ℓ / τ * Real.exp (-(us - 1)) * Real.exp 0.186 *
        Real.exp 0.13334) := mul_le_mul_of_nonneg_left hT hℓ0.le
    _ = ℓ ^ 2 / τ * (Real.exp (-(us - 1)) * Real.exp 0.186 * Real.exp 0.13334) := by ring
    _ ≤ ℓ ^ 2 / τ * (Real.exp 2 * Real.exp (-v)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = v ^ 8 * Real.exp (-v) * Real.exp 2 / τ := by rw [hℓv]; ring
    _ ≤ 1551 * 7.39 / 100000000 := by
        apply div_le_div₀ (by norm_num) _ (by norm_num) hτ
        exact mul_le_mul hv8 he2 (Real.exp_pos _).le (by norm_num)
    _ ≤ 1 := by norm_num

/-! ## `E₁` -/

lemma ell_E1_le (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu0 : 0 ≤ u) (hu2 : u < 2) (I : Set ℝ) :
    ℓ * E1term τ ℓ u I ≤ 54 := by
  have hℓ0 := ell_pos hτ hℓ
  set W := wlo τ ℓ u
  have hW := wlo_ge (u := u) hτ hℓ
  have hW1 := wlo_le_one hτ hℓ hu2
  have h := hyp_of_mem hτ hℓ hu0 hu2 ⟨le_refl W, wlo_le_U hτ hℓ hu2⟩
  obtain ⟨hg0, hg⟩ := h.gfun_le I
  have hy : Real.exp (-(kappa τ / (W * ℓ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ kappa τ / (W * ℓ) := by unfold kappa; positivity
    linarith
  have hQ : Real.exp (Qf (mOf ℓ W) W) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by linarith [h.Qm_le])
  have he := exp_one_lt'
  have hρ := Dickman.rho_le_one (W - 1)
  have hρ0 := (Dickman.rho_pos (W - 1)).le
  have hgW : gfun τ ℓ u I W ≤ 2.72 := by
    refine hg.trans ?_
    have h1 : Dickman.rho (W - 1) * Real.exp (-(kappa τ / (W * ℓ))) ≤ 1 := by
      have := mul_le_mul hρ hy (Real.exp_pos _).le (by norm_num); linarith
    have h2 := mul_le_mul h1 hQ (Real.exp_pos _).le (by norm_num)
    linarith
  unfold E1term Kp
  have e : ℓ * (2 * 2.2 * (1 + W) ^ 2 * gfun τ ℓ u I W / (W * ℓ)) =
      4.4 * (1 + W) ^ 2 * gfun τ ℓ u I W / W := by field_simp; ring
  rw [e, div_le_iff₀ (by linarith)]
  have hsq : (1 + W) ^ 2 ≤ 4 := by nlinarith
  have := mul_le_mul hsq hgW hg0 (by norm_num)
  nlinarith

/-! ## Assembly -/

/-- **Region Z1, quantitatively**:
`ℓΣ(ℓ, u) ≥ 0.5639 (4τ + 1500) - 2.0345 (τ + log 2) - 17280055`. -/
theorem ell_Sigma_ge (hτ : 100000000 ≤ τ) (hℓ : 30 * τ < ℓ) (hu0 : 0 ≤ u) (hu2 : u < 2) :
    0.5639 * (4 * τ + 1500) - 2.0345 * (τ + Real.log 2) - 17280055 ≤ ℓ * Sigma τ ℓ u := by
  have hℓ0 := ell_pos hτ hℓ
  set W := wlo τ ℓ u with hWdef
  set U := Uf τ ℓ with hUdef
  set I := paperCut τ ℓ
  have hW := wlo_ge (u := u) hτ hℓ
  have hW1 := wlo_le_one hτ hℓ hu2
  have hU3 := U_ge_three hτ hℓ
  have hWU : W ≤ U := by linarith
  have hW0 : 0 < W := by linarith
  have hτ1 : (1 : ℝ) ≤ τ := by linarith
  have hℓ3 : 3 * τ < ℓ := by linarith
  have hI := measurableSet_paperCut τ ℓ
  set k := kappa τ / ℓ with hkdef
  have hk := kappa_div_le hτ hℓ
  have hk0 := kappa_div_nonneg hτ hℓ
  have hyp : ∀ w ∈ Icc W U, Hyp τ ℓ u w := fun w hw => hyp_of_mem hτ hℓ hu0 hu2 hw
  have hF := integral_Fz1_le hW (by linarith) hU3
  have hFi := intervalIntegrable_Fz1 hW0 hWU
  -- the main integrand
  have hmainI : IntervalIntegrable (fun w => Dickman.rho (w - 1) / w) volume W U :=
    (continuousOn_rho_div hW0 hWU (fun _ => (1 : ℝ)) continuous_const).intervalIntegrable.congr
      (fun w _ => by simp)
  have hbenI := benefit_integrable k hW0 hWU
  have hexpI : IntervalIntegrable
      (fun w => Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) / w) volume W U := by
    refine (hmainI.sub hbenI).congr (fun w _ => ?_)
    have e : kappa τ / (w * ℓ) = k / w := by rw [hkdef]; field_simp
    show _ - _ = _
    rw [e]; ring
  -- M
  have hM : Mterm τ ℓ u I ≤ (Real.log (1 / W) + 1) - 0.5639 * k + 25 / ℓ * 480000 := by
    unfold Mterm
    have h1 : ∫ w in W..U, gfun τ ℓ u I w / w ≤ ∫ w in W..U,
        (Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) / w + 25 / ℓ * Fz1 w) :=
      integral_mono_on hWU (intervalIntegrable_M hτ1 hℓ3 hI) (hexpI.add (hFi.const_mul _))
        (fun w hw => (hyp w hw).bound_M I)
    rw [integral_add hexpI (hFi.const_mul _), intervalIntegral.integral_const_mul] at h1
    have h2 : ∫ w in W..U, Dickman.rho (w - 1) * Real.exp (-(kappa τ / (w * ℓ))) / w =
        (∫ w in W..U, Dickman.rho (w - 1) / w) -
          ∫ w in W..U, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w := by
      rw [← integral_sub hmainI hbenI]
      apply integral_congr
      intro w hw
      have e : kappa τ / (w * ℓ) = k / w := by rw [hkdef]; field_simp
      simp only [e]; ring
    have h3 := integral_mass_le hW0 hW1 (by linarith : (1 : ℝ) ≤ U)
    have h4 : ∫ w in (1 : ℝ)..3, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w ≤
        ∫ w in W..U, Dickman.rho (w - 1) * (1 - Real.exp (-(k / w))) / w := by
      apply integral_mono_interval hW1 (by norm_num) hU3 _ hbenI
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with w hw
      have hw0 : 0 < w := by linarith [hw.1]
      have : Real.exp (-(k / w)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := div_nonneg hk0 hw0.le; linarith)
      have := (Dickman.rho_pos (w - 1)).le
      simp only [Pi.zero_apply]
      apply div_nonneg _ hw0.le
      exact mul_nonneg this (by linarith)
    have h5 := benefit_ge hk0 hk
    have hFF : 25 / ℓ * ∫ w in W..U, Fz1 w ≤ 25 / ℓ * 480000 :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    linarith
  -- E₂, E₃
  have hE2 : E2term τ ℓ u I ≤ 2.2 / ℓ * 480000 := by
    unfold E2term Kp
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans ?_ hF
    exact integral_mono_on hWU (intervalIntegrable_E2 hτ1 hℓ3 hI) hFi
      (fun w hw => (hyp w hw).bound_E2 I)
  have hE3 : E3term τ ℓ u I ≤ 4.4 * (2 / ℓ * 480000) := by
    unfold E3term Kp
    have h1 : ∫ w in W..U, gfun τ ℓ u I w * etaF τ ℓ w / w ≤ ∫ w in W..U, 2 / ℓ * Fz1 w :=
      integral_mono_on hWU (intervalIntegrable_E3 hτ1 hℓ3 hI) (hFi.const_mul _)
        (fun w hw => (hyp w hw).bound_E3 I)
    rw [intervalIntegral.integral_const_mul] at h1
    have h2 : 2 / ℓ * ∫ w in W..U, Fz1 w ≤ 2 / ℓ * 480000 :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    have : (2 : ℝ) * 2.2 = 4.4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
  have hE1 := ell_E1_le hτ hℓ hu0 hu2 I
  have hT := ell_T_le hτ hℓ hu2 hu0
  -- `μ₀ ≤ log(1/w₁)`
  have hμ : Real.log (1 / W) ≤ 2.0345 * ((τ + Real.log 2) / ℓ) := by
    refine le_trans ?_ (log_inv_w1_le hτ hℓ)
    have hw1p : 0 < w1 τ ℓ := by have := w1_ge hτ hℓ; linarith
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le hw1p (le_max_right _ _)
  -- combine
  unfold Sigma SigmaGen
  have hk' : ℓ * k = 4 * τ + 1500 := by rw [hkdef]; unfold kappa; field_simp
  have hμ' : ℓ * Real.log (1 / W) ≤ 2.0345 * (τ + Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hμ hℓ0.le
    have e : ℓ * (2.0345 * ((τ + Real.log 2) / ℓ)) = 2.0345 * (τ + Real.log 2) := by
      field_simp
    linarith
  have hM' := mul_le_mul_of_nonneg_left hM hℓ0.le
  have hE2' := mul_le_mul_of_nonneg_left hE2 hℓ0.le
  have hE3' := mul_le_mul_of_nonneg_left hE3 hℓ0.le
  have e1 : ℓ * ((Real.log (1 / W) + 1) - 0.5639 * k + 25 / ℓ * 480000) =
      ℓ * Real.log (1 / W) + ℓ - 0.5639 * (ℓ * k) + 25 * 480000 := by field_simp
  have e2 : ℓ * (2.2 / ℓ * 480000) = 2.2 * 480000 := by field_simp
  have e3 : ℓ * (4.4 * (2 / ℓ * 480000)) = 4.4 * 2 * 480000 := by field_simp
  rw [e1] at hM'; rw [e2] at hE2'; rw [e3] at hE3'
  have e4 : ℓ * (1 - (Mterm τ ℓ u I + E1term τ ℓ u I + E2term τ ℓ u I + E3term τ ℓ u I +
      Tterm τ ℓ u)) = ℓ - (ℓ * Mterm τ ℓ u I + ℓ * E1term τ ℓ u I + ℓ * E2term τ ℓ u I +
      ℓ * E3term τ ℓ u I + ℓ * Tterm τ ℓ u) := by ring
  rw [e4]
  nlinarith

/-- **Step 7(i) of the proof of Theorem 5.6 (region Z1)**: `Σ(ℓ, u) ≥ 0` for `u < 2`. -/
theorem regionZ1 : RegionZ1 := by
  intro τ ℓ u hτ hℓ hu0 hu2
  have h := ell_Sigma_ge hτ hℓ hu0 hu2
  have hℓ0 := ell_pos hτ hℓ
  have := log_two_bounds
  have hpos : 0 < ℓ * Sigma τ ℓ u := by nlinarith
  exact (pos_of_mul_pos_right hpos hℓ0.le).le

end Z1

/-- **Step 7(i) of the proof of Theorem 5.6 (region Z1)**, exported. -/
theorem regionZ1 : RegionZ1 := Z1.regionZ1

end BSaias

end
