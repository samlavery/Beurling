module

public import RequestProject.Beurling.Noise.BSRedDeriv
public import RequestProject.Beurling.Noise.BSRedShift

/-!
# Theorem 5.6, Step 5: dividing by `G(ℓ, u)`, and comparison with the integrals of `Σ`

* `Gf_ratio`: `G(m, w) = G(ℓ, u) (ρ(w-1)/ρ(u-1)) e^{D(w)}` (since `Φ(m)/Φ(ℓ) = e^{-κ_Φ/(wℓ)}`);
* `Hf_eq_G`: `ν G(m, w) = G(ℓ, u) ((1+w)/w) g(w)`;
* `integral_le_cut`: for `[a, b] ⊆ paperCut`, `∫_a^b g φ ≤ ∫_a^{U} g 1[paperCut] φ` for
  `φ ≥ 0` continuous (this is how the window `w ≤ U(ℓ) - 1/2` of the partial summation is
  compared with the paper's cut-off `1[w ≤ U(m)]`).
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace BSaias

/-- `g(w)` without the cut-off. -/
noncomputable def g0 (τ ℓ u w : ℝ) : ℝ :=
  Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (Dfun τ ℓ u w)

lemma gfun_eq_indicator (τ ℓ u : ℝ) (I : Set ℝ) (w : ℝ) :
    gfun τ ℓ u I w = I.indicator (g0 τ ℓ u) w := rfl

lemma g0_nonneg (τ ℓ u w : ℝ) : 0 ≤ g0 τ ℓ u w := by
  unfold g0
  have := Dickman.rho_pos (w - 1); have := Dickman.rho_pos (u - 1); positivity

lemma gfun_nonneg (τ ℓ u : ℝ) (I : Set ℝ) (w : ℝ) : 0 ≤ gfun τ ℓ u I w := by
  rw [gfun_eq_indicator]; exact indicator_nonneg (fun x _ => g0_nonneg τ ℓ u x) w

lemma Gf_pos (τ ℓ u : ℝ) : 0 < Gf τ ℓ u := by
  unfold Gf
  have := Phi_pos' τ ℓ
  have := Dickman.rho_pos (u - 1)
  positivity
where
  Phi_pos' (τ ℓ : ℝ) : 0 < Phi τ ℓ := by
    unfold Phi
    have : 0 < PhiInf τ := by
      unfold PhiInf C0
      have := Real.exp_pos (kappa τ / τ)
      have : 0 < max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ))) :=
        lt_max_of_lt_left this
      positivity
    positivity

/-- `G(m, w) = G(ℓ, u) (ρ(w-1)/ρ(u-1)) e^{D(w)}`, `m = ℓw/(1+w)`. -/
lemma Gf_ratio {τ ℓ u w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    Gf τ (mOf ℓ w) w = Gf τ ℓ u * g0 τ ℓ u w := by
  unfold Gf Phi g0 Dfun
  have hr := Dickman.rho_pos (u - 1)
  have hm : kappa τ / mOf ℓ w = kappa τ / ℓ + kappa τ / (w * ℓ) := by
    unfold mOf; field_simp; ring
  have hr' : Dickman.rho (u - 1) ≠ 0 := hr.ne'
  calc PhiInf τ * Real.exp (-(kappa τ / mOf ℓ w)) * Dickman.rho (w - 1) *
        Real.exp (Qf (mOf ℓ w) w)
      = PhiInf τ * Dickman.rho (w - 1) * Real.exp (-(kappa τ / mOf ℓ w) + Qf (mOf ℓ w) w) := by
        rw [Real.exp_add]; ring
    _ = PhiInf τ * Dickman.rho (w - 1) * Real.exp ((-(kappa τ / ℓ) + Qf ℓ u) +
          (Qf (mOf ℓ w) w - Qf ℓ u - kappa τ / (w * ℓ))) := by rw [hm]; ring_nf
    _ = _ := by rw [Real.exp_add, Real.exp_add]; field_simp

/-- `Hf(w) = ν G(m, w) = G(ℓ, u) ((1+w)/w) g(w)`. -/
lemma Hf_eq_G {τ ℓ u w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    Hf τ ℓ w = Gf τ ℓ u * ((1 + w) / w) * g0 τ ℓ u w := by
  unfold Hf; rw [Gf_ratio (u := u) hℓ hw]; ring

lemma continuousOn_g0 {τ ℓ u a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    ContinuousOn (g0 τ ℓ u) (Icc a b) := by
  have hc := continuousOn_Hf (τ := τ) hℓ ha (b := b)
  have hG := Gf_pos τ ℓ u
  have : ContinuousOn (fun w => Hf τ ℓ w * w / ((1 + w) * Gf τ ℓ u)) (Icc a b) := by
    refine (hc.mul continuousOn_id).div ((continuousOn_const.add continuousOn_id).mul
      continuousOn_const) fun w hw => ?_
    have : 0 < 1 + w := by linarith [hw.1]
    positivity
  refine this.congr fun w hw => ?_
  have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
  beta_reduce
  rw [Hf_eq_G (u := u) hℓ hw0]
  have : 0 < 1 + w := by linarith
  field_simp

lemma red_measurableSet_paperCut (τ ℓ : ℝ) : MeasurableSet (paperCut τ ℓ) := by
  unfold paperCut
  apply measurableSet_le measurable_id
  unfold Uf u0 BSCert.Z2.u0 mOf
  fun_prop

/-- Comparison of the window integral with the integral of `Σ`. -/
lemma integral_le_cut {τ ℓ u a b U : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ U)
    (hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a U))
    (hφ0 : ∀ x ∈ Icc a U, 0 ≤ φ x) :
    ∫ x in a..b, g0 τ ℓ u x * φ x ≤ ∫ x in a..U, gfun τ ℓ u (paperCut τ ℓ) x * φ x := by
  have haU : a ≤ U := hab.trans hbU
  have hcont : ContinuousOn (fun x => g0 τ ℓ u x * φ x) (Icc a U) :=
    (continuousOn_g0 hℓ ha).mul hφ
  have hind : (fun x => gfun τ ℓ u (paperCut τ ℓ) x * φ x) =
      (paperCut τ ℓ).indicator (fun x => g0 τ ℓ u x * φ x) := by
    funext x
    rw [gfun_eq_indicator]
    by_cases hx : x ∈ paperCut τ ℓ
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  have hint : IntervalIntegrable (fun x => gfun τ ℓ u (paperCut τ ℓ) x * φ x) volume a U := by
    rw [hind, intervalIntegrable_iff]
    exact ((hcont.intervalIntegrable_of_Icc haU).def'.indicator (red_measurableSet_paperCut τ ℓ))
  rw [← integral_add_adjacent_intervals (hint.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le haU]; exact Icc_subset_Icc le_rfl hbU))
    (hint.mono_set (by rw [uIcc_of_le hbU, uIcc_of_le haU]; exact Icc_subset_Icc hab le_rfl))]
  have h1 : ∫ x in a..b, g0 τ ℓ u x * φ x =
      ∫ x in a..b, gfun τ ℓ u (paperCut τ ℓ) x * φ x := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp only
    rw [gfun_eq_indicator, indicator_of_mem (hcut x hx)]
  have h2 : 0 ≤ ∫ x in b..U, gfun τ ℓ u (paperCut τ ℓ) x * φ x := by
    apply integral_nonneg hbU
    intro x hx
    exact mul_nonneg (gfun_nonneg _ _ _ _ _) (hφ0 x ⟨hab.trans hx.1, hx.2⟩)
  linarith

lemma integral_cut_nonneg {τ ℓ u a U : ℝ} (haU : a ≤ U) {φ : ℝ → ℝ}
    (hφ0 : ∀ x ∈ Icc a U, 0 ≤ φ x) :
    0 ≤ ∫ x in a..U, gfun τ ℓ u (paperCut τ ℓ) x * φ x :=
  integral_nonneg haU fun x hx => mul_nonneg (gfun_nonneg _ _ _ _ _) (hφ0 x hx)

end BSaias

end
