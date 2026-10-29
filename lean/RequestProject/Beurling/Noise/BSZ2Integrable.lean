module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Integrability of the integrands of `Σ(ℓ, u)` (Theorem 5.6, Step 5)

The integrands of `M`, `E₂` and `E₃` are `g(w)/w`, `g(w)(1+w)/w` and `g(w) η_f(w)/w`, with
`g(w) = (ρ(w-1)/ρ(u-1)) e^{D(w)} 1[w ∈ I]`. For `w > 0` and `ℓ > 0` everything except the
cut-off is continuous, so on `[w_lo, U(ℓ)] ⊂ (0, ∞)` the integrands are bounded and measurable.

* `gBase_continuousAt`, `etaF_continuousAt`: continuity for `w > 0`;
* `measurableSet_paperCut`: the paper's cut-off `{w ≤ U(m)}` is measurable;
* `intervalIntegrable_M`, `intervalIntegrable_E2`, `intervalIntegrable_E3`: interval
  integrability on `[w_lo, U(ℓ)]` for every measurable cut-off, when `1 ≤ τ` and `3τ < ℓ`
  (so `w_lo ≥ w₁ > 0`).
-/

@[expose] public section

open Real MeasureTheory Set

namespace BSaias

/-- The continuous part of `g`: `(ρ(w-1)/ρ(u-1)) e^{D(w)}`. -/
noncomputable def gBase (τ ℓ u w : ℝ) : ℝ :=
  Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (Dfun τ ℓ u w)

lemma gfun_eq (τ ℓ u : ℝ) (I : Set ℝ) (w : ℝ) :
    gfun τ ℓ u I w = I.indicator (gBase τ ℓ u) w := rfl

lemma mOf_pos {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) : 0 < mOf ℓ w := by
  unfold mOf; positivity

lemma gBase_continuousAt (τ ℓ u : ℝ) {w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    ContinuousAt (gBase τ ℓ u) w := by
  have hm : 0 < mOf ℓ w := mOf_pos hℓ hw
  have h1 : (1 + w) ≠ 0 := by positivity
  have h2 : (2 + w) ≠ 0 := by positivity
  unfold gBase Dfun Qf aQ BSCert.Z2.A mOf u0 BSCert.Z2.u0
  unfold mOf at hm
  have hsq : √(ℓ * w / (1 + w)) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have := Dickman.continuous_rho
  fun_prop (disch := first | assumption | positivity | exact hm.ne' | exact hsq)

lemma etaF_continuousAt (τ ℓ : ℝ) {w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    ContinuousAt (etaF τ ℓ) w := by
  have hm : 0 < mOf ℓ w := mOf_pos hℓ hw
  have h1 : (1 + w) ≠ 0 := by positivity
  have h2 : (2 + w) ≠ 0 := by positivity
  unfold etaF dpos BSCert.Z2.A mOf u0 BSCert.Z2.u0
  unfold mOf at hm
  have hsq : √(ℓ * w / (1 + w)) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hsq2 : (ℓ * w / (1 + w)) * √(√(ℓ * w / (1 + w))) ≠ 0 := by positivity
  have hsq3 : (ℓ * w / (1 + w)) * √(ℓ * w / (1 + w)) ≠ 0 := by positivity
  have h4 : 4 * ((ℓ * w / (1 + w)) * √(√(ℓ * w / (1 + w)))) ≠ 0 := by positivity
  have h5 : 4 * ((ℓ * w / (1 + w)) * √(ℓ * w / (1 + w))) ≠ 0 := by positivity
  have h6 : (ℓ * w / (1 + w)) ^ 2 ≠ 0 := by positivity
  fun_prop (disch := first | assumption | positivity | exact hm.ne' | exact hsq)

/-- The paper's cut-off `{w : w ≤ U(m)}` is a measurable set. -/
lemma measurableSet_paperCut (τ ℓ : ℝ) : MeasurableSet (paperCut τ ℓ) := by
  unfold paperCut Uf mOf u0 BSCert.Z2.u0
  apply measurableSet_le measurable_id
  fun_prop

lemma w1_pos {τ ℓ : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) : 0 < w1 τ ℓ := by
  unfold w1
  have := Real.log_two_lt_d9
  have := Real.log_pos one_lt_two
  apply div_pos <;> norm_num at * <;> nlinarith

lemma wlo_pos {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) : 0 < wlo τ ℓ u :=
  lt_of_lt_of_le (w1_pos hτ hℓ) (le_max_right _ _)

lemma Uf_pos {τ ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < Uf τ ℓ := by
  unfold Uf u0 BSCert.Z2.u0
  have : 0 < √(√ℓ) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hℓ)
  have : 0 ≤ √(√ℓ) * √(2 * Real.log (ℓ / τ) + 4) := by positivity
  linarith

/-- The interval between `w_lo` and `U(ℓ)` lies in `(0, ∞)`. -/
lemma uIcc_subset {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) :
    uIcc (wlo τ ℓ u) (Uf τ ℓ) ⊆ Ioi 0 := by
  intro w hw
  rcases le_total (wlo τ ℓ u) (Uf τ ℓ) with h | h
  · rw [uIcc_of_le h] at hw; exact lt_of_lt_of_le (wlo_pos hτ hℓ) hw.1
  · rw [uIcc_of_ge h] at hw; exact lt_of_lt_of_le (Uf_pos (by linarith)) hw.1

/-- A function continuous on `(0, ∞)`, cut off by a measurable set, is interval integrable on
`[w_lo, U(ℓ)]`. -/
lemma intervalIntegrable_cut {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) {I : Set ℝ}
    (hI : MeasurableSet I) {F : ℝ → ℝ} (hF : ∀ w, 0 < w → ContinuousAt F w) :
    IntervalIntegrable (I.indicator F) volume (wlo τ ℓ u) (Uf τ ℓ) := by
  have hc : ContinuousOn F (uIcc (wlo τ ℓ u) (Uf τ ℓ)) := fun w hw =>
    (hF w (uIcc_subset hτ hℓ hw)).continuousWithinAt
  have hi := (hc.intervalIntegrable (μ := volume))
  rw [intervalIntegrable_iff] at hi ⊢
  exact hi.indicator hI

lemma intervalIntegrable_M {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    IntervalIntegrable (fun w => gfun τ ℓ u I w / w) volume (wlo τ ℓ u) (Uf τ ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have e : (fun w => gfun τ ℓ u I w / w) = I.indicator (fun w => gBase τ ℓ u w / w) := by
    funext w; by_cases h : w ∈ I <;> simp [gfun_eq, h]
  rw [e]
  exact intervalIntegrable_cut hτ hℓ hI fun w hw =>
    (gBase_continuousAt τ ℓ u hℓ0 hw).div continuousAt_id hw.ne'

lemma intervalIntegrable_E2 {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    IntervalIntegrable (fun w => gfun τ ℓ u I w * (1 + w) / w) volume (wlo τ ℓ u)
      (Uf τ ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have e : (fun w => gfun τ ℓ u I w * (1 + w) / w) =
      I.indicator (fun w => gBase τ ℓ u w * (1 + w) / w) := by
    funext w; by_cases h : w ∈ I <;> simp [gfun_eq, h]
  rw [e]
  exact intervalIntegrable_cut hτ hℓ hI fun w hw =>
    ((gBase_continuousAt τ ℓ u hℓ0 hw).mul (continuousAt_const.add continuousAt_id)).div
      continuousAt_id hw.ne'

lemma intervalIntegrable_E3 {τ ℓ u : ℝ} (hτ : 1 ≤ τ) (hℓ : 3 * τ < ℓ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    IntervalIntegrable (fun w => gfun τ ℓ u I w * etaF τ ℓ w / w) volume (wlo τ ℓ u)
      (Uf τ ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have e : (fun w => gfun τ ℓ u I w * etaF τ ℓ w / w) =
      I.indicator (fun w => gBase τ ℓ u w * etaF τ ℓ w / w) := by
    funext w; by_cases h : w ∈ I <;> simp [gfun_eq, h]
  rw [e]
  exact intervalIntegrable_cut hτ hℓ hI fun w hw =>
    ((gBase_continuousAt τ ℓ u hℓ0 hw).mul (etaF_continuousAt τ ℓ hℓ0 hw)).div
      continuousAt_id hw.ne'

end BSaias

end
