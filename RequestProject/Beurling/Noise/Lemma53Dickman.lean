module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Lemma 5.3: the Dickman-function inequalities of the induction step

With `φ(s) = a_V(sL, s) = 12.8 s log(s+2)/L` (`phiV`), and `r = Dickman.ratio`:

* `phiV_sub_ge`: `φ(u) - φ(s) ≥ α(u - s)` on `[u-1, u]`, `α = BSCert.lemVAlpha u L`;
* `rho_le_mul_exp`: `ρ(s) ≤ ρ(u) e^{(u-s) r(u)}` for `s ≤ u`, `u ≥ 1`
  (`ρ(u-t)/ρ(u) ≤ e^{t r(u)}`);
* `integral_rho_mul_ge_half`, `integral_rho_mul_ge_ratio`: the mean of `u - s` under the
  density `∝ ρ(s)` on `[u-1, u]` is at least `1/2`, and at least `1 - 1/r(u-1)` for `u ≥ 2`;
* `integral_rho_exp_le`: the one-step bound
  `∫_{u-1}^u ρ(s) e^{φ(s)} ds ≤ e^{φ(u)} u ρ(u) (1 - (1 - e^{-α}) E_*)`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Dickman

namespace BSaias

/-- `φ(s) = 12.8 s log(s+2)/L` (`= a_V(sL, s)`). -/
noncomputable def phiV (L s : ℝ) : ℝ := 12.8 * s * Real.log (s + 2) / L

/-- `φ'(s) = 12.8 (log(s+2) + s/(s+2))/L`. -/
noncomputable def phiV' (L s : ℝ) : ℝ := 12.8 * (Real.log (s + 2) + s / (s + 2)) / L

lemma hasDerivAt_phiV (L : ℝ) {s : ℝ} (hs : -2 < s) : HasDerivAt (phiV L) (phiV' L s) s := by
  have h2 : s + 2 ≠ 0 := by linarith
  have h := (((hasDerivAt_id s).const_mul 12.8).mul
    ((Real.hasDerivAt_log h2).comp s ((hasDerivAt_id s).add_const 2))).div_const L
  unfold phiV phiV'
  convert! h using 1
  simp only [Function.comp, id]; field_simp

lemma aV_eq_phiV {L u : ℝ} (hu : u ≠ 0) : aV (u * L) u = phiV L u := by
  unfold aV phiV
  field_simp
  ring

lemma phiV'_mono {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hab : a ≤ b) :
    phiV' L a ≤ phiV' L b := by
  unfold phiV'
  apply div_le_div_of_nonneg_right _ hL.le
  have h1 : Real.log (a + 2) ≤ Real.log (b + 2) := Real.log_le_log (by linarith) (by linarith)
  have h2 : a / (a + 2) ≤ b / (b + 2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  linarith

lemma phiV'_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) : 0 ≤ phiV' L s := by
  unfold phiV'
  have : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
  positivity

lemma phiV_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) : 0 ≤ phiV L s := by
  unfold phiV
  have : 0 ≤ Real.log (s + 2) := Real.log_nonneg (by linarith)
  positivity

lemma phiV_mono {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hab : a ≤ b) : phiV L a ≤ phiV L b := by
  have := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x hx => (hasDerivAt_phiV L (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hasDerivAt_phiV L (by linarith [hx.1])).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_phiV L (by linarith [hx.1])).deriv]
      exact phiV'_nonneg hL (by linarith [hx.1]))
  exact this ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- `φ(u) - φ(s) ≥ α(u - s)` for `u - 1 ≤ s ≤ u`, `u ≥ 1`. -/
lemma phiV_sub_ge {L u s : ℝ} (hL : 0 < L) (hu : 1 ≤ u) (hs1 : u - 1 ≤ s) (hs2 : s ≤ u) :
    BSCert.lemVAlpha u L * (u - s) ≤ phiV L u - phiV L s := by
  have hα : BSCert.lemVAlpha u L = phiV' L (u - 1) := by
    unfold BSCert.lemVAlpha phiV'
    congr 1
    · norm_num
      ring_nf
  rw [hα]
  set c := phiV' L (u - 1)
  have hmono := monotoneOn_of_deriv_nonneg (f := fun x => phiV L x - c * x) (convex_Icc s u)
    (fun x hx => ((hasDerivAt_phiV L (by linarith [hx.1])).sub
      ((hasDerivAt_id x).const_mul c)).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact ((hasDerivAt_phiV L (by linarith [hx.1])).sub
        ((hasDerivAt_id x).const_mul c)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      have hd : HasDerivAt (fun x => phiV L x - c * x) (phiV' L x - c * 1) x :=
        (hasDerivAt_phiV L (by linarith [hx.1])).sub ((hasDerivAt_id x).const_mul c)
      rw [hd.deriv]
      have := phiV'_mono hL (by linarith) (show u - 1 ≤ x by linarith [hx.1])
      simp only [mul_one]; linarith)
  have := hmono ⟨le_rfl, hs2⟩ ⟨hs2, le_rfl⟩ hs2
  simp only at this
  linarith

/-- `ρ(s) ≤ ρ(u) e^{(u-s) r(u)}` for `s ≤ u`, `u ≥ 1`. -/
lemma rho_le_mul_exp {u s : ℝ} (hu : 1 ≤ u) (hs : s ≤ u) :
    rho s ≤ rho u * Real.exp ((u - s) * ratio u) := by
  have hr0 : 0 < ratio u := ratio_pos (by linarith)
  -- the case `1 ≤ s`
  have key : ∀ s, 1 ≤ s → s ≤ u → rho s ≤ rho u * Real.exp ((u - s) * ratio u) := by
    intro s hs1 hsu
    set g : ℝ → ℝ := fun x => Real.log (rho x) + ratio u * x
    have hg : MonotoneOn g (Icc s u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s u)
      · apply Continuous.continuousOn
        exact (continuous_rho.log fun x => (rho_pos x).ne').add (continuous_const.mul continuous_id)
      · intro x hx
        rw [interior_Icc] at hx
        exact (((hasDerivAt_rho (by linarith [hx.1])).log (rho_pos x).ne').add
          ((hasDerivAt_id x).const_mul (ratio u))).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hd : HasDerivAt g (-(rho (x - 1) / x) / rho x + ratio u * 1) x :=
          ((hasDerivAt_rho (by linarith [hx.1])).log (rho_pos x).ne').add
            ((hasDerivAt_id x).const_mul (ratio u))
        rw [hd.deriv]
        have hr : ratio x ≤ ratio u :=
          ratio_monotoneOn (mem_Ici.mpr (by linarith [hx.1])) (mem_Ici.mpr hu) hx.2.le
        have e : -(rho (x - 1) / x) / rho x = -ratio x := by
          unfold ratio; rw [neg_div, div_div]
        rw [e]; simp only [mul_one]; linarith
    have h := hg ⟨le_rfl, hsu⟩ ⟨hsu, le_rfl⟩ hsu
    simp only [g] at h
    have hlog : Real.log (rho s) ≤ Real.log (rho u) + (u - s) * ratio u := by nlinarith
    calc rho s = Real.exp (Real.log (rho s)) := (Real.exp_log (rho_pos s)).symm
      _ ≤ Real.exp (Real.log (rho u) + (u - s) * ratio u) := Real.exp_le_exp.mpr hlog
      _ = rho u * Real.exp ((u - s) * ratio u) := by
        rw [Real.exp_add, Real.exp_log (rho_pos u)]
  rcases le_total 1 s with h1 | h1
  · exact key s h1 hs
  · rw [rho_of_le_one h1]
    have := key 1 le_rfl hu
    rw [rho_of_le_one le_rfl] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (rho_pos u).le)
    nlinarith

lemma intervalIntegrable_rho_mul (u : ℝ) :
    IntervalIntegrable (fun s => rho s * (u - s)) volume (u - 1) u :=
  (continuous_rho.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _

/-- `E_* = 1/2`: `∫_{u-1}^u ρ(s)(u - s) ds ≥ (1/2) ∫_{u-1}^u ρ`. -/
lemma integral_rho_mul_ge_half (u : ℝ) :
    (1 / 2) * ∫ s in (u - 1)..u, rho s ≤ ∫ s in (u - 1)..u, rho s * (u - s) := by
  have hc : ∫ s in (u - 1)..u, rho (u - 1 / 2) * (u - 1 / 2 - s) = 0 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegrable_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
    ring
  have hle : ∫ s in (u - 1)..u, rho (u - 1 / 2) * (u - 1 / 2 - s) ≤
      ∫ s in (u - 1)..u, rho s * (u - 1 / 2 - s) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    · exact (continuous_rho.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    · intro s _
      rcases le_total s (u - 1 / 2) with h | h
      · exact mul_le_mul_of_nonneg_right (rho_antitone h) (by linarith)
      · exact mul_le_mul_of_nonpos_right (rho_antitone h) (by linarith)
  have hsplit : ∫ s in (u - 1)..u, rho s * (u - 1 / 2 - s) =
      (∫ s in (u - 1)..u, rho s * (u - s)) - (1 / 2) * ∫ s in (u - 1)..u, rho s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (intervalIntegrable_rho_mul u) ((continuous_rho.intervalIntegrable _ _).const_mul _)]
    congr 1; funext s; ring
  linarith

/-- `E_* = 1 - 1/r(u-1)` for `u ≥ 2`: `∫_{u-1}^u ρ(s)(u-s) ds ≥ (1 - 1/r(u-1)) ∫_{u-1}^u ρ`. -/
lemma integral_rho_mul_ge_ratio {u : ℝ} (hu : 2 ≤ u) :
    (1 - 1 / ratio (u - 1)) * ∫ s in (u - 1)..u, rho s ≤
      ∫ s in (u - 1)..u, rho s * (u - s) := by
  set r0 := ratio (u - 1)
  have hr0 : 0 < r0 := ratio_pos (by linarith)
  -- `φ(s) = ρ(s)(s - u + 1)`, `φ' = ρ(s) - r(s) ρ(s)(s - u + 1) ≤ ρ(s)(1 - r₀(s - u + 1))`
  set φ : ℝ → ℝ := fun s => rho s * (s - u + 1)
  set φ' : ℝ → ℝ := fun s => -(rho (s - 1) / s) * (s - u + 1) + rho s
  have hd : ∀ s ∈ Ioo (u - 1) u, HasDerivAt φ (φ' s) s := by
    intro s hs
    have := (hasDerivAt_rho (show 1 < s by linarith [hs.1])).mul
      (((hasDerivAt_id' s).sub_const u).add_const 1)
    simpa [φ, φ', Pi.mul_def] using this
  have hφ'c : ContinuousOn φ' (Icc (u - 1) u) := by
    apply ContinuousOn.add _ continuous_rho.continuousOn
    apply ContinuousOn.mul _ (by fun_prop)
    apply ContinuousOn.neg
    apply ContinuousOn.div ((continuous_rho.comp (continuous_sub_right 1)).continuousOn)
      continuousOn_id
    intro s hs; simp only [id]; linarith [hs.1]
  have hφ'i : IntervalIntegrable φ' volume (u - 1) u := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le (by linarith)]; exact hφ'c
  have hftc : ∫ s in (u - 1)..u, φ' s = φ u - φ (u - 1) :=
    integral_eq_sub_of_hasDerivAt_of_le (by linarith)
      ((continuous_rho.mul (by fun_prop)).continuousOn) hd hφ'i
  have hφu : φ u - φ (u - 1) = rho u := by simp [φ]
  have hle : ∫ s in (u - 1)..u, φ' s ≤ ∫ s in (u - 1)..u, rho s * (1 - r0 * (s - u + 1)) := by
    apply integral_mono_on_of_le_Ioo (by linarith) hφ'i
      ((continuous_rho.mul (by fun_prop)).intervalIntegrable _ _)
    intro s hs
    have hs1 : 1 < s := by linarith [hs.1]
    have hrs : r0 ≤ ratio s :=
      ratio_monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hs1.le) hs.1.le
    have e : rho (s - 1) / s = ratio s * rho s := by
      unfold ratio; field_simp [(rho_pos s).ne']
    show φ' s ≤ rho s * (1 - r0 * (s - u + 1))
    simp only [φ']
    rw [e]
    have ht : 0 ≤ s - u + 1 := by linarith [hs.1]
    have := rho_pos s
    nlinarith [mul_le_mul_of_nonneg_right hrs (mul_nonneg this.le ht)]
  have hpos : 0 ≤ ∫ s in (u - 1)..u, rho s * (1 - r0 * (s - u + 1)) := by
    have := (rho_pos u).le; linarith
  have hexp : ∫ s in (u - 1)..u, rho s * (1 - r0 * (s - u + 1)) =
      r0 * ((∫ s in (u - 1)..u, rho s * (u - s)) - (1 - 1 / r0) * ∫ s in (u - 1)..u, rho s) := by
    rw [mul_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · congr 1; funext s; field_simp; ring
    · exact ((intervalIntegrable_rho_mul u).const_mul _)
    · exact ((continuous_rho.intervalIntegrable _ _).const_mul _).const_mul _
  rw [hexp] at hpos
  have hX := (mul_nonneg_iff_of_pos_left hr0).mp hpos
  linarith

/-- `E_*(u)`: `max(1/2, 1 - 1/r(u-1))` for `u ≥ 2`, `1/2` otherwise (as in `lemVLHS`). -/
noncomputable def Estar (u : ℝ) : ℝ :=
  if 2 ≤ u then max (1 / 2) (1 - 1 / ratio (u - 1)) else 1 / 2

lemma integral_rho_mul_ge_Estar {u : ℝ} (hu : 1 ≤ u) :
    Estar u * (u * rho u) ≤ ∫ s in (u - 1)..u, rho s * (u - s) := by
  rw [mul_rho_eq_integral hu]
  unfold Estar
  split_ifs with h
  · rcases le_total (1 / 2) (1 - 1 / ratio (u - 1)) with h' | h'
    · rw [max_eq_right h']; exact integral_rho_mul_ge_ratio h
    · rw [max_eq_left h']; exact integral_rho_mul_ge_half u
  · exact integral_rho_mul_ge_half u

lemma Estar_nonneg (u : ℝ) : 0 ≤ Estar u := by
  unfold Estar; split_ifs <;> simp [le_max_iff]

/-- **The one-step bound** of Lemma 5.3:
`∫_{u-1}^u ρ(s) e^{φ(s)} ds ≤ e^{φ(u)} u ρ(u) (1 - (1 - e^{-α}) E_*)`. -/
lemma integral_rho_exp_le {L u : ℝ} (hL : 0 < L) (hu : 1 ≤ u) :
    ∫ s in (u - 1)..u, rho s * Real.exp (phiV L s) ≤
      Real.exp (phiV L u) * (u * rho u) *
        (1 - (1 - Real.exp (-BSCert.lemVAlpha u L)) * Estar u) := by
  set α := BSCert.lemVAlpha u L
  have hα : 0 ≤ α := by
    unfold α BSCert.lemVAlpha
    have : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ (u - 1) / (u + 1) := div_nonneg (by linarith) (by linarith)
    positivity
  set k := 1 - Real.exp (-α)
  have hk : 0 ≤ k := by
    have := Real.exp_le_one_iff.mpr (show -α ≤ 0 by linarith); simp only [k]; linarith
  have hcont : ContinuousOn (fun s => rho s * Real.exp (phiV L s)) (Icc (u - 1) u) :=
    fun s hs => (continuous_rho.continuousAt.mul (Real.continuous_exp.continuousAt.comp
      (hasDerivAt_phiV L (by linarith [hs.1])).continuousAt)).continuousWithinAt
  -- pointwise: `ρ(s) e^{φ(s)} ≤ e^{φ(u)} ρ(s) (1 - k (u - s))`
  have hpt : ∀ s ∈ Icc (u - 1) u,
      rho s * Real.exp (phiV L s) ≤ Real.exp (phiV L u) * (rho s * (1 - k * (u - s))) := by
    intro s hs
    have h1 := phiV_sub_ge hL hu hs.1 hs.2
    have ht0 : 0 ≤ u - s := by linarith [hs.2]
    have ht1 : u - s ≤ 1 := by linarith [hs.1]
    -- convexity: `e^{-α t} ≤ 1 - (1 - e^{-α}) t`
    have hconv : Real.exp (-α * (u - s)) ≤ 1 - k * (u - s) := by
      have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-α)) (by linarith : 0 ≤ 1 - (u - s))
        ht0 (by ring : 1 - (u - s) + (u - s) = 1)
      simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
      simp only [k]
      calc Real.exp (-α * (u - s)) = Real.exp ((u - s) * -α) := by ring_nf
        _ ≤ 1 - (u - s) + (u - s) * Real.exp (-α) := this
        _ = 1 - (1 - Real.exp (-α)) * (u - s) := by ring
    have hexp : Real.exp (phiV L s) ≤ Real.exp (phiV L u) * Real.exp (-α * (u - s)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    have := rho_pos s
    calc rho s * Real.exp (phiV L s) ≤ rho s * (Real.exp (phiV L u) * Real.exp (-α * (u - s))) :=
          mul_le_mul_of_nonneg_left hexp this.le
      _ ≤ rho s * (Real.exp (phiV L u) * (1 - k * (u - s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv (Real.exp_pos _).le) this.le
      _ = _ := by ring
  have h1 : ∫ s in (u - 1)..u, rho s * Real.exp (phiV L s) ≤
      ∫ s in (u - 1)..u, Real.exp (phiV L u) * (rho s * (1 - k * (u - s))) :=
    intervalIntegral.integral_mono_on (by linarith)
      (hcont.intervalIntegrable_of_Icc (by linarith))
      ((continuous_const.mul (continuous_rho.mul (by fun_prop))).intervalIntegrable _ _) hpt
  have h2 : ∫ s in (u - 1)..u, Real.exp (phiV L u) * (rho s * (1 - k * (u - s))) =
      Real.exp (phiV L u) *
        ((∫ s in (u - 1)..u, rho s) - k * ∫ s in (u - 1)..u, rho s * (u - s)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (continuous_rho.intervalIntegrable _ _) ((intervalIntegrable_rho_mul u).const_mul _)]
    congr 1; funext s; ring
  have h3 := integral_rho_mul_ge_Estar hu
  rw [h2, ← mul_rho_eq_integral hu] at h1
  have := Real.exp_pos (phiV L u)
  calc _ ≤ _ := h1
    _ ≤ Real.exp (phiV L u) * (u * rho u - k * (Estar u * (u * rho u))) := by
        apply mul_le_mul_of_nonneg_left _ this.le
        nlinarith
    _ = _ := by ring

end BSaias

end
