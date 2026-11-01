module

public import RequestProject.Beurling.Noise.BSZ2Integrals

/-!
# Pointwise bounds for `g` in region Z2 (Theorem 5.6, Step 7(iii))

`Z2Hyp τ ℓ u` collects the hypotheses of region Z2 (`τ ≥ 10⁸`, `30τ < ℓ`, `2 ≤ u ≤ U(ℓ)`,
and the two convergence conditions `r(u-1) > γ₁`, `r(u-1) > γ_max` that the certificate checks).
Under it, with `ρ₀ = ρ(u-1)`, `r₀ = r(u-1)`, `s = w - u`:

* `w_lo = u - 1`;
* on `[u-1, u]`: `g(w) ≤ (ρ(w-1)/ρ₀) e^{β_I}(1 - (1 - e^{-α})(u - w))` and
  `g(w) ≤ (ρ(w-1)/ρ₀) e^{β_I}`;
* on `[u, U(ℓ)]`: `ρ(w-1)/ρ₀ ≤ e^{-r₀ s}` ((R3)), and `g(w) ≤ (ρ(w-1)/ρ₀) e^{β_II + γ s}` with
  `γ = γ₁` for `s ≤ 60` and `γ = γ_max` always.
-/

@[expose] public section

open Real Set MeasureTheory

namespace BSaias

open BSCert.Z2 (betaI betaII alpha gamma1 gammaMax)

/-- The hypotheses of region Z2 (and the convergence conditions checked by the certificate). -/
structure Z2Hyp (τ ℓ u : ℝ) : Prop where
  hτ : 100000000 ≤ τ
  hℓ : 30 * τ < ℓ
  hu1 : 2 ≤ u
  hu2 : u ≤ Uf τ ℓ
  hγ1 : gamma1 ℓ u < Dickman.ratio (u - 1)
  hγm : gammaMax ℓ u < Dickman.ratio (u - 1)

namespace Z2Hyp

variable {τ ℓ u : ℝ} (h : Z2Hyp τ ℓ u)
include h

lemma ℓ_pos : 0 < ℓ := by linarith [h.hτ, h.hℓ]
lemma τ_pos : 0 < τ := by linarith [h.hτ]

lemma wlo_eq : wlo τ ℓ u = u - 1 := by
  unfold wlo
  apply max_eq_left
  have hτ := h.τ_pos
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : w1 τ ℓ ≤ 1 := by
    unfold w1; rw [div_le_one (by linarith [h.ℓ_pos])]; linarith
  linarith [h.hu1]

lemma U_le_Ubar : Uf τ ℓ ≤ BSCert.Z2.Ubar ℓ := Uf_le_Ubar h.hτ h.ℓ_pos

lemma r0_ge : 1 ≤ Dickman.ratio (u - 1) := ratio_ge_one h.hu1

lemma gamma1_lt : 0 < Dickman.ratio (u - 1) - gamma1 ℓ u := by linarith [h.hγ1]
lemma gammaMax_lt : 0 < Dickman.ratio (u - 1) - gammaMax ℓ u := by linarith [h.hγm]

lemma gammaMax_nonneg : 0 ≤ gammaMax ℓ u := by
  rw [← slopeZ_gammaMax]; exact slopeZ_nonneg h.ℓ_pos h.hu1 (by
    have := h.U_le_Ubar; have := Uf_pos (τ := τ) h.ℓ_pos; linarith)

lemma alpha_nonneg : 0 ≤ alpha ℓ u := by
  unfold alpha
  have hu := h.hu1
  have hℓ := h.ℓ_pos
  have hk := ku_pos hu
  have : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ 11 / ℓ * u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg _ this
    apply mul_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ BSCert.Z2.ku u * max (u - u0 ℓ - 1 + BSCert.Z2.cu ℓ u) 0 / √ℓ :=
    div_nonneg (mul_nonneg (by linarith) (le_max_right _ _)) (Real.sqrt_nonneg _)
  linarith

set_option linter.unusedSectionVars false in
lemma rho0_pos : 0 < Dickman.rho (u - 1) := Dickman.rho_pos _

lemma gBase_nonneg (w : ℝ) : 0 ≤ gBase τ ℓ u w := by
  unfold gBase
  have := Dickman.rho_pos (w - 1)
  have := h.rho0_pos
  positivity

lemma gfun_le (I : Set ℝ) (w : ℝ) : gfun τ ℓ u I w ≤ gBase τ ℓ u w := by
  rw [gfun_eq]
  exact Set.indicator_le_self' (fun x _ => h.gBase_nonneg x) w

lemma gfun_nonneg (I : Set ℝ) (w : ℝ) : 0 ≤ gfun τ ℓ u I w := by
  rw [gfun_eq]
  exact Set.indicator_nonneg (fun x _ => h.gBase_nonneg x) w

/-- Part I: `g ≤ (ρ(w-1)/ρ₀) e^{β_I} (1 - (1 - e^{-α})(u - w))` on `[u-1, u]`. -/
lemma gBase_partI {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    gBase τ ℓ u w ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (betaI ℓ u) *
      (1 - (1 - Real.exp (-alpha ℓ u)) * (u - w)) := by
  have hD := D_partI (τ := τ) h.hτ h.ℓ_pos h.hu1 hw1 hwu
  have hc : 0 ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) :=
    div_nonneg (Dickman.rho_pos _).le h.rho0_pos.le
  unfold gBase
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc Real.exp (Dfun τ ℓ u w) ≤ Real.exp (betaI ℓ u - alpha ℓ u * (u - w)) :=
        Real.exp_le_exp.mpr hD
    _ = Real.exp (betaI ℓ u) * Real.exp (-(alpha ℓ u * (u - w))) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_neg_mul_le _ _ (by linarith) (by linarith))
        (Real.exp_pos _).le

/-- Part I, cruder: `g ≤ (ρ(w-1)/ρ₀) e^{β_I}` on `[u-1, u]`. -/
lemma gBase_partI' {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    gBase τ ℓ u w ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (betaI ℓ u) := by
  refine (h.gBase_partI hw1 hwu).trans ?_
  have hc : 0 ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (betaI ℓ u) := by
    have := h.rho0_pos; have := Dickman.rho_pos (w - 1); positivity
  have : 0 ≤ (1 - Real.exp (-alpha ℓ u)) * (u - w) := by
    apply mul_nonneg _ (by linarith)
    have : Real.exp (-alpha ℓ u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [h.alpha_nonneg])
    linarith
  nlinarith

/-- (R3): `ρ(w-1)/ρ₀ ≤ e^{-r₀(w-u)}` for `w ≥ u`. -/
lemma rho_ratio_le {w : ℝ} (huw : u ≤ w) :
    Dickman.rho (w - 1) / Dickman.rho (u - 1) ≤
      Real.exp (-(Dickman.ratio (u - 1) * (w - u))) := by
  rw [div_le_iff₀ h.rho0_pos]
  have := Dickman.rho_le_exp (w := u - 1) (t := w - 1) (by linarith [h.hu1]) (by linarith)
  rw [show w - 1 - (u - 1) = w - u by ring] at this
  linarith

/-- Part II: `g ≤ (ρ(w-1)/ρ₀) e^{β_II} e^{γ (w-u)}` given `D(w) ≤ β_II + γ(w - u)`. -/
lemma gBase_partII {w γ : ℝ} (hD : Dfun τ ℓ u w ≤ betaII ℓ u + γ * (w - u)) :
    gBase τ ℓ u w ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (betaII ℓ u) *
      Real.exp (γ * (w - u)) := by
  have hc : 0 ≤ Dickman.rho (w - 1) / Dickman.rho (u - 1) :=
    div_nonneg (Dickman.rho_pos _).le h.rho0_pos.le
  unfold gBase
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD) hc

/-- Part II in the form used for `E₂`, `E₃`: `g ≤ e^{β_II} e^{-(r₀ - γ)(w-u)}`. -/
lemma gBase_partII_exp {w γ : ℝ} (huw : u ≤ w)
    (hD : Dfun τ ℓ u w ≤ betaII ℓ u + γ * (w - u)) :
    gBase τ ℓ u w ≤ Real.exp (betaII ℓ u) *
      Real.exp (-((Dickman.ratio (u - 1) - γ) * (w - u))) := by
  refine (h.gBase_partII hD).trans ?_
  have := h.rho_ratio_le huw
  calc Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (betaII ℓ u) *
        Real.exp (γ * (w - u))
      ≤ Real.exp (-(Dickman.ratio (u - 1) * (w - u))) * Real.exp (betaII ℓ u) *
        Real.exp (γ * (w - u)) := by gcongr
    _ = _ := by rw [mul_comm (Real.exp (-(Dickman.ratio (u - 1) * (w - u)))), mul_assoc,
        ← Real.exp_add]; ring_nf

/-- Part II in the form used for `M`: `g/w ≤ e^{β_II} ρ(w-1)/(w ρ₀) + (e^{β_II}/u)
(e^{-(r₀-γ)(w-u)} - e^{-r₀(w-u)})`, for `γ ≥ 0`. -/
lemma gBase_partII_M {w γ : ℝ} (huw : u ≤ w) (hγ : 0 ≤ γ)
    (hD : Dfun τ ℓ u w ≤ betaII ℓ u + γ * (w - u)) :
    gBase τ ℓ u w / w ≤ Real.exp (betaII ℓ u) / Dickman.rho (u - 1) *
        (Dickman.rho (w - 1) / w) + Real.exp (betaII ℓ u) / u *
        (Real.exp (-((Dickman.ratio (u - 1) - γ) * (w - u))) -
          Real.exp (-(Dickman.ratio (u - 1) * (w - u)))) := by
  have hu0 : 0 < u := by linarith [h.hu1]
  have hw0 : 0 < w := by linarith
  have h1 := h.gBase_partII hD
  set R := Dickman.rho (w - 1) / Dickman.rho (u - 1)
  set E := Real.exp (betaII ℓ u)
  set r0 := Dickman.ratio (u - 1)
  have hR : R ≤ Real.exp (-(r0 * (w - u))) := h.rho_ratio_le huw
  have hR0 : 0 ≤ R := div_nonneg (Dickman.rho_pos _).le h.rho0_pos.le
  have hE : 0 < E := Real.exp_pos _
  have hg1 : 0 ≤ Real.exp (γ * (w - u)) - 1 := by
    have := Real.one_le_exp (mul_nonneg hγ (by linarith : 0 ≤ w - u)); linarith
  -- `R e^{γ s} = R + R (e^{γ s} - 1) ≤ R + e^{-r₀ s}(e^{γ s} - 1)`
  have h2 : R * E * Real.exp (γ * (w - u)) ≤ E * R + E * (Real.exp (-(r0 * (w - u))) *
      (Real.exp (γ * (w - u)) - 1)) := by
    have := mul_le_mul_of_nonneg_right hR hg1
    nlinarith
  have e1 : Real.exp (-(r0 * (w - u))) * (Real.exp (γ * (w - u)) - 1) =
      Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [e1] at h2
  have h3 : gBase τ ℓ u w / w ≤ (E * R + E * (Real.exp (-((r0 - γ) * (w - u))) -
      Real.exp (-(r0 * (w - u))))) / w :=
    div_le_div_of_nonneg_right (h1.trans h2) hw0.le
  refine h3.trans ?_
  have hd : 0 ≤ Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u))) := by
    have := mul_nonneg hR0 hg1
    rw [show Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u))) =
      Real.exp (-(r0 * (w - u))) * (Real.exp (γ * (w - u)) - 1) from e1.symm]
    exact mul_nonneg (Real.exp_pos _).le hg1
  have e2 : (E * R + E * (Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u))))) / w
      = E / Dickman.rho (u - 1) * (Dickman.rho (w - 1) / w) +
        E * (Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u)))) / w := by
    simp only [R]; field_simp
  rw [e2]
  have h4 : E * (Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u)))) / w ≤
      E / u * (Real.exp (-((r0 - γ) * (w - u))) - Real.exp (-(r0 * (w - u)))) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hw0 hu0]
    have := mul_nonneg hE.le hd
    nlinarith
  linarith

end Z2Hyp

end BSaias

end
