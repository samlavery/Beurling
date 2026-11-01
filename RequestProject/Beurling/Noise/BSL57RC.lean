module

public import RequestProject.Beurling.Noise.BSL57RDefs
public import RequestProject.Beurling.Noise.BSL57
public import RequestProject.Beurling.Noise.BSLargeShift

/-!
# Lemma 5.7, remainder (c): `ρ₃ ≤ 0` on the whole range (`remC`)

The paper (lines 452-455) bounds `ρ₃ ≤ E₁^lin·1.0001 D'(u-1)₊` with
`D'(u-1) ≤ σ_sh(u-1)`, which vanishes for `u < u₀ + 0.74`. In fact `D(u-1) ≤ 0` for every
`u ≥ 2` in the range: `D_A(u-1) < 0` by (P1), and for `w = u-1`,
`a(m, w) - a(ℓ, u) ≤ ((v-1)₊² + 0.5004 (v-1)₊ + 0.0628 - v₊²)/(2√ℓ) ≤ 0` (`v = u - u₀`) by the
shift bound `aQ_mOf_le` when `v ≥ 0.74`, while `a(m, w) = 0` when `v ≤ 0.74`. Hence
`e^{D(u-1)} ≤ 1`, `E₁ ≤ E₁^lin` and `ρ₃ ≤ 0`, which gives both parts of (c).
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- `h_A(u, u-1) ≤ 0` (part of (P1)). -/
lemma hA_wlo_nonpos (hu : 2 ≤ u) : hA u (u - 1) ≤ 0 := by
  unfold hA hfun
  have h1 : 0 < u - 1 := by linarith
  have hl1 : 0 ≤ Real.log (2 + (u - 1)) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 + (u - 1)) ≤ Real.log (2 + u) :=
    Real.log_le_log (by linarith) (by linarith)
  have hp : (1 + (u - 1)) ^ 4 ≤ (u - 1) * (1 + u) ^ 3 := by nlinarith [sq_nonneg u]
  rw [sub_nonpos, div_le_iff₀ h1]
  calc (1 + (u - 1)) ^ 4 * Real.log (2 + (u - 1)) ≤ (u - 1) * (1 + u) ^ 3 * Real.log (2 + u) :=
        mul_le_mul hp hl hl1 (by positivity)
    _ = (1 + u) ^ 3 * Real.log (2 + u) * (u - 1) := by ring

/-- `a(m(u-1), u-1) ≤ a(ℓ, u)`. -/
lemma aQ_wlo_le (hℓ : 1000000000000000000 ≤ ℓ) (hu : 2 ≤ u) :
    aQ (mOf ℓ (u - 1)) (u - 1) ≤ aQ ℓ u := by
  have hℓ0 : 0 < ℓ := by linarith
  have h0 : 0 ≤ aQ ℓ u := by unfold aQ; positivity
  rcases le_or_gt (u - 1) (u0 ℓ - 3) with h3 | h3
  · rw [aQ_mOf_eq_zero_low hℓ0 (by linarith) h3]; exact h0
  rcases le_or_gt (u - 1) (u0 ℓ - 0.26) with h26 | h26
  · rw [aQ_mOf_eq_zero_mid hℓ h3.le h26]; exact h0
  refine (aQ_mOf_le hℓ h3.le).trans ?_
  have hsq : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  set v := u - u0 ℓ
  have hv : 0.74 < v := by simp only [v]; linarith
  unfold aQ
  rw [max_eq_left (by linarith : 0 ≤ u - u0 ℓ)]
  rw [show u - 1 - u0 ℓ = v - 1 by simp only [v]; ring, show u - u0 ℓ = v from rfl]
  set d := max (v - 1) 0
  have e : d ^ 2 / (2 * √ℓ) + 0.2502 * d / √ℓ + 0.0314 / √ℓ =
      (d ^ 2 + 0.5004 * d + 0.0628) / (2 * √ℓ) := by field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rcases le_or_gt 1 v with h1 | h1
  · have : d = v - 1 := max_eq_left (by linarith)
    rw [this]; nlinarith
  · have : d = 0 := max_eq_right (by linarith)
    rw [this]; nlinarith

/-- `D(u-1) ≤ 0`. -/
lemma Dfun_wlo_nonpos (hR : LargeRange τ ℓ u) : Dfun τ ℓ u (u - 1) ≤ 0 := by
  obtain ⟨hτ, -, hℓ, hu, -⟩ := hR
  have hℓ0 : 0 < ℓ := by linarith
  have hκ : 0 ≤ kappa τ := by unfold kappa; linarith
  rw [Dfun_eq, Dp_eq hℓ0 (by linarith)]
  have h1 := hA_wlo_nonpos hu
  have h2 := aQ_wlo_le hℓ hu
  have h3 : 0 ≤ kappa τ / ((u - 1) * ℓ) := div_nonneg hκ (mul_pos (by linarith) hℓ0).le
  have h4 : 11 / ℓ * hA u (u - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
  linarith

/-- `ρ₃ ≤ 0` on the range of Lemma 5.7. -/
theorem rho3_nonpos (hR : LargeRange τ ℓ u) : rho3 τ ℓ u ≤ 0 := by
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hu := hR.2.2.2.1
  have hw := hR.wlo_eq
  have hρ1 := Dickman.rho_pos (u - 1)
  have hρ2 := Dickman.rho_pos (u - 1 - 1)
  have hg : gfun τ ℓ u (paperCut τ ℓ) (u - 1) ≤
      Dickman.rho (u - 1 - 1) / Dickman.rho (u - 1) := by
    unfold gfun
    refine (Set.indicator_le_self' (fun x _ => mul_nonneg (div_nonneg (Dickman.rho_pos _).le
      (Dickman.rho_pos _).le) (Real.exp_pos _).le) _).trans ?_
    have := Real.exp_le_one_iff.mpr (Dfun_wlo_nonpos hR)
    calc Dickman.rho (u - 1 - 1) / Dickman.rho (u - 1) * Real.exp (Dfun τ ℓ u (u - 1))
        ≤ Dickman.rho (u - 1 - 1) / Dickman.rho (u - 1) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  unfold rho3 E1term e1
  rw [hw, sub_nonpos]
  have hK : 0 ≤ 2 * Kp * (1 + (u - 1)) ^ 2 := by unfold Kp; positivity
  have h1 : 0 < (u - 1) * ℓ := mul_pos (by linarith) hℓ0
  calc 2 * Kp * (1 + (u - 1)) ^ 2 * gfun τ ℓ u (paperCut τ ℓ) (u - 1) / ((u - 1) * ℓ)
      ≤ 2 * Kp * (1 + (u - 1)) ^ 2 * (Dickman.rho (u - 1 - 1) / Dickman.rho (u - 1)) /
          ((u - 1) * ℓ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hK) h1.le
    _ = 2 * Kp * ((1 + (u - 1)) ^ 2 * Dickman.rho (u - 1 - 1) /
          ((u - 1) * Dickman.rho (u - 1))) / ℓ := by
        field_simp

/-- **Remainder (c)** (lines 452-455). -/
theorem remC : RemC := by
  intro τ ℓ u hR
  have h := rho3_nonpos hR
  refine ⟨fun _ => h, fun _ => ?_⟩
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hX : 0 ≤ Xu u := by
    unfold Xu Kp
    have := Real.log_nonneg (by linarith [hR.2.2.2.1] : (1 : ℝ) ≤ 1 + u); positivity
  have := mul_nonpos_of_nonneg_of_nonpos hℓ0.le h
  have : 0 ≤ 0.72 * alphaL τ ℓ * Xu u := by positivity
  linarith

end BSaias.Large

end
