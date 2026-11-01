module

public import RequestProject.Beurling.Noise.BSL57Dec
public import RequestProject.Beurling.Noise.BSLarge
public import RequestProject.Beurling.Noise.BSLargeEps

/-!
# Lemma 5.7 (remainder, in ratio form) from the added remainder bounds

* `l57_decomp` : the decomposition (lines 366-376),
  `ℓΣ ≥ c(u) + ℓ s_a - ℓ(ρ₁ + ρ₂ + ρ₃ + ρ₄ + E₃ + T)`, proved (via `M_le`);
* `lemma57Ineq_of_rem` : `Lemma57Ineq` from `Lemma57Rem` (the remainders (a)–(f) added,
  lines 434-498), the proved size of `ε` and slack `s_a`, and the positivity of `c(u)`
  (the final paragraph of the proof, lines 499-502);
* `regionLarge_of_rem` : Step 7(ii) from `Lemma57Rem` alone.
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-- **The decomposition** (proof of Lemma 5.7, lines 366-376):
`ℓΣ ≥ c(u) + ℓ s_a - ℓ(ρ₁ + ρ₂ + ρ₃ + ρ₄ + E₃ + T)`. -/
theorem l57_decomp (hR : LargeRange τ ℓ u) :
    cfun τ ℓ u + ℓ * sA ℓ u - Rsum τ ℓ u ≤ ℓ * Sigma τ ℓ u := by
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hM := mul_le_mul_of_nonneg_left (M_le hR) hℓ0.le
  have hE1 : ℓ * E1term τ ℓ u (paperCut τ ℓ) = ℓ * rho3 τ ℓ u + 2 * Kp * e1 u := by
    unfold rho3; field_simp; ring
  have hE2 : ℓ * E2term τ ℓ u (paperCut τ ℓ) = ℓ * rho4 τ ℓ u + Kp * e2 u := by
    unfold rho4; field_simp; ring
  have ej : ℓ * (11 / ℓ * jA u) = 11 * jA u := by field_simp
  have key : ℓ * Sigma τ ℓ u = ℓ - ℓ * Mterm τ ℓ u (paperCut τ ℓ) -
      ℓ * E1term τ ℓ u (paperCut τ ℓ) - ℓ * E2term τ ℓ u (paperCut τ ℓ) -
      ℓ * E3term τ ℓ u (paperCut τ ℓ) - ℓ * Tterm τ ℓ u := by
    unfold Sigma SigmaGen; ring
  have hR' : Rsum τ ℓ u = ℓ * rho1 τ ℓ u + ℓ * rho2 τ ℓ u + ℓ * rho3 τ ℓ u +
      ℓ * rho4 τ ℓ u + ℓ * E3term τ ℓ u (paperCut τ ℓ) + ℓ * Tterm τ ℓ u := by
    unfold Rsum; ring
  have hc : cfun τ ℓ u = ℓ * PhiBen τ ℓ u + (-(11 * jA u) - 2 * Kp * e1 u - Kp * e2 u) := rfl
  have hM' : ℓ * Mterm τ ℓ u (paperCut τ ℓ) ≤ ℓ - ℓ * PhiBen τ ℓ u + 11 * jA u -
      ℓ * sA ℓ u + ℓ * rho1 τ ℓ u + ℓ * rho2 τ ℓ u := by
    have : ℓ * (1 - PhiBen τ ℓ u + 11 / ℓ * jA u - sA ℓ u + rho1 τ ℓ u + rho2 τ ℓ u) =
        ℓ - ℓ * PhiBen τ ℓ u + ℓ * (11 / ℓ * jA u) - ℓ * sA ℓ u + ℓ * rho1 τ ℓ u +
          ℓ * rho2 τ ℓ u := by ring
    rw [this, ej] at hM
    exact hM
  rw [key, hR', hc]
  linarith

lemma epsL_eq : epsL τ ℓ = 20000 * lamL τ ℓ + 30 * alphaL τ ℓ + ℓ ^ (-(1 / 8 : ℝ)) := by
  unfold epsL lamL alphaL; ring

lemma lamL_nonneg (hℓ : 0 < ℓ) : 0 ≤ lamL τ ℓ := by
  unfold lamL
  have : 0 ≤ Real.log (2 + Uf τ ℓ) := Real.log_nonneg (by linarith [BSaias.Uf_pos (τ := τ) hℓ])
  positivity

lemma alphaL_nonneg : 0 ≤ alphaL τ ℓ := by
  unfold alphaL aprime; positivity

/-- The final algebra of the proof of Lemma 5.7 for `u ≥ 27` (lines 499-502). -/
lemma alg_big {c s R S ε ε1 ε2 I q1 q : ℝ} (hdec : c + s - R ≤ S)
    (hR : R ≤ ε1 * c + ε2 * max s 0 + 2.2 * I + q1) (hε0 : 0 ≤ ε) (hε1 : ε1 ≤ 0.72 * ε)
    (hε2 : ε2 ≤ ε) (hc : 0 ≤ c) (hI : 0 ≤ I) (hq : q1 ≤ q)
    (hneg : s < 0 → -(0.28 * ε * c) ≤ ε * s) :
    (1 - ε) * (c + s) - 60 * I - q ≤ S := by
  have h1 : ε1 * c ≤ 0.72 * ε * c := mul_le_mul_of_nonneg_right hε1 hc
  have h0 : 0 ≤ ε * c := mul_nonneg hε0 hc
  rcases le_or_gt 0 s with hs | hs
  · rw [max_eq_left hs] at hR
    have h2 : ε2 * s ≤ ε * s := mul_le_mul_of_nonneg_right hε2 hs
    nlinarith
  · rw [max_eq_right hs.le] at hR
    have h3 := hneg hs
    nlinarith

/-- The final algebra of the proof of Lemma 5.7 for `2 ≤ u < 27`. -/
lemma alg_small {c s R S ε ε1 q1 q : ℝ} (hdec : c + s - R ≤ S) (hR : R ≤ ε1 * c + q1)
    (hε0 : 0 ≤ ε) (hε1 : ε1 ≤ 0.72 * ε) (hc : 4000 ≤ c) (hs : -0.01 ≤ s) (hq : q1 ≤ q) :
    (1 - ε) * (c + s) - 60 * 0 - q ≤ S := by
  have h1 : ε1 * c ≤ 0.72 * ε * c := mul_le_mul_of_nonneg_right hε1 (by linarith)
  have h2 : 4000 * ε ≤ ε * c := by nlinarith
  have h3 : -0.01 * ε ≤ ε * s := by nlinarith
  nlinarith

/-- `ε s ≥ -0.28 ε c` when `s = ℓ s_a < 0`, `u ≥ 27` (lines 499-501). -/
lemma neg_slack (hR : LargeRange τ ℓ u) (h27 : 27 ≤ u) (hε0 : 0 ≤ epsL τ ℓ)
    (hc : Kp * u ^ 2 * Real.log (1 + u) ≤ cfun τ ℓ u) (hs : ℓ * sA ℓ u < 0) :
    -(0.28 * epsL τ ℓ * cfun τ ℓ u) ≤ epsL τ ℓ * (ℓ * sA ℓ u) := by
  obtain ⟨hs1, hs2⟩ := lemma57Slack τ ℓ u hR
  have hℓ := hR.2.2.1
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hsq : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  have hL3 : 3 ≤ Real.log (1 + u) := log_ge_three (by linarith)
  have hKp : Kp = 2.2 := rfl
  rw [hKp] at hc
  by_cases hbig : u0 ℓ - 2 ≤ u
  · have h1 := hs1 hbig
    have hap : 0 ≤ aprime ℓ u := by unfold aprime; positivity
    have hsl : -(0.54 * √ℓ) ≤ ℓ * sA ℓ u := by
      have e : ℓ * (0.54 / √ℓ) = 0.54 * √ℓ := by
        field_simp; nlinarith [Real.mul_self_sqrt hℓ0.le]
      have h2 : ℓ * (0.67 * aprime ℓ u - 0.54 / √ℓ) ≤ ℓ * sA ℓ u :=
        mul_le_mul_of_nonneg_left h1 hℓ0.le
      nlinarith [mul_nonneg hℓ0.le hap]
    have hu0 := u0_ge hℓ
    have hu2 : 0.99 * √ℓ ≤ u ^ 2 := by
      have hsq2 := u0_sq hℓ0.le
      nlinarith
    have hc' : 6.5 * √ℓ ≤ cfun τ ℓ u := by
      nlinarith [mul_le_mul hu2 hL3 (by norm_num) (sq_nonneg u)]
    have a1 := mul_le_mul_of_nonneg_left hsl hε0
    have a2 := mul_le_mul_of_nonneg_left hc' hε0
    nlinarith [mul_nonneg hε0 hsq.le]
  · push_neg at hbig
    obtain ⟨hsa, -⟩ := hs2 hbig
    have h729 : (729 : ℝ) ≤ u ^ 2 := by nlinarith
    have hc4 : 4000 ≤ cfun τ ℓ u := by
      have : (729 : ℝ) * 3 ≤ u ^ 2 * Real.log (1 + u) :=
        mul_le_mul h729 hL3 (by norm_num) (sq_nonneg u)
      linarith
    have a1 := mul_le_mul_of_nonneg_left hsa hε0
    have a2 := mul_le_mul_of_nonneg_left hc4 hε0
    nlinarith

/-- **Lemma 5.7, main inequality**, from the added remainder bounds (a)–(f). -/
theorem lemma57Ineq_of_rem (hrem : Lemma57Rem) : Lemma57Ineq := by
  intro τ ℓ u hR
  obtain ⟨hτ, hτℓ, hℓ, hu, -⟩ := id hR
  have hℓ0 : 0 < ℓ := hR.ℓ_pos
  have hdec := l57_decomp hR
  obtain ⟨hr27, hrs⟩ := hrem τ ℓ u hR
  have heq := epsL_eq (τ := τ) (ℓ := ℓ)
  have hlam := lamL_nonneg (τ := τ) hℓ0
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hℓ0 _
  have hε0 : 0 ≤ epsL τ ℓ := by rw [heq]; positivity
  have hκ0 : 0 ≤ kappa τ := by unfold kappa; linarith
  have hPB := PhiBen_nonneg (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0
  have hq1 : 1 / ℓ ≤ 900000000000000000 / ℓ :=
    div_le_div_of_nonneg_right (by norm_num) hℓ0.le
  have hq2 : 2500000000000000 / ℓ ≤ 900000000000000000 / ℓ :=
    div_le_div_of_nonneg_right (by norm_num) hℓ0.le
  rcases le_or_gt 27 u with h27 | h27
  · have hc : Kp * u ^ 2 * Real.log (1 + u) ≤ cfun τ ℓ u := by
      have := c0_ge h27
      unfold cfun
      nlinarith [mul_nonneg hℓ0.le hPB]
    have hc0 : 0 ≤ cfun τ ℓ u := by
      have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + u)
      have : 0 ≤ Kp * u ^ 2 * Real.log (1 + u) := by unfold Kp; positivity
      linarith
    have hmax : ℓ * max (sA ℓ u) 0 = max (ℓ * sA ℓ u) 0 := by
      rw [mul_max_of_nonneg _ _ hℓ0.le, mul_zero]
    have hR27 := hr27 h27
    rw [hmax] at hR27
    refine alg_big hdec hR27 hε0 (by rw [heq]; linarith) (by rw [heq]; linarith) hc0
      (by split_ifs <;> norm_num) hq1 (neg_slack hR h27 hε0 hc)
  · have hbig : u < u0 ℓ - 2 := by linarith [u0_ge hℓ]
    rw [if_neg (not_le.mpr hbig)]
    obtain ⟨hsa, -⟩ := (lemma57Slack τ ℓ u hR).2 hbig
    have hc := cfun_ge_small hτ hτℓ hℓ hu h27.le
    exact alg_small hdec (hrs h27) hε0 (by rw [heq]; linarith) (by linarith) hsa hq2

/-- **Step 7(ii)** from the added remainder bounds (a)–(f) of Lemma 5.7. -/
theorem regionLarge_of_rem (hrem : Lemma57Rem) : RegionLarge :=
  regionLarge_of_lemma57 (lemma57Ineq_of_rem hrem) lemma57Eps lemma57Slack

end BSaias.Large

end
