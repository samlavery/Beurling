module

public import RequestProject.Beurling.Noise.BSLargePos

/-!
# Theorem 5.6, Step 7(ii): `Σ(ℓ, u) ≥ 0` for `ℓ ≥ 10¹⁸` (`RegionLarge`)

`regionLarge_of_lemma57`: Lemma 5.7 (its three parts `Lemma57Ineq`, `Lemma57Eps`,
`Lemma57Slack`, BSLargeDefs.lean) implies `RegionLarge`. The positivity of `c(u)` that the paper
proves after Lemma 5.7 (04c-saias.tex, lines 505-536) is proved here (BSLargePos.lean), with
`BSCert.cA_certificate_dickman` on `[27, 4·10⁵]`:

* `u ≥ 27`: `c(u) ≥ c₀(u) ≥ K'u² log(1+u)`;
* `2 ≤ u < 27`: `c(u) ≥ 10⁶` (`Φ`-dominance).

The assembly is the paper's (line 534): `c(u) + ℓ s_a ≥ 0.97 c(u) > 0` by the bounds on `s_a`,
and then `ℓΣ ≥ 0.97 (c(u) + ℓs_a) - 60·1[u ≥ u₀ - 2] - 0.9 > 0`. We only use the crude
`c(u) ≥ 6.5 √ℓ` for `u ≥ u₀ - 2` (the paper has `22.7 √ℓ`).
-/

@[expose] public section

open Real

namespace BSaias.Large

lemma u0_ge {ℓ : ℝ} (hℓ : 1000000000000000000 ≤ ℓ) : 31622 ≤ u0 ℓ := by
  show 31622 ≤ √(√ℓ)
  have h1 : 1000000000 ≤ √ℓ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

lemma u0_sq {ℓ : ℝ} (_hℓ : 0 ≤ ℓ) : u0 ℓ ^ 2 = √ℓ := by
  show √(√ℓ) ^ 2 = √ℓ
  exact Real.sq_sqrt (Real.sqrt_nonneg ℓ)

lemma log_ge_three {x : ℝ} (hx : 21 ≤ x) : 3 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 3
  norm_num at this; linarith

/-- **Step 7(ii) of the proof of Theorem 5.6** from Lemma 5.7: `Σ(ℓ, u) ≥ 0` for `τ ≥ 10⁸`,
`ℓ > 30τ`, `ℓ ≥ 10¹⁸`, `2 ≤ u ≤ U(ℓ)`. -/
theorem regionLarge_of_lemma57 (h57 : Lemma57Ineq) (heps : Lemma57Eps) (hsl : Lemma57Slack) :
    RegionLarge := by
  intro τ ℓ u hτ hτℓ hℓ hu hU
  have hR : LargeRange τ ℓ u := ⟨hτ, hτℓ, hℓ, hu, hU⟩
  have hℓ0 : 0 < ℓ := by linarith
  have hκ0 : 0 ≤ kappa τ := by unfold kappa; linarith
  have hmain := h57 τ ℓ u hR
  have he := heps τ ℓ hτ hτℓ hℓ
  obtain ⟨hs1, hs2⟩ := hsl τ ℓ u hR
  have hu0 := u0_ge hℓ
  have hsq : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  have hsqsq : √ℓ * √ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
  have hsqℓ : 1000000000 ≤ √ℓ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hfrac : 900000000000000000 / ℓ ≤ 0.9 := by
    rw [div_le_iff₀ hℓ0]; linarith
  have hPB := PhiBen_nonneg (τ := τ) (ℓ := ℓ) hu hκ0 hℓ0
  -- `c ≥ c₀ ≥ K'u² log(1+u)` for `u ≥ 27`
  have hc27 : 27 ≤ u → Kp * u ^ 2 * Real.log (1 + u) ≤ cfun τ ℓ u := by
    intro h27
    have := c0_ge h27
    unfold cfun
    nlinarith [mul_nonneg hℓ0.le hPB]
  have hKp : Kp = 2.2 := rfl
  suffices h : 0 < ℓ * Sigma τ ℓ u by
    exact (pos_of_mul_pos_right h hℓ0.le).le
  by_cases hbig : u0 ℓ - 2 ≤ u
  · rw [if_pos hbig] at hmain
    have h27 : 27 ≤ u := by linarith
    have hc := hc27 h27
    have hL3 : 3 ≤ Real.log (1 + u) := log_ge_three (by linarith)
    have hu2 : 0.99 * √ℓ ≤ u ^ 2 := by
      have hsq2 := u0_sq hℓ0.le
      nlinarith
    have hc' : 6.5 * √ℓ ≤ cfun τ ℓ u := by
      rw [hKp] at hc
      nlinarith [mul_le_mul hu2 hL3 (by norm_num) (sq_nonneg u)]
    have hap : 0 ≤ aprime ℓ u := by unfold aprime; positivity
    have hsa : -(0.54 * √ℓ) ≤ ℓ * sA ℓ u := by
      have h1 := hs1 hbig
      have e : ℓ * (0.54 / √ℓ) = 0.54 * √ℓ := by
        field_simp; nlinarith
      have h2 : ℓ * (0.67 * aprime ℓ u - 0.54 / √ℓ) ≤ ℓ * sA ℓ u :=
        mul_le_mul_of_nonneg_left h1 hℓ0.le
      nlinarith [mul_nonneg hℓ0.le hap]
    have hX : 5.9 * √ℓ ≤ cfun τ ℓ u + ℓ * sA ℓ u := by linarith
    have hX0 : 0 ≤ cfun τ ℓ u + ℓ * sA ℓ u := by linarith
    have : 0.97 * (cfun τ ℓ u + ℓ * sA ℓ u) ≤ (1 - epsL τ ℓ) * (cfun τ ℓ u + ℓ * sA ℓ u) :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    nlinarith
  · rw [if_neg hbig] at hmain
    push_neg at hbig
    obtain ⟨hsa, -⟩ := hs2 hbig
    have hc : 4000 ≤ cfun τ ℓ u := by
      rcases le_or_gt 27 u with h27 | h27
      · have hc := hc27 h27
        have hL3 : 3 ≤ Real.log (1 + u) := log_ge_three (by linarith)
        rw [hKp] at hc
        have h729 : (729 : ℝ) ≤ u ^ 2 := by nlinarith
        have : (729 : ℝ) * 3 ≤ u ^ 2 * Real.log (1 + u) :=
          mul_le_mul h729 hL3 (by norm_num) (sq_nonneg u)
        linarith
      · have := cfun_ge_small hτ hτℓ hℓ hu h27.le
        linarith
    have hX0 : 0 ≤ cfun τ ℓ u + ℓ * sA ℓ u := by linarith
    have : 0.97 * (cfun τ ℓ u + ℓ * sA ℓ u) ≤ (1 - epsL τ ℓ) * (cfun τ ℓ u + ℓ * sA ℓ u) :=
      mul_le_mul_of_nonneg_right (by linarith) hX0
    simp only [mul_zero, sub_zero] at hmain
    have hX : 3999 ≤ cfun τ ℓ u + ℓ * sA ℓ u := by linarith only [hc, hsa]
    generalize Sigma τ ℓ u = S at hmain ⊢
    generalize (1 - epsL τ ℓ) * (cfun τ ℓ u + ℓ * sA ℓ u) = W at hmain this
    generalize cfun τ ℓ u + ℓ * sA ℓ u = X at this hX0 hX
    have hW : 3879 ≤ W := by linarith only [this, hX]
    generalize (900000000000000000 : ℝ) / ℓ = q at hmain hfrac
    have h1 : (3878 : ℝ) ≤ W - q := by linarith only [hW, hfrac]
    have h2 := h1.trans hmain
    have h3 : (0:ℝ) < 3878 := by norm_num
    exact lt_of_lt_of_le h3 h2

end BSaias.Large

end
