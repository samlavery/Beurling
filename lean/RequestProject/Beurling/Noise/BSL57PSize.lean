module

public import RequestProject.Beurling.Noise.BSL57RAsm
public import RequestProject.Beurling.Noise.BSLargeRatio
meta import RequestProject.BSCert.AuxCert

/-!
# Lemma 5.7: sizes on the large range

On `LargeRange τ ℓ u` (`τ ≥ 10⁸`, `ℓ ≥ max(10¹⁸, 30τ)`, `2 ≤ u ≤ Ū`):
`λ ≤ 1.5·10⁻⁶`, `α' ≤ 10⁻³` (from `ε(ℓ) ≤ 0.03`), `Λ(u) ≤ 1.001 λ ℓ`, `Λ(Ū) ≤ 1.001 λ ℓ`,
`a'(ℓ,u) ≤ α'`, `1/√ℓ ≤ α'/63244`, and the Dickman bounds `r(u-1) ≥ 1`, `r(u-1) ≥ 4.59` for
`u ≥ 27`, `r(u-1) ≥ 2.19` for `u ≥ 10`, `u r(u) ≥ 2.196`.
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

lemma rLow_26' : (459 / 100 : ℚ) ≤ BSCert.rLow BSCert.auxTable 26 := by native_decide

lemma rLow_9 : (219 / 100 : ℚ) ≤ BSCert.rLow BSCert.auxTable 9 := by native_decide

lemma ratio_ge_459 {v : ℝ} (hv : 26 ≤ v) : 4.59 ≤ Dickman.ratio v := by
  have h := ratio_ge_table (x := 26) (by norm_num) (by exact_mod_cast hv)
  have h2 : ((459 / 100 : ℚ) : ℝ) ≤ ((BSCert.rLow BSCert.auxTable 26 : ℚ) : ℝ) := by
    exact_mod_cast rLow_26'
  push_cast at h2; linarith

lemma ratio_ge_219 {v : ℝ} (hv : 9 ≤ v) : 2.19 ≤ Dickman.ratio v := by
  have h := ratio_ge_table (x := 9) (by norm_num) (by exact_mod_cast hv)
  have h2 : ((219 / 100 : ℚ) : ℝ) ≤ ((BSCert.rLow BSCert.auxTable 9 : ℚ) : ℝ) := by
    exact_mod_cast rLow_9
  push_cast at h2; linarith

lemma LargeRange.lam_le (hR : LargeRange τ ℓ u) : lamL τ ℓ ≤ 0.0000015 := by
  obtain ⟨hτ, hτℓ, hℓ, -, -⟩ := hR
  have he := lemma57Eps τ ℓ hτ hτℓ hℓ
  rw [epsL_eq] at he
  have hα := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  linarith

lemma LargeRange.alpha_le (hR : LargeRange τ ℓ u) : alphaL τ ℓ ≤ 0.001 := by
  obtain ⟨hτ, hτℓ, hℓ, -, -⟩ := hR
  have he := lemma57Eps τ ℓ hτ hτℓ hℓ
  rw [epsL_eq] at he
  have hl := lamL_nonneg (τ := τ) (by linarith : (0 : ℝ) < ℓ)
  have hp : 0 < ℓ ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  linarith

lemma LargeRange.u0_ge (hR : LargeRange τ ℓ u) : 31622 ≤ u0 ℓ := u0_ge_of hR.2.2.1

lemma LargeRange.sqrt_root (hR : LargeRange τ ℓ u) :
    0 ≤ 2 * Real.log (ℓ / τ) + 4 ∧ 2 ≤ √(2 * Real.log (ℓ / τ) + 4) := by
  have hτ := hR.τ_pos
  have hl : 0 ≤ Real.log (ℓ / τ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith [hR.2.1])
  refine ⟨by linarith, ?_⟩
  rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith

lemma LargeRange.U_ge (hR : LargeRange τ ℓ u) : 3 * u0 ℓ ≤ Uf τ ℓ := by
  have h := hR.sqrt_root.2
  have hu := hR.u0_ge
  unfold Uf; nlinarith

lemma LargeRange.u_le (hR : LargeRange τ ℓ u) : u ≤ Uf τ ℓ := hR.2.2.2.2

lemma LargeRange.sqrt_pos (hR : LargeRange τ ℓ u) : 0 < √ℓ := Real.sqrt_pos.mpr hR.ℓ_pos

/-- `a'(ℓ, u) ≤ α'` for `u ≤ Ū`. -/
lemma LargeRange.ap_le (hR : LargeRange τ ℓ u) : aprime ℓ u ≤ alphaL τ ℓ := by
  unfold alphaL aprime
  exact div_le_div_of_nonneg_right (max_le_max (by linarith [hR.u_le]) le_rfl)
    (Real.sqrt_nonneg _)

lemma LargeRange.ap_nonneg (_hR : LargeRange τ ℓ u) : 0 ≤ aprime ℓ u := by
  unfold aprime; positivity

/-- `(Ū - u₀)/√ℓ = α'`. -/
lemma LargeRange.alpha_eq (hR : LargeRange τ ℓ u) :
    alphaL τ ℓ = (Uf τ ℓ - u0 ℓ) / √ℓ := by
  unfold alphaL aprime
  rw [max_eq_left (by linarith [hR.U_ge, hR.u0_ge])]

/-- `1/√ℓ ≤ α'/63244`. -/
lemma LargeRange.inv_sqrt_le (hR : LargeRange τ ℓ u) : 1 / √ℓ ≤ alphaL τ ℓ / 63244 := by
  rw [hR.alpha_eq, div_div, div_le_div_iff₀ hR.sqrt_pos (by have := hR.sqrt_pos; positivity)]
  have h1 := hR.U_ge
  have h2 := hR.u0_ge
  have h3 := hR.sqrt_pos
  have : 63244 ≤ Uf τ ℓ - u0 ℓ := by linarith
  nlinarith

lemma Lam_le_aux {x U : ℝ} (hx : 0 ≤ x) (hxU : x ≤ U) (hU : 31622 ≤ U) :
    Lam x ≤ 1.001 * (U ^ 2 * Real.log (2 + U)) := by
  unfold Lam
  have h1 : (1 + x) ^ 2 ≤ 1.001 * U ^ 2 := by nlinarith
  have h2 : Real.log (2 + x) ≤ Real.log (2 + U) := Real.log_le_log (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul h1 h2 h3 (by positivity)]

/-- `Λ(u) ≤ 1.001 λ ℓ`. -/
lemma LargeRange.Lam_le (hR : LargeRange τ ℓ u) : Lam u ≤ 1.001 * lamL τ ℓ * ℓ := by
  have h := Lam_le_aux (x := u) (by linarith [hR.2.2.2.1]) hR.u_le
    (by linarith [hR.U_ge, hR.u0_ge])
  unfold lamL; rw [mul_assoc, div_mul_cancel₀ _ hR.ℓ_pos.ne']; exact h

/-- `Λ(Ū) ≤ 1.001 λ ℓ`. -/
lemma LargeRange.LamU_le (hR : LargeRange τ ℓ u) :
    Lam (Uf τ ℓ) ≤ 1.001 * lamL τ ℓ * ℓ := by
  have hU := hR.U_ge; have hu0 := hR.u0_ge
  have h := Lam_le_aux (x := Uf τ ℓ) (by linarith) le_rfl (by linarith)
  unfold lamL; rw [mul_assoc, div_mul_cancel₀ _ hR.ℓ_pos.ne']; exact h

lemma LargeRange.r0_ge_one (hR : LargeRange τ ℓ u) : 1 ≤ Dickman.ratio (u - 1) :=
  ratio_ge_one (by linarith [hR.2.2.2.1])

lemma LargeRange.ur_ge (hR : LargeRange τ ℓ u) : 2.196 ≤ u * Dickman.ratio u := by
  have hu := hR.2.2.2.1
  have hr : Real.log 3 ≤ Dickman.ratio u :=
    le_trans ratio_two_ge (Dickman.ratio_monotoneOn (Set.mem_Ici.mpr (by norm_num))
      (Set.mem_Ici.mpr (by linarith)) hu)
  have hl3 : (1.098 : ℝ) ≤ Real.log 3 := by
    have := Real.log_two_gt_d9
    have h3 : Real.log 3 = Real.log 2 + Real.log 1.5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h15 : (0.405 : ℝ) ≤ Real.log 1.5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_bound' (x := (0.405 : ℝ)) (by norm_num) (by norm_num) (n := 4)
        (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    linarith
  nlinarith

end BSaias.Large

end
