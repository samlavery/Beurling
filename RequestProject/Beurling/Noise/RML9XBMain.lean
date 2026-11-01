module

public import RequestProject.Beurling.Noise.RML9XBGamma5

/-!
# Proposition 5.31(iii): the large-height bound for `𝔅(y)`

`xbB_huge` : in the huge range `J = log(y/X₀) ≥ 600Λ⁴`,
`𝔅(y) ≤ (2·10⁵ δ + e^{-61}) Λ/J`, `δ = H(X₀)/X₀`, `Λ = log X₀`.

It is the sum of (α) `½ S(N) ≤ 125 δ(Λ+1.4)/J` (Lemma 5.32, `SD_le_SI`), (β) the pairs with
`w ≤ W₁` (`beta_le`) and (γ′) the pairs with `w > W₁` (`gamma_le`). The paper's constant is
`400δ + e^{-60}` with `τ₀` in place of `Λ`; the Lean bound is coarser in the `δ`-coefficient
(the windows of `𝔹₀`, `𝔹₁`, `𝔹₂` are all taken as `Win`, `|y/n - X₀| ≤ 1.6H(X₀)`), and has
`Λ ≤ τ₀` in place of `τ₀`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.31(iii), first claim** (huge range; Lean constants). -/
theorem xbB_huge {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {ε θ lam0 : ℝ}
    (hP : PaperWidth H X0m ε θ) {X0 : ℕ} (hX0e : X0m = X0 - H X0 / 2)
    (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hy : X0m ≤ y) (hJ : 600 * Real.log X0 ^ 4 ≤ Real.log (y / X0))
    (hZ : 2 * y / X0m ≤ Z) (hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ)))
    (hSR : ShortRecipLow P X0 y) :
    xbB P H tw X0m y X0 θ lam0 ≤
      (200000 * (H X0 / X0) + Real.exp (-61)) * Real.log X0 / Real.log (y / X0) := by
  set δ := H X0 / X0 with hδdef
  set Λ := Real.log X0 with hΛdef
  set J := Real.log (y / X0) with hJdef
  have hXm0 := hP.X0m_pos
  have hHp : 0 < H X0 := by linarith
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  have hHX : H X0 ≤ X0 / 1000 := by rw [div_le_iff₀ hX0] at hδ; linarith
  have hΛ : 100000000 ≤ Λ := hXl.trans (Real.log_le_log hXm0 hXm)
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJ0 : 2000 ≤ J := by nlinarith
  have hJpos : 0 < J := by linarith
  have hy0 : 0 < y := by linarith
  have hN0 : 0 < y / X0 := by positivity
  have hδ0 : Real.exp (-Λ) ≤ δ := by
    rw [hΛdef, Real.exp_neg, Real.exp_log hX0, hδdef]
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hH1 hX0.le
  have hδpos : 0 < δ := by positivity
  -- (α)
  have hα := SD_le_SI (tw := tw) h hΛ ht htv hXm0 hXm hy hJ hδ0 (by linarith) hZ hT hN0
    (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 by norm_num)]) le_rfl
  rw [div_self hN0.ne', Real.log_one, add_zero] at hα
  -- (β), (γ′)
  have hβ := beta_le h hP hX0e hH1 hδ hp2 hXl ht htv hlam hlam1 hy hJ hZ hT (tw := tw)
  have hγ := gamma_le h hP hX0e hδ hp2 hXl ht htv hlam hlam1 hy hZ hSR (tw := tw)
  have hly : J ≤ Real.log y := by
    have : Real.log y = J + Λ := by
      rw [hJdef, hΛdef, ← Real.log_mul hN0.ne' hX0.ne']; congr 1; field_simp
    linarith
  have hγ' : Real.exp (-62) * Λ / Real.log y ≤ Real.exp (-62) * Λ / J :=
    div_le_div_of_nonneg_left (by positivity) hJpos hly
  have hsplit := xbB_le_split (tw := tw) (θ := θ) (lam0 := lam0) hP hX0e hp2
    (by linarith [hP.theta_nonneg])
    hX0 hδ hy0
  rw [← Finset.sum_filter_add_sum_filter_not (Dset P X0m y)
    (fun w => Vl P w ≤ Real.exp 100)] at hsplit
  -- numerics
  have hexp : Real.exp (-Λ) ≤ Real.exp (-70) := Real.exp_le_exp.mpr (by linarith)
  have he62 : 202 * Real.exp (-70) + Real.exp (-62) * Λ ≤ Real.exp (-61) * Λ := by
    have h1 : Real.exp (-70) * Real.exp 8 = Real.exp (-62) := by
      rw [← Real.exp_add]; norm_num
    have h2 : Real.exp (-62) * Real.exp 1 = Real.exp (-61) := by
      rw [← Real.exp_add]; norm_num
    have h8 : 202 ≤ Real.exp 8 := by
      have := Real.exp_one_gt_d9
      rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      calc (202 : ℝ) ≤ 2.7 ^ 8 := by norm_num
        _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have he := Real.exp_one_gt_d9
    have hp70 := Real.exp_pos (-70)
    have hp62 := Real.exp_pos (-62)
    have : 202 * Real.exp (-70) ≤ Real.exp (-62) := by nlinarith
    rw [← h2]
    have hk : 1 ≤ Λ * (Real.exp 1 - 1) := by nlinarith
    have := mul_le_mul_of_nonneg_left hk hp62.le
    nlinarith
  rw [le_div_iff₀ hJpos]
  rw [← hJdef, ← hΛdef] at hα
  have hα' := (le_div_iff₀ hJpos).mp hα
  have hβ' := (le_div_iff₀ hJpos).mp hβ
  have hγ'' := (le_div_iff₀ hJpos).mp (hγ.trans hγ')
  have hsum : xbB P H tw X0m y X0 θ lam0 * J ≤
      1 / 2 * (250 * δ * (Λ + 1.4)) + 202 * (250 * δ * ((Λ + 101.4) * 3.0674 + 9.4091) +
        Real.exp (-Λ)) + Real.exp (-62) * Λ := by
    have := mul_le_mul_of_nonneg_right hsplit hJpos.le
    nlinarith
  have hδΛ : 1 / 2 * (250 * δ * (Λ + 1.4)) + 202 * (250 * δ * ((Λ + 101.4) * 3.0674 + 9.4091))
      ≤ 200000 * δ * Λ := by nlinarith
  nlinarith

end KR.RML9

end
