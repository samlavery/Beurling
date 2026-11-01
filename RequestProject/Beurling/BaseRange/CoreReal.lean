module

public import RequestProject.Beurling.BaseRange.Core73b
public import RequestProject.Beurling.Queue6.TNPHyp

/-!
# `Lemma73bCore` from the hypotheses of Lemma 5.20, and for the realised width

* `lemma73bCore_of_tnp` : `Lemma73bCore` from `KR.TNP.Hyp` (HBS, `PaperWidth`, the decision
  order and Corollary 6.3(ii)), the local count `|N_𝒩 - ⌊·⌋| ≤ ε_HBS v` (the conclusion of
  `BModel.hbs_local`) and `H(X₀⁻/2) ≤ κ X₀⁻/2`;
* `Hc_Xm_half_le_kappa` : the last input for the realised width `H_c = H(max(·, X₀))`
  (`log H(X₀) ≤ 0.001 Λ`);
* `Xm_facts` : `X₀/2 ≤ X₀⁻ ≤ X₀`.
-/

@[expose] public section

open Real Finset BeurlingSystem CaplLink

namespace BaseRange

/-- `H(s) ≤ (H(X₀⁻/2)/(X₀⁻/2)) s` on `[X₀⁻/2, ∞)`, from (R_H). -/
lemma ratio_of_RH {H : ℝ → ℝ} {X0m ε θ : ℝ} (hW : KR.PaperWidth H X0m ε θ) {s : ℝ}
    (hs : X0m / 2 ≤ s) : H s ≤ H (X0m / 2) / (X0m / 2) * s := by
  have hX := hW.X0m_pos
  have hy : 0 < X0m / 2 := by linarith
  set w := s / (X0m / 2)
  have hw : 1 ≤ w := by rw [le_div_iff₀ hy]; linarith
  have e : X0m / 2 * w = s := by simp only [w]; field_simp
  have h1 := hW.RH (X0m / 2) w le_rfl hw
  rw [e] at h1
  have h2 : w ^ ε ≤ w := by
    have := Real.rpow_le_rpow_of_exponent_le hw (show ε ≤ 1 by linarith [hW.eps_le])
    rwa [Real.rpow_one] at this
  have hH0 : 0 ≤ H (X0m / 2) := (hW.reg.pos _).le
  calc H s ≤ w ^ ε * H (X0m / 2) := h1
    _ ≤ w * H (X0m / 2) := mul_le_mul_of_nonneg_right h2 hH0
    _ = H (X0m / 2) / (X0m / 2) * s := by rw [← e]; field_simp

/-- **`Lemma73bCore` from the hypotheses of Lemma 5.20** (`KR.TNP.Hyp`), the local count of
`BModel.hbs_local`, and `H(X₀⁻/2)/(X₀⁻/2) ≤ κ`. -/
theorem lemma73bCore_of_tnp {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ}
    {X0m Z η1 η2 ε θ' : ℝ} {ε1 : ℝ → ℝ} (hT : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ')
    {X0 : ℕ} {xmax : ℝ} (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) (hZ : xmax / X0 ≤ Z) (hXZ : X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (hηκ : H (X0m / 2) / (X0m / 2) ≤ Construction.kappaParam X0) :
    Lemma73bCore P tw X0m X0 xmax := by
  have hW := hT.width
  have hX0m := hW.X0m_pos
  refine lemma73bCore_of hT.hbs hX hXm1 hXm2 hZ hXZ hloc H hT.dec_hi hT.dec_lo ?_ hW.small
    hT.count (fun s hs => ratio_of_RH hW hs)
    (div_nonneg (hW.reg.pos _).le (by linarith)) hηκ
  intro y z hy hz
  have := hW.lip y z hy hz
  have h0 := abs_nonneg (y - z)
  have : θ' * |y - z| ≤ 1 / 100 * |y - z| := mul_le_mul_of_nonneg_right hW.theta_le h0
  linarith

section Real

variable {θ : ℝ} {X₀ : ℕ} (hc : BModel.Cond θ X₀)
include hc

/-- `X₀/2 ≤ X₀⁻ ≤ X₀`. -/
lemma Xm_facts : (X₀ : ℝ) / 2 ≤ BModel.Xm X₀ ∧ BModel.Xm X₀ ≤ X₀ := by
  have hs := Queue6.capH_X0_small (hc := hc)
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hc.hX
  have hH0 := Construction.capH_nonneg (X₀ : ℝ) (X₀ : ℝ)
  unfold BModel.Xm
  constructor
  · have : capH X₀ X₀ ≤ X₀ := by
      have := (div_le_iff₀ hX0).mp hs; nlinarith
    linarith
  · linarith

/-- **The realised width**: `H_c(X₀⁻/2)/(X₀⁻/2) ≤ κ` (`H_c(X₀⁻/2) = H(X₀) ≤ X₀^{0.001}`). -/
lemma Hc_Xm_half_le_kappa :
    Queue6.Hc X₀ (BModel.Xm X₀ / 2) / (BModel.Xm X₀ / 2) ≤ Construction.kappaParam X₀ := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hX
  obtain ⟨h1, h2⟩ := Xm_facts hc
  have hlH := Queue6.log_capH_X0 (hc := hc)
  have hH1 : 0 < capH X₀ X₀ := lt_of_lt_of_le one_pos
    (BModel.capH_ge_one hX0.le hX le_rfl)
  have e : Queue6.Hc X₀ (BModel.Xm X₀ / 2) = capH X₀ X₀ := by
    unfold Queue6.Hc; rw [max_eq_right (by linarith)]
  rw [e, div_le_iff₀ (by linarith)]
  -- `H(X₀) ≤ e^{0.001Λ}` and `κ X₀ = e^{0.6033Λ}`
  have hHle : capH X₀ X₀ ≤ Real.exp (0.001 * Real.log X₀) := by
    rw [← Real.exp_log hH1]; exact Real.exp_le_exp.mpr hlH
  have hκX : Construction.kappaParam X₀ * X₀ =
      Real.exp (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀) := by
    rw [kappa_eq_exp hX0, Real.exp_add, Real.exp_log hX0]
  have hbig : 4 * Real.exp (0.001 * Real.log X₀) ≤
      Real.exp (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀) := by
    have e2 : Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀ =
        (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀ - 0.001 * Real.log X₀) +
          0.001 * Real.log X₀ := by ring
    rw [e2, Real.exp_add]
    have := Real.add_one_le_exp
      (Real.log X₀ * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X₀ - 0.001 * Real.log X₀)
    have hp := Real.exp_pos (0.001 * Real.log X₀)
    nlinarith
  have hκ0 := (BModel.kappa_facts hX).1
  nlinarith

end Real

end BaseRange
