module

public import RequestProject.Beurling.BaseRange.KDiff
public import RequestProject.Beurling.BaseRange.ZeroBelow

/-!
# Lemma 7.3 for the realised objects: (b) and (d)(iii) proved

* `lemma73diii_full` : **Lemma 7.3(d)(iii)** for `ρ_edge`;
* `lemma73Inputs_complete` : **`Lemma73Inputs`** for `μ₀ = mu0R`, `μ₁ = mu1R`, `ρ_edge = rhoEdge`
  with (b) from `lemma73bCore_of` and (d)(iii) from `lemma73diii_full`;
* `lemma73Inputs_tnp` : the same from the hypotheses `KR.TNP.Hyp` of Lemma 5.20;
* `mu0R_zero`, `mu1R_zero` : `μ₀ = μ₁ = 0` on `(-∞, X₀)` (the fields `hμ0`, `hμ1`).

The inputs beyond those of round 2 are the local count `|N_𝒩 - ⌊·⌋| ≤ ε_HBS v` on `[X₀⁻, Z]`
(the conclusion of `BModel.hbs_local`), the decision order and Corollary 6.3(ii) (fields of
`KR.TNP.Hyp`), and `H(X₀⁻/2)/(X₀⁻/2) ≤ κ`.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-- **Lemma 7.3(d)(iii)** for `ρ_edge = (1 + K_pt)⁻¹ μ_edge`. -/
theorem lemma73diii_full {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    {X0 : ℕ} {xmax : ℝ} (h : P.HBS X0m Z η1 η2 ε1) (hX : 10 ^ 8 ≤ Real.log X0)
    (hH : HuxleyFrom X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0)
    (hZ : xmax / X0m ≤ Z) (hXZ : X0m ≤ Z) (ht : ∀ p, p.Prime → 0 < tw p)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (H : ℝ → ℝ)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    {ηH : ℝ} (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη0 : 0 ≤ ηH)
    (hηκ : ηH ≤ Construction.kappaParam X0) :
    Lemma73diii X0 xmax (KR.Sharp.rhoEdge P tw X0m X0) := by
  have hXm0 : 0 < X0m := lt_of_lt_of_le (by norm_num) h.X0m_ge
  have hZ0 : xmax / X0 ≤ Z := by
    rcases le_or_gt 0 xmax with hx | hx
    · exact le_trans (div_le_div_of_nonneg_left hx hXm0 hXm2) hZ
    · have h1 : xmax / X0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le (Nat.cast_nonneg _)
      linarith
  exact lemma73diii_of P h hX hXm1 hXm2 ht hZ (gEdge_bound hX hH)
    (kDiffBound_of h hX hH hXm1 hXm2 hZ0 hXZ hloc H hdhi hdlo hlip hsmall hcount hrat hη0 hηκ)

/-- **The realised inputs of Lemma 7.3**, all parts proved. -/
theorem lemma73Inputs_complete {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : (X0 : ℝ) ≤ Z) {tw : ℕ → ℝ}
    (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p) {xmax : ℝ} (hZ : xmax / X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (H : ℝ → ℝ)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    {ηH : ℝ} (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη0 : 0 ≤ ηH)
    (hηκ : ηH ≤ Construction.kappaParam X0) :
    Lemma73Inputs X0 xmax (mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) := by
  have hXZ' : X0m ≤ Z := hXm2.trans hXZ
  have hXm0 : 0 < X0m := lt_of_lt_of_le (by norm_num) h.X0m_ge
  have hZ0 : xmax / X0 ≤ Z := by
    rcases le_or_gt 0 xmax with hx | hx
    · exact le_trans (div_le_div_of_nonneg_left hx hXm0 hXm2) hZ
    · have h1 : xmax / X0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le (Nat.cast_nonneg _)
      linarith
  exact lemma73Inputs_full P h hX hH hXp hXm1 hXm2 hXZ ht hdec hdec2 hZ0
    (lemma73bCore_of h hX hXm1 hXm2 hZ0 hXZ' hloc H hdhi hdlo hlip hsmall hcount hrat hη0 hηκ)
    (lemma73diii_full h hX hH hXm1 hXm2 hZ hXZ' ht hloc H hdhi hdlo hlip hsmall hcount hrat hη0
      hηκ)

/-- The decision order from `TNP.Hyp`: `t > 0` and `p ≤ 2t(p)` on the prime labels (as
`KR.Chain.dec_R`). -/
lemma tnp_dec {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    {ε θ : ℝ} (h : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) :
    (∀ r, r.Prime → 0 < tw r) ∧ (∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) := by
  have key : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r ∧ 0 < tw r := by
    intro r hr
    have hq : qp (Nat.count Nat.Prime r) = r := exists_qp_eq hr
    set j := Nat.count Nat.Prime r
    have hl : P.labelVal r = P.p j := rfl
    have hp1 := P.one_lt j
    rw [hl, ← hq]
    rcases le_or_gt (X0m / 2) (P.p j) with hj | hj
    · have h1 := h.dec_hi j hj
      have h2 := h.width.small (P.p j) hj
      rw [abs_le] at h1
      constructor <;> linarith [h1.1]
    · rw [h.dec_lo j hj]; constructor <;> linarith
  exact ⟨fun r hr => (key r hr).2, fun r hr => (key r hr).1⟩

/-- **The realised inputs of Lemma 7.3 from `KR.TNP.Hyp`** (the hypotheses of Lemma 5.20). -/
theorem lemma73Inputs_tnp {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ}
    {X0m Z η1 η2 ε θ' : ℝ} {ε1 : ℝ → ℝ} (hT : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ')
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXp : ¬ X0.Prime)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hXZ : (X0 : ℝ) ≤ Z)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    {xmax : ℝ} (hZ : xmax / X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (hηκ : H (X0m / 2) / (X0m / 2) ≤ Construction.kappaParam X0) :
    Lemma73Inputs X0 xmax (mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) := by
  have hW := hT.width
  have hX0m := hW.X0m_pos
  obtain ⟨ht, hdec2⟩ := tnp_dec hT
  refine lemma73Inputs_complete hT.hbs hX hH hXp hXm1 hXm2 hXZ ht hdec hdec2 hZ hloc H
    hT.dec_hi hT.dec_lo ?_ hW.small hT.count (fun s hs => ratio_of_RH hW hs)
    (div_nonneg (hW.reg.pos _).le (by linarith)) hηκ
  intro y z hy hz
  have := hW.lip y z hy hz
  have h0 := abs_nonneg (y - z)
  have : θ' * |y - z| ≤ 1 / 100 * |y - z| := mul_le_mul_of_nonneg_right hW.theta_le h0
  linarith

/-- `μ₀ = 0` on `(-∞, X₀)` (the field `hμ0`). -/
theorem mu0R_zero (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) : ∀ u : ℝ, u < X0 → mu0R P tw X0m X0 u = 0 :=
  fun _ hu => mu0R_zero_below' P tw X0m hX hu

/-- `μ₁ = 0` on `(-∞, X₀)` (the field `hμ1`). -/
theorem mu1R_zero (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) :
    ∀ u : ℝ, u < X0 → KR.Sharp.mu1R P tw X0m X0 u = 0 :=
  fun _ hu => mu1R_zero_below' P tw X0m hu

end BaseRange
