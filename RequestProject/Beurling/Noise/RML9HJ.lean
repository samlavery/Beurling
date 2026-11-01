module

public import RequestProject.Beurling.Noise.RML9XBMain
public import RequestProject.Beurling.Noise.RML6Bridge
public import RequestProject.Beurling.Noise.RML6BridgeNum
public import RequestProject.Beurling.Noise.TauNearLocMain

/-!
# Round 9: the input `hj` of `KR.RML6.G1BInputs` (Proposition 5.31(iii))

* `cne_le` : `4.3 C_N E_θ ≤ e^{-178}` for `E_θ = ∑_v log(2v) s_θ(v)` over the scales
  `dyScales X₀ y N`, by Lemma 5.20 localized (`KR.TNP.thetaBlk_sum_loc`:
  `E_θ ≤ 2493700 Φ₃(X₀⁻/2)`), `Φ₃(X₀⁻/2) ≤ e^{-200}` (`KR.WidthReal.Phi_tiny`, under the width
  input `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`) and `C_N ≤ 158` (`KR.Chain.CNc_bounds`). The paper's
  `4.3 C_N E_θ ≤ e^{-0.99Λ}` (eq. (tau-term-bound)) needs a sharper width input than this one
  (`H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}` only gives `Φ₃ ≈ X₀^{-7/8}`); `e^{-178}` suffices for `hj`.
* `hj_full` : `jXat … y ≤ e^{-59}` in the huge range, via `KR.RML8E.hj_of_range` with
  `B := 𝔅(y) + 4.3 C_N E_θ/log y ≤ e^{-60} Λ/J` (`xbB_huge`, `cne_le`), `τ₀ := Λ`, `δ := 0`,
  `CNE := 0`.
* `hj_def` : the same for the supremum `jXdef` over the window `W_x`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7 KR.Chain

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

lemma exp22_ge : (3.5e9 : ℝ) ≤ Real.exp 22 := by
  have h := Real.exp_one_gt_d9
  rw [show (22 : ℝ) = (22 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  calc (3.5e9 : ℝ) ≤ 2.718 ^ 22 := by norm_num
    _ ≤ Real.exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) (by linarith) 22

/-- **`4.3 C_N E_θ ≤ e^{-178}`** (Lemma 5.20 localized, at the scales `dyScales X₀ y N`). -/
theorem cne_le (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 : ℕ} {y : ℝ}
    (hΛ : 100000000 ≤ Real.log X0) {N K : ℕ} (hZ0 : 2500 ≤ Z) (hZ2 : 18 * y ≤ Z ^ 2)
    (hK : ∀ v ∈ TNP.dyScales (X0 : ℝ) y N, √(2 * v) ≤ TNP.Pk X0m K) :
    4.3 * CNc (X0 : ℝ) * ∑ v ∈ TNP.dyScales (X0 : ℝ) y N,
      Real.log (2 * v) * TNP.sTheta P H X0m K v ≤ Real.exp (-178) := by
  have hX0 : (0 : ℝ) < X0 := by
    by_contra hc; push_neg at hc
    have : (X0 : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hX4 : (4 : ℝ) ≤ X0 := by
    by_contra hc; push_neg at hc
    have : Real.log X0 < Real.log 4 := Real.log_lt_log hX0 hc
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith
  have hE := (TNP.thetaBlk_sum_loc h (TNP.dyScales_sep hX0)
    (fun v hv => TNP.dyScales_ge hX4 hv) hZ0
    (fun v hv => by linarith [TNP.dyScales_le hv]) hK).2
  have hΦ := KR.WidthReal.Phi_tiny h hHw (a := 3) le_rfl
  obtain ⟨hC0, hC⟩ := CNc_bounds hΛ
  set S := ∑ v ∈ TNP.dyScales (X0 : ℝ) y N, Real.log (2 * v) * TNP.sTheta P H X0m K v
  have hS : S ≤ 2493700 * Real.exp (-200) := hE.trans (by linarith)
  have he : 4.3 * 158 * (2493700 * Real.exp (-200)) ≤ Real.exp (-178) := by
    have e : Real.exp (-178) = Real.exp 22 * Real.exp (-200) := by
      rw [← Real.exp_add]; norm_num
    rw [e]
    have := exp22_ge
    have hp := Real.exp_pos (-200)
    nlinarith
  rcases le_total 0 S with h0 | h0
  · calc 4.3 * CNc (X0 : ℝ) * S ≤ 4.3 * 158 * (2493700 * Real.exp (-200)) := by
          apply mul_le_mul (by linarith) hS h0 (by norm_num)
      _ ≤ _ := he
  · have : 4.3 * CNc (X0 : ℝ) * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    linarith [Real.exp_pos (-178)]

/-- The start-dependent inputs of `hj` at a start `y` (huge range), with owners:
the range `X₀^{1/100} < log y` (Proposition 5.31(iii)), the horizon `2y/X₀⁻ ≤ Z`, `18y ≤ Z²`
(Model, `Good(<y)`), Theorem 5.24 at `2(y/X₀)^{0.55}` (Model / LocalPNT), Lemma 5.29 on
`Good(<y)` (`ShortRecip`, Queue6), and the scale index `K` with `√(2v) ≤ P_K` on the scales
(the choice `NK` of `jXdef`). -/
structure HjAt (P : BeurlingSystem) (X0m Z : ℝ) (X0 : ℕ) (N K : ℕ) (y : ℝ) : Prop where
  hy0 : 0 < y
  hy : (X0 : ℝ) ^ (1 / 100 : ℝ) < Real.log y
  hZ : 2 * y / X0m ≤ Z
  hZ2 : 18 * y ≤ Z ^ 2
  hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ))
  hSR : ShortRecipLow P X0 y
  hK : ∀ v ∈ TNP.dyScales (X0 : ℝ) y N, √(2 * v) ≤ TNP.Pk X0m K

set_option maxHeartbeats 1000000 in
/-- **`hj` of `KR.RML6.G1BInputs`** (Proposition 5.31(iii), huge range):
`jXat … y = log y · j₀ (𝔅(y) + 4.3 C_N E_θ/log y) ≤ e^{-59}`, via `KR.RML8E.hj_of_range`.
Inputs (owners): `TNP.Hyp` (the standing hypotheses of §5), `X₀⁻ = X₀ - H(X₀)/2`,
`1 ≤ H(X₀)`, `H(X₀)/X₀ ≤ 10⁻³`, `2·10⁵ H(X₀)/X₀ ≤ e^{-61}` (Model: `capH_ge_one`,
`capH_le_rpow`), `p_j ≥ 2`, `1 + 2θ ≤ λ₀ ≤ 1.001`, `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`
(`KR.WidthReal.Hc_Xm_half_le`), `0 ≤ j₀ ≤ 1.0001/Λ` (BaseRange: `jzX_le`), `2500 ≤ Z`, and
the start-dependent `HjAt`. -/
theorem hj_full (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℕ} {lam0 j0 y : ℝ} {N K : ℕ}
    (hX0e : X0m = X0 - H X0 / 2) (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000)
    (hδs : 200000 * (H X0 / X0) ≤ Real.exp (-61)) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hjz : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z) (hA : HjAt P X0m Z X0 N K y) :
    BModel.jXat P H tw X0m X0 θ lam0 j0 N K y ≤ Real.exp (-59) := by
  have hP := h.width
  have hXm0 := hP.X0m_pos
  have hHp : 0 < H X0 := by linarith
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  set Λ := Real.log X0 with hΛdef
  have hΛ : 100000000 ≤ Λ := h.hXm.trans (Real.log_le_log hXm0 hXm)
  have hr : (X0 : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Λ / 100) := by
    rw [Real.rpow_def_of_pos hX0, hΛdef]; ring_nf
  have hy' := hA.hy
  rw [hr] at hy'
  have hJ' := KR.RML8E.huge_of_logy hΛ hy'.le
  have hy0 := hA.hy0
  have hJe : Real.log (y / X0) = Real.log y - Λ := Real.log_div hy0.ne' hX0.ne'
  have hJ : 600 * Λ ^ 4 ≤ Real.log (y / X0) := by rw [hJe]; exact hJ'
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJpos : 0 < Real.log (y / X0) := by nlinarith
  have hyX : X0m ≤ y := by
    have : Λ ≤ Real.log y := by nlinarith
    have : (X0 : ℝ) ≤ y := by
      rw [← Real.exp_log hX0, ← Real.exp_log hy0]; exact Real.exp_le_exp.mpr this
    linarith
  have hly : Real.log (y / X0) ≤ Real.log y := by rw [hJe]; linarith
  -- `𝔅(y)` and `4.3 C_N E_θ`
  have hB := xbB_huge h.hbs hP hX0e hH1 hδ hp2 h.hXm ht htv hlam hlam1 hyX hJ hA.hZ hA.hT
    hA.hSR (tw := tw)
  have hE := cne_le h hHw hΛ hZ0 hA.hZ2 hA.hK (X0 := X0)
  set J := Real.log (y / X0) with hJdef
  set E := 4.3 * CNc (X0 : ℝ) * ∑ v ∈ TNP.dyScales (X0 : ℝ) y N,
    Real.log (2 * v) * TNP.sTheta P H X0m K v with hEdef
  have hlyp : 0 < Real.log y := by linarith
  have hE' : E / Real.log y ≤ Real.exp (-178) * Λ / J := by
    rw [div_le_div_iff₀ hlyp hJpos]
    have h1 : E * J ≤ Real.exp (-178) * J := mul_le_mul_of_nonneg_right hE hJpos.le
    have h2 : Real.exp (-178) * J ≤ Real.exp (-178) * Λ * Real.log y := by
      have h3 : J ≤ Λ * Real.log y := by nlinarith
      have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-178)).le
      linarith
    linarith
  have hsum : xbB P H tw X0m y X0 θ lam0 + E / Real.log y ≤
      (400 * 0 + Real.exp (-60)) * Λ / (Real.log y - Real.log X0) := by
    rw [← hΛdef, ← hJe]
    have hc : (200000 * (H X0 / X0) + Real.exp (-61)) * Λ / J + Real.exp (-178) * Λ / J ≤
        (400 * 0 + Real.exp (-60)) * Λ / J := by
      rw [← add_div, div_le_div_iff_of_pos_right hJpos]
      have e1 : Real.exp (-60) = Real.exp (-61) * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have e2 : Real.exp (-178) ≤ Real.exp (-61) * (1 / 2) := by
        have : Real.exp (-178) * Real.exp 117 = Real.exp (-61) := by
          rw [← Real.exp_add]; norm_num
        have h117 : 2 ≤ Real.exp 117 := by
          have := Real.add_one_le_exp (117 : ℝ); linarith
        have := Real.exp_pos (-178)
        nlinarith
      have he := Real.exp_one_gt_d9
      have hp := Real.exp_pos (-61)
      have hΛ0 : 0 ≤ Λ := by linarith
      rw [e1]
      have h4 := mul_le_mul_of_nonneg_left he.le hp.le
      have h5 : 200000 * (H X0 / X0) + Real.exp (-61) + Real.exp (-178) ≤
          400 * 0 + Real.exp (-61) * Real.exp 1 := by linarith
      have := mul_le_mul_of_nonneg_right h5 hΛ0
      linarith
    linarith
  have hfin := KR.RML8E.hj_of_range (τ0 := Λ) (δ := 0) (CNE := 0) (jz := j0) hΛ hA.hy
    (by linarith) (by linarith) hj0 hjz le_rfl (by norm_num; positivity) hsum le_rfl
    (by rw [← hΛdef]; positivity)
  unfold BModel.jXat
  rw [zero_div, add_zero] at hfin
  have e : j0 * (xbB P H tw X0m y X0 θ lam0 + E / Real.log y) * Real.log y =
      Real.log y * j0 * (xbB P H tw X0m y X0 θ lam0 + E / Real.log y) := by ring
  rw [hEdef] at e
  rw [e]
  exact hfin

/-- **`hj` for `j_{X₀}(x)`** (eq. (jX0)): the supremum `jXdef` over the window `W_x`, when every
start of the window satisfies `HjAt` at the chosen scale indices `NK y`. -/
theorem hj_def (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℕ} {lam0 j0 x : ℝ}
    {NK : ℝ → ℕ × ℕ} (hX0e : X0m = X0 - H X0 / 2) (hH1 : 1 ≤ H X0)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hδs : 200000 * (H X0 / X0) ≤ Real.exp (-61))
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hjz : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z)
    (hA : ∀ y, InW (H x) x y → HjAt P X0m Z X0 (NK y).1 (NK y).2 y) :
    BModel.jXdef P H tw X0m X0 θ lam0 j0 NK x ≤ Real.exp (-59) := by
  unfold BModel.jXdef
  exact Real.iSup_le (fun y => hj_full h hX0e hH1 hδ hδs hp2 ht htv hlam hlam1 hHw hj0 hjz hZ0
    (hA y.1 y.2)) (Real.exp_pos _).le

end KR.RML9

end
