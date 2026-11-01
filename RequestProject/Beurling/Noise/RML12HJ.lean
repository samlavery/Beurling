module

public import RequestProject.Beurling.Noise.RML12MidB

/-!
# Proposition 5.31(ii), second claim, and `j_{X₀}` on `[X₀^{1.01}, b]`

* `hj_mid_at` : in the middle range `e^{0.01Λ}/2 ≤ N = y/X₀`, `log N ≤ 600Λ⁴`,
  `j_{X₀}` at the start `y` is `≤ e^{-59}` (`xbB_mid`, `cne_le`, `j₀ ≤ 1.0001/Λ`,
  `H(X₀) ≤ X₀^{1/8}`). The paper's (ii) gives `e^{-0.0009Λ}`; `e^{-59}` is what is used.
* `hj_huge_at` : in the huge range `log N ≥ 600Λ⁴` the same bound (`xbB_huge`, `cne_le`),
  without the condition `log y > X₀^{1/100}` of `RML9.hj_full`.
* `hj_all_le` : for every `t ∈ [X₀^{1.01}, b]`, `j_{X₀}(t) = jXdef … t ≤ e^{-59}`, when every
  start `y ∈ W_t` satisfies `HjAtM` (the start-dependent inputs).

Heights: at a start `y ∈ W_t`, `t ≤ b`, the quantities read are the levels of `y` (values
`≤ 2y/X₀⁻`), Lemma 5.29 at heights `M ≤ y/X₀` (`ShortRecip`), Theorem 5.24 at `2(y/X₀)^{0.55}`
(huge range only) and the (H_BS) horizons `2y/X₀⁻ ≤ Z`, `18y ≤ Z²`; all are far below `b`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML12

open KR.RML9 KR.XB7 KR.Chain

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-! ## Numerics -/

lemma qrt_ge {L : ℝ} (hL : 100000000 ≤ L) : 100 ≤ L ^ (1 / 4 : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have h4 : (L ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  by_contra hc; push_neg at hc
  have h0 : 0 ≤ L ^ (1 / 4 : ℝ) := Real.rpow_nonneg hL0 _
  have : (L ^ (1 / 4 : ℝ)) ^ (4 : ℕ) < 100 ^ 4 := pow_lt_pow_left₀ hc h0 (by norm_num)
  rw [h4] at this; norm_num at this; linarith

lemma cube_le_exp {L : ℝ} (hL : 100000000 ≤ L) : L ^ 3 ≤ Real.exp (0.000012 * L) := by
  have hL0 : 0 < L := by linarith
  have hlog := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 4 by norm_num)
  set u := L ^ (1 / 4 : ℝ)
  have hu := qrt_ge hL
  have h4 : u ^ (4 : ℕ) = L := by
    simp only [u]; rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hul : 1000000 * u ≤ L := by
    rw [← h4]; nlinarith [pow_le_pow_left₀ (by norm_num) hu 3]
  calc L ^ 3 = Real.exp (3 * Real.log L) := by
        rw [show (3 : ℝ) * Real.log L = Real.log (L ^ 3) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]
    _ ≤ Real.exp (0.000012 * L) := by
        apply Real.exp_le_exp.mpr
        have : Real.log L ≤ 4 * u := by
          have := hlog; rw [div_eq_mul_inv] at this; norm_num at this; linarith
        nlinarith

lemma poly_exp_small {L c C : ℝ} (hL : 100000000 ≤ L) (hc : 0.0019 ≤ c) (_hC0 : 0 ≤ C)
    (hC : C ≤ Real.exp 40) : C * L ^ 3 * Real.exp (-(c * L)) ≤ Real.exp (-62) := by
  have h3 := cube_le_exp hL
  have hL3 : 0 ≤ L ^ 3 := by positivity
  calc C * L ^ 3 * Real.exp (-(c * L))
      ≤ Real.exp 40 * Real.exp (0.000012 * L) * Real.exp (-(c * L)) := by
        gcongr
    _ = Real.exp (40 + 0.000012 * L - c * L) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-62) := Real.exp_le_exp.mpr (by nlinarith)

lemma exp_20_5_ge : (15000000 : ℝ) ≤ Real.exp 20.5 := by
  have h := Real.exp_one_gt_d9
  have h20 : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp 20 ≤ Real.exp 20.5 := Real.exp_le_exp.mpr (by norm_num)
  have : (2.7 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) (by linarith) 20
  norm_num at this
  linarith

/-! ## The two ranges at a start `y` -/

/-- The start-dependent inputs of `j_{X₀}` at a start `y` (any range): the (H_BS) horizons
`2y/X₀⁻ ≤ Z`, `18y ≤ Z²` (Model), Theorem 5.24 at `2(y/X₀)^{0.55}` (Model / LocalPNT; used in the
huge range), Lemma 5.29 for `P` up to `y` (`ShortRecip`, Queue6), and the scale index `K` with
`√(2v) ≤ P_K` on the scales (the choice `NK`). -/
structure HjAtM (P : BeurlingSystem) (X0m Z : ℝ) (X0 : ℕ) (N K : ℕ) (y : ℝ) : Prop where
  hZ : 2 * y / X0m ≤ Z
  hZ2 : 18 * y ≤ Z ^ 2
  hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ))
  hSR : ShortRecipLow P X0 y
  hK : ∀ v ∈ TNP.dyScales (X0 : ℝ) y N, √(2 * v) ≤ TNP.Pk X0m K

/-- `jXat = j₀ (𝔅 log y + E)` with `E` the `τ`-term. -/
lemma jXat_eq {X0 lam0 j0 y : ℝ} {N K : ℕ} (hy : 0 < Real.log y) :
    BModel.jXat P H tw X0m X0 θ lam0 j0 N K y = j0 * (xbB P H tw X0m y X0 θ lam0 * Real.log y +
      4.3 * CNc X0 * ∑ v ∈ TNP.dyScales X0 y N, Real.log (2 * v) * TNP.sTheta P H X0m K v) := by
  unfold BModel.jXat
  field_simp

set_option maxHeartbeats 2000000 in
/-- **Proposition 5.31(ii), second claim** (middle range, at a start `y`; Lean bound
`e^{-59}`). -/
theorem hj_mid_at (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℕ} {lam0 j0 y : ℝ} {N K : ℕ}
    (hX0e : X0m = X0 - H X0 / 2) (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000)
    (hH8 : H X0 ≤ (X0 : ℝ) ^ (1 / 8 : ℝ)) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hjz : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z) (hy : X0m ≤ y)
    (hA : HjAtM P X0m Z X0 N K y)
    (hNlow : Real.exp (0.01 * Real.log X0) / 2 ≤ y / X0)
    (hJ : Real.log (y / X0) ≤ 600 * Real.log X0 ^ 4) :
    BModel.jXat P H tw X0m X0 θ lam0 j0 N K y ≤ Real.exp (-59) := by
  have hP := h.width
  have hXm0 := hP.X0m_pos
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  set Λ := Real.log X0 with hΛdef
  have hΛ : 100000000 ≤ Λ := h.hXm.trans (Real.log_le_log hXm0 hXm)
  have hy0 : 0 < y := by linarith
  set N0 := y / X0 with hN0def
  have hN0 : 0 < N0 := by positivity
  have hly : Real.log y = Real.log N0 + Λ := by
    rw [hN0def, hΛdef, Real.log_div hy0.ne' hX0.ne']; ring
  -- `N ≥ e^{100}`
  have hN100 : Real.exp 100 ≤ N0 := by
    have : Real.exp 100 * 2 ≤ Real.exp (0.01 * Λ) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      calc Real.exp 100 * 2 ≤ Real.exp 100 * Real.exp 1 := by gcongr
        _ = Real.exp 101 := by rw [← Real.exp_add]; norm_num
        _ ≤ Real.exp (0.01 * Λ) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlN0 : 100 ≤ Real.log N0 := by
    rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hN100
  have hlyp : 0 < Real.log y := by linarith
  -- the two bounds
  have hB := xbB_mid h.hbs hP hX0e hH1 hδ hp2 h.hXm ht htv hlam hlam1 hy hA.hZ hA.hSR hN100
    (tw := tw)
  have hE := cne_le h hHw hΛ hZ0 hA.hZ2 hA.hK (X0 := X0)
  set E := 4.3 * CNc (X0 : ℝ) * ∑ v ∈ TNP.dyScales (X0 : ℝ) y N,
    Real.log (2 * v) * TNP.sTheta P H X0m K v with hEdef
  rw [jXat_eq hlyp]
  -- `δ ≤ e^{-0.875Λ}`, `N^{-0.195} ≤ 2e^{-0.00195Λ}`
  set δ := H X0 / X0 with hδdef
  have hδ8 : δ ≤ Real.exp (-(0.875 * Λ)) := by
    have e1 : (X0 : ℝ) ^ (1 / 8 : ℝ) = Real.exp (Λ / 8) := by
      rw [Real.rpow_def_of_pos hX0, hΛdef]; ring_nf
    have e2 : Real.exp (-(0.875 * Λ)) = Real.exp (Λ / 8) / X0 := by
      rw [eq_div_iff hX0.ne', ← Real.exp_log hX0, ← hΛdef, ← Real.exp_add]; ring_nf
    rw [e2, hδdef]
    exact div_le_div_of_nonneg_right (hH8.trans e1.le) hX0.le
  have hNp : N0 ^ (-(0.195 : ℝ)) ≤ 2 * Real.exp (-(0.00195 * Λ)) := by
    have hlow : Real.exp (0.01 * Λ) / 2 ≤ N0 := hNlow
    have h1 : (Real.exp (0.01 * Λ) / 2) ^ (0.195 : ℝ) ≤ N0 ^ (0.195 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlow (by norm_num)
    have h2 : (Real.exp (0.01 * Λ) / 2) ^ (0.195 : ℝ) =
        Real.exp (0.00195 * Λ) / 2 ^ (0.195 : ℝ) := by
      rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]; ring_nf
    have h3 : (2 : ℝ) ^ (0.195 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (0.195 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : Real.exp (0.00195 * Λ) / 2 ≤ N0 ^ (0.195 : ℝ) := by
      rw [h2] at h1
      calc Real.exp (0.00195 * Λ) / 2 ≤ Real.exp (0.00195 * Λ) / 2 ^ (0.195 : ℝ) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) h3
        _ ≤ _ := h1
    rw [Real.rpow_neg hN0.le, Real.exp_neg]
    have hp : 0 < N0 ^ (0.195 : ℝ) := Real.rpow_pos_of_pos hN0 _
    rw [inv_eq_one_div, inv_eq_one_div, div_le_iff₀ hp]
    have he := Real.exp_pos (0.00195 * Λ)
    field_simp
    nlinarith
  -- assemble
  have hlogy : Real.log y ≤ 601 * Λ ^ 4 := by
    have : Λ ≤ Λ ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hBpos : 0 ≤ 31000 * δ + 12200 * Real.exp 19.5 * N0 ^ (-(0.195 : ℝ)) := by
    have := Real.rpow_nonneg hN0.le (-(0.195 : ℝ))
    have : 0 ≤ δ := by positivity
    positivity
  have hBl : xbB P H tw X0m y X0 θ lam0 * Real.log y ≤
      (31000 * δ + 12200 * Real.exp 19.5 * N0 ^ (-(0.195 : ℝ))) * (601 * Λ ^ 4) +
        Real.exp (-62) * Λ := by
    have h1 := mul_le_mul_of_nonneg_right hB hlyp.le
    have h2 : (31000 * δ + 12200 * Real.exp 19.5 * N0 ^ (-(0.195 : ℝ)) +
        Real.exp (-62) * Λ / Real.log y) * Real.log y =
        (31000 * δ + 12200 * Real.exp 19.5 * N0 ^ (-(0.195 : ℝ))) * Real.log y +
          Real.exp (-62) * Λ := by field_simp
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left hlogy hBpos
    linarith
  set X := (31000 * δ + 12200 * Real.exp 19.5 * N0 ^ (-(0.195 : ℝ))) * (601 * Λ ^ 4) +
    Real.exp (-62) * Λ + Real.exp (-178) with hX
  have hX0' : 0 ≤ X := by positivity
  have hstep : j0 * (xbB P H tw X0m y X0 θ lam0 * Real.log y + E) ≤ 1.0001 / Λ * X := by
    have h1 : xbB P H tw X0m y X0 θ lam0 * Real.log y + E ≤ X := by rw [hX]; linarith
    calc j0 * (xbB P H tw X0m y X0 θ lam0 * Real.log y + E) ≤ j0 * X := by
          rcases eq_or_lt_of_le hj0 with h0 | h0
          · rw [← h0]; simp
          · exact mul_le_mul_of_nonneg_left h1 h0.le
      _ ≤ 1.0001 / Λ * X := mul_le_mul_of_nonneg_right hjz hX0'
  refine hstep.trans ?_
  have hΛ0 : 0 < Λ := by linarith
  -- the three terms of `1.0001 X/Λ`
  have hT1 : 1.0001 * 601 * 31000 * Λ ^ 3 * δ ≤ Real.exp (-62) := by
    have := poly_exp_small (C := 1.0001 * 601 * 31000) hΛ (c := 0.875) (by norm_num)
      (by norm_num) (by
        have := exp_20_5_ge
        have e : Real.exp 40 = Real.exp 20.5 * Real.exp 19.5 := by
          rw [← Real.exp_add]; norm_num
        have h2 : (2 : ℝ) ≤ Real.exp 19.5 := by
          have := Real.add_one_le_exp (19.5 : ℝ); linarith
        nlinarith)
    have hL3 : 0 ≤ Λ ^ 3 := by positivity
    calc 1.0001 * 601 * 31000 * Λ ^ 3 * δ ≤ 1.0001 * 601 * 31000 * Λ ^ 3 *
          Real.exp (-(0.875 * Λ)) := mul_le_mul_of_nonneg_left hδ8 (by positivity)
      _ ≤ Real.exp (-62) := this
  have hT2 : 1.0001 * 601 * 12200 * Real.exp 19.5 * Λ ^ 3 * N0 ^ (-(0.195 : ℝ)) ≤
      Real.exp (-62) := by
    have hC : 1.0001 * 601 * 12200 * Real.exp 19.5 * 2 ≤ Real.exp 40 := by
      have h1 := exp_20_5_ge
      have e : Real.exp 19.5 * Real.exp 20.5 = Real.exp 40 := by
        rw [← Real.exp_add]; norm_num
      have := Real.exp_pos 19.5
      nlinarith
    have := poly_exp_small (C := 1.0001 * 601 * 12200 * Real.exp 19.5 * 2) hΛ (c := 0.00195)
      (by norm_num) (by positivity) hC
    have hL3 : 0 ≤ Λ ^ 3 := by positivity
    calc 1.0001 * 601 * 12200 * Real.exp 19.5 * Λ ^ 3 * N0 ^ (-(0.195 : ℝ))
        ≤ 1.0001 * 601 * 12200 * Real.exp 19.5 * Λ ^ 3 * (2 * Real.exp (-(0.00195 * Λ))) :=
          mul_le_mul_of_nonneg_left hNp (by positivity)
      _ = 1.0001 * 601 * 12200 * Real.exp 19.5 * 2 * Λ ^ 3 * Real.exp (-(0.00195 * Λ)) := by
          ring
      _ ≤ Real.exp (-62) := this
  have hexp : Real.exp (-62) * 5 ≤ Real.exp (-59) := by
    have e : Real.exp (-62) * Real.exp 3 = Real.exp (-59) := by rw [← Real.exp_add]; norm_num
    have h3 : (5 : ℝ) ≤ Real.exp 3 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num) h1 3]
    have := Real.exp_pos (-62)
    nlinarith
  have h178 : Real.exp (-178) ≤ Real.exp (-62) := Real.exp_le_exp.mpr (by norm_num)
  have hfin : 1.0001 / Λ * X = 1.0001 * 601 * 31000 * Λ ^ 3 * δ +
      1.0001 * 601 * 12200 * Real.exp 19.5 * Λ ^ 3 * N0 ^ (-(0.195 : ℝ)) +
      1.0001 * Real.exp (-62) + 1.0001 * Real.exp (-178) / Λ := by
    rw [hX]; field_simp; first | done | ring
  rw [hfin]
  have h178' : 1.0001 * Real.exp (-178) / Λ ≤ Real.exp (-62) := by
    rw [div_le_iff₀ hΛ0]
    have := Real.exp_pos (-62)
    nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.31(iii), second claim**, at a start `y` of the huge range `log N ≥ 600Λ⁴`
(without the condition `log y > X₀^{1/100}` of `RML9.hj_full`). -/
theorem hj_huge_at (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℕ} {lam0 j0 y : ℝ} {N K : ℕ}
    (hX0e : X0m = X0 - H X0 / 2) (hH1 : 1 ≤ H X0) (hδ : H X0 / X0 ≤ 1 / 1000)
    (hδs : 200000 * (H X0 / X0) ≤ Real.exp (-61)) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hjz : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z) (hy : X0m ≤ y)
    (hA : HjAtM P X0m Z X0 N K y) (hJ : 600 * Real.log X0 ^ 4 ≤ Real.log (y / X0)) :
    BModel.jXat P H tw X0m X0 θ lam0 j0 N K y ≤ Real.exp (-59) := by
  have hP := h.width
  have hXm0 := hP.X0m_pos
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  set Λ := Real.log X0 with hΛdef
  have hΛ : 100000000 ≤ Λ := h.hXm.trans (Real.log_le_log hXm0 hXm)
  have hy0 : 0 < y := by linarith
  set J := Real.log (y / X0) with hJdef
  have hly : Real.log y = J + Λ := by
    rw [hJdef, hΛdef, Real.log_div hy0.ne' hX0.ne']; ring
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJpos : 0 < J := by nlinarith
  have hlyp : 0 < Real.log y := by linarith
  have hB := xbB_huge h.hbs hP hX0e hH1 hδ hp2 h.hXm ht htv hlam hlam1 hy hJ hA.hZ hA.hT
    hA.hSR (tw := tw)
  have hE := cne_le h hHw hΛ hZ0 hA.hZ2 hA.hK (X0 := X0)
  set E := 4.3 * CNc (X0 : ℝ) * ∑ v ∈ TNP.dyScales (X0 : ℝ) y N,
    Real.log (2 * v) * TNP.sTheta P H X0m K v with hEdef
  rw [jXat_eq hlyp]
  have hc : 200000 * (H X0 / X0) + Real.exp (-61) ≤ 2 * Real.exp (-61) := by linarith
  have hJΛ : J + Λ ≤ 1.0001 * J := by
    have h3 : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
    have h4 : Λ ^ 4 = Λ * Λ ^ 3 := by ring
    have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ Λ by linarith)
    nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hBl : xbB P H tw X0m y X0 θ lam0 * Real.log y ≤ 2 * Real.exp (-61) * Λ * 1.0001 := by
    have h1 := mul_le_mul_of_nonneg_right hB hlyp.le
    have h2 : (200000 * (H X0 / X0) + Real.exp (-61)) * Λ / J * Real.log y ≤
        2 * Real.exp (-61) * Λ / J * (1.0001 * J) := by
      rw [hly]
      gcongr
    have h3 : 2 * Real.exp (-61) * Λ / J * (1.0001 * J) = 2 * Real.exp (-61) * Λ * 1.0001 := by
      field_simp
    linarith
  set X := 2 * Real.exp (-61) * Λ * 1.0001 + Real.exp (-178) with hX
  have hX0' : 0 ≤ X := by positivity
  have hstep : j0 * (xbB P H tw X0m y X0 θ lam0 * Real.log y + E) ≤ 1.0001 / Λ * X := by
    have h1 : xbB P H tw X0m y X0 θ lam0 * Real.log y + E ≤ X := by rw [hX]; linarith
    calc j0 * (xbB P H tw X0m y X0 θ lam0 * Real.log y + E) ≤ j0 * X := by
          rcases eq_or_lt_of_le hj0 with h0 | h0
          · rw [← h0]; simp
          · exact mul_le_mul_of_nonneg_left h1 h0.le
      _ ≤ 1.0001 / Λ * X := mul_le_mul_of_nonneg_right hjz hX0'
  refine hstep.trans ?_
  have hfin : 1.0001 / Λ * X = 1.0001 * 1.0001 * 2 * Real.exp (-61) +
      1.0001 * Real.exp (-178) / Λ := by
    rw [hX]; field_simp; first | done | ring
  rw [hfin]
  have e : Real.exp (-61) * Real.exp 2 = Real.exp (-59) := by rw [← Real.exp_add]; norm_num
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have h178 : 1.0001 * Real.exp (-178) / Λ ≤ Real.exp (-61) * 0.9 := by
    rw [div_le_iff₀ hΛ0]
    have : Real.exp (-178) ≤ Real.exp (-61) := Real.exp_le_exp.mpr (by norm_num)
    have := Real.exp_pos (-61)
    nlinarith
  have := Real.exp_pos (-61)
  nlinarith

/-! ## `j_{X₀}` on `[X₀^{1.01}, b]` -/

set_option maxHeartbeats 1000000 in
/-- **`j_{X₀}(t) ≤ e^{-59}` for every `t ∈ [X₀^{1.01}, b]`** (Proposition 5.31(ii) and (iii)), when
every start `y ∈ W_t` satisfies `HjAtM` at the scale indices `NK y`. -/
theorem hj_all_le (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℕ} {lam0 j0 b : ℝ}
    {NK : ℝ → ℕ × ℕ} (hX0e : X0m = X0 - H X0 / 2) (hH1 : 1 ≤ H X0)
    (hδ : H X0 / X0 ≤ 1 / 1000) (hδs : 200000 * (H X0 / X0) ≤ Real.exp (-61))
    (hH8 : H X0 ≤ (X0 : ℝ) ^ (1 / 8 : ℝ)) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hHw : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) (hj0 : 0 ≤ j0)
    (hjz : j0 ≤ 1.0001 / Real.log X0) (hZ0 : 2500 ≤ Z)
    (hA : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → ∀ y, InW (H t) t y →
      HjAtM P X0m Z X0 (NK y).1 (NK y).2 y) :
    ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      BModel.jXdef P H tw X0m X0 θ lam0 j0 NK t ≤ Real.exp (-59) := by
  intro t ht1 htb
  have hP := h.width
  have hXm0 := hP.X0m_pos
  have hXm : X0m ≤ (X0 : ℝ) := by rw [hX0e]; linarith
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  set Λ := Real.log X0 with hΛdef
  have hΛ : 100000000 ≤ Λ := h.hXm.trans (Real.log_le_log hXm0 hXm)
  have hX1 : (X0 : ℝ) ^ (1.01 : ℝ) = X0 * Real.exp (0.01 * Λ) := by
    rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add hX0, Real.rpow_one,
      Real.rpow_def_of_pos hX0, hΛdef]; ring_nf
  have he1 : 2 ≤ Real.exp (0.01 * Λ) := by
    have := Real.add_one_le_exp (0.01 * Λ); linarith
  have htX : 2 * (X0 : ℝ) ≤ t := by rw [hX1] at ht1; nlinarith
  unfold BModel.jXdef
  refine Real.iSup_le (fun ⟨y, hyW⟩ => ?_) (Real.exp_pos _).le
  have hAy := hA t ht1 htb y hyW
  -- `y ≥ 0.95 t`
  have hHt : H t ≤ t / 10 := hP.small t (by linarith)
  have hyt : 0.95 * t ≤ y := by have := hyW.1; linarith
  have hyXm : X0m ≤ y := by nlinarith
  rcases le_or_gt (600 * Λ ^ 4) (Real.log (y / X0)) with hbig | hsmall
  · exact hj_huge_at h hX0e hH1 hδ hδs hp2 ht htv hlam hlam1 hHw hj0 hjz hZ0 hyXm hAy hbig
  · refine hj_mid_at h hX0e hH1 hδ hH8 hp2 ht htv hlam hlam1 hHw hj0 hjz hZ0 hyXm hAy ?_
      hsmall.le
    have : 0.95 * (X0 * Real.exp (0.01 * Λ)) ≤ y := by rw [← hX1]; nlinarith
    rw [le_div_iff₀ hX0]
    nlinarith

end KR.RML12

end
