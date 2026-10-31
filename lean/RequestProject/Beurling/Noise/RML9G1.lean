module

public import RequestProject.Beurling.Noise.RML9Bnd
public import RequestProject.Beurling.Noise.RML9Top
public import RequestProject.Beurling.Noise.RML8EEps
public import RequestProject.Beurling.Noise.RML7G1
public import RequestProject.Beurling.Noise.RML6BridgeNum
public import RequestProject.Beurling.BaseRange.MarginHc

/-!
# Proposition 5.35(B): one constructor for `KR.RML6.G1BInputs`

`KR.RML9.g1BInputs_of` builds `KR.RML6.G1BInputs P tw X0m X₀ Tp y` at a start `y` with
`X₀^{1/100} < log y`, for the width `H = H_c = Queue6.Hc X₀` and the source
`T' = T_c + j₀ 1_{[X₀,∞)}`, `j₀ = jzX X₀`, from four groups of residual inputs:

* `G1ResModel` : the Model agent's inputs (HBS, the width, the operators of §5.3, the margin
  identity, `T_c` and `NT_pt`, the window parameter `δ` and Theorem 5.24, Steps 3–4 of
  Proposition 5.35(B));
* `G1ResQueue6` : the Queue6 agent's inputs (`TNP.Hyp`, the Step 1 count, `ν̄`, `|ϑ| ≤ 6`,
  Lemma 5.23 at `2δ`);
* `G1ResBaseRange` : `HuxleyFrom X₀` (gives `j₀ ≤ 1.0001/Λ`, `BaseRange.jzX_le`);
* `G1ResSec5` : the §5 inputs not yet proved (the two bullets of Lemma 5.34 with their sizes,
  Proposition 5.26 and Lemma 5.27 at the window points, the large-height bound of
  Proposition 5.31(iii) and `4.3 C_N E_θ ≤ e^{-0.99Λ}`).

The fields of `G1BInputs` are then proved: `hit`, `his`, `hiB` (`KR.RML7`), `h34`
(`h34_of`), `hbr` (`hbr_of`, `abs_Rres_sub_rhoSh_loc`), `hNT` (`hNT_of`, `etaG_le_etaS`),
`hbd`, `hBnd0`, `hBnd` (`hbd_full`), `hsmall2` (`hsmall2_of`, `Phi_tiny`), `hεN`
(`epsN_le`), `hEBR`, `hj` (`hj_of_range`); `g1_range` derives the ranges `log y ≥ 20`,
`y ≥ 4X₀`, `δ ≤ 1/4` from `δ ≤ X₀^{-1/2}` and `log y > X₀^{1/100}`.
-/

@[expose] public section

open MeasureTheory Set Real KR.Ops

namespace KR.RML9

/-! ## Ranges -/

lemma exp_div100_ge {Λ : ℝ} (hΛ : 100000000 ≤ Λ) : Λ + 2 ≤ Real.exp (Λ / 100) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := Λ / 100) (by linarith)
  nlinarith

/-- The ranges of `G1BInputs` at a start `y` with `X₀^{1/100} < log y`. -/
lemma g1_range {X₀ : ℕ} {y δ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)) :
    0 < (X₀ : ℝ) ∧ 20 ≤ Real.log y ∧ 4 * (X₀ : ℝ) ≤ y ∧ 1 < y ∧ δ ≤ 1 / 4 ∧
      Real.log X₀ + 2 ≤ Real.log y ∧ 16 ≤ (X₀ : ℝ) := by
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hr : (X₀ : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Real.log X₀ / 100) := by
    rw [Real.rpow_def_of_pos hX0]; ring_nf
  rw [hr] at hy
  have h1 := exp_div100_ge hΛ
  have hly : Real.log X₀ + 2 ≤ Real.log y := by linarith
  have h4 : 4 * (X₀ : ℝ) ≤ y := by
    have hl4 : Real.log 4 ≤ 2 := by
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    have hle : Real.log (4 * (X₀ : ℝ)) ≤ Real.log y := by
      rw [Real.log_mul (by norm_num) hX0.ne']; linarith
    exact (Real.log_le_log_iff (by positivity) hy0).mp hle
  have hX16 : (16 : ℝ) ≤ X₀ := by
    rw [← Real.exp_log hX0]
    have : (16 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 3]
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  have hδ4 : (X₀ : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hX0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    rw [Real.le_sqrt (by norm_num) hX0.le]; linarith
  refine ⟨hX0, by linarith, h4, by linarith, hδ.trans hδ4, hly, hX16⟩

/-! ## The residual inputs, by owner -/

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X₀ : ℕ} {y Z η1 η2 : ℝ}
  {ε1 : ℝ → ℝ} {εW θW εS δ thrS : ℝ} {ρ ν NT vtH TcL Jl : LocInt} {ϑ NTpt Tc : ℝ → ℝ}

/-- The source `T' = T_c + j₀ 1_{[X₀,∞)}`, `j₀ = jzX X₀`. -/
noncomputable abbrev TpR (X₀ : ℕ) (Tc : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Tc t + BModel.jzX X₀ * KR.Chain.ind X₀ t

/-- The interval `J = [y(1-2δ), y(1-δ)]`. -/
abbrev Jint (y δ : ℝ) : Set ℝ := Icc (y * (1 - 2 * δ)) (y * (1 - δ))

/-- **The Model agent's inputs.** -/
structure G1ResModel (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (y Z η1 η2 : ℝ)
    (ε1 : ℝ → ℝ) (εW θW εS δ thrS : ℝ) (ρ ν NT vtH TcL Jl : LocInt) (ϑ NTpt Tc : ℝ → ℝ)
    (hO : OpHyp P (Queue6.Hc X₀) X0m) : Type where
  /-- the parameter conditions of §2.2 (`Cond θ X₀`) -/
  θc : ℝ
  hc : BModel.Cond θc X₀
  /-- the window parameter of Proposition 5.35(B), Step 1 -/
  hδ0 : 0 < δ
  hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ)
  hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
    Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)
  hδL : δ ≤ 1 / Real.log y ^ 4
  /-- Theorem 5.24 below the certified horizon -/
  hT : LocalPNT.Theorem524Concl P X₀ (y * (1 - δ))
  /-- (HBS) on `[1, Z]` (§5.2) -/
  hbs : P.HBS X0m Z η1 η2 ε1
  /-- (R_H) for `capH` (`BModel.capHSlope`), `ε ≤ 1/2` -/
  hS : KR.WidthReal.CapHSlope X₀ εS
  hεS0 : 0 ≤ εS
  hεS1 : εS ≤ 1 / 2
  /-- the width conditions of §5.1 for `H_c` (`KR.WidthReal.paperWidth_Hc`) -/
  hPW : KR.PaperWidth (Queue6.Hc X₀) X0m εW θW
  hXm1 : 1 ≤ X0m
  hX0m : X0m ≤ X₀
  /-- positive decision times (`dec_R`) -/
  htw : ∀ r, r.Prime → 0 < tw r
  /-- the horizons: `2y/X₀⁻ ≤ Z`, `2500 ≤ Z`, `18y ≤ Z²` -/
  hZ : 2 * y / X0m ≤ Z
  hZ0 : 2500 ≤ Z
  hZ18 : 18 * y ≤ Z ^ 2
  /-- `T_c` measurable and `|T_c| ≤ 2` below `3y` (§5.1) -/
  hTm : Measurable Tc
  hTb : ∀ t, t ≤ 3 * y → |Tc t| ≤ 2
  /-- the `LocInt` forms of `T_c` and `j₀ 1_{[X₀,∞)}` -/
  hTcL : (TcL : ℝ → ℝ) = Tc
  hJl : (Jl : ℝ → ℝ) = fun t => BModel.jzX X₀ * KR.Chain.ind X₀ t
  /-- the margin identity (Proposition 5.11 with (Ttilde)) -/
  hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / Queue6.Hc X₀ z
  hmargin : ρ + Bo hO (Ko (tw := tw) hO ρ) = Bo hO (TcL + Jl) + vtH - ν - NT
  hLBd : LBd ((TcL + Jl : LocInt) : ℝ → ℝ)
  /-- `NT = B NT_pt` and `|NT_pt| ≤ 54 η` at the window heights (eq. (NT), Lemma 5.20) -/
  hNTeq : ∀ z, (NT : ℝ → ℝ) z = Margin.Bavg (Queue6.Hc X₀ z) NTpt z
  hNTpt : ∀ s, y / 4 ≤ s → s ≤ 2 * y →
    |NTpt s| ≤ 54 * KR.etaG P (Queue6.Hc X₀) tw X0m (fun _ => 1) s
  /-- Steps 3–4 of Proposition 5.35(B) -/
  j0 : ℝ
  jS : ℝ
  detS : ℝ
  othS : ℝ
  hdec34 : ∀ z ∈ Jint y δ,
    rhoSh P tw X0m z (TpR X₀ Tc) - rhoSh P tw X0m y (TpR X₀ Tc) ≤
      4 * thrS + j0 * jS + detS + othS
  N : ℝ
  HN : ℝ
  θ : ℝ
  hj0 : 0 ≤ j0
  hj1 : j0 ≤ 1
  hjS : jS ≤ 4.1 * δ + 3 * HN / N + 2 * N ^ (thetaB θ - 1)
  hN : Real.exp (Real.log y / 2) ≤ N
  hHN0 : 0 ≤ HN
  hHN : HN ≤ N ^ (1 / 8 : ℝ)
  hθ0 : 0 ≤ θ
  hθ : θ ≤ 1 / 2
  CS : ℝ
  hCS0 : 0 ≤ CS
  hCS : CS ≤ 77
  hdet : Real.log y * detS ≤ CS * (7 * Real.log X₀ ^ 4 * (X₀ : ℝ) ^ (-(1 / 12) : ℝ) +
    90 * Real.log X₀ ^ (4.7 : ℝ) * Real.exp (-(Real.log X₀ / 12)))
  hoth : Real.log y * othS ≤ 1 / 10 ^ 27

/-- **The Queue6 agent's inputs.** -/
structure G1ResQueue6 (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (y Z η1 η2 : ℝ)
    (ε1 : ℝ → ℝ) (εW θW δ thrS : ℝ) (ρ ν : LocInt) (ϑ : ℝ → ℝ) : Type where
  /-- the standing hypotheses of Lemma 5.20 (`Queue6.tnpHyp_R`) -/
  htnp : KR.TNP.Hyp P (Queue6.Hc X₀) tw X0m Z η1 η2 ε1 εW θW
  /-- Step 1, first bullet: the prime window count -/
  Eloc : ℝ
  hE0 : 0 ≤ Eloc
  hE : Eloc ≤ 40 * √y
  hcount : LocalPNT.piCount P (y * (1 - δ)) - LocalPNT.piCount P (y * (1 - 2 * δ)) - Eloc ≤
    ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), (ρ : ℝ → ℝ) z
  /-- Lemma 5.22 on `J`: `|ν| ≤ ν̄`, with `log y · ν̄ ≤ 10⁻²⁷` ((sw-sums)) -/
  nb : ℝ
  hν : ∀ z ∈ Jint y δ, |(ν : ℝ → ℝ) z| ≤ nb
  hnb : Real.log y * nb ≤ 1 / 10 ^ 27
  /-- the slot granularity `|ϑ| ≤ 6` on `J` -/
  hϑ : ∀ z ∈ Jint y δ, |ϑ z| ≤ 6
  /-- Lemma 5.23 at `2δ` (`threshold_mass`) -/
  Hy : ℝ
  Kloc : ℝ
  hthr : thrS ≤ 55 * (2 * δ) * Real.log y * (Real.log Hy + Real.log (1 / (2 * δ)) + 2) +
    14 * (Kloc + 2) * Real.log y * √(Hy / (2 * δ * y))
  hH1 : 1 ≤ Hy
  hH : Hy ≤ Real.exp (Real.log y / 8)
  hK0 : 0 ≤ Kloc
  hK : Kloc ≤ Hy

/-- **The BaseRange agent's input**: (huxley) from `X₀` on (gives `j₀ ≤ 1.0001/Λ`). -/
structure G1ResBaseRange (X₀ : ℕ) : Prop where
  hHux : BaseRange.HuxleyFrom (X₀ : ℝ)

/-- **The §5 inputs not yet proved.** -/
structure G1ResSec5 (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (y δ : ℝ)
    (ρ ν NT vtH TcL Jl : LocInt) (Tc : ℝ → ℝ) (hO : OpHyp P (Queue6.Hc X₀) X0m) : Type where
  /-- the sizes of `ε_N` (Lemma 5.34, (sw-sums), (osc), Lemma 5.20) -/
  CN : ℝ
  hCN : CN ≤ 158
  SK : ℝ
  SG : ℝ
  h6 : ℝ
  hSK0 : 0 ≤ SK
  hSK : SK ≤ 1 / 10 ^ 20
  hSG0 : 0 ≤ SG
  hSG : SG ≤ Real.exp (-41) + 2 / 10 ^ 22
  hh6 : h6 ≤ 1 / 10 ^ 20
  /-- the two bullets of Lemma 5.34 on `J` (`hK_field`, `hG_field_paper` at the starts of `J`)
  and their size `ε_N` -/
  aK : ℝ → ℝ
  bG : ℝ → ℝ
  hKb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO TcL - TcL) + vtH - ν - NT)))) : ℝ → ℝ) z| ≤ aK z
  hGb : ∀ z ∈ Jint y δ, Real.log z * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl) -
        Bo hO (Bo hO (TcL + Jl) + vtH - ν - NT - Bo hO Jl)))) : ℝ → ℝ) z| ≤ bG z
  hsize : ∀ z ∈ Jint y δ, (aK z + bG z + 6 * Real.log z / Queue6.Hc X₀ z) / Real.log z ≤
    (5.1 * CN * SK + 35.8 * CN * 10 * SG + h6) / Real.log y
  /-- `H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}` (`KR.WidthReal.Hc_Xm_half_le` at `X₀⁻ = Xm X₀`) -/
  hHhalf : Queue6.Hc X₀ (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)
  /-- Proposition 5.26 at the heights read, `s ∈ [y/4, y(1-δ) + H_c(y)/2]` (the window points
  of `J`; `Ytop_le_b`: these lie below the event height), with `sizeE_le`:
  `|BR_c| ≤ e^{-76}/log y` -/
  hBRs : ∀ s, y / 4 ≤ s → s ≤ Ytop X₀ y δ →
    |KR.BRc P (Queue6.Hc X₀) tw X0m s Tc| ≤ Real.exp (-76) / Real.log y
  /-- Lemma 5.27 at the heights read (as for `hBRs`):
  `|R_res 1 - ρ^sh 1| ≤ 𝔅 + 4.3 C_N E_θ/log y` -/
  Bx : ℝ
  CNE : ℝ
  hXBs : ∀ s, y / 4 ≤ s → s ≤ Ytop X₀ y δ →
    |KR.Rres P (Queue6.Hc X₀) tw X0m s (KR.Chain.ind X₀) -
      KR.rhoSh P tw X0m s (KR.Chain.ind X₀)| ≤ Bx + CNE / Real.log y
  /-- Proposition 5.31(iii) at large heights and `4.3 C_N E_θ ≤ e^{-0.99Λ}` -/
  δx : ℝ
  τ0 : ℝ
  hτ0 : 0 ≤ τ0
  hτ : τ0 ≤ 1.0001 * Real.log X₀
  hδx0 : 0 ≤ δx
  hδx : 400 * δx ≤ Real.exp (-60) / 2
  hBx : Bx ≤ (400 * δx + Real.exp (-60)) * τ0 / (Real.log y - Real.log X₀)
  hCNE0 : 0 ≤ CNE
  hCNE : CNE ≤ Real.exp (-(0.99 * Real.log X₀))

/-! ## The window points -/

lemma win_bounds {hO : OpHyp P (Queue6.Hc X₀) X0m} (hX0m : X0m ≤ X₀) (hX0 : 0 < (X₀ : ℝ))
    (hy4 : 4 * (X₀ : ℝ) ≤ y) (_hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) {z s : ℝ} (hz : z ∈ Jint y δ)
    (hs1 : z - Queue6.Hc X₀ z / 2 ≤ s) (hs2 : s ≤ z + Queue6.Hc X₀ z / 2) :
    y / 4 ≤ s ∧ s ≤ 2 * y ∧ X0m ≤ s ∧ 1.2 * |s| ≤ 3 * y ∧ y / 2 ≤ z ∧ z ≤ y := by
  obtain ⟨hz1, hz2⟩ := hz
  have hy0 : 0 < y := by linarith
  have hzl : y / 2 ≤ z := by nlinarith
  have hzu : z ≤ y := by nlinarith
  have hH := hO.small z (by linarith)
  have hHp := hO.pos z
  have hs0 : y / 4 ≤ s := by linarith
  refine ⟨hs0, by linarith, by linarith, ?_, hzl, hzu⟩
  rw [abs_of_nonneg (by linarith)]; linarith

/-! ## The constructor -/

/-- **`G1BInputs` at a start `y` with `X₀^{1/100} < log y`**, for `H = H_c` and
`T' = T_c + j₀ 1_{[X₀,∞)}`, from the four groups of residual inputs. -/
noncomputable def g1BInputs_of (hO : OpHyp P (Queue6.Hc X₀) X0m) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y)
    (M : G1ResModel P tw X0m X₀ y Z η1 η2 ε1 εW θW εS δ thrS ρ ν NT vtH TcL Jl ϑ NTpt Tc hO)
    (Q : G1ResQueue6 P tw X0m X₀ y Z η1 η2 ε1 εW θW δ thrS ρ ν ϑ)
    (B : G1ResBaseRange X₀)
    (S : G1ResSec5 P tw X0m X₀ y δ ρ ν NT vtH TcL Jl Tc hO) :
    KR.RML6.G1BInputs P tw X0m X₀ (TpR X₀ Tc) y :=
  have hΛ : 100000000 ≤ Real.log X₀ := by have := M.hc.hX; norm_num at this ⊢; linarith
  have hR := g1_range hΛ hy0 hy M.hδ
  have hX0 := hR.1
  have hL := hR.2.1
  have hy4 := hR.2.2.1
  have hy1 := hR.2.2.2.1
  have hδ4 := hR.2.2.2.2.1
  have hX16 := hR.2.2.2.2.2.2
  have hly0 : 0 < Real.log y := by linarith
  have hab : y * (1 - 2 * δ) ≤ y * (1 - δ) := by nlinarith [M.hδ0]
  have ha0 : 0 ≤ y * (1 - 2 * δ) := by nlinarith [M.hδ0]
  have hb3 : y * (1 - δ) ≤ 3 * y := by nlinarith [M.hδ0]
  have hXmpos : 0 < X0m := by linarith [M.hXm1]
  have hjz0 : 0 ≤ BModel.jzX X₀ := BModel.jzX_nonneg M.hc
  have hjz : BModel.jzX X₀ ≤ 1.0001 / Real.log X₀ := BaseRange.jzX_le M.hc.hX B.hHux
  have hjz1 : BModel.jzX X₀ ≤ 1 := hjz.trans (by
    rw [div_le_one (by linarith)]; linarith)
  have hTJ : ((TcL + Jl : LocInt) : ℝ → ℝ) = TpR X₀ Tc := by
    funext t
    rw [AddSubgroup.coe_add, Pi.add_apply, M.hTcL, M.hJl]
  have hTpm : Measurable (TpR X₀ Tc) :=
    M.hTm.add (measurable_const.mul (KR.Chain.ind_measurable (X₀ : ℝ)))
  { δ := δ
    hδ0 := M.hδ0
    hδ := M.hδ
    hδlow := M.hδlow
    hδL := M.hδL
    hT := M.hT
    ρt := (ρ : ℝ → ℝ)
    Eloc := Q.Eloc
    hE0 := Q.hE0
    hE := Q.hE
    hcount := Q.hcount
    ν := (ν : ℝ → ℝ)
    NT := (NT : ℝ → ℝ)
    BRT := fun z => Margin.Bavg (Queue6.Hc X₀ z)
      (fun s => KR.Rres P (Queue6.Hc X₀) tw X0m s (TpR X₀ Tc)) z
    Bρs := fun z => Margin.Bavg (Queue6.Hc X₀ z) (fun s => KR.rhoSh P tw X0m s (TpR X₀ Tc)) z
    εN := 5.1 * S.CN * S.SK + 35.8 * S.CN * 10 * S.SG + S.h6
    EBR := Real.exp (-76)
    j := Real.log y * BModel.jzX X₀ * (S.Bx + S.CNE / Real.log y)
    nb := Q.nb
    η := KR.RML8E.etaS (Queue6.Hc X₀) X0m y
    Bnd := 3 * (Real.log (2 * y / X0m) + 1) *
      (3 * κW X₀ εS y δ * (bW y δ - aW y δ) + 8 * HsW X₀ y)
    hit := ρ.2 _ _
    his := KR.RML7.his_of hXmpos M.hTm M.hTb (BModel.jzX X₀) (X₀ : ℝ) hab ha0 hb3
    hiB := KR.RML7.hiB_of hO hab
      (KR.TcLoc.intRS_loc hXmpos M.hTm M.hTb (BModel.jzX X₀) (X₀ : ℝ)
        (by linarith : (0 : ℝ) ≤ 3 * y) le_rfl le_rfl) (by linarith)
      (fun z hz => by
        have h1 := win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz
          (le_refl (z - Queue6.Hc X₀ z / 2)) (by linarith [hO.pos z])
        have h2 := win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz
          (by linarith [hO.pos z]) (le_refl (z + Queue6.Hc X₀ z / 2))
        exact ⟨by linarith [h1.1], by linarith [h2.2.1]⟩)
    h34 := by
      intro z hz
      have h := KR.RML7.h34_of (tw := tw) hO M.hPW ρ ν NT vtH TcL Jl ϑ M.hvt M.hmargin M.hLBd
        S.aK S.bG (lo := y * (1 - 2 * δ)) (hi := y * (1 - δ)) (y := y)
        (εN := 5.1 * S.CN * S.SK + 35.8 * S.CN * 10 * S.SG + S.h6)
        (fun z hz => by
          have := win_bounds (hO := hO) (s := z) M.hX0m hX0 hy4 M.hδ0 hδ4 hz
            (by linarith [hO.pos z]) (by linarith [hO.pos z])
          exact Real.log_pos (by linarith [this.2.2.2.2.1, hX16]))
        S.hKb S.hGb Q.hϑ S.hsize z hz
      rw [hTJ] at h
      exact h
    hbr := by
      refine KR.RML7.hbr_of hO (F := TpR X₀ Tc)
        (c := (Real.exp (-76) + Real.log y * BModel.jzX X₀ * (S.Bx + S.CNE / Real.log y)) /
          Real.log y) ?_ ?_ ?_
      · intro z hz
        exact KR.TcLoc.intRT_loc hO M.hPW M.hTm M.hTb (BModel.jzX X₀) (X₀ : ℝ)
          (by linarith [hO.pos z]) (fun s h1 h2 =>
            (win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz h1 h2).2.2.2.1)
      · intro z hz
        have h1 := win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz
          (le_refl (z - Queue6.Hc X₀ z / 2)) (by linarith [hO.pos z])
        have h2 := win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz
          (by linarith [hO.pos z]) (le_refl (z + Queue6.Hc X₀ z / 2))
        exact KR.TcLoc.intRS_loc hXmpos M.hTm M.hTb (BModel.jzX X₀) (X₀ : ℝ)
          (by linarith [hO.pos z]) (by linarith [h1.1]) (by linarith [h2.2.1])
      · intro z hz s hs1 hs2
        obtain ⟨hw1, hw2, hw3, hw4, -, -⟩ :=
          win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz hs1 hs2
        have hls : 0 < Real.log s := Real.log_pos (by linarith [hX16])
        have hTb' : ∀ t, t ≤ 1.2 * s → |Tc t| ≤ 2 := fun t ht => M.hTb t (by
          rw [abs_of_nonneg (by linarith)] at hw4; linarith)
        have hBR : Real.log s * |KR.BRc P (Queue6.Hc X₀) tw X0m s Tc| ≤
            Real.log s * (Real.exp (-76) / Real.log y) :=
          mul_le_mul_of_nonneg_left (S.hBRs s hw1 (win_le_Ytop hΛ hy0 M.hδ0 hz hs2)) hls.le
        have h := KR.RML7.abs_Rres_sub_rhoSh_loc (tw := tw) (j0 := BModel.jzX X₀) hO M.hPW hw3
          hls M.hTm hTb' hBR (S.hXBs s hw1 (win_le_Ytop hΛ hy0 M.hδ0 hz hs2))
        have e : Real.log s * (Real.exp (-76) / Real.log y) / Real.log s +
            |BModel.jzX X₀| * (S.Bx + S.CNE / Real.log y) =
            (Real.exp (-76) + Real.log y * BModel.jzX X₀ * (S.Bx + S.CNE / Real.log y)) /
              Real.log y := by
          rw [abs_of_nonneg hjz0]; field_simp
        rw [e] at h
        exact h
    hν := Q.hν
    hNT := by
      intro z hz
      rw [M.hNTeq z]
      refine KR.RML7.hNT_of hO (fun z' hz' s hs1 hs2 => ?_) z hz
      obtain ⟨hw1, hw2, -, -, -, -⟩ :=
        win_bounds (hO := hO) M.hX0m hX0 hy4 M.hδ0 hδ4 hz' hs1 hs2
      have hs1' : 1 ≤ s := by linarith [hX16]
      have hys : Real.log y ≤ 2 * Real.log s := by
        have h4 : Real.log y - Real.log 4 ≤ Real.log s := by
          rw [← Real.log_div hy0.ne' (by norm_num)]
          exact Real.log_le_log (by positivity) (by linarith)
        have hl4 : Real.log 4 ≤ 2 := by
          have e : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
          have := Real.log_two_lt_d9; linarith
        linarith
      have he := KR.RML8E.etaG_le_etaS Q.htnp hy1 hs1' hys M.hZ0 (by linarith [M.hZ18])
      have hn := M.hNTpt s hw1 hw2
      linarith
    hbd := (hbd_full M.hc.hX M.hεS0 M.hεS1 M.hS M.hbs M.htw M.hXm1 hTpm (by linarith)
      (by linarith [M.hX0m]) hL M.hδ0 hδ4 M.hZ (fun u hu1 hu2 => by
        have h1 := M.hTb u (by linarith)
        have h2 : |BModel.jzX X₀ * KR.Chain.ind X₀ u| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hjz0]
          have := KR.Chain.ind_abs_le (X₀ : ℝ) u
          nlinarith [abs_nonneg (KR.Chain.ind (X₀ : ℝ) u)]
        calc |TpR X₀ Tc u| ≤ |Tc u| + |BModel.jzX X₀ * KR.Chain.ind X₀ u| := abs_add_le _ _
          _ ≤ 3 := by linarith)).1
    hBnd0 := (hbd_full M.hc.hX M.hεS0 M.hεS1 M.hS M.hbs M.htw M.hXm1 hTpm (by linarith)
      (by linarith [M.hX0m]) hL M.hδ0 hδ4 M.hZ (fun u hu1 hu2 => by
        have h1 := M.hTb u (by linarith)
        have h2 : |BModel.jzX X₀ * KR.Chain.ind X₀ u| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hjz0]
          have := KR.Chain.ind_abs_le (X₀ : ℝ) u
          nlinarith [abs_nonneg (KR.Chain.ind (X₀ : ℝ) u)]
        calc |TpR X₀ Tc u| ≤ |Tc u| + |BModel.jzX X₀ * KR.Chain.ind X₀ u| := abs_add_le _ _
          _ ≤ 3 := by linarith)).2.1
    hBnd := (hbd_full M.hc.hX M.hεS0 M.hεS1 M.hS M.hbs M.htw M.hXm1 hTpm (by linarith)
      (by linarith [M.hX0m]) hL M.hδ0 hδ4 M.hZ (fun u hu1 hu2 => by
        have h1 := M.hTb u (by linarith)
        have h2 : |BModel.jzX X₀ * KR.Chain.ind X₀ u| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hjz0]
          have := KR.Chain.ind_abs_le (X₀ : ℝ) u
          nlinarith [abs_nonneg (KR.Chain.ind (X₀ : ℝ) u)]
        calc |TpR X₀ Tc u| ≤ |Tc u| + |BModel.jzX X₀ * KR.Chain.ind X₀ u| := abs_add_le _ _
          _ ≤ 3 := by linarith)).2.2
    hsmall2 := KR.RML8E.hsmall2_of hy1 Q.hnb
      (KR.WidthReal.Phi_tiny Q.htnp S.hHhalf (a := 2) (by norm_num))
    hεN := KR.RML8E.epsN_le S.hCN S.hSK0 S.hSK S.hSG0 S.hSG S.hh6
    hEBR := le_rfl
    hj := KR.RML8E.hj_of_range hΛ hy S.hτ0 S.hτ hjz0 hjz S.hδx0 S.hδx S.hBx S.hCNE0 S.hCNE
    thrS := thrS
    j0 := M.j0
    jS := M.jS
    detS := M.detS
    othS := M.othS
    hdec34 := M.hdec34
    Hy := Q.Hy
    Kloc := Q.Kloc
    hthr := Q.hthr
    hH1 := Q.hH1
    hH := Q.hH
    hK0 := Q.hK0
    hK := Q.hK
    N := M.N
    HN := M.HN
    θ := M.θ
    hj0 := M.hj0
    hj1 := M.hj1
    hjS := M.hjS
    hN := M.hN
    hHN0 := M.hHN0
    hHN := M.hHN
    hθ0 := M.hθ0
    hθ := M.hθ
    CS := M.CS
    hCS0 := M.hCS0
    hCS := M.hCS
    hdet := M.hdet
    hoth := M.hoth }

end KR.RML9

end
