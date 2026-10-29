module

public import RequestProject.Beurling.Model.MarginMine
public import RequestProject.Beurling.Model.S2Final
public import RequestProject.Beurling.Model.Wire
public import RequestProject.Beurling.BaseRange.Lemma73R

/-!
# The final assembly: Theorem 2.1 / Corollary 2.2 from (84) and the open inputs

The local Proposition 5.38 (`BModel.pointwiseMarginOn_of_loc`, from `RealMarginLoc`) and the
proved eq. (s2) (`BModel.s2Core`) give `Theorem21InputsZ`, hence Corollary 2.2.

The fields of `RealMarginLoc` are split as follows.

* **Proved here** (Model): `hbs` (`hbs_Zc`: (H_BS) on `[1, Zc b]` on `Good(< b)`), `hSG`
  (`NiceEv`), `hX1` (`log X₀ ≥ 10⁸ + 1`, from `X₀ ≥ e^{10⁸+1}`), the horizon `Z = Zc b` with
  `hZ` (`2(b + H(b))/X₀⁻ ≤ Z`) and the Z conditions of the bridge (`Zc_facts`: `2500 ≤ Z`,
  `18(b + H(b)) ≤ Z²`, `X₀⁻ ≤ Z`), `η₁ = η₂ = 10⁻³`, `ε₁ = hbsEps`, `ε = 4·10⁻⁶` (`hε0`, `hε`),
  `λ₀ = 1.001` (`hlam`, `hlam1`), `j₀ = 1 - ρ_det(X₀)` (`hj0`, from (84) via
  `Model.rhoDet_le`), `xmax = b + H(b)` (`hxmax`), and
  `hDiff` (`CapHDiffProof.capHDiff`, `Model/CapHDiff.lean`: `H` is differentiable off a
  countable set, §5.1 "`H` is piecewise smooth").
* **Open, Model-owned**: `hSlope` (`CapHSlope X₀ 4·10⁻⁶`: (R_H) for `capH`, integrated form;
  Theorem 6.23(c) with §5.1 "Regularity of `H`"; deterministic), and `hTm`, `hTb` (`TcBound`:
  `T_c` is measurable and `|T_c| ≤ 2`; §5.1 "`|T'| ≤ 2`" with the jump at `X₀` removed, and
  Lemma rhoA(b) for the part `K_𝒜 ρ̃`), a.s.
* **Open, owned by the other agents**, grouped by paper section, with the Model choices
  substituted: `RestBase` (§7: (huxley), Lemma 7.3's inputs), `RestBridge` (Proposition 5.18
  step (iii), Proposition 5.26, Lemma 5.27, Lemma 5.20), `RestRes` (Proposition 5.35,
  Lemma 5.34, the margin identity), `RestMargin` (Proposition 5.38, steps 1–6).

Main result: `corollary_2_2_final : ShortIntervalPNT → Theorem21InputsFinal → ¬ QuestionQ`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP KR.Chain
  CaplLink Queue6

namespace BModel

/-- **§7 inputs** of `RealMarginLoc` ((huxley), Lemma 7.3), at `xmax = b + H(b)`. -/
structure RestBase (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where
  /-- (huxley) and Lemma 7.3's inputs (§7) -/
  hHux : BaseRange.HuxleyFrom X₀

/-- **Proposition 5.18 step (iii), Proposition 5.26, Lemma 5.27, Lemma 5.20** inputs of
`RealMarginLoc`, at the Model choices `Z = Zc b`, `ε = 4·10⁻⁶`, `λ₀ = 1.001`, `j₀ = jzX X₀`. -/
structure RestBridge (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where
  EBR : ℝ → ℝ
  jX : ℝ → ℝ
  EBR_nonneg : ∀ x, 0 ≤ EBR x
  jX_nonneg : ∀ x, 0 ≤ jX x
  /-- **Proposition 5.26, Lemma 5.27, Lemma 5.20** at the starts of the windows of the centres
  `X₁ ≤ x ≤ b` -/
  bridge : ∀ x y, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → InW (Queue6.Hc X₀ x) x y →
    BridgeR (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ ((epsH) / 10) (lamH)
      (TcR θ X₀ ω (jzX X₀)) (jzX X₀) y (EBR x) (jX x)

/-- **Proposition 5.35, Lemma 5.34 and the margin identity** inputs of `RealMarginLoc`. -/
structure RestRes (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where
  /-- **Proposition 5.35**, residual inputs, at `X₀ ≤ y ≤ b + H(b)` -/
  g1 : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b →
    G1At (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀) (KR.Sharp.rhoEdge (PR θ X₀ ω)
        (twR θ X₀ ω) (Xm X₀) X₀)
      (fun t => TcR θ X₀ ω (jzX X₀) t + (jzX X₀) * ind X₀ t) y
  /-- `NT` (locally integrable) -/
  NT : KR.Ops.LocInt
  ϑ : ℝ → ℝ
  a : ℝ → ℝ
  bb : ℝ → ℝ
  /-- Lemma 5.34, first bullet (from Proposition 5.18; `KR.Ops.hK_of_kernel` reduces it to the
  kernel part at each start of the window) -/
  hK : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
    Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO (KR.Ops.Bo hO
      (KR.Ops.Ro (tw := twR θ X₀ ω) hO ((KR.Ops.Bo hO TcL - TcL) + vtH -
        nuRes hO (twR θ X₀ ω) ρL TcL (JL (jzX X₀) X₀) vtH NT - NT)))) : ℝ → ℝ) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
    Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ro (tw := twR θ X₀ ω) hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO
      ((KR.Ops.Bo hO (TcL + JL (jzX X₀) X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL
        (jzX X₀) X₀) vtH NT -
          NT - KR.Ops.Bo hO (JL (jzX X₀) X₀)) -
        KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL (jzX X₀) X₀) + vtH -
          nuRes hO (twR θ X₀ ω) ρL TcL (JL (jzX X₀) X₀) vtH NT - NT - KR.Ops.Bo hO (JL
            (jzX X₀) X₀))))) :
      ℝ → ℝ) x| ≤ bb x
  /-- `|ϑ| ≤ 6` (eq. (Ttilde)) -/
  hϑ : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → |ϑ x| ≤ 6
  -- **Lemma 5.34**, on the operators of §5.3 (`KR.Ops`: `B = Bo`, `K_pt = Ko`, `R_res = Ro` on
  -- `LocInt`; `R_res` inverts `1 + K_pt B` and `1 + B K_pt` is injective by `Nop_spec`,
  -- `inj_spec`; `B` is the window average by definition). `ν` is the residual `nuRes`, so the
  -- margin identity holds by definition. The fields quantify over the proof `hO` of `OpHyp`
  -- (any two are equal; `RealMarginLoc.opH` provides one).
  /-- `ρ̃` is locally integrable -/
  ρL : KR.Ops.LocInt
  hρL : (ρL : ℝ → ℝ) = rhoT θ X₀ ω
  /-- `T_c` is locally integrable -/
  TcL : KR.Ops.LocInt
  hTcL : (TcL : ℝ → ℝ) = TcR θ X₀ ω (jzX X₀)
  /-- `ϑ/H` (locally integrable) -/
  vtH : KR.Ops.LocInt
  hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / Queue6.Hc X₀ z
  /-- `T' = T_c + J` bounded and measurable on half-lines -/
  hTLBd : KR.Ops.LBd (fun t => TcR θ X₀ ω (jzX X₀) t + (jzX X₀) * ind X₀ t)

/-- **Proposition 5.38, steps 1–6** inputs of `RealMarginLoc`. -/
structure RestMargin (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) (EBR : ℝ → ℝ) (jX : ℝ → ℝ)
  (ρL : KR.Ops.LocInt) (TcL : KR.Ops.LocInt) (NT : KR.Ops.LocInt) (vtH : KR.Ops.LocInt)
    (a : ℝ → ℝ) (bb : ℝ → ℝ) where
  -- **Proposition 5.38(a)**
  Bt : ℝ → ℝ
  η : ℝ → ℝ
  sη : ℝ
  /-- window integrability of `m` -/
  intm : ∀ t, IntervalIntegrable (marginM θ X₀ ω) volume
    (t - Queue6.Hc X₀ t / 2) (t + Queue6.Hc X₀ t / 2)
  /-- **Steps 1–5**: the parameters of the recursion and its super-solution -/
  p : Margin.Rec.CP
  T0 : ℝ
  err : ℝ → ℝ
  e : ℝ → ℕ → ℝ
  ηV : ℝ → ℝ
  chain : Margin.Rec.ChainHyp (PR θ X₀ ω) p (Queue6.Hc X₀)
  hpXm : p.Xm = Xm X₀
  hpε : p.ε ≤ 0.01
  hT0 : p.cinf + p.Kc ≤ T0
  hT0wf : 2 ≤ T0 * (1 - p.θ0)
  hT0T : T0 ≤ b
  /-- `ρ̃ = 0` below `X₀⁻` (the slots are `≥ X₀`, §5.1) -/
  hρ0 : ∀ z, z < Xm X₀ → rhoT θ X₀ ω z = 0
  hT0' : ∀ t, T0 ≤ t → t ≤ b → 0 ≤ t ∧ 1.01 * Queue6.Hc X₀ t ≤ t
  /-- `H`-regularity at a cofactor (`HStep`) -/
  hgeom : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
    Margin.Rec.HStep (Queue6.Hc X₀) p.ε t (t / KR.Vl (PR θ X₀ ω) w) (KR.Vl (PR θ X₀ ω) w)
  s2ε : ℝ → ℝ
  s2mst : ℝ → ℝ
  /-- **Step 1 / Lemma 5.22 on `A₊`** (Queue6): `σ(A₊) = ∫_{A₊} m + E₊`, `|E₊| ≤ (epsH)` -/
  hS2Ep : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |Margin.Exact.sigmaS ((Queue6.s2Q θ X₀ ω) z s) ((Queue6.s2sl θ X₀ ω) z s) (Margin.Exact.Aplus
      (Queue6.Hc X₀) z s) -
      ∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε z
  /-- **Step 1 / Lemma 5.22 on `A₋`** (Queue6): `σ(A₋) = ∫_{A₋} m + E₋`, `|E₋| ≤ (epsH)` -/
  hS2Em : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |Margin.Exact.sigmaS ((Queue6.s2Q θ X₀ ω) z s) ((Queue6.s2sl θ X₀ ω) z s) (Margin.Exact.Aminus
      (Queue6.Hc X₀) z s) -
      ∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε z
  /-- **Step 2, strip comparison on `A₊`** (§5): `|∫_{A₊} m - ∫_{I₊} m| ≤ 1.05 δ_z H(z) m*`,
  `I₊ = (z + H/2, z + H/2 + s]` -/
  hS2sp : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |(∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
      ∫ r in (z + Queue6.Hc X₀ z / 2)..(z + Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
      1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * s2mst z
  /-- **Step 2, strip comparison on `A₋`** (§5), `I₋ = (z - H/2, z - H/2 + s]` -/
  hS2sm : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |(∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
      ∫ r in (z - Queue6.Hc X₀ z / 2)..(z - Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
      1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * s2mst z
  /-- **Step 2**, `H(z) ≤ 1.01 H(x)` on the lower strip (regularity of `H`, §5) -/
  hS2H : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ x ∈ Icc (z - Queue6.Hc X₀ z / 2)
    (z + 0.51 * Queue6.Hc X₀ z), Queue6.Hc X₀ z ≤ 1.01 * Queue6.Hc X₀ x
  /-- **Step 2**, integrability of `m` on the strips -/
  hS2mi : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    IntervalIntegrable (marginM θ X₀ ω) volume (z - Queue6.Hc X₀ z / 2)
      (z + Queue6.Hc X₀ z / 2 + s)
  /-- **Step 2**, the error: `2ε/H(z) + (3.3 + 2.1 m*) δ_z ≤ err(z)` -/
  hS2err : ∀ z, S2Rng θ X₀ ω p T0 b z →
    2 * s2ε z / Queue6.Hc X₀ z + (3.3 + 2.1 * s2mst z) * (Queue6.s2δ X₀) z ≤ err z
  /-- **Step 3**, the recursion weights: `err(z') ≤ e(t, w)` on the strip of `(t, w)` -/
  hS2e : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, ∀ z',
    t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
      z' ≤ t / KR.Vl (PR θ X₀ ω) w → err z' ≤ e t w
  he0 : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, 0 ≤ e t w
  /-- filter switching and `ΔNT_pt ≤ 2η` -/
  hsw : ∀ t, T0 ≤ t → t ≤ b → ∀ hh, |hh| ≤ 1.01 * Queue6.Hc X₀ t →
    |∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
        (Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) (t + hh) w -
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w) *
        (rhoT θ X₀ ω ((t + hh) / KR.Vl (PR θ X₀ ω) w) / KR.Vl (PR θ X₀ ω) w)| +
      |NTpt θ X₀ ω (t + hh) - NTpt θ X₀ ω t| ≤ 2 * ηV t
  /-- **Step 4** (`Margin.Var.step4` proves it from Lemma 5.21) -/
  hS4 : ∀ t, T0 ≤ t → t ≤ b →
    (oVc θ X₀ ω) t + 2 * ηV t + ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, e t w / KR.Vl (PR θ X₀ ω) w ≤
      p.ES / Real.log t
  /-- the base case below `T₀` -/
  hbase : ∀ t, t < T0 → Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω) t ≤
    Margin.Rec.PhiC (PR θ X₀ ω) p t 1
  /-- **Step 5**: `ε' ≤ 0.045` (the transfer of `A₀(0.045)` to `𝒩`, with the head bound
  `1 + 2.2181`, is then `Margin.Rec.hhead_loc`) -/
  hpε' : p.ε' ≤ 0.045
  /-- **Step 5**: Rankin's tail bound (`τ ≤ 0.06`) -/
  htail : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    ∑ M ∈ ((KR.NAll (PR θ X₀ ω) t (p.Xm / 2)).filter (fun M =>
        Margin.Rec.cutL (PR θ X₀ ω) p M ≤ t / Margin.Rec.Vv (PR θ X₀ ω) M)).filter
        (fun M => ¬ Margin.Rec.Vv (PR θ X₀ ω) M ≤ √t),
      Margin.Rec.Aw (PR θ X₀ ω) p M * (p.ES / Real.log (t / Margin.Rec.Vv (PR θ X₀ ω) M)) ≤
        0.06 * p.ES / Real.log t
  /-- Step 6(a): `M = Bm + B NT_pt + ϑ/H` with `|B NT_pt + ϑ/H| ≤ 54η + 6/H` -/
  hdec : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ t,
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    rhoT θ X₀ ω t + (nuRes hO (twR θ X₀ ω) ρL TcL (JL (jzX X₀) X₀) vtH NT : ℝ → ℝ) t +
      (NT : ℝ → ℝ) t = Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t + Bt t
  hBt : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → |Bt t| ≤ 54 * η t + 6 / Queue6.Hc X₀ t
  hsη : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → Real.log t * η t ≤ sη
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    oTot (Queue6.Hc X₀ t) t (EBR t) (jX t) +
      (a t + bb t + 6 * Real.log t / Queue6.Hc X₀ t) + EBR t + jX t +
      54 * sη + 6 * Real.log t / Queue6.Hc X₀ t + 6.5 * p.ES + VX (PR θ X₀ ω) p t ≤ 0.01
  /-- **Proposition 5.33**: `j_{X₀} ≤ 0.4209` -/
  hjb : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b → (jbc θ X₀ ω) t ≤ 0.4209
  /-- **Proposition 5.38(c)** (Step 6(c)): the source bounds on `[X₀, 2X₀)` -/
  hc : ∀ t, (X₀ : ℝ) ≤ t → t < 2 * X₀ → t ≤ b →
    (∃ Tp, marginM θ X₀ ω t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
    (∃ Tp rt, marginM θ X₀ ω t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
      rt ≤ 0.5001 / Real.log X₀ ∧ Real.log t ≤ Real.log X₀ + 0.7)

/-! ### The open Model inputs -/

variable {θ : ℝ} {X₀ : ℕ}

/-- **`TNP.Hyp` for the realised system** at the Model choices (`Queue6.tnpHyp_R`, with
`PaperWidth` from `paperWidth_Hc`, `capHSlope`, `capHDiff`). -/
theorem tnpR (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) :
    KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10) := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hw : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) epsH (epsH / 10) :=
    KR.WidthReal.paperWidth_Hc hX (by unfold epsH; norm_num) (by unfold epsH; norm_num)
      (CapHSlopeProof.capHSlope hX) (CapHDiffProof.capHDiff hX)
  have h := Queue6.tnpHyp_R hc hev hSG hX1 hbs hw
  rw [← twR_eq hc ω] at h
  exact h

/-- **`RealMarginLoc` from the Model fields and the four groups of the other agents**, on
`Good(< t) ∩ NiceEv` with `X₀ ≤ b ≤ t`. -/
noncomputable def realMarginLoc_of (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hN : ω ∈ NiceEv θ X₀) (hbt : b ≤ t)
    (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hin : BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀))
    (Bs : RestBase θ X₀ ω b) (Br : RestBridge θ X₀ ω b)
    (Rs : RestRes θ X₀ ω b)
    (Mg : RestMargin θ X₀ ω b Br.EBR Br.jX Rs.ρL Rs.TcL Rs.NT Rs.vtH Rs.a Rs.bb) :
    RealMarginLoc hc ω b where
  Z := Zc X₀ b
  η1 := 1 / 1000
  η2 := 1 / 1000
  ε1 := hbsEps X₀
  ε := epsH
  lam0 := lamH
  j0 := jzX X₀
  xmax := b + Queue6.Hc X₀ b
  μ0 := BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
  μ1 := KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
  ρedge := KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
  hbs := hbs
  hSG := hN.2.1
  hX1 := hX1
  hε0 := by norm_num [epsH]
  hε := by norm_num [epsH]
  hSlope := CapHSlopeProof.capHSlope (by linarith)
  hDiff := CapHDiffProof.capHDiff (by linarith)
  hlam := by norm_num [epsH, lamH]
  hlam1 := by norm_num [lamH]
  hTm := measurable_TcR hc ω _
  hTb := fun t ht => TcR_abs_le hc hev ω (tnpR hc hev hbs hN.2.1 hX1) ht
  hj0 := jzX_nonneg hc
  hHux := Bs.hHux
  hin := hin
  hμ0 := BaseRange.mu0R_zero _ _ _ hc.hX
  hμ1 := BaseRange.mu1R_zero _ _ _ _
  hxmax := le_rfl
  hZ := (Zc_facts hc hb).2.2.2
  EBR := Br.EBR
  jX := Br.jX
  EBR_nonneg := Br.EBR_nonneg
  jX_nonneg := Br.jX_nonneg
  x0s := Queue6.x0sHyp_G0 (e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  bridge := Br.bridge
  g1 := Rs.g1
  ρL := Rs.ρL
  hρL := Rs.hρL
  TcL := Rs.TcL
  hTcL := Rs.hTcL
  NT := Rs.NT
  ϑ := Rs.ϑ
  vtH := Rs.vtH
  hvt := Rs.hvt
  hTLBd := Rs.hTLBd
  a := Rs.a
  bb := Rs.bb
  hK := Rs.hK
  hG := Rs.hG
  hϑ := Rs.hϑ
  Bt := Mg.Bt
  η := Mg.η
  sη := Mg.sη
  intm := Mg.intm
  p := Mg.p
  T0 := Mg.T0
  err := Mg.err
  e := Mg.e
  oV := oVc θ X₀ ω
  ηV := Mg.ηV
  chain := Mg.chain
  hpXm := Mg.hpXm
  hpε := Mg.hpε
  hT0 := Mg.hT0
  hT0wf := Mg.hT0wf
  hT0T := Mg.hT0T
  hmbdd := marginM_bdd hc hev ω _
  hρ0 := Mg.hρ0
  hT0' := Mg.hT0'
  hgeom := Mg.hgeom
  s2Q := Queue6.s2Q θ X₀ ω
  s2sl := Queue6.s2sl θ X₀ ω
  s2δ := Queue6.s2δ X₀
  s2ε := Mg.s2ε
  s2mst := Mg.s2mst
  hS2rep := fun z _ s hs0 _ => ⟨Queue6.hS2rep_R hc ω z s z (by linarith), Queue6.hS2rep_R hc ω z s
    (z + s) le_rfl⟩
  hS2w := fun z _ s hs0 hs => Queue6.hS2w_R hc ω hs0 hs
  hS2cp := fun z _ s hs0 hs => (Queue6.hS2c_R hc hev hs0 hs).1
  hS2cm := fun z _ s hs0 hs => (Queue6.hS2c_R hc hev hs0 hs).2
  hS2Ep := Mg.hS2Ep
  hS2Em := Mg.hS2Em
  hS2sp := Mg.hS2sp
  hS2sm := Mg.hS2sm
  hS2δ := fun z _ => div_nonneg (by norm_num) (by unfold Queue6.Hc; exact capH_nonneg _ _)
  hS2H := Mg.hS2H
  hS2mi := Mg.hS2mi
  hS2err := Mg.hS2err
  hS2e := Mg.hS2e
  he0 := Mg.he0
  hoscV := fun t _ htb hh hhh => hoscV_c hc hev ω (tnpR hc hev hbs hN.2.1 hX1) (by linarith)
    (Zc_facts hc hb).2.2.2 htb hhh
  hsw := Mg.hsw
  hS4 := Mg.hS4
  hbase := Mg.hbase
  hpε' := Mg.hpε'
  htail := Mg.htail
  hdec := Mg.hdec
  hBt := Mg.hBt
  hsη := Mg.hsη
  hsmall := Mg.hsmall
  jb := jbc θ X₀ ω
  hsum := by intro t _ _ _; unfold jbc; exact BModel.RML6.hsum_canon _ _ _
  hjb := Mg.hjb
  hc := Mg.hc
  hz := fun t ht => BModel.RML6.marginM_eq_zero_low hc ω ht

/-- **Lemma 7.3's inputs** (`BaseRange.lemma73Inputs_R`) where the (H_BS) horizon reaches `X₀`
(`4X₀ + 2 ≤ b`). -/
theorem hin_R (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hb : (X₀ : ℝ) ≤ b) (hbig : 4 * (X₀ : ℝ) + 2 ≤ b) (hH : BaseRange.HuxleyFrom X₀) :
    BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀) := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hXZ : (X₀ : ℝ) ≤ Zc X₀ b := by unfold Zc; rw [if_pos hbig]; linarith
  have hZ2 := (Zc_facts hc hb).2.2.2
  have hH0 : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
  have hZ' : (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ2
    rw [mul_div_assoc]
    have : 0 ≤ (b + Queue6.Hc X₀ b) / Xm X₀ := div_nonneg (by linarith) hXm0.le
    linarith
  have h := BaseRange.lemma73Inputs_R hc hev hSG hX1 hbs (by norm_num)
    (by norm_num) (CapHSlopeProof.capHSlope hX) (CapHDiffProof.capHDiff hX)
    hH hXZ hZ' (fun v h1 h2 => hbs.err v h1 h2)
  rw [← twR_eq hc ω] at h
  exact h

variable (θ X₀) in
/-- **The inputs owned by the other agents** (the four groups, at the Model choices), at
`(ω, b)`. -/
def OthersInputs (ω : JitterΩ) (b : ℝ) : Prop :=
  ∃ (Bs : RestBase θ X₀ ω b) (Br : RestBridge θ X₀ ω b) (Rs : RestRes θ X₀ ω b),
    Nonempty (RestMargin θ X₀ ω b Br.EBR Br.jX Rs.ρL Rs.TcL Rs.NT Rs.vtH Rs.a Rs.bb)

/-- `RealMarginLoc` from the Model fields and `OthersInputs`. -/
theorem realMarginLoc_of_others (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hN : ω ∈ NiceEv θ X₀) (hbt : b ≤ t)
    (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hin : BaseRange.HuxleyFrom X₀ → BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀))
    (hO : OthersInputs θ X₀ ω b) : Nonempty (RealMarginLoc hc ω b) := by
  obtain ⟨Bs, Br, Rs, ⟨Mg⟩⟩ := hO
  exact ⟨realMarginLoc_of hc hev hG hN hbt hb hbs hX1 (hin Bs.hHux) Bs Br Rs Mg⟩

variable (θ X₀) in
/-- **Lemma 7.3's inputs at the windows with `b < 4X₀ + 2`** (BaseRange): there the
(H_BS) horizon `Zc b = X₀⁻` of `Good(< b)` does not reach `X₀`, which `lemma73Inputs_R` needs. -/
def Lemma73Low (ω : JitterΩ) (b : ℝ) : Prop :=
  b < 4 * (X₀ : ℝ) + 2 → BaseRange.HuxleyFrom X₀ → BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
    (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
    (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
    (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)

/-! ### The top level -/

/-- **Theorem 2.1, hypothesis, final form.** For `X₀ ≥ e^{10⁸+1}` (and `≥ X_Hux`):

* **owned by the other agents**, a.s. on `Good(< b)` for every admissible window `[a, b)`: the
  four groups `RestBase` (§7), `RestBridge` (Proposition 5.18(iii), 5.26, Lemmas 5.27, 5.20),
  `RestRes` (Proposition 5.35, Lemma 5.34), `RestMargin` (Proposition 5.38, steps 1–6), at the
  Model choices. -/
def Theorem21InputsFinal : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8 + 1) ≤ X₀ → XHux ≤ X₀ →
      ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
        ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) →
          Lemma73Low θ X₀ ω b ∧ OthersInputs θ X₀ ω b

/-- `Theorem21InputsFinal` implies `Theorem21InputsZ`, given (84): eq. (s2) is `s2Core`, and
`R1Ident` is `r1Ident_of_marginOn` with Proposition 5.38 on `[X₀, b]` from `RealMarginLoc`
(`hPM_of_loc`), assembled by `realMarginLoc_of`. -/
theorem theorem21InputsZ_final (hHB : ShortIntervalPNT) (h : Theorem21InputsFinal) :
    Theorem21InputsZ := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := hHB
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨max (max XHux x₁) (Real.exp (10 ^ 8 + 1)), fun X₀ hev h1 h2 => ?_⟩
  have h2a : XHux ≤ X₀ := (le_max_left _ _).trans ((le_max_left _ _).trans h2)
  have h2b : x₁ ≤ X₀ := (le_max_right _ _).trans ((le_max_left _ _).trans h2)
  have h2c : Real.exp (10 ^ 8 + 1) ≤ X₀ := (le_max_right _ _).trans h2
  have hRest := hX X₀ hev h2c h2a
  have hlog1 : 10 ^ 8 + 1 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h2c
    rwa [Real.log_exp] at this
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono h2b⟩
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; simpa using this
  have hR : ∀ (m : ℕ) (a b : ℤ), Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Nonempty (RealMarginLoc hc ω (b : ℝ)) := by
    intro m a b hadm
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
    have hb : (X₀ : ℝ) ≤ b := (X₀_le_uS (X₀ := X₀) (by linarith) m).trans hadm.1
    filter_upwards [hRest m a b hadm, hnice] with ω hω hN hG
    have hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat := hG.1
    have hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n := fun n hn =>
      mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
    obtain ⟨hlow, hO⟩ := hω hG
    have hbs := hbs_Zc hc hev hb hQC hE1 hN
    have hb0 : (0 : ℤ) ≤ b := by
      have : (0 : ℝ) ≤ b := le_trans hX0 hb
      exact_mod_cast this
    have hbt : (b : ℝ) ≤ ((tE2 b : ℕ) : ℝ) := by
      unfold tE2; rw [show ((b.toNat : ℕ) : ℝ) = (b : ℝ) by exact_mod_cast Int.toNat_of_nonneg hb0]
    refine realMarginLoc_of_others hc hev hG hN hbt hb hbs hlog1 (fun hH => ?_) hO
    rcases le_or_gt (4 * (X₀ : ℝ) + 2) b with hbig | hsmall
    · exact hin_R hc hev hbs hN.2.1 hlog1 hb hbig hH
    · exact hlow hsmall hH
  have hcore := s2Core hc hev
  exact ⟨{ compE3 := e3CompBound hc hev
           s2E3 := e3S2Bound_of hc hev hcore
           r1Ident := r1Ident_of_marginOn hc hev (e3Family θ X₀) (hPM_of_loc hc hev _ hR)
           s2E2 := e2S2Bound_of hc hev hcore }⟩

/-- **Corollary 2.2** from (84) and `Theorem21InputsFinal`. -/
theorem corollary_2_2_final (hHB : ShortIntervalPNT) (h : Theorem21InputsFinal) :
    ¬ QuestionQ :=
  corollary_2_2_of_Z hHB (theorem21InputsZ_final hHB h)

end BModel
