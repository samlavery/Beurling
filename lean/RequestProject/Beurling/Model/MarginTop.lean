module

public import RequestProject.Beurling.Model.MarginMine
public import RequestProject.Beurling.Model.S2Final
public import RequestProject.Beurling.Model.Wire3
public import RequestProject.Beurling.Model.SigmaResp
public import RequestProject.Beurling.Model.OscBound
public import RequestProject.Beurling.Model.BtNT
public import RequestProject.Beurling.Model.G1BWire
public import RequestProject.Beurling.Model.G1BJumpProof
public import RequestProject.Beurling.Model.G1BRprime
public import RequestProject.Beurling.Model.JXbdd
public import RequestProject.Beurling.Noise.RML6G1
public import RequestProject.Beurling.BaseRange.Lemma73Low
public import RequestProject.Beurling.BaseRange.MarginHc

/-!
# The final assembly: Theorem 2.1 / Corollary 2.2 from (84) and the open inputs

The local Proposition 5.38 (`BModel.pointwiseMarginOn_of_loc`, from `RealMarginLoc`) and the
proved eq. (s2) (`BModel.s2Core`) give `Theorem21InputsZ`, hence Corollary 2.2.

The fields of `RealMarginLoc` are split as follows.

* **Proved here** (Model): `hbs` (`hbs_Zc`: (H_BS) on `[1, Zc b]` on `Good(< b)`), `hSG`
  (`NiceEv`), `hX1` (`log X₀ ≥ 10⁸ + 1`, from `X₀ ≥ e^{10⁸+1}`), the horizon `Z = Zc b` with
  `hZ` (`2(b + H(b))/X₀⁻ ≤ Z`) and the Z conditions of the bridge (`Zc_facts`: `2500 ≤ Z`,
  `18(b + H(b)) ≤ Z²`, `X₀⁻ ≤ Z`), `η₁ = η₂ = 10⁻³`, `ε₁ = hbsEps`, `ε = 4·10⁻⁶` (`hε0`, `hε`),
  `λ₀ = 1.00003` (`hlam`, `hlam1`), `j₀ = 1 - ρ_det(X₀)` (`hj0`, from (84) via
  `Model.rhoDet_le`), `xmax = b + H(b)` (`hxmax`), and
  `hDiff` (`CapHDiffProof.capHDiff`, `Model/CapHDiff.lean`: `H` is differentiable off a
  countable set, §5.1 "`H` is piecewise smooth").
* **Proved here** as well: `hSlope`, `hDiff`, `hTm`, `hTb`, `hosc` (eq. (osc)), `hbdd`,
  `jX_nonneg`, `η`, `sη`, `intm`, `hBt` (Step 6(a), eq. (NT)), and the Model fields of
  `G1BInputs` (Proposition 5.35(B)).
* **Taken as arguments**: `hin` (Lemma 7.3's inputs) and `hjbA` (`j_{X₀} ≤ 0.4209`,
  Proposition 5.33), proved by BaseRange in files importing this one.
* **Open, owned by the other agents**, grouped by paper section, with the Model choices
  substituted: `RestBase` (§7: (huxley)), `RestBridge` (now empty), `RestRes` (Proposition
  5.35, Lemma 5.34, the margin identity), `RestMargin` (Proposition 5.38, steps 1–6).

The top level (`corollary_2_2_hux : Huxley84 → Theorem21InputsH → ¬ QuestionQ`) is in
`Model/MarginFinal.lean`.
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
`RealMarginLoc`, at the Model choices `Z = Zc b`, `ε = 4·10⁻⁶`, `λ₀ = 1.00003`, `j₀ = jzX X₀`. -/
structure RestBridge (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where


/-- **Proposition 5.35, Lemma 5.34 and the margin identity** inputs of `RealMarginLoc`. -/
structure RestRes (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where
  /-- **Proposition 5.35(B)**'s non-Model inputs on range (B) (`KR.RML6.G1BRest`: Queue6's
  Step 1 count and Lemma 5.23 at `2δ`, §5's Step 2), at the Model's `δ = deltaB`, `ρ̃ = rhoT` and
  threshold mass `threshSum tJ y (2δ)` -/
  g1B : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b → (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y →
    KR.RML6.G1BRest (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
      (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * ind X₀ t) y (deltaB θ X₀ ω y) (rhoT θ X₀ ω)
      ((PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y))
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
structure RestMargin (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) (a : ℝ → ℝ) (bb : ℝ → ℝ) where
  /-- **Steps 1–5**: the parameters of the recursion and its super-solution -/
  p : Margin.Rec.CP
  T0 : ℝ
  e : ℝ → ℕ → ℝ
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
  s2mst : ℝ → ℝ
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
  /-- **Step 3**, the recursion weights: `(fun z => 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3
  X₀ (uS X₀ (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 +
    (6.6 + 4.2 * s2mst z) / Queue6.Hc X₀ z)(z') ≤ e(t, w)` on the strip of `(t, w)` -/
  hS2e : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, ∀ z',
    t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
      z' ≤ t / KR.Vl (PR θ X₀ ω) w → (fun z => 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀
        (uS X₀ (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 +
          (6.6 + 4.2 * s2mst z) / Queue6.Hc X₀ z) z' ≤ e t w
  he0 : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, 0 ≤ e t w
  /-- **Step 4** (`Margin.Var.step4` proves it from Lemma 5.21) -/
  hS4 : ∀ t, T0 ≤ t → t ≤ b →
    (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω p) t + ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, e t w / KR.Vl
      (PR θ X₀ ω) w ≤
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
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    oTot (Queue6.Hc X₀ t) t ((fun _ => EBRc) t) ((fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀)
      (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t) +
      (a t + bb t + 6 * Real.log t / Queue6.Hc X₀ t) + (fun _ => EBRc) t + (fun x => jXdef
        (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t +
      54 * (sηB X₀) + 6 * Real.log t / Queue6.Hc X₀ t + 6.5 * p.ES + VX (PR θ X₀ ω) p t ≤ 0.01
  /-- Step 6(b), "Sum" -/
  hsum : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
    rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω (jzX X₀) s +
      (jzX X₀) * ind X₀ s) *
      Real.log t - (fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀
        (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t - 1 / 10 ^ 12 ≤ marginM θ X₀ ω t * Real.log t

/-! ### The open Model inputs -/

variable {θ : ℝ} {X₀ : ℕ}

/-- **`RealMarginLoc` from the Model fields and the four groups of the other agents**, on
`Good(< t) ∩ NiceEv` with `X₀ ≤ b ≤ t`. -/
noncomputable def realMarginLoc_of (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hN : ω ∈ NiceEv θ X₀) (hbt : b ≤ t)
    (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hEpm : ∀ z s : ℝ, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z → max z X₀ + 2 * Queue6.Hc X₀ z ≤ t →
      |Margin.Exact.sigmaS (Queue6.s2Q θ X₀ ω z s) (Queue6.s2sl θ X₀ ω z s)
          (Margin.Exact.Aplus (Queue6.Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ Queue6.s2ε X₀ z ∧
      |Margin.Exact.sigmaS (Queue6.s2Q θ X₀ ω z s) (Queue6.s2sl θ X₀ ω z s)
          (Margin.Exact.Aminus (Queue6.Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ Queue6.s2ε X₀ z)
    (hin : BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀))
    (hjbA : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ≤ 0.4209)
    (Bs : RestBase θ X₀ ω b) (Br : RestBridge θ X₀ ω b)
    (Rs : RestRes θ X₀ ω b)
    (Mg : RestMargin θ X₀ ω b Rs.a Rs.bb) :
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
  EBR := fun _ => EBRc
  jX := fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH
    (jzX X₀) (NKc X₀) x
  EBR_nonneg := fun _ => (Real.exp_pos _).le
  jX_nonneg := jXnn_c hc hev (tnpR hc hev hbs hN.2.1 hX1) (by norm_num [lamH]) (jzX_nonneg hc)
    (NKc X₀)
  x0s := Queue6.x0sHyp_G0 (e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  bridge := fun x y hx hxb hW => bridge_c hc hev hb hbs hN.2.1 hX1 hx hxb hW
    (hosc_c hc hev hb hbt hG.1 (fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn) hN
      (tnpR hc hev hbs hN.2.1 hX1) hx hxb hW) (hbdd_c hc hev hb
        (tnpR hc hev hbs hN.2.1 hX1) x hx hxb)
  g1 := fun y hy hyb => KR.RML6.g1_of (by norm_num at hX1 ⊢; linarith) (Xm_pos' hc)
    (Xm_le_X0 hc) hy (sigmaAResp_R hc hev hb hbt hG.1 (fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG
      (Sum.inl n) hn) hN hbs hX1 hy hyb) (fun hyL => g1B_mk hc hev hb hbt hG.1
        (fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn) hN
          (tnpR hc hev hbs hN.2.1 hX1) hy hyb hyL (jumpCount_c hc hev hb hbt hG.1
            (fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn) hN hy hyb hyL)
              (rprimeChange_c hc ω hb (tnpR hc hev hbs hN.2.1 hX1) hy hyb) (Rs.g1B y hy hyb hyL))
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
  Bt := Btc θ X₀ ω (opR hc hev hbs hN.2.1 hX1) Rs.ρL Rs.TcL Rs.vtH Rs.NT
  η := ηB θ X₀ ω
  sη := sηB X₀
  intm := intm_c hc hev ω
  p := Mg.p
  T0 := Mg.T0
  err := fun z => 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀ (uS X₀
    (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 +
      (6.6 + 4.2 * Mg.s2mst z) / Queue6.Hc X₀ z
  e := Mg.e
  oV := oVc θ X₀ ω
  ηV := ηVc θ X₀ ω Mg.p
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
  s2ε := Queue6.s2ε X₀
  s2mst := Mg.s2mst
  hS2rep := fun z _ s hs0 _ => ⟨Queue6.hS2rep_R hc ω z s z (by linarith), Queue6.hS2rep_R hc ω z s
    (z + s) le_rfl⟩
  hS2w := fun z _ s hs0 hs => Queue6.hS2w_R hc ω hs0 hs
  hS2cp := fun z _ s hs0 hs => (Queue6.hS2c_R hc hev hs0 hs).1
  hS2cm := fun z _ s hs0 hs => (Queue6.hS2c_R hc hev hs0 hs).2
  hS2Ep := fun z hz s hs0 hs => (hS2E_field hc ω hb hbt (KR.Chain.p_ge_two_of
    (tnpR hc hev hbs hN.2.1 hX1) (Xm_le_Zc' hc b)) hEpm Mg.p Mg.T0 z hz s hs0 hs).1
  hS2Em := fun z hz s hs0 hs => (hS2E_field hc ω hb hbt (KR.Chain.p_ge_two_of
    (tnpR hc hev hbs hN.2.1 hX1) (Xm_le_Zc' hc b)) hEpm Mg.p Mg.T0 z hz s hs0 hs).2
  hS2sp := Mg.hS2sp
  hS2sm := Mg.hS2sm
  hS2δ := fun z _ => div_nonneg (by norm_num) (by unfold Queue6.Hc; exact capH_nonneg _ _)
  hS2H := Mg.hS2H
  hS2mi := Mg.hS2mi
  hS2err := fun z _ => Queue6.hS2err_R hc z (Mg.s2mst z)
  hS2e := Mg.hS2e
  he0 := Mg.he0
  hoscV := fun t _ htb hh hhh => hoscV_c hc hev ω (tnpR hc hev hbs hN.2.1 hX1) (by linarith)
    (Zc_facts hc hb).2.2.2 htb hhh
  hsw := fun t _ htb hh hhh => hsw_c hc hev ω Mg.p htb hhh
  hS4 := Mg.hS4
  hbase := Mg.hbase
  hpε' := Mg.hpε'
  htail := Mg.htail
  hdec := fun hO t _ _ => hdec_c ω (opR hc hev hbs hN.2.1 hX1) Rs.ρL Rs.TcL Rs.vtH Rs.NT hO t
  hBt := hBt_c hc hev ω
    (opR hc hev hbs hN.2.1 hX1) Rs.ρL Rs.TcL Rs.vtH Rs.NT Rs.hρL Rs.hTcL Rs.hvt Rs.hϑ
  hsη := hsη_c hc hev ω hb (tnpR hc hev hbs hN.2.1 hX1)
  hsmall := Mg.hsmall
  jb := fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH
    (jzX X₀) (NKc X₀) x
  hsum := Mg.hsum
  hjb := hjbA
  hc := BaseRange.margin_hc hc hev Bs.hHux ω b
  hz := fun t ht => BModel.RML6.marginM_eq_zero_low hc ω ht

/-- **Lemma 7.3's inputs** (`BaseRange.lemma73Inputs_R'`, with (H_BS) on `[1, Zc b]`,
`X₀⁻ ≤ Zc b`). -/
theorem hin_R (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hb : (X₀ : ℝ) ≤ b) (hH : BaseRange.HuxleyFrom X₀) :
    BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀) := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hZ2 := (Zc_facts hc hb).2.2.2
  have hH0 : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
  have hZ' : (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ2
    rw [mul_div_assoc]
    have : 0 ≤ (b + Queue6.Hc X₀ b) / Xm X₀ := div_nonneg (by linarith) hXm0.le
    linarith
  have h := BaseRange.lemma73Inputs_R' hc hev hSG hX1 hbs (by norm_num)
    (by norm_num) (CapHSlopeProof.capHSlope hX) (CapHDiffProof.capHDiff hX)
    hH (Xm_le_Zc' hc b) hZ' (fun v h1 h2 => hbs.err v h1 h2)
  rw [← twR_eq hc ω] at h
  exact h

variable (θ X₀) in
/-- **The inputs owned by the other agents** (the four groups, at the Model choices), at
`(ω, b)`. -/
def OthersInputs (ω : JitterΩ) (b : ℝ) : Prop :=
  ∃ (Bs : RestBase θ X₀ ω b) (Br : RestBridge θ X₀ ω b) (Rs : RestRes θ X₀ ω b),
    Nonempty (RestMargin θ X₀ ω b Rs.a Rs.bb)

/-- `RealMarginLoc` from the Model fields and `OthersInputs`. -/
theorem realMarginLoc_of_others (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hN : ω ∈ NiceEv θ X₀) (hbt : b ≤ t)
    (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hEpm : ∀ z s : ℝ, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z → max z X₀ + 2 * Queue6.Hc X₀ z ≤ t →
      |Margin.Exact.sigmaS (Queue6.s2Q θ X₀ ω z s) (Queue6.s2sl θ X₀ ω z s)
          (Margin.Exact.Aplus (Queue6.Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ Queue6.s2ε X₀ z ∧
      |Margin.Exact.sigmaS (Queue6.s2Q θ X₀ ω z s) (Queue6.s2sl θ X₀ ω z s)
          (Margin.Exact.Aminus (Queue6.Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ Queue6.s2ε X₀ z)
    (hin : BaseRange.HuxleyFrom X₀ → BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
      (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
      (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀))
    (hjbA : BaseRange.HuxleyFrom X₀ → ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ≤ 0.4209)
    (hO : OthersInputs θ X₀ ω b) : Nonempty (RealMarginLoc hc ω b) := by
  obtain ⟨Bs, Br, Rs, ⟨Mg⟩⟩ := hO
  exact ⟨realMarginLoc_of hc hev hG hN hbt hb hbs hX1 hEpm (hin Bs.hHux) (hjbA Bs.hHux) Bs Br Rs
    Mg⟩

variable (θ X₀) in
/-- **Lemma 7.3's inputs at the windows with `b < 4X₀ + 2`** (kept for `BaseRange.lemma73Low_of`;
the top level now uses `hin_R` for every `b`). -/
def Lemma73Low (ω : JitterΩ) (b : ℝ) : Prop :=
  b < 4 * (X₀ : ℝ) + 2 → BaseRange.HuxleyFrom X₀ → BaseRange.Lemma73Inputs X₀ (b + Queue6.Hc X₀ b)
    (BaseRange.mu0R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
    (KR.Sharp.mu1R (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)
    (KR.Sharp.rhoEdge (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀)

end BModel
