module

public import RequestProject.Beurling.Noise.MarginChainLoc
public import RequestProject.Beurling.Noise.MarginRealTop
public import RequestProject.Beurling.Noise.MarginInt
public import RequestProject.Beurling.Noise.KRTrueX0

/-!
# Proposition 5.38 on `[X₀, b]` for the margin density of the construction

The top level (`BModel.r1Ident_of_marginOn`, `corollary_2_2_of_MOn`, `MarginRealTop.lean`) needs
`PointwiseMarginOn (marginM θ X₀ ω) X₀ b` a.s. on `Good(< b)`. This file instantiates the local
chain `KR.Chain.ChainInputsLoc` (`MarginChainLoc.lean`) for

* `P = PR θ X₀ ω` (the realised system), `H = Hc X₀ = capH X₀ (max · X₀)`, `X₀⁻ = Xm X₀`,
* `tw = twR θ X₀ ω` (`MarginObjects`; equal to `Queue6.twR` by `BModel.twR_eq`),
* `m = marginM θ X₀ ω`, `ρ̃ = rhoT`, `NT_pt = NTpt`, `K_pt = KptR`, and the effective source
  `T' = T'_cont + K_𝒜 ρ̃` split as `T_c + j₀ 1_{[X₀,∞)}` (§5.1),

and proves the following fields (`RealMarginLoc.toCI`):

* `TNP.Hyp` (`Queue6.tnpHyp_R`, from (HBS), `ω ∈ SG` and `PaperWidth`), with `PaperWidth` from
  `KR.WidthReal.paperWidth_Hc` (inputs `CapHSlope`, `CapHDiff`), `θ = ε/10`;
* `X₀⁻ = X₀ - H(X₀)/2`, `log X₀ ≥ 10⁸`, prime values `≥ 2`, the decision order `t > 0`,
  `p ≤ 2t(p)` (`dec_R`, from `dec_hi`/`dec_lo` and `H(y) ≤ y/10`);
* the window integrability of `R_res T'`, `ρ^sh T'` (`KR.Int.intRT_of`, `intRS_of`);
* `m = T' - K_pt ρ̃ - NT_pt` (`BModel.marginM_eq`);
* step (iii) of Proposition 5.18, `EtaX0Sum` on the dyadic scales (`KR.X0S.Hyp.etaX0Sum_of`,
  `dyScales_dyadic`), from the window count of `KR.X0S.Hyp`.

The remaining inputs are the fields of `RealMarginLoc`, each citing the paper statement it is.
eq. (NT) is not used in this form: `NT_pt` enters through the filter switching `hsw` and the
Step 6(a) decomposition `hdec`/`hBt`.

Main result: `BModel.pointwiseMarginOn_of_loc`, and `BModel.hPM_of_loc`, the hypothesis `hPM` of
`r1Ident_of_marginOn`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP

namespace KR.Chain

lemma dyScales_dyadic {X0 x : ℝ} {N : ℕ} : KR.X0S.Dyadic X0 (dyScales X0 x N) := by
  intro v hv
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
  refine ⟨(k : ℤ) - 2, ?_⟩
  rw [zpow_sub₀ (by norm_num), zpow_natCast]
  norm_num
  ring

/-- The decision order from `TNP.Hyp`: `t > 0` and `p ≤ 2t(p)` on the prime labels. -/
lemma dec_R {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    {ε θ : ℝ} (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) :
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

end KR.Chain

namespace BModel

open KR.Chain

variable {θ : ℝ} {X₀ : ℕ}

/-- The part `T_c` of the effective source `T' = T'_cont + K_𝒜 ρ̃` off the jump at `X₀`
(§5.1, "The jump at `X₀`"). -/
noncomputable def TcR (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (j0 : ℝ) (y : ℝ) : ℝ :=
  TpCont θ X₀ ω y + KAbsR θ X₀ ω (rhoT θ X₀ ω) y - j0 * ind X₀ y

/-- **The bridge data at a start `y`** for the realised system: the dyadic scales, the
oscillation and the size relations of `BridgeAt2` (with `s⁰ = sX0 X₀` of step (iii)), and the
conclusions of Lemma 5.20 at `y`. -/
structure BridgeR (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 : ℝ)
    (Tc : ℝ → ℝ) (j0 y EBR j : ℝ) where
  N : ℕ
  K : ℕ
  hN2 : 2 < N
  hN : y < X0 * 2 ^ N / 4
  hK : √(2 * y) ≤ TNP.Pk X0m K
  o : ℝ → ℝ
  /-- **Proposition 5.18, step (iii)**, unweighted: `∑_v s⁰_v ≤ 1.52` (used in Lemma 5.27) -/
  etaX0Sum : ∑ v ∈ dyScales X0 y N, KR.X0S.sX0 X0 v ≤ 1.52
  /-- the oscillation of `T_c` (eq. (osc)) -/
  osc : OscBound P H y Tc (dyScales X0 y N) o
  /-- the terminal oscillation (proof of Proposition 5.26, second bullet) -/
  termOsc : TermOsc P H tw X0m y Tc (o X0)
  /-- `E_BR` bounds the right side of Proposition 5.26 -/
  sizeE : (5.1 * CNc X0 + CSc) * ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u +
      8.4 * CNc X0 * ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * TNP.sTheta P H X0m K v ≤ EBR
  /-- eq. (jX0) -/
  sizeJ : j0 * (xbB P H tw X0m y X0 θ lam0 +
      4.3 * CNc X0 * (∑ v ∈ dyScales X0 y N, Real.log (2 * v) * TNP.sTheta P H X0m K v) /
        Real.log y) * Real.log y ≤ j
  /-- **Lemma 5.20** at `y` -/
  l520 : L520At P H tw X0m X0 lam0 y N K

/-- **The remaining inputs of Proposition 5.38 on `[X₀, b]` for the construction.**
Notation: `P = PR θ X₀ ω`, `H = Hc X₀`, `X₀⁻ = Xm X₀`, `tw = twR θ X₀ ω`, `ρ̃ = rhoT θ X₀ ω`,
`m = marginM θ X₀ ω`, `T_c = TcR θ X₀ ω j₀`, `θ_H = ε/10`, `X₁ = X₀^{1.01}`. -/
structure RealMarginLoc (hc : Cond θ X₀) (ω : JitterΩ) (b : ℝ) where
  Z : ℝ
  η1 : ℝ
  η2 : ℝ
  ε1 : ℝ → ℝ
  ε : ℝ
  lam0 : ℝ
  j0 : ℝ
  xmax : ℝ
  μ0 : ℝ → ℝ
  μ1 : ℝ → ℝ
  ρedge : ℝ → ℝ
  θo : ℝ
  /-- **(HBS)** on `[1, Z]` (§5.2; on `Good(< b)` from `BModel.hbs_local`) -/
  hbs : (PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1
  /-- `ω ∈ SG` (the stage-good event of `Queue6`, used for Corollary 6.3(ii)) -/
  hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)
  hX1 : 10 ^ 8 + 1 ≤ Real.log X₀
  hε0 : 0 ≤ ε
  hε : ε ≤ 4 / 1000000
  /-- **(R_H)** for `capH` on `[X₀, ∞)` (§5.1, Theorem 6.23(c)) -/
  hSlope : KR.WidthReal.CapHSlope X₀ ε
  /-- `capH` is differentiable off a countable set (`WidthReg`) -/
  hDiff : KR.WidthReal.CapHDiff X₀
  hlam : 1 + 3 * (ε / 10) ≤ lam0
  hlam1 : lam0 ≤ 1.001
  /-- `T_c` measurable, `|T_c| ≤ 2` (§5.1: `|T'| ≤ 2`) -/
  hTm : Measurable (TcR θ X₀ ω j0)
  hTb : ∀ t, |TcR θ X₀ ω j0 t| ≤ 2
  hj0 : 0 ≤ j0
  /-- (huxley) and Lemma 7.3's inputs (§7) -/
  hHux : BaseRange.HuxleyFrom X₀
  hin : BaseRange.Lemma73Inputs X₀ xmax μ0 μ1 ρedge
  hμ0 : ∀ u : ℝ, u < X₀ → μ0 u = 0
  hμ1 : ∀ u : ℝ, u < X₀ → μ1 u = 0
  hxmax : b + Queue6.Hc X₀ b ≤ xmax
  /-- the cofactor horizon of (HBS) -/
  hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z
  EBR : ℝ → ℝ
  jX : ℝ → ℝ
  EBR_nonneg : ∀ x, 0 ≤ EBR x
  jX_nonneg : ∀ x, 0 ≤ jX x
  /-- **Proposition 5.18, step (iii)**, the window count (Corollary 3.8, target (6),
  Lemma 6.26) and the growth `H ≤ y^{1/8}` (`KR.X0S.Hyp`) -/
  x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θo
  /-- **Proposition 5.26, Lemma 5.27, Lemma 5.20** at the starts of the windows of the centres
  `X₁ ≤ x ≤ b` -/
  bridge : ∀ x y, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → InW (Queue6.Hc X₀ x) x y →
    BridgeR (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
      (TcR θ X₀ ω j0) j0 y (EBR x) (jX x)
  /-- **Proposition 5.35**, residual inputs, at `X₀ ≤ y ≤ b + H(b)` -/
  g1 : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b →
    G1At (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ μ0 μ1 ρedge
      (fun t => TcR θ X₀ ω j0 t + j0 * ind X₀ t) y
  -- **Lemma 5.34**
  B : (ℝ → ℝ) →+ (ℝ → ℝ)
  K : (ℝ → ℝ) →+ (ℝ → ℝ)
  R : (ℝ → ℝ) →+ (ℝ → ℝ)
  /-- `R_res` inverts `1 + K_pt B` (§5.3) -/
  hR : ∀ g, R g + K (B (R g)) = g
  /-- the push-through form determines `ρ̃` (§5.3) -/
  hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f'
  ν : ℝ → ℝ
  NT : ℝ → ℝ
  ϑ : ℝ → ℝ
  /-- the margin identity (Proposition 5.11 with (Ttilde)) -/
  hmargin : rhoT θ X₀ ω + B (K (rhoT θ X₀ ω)) = B (TcR θ X₀ ω j0 + fun t => j0 * ind X₀ t) +
    (fun z => ϑ z / Queue6.Hc X₀ z) - ν - NT
  /-- `B` is the window average -/
  hBx : ∀ g x, B g x = Margin.Bavg (Queue6.Hc X₀ x) g x
  /-- `R` is the long operator on `T'` -/
  hRres : R (TcR θ X₀ ω j0 + fun t => j0 * ind X₀ t) =
    fun y => Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) y
      (fun t => TcR θ X₀ ω j0 t + j0 * ind X₀ t)
  a : ℝ → ℝ
  bb : ℝ → ℝ
  /-- Lemma 5.34, first bullet (from Proposition 5.18) -/
  hK : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → Real.log x *
    |B (K (B (R ((B (TcR θ X₀ ω j0) - TcR θ X₀ ω j0) + (fun z => ϑ z / Queue6.Hc X₀ z) - ν -
      NT)))) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → Real.log x *
    |B (R (K ((B (TcR θ X₀ ω j0 + fun t => j0 * ind X₀ t) + (fun z => ϑ z / Queue6.Hc X₀ z) -
        ν - NT - B (fun t => j0 * ind X₀ t)) -
      B (B (TcR θ X₀ ω j0 + fun t => j0 * ind X₀ t) + (fun z => ϑ z / Queue6.Hc X₀ z) - ν -
        NT - B (fun t => j0 * ind X₀ t))))) x| ≤ bb x
  /-- `|ϑ| ≤ 6` (eq. (Ttilde)) -/
  hϑ : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → |ϑ x| ≤ 6
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
  oV : ℝ → ℝ
  ηV : ℝ → ℝ
  chain : Margin.Rec.ChainHyp (PR θ X₀ ω) p (Queue6.Hc X₀)
  hpXm : p.Xm = Xm X₀
  hpε : p.ε ≤ 0.01
  hT0 : p.cinf + p.Kc ≤ T0
  hT0wf : 2 ≤ T0 * (1 - p.θ0)
  hT0T : T0 ≤ b
  /-- `m` is bounded -/
  hmbdd : ∃ C, ∀ y, |marginM θ X₀ ω y| ≤ C
  /-- `ρ̃ = 0` below `X₀⁻` (the slots are `≥ X₀`, §5.1) -/
  hρ0 : ∀ z, z < Xm X₀ → rhoT θ X₀ ω z = 0
  hT0' : ∀ t, T0 ≤ t → t ≤ b → 0 ≤ t ∧ 1.01 * Queue6.Hc X₀ t ≤ t
  /-- `H`-regularity at a cofactor (`HStep`) -/
  hgeom : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
    Margin.Rec.HStep (Queue6.Hc X₀) p.ε t (t / KR.Vl (PR θ X₀ ω) w) (KR.Vl (PR θ X₀ ω) w)
  /-- **Step 2** (`Step2At`: the exact form `MarginExact.step2_exact_bullet` with the weights
  and slot counts, Lemma 5.22 on `A±`, the strip comparison) -/
  hS2 : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, ∀ z',
    t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
      z' ≤ t / KR.Vl (PR θ X₀ ω) w →
        Margin.Rec.Step2At (Queue6.Hc X₀) (rhoT θ X₀ ω)
          (Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω)) err z' ∧ err z' ≤ e t w
  he0 : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, 0 ≤ e t w
  /-- the oscillation of `T'` (eq. (osc)) -/
  hoscV : ∀ t, T0 ≤ t → t ≤ b → ∀ hh, |hh| ≤ 1.01 * Queue6.Hc X₀ t →
    |(TcR θ X₀ ω j0 (t + hh) + j0 * ind X₀ (t + hh)) - (TcR θ X₀ ω j0 t + j0 * ind X₀ t)| ≤
      oV t
  /-- filter switching and `ΔNT_pt ≤ 2η` -/
  hsw : ∀ t, T0 ≤ t → t ≤ b → ∀ hh, |hh| ≤ 1.01 * Queue6.Hc X₀ t →
    |∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
        (Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) (t + hh) w -
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w) *
        (rhoT θ X₀ ω ((t + hh) / KR.Vl (PR θ X₀ ω) w) / KR.Vl (PR θ X₀ ω) w)| +
      |NTpt θ X₀ ω (t + hh) - NTpt θ X₀ ω t| ≤ 2 * ηV t
  /-- **Step 4** (`Margin.Var.step4` proves it from Lemma 5.21) -/
  hS4 : ∀ t, T0 ≤ t → t ≤ b →
    oV t + 2 * ηV t + ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, e t w / KR.Vl (PR θ X₀ ω) w ≤
      p.ES / Real.log t
  /-- the base case below `T₀` -/
  hbase : ∀ t, t < T0 → Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω) t ≤
    Margin.Rec.PhiC (PR θ X₀ ω) p t 1
  /-- **Step 5**: the transfer of `A₀(0.045)` to `𝒩` -/
  hhead : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    ∑ M ∈ ((KR.NAll (PR θ X₀ ω) t (p.Xm / 2)).filter (fun M =>
        Margin.Rec.cutL (PR θ X₀ ω) p M ≤ t / Margin.Rec.Vv (PR θ X₀ ω) M)).filter
        (fun M => Margin.Rec.Vv (PR θ X₀ ω) M ≤ √t),
      Margin.Rec.Aw (PR θ X₀ ω) p M ≤ 1 + BSCert.Consts.ordA 1.955
  /-- **Step 5**: Rankin's tail bound (`τ ≤ 0.06`) -/
  htail : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    ∑ M ∈ ((KR.NAll (PR θ X₀ ω) t (p.Xm / 2)).filter (fun M =>
        Margin.Rec.cutL (PR θ X₀ ω) p M ≤ t / Margin.Rec.Vv (PR θ X₀ ω) M)).filter
        (fun M => ¬ Margin.Rec.Vv (PR θ X₀ ω) M ≤ √t),
      Margin.Rec.Aw (PR θ X₀ ω) p M * (p.ES / Real.log (t / Margin.Rec.Vv (PR θ X₀ ω) M)) ≤
        0.06 * p.ES / Real.log t
  /-- Step 6(a): `M = Bm + B NT_pt + ϑ/H` with `|B NT_pt + ϑ/H| ≤ 54η + 6/H` -/
  hdec : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    rhoT θ X₀ ω t + ν t + NT t = Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t + Bt t
  hBt : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → |Bt t| ≤ 54 * η t + 6 / Queue6.Hc X₀ t
  hsη : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → Real.log t * η t ≤ sη
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    oTot (Queue6.Hc X₀ t) t (EBR t) (jX t) +
      (a t + bb t + 6 * Real.log t / Queue6.Hc X₀ t) + EBR t + jX t +
      54 * sη + 6 * Real.log t / Queue6.Hc X₀ t + 6.5 * p.ES + VX (PR θ X₀ ω) p t ≤ 0.01
  -- **Proposition 5.38(b)**
  jb : ℝ → ℝ
  /-- Step 6(b), "Sum" -/
  hsum : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
    rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω j0 s + j0 * ind X₀ s) *
      Real.log t - jb t - 1 / 10 ^ 12 ≤ marginM θ X₀ ω t * Real.log t
  /-- **Proposition 5.33**: `j_{X₀} ≤ 0.4209` -/
  hjb : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b → jb t ≤ 0.4209
  /-- **Proposition 5.38(c)** (Step 6(c)): the source bounds on `[X₀, 2X₀)` -/
  hc : ∀ t, (X₀ : ℝ) ≤ t → t < 2 * X₀ → t ≤ b →
    (∃ Tp, marginM θ X₀ ω t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
    (∃ Tp rt, marginM θ X₀ ω t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
      rt ≤ 0.5001 / Real.log X₀ ∧ Real.log t ≤ Real.log X₀ + 0.7)
  /-- `m = 0` below `X₀` -/
  hz : ∀ t : ℝ, t < X₀ → marginM θ X₀ ω t = 0

namespace RealMarginLoc

variable {hc : Cond θ X₀} {ω : JitterΩ} {b : ℝ}

lemma hX (R : RealMarginLoc hc ω b) : 10 ^ 8 ≤ Real.log X₀ := by linarith [R.hX1]

/-- `PaperWidth` for `Hc X₀`. -/
lemma width (R : RealMarginLoc hc ω b) :
    KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) R.ε (R.ε / 10) :=
  KR.WidthReal.paperWidth_Hc R.hX R.hε0 R.hε R.hSlope R.hDiff

/-- `TNP.Hyp` for the realised system (`Queue6.tnpHyp_R`), with `tw = twR`. -/
lemma tnp (R : RealMarginLoc hc ω b) (hev : Even X₀) :
    KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) R.Z R.η1 R.η2 R.ε1 R.ε
      (R.ε / 10) := by
  rw [twR_eq hc ω]
  exact Queue6.tnpHyp_R hc hev R.hSG R.hX1 R.hbs R.width

lemma hX0e (_R : RealMarginLoc hc ω b) :
    Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
  unfold Xm Queue6.Hc; rw [max_self]

/-- `T_c + j₀ 1_{[X₀,∞)} = T'_cont + K_𝒜 ρ̃`. -/
lemma Tp_eq (R : RealMarginLoc hc ω b) (y : ℝ) :
    TcR θ X₀ ω R.j0 y + R.j0 * ind X₀ y = TpCont θ X₀ ω y + KAbsR θ X₀ ω (rhoT θ X₀ ω) y := by
  unfold TcR; ring

/-- **The local chain inputs for the construction**. -/
noncomputable def toCI (R : RealMarginLoc hc ω b) (hev : Even X₀) :
    ChainInputsLoc (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ R.Z R.η1 R.η2 R.ε1 R.ε
      (R.ε / 10) R.lam0 (TcR θ X₀ ω R.j0) R.j0 R.xmax R.μ0 R.μ1 R.ρedge (marginM θ X₀ ω) b where
  tnp := R.tnp hev
  hX := R.hX
  hX0e := R.hX0e
  hp2 := by
    intro j
    have hb := (R.tnp hev).hbs
    rcases le_or_gt ((PR θ X₀ ω).p j) R.Z with hj | hj
    · exact hb.p_ge_two hj
    · have hXm7 : (10 : ℝ) ^ 7 ≤ Xm X₀ := hb.X0m_ge
      have hZ := R.x0s.hZ
      norm_num at hXm7
      linarith
  ht := (dec_R (R.tnp hev)).1
  htv := (dec_R (R.tnp hev)).2
  hlam := R.hlam
  hlam1 := R.hlam1
  hTm := R.hTm
  hTb := R.hTb
  hj0 := R.hj0
  hHux := R.hHux
  hin := R.hin
  hμ0 := R.hμ0
  hμ1 := R.hμ1
  hxmax := R.hxmax
  hZ := R.hZ
  EBR := R.EBR
  jX := R.jX
  EBR_nonneg := R.EBR_nonneg
  jX_nonneg := R.jX_nonneg
  bridge := fun x y hx hxT hy =>
    let D := R.bridge x y hx hxT hy
    { N := D.N
      K := D.K
      hN2 := D.hN2
      hN := D.hN
      hK := D.hK
      s0 := KR.X0S.sX0 X₀
      o := D.o
      etaX0 := R.x0s.etaX0Sum_of dyScales_dyadic
      etaX0Sum := D.etaX0Sum
      osc := D.osc
      termOsc := D.termOsc
      sizeE := D.sizeE
      sizeJ := D.sizeJ
      l520 := D.l520 }
  g1 := R.g1
  B := R.B
  K := R.K
  R := R.R
  hR := R.hR
  hinj := R.hinj
  ρ := rhoT θ X₀ ω
  ν := R.ν
  NT := R.NT
  ϑ := R.ϑ
  hmargin := R.hmargin
  hBx := R.hBx
  hRres := R.hRres
  a := R.a
  b := R.bb
  hK := R.hK
  hG := R.hG
  hϑ := R.hϑ
  intRT := KR.Int.intRT_of (PR θ X₀ ω) R.width.reg (twR θ X₀ ω) R.width.X0m_pos R.hTm R.hTb
    R.j0 X₀
  intRS := KR.Int.intRS_of (PR θ X₀ ω) (twR θ X₀ ω) R.width.X0m_pos R.hTm R.hTb R.j0 X₀
  Bt := R.Bt
  η := R.η
  sη := R.sη
  intm := R.intm
  p := R.p
  T0 := R.T0
  NTpt := NTpt θ X₀ ω
  err := R.err
  e := R.e
  oV := R.oV
  ηV := R.ηV
  chain := R.chain
  hpXm := R.hpXm
  hpε := R.hpε
  hT0 := R.hT0
  hT0wf := R.hT0wf
  hT0T := R.hT0T
  hm := by
    funext y
    rw [R.Tp_eq y, marginM_eq, R.hpXm]
    rfl
  hmbdd := R.hmbdd
  hρ0 := by rw [R.hpXm]; exact R.hρ0
  hT0' := R.hT0'
  hgeom := R.hgeom
  hS2 := R.hS2
  he0 := R.he0
  hoscV := R.hoscV
  hsw := R.hsw
  hS4 := R.hS4
  hbase := R.hbase
  hhead := R.hhead
  htail := R.htail
  hdec := R.hdec
  hBt := R.hBt
  hsη := R.hsη
  hsmall := R.hsmall
  jb := R.jb
  hsum := R.hsum
  hjb := R.hjb
  hc := R.hc
  hz := R.hz

end RealMarginLoc

/-- **Proposition 5.38 on `[X₀, b]` for the margin density of the construction.** -/
theorem pointwiseMarginOn_of_loc {hc : Cond θ X₀} (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (R : RealMarginLoc hc ω b) : PointwiseMarginOn (marginM θ X₀ ω) X₀ b :=
  let h := (R.toCI hev).prop_5_38_on
  ⟨h.ge, h.zero⟩

/-- **The hypothesis `hPM` of `r1Ident_of_marginOn`** from the inputs `RealMarginLoc` a.s. on
`Good(< b)`. -/
theorem hPM_of_loc (hc : Cond θ X₀) (hev : Even X₀) (D : Queue6.Sec5Family)
    (hR : ∀ (m : ℕ) (a b : ℤ), Queue6.Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ Queue6.G0 θ X₀ D (Queue6.tE2 b) → Nonempty (RealMarginLoc hc ω (b : ℝ))) :
    ∀ (m : ℕ) (a b : ℤ), Queue6.Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ Queue6.G0 θ X₀ D (Queue6.tE2 b) → PointwiseMarginOn (marginM θ X₀ ω) X₀ b := by
  intro m a b hadm
  filter_upwards [hR m a b hadm] with ω hω hG
  obtain ⟨R⟩ := hω hG
  exact pointwiseMarginOn_of_loc hev R

end BModel

namespace BModel

/-- `hPM_of_loc` feeds `r1Ident_of_marginOn` directly. -/
example {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀) (D : Queue6.Sec5Family)
    (hR : ∀ (m : ℕ) (a b : ℤ), Queue6.Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ Queue6.G0 θ X₀ D (Queue6.tE2 b) → Nonempty (RealMarginLoc hc ω (b : ℝ))) :
    ∀ m a b, Queue6.Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ Queue6.G0 θ X₀ D (Queue6.tE2 b) →
      Margin.R1Ident θ X₀ m a b ω :=
  r1Ident_of_marginOn hc hev D (hPM_of_loc hc hev D hR)

end BModel

end
