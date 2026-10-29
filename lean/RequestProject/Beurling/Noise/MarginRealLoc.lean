module

public import RequestProject.Beurling.Noise.MarginChainLoc
public import RequestProject.Beurling.Noise.RML14Kap
public import RequestProject.Beurling.Noise.MarginRealTop
public import RequestProject.Beurling.Noise.MarginInt
public import RequestProject.Beurling.Noise.KRTrueX0
public import RequestProject.Beurling.Noise.MarginExact
public import RequestProject.Beurling.Noise.RML6PredMain
public import RequestProject.Beurling.Noise.RML6Var2Head

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
* step (iii) of Proposition 5.18, `EtaX0SumLoc` on the dyadic scales (`KR.X0S.Hyp.etaX0SumLoc_of`,
  `dyScales_dyadic`), from the window count of `KR.X0S.Hyp` at heights `≤ b + H(b)`;
* Lemma 5.34 (`hpred_R`), from `KR.Ops.pred_Rres` on `LocInt`, with `ν` the residual of the
  margin identity (`nuRes`, `margin_nuRes`); `OpHyp` (`opH`);
* the Step 5 head bound `1 + 2.2181` (`Margin.Rec.hhead_loc`, given `ε' ≤ 0.045`).

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

variable (θ X₀) in
/-- The points `z` at which Step 2 of the proof of Proposition 5.38 is used: `z ∈ [t/w - 0.52
H(t/w), t/w]` for a height `T₀ ≤ t ≤ b` and a cofactor `w` of the recursion. -/
def S2Rng (ω : JitterΩ) (p : Margin.Rec.CP) (T0 b z : ℝ) : Prop :=
  ∃ t, T0 ≤ t ∧ t ≤ b ∧ ∃ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
    t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z ∧
      z ≤ t / KR.Vl (PR θ X₀ ω) w

/-- `j₀ 1_{[X₀,∞)}` as a locally integrable function. -/
noncomputable def JL (j0 : ℝ) (X₀ : ℕ) : KR.Ops.LocInt :=
  ⟨fun t => j0 * ind X₀ t, KR.Ops.mem_LocInt.mpr fun a c =>
    (show KR.BM (fun t => j0 * ind X₀ t) from
      ⟨measurable_const.mul (ind_measurable _), |j0|, fun t => by
        rw [abs_mul]
        have := ind_abs_le (X₀ : ℝ) t
        nlinarith [abs_nonneg j0, abs_nonneg (ind (X₀ : ℝ) t)]⟩).intervalIntegrable a c⟩

/-- **`ν` as the residual of the margin identity** (Proposition 5.11 with (Ttilde)):
`ν := B(T_c + J) + ϑ/H - NT - ρ̃ - B K_pt ρ̃`, so that the identity holds by definition
(`margin_nuRes`); that `ν` is the noise of the paper (and its bounds) is the input of
Lemma 5.22. -/
noncomputable def nuRes {P : BeurlingSystem} {H : ℝ → ℝ} {X0m : ℝ} (hO : KR.Ops.OpHyp P H X0m)
    (tw : ℕ → ℝ) (ρ Tc J vtH NT : KR.Ops.LocInt) : KR.Ops.LocInt :=
  KR.Ops.Bo hO (Tc + J) + vtH - NT - ρ - KR.Ops.Bo hO (KR.Ops.Ko (tw := tw) hO ρ)

lemma margin_nuRes {P : BeurlingSystem} {H : ℝ → ℝ} {X0m : ℝ} (hO : KR.Ops.OpHyp P H X0m)
    (tw : ℕ → ℝ) (ρ Tc J vtH NT : KR.Ops.LocInt) :
    ρ + KR.Ops.Bo hO (KR.Ops.Ko (tw := tw) hO ρ) =
      KR.Ops.Bo hO (Tc + J) + vtH - nuRes hO tw ρ Tc J vtH NT - NT := by
  unfold nuRes; abel

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
  /-- `T_c` measurable (`BModel.measurable_TcR`), and `|T_c| ≤ 2` (§5.1: `|T'| ≤ 2`) below the
  (HBS) horizon, `t/X₀⁻ ≤ Z` (Lemma 6.27(b) reads (HBS) up to `t/X₀⁻`; `BModel.TcR_abs_le` at
  `j0 = jzX X₀`) -/
  hTm : Measurable (TcR θ X₀ ω j0)
  hTb : ∀ t, t / Xm X₀ ≤ Z → |TcR θ X₀ ω j0 t| ≤ 2
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
  Lemma 6.26) at the heights `X₀²/2 < y ≤ b + H(b)`, and the growth `H ≤ y^{1/8}`
  (`KR.X0S.Hyp`, with `θo = θ`; `Queue6.x0sHyp_G0` at `t = tE2 b`). The consumers evaluate
  `η_{X₀}` only at positions `≤` the start `y ≤ b + H(b)` (`EtaX0SumLoc`). -/
  x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θ (b + Queue6.Hc X₀ b)
  /-- **Proposition 5.26, Lemma 5.27, Lemma 5.20** at the starts of the windows of the centres
  `X₁ ≤ x ≤ b` -/
  bridge : ∀ x y, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → InW (Queue6.Hc X₀ x) x y →
    BridgeR (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
      (TcR θ X₀ ω j0) j0 y (EBR x) (jX x)
  /-- **Proposition 5.35**, residual inputs, at `X₀ ≤ y ≤ b + H(b)` -/
  g1 : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b →
    G1At (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ μ0 μ1 ρedge
      (fun t => TcR θ X₀ ω j0 t + j0 * ind X₀ t) y
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
  hTcL : (TcL : ℝ → ℝ) = TcR θ X₀ ω j0
  /-- `NT` (locally integrable) -/
  NT : KR.Ops.LocInt
  ϑ : ℝ → ℝ
  /-- `ϑ/H` (locally integrable) -/
  vtH : KR.Ops.LocInt
  hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / Queue6.Hc X₀ z
  /-- `T' = T_c + J` bounded and measurable on half-lines -/
  hTLBd : KR.Ops.LBd (fun t => TcR θ X₀ ω j0 t + j0 * ind X₀ t)
  a : ℝ → ℝ
  bb : ℝ → ℝ
  /-- Lemma 5.34, first bullet (from Proposition 5.18; `KR.Ops.hK_of_kernel` reduces it to the
  kernel part at each start of the window) -/
  hK : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
    Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO (KR.Ops.Bo hO
      (KR.Ops.Ro (tw := twR θ X₀ ω) hO ((KR.Ops.Bo hO TcL - TcL) + vtH -
        nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT)))) : ℝ → ℝ) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
    Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ro (tw := twR θ X₀ ω) hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO
      ((KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT -
          NT - KR.Ops.Bo hO (JL j0 X₀)) -
        KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
          nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀))))) :
      ℝ → ℝ) x| ≤ bb x
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
  /-- `m` is bounded up to `2b + 1.01 H(2b)` (every envelope window used lies there) -/
  hmbdd : ∃ C, ∀ y, y ≤ 2 * b + 1.01 * Queue6.Hc X₀ (2 * b) → |marginM θ X₀ ω y| ≤ C
  /-- `ρ̃ = 0` below `X₀⁻` (the slots are `≥ X₀`, §5.1) -/
  hρ0 : ∀ z, z < Xm X₀ → rhoT θ X₀ ω z = 0
  hT0' : ∀ t, T0 ≤ t → t ≤ b → 0 ≤ t ∧ 1.01 * Queue6.Hc X₀ t ≤ t
  /-- `H`-regularity at a cofactor (`HStep`) -/
  hgeom : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
    Margin.Rec.HStep (Queue6.Hc X₀) p.ε t (t / KR.Vl (PR θ X₀ ω) w) (KR.Vl (PR θ X₀ ω) w)
  /-- **Step 2**, data: the local slot family `(Q, s_q)` representing `ρ̃` at `z, z+s`, the
  local variation `δ_z` of `H`, the error `ε` of Lemma 5.22 and the bound `m*` -/
  s2Q : ℝ → ℝ → Finset ℕ
  s2sl : ℝ → ℝ → ℕ → ℝ
  s2δ : ℝ → ℝ
  s2ε : ℝ → ℝ
  s2mst : ℝ → ℝ
  /-- **Step 2, slot representation** (Queue6: the slot measure): near `z`, `ρ̃` is the
  box sum of the finite slot family `Q`, `ρ̃(y) = ∑_q H(s_q)⁻¹ 1[y ∈ [s_q ± H(s_q)/2)]` (§5.1) -/
  hS2rep : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    rhoT θ X₀ ω z = Margin.Exact.rhoTilde (s2Q z s) (s2sl z s) (Queue6.Hc X₀) z ∧
      rhoT θ X₀ ω (z + s) = Margin.Exact.rhoTilde (s2Q z s) (s2sl z s) (Queue6.Hc X₀) (z + s)
  /-- **Step 2, weights** (Queue6): `|H(z)/H(s_q) - 1| ≤ 1.6 δ_z` for the slots in `A±` -/
  hS2w : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    ∀ q ∈ s2Q z s, (s2sl z s q ∈ Margin.Exact.Aplus (Queue6.Hc X₀) z s ∨
      s2sl z s q ∈ Margin.Exact.Aminus (Queue6.Hc X₀) z s) →
      |Queue6.Hc X₀ z / Queue6.Hc X₀ (s2sl z s q) - 1| ≤ 1.6 * s2δ z
  /-- **Step 2, slot counts** (Queue6): `σ(A₊) ≤ 1.03 H(z)` -/
  hS2cp : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    Margin.Exact.sigmaS (s2Q z s) (s2sl z s) (Margin.Exact.Aplus (Queue6.Hc X₀) z s) ≤
      1.03 * Queue6.Hc X₀ z
  /-- **Step 2, slot counts** (Queue6): `σ(A₋) ≤ 1.03 H(z)` -/
  hS2cm : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    Margin.Exact.sigmaS (s2Q z s) (s2sl z s) (Margin.Exact.Aminus (Queue6.Hc X₀) z s) ≤
      1.03 * Queue6.Hc X₀ z
  /-- **Step 1 / Lemma 5.22 on `A₊`** (Queue6): `σ(A₊) = ∫_{A₊} m + E₊`, `|E₊| ≤ ε` -/
  hS2Ep : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |Margin.Exact.sigmaS (s2Q z s) (s2sl z s) (Margin.Exact.Aplus (Queue6.Hc X₀) z s) -
      ∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε z
  /-- **Step 1 / Lemma 5.22 on `A₋`** (Queue6): `σ(A₋) = ∫_{A₋} m + E₋`, `|E₋| ≤ ε` -/
  hS2Em : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |Margin.Exact.sigmaS (s2Q z s) (s2sl z s) (Margin.Exact.Aminus (Queue6.Hc X₀) z s) -
      ∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε z
  /-- **Step 2, strip comparison on `A₊`** (§5): `|∫_{A₊} m - ∫_{I₊} m| ≤ 1.05 δ_z H(z) m*`,
  `I₊ = (z + H/2, z + H/2 + s]` -/
  hS2sp : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |(∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
      ∫ r in (z + Queue6.Hc X₀ z / 2)..(z + Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
      1.05 * s2δ z * Queue6.Hc X₀ z * s2mst z
  /-- **Step 2, strip comparison on `A₋`** (§5), `I₋ = (z - H/2, z - H/2 + s]` -/
  hS2sm : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    |(∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
      ∫ r in (z - Queue6.Hc X₀ z / 2)..(z - Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
      1.05 * s2δ z * Queue6.Hc X₀ z * s2mst z
  /-- `δ_z ≥ 0` -/
  hS2δ : ∀ z, S2Rng θ X₀ ω p T0 b z → 0 ≤ s2δ z
  /-- **Step 2**, `H(z) ≤ 1.01 H(x)` on the lower strip (regularity of `H`, §5) -/
  hS2H : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ x ∈ Icc (z - Queue6.Hc X₀ z / 2)
    (z + 0.51 * Queue6.Hc X₀ z), Queue6.Hc X₀ z ≤ 1.01 * Queue6.Hc X₀ x
  /-- **Step 2**, integrability of `m` on the strips -/
  hS2mi : ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
    IntervalIntegrable (marginM θ X₀ ω) volume (z - Queue6.Hc X₀ z / 2)
      (z + Queue6.Hc X₀ z / 2 + s)
  /-- **Step 2**, the error: `2ε/H(z) + (3.3 + 2.1 m*) δ_z ≤ err(z)` -/
  hS2err : ∀ z, S2Rng θ X₀ ω p T0 b z →
    2 * s2ε z / Queue6.Hc X₀ z + (3.3 + 2.1 * s2mst z) * s2δ z ≤ err z
  /-- **Step 3**, the recursion weights: `err(z') ≤ e(t, w)` on the strip of `(t, w)` -/
  hS2e : ∀ t, T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, ∀ z',
    t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
      z' ≤ t / KR.Vl (PR θ X₀ ω) w → err z' ≤ e t w
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
  /-- **Step 4**, filtered by `κ_w(t)` as in the paper (04g Step 3) -/
  hS4 : ∀ t, T0 ≤ t → t ≤ b →
    oV t + 2 * ηV t + ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
      Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w * (e t w / KR.Vl (PR θ X₀ ω) w) ≤
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
    rhoT θ X₀ ω t + (nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT : ℝ → ℝ) t +
      (NT : ℝ → ℝ) t = Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t + Bt t
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

/-- **Step 2** (`Margin.Rec.Step2At`) from its split fields: the exact form with weights
(`Margin.Exact.step2_exact_bullet`, through the slot representation `hS2rep`), Lemma 5.22 on
`A±`, the strip comparison, and `H(z) ≤ 1.01 H(x)` on the lower strip
(`Margin.Rec.step2At_of`). -/
theorem hS2_of (R : RealMarginLoc hc ω b) :
    ∀ t, R.T0 ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω) R.p t, ∀ z',
      t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
        z' ≤ t / KR.Vl (PR θ X₀ ω) w →
          Margin.Rec.Step2At (Queue6.Hc X₀) (rhoT θ X₀ ω)
            (Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω)) R.err z' ∧ R.err z' ≤ R.e t w := by
  intro t ht0 htb w hw z' h1 h2
  have hz : S2Rng θ X₀ ω R.p R.T0 b z' := ⟨t, ht0, htb, w, hw, h1, h2⟩
  refine ⟨?_, R.hS2e t ht0 htb w hw z' h1 h2⟩
  have hHpos : ∀ y, 0 < Queue6.Hc X₀ y := KR.WidthReal.Hc_pos R.hX
  have hb0 := R.hT0' b (R.hT0T) le_rfl
  have hz'b : z' ≤ b := by
    have hV := KR.one_le_valN_label (PR θ X₀ ω) w
    have ht0 : 0 ≤ t := (R.hT0' t ht0 htb).1
    have : t / KR.Vl (PR θ X₀ ω) w ≤ t := div_le_self ht0 hV
    linarith
  have hloc : ∀ x ∈ Icc (z' - Queue6.Hc X₀ z' / 2) (z' + 0.51 * Queue6.Hc X₀ z'), ∀ hh,
      |hh| ≤ 1.01 * Queue6.Hc X₀ x →
        |marginM θ X₀ ω (x + hh) - marginM θ X₀ ω x| ≤
          Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω) x := by
    intro x hx hh hh1
    have hHm := KR.WidthReal.Hc_mono R.hX
    have hHz : Queue6.Hc X₀ z' ≤ Queue6.Hc X₀ b := hHm hz'b
    have hx2 : x ≤ 2 * b := by linarith [hx.2, hb0.2, hHpos b]
    have hHx : Queue6.Hc X₀ x ≤ Queue6.Hc X₀ (2 * b) := hHm hx2
    refine Margin.Rec.le_vSup_loc ?_ hh1
    obtain ⟨C, hC⟩ := R.hmbdd
    refine ⟨C, fun y hy => hC y ?_⟩
    have := (abs_le.mp hy).2
    linarith
  refine Margin.Rec.step2At_of_loc (m := marginM θ X₀ ω) (hHpos z')
    hloc (R.hS2H z' hz) (R.hS2mi z' hz) ?_
  intro s hs0 hs1
  obtain ⟨hr0, hr1⟩ := R.hS2rep z' hz s hs0 hs1
  set Q := R.s2Q z' s
  set sl := R.s2sl z' s
  set JAp := ∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z' s, marginM θ X₀ ω r
  set JAm := ∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z' s, marginM θ X₀ ω r
  set σp := Margin.Exact.sigmaS Q sl (Margin.Exact.Aplus (Queue6.Hc X₀) z' s)
  set σm := Margin.Exact.sigmaS Q sl (Margin.Exact.Aminus (Queue6.Hc X₀) z' s)
  refine ⟨R.s2ε z', R.s2δ z', R.s2mst z', σp, σm, σp - JAp, σm - JAm, JAp, JAm, ?_, by ring,
    by ring, R.hS2Ep z' hz s hs0 hs1, R.hS2Em z' hz s hs0 hs1, R.hS2sp z' hz s hs0 hs1,
    R.hS2sm z' hz s hs0 hs1, R.hS2err z' hz⟩
  rw [hr0, hr1]
  exact Margin.Exact.step2_exact_bullet (Q := Q) (sl := sl) (H := Queue6.Hc X₀)
    (fun q _ => hHpos _) hs0
    (R.hS2δ z' hz) (R.hS2w z' hz s hs0 hs1) (R.hS2cp z' hz s hs0 hs1) (R.hS2cm z' hz s hs0 hs1)

lemma hX0e (_R : RealMarginLoc hc ω b) :
    Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
  unfold Xm Queue6.Hc; rw [max_self]

/-- `T_c + j₀ 1_{[X₀,∞)} = T'_cont + K_𝒜 ρ̃`. -/
lemma Tp_eq (R : RealMarginLoc hc ω b) (y : ℝ) :
    TcR θ X₀ ω R.j0 y + R.j0 * ind X₀ y = TpCont θ X₀ ω y + KAbsR θ X₀ ω (rhoT θ X₀ ω) y := by
  unfold TcR; ring

/-- Prime values `≥ 2` (from (HBS) below the horizon, and `X₀⁻ ≤ Z` above). -/
lemma hp2 (R : RealMarginLoc hc ω b) : ∀ j, 2 ≤ (PR θ X₀ ω).p j := by
  intro j
  rcases le_or_gt ((PR θ X₀ ω).p j) R.Z with hj | hj
  · exact R.hbs.p_ge_two hj
  · have hXm7 : (10 : ℝ) ^ 7 ≤ Xm X₀ := R.hbs.X0m_ge
    have hZ := R.x0s.hZ
    norm_num at hXm7
    linarith

/-- The hypotheses `OpHyp` of the operators of §5.3 for `Hc X₀`. -/
lemma opH (R : RealMarginLoc hc ω b) : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) :=
  KR.Ops.opHyp_Hc R.hX R.width R.hp2

/-- **Lemma 5.34, the input (predictable) of Theorem 5.37**, from `KR.Ops.pred_Rres`. -/
theorem hpred_R (R : RealMarginLoc hc ω b) : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
    Real.log x * Margin.Bavg (Queue6.Hc X₀ x) (fun y => Rres (PR θ X₀ ω) (Queue6.Hc X₀)
        (twR θ X₀ ω) (Xm X₀) y (fun t => TcR θ X₀ ω R.j0 t + R.j0 * ind X₀ t)) x -
      (R.a x + R.bb x + 6 * Real.log x / Queue6.Hc X₀ x) ≤
      Real.log x * (rhoT θ X₀ ω x +
        (nuRes R.opH (twR θ X₀ ω) R.ρL R.TcL (JL R.j0 X₀) R.vtH R.NT : ℝ → ℝ) x +
        (R.NT : ℝ → ℝ) x) := by
  intro x hx hxb
  have hX1 : (1 : ℝ) < X₀ := BaseRange.one_lt_of_log R.hX
  have h1 : (1 : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have e : ((R.TcL + JL R.j0 X₀ : KR.Ops.LocInt) : ℝ → ℝ) =
      fun t => TcR θ X₀ ω R.j0 t + R.j0 * ind X₀ t := by
    rw [AddSubgroup.coe_add, R.hTcL]; rfl
  have hT : KR.Ops.LBd ((R.TcL + JL R.j0 X₀ : KR.Ops.LocInt) : ℝ → ℝ) := by
    rw [e]; exact R.hTLBd
  have h := KR.Ops.pred_Rres (tw := twR θ X₀ ω) R.opH R.width R.ρL
    (nuRes R.opH (twR θ X₀ ω) R.ρL R.TcL (JL R.j0 X₀) R.vtH R.NT) R.NT R.vtH R.TcL
    (JL R.j0 X₀) R.ϑ hT R.hvt (margin_nuRes _ _ _ _ _ _ _) hlx (R.hK R.opH x hx hxb)
    (R.hG R.opH x hx hxb) (R.hϑ x hx hxb)
  rw [e, R.hρL] at h
  exact h

/-- Heights below `2(b + H(b))` are below the (HBS) horizon: `t/X₀⁻ ≤ Z`. -/
lemma div_Xm_le_Z (R : RealMarginLoc hc ω b) {t : ℝ} (ht : t ≤ 2 * (b + Queue6.Hc X₀ b)) :
    t / Xm X₀ ≤ R.Z := by
  refine le_trans ?_ R.hZ
  exact div_le_div_of_nonneg_right ht R.width.X0m_pos.le

lemma win_le (R : RealMarginLoc hc ω b) {x : ℝ} (_hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x) :
    x - Queue6.Hc X₀ x / 2 ≤ x + Queue6.Hc X₀ x / 2 := by
  have := (R.width.reg.pos x).le
  linarith

/-- The points of a window of a centre `X₀^{1.01} ≤ x ≤ b` are positive and `1.2|y| ≤ 2(b+H(b))`. -/
lemma win_point (R : RealMarginLoc hc ω b) {x y : ℝ} (hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x)
    (hxb : x ≤ b) (hy1 : x - Queue6.Hc X₀ x / 2 ≤ y) (hy2 : y ≤ x + Queue6.Hc X₀ x / 2) :
    0 ≤ y ∧ 1.2 * |y| ≤ 2 * (b + Queue6.Hc X₀ b) := by
  have hXm := R.width.X0m_pos
  have hX1 : (1 : ℝ) ≤ X₀ := by
    have := KR.WidthReal.X0_pos R.hX (X₀ := X₀)
    have h2 := R.hX
    by_contra hc'
    push_neg at hc'
    have : Real.log (X₀ : ℝ) ≤ 0 := Real.log_nonpos this.le hc'.le
    linarith
  have hXx : (X₀ : ℝ) ≤ x := le_trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1 : ℝ) ≤ 1.01)) hx
  have hXmX : Xm X₀ ≤ X₀ := by
    rw [R.hX0e]; have := (R.width.reg.pos (X₀ : ℝ)).le; linarith
  have hHx : Queue6.Hc X₀ x ≤ x / 10 := R.width.small x (by linarith)
  have hHm := KR.WidthReal.Hc_mono R.hX hxb
  have hHb := (KR.WidthReal.Hc_pos R.hX b).le
  have hy0 : 0 ≤ y := by have := (R.width.reg.pos x).le; linarith
  refine ⟨hy0, ?_⟩
  rw [abs_of_nonneg hy0]
  linarith

/-- **The local chain inputs for the construction**. -/
noncomputable def toCI (R : RealMarginLoc hc ω b) (hev : Even X₀) :
    ChainInputsLoc (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ R.Z R.η1 R.η2 R.ε1 R.ε
      (R.ε / 10) R.lam0 (TcR θ X₀ ω R.j0) R.j0 R.xmax R.μ0 R.μ1 R.ρedge (marginM θ X₀ ω) b where
  tnp := R.tnp hev
  hX := R.hX
  hX0e := R.hX0e
  hp2 := R.hp2
  ht := (dec_R (R.tnp hev)).1
  htv := (dec_R (R.tnp hev)).2
  hlam := R.hlam
  hlam1 := R.hlam1
  hTm := R.hTm
  hTb := fun t ht => R.hTb t (R.div_Xm_le_Z ht)
  hO := R.opH
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
      etaX0 := R.x0s.etaX0SumLoc_of dyScales_dyadic (by
        have hy2 := hy.2
        have hHm := KR.WidthReal.Hc_mono R.hX hxT
        have hHb := (KR.WidthReal.Hc_pos R.hX b).le
        linarith)
      etaX0Sum := D.etaX0Sum
      osc := D.osc
      termOsc := D.termOsc
      sizeE := D.sizeE
      sizeJ := D.sizeJ
      l520 := D.l520 }
  g1 := R.g1
  ρ := rhoT θ X₀ ω
  ν := (nuRes R.opH (twR θ X₀ ω) R.ρL R.TcL (JL R.j0 X₀) R.vtH R.NT : ℝ → ℝ)
  NT := (R.NT : ℝ → ℝ)
  a := R.a
  b := R.bb
  hpred := R.hpred_R
  intRT := fun x hx hxb => KR.TcLoc.intRT_loc R.opH R.width R.hTm
    (fun t ht => R.hTb t (R.div_Xm_le_Z ht)) R.j0 X₀ (R.win_le hx) (fun y hy1 hy2 =>
      (R.win_point hx hxb hy1 hy2).2)
  intRS := fun x hx hxb => KR.TcLoc.intRS_loc R.width.X0m_pos R.hTm
    (fun t ht => R.hTb t (R.div_Xm_le_Z ht)) R.j0 X₀ (R.win_le hx)
    (R.win_point hx hxb le_rfl (R.win_le hx)).1
    (by have := (R.win_point hx hxb (R.win_le hx) le_rfl).2
        have := (R.win_point hx hxb (R.win_le hx) le_rfl).1
        rw [abs_of_nonneg (by linarith)] at *; linarith)
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
  hmbdd := by
    obtain ⟨C, hC⟩ := R.hmbdd
    exact ⟨C, fun y hy => hC y (by linarith [(KR.WidthReal.Hc_pos R.hX (2 * b)).le])⟩
  hρ0 := by rw [R.hpXm]; exact R.hρ0
  hT0' := R.hT0'
  hgeom := R.hgeom
  hS2 := R.hS2_of
  he0 := R.he0
  hoscV := R.hoscV
  hsw := R.hsw
  hS4 := R.hS4
  hbase := R.hbase
  hhead := fun t _ htb => Margin.Rec.hhead_loc _ R.hbs (R.tnp hev).hXm R.p R.hpXm R.hpε'
    (by
      have hX := (R.tnp hev).width.X0m_pos
      have hHb := (KR.WidthReal.Hc_pos R.hX b).le
      refine le_trans ?_ R.hZ
      exact div_le_div_of_nonneg_right (by linarith) hX.le) _
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  htail := R.htail
  hdec := R.hdec R.opH
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
