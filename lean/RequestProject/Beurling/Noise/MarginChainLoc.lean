module

public import RequestProject.Beurling.Noise.MarginChain2
public import RequestProject.Beurling.Noise.MarginChainLocRec
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# The chain Bridge → Theorem 5.37 → Proposition 5.38 up to a height `T`

`ChainInputs2` (`MarginChain2.lean`) quantifies its inputs over **all** heights, which the good
event `Good(< b)` does not control (it controls the construction up to its horizon). Corollary
5.40 on a window `[a, b)` reads the margin only on `[X₀, b]`. `ChainInputsLoc … T` is
`ChainInputs2` with every height-quantified input restricted to the heights read by
Proposition 5.38 on `[X₀, T]`:

* the centres `x ≤ T` of Theorem 5.37 and their windows `W_x ⊆ (-∞, T + H(T)]`
  (`window_le`, from the `θ`-Lipschitz bound of `PaperWidth`);
* the heights `y ≤ T + H(T)` of Proposition 5.35 (`g1`), with `T + H(T) ≤ x_max` (§7) and the
  cofactor horizon `2(T + H(T))/X₀⁻ ≤ Z` of (HBS);
* the recursion of Steps 1–5 at the heights `T₀ ≤ t ≤ T` (`Margin.Rec.variation_le_chain_loc`);
* the error sizes, Step 6(a)–(c) at `t ≤ T`.

The Lemma 5.20 conclusions at a start `y` (`L520At`: `EtaBound` with `λ₀ C_N E_η ≤ ½`,
`ThetaBlk`, scales `≥ 1/2`) are a field of the bridge data (`BridgeAtL`). They are proved by
`TauNearProof*` under the horizon `18y ≤ Z` (`l520At_of_18`, with the width bound
`H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}` that holds for the realised width, `KR.WidthReal.Hc_Xm_half_le`,
in place of the standard width, which fails for it, `not_hHstd_Hc`); a proof at the cofactor
horizon `2y/X₀⁻ ≤ Z` (the paper's reading range) is to be supplied for the field.

Main result: `ChainInputsLoc.prop_5_38_on : MarginOn m X₀ T`, **Proposition 5.38 (a)–(c) on
`[X₀, T]`**.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem

namespace KR.Chain

open KR.TNP

/-- **Proposition 5.38 up to the height `T`**: `0.399 ≤ m(t) log t` on `[X₀, T]`, `m = 0` below
`X₀`. -/
structure MarginOn (m : ℝ → ℝ) (X0 T : ℝ) : Prop where
  ge : ∀ t, X0 ≤ t → t ≤ T → 0.399 ≤ m t * Real.log t
  zero : ∀ t, t < X0 → m t = 0

/-- **The conclusions of Lemma 5.20 at a start `y`** on the dyadic scales `dyScales X₀ y N` with
the blocks of `K`: the scales are `≥ 1/2`, `EtaBound` with `λ₀ C_N E_η ≤ ½`, and `ThetaBlk`. -/
def L520At (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 lam0 y : ℝ) (N K : ℕ) :
    Prop :=
  (∀ u ∈ dyScales X0 y N, 1 / 2 ≤ u) ∧
    EtaBound P H tw X0m (dyScales X0 y N) (sEta P H X0m K) ∧
    lam0 * CNc X0 * ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sEta P H X0m K v ≤ 1 / 2 ∧
    ThetaBlk P H tw X0m (dyScales X0 y N) (sTheta P H X0m K)

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **Lemma 5.20 at a start `y`** from `TauNearProof*`, under `18 y ≤ Z` and the width bound
`H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}`. -/
theorem l520At_of_18 (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 y lam0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (h18 : 18 * y ≤ Z) {N K : ℕ}
    (hK : √(2 * y) ≤ Pk X0m K) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
    L520At P H tw X0m X0 lam0 y N K := by
  obtain ⟨h1, h2, h3, h4⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  refine ⟨fun u hu => by linarith [h2 u hu], (etaBound_energy h h1 h2 h3 h4).1, ?_,
    (thetaBlk_sum h h1 h2 h3 h4).1⟩
  exact KR.WidthReal.energy_small_r h hH h1 h2 h3 h4 hlam0 hlam
    (CNt_bounds (sizes h hX0e hX0m).2.1).1 (CNt_bounds (sizes h hX0e hX0m).2.1).2

/-- **The bridge data at a start `y`**, localized: `BridgeAt2` and the conclusions of Lemma 5.20
(`L520At`) at its scales. -/
structure BridgeAtL (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 : ℝ)
    (Tc : ℝ → ℝ) (j0 y EBR j : ℝ) extends BridgeAt2 P H tw X0m X0 θ lam0 Tc j0 y EBR j where
  /-- **Lemma 5.20** at `y` (`l520At_of_18` proves it under `18 y ≤ Z`) -/
  l520 : L520At P H tw X0m X0 lam0 y N K

/-- `BridgeAtL` gives `BridgeAt`. -/
noncomputable def BridgeAtL.toBridgeAt {X0 lam0 : ℝ} {Tc : ℝ → ℝ} {j0 y EBR j : ℝ}
    (D : BridgeAtL P H tw X0m X0 θ lam0 Tc j0 y EBR j) (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hy : X0 ≤ y) :
    BridgeAt P H tw X0m X0 θ lam0 Tc j0 y EBR j where
  Sc := dyScales X0 y D.N
  s := sEta P H X0m D.K
  s0 := D.s0
  th := sTheta P H X0m D.K
  o := D.o
  cov := cover_NAll (sizes h hX0e hX0m).2.2.2.2 (sizes h hX0e hX0m).1
    (by linarith [(sizes h hX0e hX0m).2.2.1, (sizes h hX0e hX0m).2.2.2.2]) D.hN
  covL := cover_levels (sizes h hX0e hX0m).2.2.2.2 (sizes h hX0e hX0m).1
    (sizes h hX0e hX0m).2.2.1 D.hN
  sc1 := D.l520.1
  sc := fun u hu => dyScales_kind (sizes h hX0e hX0m).2.2.2.2 (sizes h hX0e hX0m).2.2.1 hu
  eta := D.l520.2.1
  etaSmall := D.l520.2.2.1
  etaX0 := D.etaX0
  etaX0Sum := D.etaX0Sum
  theta := D.l520.2.2.2
  osc := D.osc
  X0mem := X0_mem_dyScales D.hN2 hy
  termOsc := D.termOsc
  sizeE := D.sizeE
  sizeJ := D.sizeJ

/-- **The inputs of the chain up to the height `T`** (see the module docstring); `X₁ = X₀^{1.01}`.
The fields are those of `ChainInputs2` with the heights restricted. -/
structure ChainInputsLoc (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ)
    (Z η1 η2 : ℝ) (ε1 : ℝ → ℝ) (ε θ lam0 : ℝ) (Tc : ℝ → ℝ) (j0 xmax : ℝ)
    (μ0 μ1 ρedge m : ℝ → ℝ) (T : ℝ) where
  -- standing hypotheses
  /-- (HBS), `log X₀⁻ ≥ 10⁸`, `PaperWidth`, the decision order and Corollary 6.3(ii) -/
  tnp : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ
  hX : 10 ^ 8 ≤ Real.log X0
  hX0e : X0m = X0 - H X0 / 2
  hp2 : ∀ j, 2 ≤ P.p j
  ht : ∀ r, r.Prime → 0 < tw r
  htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r
  hlam : 1 + 3 * θ ≤ lam0
  hlam1 : lam0 ≤ 1.001
  /-- `T_c` measurable with `|T_c| ≤ 2` (§5.1: `|T'| ≤ 2`) -/
  hTm : Measurable Tc
  hTb : ∀ t, |Tc t| ≤ 2
  hj0 : 0 ≤ j0
  /-- (huxley) and Lemma 7.3's inputs (§7) -/
  hHux : BaseRange.HuxleyFrom X0
  hin : BaseRange.Lemma73Inputs X0 xmax μ0 μ1 ρedge
  hμ0 : ∀ u : ℝ, u < X0 → μ0 u = 0
  hμ1 : ∀ u : ℝ, u < X0 → μ1 u = 0
  /-- the heights read: `y ≤ T + H(T) ≤ x_max` (§7) -/
  hxmax : T + H T ≤ xmax
  /-- the cofactor horizon of (HBS): `2y/X₀⁻ ≤ Z` for `y ≤ T + H(T)` -/
  hZ : 2 * (T + H T) / X0m ≤ Z
  -- the window quantities, as functions of the centre `x`
  EBR : ℝ → ℝ
  jX : ℝ → ℝ
  EBR_nonneg : ∀ x, 0 ≤ EBR x
  jX_nonneg : ∀ x, 0 ≤ jX x
  /-- **Proposition 5.26 and Lemma 5.27** (with Lemma 5.20) at the starts of the windows of the
  centres `X₀^{1.01} ≤ x ≤ T` -/
  bridge : ∀ x y, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ T → InW (H x) x y →
    BridgeAtL P H tw X0m X0 θ lam0 Tc j0 y (EBR x) (jX x)
  /-- **Proposition 5.35**, residual inputs, at the heights `X₀ ≤ y ≤ T + H(T)` -/
  g1 : ∀ y, (X0 : ℝ) ≤ y → y ≤ T + H T →
    G1At P tw X0m X0 μ0 μ1 ρedge (fun t => Tc t + j0 * ind X0 t) y
  -- **Lemma 5.34**
  B : (ℝ → ℝ) →+ (ℝ → ℝ)
  K : (ℝ → ℝ) →+ (ℝ → ℝ)
  R : (ℝ → ℝ) →+ (ℝ → ℝ)
  /-- `R_res` inverts `1 + K_pt B` (§5.3) -/
  hR : ∀ g, R g + K (B (R g)) = g
  /-- the push-through form determines `ρ̃` (§5.3) -/
  hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f'
  ρ : ℝ → ℝ
  ν : ℝ → ℝ
  NT : ℝ → ℝ
  ϑ : ℝ → ℝ
  /-- the margin identity (Proposition 5.11 with (Ttilde)) -/
  hmargin : ρ + B (K ρ) = B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT
  /-- `B` is the window average -/
  hBx : ∀ g x, B g x = Margin.Bavg (H x) g x
  /-- `R` is the long operator on `T'` -/
  hRres : R (Tc + fun t => j0 * ind X0 t) =
    fun y => Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t)
  a : ℝ → ℝ
  b : ℝ → ℝ
  /-- Lemma 5.34, first bullet (from Proposition 5.18) -/
  hK : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ T → Real.log x *
    |B (K (B (R ((B Tc - Tc) + (fun z => ϑ z / H z) - ν - NT)))) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ T → Real.log x *
    |B (R (K ((B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t)) -
      B (B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t))))) x| ≤ b x
  /-- `|ϑ| ≤ 6` (eq. (Ttilde)) at the centres `x ≤ T` -/
  hϑ : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ T → |ϑ x| ≤ 6
  /-- window integrability of `R_res T'` and `ρ^sh T'` (`KR.Int.intRT_of`, `intRS_of`) -/
  intRT : ∀ x, IntervalIntegrable (fun y => Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  intRS : ∀ x, IntervalIntegrable (fun y => rhoSh P tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  -- **Proposition 5.38(a)**
  Bt : ℝ → ℝ
  η : ℝ → ℝ
  sη : ℝ
  intm : ∀ t, IntervalIntegrable m volume (t - H t / 2) (t + H t / 2)
  /-- **Steps 1–5**: the parameters of the recursion and `m = T' - K_pt ρ̃ - NT_pt` -/
  p : Margin.Rec.CP
  T0 : ℝ
  NTpt : ℝ → ℝ
  err : ℝ → ℝ
  e : ℝ → ℕ → ℝ
  oV : ℝ → ℝ
  ηV : ℝ → ℝ
  chain : Margin.Rec.ChainHyp P p H
  hpXm : p.Xm = X0m
  hpε : p.ε ≤ 0.01
  hT0 : p.cinf + p.Kc ≤ T0
  hT0wf : 2 ≤ T0 * (1 - p.θ0)
  hT0T : T0 ≤ T
  hm : m = fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw p.Xm ρ y - NTpt y
  hmbdd : ∃ C, ∀ y, |m y| ≤ C
  hρ0 : ∀ z, z < p.Xm → ρ z = 0
  hT0' : ∀ t, T0 ≤ t → t ≤ T → 0 ≤ t ∧ 1.01 * H t ≤ t
  /-- `H`-regularity at a cofactor (`HStep`) -/
  hgeom : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Margin.Rec.Fset P p t,
    Margin.Rec.HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w)
  /-- **Step 2** (`Step2At`: exact form, Lemma 5.22 on `A±`, the strip comparison) -/
  hS2 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Margin.Rec.Fset P p t, ∀ z',
    t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
      Margin.Rec.Step2At H ρ (Margin.Rec.vSup H m) err z' ∧ err z' ≤ e t w
  he0 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Margin.Rec.Fset P p t, 0 ≤ e t w
  /-- the oscillation of `T'` (eq. (osc)) -/
  hoscV : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t →
    |(Tc (t + hh) + j0 * ind X0 (t + hh)) - (Tc t + j0 * ind X0 t)| ≤ oV t
  /-- filter switching and `ΔNT ≤ 2η` -/
  hsw : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t →
    |∑ w ∈ Margin.Rec.Fset P p t, (Margin.Rec.kap P tw (t + hh) w - Margin.Rec.kap P tw t w) *
        (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NTpt (t + hh) - NTpt t| ≤ 2 * ηV t
  /-- **Step 4** (`Margin.Var.step4` proves it from Lemma 5.21) -/
  hS4 : ∀ t, T0 ≤ t → t ≤ T →
    oV t + 2 * ηV t + ∑ w ∈ Margin.Rec.Fset P p t, e t w / KR.Vl P w ≤ p.ES / Real.log t
  /-- the base case below `T₀` -/
  hbase : ∀ t, t < T0 → Margin.Rec.vSup H m t ≤ Margin.Rec.PhiC P p t 1
  /-- **Step 5**: the transfer of `A₀(0.045)` to `𝒩` -/
  hhead : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T →
    ∑ M ∈ ((KR.NAll P t (p.Xm / 2)).filter (fun M => Margin.Rec.cutL P p M ≤
        t / Margin.Rec.Vv P M)).filter (fun M => Margin.Rec.Vv P M ≤ √t),
      Margin.Rec.Aw P p M ≤ 1 + BSCert.Consts.ordA 1.955
  /-- **Step 5**: Rankin's tail bound (`τ ≤ 0.06`) -/
  htail : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T →
    ∑ M ∈ ((KR.NAll P t (p.Xm / 2)).filter (fun M => Margin.Rec.cutL P p M ≤
        t / Margin.Rec.Vv P M)).filter (fun M => ¬ Margin.Rec.Vv P M ≤ √t),
      Margin.Rec.Aw P p M * (p.ES / Real.log (t / Margin.Rec.Vv P M)) ≤ 0.06 * p.ES / Real.log t
  /-- Step 6(a): `M = Bm + B NT_pt + ϑ/H` with `|B NT_pt + ϑ/H| ≤ 54η + 6/H` -/
  hdec : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T →
    ρ t + ν t + NT t = Margin.Bavg (H t) m t + Bt t
  hBt : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T → |Bt t| ≤ 54 * η t + 6 / H t
  hsη : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T → Real.log t * η t ≤ sη
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ T →
    oTot (H t) t (EBR t) (jX t) + (a t + b t + 6 * Real.log t / H t) + EBR t + jX t +
      54 * sη + 6 * Real.log t / H t + 6.5 * p.ES + VX P p t ≤ 0.01
  -- **Proposition 5.38(b)**
  jb : ℝ → ℝ
  /-- Step 6(b), "Sum": `m log t ≥ ρ^sh log t - j_{X₀} - 10⁻¹²` -/
  hsum : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) → t ≤ T →
    rhoSh P tw X0m t (fun s => Tc s + j0 * ind X0 s) * Real.log t - jb t - 1 / 10 ^ 12 ≤
      m t * Real.log t
  /-- **Proposition 5.33**: `j_{X₀} ≤ 0.4209` -/
  hjb : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) → t ≤ T → jb t ≤ 0.4209
  -- **Proposition 5.38(c)** (Step 6(c)): the source bounds on `[X₀, 2X₀)`
  hc : ∀ t, (X0 : ℝ) ≤ t → t < 2 * X0 → t ≤ T →
    (∃ Tp, m t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
    (∃ Tp rt, m t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
      rt ≤ 0.5001 / Real.log X0 ∧ Real.log t ≤ Real.log X0 + 0.7)
  /-- `m = 0` below `X₀` -/
  hz : ∀ t : ℝ, t < X0 → m t = 0

namespace ChainInputsLoc

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ}
  {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} {ε θ lam0 : ℝ} {Tc : ℝ → ℝ} {j0 xmax : ℝ}
  {μ0 μ1 ρedge m : ℝ → ℝ} {T : ℝ}

lemma X0_gt (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T) :
    (1 : ℝ) < X0 := BaseRange.one_lt_of_log I.hX

lemma X0m_le (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T) :
    X0m ≤ X0 := by
  have hH : 0 ≤ H X0 := (I.tnp.width.reg.pos _).le
  rw [I.hX0e]; linarith

lemma lam_bounds (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T) :
    0 ≤ lam0 ∧ lam0 ≤ 2 := by
  have := I.tnp.width.theta_nonneg; have := I.hlam; have := I.hlam1
  constructor <;> linarith

lemma two_X0_le (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T) :
    2 * (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) := by
  have hX1 := I.X0_gt
  have hX0p : (0 : ℝ) < X0 := by linarith
  have hlog : Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) = 1.01 * Real.log X0 :=
    Real.log_rpow (by linarith) _
  have h2 : Real.log (2 * (X0 : ℝ)) ≤ Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) := by
    rw [hlog, Real.log_mul (by norm_num) hX0p.ne']
    have := Real.log_two_lt_d9
    have := I.hX
    norm_num at this ⊢; nlinarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h2

/-- The window at `x ≥ X₀^{1.01}` lies in `[X₀, ∞)` and `x - H/2 > 1`. -/
lemma window_bounds
    (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    {x : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) :
    0 < H x ∧ (X0 : ℝ) ≤ x - H x / 2 ∧ 1 < x - H x / 2 := by
  have hX1 := I.X0_gt
  have hb := I.two_X0_le
  have hXmle := I.X0m_le
  have hXm0 := I.tnp.width.X0m_pos
  have hHs : H x ≤ x / 10 := I.tnp.width.small x (by linarith)
  have hH0 : 0 < H x := I.tnp.width.reg.pos x
  refine ⟨hH0, by linarith, by linarith⟩

/-- The windows of the centres `x ≤ T` lie below `T + H(T)`. -/
lemma window_le (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    {x y : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) (hxT : x ≤ T) (hy : InW (H x) x y) :
    y ≤ T + H T := by
  have hP := I.tnp.width
  have hX1 := I.X0_gt
  have hb := I.two_X0_le
  have hXmle := I.X0m_le
  have hx2 : X0m / 2 ≤ x := by linarith
  have hlip := hP.lip x T hx2 (by linarith)
  rw [abs_le] at hlip
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hTx : |x - T| = T - x := by rw [abs_of_nonpos (by linarith)]; ring
  rw [hTx] at hlip
  have hHT : 0 ≤ H T := (hP.reg.pos T).le
  have h1 : θ * (T - x) ≤ (T - x) / 100 := by nlinarith
  have := hy.2
  linarith [hlip.2]

lemma start_ge (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    {x y : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) (hy : InW (H x) x y) : (X0 : ℝ) ≤ y := by
  have := (I.window_bounds hx).2.1
  linarith [hy.1]

lemma hZy (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    {y : ℝ} (hy : y ≤ T + H T) : 2 * y / X0m ≤ Z := by
  have hXm0 := I.tnp.width.X0m_pos
  refine le_trans ?_ I.hZ
  exact div_le_div_of_nonneg_right (by linarith) hXm0.le

/-- **Theorem 5.37** at `X₀^{1.01} ≤ x ≤ T`. -/
theorem thm_5_37
    (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    {x : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) (hxT : x ≤ T) :
    0.97 - oTot (H x) x (I.EBR x) (I.jX x) - (I.a x + I.b x + 6 * Real.log x / H x) -
        I.EBR x - I.jX x ≤ Real.log x * (I.ρ x + I.ν x + I.NT x) := by
  obtain ⟨hH0, hw2, hw3⟩ := I.window_bounds hx
  have hX1 := I.X0_gt
  have hXmle := I.X0m_le
  have hP := I.tnp.width
  have hlam2 : 1 + 2 * θ ≤ lam0 := by linarith [hP.theta_nonneg, I.hlam]
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- (predictable)
  have hpred := hpred_of I.B I.K I.R I.hR I.hinj I.ρ I.ν I.NT I.ϑ Tc
    (fun t => j0 * ind X0 t) H I.hmargin hlx0 hH0 (fun g => I.hBx g x) (I.hK x hx hxT)
    (I.hG x hx hxT) (I.hϑ x hx hxT)
  rw [I.hRres] at hpred
  -- (bridge)
  have hbr : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      rhoSh P tw X0m y (ChainInputs.Tp j0 X0 Tc) - (I.EBR x + I.jX x) / Real.log y ≤
        Rres P H tw X0m y (ChainInputs.Tp j0 X0 Tc) := by
    intro y hy1 hy2
    have hW : InW (H x) x y := ⟨hy1, hy2⟩
    have hy : (X0 : ℝ) ≤ y := I.start_ge hx hW
    have hZ := I.hZy (I.window_le hx hxT hW)
    have D := (I.bridge x y hx hxT hW).toBridgeAt I.tnp I.hX0e hXmle hy
    have hly : 0 < Real.log y := Real.log_pos (by linarith)
    have hBR := prop_5_26_hbs I.tnp.hbs I.tnp.hXm hP I.hX0e I.hp2 I.ht I.htv hlam2 I.hlam1
      (hXmle.trans hy) hZ (Real.log_pos hX1) hXmle D.cov D.covL D.sc1 D.sc D.eta
      D.etaSmall D.etaX0 D.theta I.hTm I.hTb D.osc D.X0mem D.termOsc
    have hXB := lemma_5_27 I.tnp.hbs I.tnp.hXm hP I.hX0e I.hp2 I.ht I.htv I.hlam I.hlam1
      (hXmle.trans hy) hZ (Real.log_pos hX1) hXmle D.cov D.sc1 D.sc D.eta D.etaSmall
      D.etaX0.1 D.etaX0Sum D.theta
    exact hbr_of hP.reg hly I.hTm I.hTb I.hj0 hBR hXB D.sizeE D.sizeJ
  -- (g1)
  have hg1pt : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      0.97 ≤ rhoSh P tw X0m y (ChainInputs.Tp j0 X0 Tc) * Real.log y := by
    intro y hy1 hy2
    have hW : InW (H x) x y := ⟨hy1, hy2⟩
    have hy : (X0 : ℝ) ≤ y := I.start_ge hx hW
    have hyT := I.window_le hx hxT hW
    obtain ⟨rA, hd, hA, hB⟩ := I.g1 y hy hyT
    exact (KR.G1.prop_5_35 I.tnp.hbs I.tnp.hXm I.hX I.hHux I.hin I.ht I.htv hXmle hy
      (by linarith [I.hxmax]) (I.hZy hyT) I.hμ0 I.hμ1 hd hA hB).2 (by
        have hHs : H x ≤ x / 10 := hP.small x (by linarith [I.two_X0_le, hP.X0m_pos])
        linarith)
  have hg1 := avg_ge hH0 hw3 (by norm_num) (I.intRS x) hg1pt
  have hg1' : 0.97 - 0.97 * (1 - Real.log x / Real.log (x + H x / 2)) ≤
      Real.log x * Margin.Bavg (H x) (fun y => rhoSh P tw X0m y (ChainInputs.Tp j0 X0 Tc)) x := by
    linarith
  have hδ : Real.log x / Real.log (x - H x / 2) ≤
      1 + (Real.log x / Real.log (x - H x / 2) - 1) := by linarith
  have h537 := Margin.thm_5_37' hH0 hw3 (by linarith [I.EBR_nonneg x, I.jX_nonneg x])
    (I.intRT x) (I.intRS x) hpred hbr hg1' hδ
  unfold oTot
  linarith

lemma hvar_of (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    (t y : ℝ) (hy : InW (H t) t y) : |m y - m t| ≤ Margin.Rec.vSup H m t := by
  have hH : 0 ≤ H t := (I.tnp.width.reg.pos t).le
  have hyt : y = t + (y - t) := by ring
  rw [hyt]
  refine Margin.Rec.le_vSup I.hmbdd ?_
  rw [abs_le]; constructor <;> linarith [hy.1, hy.2]

/-- **Steps 1–5** at `X₀^{1.01} ≤ t ≤ T`. -/
theorem hv_of (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T)
    (t : ℝ) (ht : (X0 : ℝ) ^ (1.01 : ℝ) ≤ t) (htT : t ≤ T) :
    Margin.Rec.vSup H m t * Real.log t ≤ 6.5 * I.p.ES + VX P I.p t := by
  have hX1 := I.X0_gt
  have hX1' : (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) := by linarith [I.two_X0_le]
  have ht1 : 1 < t := by linarith
  have hvs : Margin.Rec.vSup H m = Margin.Rec.vSup H
      (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y) :=
    congrArg (Margin.Rec.vSup H) I.hm
  have hS2 : ∀ t, I.T0 ≤ t → t ≤ T → ∀ w ∈ Margin.Rec.Fset P I.p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Margin.Rec.Step2At H I.ρ (Margin.Rec.vSup H
          (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y))
          I.err z' ∧ I.err z' ≤ I.e t w := by
    intro t ht htT w hw z' h1 h2
    have := I.hS2 t ht htT w hw z' h1 h2
    rwa [hvs] at this
  have hbase : ∀ t, t < I.T0 → Margin.Rec.vSup H
      (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y) t ≤
        Margin.Rec.PhiC P I.p t 1 := by
    intro t ht
    have := I.hbase t ht
    rwa [hvs] at this
  rw [hvs]
  have hvc := Margin.Rec.variation_le_chain_loc P I.p tw I.chain I.hpε I.hT0 I.hT0wf I.hT0T
    I.hρ0 I.hT0' I.hgeom hS2 I.he0 I.hoscV I.hsw I.hS4 hbase t htT
  have hh := I.hhead t ht htT
  have htl := I.htail t ht htT
  unfold VX
  exact hv_of_chain _ _ (Margin.Rec.Aw P I.p) (Margin.Rec.Vv P) ht1 I.chain.hES
    (fun M _ => Margin.Rec.Aw_nonneg (P := P) (p := I.p) M)
    (fun M _ => Margin.Rec.Vv_pos (P := P) M) hvc hh htl

/-- **Proposition 5.38 (a)–(c) on `[X₀, T]`**: `m(t) log t ≥ 0.399` for `X₀ ≤ t ≤ T`, and
`m = 0` below `X₀`. -/
theorem prop_5_38_on
    (I : ChainInputsLoc P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m T) :
    MarginOn m X0 T := by
  have hX1 := I.X0_gt
  have hXmle := I.X0m_le
  have h2X := I.two_X0_le
  refine ⟨fun t ht htT => ?_, I.hz⟩
  rcases lt_or_ge t (2 * X0) with h1 | h1
  · -- (c)
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    rcases I.hc t ht h1 htT with ⟨Tq, hm, hT⟩ | ⟨Tq, rt, hm, hT, hr, hl⟩
    · linarith [Margin.Var.prop_5_38_c_low hlt hm hT]
    · have hΛ : (100000000 : ℝ) ≤ Real.log X0 := by have := I.hX; norm_num at this ⊢; linarith
      have := Margin.Var.prop_5_38_c_high hlt hΛ hm hT hr hl
      linarith
  rcases le_or_gt t ((X0 : ℝ) ^ (1.01 : ℝ)) with h2 | h2
  · -- (b)
    have hy : (X0 : ℝ) ≤ t := by linarith
    have hyT : t ≤ T + H T := by linarith [(I.tnp.width.reg.pos T).le]
    obtain ⟨rA, hd, hA, hB⟩ := I.g1 t hy hyT
    have h35 := (KR.G1.prop_5_35 I.tnp.hbs I.tnp.hXm I.hX I.hHux I.hin I.ht I.htv hXmle hy
      (by linarith [I.hxmax]) (I.hZy hyT) I.hμ0 I.hμ1 hd hA hB).1 h2
    exact Margin.prop_5_38_b (I.hsum t h1 h2 htT) h35 (I.hjb t h1 h2 htT)
  · -- (a)
    have ht' : (X0 : ℝ) ^ (1.01 : ℝ) ≤ t := h2.le
    obtain ⟨hH0, -, hw3⟩ := I.window_bounds ht'
    have h37 := I.thm_5_37 ht' htT
    have := Margin.Var.prop_5_38_a_of hH0 (by linarith) (I.intm t)
      (fun y hy1 hy2 => I.hvar_of t y ⟨hy1, hy2⟩) (I.hv_of t ht' htT) (I.hdec t ht' htT)
      (I.hBt t ht' htT) (I.hsη t ht' htT) (by linarith) (I.hsmall t ht' htT)
    linarith

end ChainInputsLoc

end KR.Chain

end
