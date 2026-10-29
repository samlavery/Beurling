module

public import RequestProject.Beurling.Noise.MarginChain
public import RequestProject.Beurling.Noise.MarginRecStep
public import RequestProject.Beurling.Noise.TNPThread

/-!
# The chain Bridge → Theorem 5.37 → Proposition 5.38 → Corollary 5.40, second form

`ChainInputs2` is `ChainInputs` (`MarginChain.lean`) with:

* the Lemma 5.20 fields of the bridge data (`EtaBound` with `λ₀ C_N E_η ≤ ½`, `ThetaBlk`) and
  the scale covering hypotheses removed: they are proved on the dyadic scales `dyScales X₀ y N`
  by `TauNearProof*.lean` (`TNPThread.lean`); in their place the standing hypotheses of that
  proof, `TNP.Hyp` (with Corollary 6.3(ii), field `count`), the standard width at `X₀⁻/2`, and
  the horizon `18 y ≤ Z`;
* the variation bound of Steps 1–5 of Proposition 5.38 (`hv`, with `vt`, `hvar`, `E_S`, `V`)
  removed: it is proved from the recursion (`Margin.Rec.variation_le_chain`: Steps 1–3 with the
  super-solution) and Step 5 (`hv_of_chain` below); in its place the remaining inputs of those
  steps (`Step2At`, `HStep`, the oscillation, the filter switching, Step 4, the base case, the
  `A₀(0.045)` transfer and Rankin's tail), with `m = T' - K_pt ρ̃ - NT_pt`.

`ChainInputs2.toCI` builds a `ChainInputs`, so Theorem 5.37, Proposition 5.38 and Corollary 5.40
follow (`thm_5_37`, `prop_5_38`, `cor_5_40`, `cor_5_40_queue`).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem

namespace KR.Chain

open KR.TNP

/-! ## Step 5 in level form -/

/-- **Step 5 of the proof of Proposition 5.38**, for a chain sum over levels: the head
`V(M) ≤ √t` costs `log(t/V(M)) ≥ ½ log t` and `∑ A ≤ 1 + A₀(0.045) ≤ 3.218`; the tail is at most
`0.06 E_S/log t`. -/
theorem hv_of_chain {t ES j v : ℝ} (S1 S2 : Finset ℕ) (A V : ℕ → ℝ) (ht : 1 < t)
    (hES : 0 ≤ ES) (hA : ∀ M ∈ S1, 0 ≤ A M) (hV0 : ∀ M ∈ S1, 0 < V M)
    (hv : v ≤ ∑ M ∈ S1, A M * (ES / Real.log (t / V M)) + j * ∑ M ∈ S2, A M)
    (hhead : ∑ M ∈ S1.filter (fun M => V M ≤ √t), A M ≤ 1 + BSCert.Consts.ordA 1.955)
    (htail : ∑ M ∈ S1.filter (fun M => ¬ V M ≤ √t), A M * (ES / Real.log (t / V M)) ≤
      0.06 * ES / Real.log t) :
    v * Real.log t ≤ 6.5 * ES + Real.log t * (j * ∑ M ∈ S2, A M) := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have hA0 := BSCert.Consts.ordA_1955_le
  have hsq : Real.log √t = Real.log t / 2 := Real.log_sqrt (by linarith)
  have hhd : ∀ M ∈ S1.filter (fun M => V M ≤ √t),
      A M * (ES / Real.log (t / V M)) ≤ A M * (2 * ES / Real.log t) := by
    intro M hM
    obtain ⟨hM1, hM2⟩ := Finset.mem_filter.mp hM
    have hV := hV0 M hM1
    have hl : Real.log t / 2 ≤ Real.log (t / V M) := by
      rw [Real.log_div (by linarith) hV.ne']
      have := Real.log_le_log hV hM2
      linarith
    apply mul_le_mul_of_nonneg_left _ (hA M hM1)
    rw [div_le_div_iff₀ (by linarith) hlt]
    nlinarith
  have hsplit := (Finset.sum_filter_add_sum_filter_not S1 (fun M => V M ≤ √t)
    (fun M => A M * (ES / Real.log (t / V M)))).symm
  have hH : ∑ M ∈ S1.filter (fun M => V M ≤ √t), A M * (ES / Real.log (t / V M)) ≤
      (1 + 2.218) * (2 * ES / Real.log t) := by
    refine (Finset.sum_le_sum hhd).trans ?_
    rw [← Finset.sum_mul]
    have : 0 ≤ 2 * ES / Real.log t := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have hsum : ∑ M ∈ S1, A M * (ES / Real.log (t / V M)) ≤ 6.5 * ES / Real.log t := by
    rw [hsplit]
    have : (1 + 2.218) * (2 * ES / Real.log t) + 0.06 * ES / Real.log t ≤
        6.5 * ES / Real.log t := by
      have e1 : (1 + 2.218) * (2 * ES / Real.log t) + 0.06 * ES / Real.log t =
          (6.436 * ES + 0.06 * ES) / Real.log t := by field_simp; ring
      rw [e1, div_le_div_iff_of_pos_right hlt]
      nlinarith
    linarith
  have e : 6.5 * ES / Real.log t * Real.log t = 6.5 * ES := by field_simp
  nlinarith

/-! ## The data -/

/-- The `V_{X₀}` term of Step 5: `log t · j ∑_{|t/M - X₀| ≤ R₀} H_ord(M) M^{ε'-2}`. -/
noncomputable def VX (P : BeurlingSystem) (p : Margin.Rec.CP) (t : ℝ) : ℝ :=
  Real.log t * (p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter
    (fun M => |t / Margin.Rec.Vv P M - p.X0| ≤ p.R0), Margin.Rec.Aw P p M)

/-- **The bridge data at a start `y`**, with Lemma 5.20 discharged: the dyadic scales
`dyScales X₀ y N` (`N`, `K` large), the step (iii) bounds `s⁰` (`EtaX0Sum`), the oscillation
`o` (`OscBound`), `TermOsc`, and the size relations to `E_BR` and `j`; the `θ`-blocks are
`sTheta P H X₀⁻ K`. -/
structure BridgeAt2 (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 : ℝ)
    (Tc : ℝ → ℝ) (j0 y EBR j : ℝ) where
  N : ℕ
  K : ℕ
  hN2 : 2 < N
  hN : y < X0 * 2 ^ N / 4
  hK : √(2 * y) ≤ Pk X0m K
  s0 : ℝ → ℝ
  o : ℝ → ℝ
  /-- **Proposition 5.18, step (iii)** -/
  etaX0 : EtaX0Sum P H X0m X0 (dyScales X0 y N) s0
  etaX0Sum : ∑ v ∈ dyScales X0 y N, s0 v ≤ 1.52
  /-- the oscillation of `T_c` (eq. (osc)) -/
  osc : OscBound P H y Tc (dyScales X0 y N) o
  /-- the terminal oscillation (proof of Proposition 5.26, second bullet) -/
  termOsc : TermOsc P H tw X0m y Tc (o X0)
  /-- `E_BR` bounds the right side of Proposition 5.26 -/
  sizeE : (5.1 * CNc X0 + CSc) * ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u +
      8.4 * CNc X0 * ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v ≤ EBR
  /-- eq. (jX0) -/
  sizeJ : j0 * (xbB P H tw X0m y X0 θ lam0 +
      4.3 * CNc X0 * (∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v) /
        Real.log y) * Real.log y ≤ j

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `BridgeAt2` gives `BridgeAt`: the Lemma 5.20 fields from `TauNearProof*`. -/
noncomputable def BridgeAt2.toBridgeAt {X0 lam0 : ℝ} {Tc : ℝ → ℝ} {j0 y EBR j : ℝ}
    (D : BridgeAt2 P H tw X0m X0 θ lam0 Tc j0 y EBR j) (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hy : X0 ≤ y) (h18 : 18 * y ≤ Z)
    (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
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
  sc1 := fun u hu => by
    linarith [(scale_facts h hX0e hX0m h18 (N := D.N) D.hK).2.1 u hu]
  sc := fun u hu => dyScales_kind (sizes h hX0e hX0m).2.2.2.2 (sizes h hX0e hX0m).2.2.1 hu
  eta := (etaBound_energy h (scale_facts h hX0e hX0m h18 D.hK).1
    (scale_facts h hX0e hX0m h18 D.hK).2.1 (scale_facts h hX0e hX0m h18 D.hK).2.2.1
    (scale_facts h hX0e hX0m h18 D.hK).2.2.2).1
  etaSmall := energy_small h hH (scale_facts h hX0e hX0m h18 D.hK).1
    (scale_facts h hX0e hX0m h18 D.hK).2.1 (scale_facts h hX0e hX0m h18 D.hK).2.2.1
    (scale_facts h hX0e hX0m h18 D.hK).2.2.2 hlam0 hlam (CNt_bounds (sizes h hX0e hX0m).2.1).1
    (CNt_bounds (sizes h hX0e hX0m).2.1).2
  etaX0 := D.etaX0
  etaX0Sum := D.etaX0Sum
  theta := (thetaBlk_sum h (scale_facts h hX0e hX0m h18 D.hK).1
    (scale_facts h hX0e hX0m h18 D.hK).2.1 (scale_facts h hX0e hX0m h18 D.hK).2.2.1
    (scale_facts h hX0e hX0m h18 D.hK).2.2.2).1
  osc := D.osc
  X0mem := X0_mem_dyScales D.hN2 hy
  termOsc := D.termOsc
  sizeE := D.sizeE
  sizeJ := D.sizeJ

/-- **The inputs of the chain, with Lemma 5.20 and Steps 1–5 of Proposition 5.38 discharged**
(see the module docstring); `X₁ = X₀^{1.01}`. -/
structure ChainInputs2 (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ)
    (Z η1 η2 : ℝ) (ε1 : ℝ → ℝ) (ε θ lam0 : ℝ) (Tc : ℝ → ℝ) (j0 xmax : ℝ)
    (μ0 μ1 ρedge m : ℝ → ℝ) where
  -- standing hypotheses
  /-- (HBS), `log X₀⁻ ≥ 10⁸`, `PaperWidth`, the decision order and Corollary 6.3(ii)
  (`TNP.Hyp`, the hypotheses of the proof of Lemma 5.20) -/
  tnp : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ
  /-- the standard width at `X₀⁻/2` (§5.1) -/
  hHstd : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2)
  hX : 10 ^ 8 ≤ Real.log X0
  hX0e : X0m = X0 - H X0 / 2
  hp2 : ∀ j, 2 ≤ P.p j
  ht : ∀ r, r.Prime → 0 < tw r
  htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r
  hlam : 1 + 3 * θ ≤ lam0
  hlam1 : lam0 ≤ 1.001
  hTm : Measurable Tc
  hTb : ∀ t, |Tc t| ≤ 2
  hj0 : 0 ≤ j0
  /-- (huxley) and Lemma 7.3's inputs (§7) -/
  hHux : BaseRange.HuxleyFrom X0
  hin : BaseRange.Lemma73Inputs X0 xmax μ0 μ1 ρedge
  hμ0 : ∀ u : ℝ, u < X0 → μ0 u = 0
  hμ1 : ∀ u : ℝ, u < X0 → μ1 u = 0
  /-- the heights read: `y ≤ xmax` and `2y/X₀⁻ ≤ Z` on the windows used -/
  hxmax : ∀ y, (X0 : ℝ) ≤ y → y ≤ xmax
  /-- the horizon of the proof of Lemma 5.20 (`18 y ≤ Z`; it implies `2y/X₀⁻ ≤ Z`) -/
  hZ18 : ∀ y, (X0 : ℝ) ≤ y → 18 * y ≤ Z
  -- the window quantities, as functions of the centre `x`
  EBR : ℝ → ℝ
  jX : ℝ → ℝ
  EBR_nonneg : ∀ x, 0 ≤ EBR x
  jX_nonneg : ∀ x, 0 ≤ jX x
  /-- **Propositions 5.26 and Lemma 5.27** at every start of the windows of `x ≥ X₀^{1.01}/2` -/
  bridge : ∀ x y, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → InW (H x) x y →
    BridgeAt2 P H tw X0m X0 θ lam0 Tc j0 y (EBR x) (jX x)
  /-- **Proposition 5.35**, residual inputs, at every start `y ≥ X₀` -/
  g1 : ∀ y, (X0 : ℝ) ≤ y → G1At P tw X0m X0 μ0 μ1 ρedge (fun t => Tc t + j0 * ind X0 t) y
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
  hK : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → Real.log x *
    |B (K (B (R ((B Tc - Tc) + (fun z => ϑ z / H z) - ν - NT)))) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → Real.log x *
    |B (R (K ((B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t)) -
      B (B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t))))) x| ≤ b x
  /-- `|ϑ| ≤ 6` (eq. (Ttilde)) -/
  hϑ : ∀ x, |ϑ x| ≤ 6
  /-- window integrability of `R_res T'` and `ρ^sh T'` -/
  intRT : ∀ x, IntervalIntegrable (fun y => Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  intRS : ∀ x, IntervalIntegrable (fun y => rhoSh P tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  -- **Proposition 5.38(a)**
  Bt : ℝ → ℝ
  η : ℝ → ℝ
  sη : ℝ
  intm : ∀ t, IntervalIntegrable m volume (t - H t / 2) (t + H t / 2)
  /-- **Steps 1–5 of the proof of Proposition 5.38**: the parameters of the recursion and its
  super-solution (`Margin.Rec.CP`, `ChainHyp`), and `m = T' - K_pt ρ̃ - NT_pt` -/
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
  hm : m = fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw p.Xm ρ y - NTpt y
  hmbdd : ∃ C, ∀ y, |m y| ≤ C
  hρ0 : ∀ z, z < p.Xm → ρ z = 0
  hT0' : ∀ t, T0 ≤ t → 0 ≤ t ∧ 1.01 * H t ≤ t
  /-- `H`-regularity at a cofactor (`HStep`) -/
  hgeom : ∀ t, T0 ≤ t → ∀ w ∈ Margin.Rec.Fset P p t,
    Margin.Rec.HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w)
  /-- **Step 2** (`Step2At`: exact form, Lemma 5.22 on `A±`, the strip comparison) -/
  hS2 : ∀ t, T0 ≤ t → ∀ w ∈ Margin.Rec.Fset P p t, ∀ z',
    t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
      Margin.Rec.Step2At H ρ (Margin.Rec.vSup H m) err z' ∧ err z' ≤ e t w
  he0 : ∀ t, T0 ≤ t → ∀ w ∈ Margin.Rec.Fset P p t, 0 ≤ e t w
  /-- the oscillation of `T'` (eq. (osc)) -/
  hoscV : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t →
    |(Tc (t + hh) + j0 * ind X0 (t + hh)) - (Tc t + j0 * ind X0 t)| ≤ oV t
  /-- filter switching and `ΔNT ≤ 2η` -/
  hsw : ∀ t, T0 ≤ t → ∀ hh, |hh| ≤ 1.01 * H t →
    |∑ w ∈ Margin.Rec.Fset P p t, (Margin.Rec.kap P tw (t + hh) w - Margin.Rec.kap P tw t w) *
        (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NTpt (t + hh) - NTpt t| ≤ 2 * ηV t
  /-- **Step 4** (`Margin.Var.step4` proves it from Lemma 5.21) -/
  hS4 : ∀ t, T0 ≤ t →
    oV t + 2 * ηV t + ∑ w ∈ Margin.Rec.Fset P p t, e t w / KR.Vl P w ≤ p.ES / Real.log t
  /-- the base case below `T₀` -/
  hbase : ∀ t, t < T0 → Margin.Rec.vSup H m t ≤ Margin.Rec.PhiC P p t 1
  /-- **Step 5**: the transfer of `A₀(0.045)` to `𝒩` (head of the chain sum) -/
  hhead : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t →
    ∑ M ∈ ((KR.NAll P t (p.Xm / 2)).filter (fun M => Margin.Rec.cutL P p M ≤
        t / Margin.Rec.Vv P M)).filter (fun M => Margin.Rec.Vv P M ≤ √t),
      Margin.Rec.Aw P p M ≤ 1 + BSCert.Consts.ordA 1.955
  /-- **Step 5**: Rankin's tail bound (`τ ≤ 0.06`) -/
  htail : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t →
    ∑ M ∈ ((KR.NAll P t (p.Xm / 2)).filter (fun M => Margin.Rec.cutL P p M ≤
        t / Margin.Rec.Vv P M)).filter (fun M => ¬ Margin.Rec.Vv P M ≤ √t),
      Margin.Rec.Aw P p M * (p.ES / Real.log (t / Margin.Rec.Vv P M)) ≤ 0.06 * p.ES / Real.log t
  /-- Step 6(a): `M = Bm + B NT_pt + ϑ/H` with `|B NT_pt + ϑ/H| ≤ 54η + 6/H` -/
  hdec : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → ρ t + ν t + NT t = Margin.Bavg (H t) m t + Bt t
  hBt : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → |Bt t| ≤ 54 * η t + 6 / H t
  hsη : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → Real.log t * η t ≤ sη
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t →
    oTot (H t) t (EBR t) (jX t) + (a t + b t + 6 * Real.log t / H t) + EBR t + jX t +
      54 * sη + 6 * Real.log t / H t + 6.5 * p.ES + VX P p t ≤ 0.01
  -- **Proposition 5.38(b)**
  jb : ℝ → ℝ
  /-- Step 6(b), "Sum": `m log t ≥ ρ^sh log t - j_{X₀} - 10⁻¹²` -/
  hsum : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) →
    rhoSh P tw X0m t (fun s => Tc s + j0 * ind X0 s) * Real.log t - jb t - 1 / 10 ^ 12 ≤
      m t * Real.log t
  /-- **Proposition 5.33**: `j_{X₀} ≤ 0.4209` -/
  hjb : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) → jb t ≤ 0.4209
  -- **Proposition 5.38(c)** (Step 6(c)): the source bounds on `[X₀, 2X₀)`
  hc : ∀ t, (X0 : ℝ) ≤ t → t < 2 * X0 →
    (∃ Tp, m t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
    (∃ Tp rt, m t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
      rt ≤ 0.5001 / Real.log X0 ∧ Real.log t ≤ Real.log X0 + 0.7)
  /-- `m = 0` below `X₀` -/
  hz : ∀ t : ℝ, t < X0 → m t = 0


namespace ChainInputs2

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ}
  {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} {ε θ lam0 : ℝ} {Tc : ℝ → ℝ} {j0 xmax : ℝ}
  {μ0 μ1 ρedge m : ℝ → ℝ}

lemma X0_gt (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    (1 : ℝ) < X0 := BaseRange.one_lt_of_log I.hX

lemma X0m_le (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    X0m ≤ X0 := by
  have hH : 0 ≤ H X0 := (I.tnp.width.reg.pos _).le
  rw [I.hX0e]; linarith

lemma lam_bounds (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    0 ≤ lam0 ∧ lam0 ≤ 2 := by
  have := I.tnp.width.theta_nonneg; have := I.hlam; have := I.hlam1
  constructor <;> linarith

/-- The starts of the windows of `x ≥ X₀^{1.01}` are `≥ X₀`. -/
lemma start_ge (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {x y : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) (hy : InW (H x) x y) : (X0 : ℝ) ≤ y := by
  have hX1 := I.X0_gt
  have hX1' : (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) :=
    Real.self_le_rpow_of_one_le hX1.le (by norm_num)
  have hXm0 := I.tnp.width.X0m_pos
  have hXmle := I.X0m_le
  have hHs : H x ≤ x / 10 := I.tnp.width.small x (by linarith)
  have hlog : Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) = 1.01 * Real.log X0 :=
    Real.log_rpow (by linarith) _
  have hbig : 2 * (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) := by
    have hX0p : (0 : ℝ) < X0 := by linarith
    have h2 : Real.log (2 * (X0 : ℝ)) ≤ Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) := by
      rw [hlog, Real.log_mul (by norm_num) hX0p.ne']
      have := Real.log_two_lt_d9
      have := I.hX
      norm_num at this ⊢; nlinarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h2
  have := hy.1
  linarith

/-- The window variation of `m` is at most `vSup H m`. -/
lemma hvar_of (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    (t y : ℝ) (hy : InW (H t) t y) : |m y - m t| ≤ Margin.Rec.vSup H m t := by
  have hH : 0 ≤ H t := (I.tnp.width.reg.pos t).le
  have hyt : y = t + (y - t) := by ring
  rw [hyt]
  refine Margin.Rec.le_vSup I.hmbdd ?_
  rw [abs_le]; constructor <;> linarith [hy.1, hy.2]

/-- **Steps 1–5 of Proposition 5.38**: `v(t) log t ≤ 6.5 E_S + V_{X₀}(t)`, from the recursion
(`variation_le_chain`) and Step 5 (`hv_of_chain`). -/
theorem hv_of (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    (t : ℝ) (ht : (X0 : ℝ) ^ (1.01 : ℝ) ≤ t) :
    Margin.Rec.vSup H m t * Real.log t ≤ 6.5 * I.p.ES + VX P I.p t := by
  have hX1 := I.X0_gt
  have hX1' : (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) :=
    Real.self_le_rpow_of_one_le hX1.le (by norm_num)
  have ht1 : 1 < t := by linarith
  have hvs : Margin.Rec.vSup H m = Margin.Rec.vSup H
      (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y) :=
    congrArg (Margin.Rec.vSup H) I.hm
  have hS2 : ∀ t, I.T0 ≤ t → ∀ w ∈ Margin.Rec.Fset P I.p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Margin.Rec.Step2At H I.ρ (Margin.Rec.vSup H
          (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y))
          I.err z' ∧ I.err z' ≤ I.e t w := by
    intro t ht w hw z' h1 h2
    have := I.hS2 t ht w hw z' h1 h2
    rwa [hvs] at this
  have hbase : ∀ t, t < I.T0 → Margin.Rec.vSup H
      (fun y => (Tc y + j0 * ind X0 y) - KR.Sharp.Kpt P tw I.p.Xm I.ρ y - I.NTpt y) t ≤
        Margin.Rec.PhiC P I.p t 1 := by
    intro t ht
    have := I.hbase t ht
    rwa [hvs] at this
  rw [hvs]
  have hvc := Margin.Rec.variation_le_chain P I.p tw I.chain I.hpε I.hT0 I.hT0wf I.hρ0 I.hT0'
    I.hgeom hS2 I.he0 I.hoscV I.hsw I.hS4 hbase t
  have hh := I.hhead t ht
  have htl := I.htail t ht
  unfold VX
  exact hv_of_chain _ _ (Margin.Rec.Aw P I.p) (Margin.Rec.Vv P) ht1 I.chain.hES
    (fun M _ => Margin.Rec.Aw_nonneg (P := P) (p := I.p) M)
    (fun M _ => Margin.Rec.Vv_pos (P := P) M) hvc hh htl

/-- `ChainInputs2` gives the inputs `ChainInputs` of `MarginChain.lean`. -/
noncomputable def toCI
    (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m where
  hbs := I.tnp.hbs
  hXm := I.tnp.hXm
  hX := I.hX
  hP := I.tnp.width
  hX0e := I.hX0e
  hp2 := I.hp2
  ht := I.ht
  htv := I.htv
  hlam := I.hlam
  hlam1 := I.hlam1
  hTm := I.hTm
  hTb := I.hTb
  hj0 := I.hj0
  hHux := I.hHux
  hin := I.hin
  hμ0 := I.hμ0
  hμ1 := I.hμ1
  hxmax := I.hxmax
  hZ := fun y hy => xZ_of I.tnp (I.X0m_le.trans hy) (I.hZ18 y hy)
  EBR := I.EBR
  jX := I.jX
  EBR_nonneg := I.EBR_nonneg
  jX_nonneg := I.jX_nonneg
  bridge := fun x y hx hy => (I.bridge x y hx hy).toBridgeAt I.tnp I.hHstd I.hX0e I.X0m_le
    (I.start_ge hx hy) (I.hZ18 y (I.start_ge hx hy)) I.lam_bounds.1 I.lam_bounds.2
  g1 := I.g1
  B := I.B
  K := I.K
  R := I.R
  hR := I.hR
  hinj := I.hinj
  ρ := I.ρ
  ν := I.ν
  NT := I.NT
  ϑ := I.ϑ
  hmargin := I.hmargin
  hBx := I.hBx
  hRres := I.hRres
  a := I.a
  b := I.b
  hK := I.hK
  hG := I.hG
  hϑ := I.hϑ
  intRT := I.intRT
  intRS := I.intRS
  vt := Margin.Rec.vSup H m
  Bt := I.Bt
  η := I.η
  sη := I.sη
  ES := fun _ => I.p.ES
  V := VX P I.p
  intm := I.intm
  hvar := fun t _ y hy => I.hvar_of t y hy
  hv := I.hv_of
  hdec := I.hdec
  hBt := I.hBt
  hsη := I.hsη
  hsmall := I.hsmall
  jb := I.jb
  hsum := I.hsum
  hjb := I.hjb
  hc := I.hc
  hz := I.hz

/-- **Theorem 5.37** for the realised system, from `ChainInputs2`. -/
theorem thm_5_37 (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {x : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) :
    0.97 - oTot (H x) x (I.EBR x) (I.jX x) - (I.a x + I.b x + 6 * Real.log x / H x) -
        I.EBR x - I.jX x ≤ Real.log x * (I.ρ x + I.ν x + I.NT x) :=
  I.toCI.thm_5_37 hx

/-- **Proposition 5.38** (a)–(c) for the realised system, from `ChainInputs2`. -/
theorem prop_5_38 (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    Margin.PointwiseMargin m X0 :=
  I.toCI.prop_5_38

/-- **Corollary 5.40 (R1′ on every window)** for the realised system, from `ChainInputs2`. -/
theorem cor_5_40 (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, (X0 : ℝ) ≤ t → t ≤ b → Real.log t ≤ L) (hL0 : 0 < L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2) :
    0.399 * max (b - max a (X0 : ℝ)) 0 / L - 2 ≤ ell - comp :=
  I.toCI.cor_5_40 hab hm hL hL0 hbook

/-- **Corollary 5.40 in the form used in Theorem 6.6**, from `ChainInputs2`. -/
theorem cor_5_40_queue
    (I : ChainInputs2 P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, (X0 : ℝ) ≤ t → t ≤ b → Real.log t ≤ L) (hL1 : 1 ≤ L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2)
    (hell : ell ≤ 1.01 * max (b - max a (X0 : ℝ)) 0 + 1) :
    comp ≤ ell * (1 - 0.15 / L) + 3 :=
  I.toCI.cor_5_40_queue hab hm hL hL1 hbook hell

end ChainInputs2

end KR.Chain

end
