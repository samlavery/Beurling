module

public import RequestProject.Beurling.Noise.RML6Bridge
public import RequestProject.Beurling.Noise.TcLocal

/-!
# The bridge record with `|T_c| ≤ 2` only below the (HBS) horizon

`bridgeR_mk_loc`, `bridgeR_real_loc` : the versions of `bridgeR_mk`, `bridgeR_real` that need
`|T_c| ≤ 2` only below a height `Y` with `1.2 y ≤ Y` (for the realised system, `Y = X₀⁻ Z`, the
(HBS) horizon of Lemma 6.27(b)). The oscillation is that of the clamped function
`T_c(min(·, Y))` (`KR.TcLoc.clampT`), which agrees with `T_c` at every point the bridge reads.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction KR KR.TNP

namespace KR.TcLoc

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- The oscillation input for `T_c` from that of the clamped function. -/
lemma oscBound_unclamp (hO : KR.Ops.OpHyp P H X0m) {y Y : ℝ} (hy : X0m ≤ y)
    (hY : 1.2 * y ≤ Y) {Tc : ℝ → ℝ} {Sc : Finset ℝ} {o : ℝ → ℝ}
    (h : OscBound P H y (clampT Y Tc) Sc o) : OscBound P H y Tc Sc o := by
  intro u hu
  refine ⟨(h u hu).1, fun n hn hn2 s hs => ?_⟩
  obtain ⟨h1, h2⟩ := osc_point_le hO hy hs
  rw [← clampT_eq (Tc := Tc) (h2.trans hY), ← clampT_eq (Tc := Tc) (h1.trans hY)]
  exact (h u hu).2 n hn hn2 s hs

/-- The terminal oscillation input for `T_c` from that of the clamped function. -/
lemma termOsc_unclamp (hO : KR.Ops.OpHyp P H X0m) {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) {y Y : ℝ} (hXy : X0 ≤ y)
    (hY : 1.2 * y ≤ Y) {Tc : ℝ → ℝ} {oX0 : ℝ} (h : TermOsc P H tw X0m y (clampT Y Tc) oX0) :
    TermOsc P H tw X0m y Tc oX0 := by
  intro n t hne
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have ht := KR.Chain.SX0_support (x := y) hP hX0 hval2 hne
  have hHX : H X0 ≤ X0 / 10 := hO.small X0 (by
    have := hO.X0m_pos; have := hO.pos X0; linarith)
  have hX0p : 0 ≤ X0 := by have := hO.X0m_pos; have := hO.pos X0; linarith
  rw [← clampT_eq (Tc := Tc) (show t ≤ Y by nlinarith)]
  exact h n t hne

end KR.TcLoc

namespace BModel

open KR.Chain KR.TcLoc

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **The bridge record at a start `y`** with `|T_c| ≤ 2` only below `Y ≥ 1.2 y`; the
oscillation is `o = oscR H (T_c(min(·, Y)))`. -/
noncomputable def bridgeR_mk_loc (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hO : KR.Ops.OpHyp P H X0m)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 θH lam0 j0 y EBR j Y : ℝ}
    {Tc : ℝ → ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0)
    (hX96 : (10 : ℝ) ^ 96 ≤ X0)
    (hy : X0 ≤ y) (hyZ : y ≤ Z) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) (hY : 1.2 * y ≤ Y)
    (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (hTlow : ∀ t, t ≤ X0 → Tc t = 0)
    (N K : ℕ) (hN2 : 2 < N) (hN : y < X0 * 2 ^ N / 4) (hK : √(2 * y) ≤ Pk X0m K)
    (hosc : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * oscR H (clampT Y Tc) u ≤
      Real.exp (-83))
    (hEBR : Real.exp (-76) ≤ EBR)
    (hj : jXat P H tw X0m X0 θH lam0 j0 N K y ≤ j) :
    BridgeR P H tw X0m X0 θH lam0 Tc j0 y EBR j :=
  have hXY : X0 ≤ Y := by
    have := (sizes h hX0e hX0m).2.2.2.2; nlinarith
  have hlow : ∀ t, t ≤ X0 → clampT Y Tc t = 0 := fun t ht => by
    rw [clampT_eq (ht.trans hXY)]; exact hTlow t ht
  let B := bridgeR_mk h hH (tw := tw) (θH := θH) (j0 := j0) (EBR := EBR) (j := j) hX0e hX0m
    hX96 hy hyZ hlam0 hlam (clampT_abs_le hTb) hlow N K hN2 hN hK hosc hEBR hj
  { N := B.N
    K := B.K
    hN2 := B.hN2
    hN := B.hN
    hK := B.hK
    o := B.o
    etaX0Sum := B.etaX0Sum
    osc := oscBound_unclamp hO (hX0m.trans hy) hY B.osc
    termOsc := termOsc_unclamp hO h.width hX0e (p_ge_two_of h (by linarith)) hy hY B.termOsc
    sizeE := B.sizeE
    sizeJ := B.sizeJ
    l520 := B.l520 }

/-- **The bridge record for the realised system** with `|T_c| ≤ 2` only below the (HBS)
horizon, `t/X₀⁻ ≤ Z` (the form `BModel.TcR_abs_le` supplies); the oscillation is that of
`T_c(min(·, X₀⁻ Z))`. -/
noncomputable def bridgeR_real_loc {θ' : ℝ} {X₀ : ℕ} {ω : JitterΩ} {Z η1 η2 ε : ℝ}
    {ε1 : ℝ → ℝ}
    (h : Hyp (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) Z η1 η2 ε1 ε (ε / 10))
    (hX : 10 ^ 8 ≤ Real.log X₀) {lam0 j0 x y : ℝ} (NK : ℝ → ℕ × ℕ)
    (hy : (X₀ : ℝ) ≤ y) (hyZ : y ≤ Z) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hTb : ∀ t, t / Xm X₀ ≤ Z → |TcR θ' X₀ ω j0 t| ≤ 2)
    (hTlow : ∀ t : ℝ, t ≤ (X₀ : ℝ) → TcR θ' X₀ ω j0 t = 0)
    (hNK : 2 < (NK y).1 ∧ y < X₀ * 2 ^ (NK y).1 / 4 ∧ √(2 * y) ≤ Pk (Xm X₀) (NK y).2)
    (hosc : ∑ u ∈ dyScales X₀ y (NK y).1, Real.log (2 * u) *
      oscR (Queue6.Hc X₀) (clampT (Xm X₀ * Z) (TcR θ' X₀ ω j0)) u ≤ Real.exp (-83))
    (hW : InW (Queue6.Hc X₀ x) x y)
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ x) x y} =>
      jXat (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0
        (NK y.1).1 (NK y.1).2 y.1)) :
    BridgeR (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
      (TcR θ' X₀ ω j0) j0 y EBRc
      (jXdef (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0 NK x) :=
  have hp2 : ∀ j, 2 ≤ (PR θ' X₀ ω).p j := p_ge_two_of h (by
    have e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
      unfold Xm Queue6.Hc; rw [max_self]
    have := h.width.reg.pos (X₀ : ℝ)
    linarith)
  have hXmpos : 0 < Xm X₀ := h.width.X0m_pos
  have hXm12 : (1.2 : ℝ) ≤ Xm X₀ := by
    have h1 := KR.WidthReal.Xm_ge hX (X₀ := X₀)
    have h2 := ten96_le hX
    linarith
  have hZ0 : 0 ≤ Z := by have := ten96_le hX; linarith
  bridgeR_mk_loc h (KR.Ops.opHyp_Hc hX h.width hp2) (KR.WidthReal.Hc_Xm_half_le hX)
    (by unfold Xm Queue6.Hc; rw [max_self]) (by
      have e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
        unfold Xm Queue6.Hc; rw [max_self]
      have := h.width.reg.pos (X₀ : ℝ)
      linarith)
    (ten96_le hX)
    hy hyZ hlam0 hlam (by nlinarith)
    (fun t ht => hTb t (by rw [div_le_iff₀ hXmpos]; linarith)) hTlow
    (NK y).1 (NK y).2 hNK.1 hNK.2.1 hNK.2.2 hosc le_rfl (le_jXdef hW hbdd)

end BModel

end
