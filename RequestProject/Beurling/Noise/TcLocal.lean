module

public import RequestProject.Beurling.Noise.MarginInt
public import RequestProject.Beurling.Noise.RML6PredRres
public import RequestProject.Beurling.Noise.RML6BridgeOsc

/-!
# The bridge inputs with `|T_c| ≤ 2` only below a height

The construction gives `|T_c| ≤ 2` only below the (HBS) horizon (Lemma 6.27(b) reads (HBS) up
to `t/X₀⁻`). The consumers of `|T_c| ≤ 2` read `T_c` only at heights `≤ 1.2 y` for a start `y`
(`R_res` reads `(-∞, 1.2|y|]`, `ρ^sh` reads the positions `y/n ≤ y`). We replace `T_c` by the
clamped function `T_c(min(·, Y))`, which is bounded everywhere and agrees with `T_c` below `Y`:

* `clampT`, `clampT_abs_le`, `measurable_clampT`, `clampT_eq`;
* `rhoSh_congr` : `ρ^sh g (y)` reads `g` only on `(-∞, y]`;
* `oscBound_clamp`, `termOsc_clamp` : the oscillation inputs transfer;
* `prop_5_26_loc`, `hbr_of_loc` : Proposition 5.26 and the (bridge) input with the local bound;
* `intRT_loc`, `intRS_loc` : the window integrability with the local bound.
-/

@[expose] public section

open Finset MeasureTheory Set Real BeurlingSystem

namespace KR.TcLoc

/-- `T_c` clamped at the height `Y`: `T_c(min(t, Y))`. -/
noncomputable def clampT (Y : ℝ) (Tc : ℝ → ℝ) (t : ℝ) : ℝ := Tc (min t Y)

lemma clampT_eq {Y : ℝ} {Tc : ℝ → ℝ} {t : ℝ} (ht : t ≤ Y) : clampT Y Tc t = Tc t := by
  unfold clampT; rw [min_eq_left ht]

lemma clampT_abs_le {Y : ℝ} {Tc : ℝ → ℝ} (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (t : ℝ) :
    |clampT Y Tc t| ≤ 2 := hTb _ (min_le_right _ _)

lemma measurable_clampT {Y : ℝ} {Tc : ℝ → ℝ} (hTm : Measurable Tc) :
    Measurable (clampT Y Tc) :=
  hTm.comp (measurable_id.min measurable_const)

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- `ρ^sh g (y)` reads `g` only on `(-∞, y]`. -/
lemma rhoSh_congr {y : ℝ} (hy : 0 ≤ y) {F G : ℝ → ℝ} (hFG : ∀ t, t ≤ y → F t = G t) :
    rhoSh P tw X0m y F = rhoSh P tw X0m y G := by
  unfold rhoSh
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hFG _ (posn_le_self (P := P) hy n)]

/-- The positions read by `OscBound` at a start `y ≥ X₀⁻` lie below `1.2 y`. -/
lemma osc_point_le (hO : KR.Ops.OpHyp P H X0m) {y : ℝ} (hy : X0m ≤ y) {n : ℕ} {s : ℝ}
    (hs : |s - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n)) :
    posn P.labelVal y n ≤ 1.2 * y ∧ s ≤ 1.2 * y := by
  have hX := hO.X0m_pos
  have hy0 : 0 ≤ y := by linarith
  have hp := posn_le_self (P := P) hy0 n
  have hpH : H (posn P.labelVal y n) ≤ y / 10 := by
    rcases le_or_gt (X0m / 2) (posn P.labelVal y n) with h | h
    · have := hO.small _ h; linarith
    · have := hO.low _ h; linarith
  have := (abs_le.mp hs).2
  constructor <;> nlinarith

/-- The oscillation input transfers to the clamped function. -/
lemma oscBound_clamp (hO : KR.Ops.OpHyp P H X0m) {y Y : ℝ} (hy : X0m ≤ y) (hY : 1.2 * y ≤ Y)
    {Tc : ℝ → ℝ} {Sc : Finset ℝ} {o : ℝ → ℝ} (h : OscBound P H y Tc Sc o) :
    OscBound P H y (clampT Y Tc) Sc o := by
  intro u hu
  refine ⟨(h u hu).1, fun n hn hn2 s hs => ?_⟩
  obtain ⟨h1, h2⟩ := osc_point_le hO hy hs
  rw [clampT_eq (h2.trans hY), clampT_eq (h1.trans hY)]
  exact (h u hu).2 n hn hn2 s hs

/-- The terminal oscillation input transfers to the clamped function. -/
lemma termOsc_clamp (hO : KR.Ops.OpHyp P H X0m) {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) {y Y : ℝ} (hXy : X0 ≤ y)
    (hY : 1.2 * y ≤ Y) {Tc : ℝ → ℝ} {oX0 : ℝ} (h : TermOsc P H tw X0m y Tc oX0) :
    TermOsc P H tw X0m y (clampT Y Tc) oX0 := by
  intro n t hne
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have ht := KR.Chain.SX0_support (x := y) hP hX0 hval2 hne
  have hHX : H X0 ≤ X0 / 10 := hO.small X0 (by
    have := hO.X0m_pos; have := hO.pos X0; linarith)
  have hX0p : 0 ≤ X0 := by have := hO.X0m_pos; have := hO.pos X0; linarith
  rw [clampT_eq (by nlinarith)]
  exact h n t hne

/-- `BR_c` at a start `y ≥ X₀⁻` reads `T_c` only below `1.2 y`. -/
lemma BRc_congr (hO : KR.Ops.OpHyp P H X0m) {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {y : ℝ}
    (hy : X0m ≤ y) {F G : ℝ → ℝ} (hFG : ∀ t, t ≤ 1.2 * y → F t = G t) :
    BRc P H tw X0m y F = BRc P H tw X0m y G := by
  have hy0 : 0 ≤ y := by have := hO.X0m_pos; linarith
  unfold BRc
  rw [KR.Ops.Rres_congr (tw := tw) hO hP (fun t ht => hFG t (by rwa [abs_of_nonneg hy0] at ht)),
    rhoSh_congr hy0 (fun t ht => hFG t (by linarith))]

/-- **Proposition 5.26 with `|T_c| ≤ 2` only below `1.2 x`.** -/
theorem prop_5_26_loc {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hO : KR.Ops.OpHyp P H X0m)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) (hXx : X0 ≤ x) {Sc : Finset ℝ} {s s0 th : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v)
    (hcovL : ∀ n ∈ levels P X0m x, ∃ u ∈ Sc, n ∈ NW P x u) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0s : EtaX0SumLoc P H X0m X0 Sc s0 x) (hθ : ThetaBlk P H tw X0m Sc th)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, t ≤ 1.2 * x → |Tc t| ≤ 2) {o : ℝ → ℝ}
    (hosc : OscBound P H x Tc Sc o) (hX0S : X0 ∈ Sc) (hTo : TermOsc P H tw X0m x Tc (o X0)) :
    Real.log x * |BRc P H tw X0m x Tc| ≤
      (5.1 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) +
        max (2.01 * BSaias.PhiInf 100000000) 1.4) * ∑ u ∈ Sc, Real.log (2 * u) * o u +
      8.4 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
        ∑ v ∈ Sc, Real.log (2 * v) * th v := by
  rw [BRc_congr (tw := tw) hO hP hx (G := clampT (1.2 * x) Tc)
    (fun t ht => (clampT_eq ht).symm)]
  exact prop_5_26_hbs h hXm hP hX0e hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hcov hcovL hSc1 hSc
    hEta hE hX0s hθ (measurable_clampT hTm) (clampT_abs_le hTb)
    (oscBound_clamp hO hx le_rfl hosc) hX0S (termOsc_clamp hO hP hX0e hp2 hXx le_rfl hTo)

/-- **The input (bridge) of Theorem 5.37 at `y`**, with `|T_c| ≤ 2` only below `1.2 y`. -/
theorem hbr_of_loc (hO : KR.Ops.OpHyp P H X0m) {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    {y X0 j0 E b EBR j : ℝ} (hy : X0m ≤ y) (hly : 0 < Real.log y)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, t ≤ 1.2 * y → |Tc t| ≤ 2) (hj0 : 0 ≤ j0)
    (hBR : Real.log y * |BRc P H tw X0m y Tc| ≤ E)
    (hXB : |Rres P H tw X0m y (KR.Chain.ind X0) - rhoSh P tw X0m y (KR.Chain.ind X0)| ≤ b)
    (hE : E ≤ EBR) (hj : j0 * b * Real.log y ≤ j) :
    rhoSh P tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t) - (EBR + j) / Real.log y ≤
      Rres P H tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t) := by
  have hy0 : 0 ≤ y := by have := hO.X0m_pos; linarith
  set Tc' := clampT (1.2 * y) Tc
  have hcong : ∀ t, t ≤ 1.2 * y →
      Tc' t + j0 * KR.Chain.ind X0 t = Tc t + j0 * KR.Chain.ind X0 t :=
    fun t ht => by show clampT (1.2 * y) Tc t + _ = _; rw [clampT_eq ht]
  have hBR' : Real.log y * |BRc P H tw X0m y Tc'| ≤ E := by
    rwa [BRc_congr (tw := tw) hO hP hy (G := Tc) (fun t ht => clampT_eq ht)]
  have := KR.Chain.hbr_of (tw := tw) hP.reg hly (measurable_clampT hTm) (clampT_abs_le hTb) hj0
    hBR' hXB hE hj
  rwa [rhoSh_congr hy0 (fun t ht => hcong t (by linarith)),
    KR.Ops.Rres_congr (tw := tw) hO hP
      (fun t ht => hcong t (by rwa [abs_of_nonneg hy0] at ht))] at this

/-- **Window integrability of `R_res T'`** with `|T_c| ≤ 2` only below `Y`, for windows with
`1.2|y| ≤ Y`. -/
theorem intRT_loc (hO : KR.Ops.OpHyp P H X0m) {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) {Y : ℝ} (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (j0 X0 : ℝ)
    {a b : ℝ} (hab : a ≤ b) (hY : ∀ y, a ≤ y → y ≤ b → 1.2 * |y| ≤ Y) :
    IntervalIntegrable
      (fun y => Rres P H tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t)) volume a b := by
  have hI := KR.Int.intervalIntegrable_Rres P hP.reg tw hO.X0m_pos
    (KR.Int.Tp_measurable (measurable_clampT (Y := Y) hTm) j0 X0)
    (KR.Int.Tp_abs_le (clampT_abs_le hTb) j0 X0) a b
  refine hI.congr ?_
  rw [uIoc_of_le hab]
  intro y hy
  exact KR.Ops.Rres_congr (tw := tw) hO hP fun t ht => by
    rw [clampT_eq (ht.trans (hY y hy.1.le hy.2))]

/-- **Window integrability of `ρ^sh T'`** with `|T_c| ≤ 2` only below `Y`, for windows in
`[0, Y]`. -/
theorem intRS_loc (hX : 0 < X0m) {Tc : ℝ → ℝ} (hTm : Measurable Tc) {Y : ℝ}
    (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (j0 X0 : ℝ) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hbY : b ≤ Y) :
    IntervalIntegrable
      (fun y => rhoSh P tw X0m y (fun t => Tc t + j0 * KR.Chain.ind X0 t)) volume a b := by
  have hI := KR.Int.intervalIntegrable_rhoSh P tw hX
    (KR.Int.Tp_measurable (measurable_clampT (Y := Y) hTm) j0 X0)
    (KR.Int.Tp_abs_le (clampT_abs_le hTb) j0 X0) a b
  refine hI.congr ?_
  rw [uIoc_of_le hab]
  intro y hy
  exact rhoSh_congr (by linarith [hy.1]) fun t ht => by
    rw [clampT_eq (ht.trans (hy.2.trans hbY))]

end KR.TcLoc

end
