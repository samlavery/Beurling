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

/-- **The clamp height of correction #109** at a start `y`: the oscillation inputs read `T_c`
only on `(-∞, y/2 + 4.2 H(y)]`. -/
noncomputable def oscHt (H : ℝ → ℝ) (y : ℝ) : ℝ := y / 2 + 4.2 * H y

/-- At a start `y ≥ 0`, a level `n ≥ 2` has `x/n ≤ y/2`, and (for `H` monotone) its window
`|s - y/n| ≤ 1.02 H(y/n)` lies below `y/2 + 1.02 H(y)`. -/
lemma osc_point_half (hO : KR.Ops.OpHyp P H X0m) (hmono : Monotone H) {y : ℝ} (hy : 0 ≤ y)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : |s - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n)) :
    posn P.labelVal y n ≤ y / 2 ∧ s ≤ y / 2 + 1.02 * H y := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hO.p2 _
  have hw : 2 ≤ LemmaM.valN P.labelVal n := two_le_valN hval2 hn
  have hp : posn P.labelVal y n ≤ y / 2 := by
    unfold posn
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpy : posn P.labelVal y n ≤ y := by linarith
  have hH := hmono hpy
  have := (abs_le.mp hs).2
  exact ⟨hp, by linarith⟩

lemma oscHt_le (hO : KR.Ops.OpHyp P H X0m) {y : ℝ} (hy : X0m ≤ y) : oscHt H y ≤ 1.2 * y := by
  have hX := hO.X0m_pos
  have := hO.small y (by linarith)
  unfold oscHt; linarith

/-- The oscillation input for `T_c` from that of `T_c` clamped at `y/2 + 4.2 H(y)`. -/
lemma oscBound_unclamp_half (hO : KR.Ops.OpHyp P H X0m) (hmono : Monotone H) {y : ℝ}
    (hy : 0 ≤ y) {Tc : ℝ → ℝ} {Sc : Finset ℝ} {o : ℝ → ℝ}
    (h : OscBound P H y (clampT (oscHt H y) Tc) Sc o) : OscBound P H y Tc Sc o := by
  intro u hu
  refine ⟨(h u hu).1, fun n hn hn2 s hs => ?_⟩
  obtain ⟨h1, h2⟩ := osc_point_half hO hmono hy hn2 hs
  have hHy := hO.pos y
  have e1 : posn P.labelVal y n ≤ oscHt H y := by unfold oscHt; linarith
  have e2 : s ≤ oscHt H y := by unfold oscHt; linarith
  rw [← clampT_eq (Tc := Tc) e2, ← clampT_eq (Tc := Tc) e1]
  exact (h u hu).2 n hn hn2 s hs

end KR.TcLoc

namespace KR.Chain

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- **The support of `S^{X₀}_n`** at a start `x ≥ 0` lies below `x/2 + 1.03 H(X₀)` (correction
#109: the terminal sources read `T_c` only at heights `≤ x/2 + 2.1 H(x)`). -/
lemma SX0_support_half {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) (hx : 0 ≤ x) {n : ℕ} {t : ℝ}
    (hne : SX0 val x H tw X0m n t ≠ 0) : t ≤ x / 2 + 1.03 * H X0 := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  unfold SX0 SsrcP at hne
  rw [neg_ne_zero] at hne
  obtain ⟨d, hdm, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hd, hXn⟩ := Finset.mem_filter.mp hdm
  have hd1 : d ≠ 1 := fun h => by subst h; exact hdne (srcStep_one hval n t)
  obtain ⟨v, hposd, hvd, ht⟩ := srcStep_support hP hval2 hd1 hdne
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by have := two_le_div_of_mem hd; intro h; subst h; simp at this
  set w := LemmaM.valN val (n / d)
  have hw : 2 ≤ w := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < w := by linarith
  have hpn : posn val x d / w = posn val x n := posn_div hval hdn hn0
  have hXm := hP.X0m_pos
  have hsd := hP.small _ hposd
  have hHd := hP.reg.pos (posn val x d)
  have hXN : |posn val x n - X0m| ≤ 1.02 * H (posn val x d) / w := hXn
  have hpos : X0m / 2 ≤ posn val x n := by
    have h1 : 1.02 * H (posn val x d) / w ≤ 0.102 * posn val x n := by
      rw [← hpn, div_le_iff₀ hw0]
      have : 0.102 * (posn val x d / w) * w = 0.102 * posn val x d := by field_simp
      rw [this]; linarith
    have := (abs_le.mp hXN).1
    nlinarith
  obtain ⟨hR, -⟩ := near_ii hP hX0 hval2 hd hpos hXn
  have hHX := hP.reg.pos X0
  have hX0pos : 0 < X0 := by
    by_contra h; push_neg at h; linarith
  have hsX := hP.small X0 (by linarith)
  have hc : |v / w - posn val x n| ≤ 0.52 * H X0 := by
    rw [← hpn, ← sub_div, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    have : |v - posn val x d| / w * w = |v - posn val x d| := by field_simp
    have h2 : 1.02 * H (posn val x d) ≤ 0.52 * H X0 * w := by
      rwa [div_le_iff₀ hw0] at hR
    linarith
  have hcX : |v / w - X0m| ≤ 1.04 * H X0 := by
    have := abs_sub_le (v / w) (posn val x n) X0m
    have h3 : |posn val x n - X0m| ≤ 0.52 * H X0 := hXN.trans hR
    linarith
  have hc2 : X0m / 2 ≤ v / w := by
    have := (abs_le.mp hcX).1
    linarith
  have hHc : H (v / w) ≤ 1.0154 * H X0 := by
    have hl := hP.lip (v / w) X0 hc2 (by linarith)
    have hθ := hP.theta_le
    have hθ0 := hP.theta_nonneg
    have hd' : |v / w - X0| ≤ 1.54 * H X0 := by
      have := abs_sub_le (v / w) X0m X0
      have e : |X0m - X0| = H X0 / 2 := by
        rw [hX0, show X0 - H X0 / 2 - X0 = -(H X0 / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    have := (abs_le.mp hl).2
    nlinarith [abs_nonneg (v / w - X0)]
  -- `x/n ≤ x/2`
  have hVd : 1 ≤ LemmaM.valN val d := LemmaM.one_le_valN val hval
  have hpd : posn val x d ≤ x := by
    unfold posn; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hpnx : posn val x n ≤ x / 2 := by
    rw [← hpn, div_le_iff₀ hw0]; nlinarith
  have := (abs_le.mp ht).2
  have := (abs_le.mp hc).2
  linarith

end KR.Chain

namespace KR.TcLoc

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- The terminal oscillation input for `T_c` from that of `T_c` clamped at `y/2 + 4.2 H(y)`. -/
lemma termOsc_unclamp_half (hO : KR.Ops.OpHyp P H X0m) (hmono : Monotone H) {X0 ε θ : ℝ}
    (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2) {y : ℝ} (hXy : X0 ≤ y)
    {Tc : ℝ → ℝ} {oX0 : ℝ} (h : TermOsc P H tw X0m y (clampT (oscHt H y) Tc) oX0) :
    TermOsc P H tw X0m y Tc oX0 := by
  intro n t hne
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hO.p2 _
  have hX0p : 0 ≤ X0 := by have := hO.X0m_pos; have := hO.pos X0; linarith
  have ht := KR.Chain.SX0_support_half (x := y) hP hX0 hval2 (by linarith) hne
  have hHm := hmono hXy
  have hHy := hO.pos y
  rw [← clampT_eq (Tc := Tc) (show t ≤ oscHt H y by unfold oscHt; nlinarith)]
  exact h n t hne

/-- **Heights read at a start `x` (correction #109).** For a start `y` in the window of `x`
(`|y - x| ≤ H(x)/2`, `x - H(x)/2 ≥ X₀⁻/2`), every point `s` of the window of a level `n ≥ 2`
of `y` lies below `x/2 + 2.1 H(x)`. So the scale-wise bounds `F̄_r(u)`, `sup F_r⁺` and the
oscillation `o_u` only read heights `≤ x/2 + 2.1 H(x)`, and windows meeting them lie in
`(-∞, x/2 + 4.2 H(x)]`. -/
lemma read_height_le (hO : KR.Ops.OpHyp P H X0m) (hmono : Monotone H) {ε θ : ℝ}
    (hP : PaperWidth H X0m ε θ) {x y : ℝ} (hx : X0m / 2 ≤ x - H x / 2)
    (hy1 : x - H x / 2 ≤ y) (hy2 : y ≤ x + H x / 2) {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : |s - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n)) :
    s ≤ x / 2 + 2.1 * H x := by
  have hHx := hO.pos x
  have hy0 : 0 ≤ y := by have := hO.X0m_pos; linarith
  obtain ⟨-, h2⟩ := osc_point_half hO hmono hy0 hn hs
  have hl := hP.lip y x (by linarith) (by linarith)
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hyx : |y - x| ≤ H x / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hHy : H y ≤ H x + θ * (H x / 2) := by
    have := (abs_le.mp hl).2
    nlinarith [abs_nonneg (y - x)]
  nlinarith

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
    (hy : X0 ≤ y) (hXmZ : X0m ≤ Z) (h18 : 18 * y ≤ Z ^ 2) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hY : 1.2 * y ≤ Y) (hmono : Monotone H)
    (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (hTlow : ∀ t, t ≤ X0 → Tc t = 0)
    (N K : ℕ) (hN2 : 2 < N) (hN : y < X0 * 2 ^ N / 4) (hK : √(2 * y) ≤ Pk X0m K)
    (hosc : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * oscR H (clampT (oscHt H y) Tc) u ≤
      Real.exp (-83))
    (hEBR : Real.exp (-76) ≤ EBR)
    (hj : jXat P H tw X0m X0 θH lam0 j0 N K y ≤ j) :
    BridgeR P H tw X0m X0 θH lam0 Tc j0 y EBR j :=
  have hlow : ∀ t, t ≤ X0 → clampT (oscHt H y) Tc t = 0 := fun t ht => by
    unfold clampT; exact hTlow _ ((min_le_left _ _).trans ht)
  have hYo : oscHt H y ≤ Y := (oscHt_le hO (hX0m.trans hy)).trans hY
  have hTb' : ∀ t, t ≤ oscHt H y → |Tc t| ≤ 2 := fun t ht => hTb t (ht.trans hYo)
  let B := bridgeR_mk h hH (tw := tw) (θH := θH) (j0 := j0) (EBR := EBR) (j := j) hX0e hX0m
    hX96 hy hXmZ h18 hlam0 hlam (clampT_abs_le hTb') hlow N K hN2 hN hK hosc hEBR hj
  { N := B.N
    K := B.K
    hN2 := B.hN2
    hN := B.hN
    hK := B.hK
    o := B.o
    etaX0Sum := B.etaX0Sum
    osc := oscBound_unclamp_half hO hmono (by
      have := hO.X0m_pos; linarith [hX0m.trans hy]) B.osc
    termOsc := termOsc_unclamp_half hO hmono h.width hX0e hy B.termOsc
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
    (hy : (X₀ : ℝ) ≤ y) (hXmZ : Xm X₀ ≤ Z) (hyZ : 2 * y / Xm X₀ ≤ Z) (h18 : 18 * y ≤ Z ^ 2)
    (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hTb : ∀ t, t / Xm X₀ ≤ Z → |TcR θ' X₀ ω j0 t| ≤ 2)
    (hTlow : ∀ t : ℝ, t ≤ (X₀ : ℝ) → TcR θ' X₀ ω j0 t = 0)
    (hNK : 2 < (NK y).1 ∧ y < X₀ * 2 ^ (NK y).1 / 4 ∧ √(2 * y) ≤ Pk (Xm X₀) (NK y).2)
    (hosc : ∑ u ∈ dyScales X₀ y (NK y).1, Real.log (2 * u) *
      oscR (Queue6.Hc X₀) (clampT (oscHt (Queue6.Hc X₀) y) (TcR θ' X₀ ω j0)) u ≤
        Real.exp (-83))
    (hW : InW (Queue6.Hc X₀ x) x y)
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ x) x y} =>
      jXat (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0
        (NK y.1).1 (NK y.1).2 y.1)) :
    BridgeR (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
      (TcR θ' X₀ ω j0) j0 y EBRc
      (jXdef (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0 NK x) :=
  have hp2 : ∀ j, 2 ≤ (PR θ' X₀ ω).p j := p_ge_two_of h hXmZ
  have hXmpos : 0 < Xm X₀ := h.width.X0m_pos
  bridgeR_mk_loc (Y := Xm X₀ * Z) h (KR.Ops.opHyp_Hc hX h.width hp2) (KR.WidthReal.Hc_Xm_half_le hX)
    (by unfold Xm Queue6.Hc; rw [max_self]) (by
      have e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
        unfold Xm Queue6.Hc; rw [max_self]
      have := h.width.reg.pos (X₀ : ℝ)
      linarith)
    (ten96_le hX)
    hy hXmZ h18 hlam0 hlam (by rw [div_le_iff₀ hXmpos] at hyZ; linarith)
    (KR.WidthReal.Hc_mono hX) (fun t ht => hTb t (by rw [div_le_iff₀ hXmpos]; linarith)) hTlow
    (NK y).1 (NK y).2 hNK.1 hNK.2.1 hNK.2.2 hosc le_rfl (le_jXdef hW hbdd)

end BModel

end
