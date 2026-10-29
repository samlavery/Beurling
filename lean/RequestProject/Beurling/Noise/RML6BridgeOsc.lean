module

public import RequestProject.Beurling.Noise.BridgeNear

/-!
# Bridge data for the realised margin: the oscillation `o_u` of `T_c`

* `KR.Chain.oscR H Tc u` : **the oscillation `o_u` of `T_c` at the scale `u`** (proof of
  Proposition 5.26, first bullet; eq. (osc)): the supremum of `|T_c(s) - T_c(t)|` over
  `t ∈ [u, 2u)` and `|s - t| ≤ 2.04 max(H(t), H(u))` — the windows of length `≤ 2.04 H(u)`
  meeting `[u, 2u)` of the paper (for `u ≥ X₀⁻/2`, `H(t) ≤ 2^ε H(u)` by (R_H), so the two
  agree up to the factor `2^ε ≤ 1.001`).
* `KR.Chain.oscBound_oscR` : the field `osc` (`OscBound`) holds for `o = oscR H T_c` at every
  start and every family of scales, for any `T_c` with `|T_c| ≤ 2`.
* `KR.Chain.termOsc_oscR` : the field `termOsc` (proof of Proposition 5.26, second bullet): on
  the support of `S^{X₀}_n`, `|T_c| ≤ o_{X₀}`, given that `T_c` vanishes on `(-∞, X₀]`. The
  support of an `X₀`-near source lies in `[X₀⁻ - 1.6 H(X₀), X₀ + 1.05 H(X₀)]`
  (`SX0_support`).
-/

@[expose] public section

open Finset MeasureTheory Set Real

namespace KR.Chain

/-- **The oscillation `o_u` of `T_c`** at the scale `u`. -/
noncomputable def oscR (H : ℝ → ℝ) (Tc : ℝ → ℝ) (u : ℝ) : ℝ :=
  ⨆ p : {p : ℝ × ℝ // u ≤ p.2 ∧ p.2 < 2 * u ∧ |p.1 - p.2| ≤ 2.04 * max (H p.2) (H u)},
    |Tc p.1.1 - Tc p.1.2|

variable {H : ℝ → ℝ} {Tc : ℝ → ℝ}

lemma oscR_nonneg (u : ℝ) : 0 ≤ oscR H Tc u :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma le_oscR (hTb : ∀ t, |Tc t| ≤ 2) {u s t : ℝ} (h1 : u ≤ t) (h2 : t < 2 * u)
    (h3 : |s - t| ≤ 2.04 * max (H t) (H u)) : |Tc s - Tc t| ≤ oscR H Tc u := by
  have hbdd : BddAbove (Set.range fun p : {p : ℝ × ℝ // u ≤ p.2 ∧ p.2 < 2 * u ∧
      |p.1 - p.2| ≤ 2.04 * max (H p.2) (H u)} => |Tc p.1.1 - Tc p.1.2|) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨p, rfl⟩
    have := hTb p.1.1
    have := hTb p.1.2
    calc |Tc p.1.1 - Tc p.1.2| ≤ |Tc p.1.1| + |Tc p.1.2| := abs_sub _ _
      _ ≤ 4 := by linarith
  exact le_ciSup hbdd (⟨(s, t), h1, h2, h3⟩ : {p : ℝ × ℝ // u ≤ p.2 ∧ p.2 < 2 * u ∧
      |p.1 - p.2| ≤ 2.04 * max (H p.2) (H u)})

/-- **The field `osc`**: `OscBound` for `o = oscR H T_c`. -/
theorem oscBound_oscR (P : BeurlingSystem) (hTb : ∀ t, |Tc t| ≤ 2) (y : ℝ) (Sc : Finset ℝ)
    (hSc : ∀ u ∈ Sc, 0 < u) (hH : ∀ t, 0 ≤ H t) : OscBound P H y Tc Sc (oscR H Tc) := by
  intro u hu
  refine ⟨oscR_nonneg u, fun n hn _ s hs => ?_⟩
  obtain ⟨-, h1, h2⟩ := (mem_NW P (hSc u hu)).mp hn
  have e : posn P.labelVal y n = y / LemmaM.valN P.labelVal n := rfl
  rw [← e] at h1 h2
  apply le_oscR hTb h1 h2
  refine hs.trans ?_
  have := le_max_left (H (posn P.labelVal y n)) (H u)
  have := hH (posn P.labelVal y n)
  nlinarith

variable {val : ℕ → ℝ} {x : ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- A non-zero source step from `d ≥ 2` has its point within half a window of a centre `v/w`,
`v` in the support of `C_d`. -/
lemma srcStep_support {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ val p)
    {d n : ℕ} (hd1 : d ≠ 1) {t : ℝ}
    (hne : srcStep val x H (phiT tw X0m) (kapN tw X0m val x) d n t ≠ 0) :
    ∃ v, X0m / 2 ≤ posn val x d ∧ |v - posn val x d| ≤ 1.02 * H (posn val x d) ∧
      |t - v / LemmaM.valN val (n / d)| ≤ H (v / LemmaM.valN val (n / d)) / 2 := by
  by_contra hcon
  push_neg at hcon
  apply hne
  unfold srcStep
  rw [if_neg hd1]
  unfold Qd
  have hsupp := gK_support (x := x) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h)
  rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)]
  simp only [Pi.zero_apply]
  by_cases hg : gK val x H (phiT tw X0m) d v = 0
  · rw [hg]; ring
  obtain ⟨hposd, hvd⟩ := hsupp d v hg
  have hfar := hcon v hposd hvd
  have hk : kd H (v / LemmaM.valN val (n / d)) t = 0 := by
    unfold kd
    rw [Set.indicator_of_notMem, mul_zero]
    rintro ⟨h1, h2⟩
    have : |t - v / LemmaM.valN val (n / d)| ≤ H (v / LemmaM.valN val (n / d)) / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  rw [hk]; ring

/-- **The support of `S^{X₀}_n`** lies below `X₀ + 1.05 H(X₀)`. -/
lemma SX0_support {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hX0 : X0m = X0 - H X0 / 2)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {n : ℕ} {t : ℝ}
    (hne : SX0 val x H tw X0m n t ≠ 0) : t ≤ X0 + 1.05 * H X0 := by
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
  -- `x/n ≥ X₀⁻/2`
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
  -- the centre `c = v/w`
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
  have := (abs_le.mp ht).2
  have := (abs_le.mp hcX).2
  linarith

/-- **The field `termOsc`**: if `T_c = 0` on `(-∞, X₀]` and `|T_c| ≤ 2`, then on the support of
`S^{X₀}_n`, `|T_c| ≤ o_{X₀}`. -/
theorem termOsc_oscR (P : BeurlingSystem) {X0 ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0 : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (hTb : ∀ t, |Tc t| ≤ 2)
    (hTlow : ∀ t, t ≤ X0 → Tc t = 0) (y : ℝ) :
    TermOsc P H tw X0m y Tc (oscR H Tc X0) := by
  intro n t hne
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have ht := SX0_support (x := y) hP hX0 hval2 hne
  have hXm := hP.X0m_pos
  have hHX := hP.reg.pos X0
  have hX0pos : 0 < X0 := by by_contra h; push_neg at h; linarith
  rcases le_or_gt t X0 with hle | hgt
  · rw [hTlow t hle, abs_zero]; exact oscR_nonneg _
  · have e : |Tc t| = |Tc t - Tc X0| := by rw [hTlow X0 le_rfl, sub_zero]
    rw [e]
    apply le_oscR hTb le_rfl (by linarith)
    rw [abs_of_pos (by linarith), max_self]
    linarith

end KR.Chain

end
