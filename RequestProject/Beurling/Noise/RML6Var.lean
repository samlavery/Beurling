module

public import RequestProject.Beurling.Noise.MarginRealLoc
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# Proposition 5.38 internals for the construction (fields of `BModel.RealMarginLoc`)

Proved here, for the realised system `PR θ X₀ ω`, the width `H_c = Hc X₀` and the margin
density `m = marginM θ X₀ ω`:

* `marginM_eq_zero_low` : **`hz`**, `m = 0` below `X₀`. Below `X₀` the source `T'_cont` vanishes
  (`TpCont`), and the compensator density `c` vanishes: a cofactor `w ≠ 0` of a prime decided at
  a slot has value `≥ 2` (`pos2_DM`), so `y/w < X₀/2 ≤ X₀⁻` misses the cut-off `y/w ≥ X₀⁻`.
* `hStep_Hc` : **`hgeom`**, the `H`-regularity at a cofactor (`Margin.Rec.HStep`), from (RH)
  (`PaperWidth.RH`) for the compression and from `CapHSlope` together with `H(y) ≤ y^{1/8}`
  (`capH_le_rpow`) for the two neighbour bounds.
* `hdec_canon`, `hsum_canon` : **`hdec`**, **`hsum`** hold with the canonical choices
  `Bt := ρ̃ + ν + NT - B m` and `jb := ρ^sh T' log t - m log t - 10⁻¹²`; with these choices the
  content of Step 6(a)/(b) is in `hBt` and `hjb` (Proposition 5.33).
-/

@[expose] public section

open Real Set MeasureTheory Construction CaplLink BModel KR AbsorbEmpty

namespace BModel.RML6

variable {θ : ℝ} {X₀ : ℕ}

/-! ## `hz`: the margin vanishes below `X₀` -/

open Classical in
/-- The compensator density vanishes below `X₀`. -/
lemma compDen_eq_zero_low (hc : Cond θ X₀) (ω : JitterΩ) {y : ℝ} (hy : y < X₀) :
    compDen θ X₀ ω y = 0 := by
  have hX := hc.hX
  have hpos2 : Pos2 (Queue6.DD θ X₀ ω) :=
    show Pos2 (DM (Mcl θ X₀ ω) (Ucl ω)) from pos2_DM hX (U := Ucl ω) (fun j => clamp01_mem (ω j))
      (by rw [Mcl_eq hc]; exact (hc.std ω).limModel_low)
  have hXm : (X₀ : ℝ) / 2 ≤ Xm X₀ := WidthReal.Xm_ge hX
  unfold compDen
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  unfold compTerm
  by_cases hA : ω ∈ lawA θ X₀ k
  · rw [Set.indicator_of_mem hA]
    have hsum : (∑' w : PIdx X₀ →₀ ℕ, if w ∈ cofP θ X₀ k ω ∧ Xm X₀ ≤ y / eval (Queue6.DD θ X₀ ω) w ∧
        ¬ (10 ^ 7 ≤ Real.log y ∧ y / eval (Queue6.DD θ X₀ ω) w < absorbY X₀ y) then
        (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 (y / eval (Queue6.DD θ X₀ ω) w) *
          ENNReal.ofReal (eval (Queue6.DD θ X₀ ω) w)⁻¹ else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      rw [if_neg]
      rintro ⟨⟨hlive, hw0, -⟩, hcut, -⟩
      obtain ⟨i, hi⟩ : ∃ i, i ∈ w.support := by
        by_contra hne
        push_neg at hne
        exact hw0 (Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hne))
      have h2 : 2 ≤ eval (Queue6.DD θ X₀ ω) w :=
        (pval_ge_two hpos2 hlive hi).trans (pval_le_eval hpos2.pos hlive hi)
      have hev : 0 < eval (Queue6.DD θ X₀ ω) w := by linarith
      have hX0 : (0 : ℝ) < X₀ := WidthReal.X0_pos hX
      have : y / eval (Queue6.DD θ X₀ ω) w < Xm X₀ := by
        rcases le_or_gt y 0 with hy0 | hy0
        · have : y / eval (Queue6.DD θ X₀ ω) w ≤ 0 := div_nonpos_of_nonpos_of_nonneg hy0 hev.le
          linarith
        · rw [div_lt_iff₀ hev]
          nlinarith
      linarith
    rw [hsum, mul_zero]
  · rw [Set.indicator_of_notMem hA]

/-- **`hz`** (Proposition 5.38, "`m = 0` below `X₀`"). -/
theorem marginM_eq_zero_low (hc : Cond θ X₀) (ω : JitterΩ) {y : ℝ} (hy : y < X₀) :
    marginM θ X₀ ω y = 0 := by
  unfold marginM TpCont
  rw [if_neg (not_le.mpr hy), compDen_eq_zero_low hc ω hy]
  simp

/-! ## `hgeom`: `H`-regularity at a cofactor -/

lemma rpow_eighth_le_tiny {a : ℝ} (ha : (10 : ℝ) ^ 12 ≤ a) : a ^ (1 / 8 : ℝ) ≤ a / 10 ^ 10 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h78 : (10 : ℝ) ^ 10 ≤ a ^ (7 / 8 : ℝ) := by
    have h1 : ((10 : ℝ) ^ 12) ^ (7 / 8 : ℝ) ≤ a ^ (7 / 8 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) ha (by norm_num)
    have h2 : ((10 : ℝ) ^ 12) ^ (7 / 8 : ℝ) = (10 : ℝ) ^ (21 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h3 : (10 : ℝ) ^ (10 : ℝ) ≤ (10 : ℝ) ^ (21 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h4 : (10 : ℝ) ^ (10 : ℝ) = (10 : ℝ) ^ (10 : ℕ) := by norm_cast
    linarith
  have hsplit : a = a ^ (1 / 8 : ℝ) * a ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add ha0]; norm_num
  rw [le_div_iff₀ (by norm_num)]
  have h18 : 0 ≤ a ^ (1 / 8 : ℝ) := Real.rpow_nonneg ha0.le _
  nlinarith

lemma X0_ge_tera (hX : 10 ^ 8 ≤ Real.log X₀) : (10 : ℝ) ^ 12 ≤ X₀ := by
  have hX0 : (0 : ℝ) < X₀ := WidthReal.X0_pos hX
  rw [← Real.exp_log hX0]
  have : (10 : ℝ) ^ 12 ≤ Real.exp 28 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have he : Real.exp 28 = Real.exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    calc (10 : ℝ) ^ 12 ≤ 2.7 ^ 28 := by norm_num
      _ ≤ Real.exp 1 ^ 28 := pow_le_pow_left₀ (by norm_num) h2 28
  exact this.trans (Real.exp_le_exp.mpr (by linarith))

/-- The neighbour ratio: `H_c(y) ≤ (1 + 10⁻⁹) H_c(z')` for `y - 0.52 H_c(y) ≤ z' ≤ y`. -/
lemma Hc_neg_ratio (hX : 10 ^ 8 ≤ Real.log X₀) {εH : ℝ} (hε1 : εH ≤ 1)
    (hS : WidthReal.CapHSlope X₀ εH) {y z : ℝ} (hz1 : y - 0.52 * Queue6.Hc X₀ y ≤ z)
    (hz2 : z ≤ y) : Queue6.Hc X₀ y ≤ (1 + 1 / 10 ^ 9) * Queue6.Hc X₀ z := by
  have hX0 : (0 : ℝ) < X₀ := WidthReal.X0_pos hX
  have hHz := WidthReal.Hc_pos hX z
  rcases lt_or_ge y X₀ with hy | hy
  · have e1 : Queue6.Hc X₀ y = capH X₀ X₀ := by unfold Queue6.Hc; rw [max_eq_right hy.le]
    have e2 : Queue6.Hc X₀ z = capH X₀ X₀ := by
      unfold Queue6.Hc; rw [max_eq_right (hz2.trans hy.le)]
    rw [e1, e2]
    have := WidthReal.capH_one_le hX (le_refl (X₀ : ℝ))
    nlinarith
  · have hT := X0_ge_tera hX
    have hy0 : 0 < y := lt_of_lt_of_le hX0 hy
    have eY : Queue6.Hc X₀ y = capH X₀ y := by unfold Queue6.Hc; rw [max_eq_left hy]
    have hHy : capH X₀ y ≤ y / 10 ^ 10 :=
      (InitialRange.capH_le_rpow hX0.le hX hy).trans (rpow_eighth_le_tiny (hT.trans hy))
    rw [eY] at hz1 ⊢
    have hz0 : 0 < z := by nlinarith
    set a := max z (X₀ : ℝ) with ha
    have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
    have hay : a ≤ y := max_le hz2 hy
    have ha0 : 0 < a := lt_of_lt_of_le hX0 haX
    have eZ : Queue6.Hc X₀ z = capH X₀ a := rfl
    rw [eZ]
    have h1 := hS a y haX hay
    have hr1 : 1 ≤ y / a := by rw [le_div_iff₀ ha0]; linarith
    have h2 : (y / a) ^ εH ≤ y / a := by
      calc (y / a) ^ εH ≤ (y / a) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 hε1
        _ = y / a := Real.rpow_one _
    have h3 : y / a ≤ 1 + 1 / 10 ^ 9 := by
      rw [div_le_iff₀ ha0]
      have : z ≤ a := le_max_left _ _
      nlinarith
    have hHa := WidthReal.capH_one_le hX haX
    calc capH X₀ y ≤ (y / a) ^ εH * capH X₀ a := h1
      _ ≤ (1 + 1 / 10 ^ 9) * capH X₀ a :=
          mul_le_mul_of_nonneg_right (h2.trans h3) (by linarith)

/-- **`hgeom`** (Step 3, `H`-regularity at a cofactor) for the realised width: for a level `w`
with `t/w ≥ X₀⁻/2` and `w ≥ 1`, `HStep (Hc X₀) ε t (t/w) w`, given `PaperWidth` with exponent
`εH ≤ ε` and the slope bound `CapHSlope X₀ εH`. -/
theorem hStep_Hc (hX : 10 ^ 8 ≤ Real.log X₀) {εH θH ε : ℝ}
    (hP : PaperWidth (Queue6.Hc X₀) (Xm X₀) εH θH) (hS : WidthReal.CapHSlope X₀ εH)
    (hεε : εH ≤ ε) {t w : ℝ} (hw : 1 ≤ w) (htw : Xm X₀ / 2 ≤ t / w) :
    Margin.Rec.HStep (Queue6.Hc X₀) ε t (t / w) w where
  compress := by
    intro hh hhh
    have hw0 : 0 < w := by linarith
    have hRH := hP.RH (t / w) w htw hw
    rw [div_mul_cancel₀ t hw0.ne'] at hRH
    have hpow : w ^ εH ≤ w ^ ε := Real.rpow_le_rpow_of_exponent_le hw hεε
    have hHp := WidthReal.Hc_pos hX (t / w)
    have hwe : w ^ (ε - 1) = w ^ ε / w := by
      rw [Real.rpow_sub_one hw0.ne']
    rw [hwe, div_le_iff₀ hw0]
    have : 1.01 * Queue6.Hc X₀ t ≤ 1.01 * (w ^ ε * Queue6.Hc X₀ (t / w)) := by
      have := mul_le_mul_of_nonneg_right hpow hHp.le
      nlinarith
    calc |hh| ≤ 1.01 * Queue6.Hc X₀ t := hhh
      _ ≤ 1.01 * (w ^ ε * Queue6.Hc X₀ (t / w)) := this
      _ = 1.01 * (w ^ ε / w) * Queue6.Hc X₀ (t / w) * w := by field_simp
  neg_ratio := fun z hz1 hz2 =>
    Hc_neg_ratio hX (by linarith [hP.eps_le]) hS hz1 hz2
  neg_le := fun z _ hz2 => WidthReal.Hc_mono hX hz2
  pos := WidthReal.Hc_pos hX _

/-- `hgeom` at the levels of the recursion: `w ∈ Fset t` gives `t/w ≥ X₀⁻/2` and `w ≥ 1`. -/
theorem hgeom_of (hX : 10 ^ 8 ≤ Real.log X₀) {εH θH : ℝ} (ω : JitterΩ) (p : Margin.Rec.CP)
    (hpXm : p.Xm = Xm X₀) (hP : PaperWidth (Queue6.Hc X₀) (Xm X₀) εH θH)
    (hS : WidthReal.CapHSlope X₀ εH) (hεε : εH ≤ p.ε) (t : ℝ) (w : ℕ)
    (hwF : w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t) :
    Margin.Rec.HStep (Queue6.Hc X₀) p.ε t (t / KR.Vl (PR θ X₀ ω) w) (KR.Vl (PR θ X₀ ω) w) := by
  unfold Margin.Rec.Fset at hwF
  obtain ⟨hwN, -⟩ := Finset.mem_filter.mp hwF
  have hXm0 : 0 < p.Xm / 2 := by rw [hpXm]; linarith [hP.X0m_pos]
  have hpos := posn_ge_of_mem_NAll (P := PR θ X₀ ω) hwN hXm0
  have hw1 : 1 ≤ KR.Vl (PR θ X₀ ω) w :=
    LemmaM.one_le_valN _ (fun r _ => (PR θ X₀ ω).one_le_labelVal r)
  refine hStep_Hc hX hP hS hεε hw1 ?_
  rw [← hpXm]
  exact hpos

/-! ## `hdec`, `hsum`: the canonical choices of `Bt` and `jb` -/

/-- **`hdec`** with the canonical `Bt := ρ̃ + ν + NT - B m` (Step 6(a); the content is then `hBt`,
`|B NT_pt + ϑ/H| ≤ 54η + 6/H`). -/
theorem hdec_canon (ω : JitterΩ) (ν NT : ℝ → ℝ) (t : ℝ) :
    rhoT θ X₀ ω t + ν t + NT t = Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t +
      (rhoT θ X₀ ω t + ν t + NT t - Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t) := by
  ring

/-- **`hsum`** with the canonical `jb := ρ^sh T' log t - m log t - 10⁻¹²` (Step 6(b); the content
is then `hjb`, Proposition 5.33: `j_{X₀} ≤ 0.4209`). -/
theorem hsum_canon (rs mt L : ℝ) :
    rs * L - (rs * L - mt * L - 1 / 10 ^ 12) - 1 / 10 ^ 12 ≤ mt * L := by
  linarith

end BModel.RML6

end
