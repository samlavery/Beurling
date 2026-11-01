module

public import RequestProject.Beurling.Model.Wire3

/-!
# `j_{X₀} ≥ 0` (the field `jXnn`)

`j_{X₀}(x) = sup_{y ∈ W_x} j₀ (𝔹(y) + 4.3 C_N ∑_v log(2v) s_θ(v)/log y) log y` (eq. (jX0),
Proposition 5.33) is a supremum of non-negative terms: `𝔹 ≥ 0` (its steps are `TV`, `KR`-norms
and `|c_n|`), `s_θ ≥ 0`, and for `y < 1` both `𝔹(y)` and the scale sum vanish (no level
`n ≥ 2` has `y/n ≥ X₀⁻/2`, and no dyadic scale `X₀ 2ᵏ/4` is `≤ y`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `𝔹(y) ≥ 0` for `H > 0`, `λ₀ ≥ 0`. -/
lemma xbB_nonneg {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m X0 θ' lam0 : ℝ}
    (hH : ∀ z, 0 < H z) (hlam : 0 ≤ lam0) (y : ℝ) : 0 ≤ xbB P H tw X0m y X0 θ' lam0 := by
  unfold xbB
  refine Finset.sum_nonneg fun n _ => div_nonneg (add_nonneg ?_ (Finset.sum_nonneg
    fun d _ => ?_)) (KR.Sharp.Vl_pos P n).le
  · split_ifs
    · positivity
    · exact le_rfl
  · unfold xbBstep
    have hT : 0 ≤ TVD P H tw X0m y d := by unfold TVD; positivity
    have hK : 0 ≤ KRD P H tw X0m y d := by unfold KRD; positivity
    have hV := KR.Sharp.Vl_pos P (n / d)
    have hHn := hH (posn P.labelVal y n)
    split_ifs <;> positivity

/-- `𝔹(y) = 0` for `y < X₀⁻/2`: there are no levels. -/
lemma xbB_low {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m X0 θ' lam0 : ℝ}
    (hX : 0 < X0m) {y : ℝ} (hy : y < X0m / 2) : xbB P H tw X0m y X0 θ' lam0 = 0 := by
  unfold xbB
  refine Finset.sum_eq_zero fun n hn => ?_
  exfalso
  have h1 := (KR.Sharp.mem_NAll_iff P (by linarith : 0 < X0m / 2)).mp
    (Finset.mem_filter.mp hn).1
  have hV1 : 1 ≤ Vl P n := LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)
  have h2 := (KR.Sharp.le_div_iff_cut P (by linarith : 0 < X0m / 2)).mp h1.2
  have h3 : y / Vl P n ≤ y ∨ y < 0 := by
    rcases le_or_gt 0 y with h | h
    · exact Or.inl (div_le_self h hV1)
    · exact Or.inr h
  rcases h3 with h3 | h3
  · linarith
  · have : y / Vl P n < 0 := div_neg_of_neg_of_pos h3 (by linarith)
    linarith

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`j_{X₀}(x) ≥ 0`** (the field `jXnn`), given (H_BS) through `KR.TNP.Hyp`. -/
theorem jXnn_c {ω : JitterΩ} {Z η1 η2 ε1' εH θH : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εH θH)
    {lam0 j0 : ℝ} (hlam : 0 ≤ lam0) (hj0 : 0 ≤ j0) (NK : ℝ → ℕ × ℕ) (x : ℝ) :
    0 ≤ jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ ε1' lam0 j0 NK x := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hXmh : (2 : ℝ) ≤ Xm X₀ / 2 := by
    have := KR.WidthReal.Xm_ge hX (X₀ := X₀); linarith
  have hH : ∀ z, 0 < Queue6.Hc X₀ z := KR.WidthReal.Hc_pos hX
  unfold jXdef
  refine Real.iSup_nonneg fun ⟨y, _⟩ => ?_
  show 0 ≤ jXat _ _ _ _ _ _ _ _ _ _ y
  unfold jXat
  have hB := xbB_nonneg (P := PR θ X₀ ω) (tw := twR θ X₀ ω) (X0m := Xm X₀) (X0 := X₀)
    (θ' := ε1') hH hlam y
  have hC : 0 ≤ CNc (X₀ : ℝ) := by
    unfold CNc
    have : 0 ≤ 4.71 / Real.log X₀ := div_nonneg (by norm_num) (by linarith)
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_trans (by norm_num) (le_max_right _ _)
    positivity
  rcases le_or_gt 1 y with hy | hy
  · have hl : 0 ≤ Real.log y := Real.log_nonneg hy
    have hS : 0 ≤ ∑ v ∈ dyScales (X₀ : ℝ) y (NK y).1, Real.log (2 * v) *
        TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NK y).2 v := by
      refine Finset.sum_nonneg fun v hv => mul_nonneg ?_ ?_
      · obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        exact Real.log_nonneg (by nlinarith)
      · exact KR.TNP.blk_nonneg hT.width _ (fun k => by
          have h1 := KR.TNP.Pk_ge_one hT.width.X0m_pos hT.hXm k
          have h2 := Real.log_nonneg h1; linarith) v
    have : 0 ≤ 4.3 * CNc (X₀ : ℝ) * (∑ v ∈ dyScales (X₀ : ℝ) y (NK y).1, Real.log (2 * v) *
        TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NK y).2 v) / Real.log y := by
      positivity
    positivity
  · rw [xbB_low hXm0 (by linarith)]
    have hE : dyScales (X₀ : ℝ) y (NK y).1 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      obtain ⟨k, -, rfl, hv⟩ := mem_dyScales.mp hv
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    rw [hE]; simp

end BModel

end
