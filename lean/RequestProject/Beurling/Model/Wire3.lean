module

public import RequestProject.Beurling.Model.Wire2

/-!
# The bridge field of `RealMarginLoc` from `bridgeR_real_loc`

* `NKc` : the scale indices `N(y)`, `K(y)` (by choice, `exists_NK`);
* `bridge_c` : the field `bridge` with `E_BR = e^{-76}` and `j = j_{X₀}(x) = jXdef`, from
  (H_BS) on `[1, Zc b]` (`tnpR`), `|T_c| ≤ 2` below the horizon (`TcR_abs_le`), `T_c = 0` on
  `(-∞, X₀]` (`TcR_low`), the horizon conditions (`Zc_facts`), and the remaining inputs `hosc`
  (eq. (osc), first display, for the clamped `T_c`) and `hbdd` (the eq. (jX0) family bounded on
  `W_x`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

lemma Xm_le_X0 (hc : Cond θ X₀) : Xm X₀ ≤ X₀ := by
  have := capH_ge_one (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  unfold Xm; linarith

lemma Xm_pos' (hc : Cond θ X₀) : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]

open Classical in
variable (X₀) in
/-- The scale indices `(N, K)` at a start `y` (by choice). -/
noncomputable def NKc (y : ℝ) : ℕ × ℕ :=
  if h : ∃ N K : ℕ, 2 < N ∧ y < (X₀ : ℝ) * 2 ^ N / 4 ∧ √(2 * y) ≤ Pk (Xm X₀) K then
    (h.choose, h.choose_spec.choose) else (0, 0)

lemma NKc_spec (hc : Cond θ X₀) (y : ℝ) :
    2 < (NKc X₀ y).1 ∧ y < X₀ * 2 ^ (NKc X₀ y).1 / 4 ∧ √(2 * y) ≤ Pk (Xm X₀) (NKc X₀ y).2 := by
  classical
  have hX0 : (0 : ℝ) < X₀ := by
    have := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hex := exists_NK (X0m := Xm X₀) hX0 hXm y
  unfold NKc
  rw [dif_pos hex]
  exact hex.choose_spec.choose_spec

/-- **The field `bridge`** (Proposition 5.26, Lemma 5.27, Lemma 5.20 at the starts of the
windows), from `bridgeR_real_loc`. -/
noncomputable def bridge_c (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    {x y : ℝ} (hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x) (hxb : x ≤ b) (hW : InW (Queue6.Hc X₀ x) x y)
    (hosc : ∑ u ∈ dyScales X₀ y (NKc X₀ y).1, Real.log (2 * u) *
      oscR (Queue6.Hc X₀) (clampT (oscHt (Queue6.Hc X₀) y) (TcR θ X₀ ω (jzX X₀))) u ≤
        Real.exp (-83))
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ x) x y} =>
      jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀ y.1).1 (NKc X₀ y.1).2 y.1)) :
    BridgeR (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH
      (TcR θ X₀ ω (jzX X₀)) (jzX X₀) y EBRc
      (jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) x) :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hT := tnpR hc hev hbs hSG hX1
  have hmono := KR.WidthReal.Hc_mono hX
  have hHx : Queue6.Hc X₀ x ≤ Queue6.Hc X₀ b := hmono hxb
  have hHb0 : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
  have hyb : y ≤ b + Queue6.Hc X₀ b := by have := hW.2; linarith
  have hZ := Zc_facts hc hb
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  -- `y ≥ X₀`
  have hxX : 2 * (X₀ : ℝ) ≤ x := by
    have h1 : (X₀ : ℝ) ^ (1.01 : ℝ) = X₀ * (X₀ : ℝ) ^ (0.01 : ℝ) := by
      rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have h2 : (2 : ℝ) ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := by
      have hb2 : (2 : ℝ) ^ (100 : ℝ) ≤ X₀ := by
        have := ten96_le hX
        have : (2 : ℝ) ^ (100 : ℝ) ≤ 10 ^ 96 := by norm_num
        linarith
      calc (2 : ℝ) = ((2 : ℝ) ^ (100 : ℝ)) ^ (0.01 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := Real.rpow_le_rpow (by positivity) hb2 (by norm_num)
    rw [h1] at hx; nlinarith
  have hy : (X₀ : ℝ) ≤ y := by
    have hHx4 : Queue6.Hc X₀ x ≤ x / 4 := by
      unfold Queue6.Hc; rw [max_eq_left (by linarith)]
      have := four_capH_le hX0 hX (show (X₀ : ℝ) ≤ x by linarith); linarith
    have := hW.1; linarith
  have hyZ : 2 * y / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have h18 : 18 * y ≤ Zc X₀ b ^ 2 := KR.Chain.sq18_of_cofactor hXm0 hZ.1
    (le_trans (div_le_div_of_nonneg_right (by linarith) hXm0.le) (Zc_18 hc hb))
  bridgeR_real_loc hT hX (NKc X₀) hy hZ.1 hyZ h18 (by norm_num [lamH]) (by norm_num [lamH])
    (fun t ht => TcR_abs_le hc hev ω hT ht) (fun t ht => TcR_low hc ω ht) (NKc_spec hc y) hosc
    hW hbdd

end BModel
