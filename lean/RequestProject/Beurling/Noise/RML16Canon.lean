module

public import RequestProject.Beurling.Noise.RML7Canon

/-!
# The jump fields of `RealMarginLoc` for the canonical parameters

With `p = canonP X₀ εH ES j` the super-solution's `j`-term covers the jump at `X₀`
(04g Step 3, base case): `canonP_hpj` (`j₀ ≤ p.j` for `j = j₀`) and `canonP_hJr` (the jump window
`|t - X₀| ≤ 1.01 H(t)` lies in the radius `r(1) = R₀ - K_r` of the super-solution).
-/

@[expose] public section

open Real

namespace BModel.RML16

variable {X₀ : ℕ}

/-- `a^{1/8} ≤ a/16384` for `a ≥ 2¹⁶`. -/
lemma rpow_eighth_le' {a : ℝ} (ha : 65536 ≤ a) : a ^ (1 / 8 : ℝ) ≤ a / 16384 := by
  have ha0 : 0 < a := by linarith
  have h1 : a = a ^ (1 / 8 : ℝ) * a ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add ha0]; norm_num
  have h2 : (65536 : ℝ) ^ (7 / 8 : ℝ) ≤ a ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) ha (by norm_num)
  have h3 : (65536 : ℝ) ^ (7 / 8 : ℝ) = 16384 := by
    rw [show (65536 : ℝ) = 2 ^ (16 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h4 : 0 < a ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ha0 _
  rw [h3] at h2
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

theorem canonP_hpj (εH ES j : ℝ) : j ≤ (RML7.canonP X₀ εH ES j).j := le_rfl

/-- **The jump window lies in `r(1)`** for the canonical parameters. -/
theorem canonP_hJr (hX : 10 ^ 8 ≤ Real.log X₀) (P : BeurlingSystem) (εH ES j : ℝ) {t : ℝ}
    (ht : |t - X₀| ≤ 1.01 * Queue6.Hc X₀ t) :
    |t - (RML7.canonP X₀ εH ES j).X0| ≤ Margin.Rec.radJ P (RML7.canonP X₀ εH ES j) 1 := by
  have hX0 := KR.WidthReal.X0_ge hX
  have hXm := RML7.Xm_le_X0 hX
  have h3 : Queue6.Hc X₀ (3 * X₀) ≤ 3 * X₀ / 16384 := by
    unfold Queue6.Hc
    rw [max_eq_left (by linarith)]
    exact (InitialRange.capH_le_rpow (Nat.cast_nonneg _) hX (by linarith)).trans
      (rpow_eighth_le' (by linarith))
  have hHt : Queue6.Hc X₀ t ≤ 3 * X₀ / 16384 := by
    by_cases htle : t ≤ 3 * X₀
    · exact (KR.WidthReal.Hc_mono hX htle).trans h3
    · exfalso
      push_neg at htle
      have hc : Queue6.Hc X₀ t ≤ t / 40 := by
        unfold Queue6.Hc
        rw [max_eq_left (by linarith)]
        exact KR.WidthReal.capH_le_tenth hX (by linarith)
      have := (abs_le.mp ht).2
      linarith
  have hr : Margin.Rec.radJ P (RML7.canonP X₀ εH ES j) 1 =
      X₀ - 1.21 * (Xm X₀ / 2) - 5 * Queue6.Hc X₀ (3 * X₀) := by
    unfold Margin.Rec.radJ
    rw [Margin.Rec.Vv_one, Real.one_rpow, mul_one]
    rfl
  rw [hr, show (RML7.canonP X₀ εH ES j).X0 = X₀ from rfl]
  have := abs_le.mp ht
  rw [abs_le]; constructor <;> nlinarith

end BModel.RML16

end
