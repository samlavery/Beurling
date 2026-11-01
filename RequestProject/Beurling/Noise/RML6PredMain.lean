module

public import RequestProject.Beurling.Noise.RML6PredRres

/-!
# Lemma 5.34's input of Theorem 5.37 with the kernel operator `R_res`

* `KR.Ops.pred_Rres` : the input (predictable) of `Margin.thm_5_37`, i.e.
  `log x · B(R_res T')(x) - ε_N ≤ log x · (ρ̃ + ν + NT)(x)`, with `R_res` the operator of the
  kernels (`BridgeBR.Rres`, as in Propositions 5.26, 5.35) — from `hpred_of_ops` and
  `Rres_eq_Nop`. Its remaining inputs are exactly: the margin identity (Proposition 5.11, in
  `LocInt`), the two bullets of the proof of Lemma 5.34, `|ϑ(x)| ≤ 6`, and `T' = T_c + J` bounded
  and measurable on half-lines.
* `KR.Ops.BKBR_eq` : `B K_pt B R F = B (F - R_res F)`, so the first bullet is a bound on the
  window average of the kernel part `∑_n n⁻¹ ∫ F dC_n^y` (`hK_of_kernel`), which is what
  Proposition 5.18 bounds at each start `y`.
-/

@[expose] public section

open MeasureTheory Set Finset BeurlingSystem KR.Sharp

namespace KR.Ops

variable {H : ℝ → ℝ} {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m ε θ : ℝ}

/-- **The input (predictable) of Theorem 5.37, with the kernel operator `R_res`.** -/
theorem pred_Rres (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ)
    (ρ ν NT vtH Tc J : LocInt) (ϑ : ℝ → ℝ) (hT : LBd ((Tc + J : LocInt) : ℝ → ℝ))
    (hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / H z)
    (hmargin : ρ + Bo hO (Ko (tw := tw) hO ρ) = Bo hO (Tc + J) + vtH - ν - NT)
    {x a b : ℝ} (hlx : 0 ≤ Real.log x)
    (hK : Real.log x * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO Tc - Tc) + vtH - ν - NT)))) : ℝ → ℝ) x| ≤ a)
    (hG : Real.log x * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (Tc + J) + vtH - ν - NT - Bo hO J) -
        Bo hO (Bo hO (Tc + J) + vtH - ν - NT - Bo hO J)))) : ℝ → ℝ) x| ≤ b)
    (hϑ : |ϑ x| ≤ 6) :
    Real.log x * Margin.Bavg (H x) (fun y => Rres P H tw X0m y ((Tc + J : LocInt) : ℝ → ℝ)) x -
        (a + b + 6 * Real.log x / H x) ≤
      Real.log x * ((ρ : ℝ → ℝ) x + (ν : ℝ → ℝ) x + (NT : ℝ → ℝ) x) := by
  have h := hpred_of_ops (tw := tw) hO ρ ν NT vtH Tc J ϑ hvt hmargin hlx hK hG hϑ
  have e : (fun y => Rres P H tw X0m y ((Tc + J : LocInt) : ℝ → ℝ)) =
      ((Ro (tw := tw) hO (Tc + J) : LocInt) : ℝ → ℝ) := by
    funext y; exact Rres_eq_Nop hO hP (Tc + J) hT y
  rw [e]; exact h

/-- The window average is bounded by a bound on the window. -/
lemma abs_Bavg_le_on {f : ℝ → ℝ} {c h x : ℝ} (hh : 0 < h)
    (hc : ∀ t, x - h / 2 ≤ t → t ≤ x + h / 2 → |f t| ≤ c) :
    |Margin.Bavg h f x| ≤ c := by
  unfold Margin.Bavg
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x - h / 2) (b := x + h / 2)
    (C := c) (f := f) (fun s hs => by
      rw [Set.uIoc_of_le (by linarith)] at hs
      rw [Real.norm_eq_abs]; exact hc s hs.1.le hs.2)
  rw [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < x + h / 2 - (x - h / 2) by linarith)] at this
  rw [abs_mul, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * |∫ s in (x - h / 2)..(x + h / 2), f s| ≤ h⁻¹ * (c * (x + h / 2 - (x - h / 2))) :=
        mul_le_mul_of_nonneg_left this (inv_pos.mpr hh).le
    _ = c := by field_simp; ring

/-- `B K_pt B R F = B (F - R_res F)` (push-through: `K_pt B R = 1 - R`). -/
theorem BKBR_eq (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (F : LocInt)
    (hF : LBd (F : ℝ → ℝ)) (x : ℝ) :
    (Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO F))) : ℝ → ℝ) x =
      Margin.Bavg (H x) (fun y => (F : ℝ → ℝ) y - Rres P H tw X0m y F) x := by
  have hspec := congrArg (fun u : LocInt => (u : ℝ → ℝ)) (Nop_spec (tw := tw) hO F)
  simp only [AddSubgroup.coe_add] at hspec
  have e : ((Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO F)) : LocInt) : ℝ → ℝ) =
      fun y => (F : ℝ → ℝ) y - Rres P H tw X0m y F := by
    funext y
    rw [Rres_eq_Nop hO hP F hF y]
    have := congrFun hspec y
    simp only [Pi.add_apply] at this
    linarith
  show Margin.Bavg (H x) _ x = _
  rw [e]

/-- **The first bullet of Lemma 5.34 from per-start kernel bounds**: if at every start `y` of the
window of `x`, `log x · |∑_n n⁻¹ ∫ F dC_n^y| ≤ a` (the kernel part of `R_res F`, bounded by
Proposition 5.18 with the oscillation of `F`), then `log x · |B K_pt B R F (x)| ≤ a`. -/
theorem hK_of_kernel (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (F : LocInt)
    (hF : LBd (F : ℝ → ℝ)) {x a : ℝ} (hlx : 0 ≤ Real.log x)
    (hker : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      Real.log x * |∑ n ∈ levels P X0m y,
        (∫ t, (F : ℝ → ℝ) t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n| ≤ a) :
    Real.log x * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO F))) : ℝ → ℝ) x| ≤ a := by
  rw [BKBR_eq hO hP F hF x]
  rcases eq_or_lt_of_le hlx with h0 | hpos
  · rw [← h0, zero_mul]
    have := hker x (by linarith [hO.pos x]) (by linarith [hO.pos x])
    rw [← h0, zero_mul] at this; exact this
  have hb : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      |(F : ℝ → ℝ) y - Rres P H tw X0m y F| ≤ a / Real.log x := by
    intro y h1 h2
    have := hker y h1 h2
    have e : (F : ℝ → ℝ) y - Rres P H tw X0m y F = -∑ n ∈ levels P X0m y,
        (∫ t, (F : ℝ → ℝ) t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n := by
      unfold Rres; ring
    rw [e, abs_neg, le_div_iff₀ hpos, mul_comm]; exact this
  have := abs_Bavg_le_on (hO.pos x) hb
  rw [le_div_iff₀ hpos] at this
  linarith

end KR.Ops

end
