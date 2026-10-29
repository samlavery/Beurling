module

public import RequestProject.Beurling.Noise.MarginPoint

/-!
# The Lemma 5.34 fields of `RealMarginLoc` cannot all hold: `B` additive with `hBx`

`RealMarginLoc` (and `KR.Chain.ChainInputs`, `ChainInputs2`, `ChainInputsLoc`) asks for an
additive map `B : (ℝ → ℝ) →+ (ℝ → ℝ)` with `hBx : ∀ g x, B g x = Bavg (H x) g x`. The window
average `Bavg h g x = h⁻¹ ∫_{x-h/2}^{x+h/2} g` is additive only on functions integrable on the
window (the Bochner integral of a non-integrable function is `0`), so no such `B` exists as soon as
`H x > 0` (`no_additive_Bavg`). Hence `RealMarginLoc hc ω b` is empty (`RealMarginLoc.isEmpty`,
`RML6PredBugRML.lean`),
and a corrected interface is needed: `RML6PredOps.lean` states the Lemma 5.34 operators as maps
that are additive on locally integrable functions only, which is all the proof uses.

Witness: `f y = (y - x)⁻¹` is not integrable on the window (`intervalIntegrable_sub_inv_iff`), so
`Bavg f x = Bavg (f + 1) x = 0`, while `Bavg 1 x = 1`.
-/

@[expose] public section

open MeasureTheory

namespace Margin

lemma Bavg_one {h : ℝ} (hh : 0 < h) (x : ℝ) : Bavg h (fun _ => 1) x = 1 := by
  unfold Bavg
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp
  ring

/-- **No additive map agrees with the window average at a point with positive width.** -/
theorem no_additive_Bavg {H : ℝ → ℝ} {x : ℝ} (hH : 0 < H x) :
    ¬ ∃ B : (ℝ → ℝ) →+ (ℝ → ℝ), ∀ g, B g x = Bavg (H x) g x := by
  rintro ⟨B, hB⟩
  set f : ℝ → ℝ := fun y => (y - x)⁻¹
  have hni : ¬ IntervalIntegrable f volume (x - H x / 2) (x + H x / 2) := by
    rw [intervalIntegrable_sub_inv_iff]
    push_neg
    refine ⟨by linarith, ?_⟩
    rw [Set.mem_uIcc]; left; constructor <;> linarith
  have h1 : Bavg (H x) f x = 0 := by
    unfold Bavg
    rw [intervalIntegral.integral_undef hni, mul_zero]
  have hni2 : ¬ IntervalIntegrable (fun y => f y + 1) volume (x - H x / 2) (x + H x / 2) := by
    intro hc
    apply hni
    have := hc.sub (intervalIntegrable_const (c := (1 : ℝ)))
    simpa using this
  have h2 : Bavg (H x) (fun y => f y + 1) x = 0 := by
    unfold Bavg
    rw [intervalIntegral.integral_undef hni2, mul_zero]
  have hadd := congrFun (B.map_add f (fun _ => 1)) x
  have e : (f + fun _ => (1 : ℝ)) = fun y => f y + 1 := rfl
  rw [e, Pi.add_apply, hB, hB, hB, h1, h2, Bavg_one hH] at hadd
  norm_num at hadd

end Margin

end
