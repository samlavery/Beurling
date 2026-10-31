module

public import RequestProject.Beurling.Construction.Unadapted

/-!
# The lag bound (13) from the slot-model data alone

Proposition 4.1 (the lag bound `|N_P(x) - T(x)| ≤ x^η`, `η = min(θ, 1/2 - θ)/2`) is derived from
the per-window queue data (`QueueWindowData`) and the landing data (`Landing`, `LandingInit`) of
the slot model. In particular it does **not** use (HBS), the cluster event or any bound on the
absorbed set: this is what makes it usable in the derivation of (HBS) itself
(`HBSDerive.lean`).
-/

@[expose] public section

open MeasureTheory Set Real CaplLink QueueBound LagSplit SlotModel InitialRange QueueMono
  Bookkeeping

namespace Construction

/-- **The lag bound from the slot data**: for `log X₀ ≥ 10⁸`, `θ ∈ [1/20, 1/2 - 10⁻⁴]`, the queue data
and the landing data give `|N(x) - T(x)| ≤ x^η` for every `x ≥ X₀`. -/
theorem lag_of_slotData {θ : ℝ} (hθ1 : 1 / 20 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (M : SlotModel X₀) (N : ℝ → ℝ) (hq : M.QueueWindowData)
    (κp : ℝ → ℝ) (hκp : ∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x)
    (hland : ∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x)
    (hinit : ∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x) :
    ∀ x ≥ (X₀ : ℝ), |N x - M.T x| ≤ x ^ lagExponent θ := by
  intro x hx
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · have hLx : 0 < Real.log x := by
      have h1 := one_lt_of_logX hX0 hX
      have := Real.log_le_log (by linarith) hx
      linarith
    obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
    have hH : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
    have h12 := ((hland x hx hlate).toSlotData M hX hq hx).two_sided
    have e : -(capH X₀ x / 2 * (1 + κp x / Real.log x)) =
        -(capH X₀ x / 2) * (1 + κp x / Real.log x) := by ring
    rw [e] at h12
    have hB0 := queueB_nonneg hX0 hX hx
    exact lag_rpow_of_queue (by linarith) hθ2 hX0 hX hx
      (abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH hB0 le_rfl h12.1 h12.2)
  · exact lag_rpow_initial hθ1 hθ2 hX0 hX hx (hκp X₀ le_rfl).1 (hκp X₀ le_rfl).2
      ((hinit x hx hearly).abs_le M hX hq hx hearly)

end Construction

end
