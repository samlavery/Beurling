module

public import RequestProject.Beurling.Queue6.S2Ep

/-!
# `hS2Ep`/`hS2Em` without the time condition far below `X₀`, and with `2z ≤ t`

* `hS2Epm_low` : for `z < X₀ - 1.6 H(X₀)` the sets `A± ∩ [X₀, ∞)` are empty (`Aplus_bounds`,
  `Aminus_bounds`), so `σ(A±) = 0` (the slots start at or above `X₀`) and `∫_{A±} m = 0`
  (`m = 0` below `X₀`): the bound holds surely, for every `ω`;
* `hS2Epm_R2` : the fields `hS2Ep`, `hS2Em` a.s. on `Good(< t) ∩ NiceEv` under `2z ≤ t` only
  (the form available on `S2Rng`, where `z ≤ t'/V(w) ≤ b/2`): either `z < X₀ - 1.6 H(X₀)`, or
  `max(z, X₀) + 2H(z) ≤ 2z ≤ t` and `hS2Epm_R` applies.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- The slot measure of a set without points above `X₀` vanishes. -/
lemma sigmaS_eq_zero (ω : JitterΩ) {z s : ℝ} {A : Set ℝ} (hA : ∀ x ∈ A, x < X₀) :
    Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) A = 0 := by
  classical
  unfold Margin.Exact.sigmaS
  have : (s2Q θ X₀ ω z s).filter (fun q => s2sl θ X₀ ω z s q ∈ A) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun q _ hq => ?_
    have := hA _ hq
    have := slotF_ge hc q ω
    simp only [s2sl] at *
    linarith
  rw [this]; simp

/-- The margin integral over a set without points above `X₀` vanishes. -/
lemma integral_eq_zero_low (ω : JitterΩ) {A : Set ℝ} (hA : ∀ x ∈ A, x < X₀) :
    ∫ r in A, marginM θ X₀ ω r = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun x hx => RML6.marginM_eq_zero_low hc ω (hA x hx)

/-- **`hS2Ep`, `hS2Em` far below `X₀`**: for `z < X₀ - 1.6 H(X₀)` and `0 ≤ s ≤ 1.01 H(z)`,
`σ(A±) - ∫_{A±} m = 0`, for every `ω`. -/
theorem hS2Epm_low (ω : JitterΩ) {z s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1.01 * Hc X₀ z)
    (hz : z < X₀ - 1.6 * capH X₀ X₀) :
    |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aplus (Hc X₀) z s) -
        ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r| = 0 ∧
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s)
          (Margin.Exact.Aminus (Hc X₀) z s) -
        ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r| = 0 := by
  have hH0 : 200 ≤ capH X₀ X₀ := by
    have := log_le_capH (Nat.cast_nonneg _) hc.hX (le_refl (X₀ : ℝ))
    have : 0 ≤ Real.log (X₀ : ℝ) := by linarith [hc.hX]
    linarith
  have hHz : Hc X₀ z = capH X₀ X₀ := by
    unfold Hc; rw [max_eq_right (by linarith)]
  rw [hHz] at hs
  have hp : ∀ x ∈ Margin.Exact.Aplus (Hc X₀) z s, x < X₀ := fun x hx => by
    by_contra h; push_neg at h
    have := (Aplus_bounds hc hs0 (by rw [hHz]; exact hs) x hx h).2
    rw [hHz] at this; linarith
  have hm : ∀ x ∈ Margin.Exact.Aminus (Hc X₀) z s, x < X₀ := fun x hx => by
    by_contra h; push_neg at h
    have := (Aminus_bounds hc hs0 (by rw [hHz]; exact hs) x hx h).2
    rw [hHz] at this; linarith
  rw [sigmaS_eq_zero hc ω hp, integral_eq_zero_low hc ω hp, sigmaS_eq_zero hc ω hm,
    integral_eq_zero_low hc ω hm]
  simp

variable (hev : Even X₀)
include hev

/-- **The fields `hS2Ep`, `hS2Em` under `2z ≤ t`**: a.s., for every `t`, on
`Good(< t) ∩ NiceEv`, for every `z` with `2z ≤ t` and `0 ≤ s ≤ 1.01 H(z)`,
`|σ(A±) - ∫_{A±} m| ≤ ε_z`. -/
theorem hS2Epm_R2 : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ z s : ℝ, 0 ≤ s → s ≤ 1.01 * Hc X₀ z → 2 * z ≤ t →
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aplus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z ∧
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aminus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z := by
  filter_upwards [hS2Epm_R hc hev] with ω hω
  intro t hG hN z s hs0 hs hzt
  have he := s2ε_ge hc z
  rcases lt_or_ge z (X₀ - 1.6 * capH X₀ X₀) with hz | hz
  · obtain ⟨h1, h2⟩ := hS2Epm_low hc ω hs0 hs hz
    rw [h1, h2]; constructor <;> linarith
  · refine hω t hG hN z s hs0 hs ?_
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    have hHz := Hc_le hc z
    rcases le_total z (X₀ : ℝ) with h | h
    · rw [max_eq_right h] at hHz ⊢
      have : Hc X₀ z = capH X₀ X₀ := by unfold Hc; rw [max_eq_right h]
      rw [this]
      have := X₀_ge_two_pow hc.hX
      linarith
    · rw [max_eq_left h] at hHz ⊢
      have := X₀_ge_two_pow hc.hX
      linarith

end Queue6

end
