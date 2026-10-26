module

public import Mathlib

/-!
# Rankin's bound for the rigid set (proof of Lemma 3.4)

The rigid set `D` is the set of `X₀`-smooth integers (all prime factors `< X₀`), and
`Ψ(x, X₀) = #(D ∩ [1, x])`. Rankin's method gives, for every `θ > 0`,

  `Ψ(x, X₀) ≤ ∑_{d ∈ D} (x/d)^θ = x^θ ∏_{p < X₀} (1 - p^{-θ})^{-1}`.

* `smoothCount` : `Ψ(x, X₀)`;
* `smoothCount_le_rankin` : Rankin's bound; in particular `Ψ(x, X₀) = O(x^θ)` for every `θ > 0`,
  which is the input for the bound `|E_rig(x)| ≤ C_{X₀} x^θ` in the target error (8).
-/

@[expose] public section

open Finset

namespace Rankin

/-- `Ψ(x, X₀)`: the number of `X₀`-smooth positive integers `n ≤ x`. -/
noncomputable def smoothCount (X₀ : ℕ) (x : ℝ) : ℕ := (Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).card

/-- The Rankin constant `∏_{p < X₀} (1 - p^{-θ})^{-1}`. -/
noncomputable def rankinConst (X₀ : ℕ) (θ : ℝ) : ℝ :=
  ∏ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-θ))⁻¹

lemma hasSum_smooth_rpow (X₀ : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun m : X₀.smoothNumbers => (m : ℝ) ^ (-θ)) ∧
    HasSum (fun m : X₀.smoothNumbers => (m : ℝ) ^ (-θ)) (rankinConst X₀ θ) := by
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ (-θ) with hf
  have hpow : ∀ p n : ℕ, f (p ^ n) = ((p : ℝ) ^ (-θ)) ^ n := by
    intro p n
    simp only [hf, Nat.cast_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
      ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]
  have hlt : ∀ {p : ℕ}, p.Prime → (p : ℝ) ^ (-θ) < 1 := by
    intro p hp
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hnn : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ (-θ) := fun p => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have h1 : f 1 = 1 := by simp [hf]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n _
    simp only [hf, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simp only [hpow, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hnn p)]
    exact summable_geometric_of_lt_one (hnn p) (hlt hp)
  obtain ⟨hs, hh⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 hmul hsum X₀
  refine ⟨hs.of_norm, ?_⟩
  convert hh using 1
  unfold rankinConst
  apply prod_congr rfl
  intro p hp
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  simp only [hpow]
  rw [tsum_geometric_of_lt_one (hnn p) (hlt hp')]

/-- **Rankin's bound**: `Ψ(x, X₀) ≤ x^θ ∏_{p < X₀} (1 - p^{-θ})^{-1}` for `θ > 0`, `x ≥ 0`. -/
theorem smoothCount_le_rankin (X₀ : ℕ) {θ : ℝ} (hθ : 0 < θ) {x : ℝ} (hx : 0 ≤ x) :
    (smoothCount X₀ x : ℝ) ≤ x ^ θ * rankinConst X₀ θ := by
  obtain ⟨hs, hh⟩ := hasSum_smooth_rpow X₀ hθ
  set S := Nat.smoothNumbersUpTo ⌊x⌋₊ X₀ with hS
  have hmem : ∀ n ∈ S, n ∈ X₀.smoothNumbers ∧ 1 ≤ n ∧ (n : ℝ) ≤ x := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    refine ⟨hn.2, Nat.one_le_iff_ne_zero.mpr hn.2.1, ?_⟩
    exact (Nat.cast_le.mpr hn.1).trans (Nat.floor_le hx)
  have h1 : (smoothCount X₀ x : ℝ) ≤ ∑ n ∈ S, x ^ θ * (n : ℝ) ^ (-θ) := by
    unfold smoothCount
    rw [← hS, card_eq_sum_ones, Nat.cast_sum]
    apply sum_le_sum
    intro n hn
    obtain ⟨-, hn1, hnx⟩ := hmem n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    simp only [Nat.cast_one, one_mul]
    exact Real.rpow_le_rpow hn0.le hnx hθ.le
  have h2 : ∑ n ∈ S, (n : ℝ) ^ (-θ) ≤ rankinConst X₀ θ := by
    rw [← hh.tsum_eq]
    have hsub : ∑ n ∈ S, (n : ℝ) ^ (-θ) =
        ∑ m ∈ S.subtype (· ∈ X₀.smoothNumbers), ((m : ℕ) : ℝ) ^ (-θ) := by
      rw [sum_subtype_of_mem (fun n : ℕ => (n : ℝ) ^ (-θ))]
      exact fun n hn => (hmem n hn).1
    rw [hsub]
    exact hs.sum_le_tsum _ (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc (smoothCount X₀ x : ℝ) ≤ ∑ n ∈ S, x ^ θ * (n : ℝ) ^ (-θ) := h1
    _ = x ^ θ * ∑ n ∈ S, (n : ℝ) ^ (-θ) := by rw [mul_sum]
    _ ≤ x ^ θ * rankinConst X₀ θ :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx θ)

end Rankin

end
