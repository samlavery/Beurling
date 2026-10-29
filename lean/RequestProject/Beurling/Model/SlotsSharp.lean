module

public import RequestProject.Beurling.Model.Window

/-!
# The sharp slot density (standing fact (F1) of §6)

* `contD_upper_log` : `C(x') - C(x) ≤ (1 + 0.02/log x)(x' - x)` on `[X₀, ∞)` (`ρ_det, ρ̄_A ≥ 0` and
  `|R'| ≤ 0.02/log`, `abs_deriv_osc_le`): the continuous slot starts have density at most
  `T'_cont ≤ 1 + κ₊/log`;
* `window_count_sharp` : a window `(a, b]`, `X₀ ≤ a`, holds at most `(1 + 0.02/log a)(b - a) + 1`
  starts of placed slots with unit jumps.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **The sharp upper slope of the continuous part.** -/
theorem contD_upper_log (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    (hX : 10 ^ 8 ≤ Real.log X₀) (D : PrimeData) (hD : LocFinD D) {x x' : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    contD θ X₀ D x' - contD θ X₀ D x ≤ (1 + 0.02 / Real.log x) * (x' - x) := by
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  have hA := absSet_locFin (X₀ := X₀) hD
  unfold contD
  rw [show uA θ = (fun n => solveU (θ / 2) n) from rfl]
  rw [contPart_sub (fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy)
    (fun y hy => intervalIntegrable_absorbedDensityCap _ hA hb hX1 hy) hx hxx]
  have h1 : 0 ≤ ∫ u in x..x', Target.rhoDet X₀ (kappaParam X₀) u :=
    intervalIntegral.integral_nonneg hxx fun u hu => rhoDet_nonneg X₀ hκ0 (by linarith [hu.1])
  have h2 : 0 ≤ ∫ u in x..x', absorbedDensityCap (θ / 2) (absSet X₀ D)
      (fun n => solveU (θ / 2) n) u :=
    intervalIntegral.integral_nonneg hxx fun u hu =>
      (absorbedDensityCap_mem _ (by linarith [hu.1]) _).1
  have hlx : 10 ^ 8 ≤ Real.log x := hX.trans (Real.log_le_log (by linarith) hx)
  have hγ := gammaD_range (θ := θ) hX D
  have hR := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Icc x x')
    (f := osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) (C := 0.02 / Real.log x)
    (fun y hy => (hasDerivAt_osc _ _ hX1.le (by linarith [hy.1])).differentiableAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      refine (abs_deriv_osc_le hθ hX hγ (hx.trans hy.1)).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith)
        (Real.log_le_log (by linarith) hy.1))
    (convex_Icc _ _) (left_mem_Icc.mpr hxx) (right_mem_Icc.mpr hxx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x' - x)] at hR
  have h4 := (abs_le.mp hR).2
  have : (1 + 0.02 / Real.log x) * (x' - x) = (x' - x) + 0.02 / Real.log x * (x' - x) := by
    ring
  linarith

section Sharp

variable {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- **The sharp window count of placed slot starts with unit jumps.** -/
theorem window_count_sharp (S₀ : Set ℕ)
    (hS₀ : ∀ m ∈ S₀, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel U) (h.limModel.slot (m + 1)))
    {a b : ℝ} (ha : (X₀ : ℝ) ≤ a) (hab : a ≤ b) :
    ({m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧ h.limModel.slot (m + 1) ≤ b}.ncard : ℝ) ≤
      (1 + 0.02 / Real.log a) * (b - a) + 1 := by
  classical
  set M := h.limModel
  set W := winFacts h
  set S := {m | m ∈ S₀ ∧ a < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}
  have hX := h.hX
  have hla : 10 ^ 8 ≤ Real.log a := hX.trans (Real.log_le_log (by
    linarith [X₀_ge_two_pow hX]) ha)
  have hge : ∀ m ∈ S, (X₀ : ℝ) < M.slot (m + 1) := fun m hm => lt_of_le_of_lt ha hm.2.1
  have hc0 : 0 ≤ 1 + 0.02 / Real.log a := by positivity
  set C := contD θ X₀ (DM M U)
  set g : ℕ → ℕ := fun m => ⌊C (M.slot (m + 1)) - C a⌋₊
  have hpos : ∀ m ∈ S, 0 ≤ C (M.slot (m + 1)) - C a := by
    intro m hm
    have := W.cmono _ _ ha hm.2.1.le
    linarith
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' hg
    by_contra hne
    have h3 : (g m : ℝ) = g m' := by rw [hg]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := placed_gap W (hS₀ m hm.1).2 (hS₀ m' hm'.1).2 hlt (hS₀ m hm.1).1
        (hS₀ m' hm'.1).1 (hge m hm)
      have h1 := Nat.floor_le (hpos m hm)
      have h2 := Nat.lt_floor_add_one (C (M.slot (m' + 1)) - C a)
      simp only [g] at h3
      linarith
    · have := placed_gap W (hS₀ m' hm'.1).2 (hS₀ m hm.1).2 hlt (hS₀ m' hm'.1).1
        (hS₀ m hm.1).1 (hge m' hm')
      have h1 := Nat.floor_le (hpos m' hm')
      have h2 := Nat.lt_floor_add_one (C (M.slot (m + 1)) - C a)
      simp only [g] at h3
      linarith
  have hmaps : Set.MapsTo g S
      (Finset.range (⌊(1 + 0.02 / Real.log a) * (b - a)⌋₊ + 1) : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    have hup := contD_upper_log h.hθ hX (DM M U) (locFinD_DM hX h.hU _) ha hm.2.1.le
    have h0 : 0 ≤ M.slot (m + 1) - a := by linarith [hm.2.1]
    have : (1 + 0.02 / Real.log a) * (M.slot (m + 1) - a) ≤
        (1 + 0.02 / Real.log a) * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hm.2.2]) hc0
    linarith
  have hcard := Set.ncard_le_ncard_of_injOn g hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at hcard
  have hL0 : 0 ≤ (1 + 0.02 / Real.log a) * (b - a) := mul_nonneg hc0 (by linarith)
  have h1 : ((⌊(1 + 0.02 / Real.log a) * (b - a)⌋₊ + 1 : ℕ) : ℝ) ≤
      (1 + 0.02 / Real.log a) * (b - a) + 1 := by
    push_cast; linarith [Nat.floor_le hL0]
  have hc : (S.ncard : ℝ) ≤ ((⌊(1 + 0.02 / Real.log a) * (b - a)⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

end Sharp

end BModel

end
