module

public import RequestProject.Beurling.GenLemma51Final

/-!
# The Euler-factor sums behind (F3′) and Lemma A.6 (S3)(d)

For `v > 1` put `w(v) = -log(1 - 1/v)`, so `(1 - 1/v)⁻¹ = e^{w(v)}`. For a Beurling system whose
local Mertens bound (Lemma 5.1(iv)) holds at every height,

* `wE_le` : `w(v) ≤ 1/v + 2/v²` for `v ≥ 2`;
* `sum_inv_sq_realised_le` : `∑_{y₀ < p ≤ V} 1/p² ≤ 5.8/(y₀ log y₀)` (dyadic blocks and (iv));
* `sum_wE_le` : `∑_{y₀ < p ≤ V} w(p) ≤ log(log V/log y₀) + 2.20/log y₀ + 11.6/(y₀ log y₀)`.

This is the second group of the proof of (F3′) (§5, "the realised primes in `(y₀, s - H(s)]`"),
with `1/y₀` replaced by the dyadic bound for the second-order terms.

The rational primes enter through the Mertens product estimate `Mertens.ZinfR_one_le`
(`∏_{p<X} (1 - 1/p)⁻¹ ≤ 1.8 log X` for `log X ≥ 10⁴`), not through Rosser–Schoenfeld.
-/

@[expose] public section

open Finset Real

namespace BModel

/-- `w(v) = -log(1 - 1/v)`, the logarithm of the Euler factor `(1 - 1/v)⁻¹`. -/
noncomputable def wE (v : ℝ) : ℝ := -Real.log (1 - v⁻¹)

lemma wE_arg_pos {v : ℝ} (hv : 1 < v) : 0 < 1 - v⁻¹ := by
  have : v⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv
  linarith

lemma exp_wE {v : ℝ} (hv : 1 < v) : Real.exp (wE v) = (1 - v⁻¹)⁻¹ := by
  unfold wE; rw [Real.exp_neg, Real.exp_log (wE_arg_pos hv)]

lemma wE_nonneg {v : ℝ} (hv : 1 < v) : 0 ≤ wE v := by
  unfold wE
  have h0 : 0 < v⁻¹ := by have : 0 < v := by linarith
                          positivity
  have h1 : 1 - v⁻¹ ≤ 1 := by linarith
  have := Real.log_nonpos (wE_arg_pos hv).le h1
  linarith

/-- `w(v) ≤ 1/v + 2/v²` for `v ≥ 2`. -/
lemma wE_le {v : ℝ} (hv : 2 ≤ v) : wE v ≤ v⁻¹ + 2 * v⁻¹ ^ 2 := by
  set t := v⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [ht]; exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hpos : 0 < 1 - t := by linarith
  unfold wE
  rw [← ht, ← Real.log_inv]
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have h2 : (1 - t)⁻¹ ≤ 1 + t + 2 * t ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

/-- The local Mertens bound (Lemma 5.1(iv)), upper half, at every height. -/
def MertensUpper (P : BeurlingSystem) : Prop :=
  ∀ y x : ℝ, 2 ≤ y → y ≤ x →
    ∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j ≤
      Real.log (Real.log x / Real.log y) + 2.20 / Real.log y

/-- (HBS) at every height gives `MertensUpper` (Lemma 5.1(iv)). -/
lemma mertensUpper_of_HBS {P : BeurlingSystem} {X0m η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : ∀ z, P.HBS X0m z η1 η2 ε1) : MertensUpper P := by
  intro y x hy hyx
  have := P.lemma_5_1 (h x) (by linarith) le_rfl
  have h2 := (abs_le.mp (this.2.2.2 y hy hyx)).2
  linarith

/-- One dyadic block: `∑_{y < p ≤ 2y} 1/p² ≤ 2.9/(y log y)` for `y ≥ 3`. -/
lemma block_inv_sq_le {P : BeurlingSystem} (hM : MertensUpper P) {y : ℝ} (hy : 3 ≤ y) :
    ∑ j ∈ (P.primesLe (2 * y)).filter (fun j => y < P.p j), 1 / P.p j ^ 2 ≤
      2.9 / (y * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hL : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  have h1 : ∀ j ∈ (P.primesLe (2 * y)).filter (fun j => y < P.p j),
      1 / P.p j ^ 2 ≤ y⁻¹ * (1 / P.p j) := by
    intro j hj
    rw [mem_filter] at hj
    have hp : 0 < P.p j := by linarith [hj.2]
    have e : y⁻¹ * (1 / P.p j) = 1 / (y * P.p j) := by field_simp
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_right hj.2.le hp.le
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h2 := hM y (2 * y) (by linarith) (by linarith)
  have hl2 : Real.log (Real.log (2 * y) / Real.log y) ≤ 0.7 / Real.log y := by
    rw [Real.log_mul (by norm_num) hy0.ne']
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (Real.log 2 + Real.log y) / Real.log y by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    have e : (Real.log 2 + Real.log y) / Real.log y - 1 = Real.log 2 / Real.log y := by
      field_simp; ring
    rw [e] at h
    have := Real.log_two_lt_d9
    have : Real.log 2 / Real.log y ≤ 0.7 / Real.log y :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have h3 : ∑ j ∈ (P.primesLe (2 * y)).filter (fun j => y < P.p j), 1 / P.p j ≤
      2.9 / Real.log y := by
    have : 2.9 / Real.log y = 0.7 / Real.log y + 2.20 / Real.log y := by ring
    linarith
  calc y⁻¹ * ∑ j ∈ (P.primesLe (2 * y)).filter (fun j => y < P.p j), 1 / P.p j
      ≤ y⁻¹ * (2.9 / Real.log y) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2.9 / (y * Real.log y) := by field_simp

/-- **The second-order terms**: `∑_{y₀ < p ≤ V} 1/p² ≤ 5.8/(y₀ log y₀)` for `y₀ ≥ 3`. -/
theorem sum_inv_sq_realised_le {P : BeurlingSystem} (hM : MertensUpper P) {y₀ : ℝ}
    (hy : 3 ≤ y₀) (V : ℝ) :
    ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2 ≤
      5.8 / (y₀ * Real.log y₀) := by
  have hy0 : 0 < y₀ := by linarith
  have hL : 0 < Real.log y₀ := Real.log_pos (by linarith)
  set c := 5.8 / (y₀ * Real.log y₀) with hc
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ K : ℕ, ∑ j ∈ (P.primesLe (y₀ * 2 ^ K)).filter (fun j => y₀ < P.p j),
      1 / P.p j ^ 2 ≤ c * (1 - (1 / 2) ^ K) := by
    intro K
    induction K with
    | zero =>
      simp only [pow_zero, mul_one, sub_self, mul_zero]
      rw [Finset.sum_eq_zero]
      intro j hj
      rw [mem_filter, BeurlingSystem.mem_primesLe] at hj
      linarith [hj.1, hj.2]
    | succ K ih =>
      set y := y₀ * 2 ^ K with hydef
      have hyy : y₀ ≤ y := by
        rw [hydef]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := K)]
      rw [← sum_filter_add_sum_filter_not _ (fun j => P.p j ≤ y)]
      have hA : ∑ j ∈ ((P.primesLe (y₀ * 2 ^ (K + 1))).filter (fun j => y₀ < P.p j)).filter
          (fun j => P.p j ≤ y), 1 / P.p j ^ 2 ≤
          ∑ j ∈ (P.primesLe y).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe] at hj ⊢
          exact ⟨hj.2, hj.1.2⟩
        · intro j _ _; positivity
      have hB : ∑ j ∈ ((P.primesLe (y₀ * 2 ^ (K + 1))).filter (fun j => y₀ < P.p j)).filter
          (fun j => ¬ P.p j ≤ y), 1 / P.p j ^ 2 ≤
          ∑ j ∈ (P.primesLe (2 * y)).filter (fun j => y < P.p j), 1 / P.p j ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe, not_le] at hj ⊢
          refine ⟨?_, hj.2⟩
          have : y₀ * 2 ^ (K + 1) = 2 * y := by rw [hydef, pow_succ]; ring
          linarith [hj.1.1]
        · intro j _ _; positivity
      have hb := block_inv_sq_le hM (y := y) (by linarith)
      have hlog : Real.log y₀ ≤ Real.log y := Real.log_le_log hy0 hyy
      have hb2 : 2.9 / (y * Real.log y) ≤ 2.9 / (y * Real.log y₀) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hlog (by linarith))
      have e : 2.9 / (y * Real.log y₀) = c * (1 / 2) ^ K / 2 := by
        have h2K : (1 / 2 : ℝ) ^ K * 2 ^ K = 1 := by
          rw [← mul_pow]; norm_num
        rw [hc, hydef]; field_simp; linear_combination (-(29 / 5) : ℝ) * h2K
      have e2 : c * (1 - (1 / 2) ^ (K + 1)) = c * (1 - (1 / 2) ^ K) + c * (1 / 2) ^ K / 2 := by
        ring
      linarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (V / y₀) (by norm_num : (1 : ℝ) < 2)
  have hVK : V ≤ y₀ * 2 ^ K := by
    rw [div_lt_iff₀ hy0] at hK; linarith
  calc ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2
      ≤ ∑ j ∈ (P.primesLe (y₀ * 2 ^ K)).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe] at hj ⊢
          exact ⟨hj.1.trans hVK, hj.2⟩
        · intro j _ _; positivity
    _ ≤ c * (1 - (1 / 2) ^ K) := key K
    _ ≤ c := by
        have : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
        nlinarith

/-- **The realised Euler factors above `y₀`**:
`∑_{y₀ < p ≤ V} w(p) ≤ log(log V/log y₀) + 2.20/log y₀ + 11.6/(y₀ log y₀)`. -/
theorem sum_wE_le {P : BeurlingSystem} (hM : MertensUpper P) {y₀ V : ℝ} (hy : 3 ≤ y₀)
    (hyV : y₀ ≤ V) :
    ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), wE (P.p j) ≤
      Real.log (Real.log V / Real.log y₀) + 2.20 / Real.log y₀ +
        11.6 / (y₀ * Real.log y₀) := by
  have h1 : ∀ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j),
      wE (P.p j) ≤ 1 / P.p j + 2 * (1 / P.p j ^ 2) := by
    intro j hj
    rw [mem_filter] at hj
    have := wE_le (v := P.p j) (by linarith [hj.2])
    simp only [one_div, inv_pow] at this ⊢
    exact this
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h2 := hM y₀ V (by linarith) hyV
  have h3 := sum_inv_sq_realised_le hM hy V
  have e : 11.6 / (y₀ * Real.log y₀) = 2 * (5.8 / (y₀ * Real.log y₀)) := by ring
  linarith

end BModel
