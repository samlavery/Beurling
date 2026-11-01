module

public import RequestProject.Beurling.GenChebyshev

/-!
# Partial summation for `∫ log v dN` and the first error integral of Lemma 5.1

* `sum_log_eq` : for finitely many points `v_i ∈ [1, x]`,
  `∑ log v_i = #· log x - ∫_1^x #{i : v_i ≤ t} dt / t`;
* `ellN_eq`, `log_factorial_floor_eq` : the two instances, `∫_{[1,x]} log v dN` for a Beurling
  system and `log ⌊x⌋!` for `ℕ`;
* `abs_ellN_sub_le` : with `E₁ = N - ⌊·⌋`, `|∫ log v dE₁| ≤ |E₁(x)| log x + ∫_1^x |E₁(v)| dv/v`,
  bounded by `d x + c x` when `|E₁(x)| log x ≤ d x` and `|E₁(t)| ≤ c t` on `[1, x]`.
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace GenPartial

lemma intervalIntegrable_indicator_inv {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable ((Set.Ici v).indicator (fun t : ℝ => 1 / t)) volume a b := by
  have hc : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (lt_of_lt_of_le ha ht.1).ne'
  rw [intervalIntegrable_iff] at hc ⊢
  exact hc.indicator measurableSet_Ici

/-- `∫_1^x 1_{t ≥ v} dt/t = log x - log v` for `1 ≤ v ≤ x`. -/
lemma integral_indicator_inv {v x : ℝ} (hv : 1 ≤ v) (hvx : v ≤ x) :
    ∫ t in (1 : ℝ)..x, (Set.Ici v).indicator (fun t : ℝ => 1 / t) t =
      Real.log x - Real.log v := by
  rw [← integral_add_adjacent_intervals (b := v)
    (intervalIntegrable_indicator_inv one_pos hv)
    (intervalIntegrable_indicator_inv (by linarith) hvx)]
  have h1 : ∫ t in (1 : ℝ)..v, (Set.Ici v).indicator (fun t : ℝ => 1 / t) t = 0 := by
    rw [integral_of_le hv, setIntegral_indicator measurableSet_Ici]
    apply setIntegral_measure_zero
    apply measure_mono_null (t := {v})
    · intro t ht; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici] at ht
      exact le_antisymm ht.1.2 ht.2
    · exact Real.volume_singleton
  have h2 : ∫ t in v..x, (Set.Ici v).indicator (fun t : ℝ => 1 / t) t =
      ∫ t in v..x, 1 / t := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hvx] at ht
    simp [Set.indicator_of_mem (show t ∈ Set.Ici v from ht.1)]
  rw [h1, h2, integral_one_div, Real.log_div (by linarith) (by linarith)]
  · ring
  · rw [Set.uIcc_of_le hvx]; intro h; linarith [h.1]

/-- **Partial summation**: for points `v_i ∈ [1, x]`,
`∑ log v_i = #s · log x - ∫_1^x #{i : v_i ≤ t} dt/t`. -/
theorem sum_log_eq {ι : Type*} (s : Finset ι) (v : ι → ℝ) {x : ℝ}
    (hv : ∀ i ∈ s, 1 ≤ v i ∧ v i ≤ x) :
    ∑ i ∈ s, Real.log (v i) = (s.card : ℝ) * Real.log x -
      ∫ t in (1 : ℝ)..x, ((s.filter (fun i => v i ≤ t)).card : ℝ) / t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp
  have hx : 1 ≤ x := (hv i0 hi0).1.trans (hv i0 hi0).2
  have hfun : (fun t : ℝ => ((s.filter (fun i => v i ≤ t)).card : ℝ) / t) =
      fun t => ∑ i ∈ s, (Set.Ici (v i)).indicator (fun t : ℝ => 1 / t) t := by
    funext t
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v i ≤ t
    · simp [h, Set.indicator_of_mem (show t ∈ Set.Ici (v i) from h)]
    · simp [h, Set.indicator_of_notMem (show t ∉ Set.Ici (v i) from h)]
  rw [hfun, integral_finset_sum (fun i _ => intervalIntegrable_indicator_inv one_pos hx)]
  rw [Finset.sum_congr rfl (fun i hi => integral_indicator_inv (hv i hi).1 (hv i hi).2)]
  rw [Finset.sum_sub_distrib]
  simp

end GenPartial

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- Partial summation for a Beurling system: `ℓ_N(x) = N(x) log x - ∫_1^x N(t) dt/t`. -/
theorem ellN_eq {x : ℝ} (hx : 1 ≤ x) :
    P.ellN x = P.N x * Real.log x - ∫ t in (1 : ℝ)..x, P.N t / t := by
  unfold ellN
  rw [GenPartial.sum_log_eq (P.elems x) P.val (fun e he => ⟨P.one_le_val e, (P.mem_elems).mp he⟩),
    N_eq_card]
  congr 1
  apply integral_congr
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  simp only
  rw [N_eq_card]
  congr 3
  ext e; simp only [mem_filter, mem_elems]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.trans ht.2, h⟩

/-- Partial summation for `ℕ`: `log ⌊x⌋! = ⌊x⌋ log x - ∫_1^x ⌊t⌋ dt/t`. -/
theorem log_factorial_floor_eq {x : ℝ} (hx : 1 ≤ x) :
    Real.log (⌊x⌋₊.factorial : ℝ) = (⌊x⌋₊ : ℝ) * Real.log x -
      ∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t := by
  have hx0 : 0 ≤ x := by linarith
  have hfac : Real.log (⌊x⌋₊.factorial : ℝ) = ∑ n ∈ Icc 1 ⌊x⌋₊, Real.log (n : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Finset.Ico_add_one_right_eq_Icc, Nat.cast_prod, Real.log_prod]
    intro n hn; have := (mem_Icc.mp hn).1; positivity
  rw [hfac, GenPartial.sum_log_eq (Icc 1 ⌊x⌋₊) (fun n : ℕ => (n : ℝ))]
  · simp only [Nat.card_Icc, add_tsub_cancel_right]
    congr 1
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    simp only
    congr 2
    have : (Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t) = Icc 1 ⌊t⌋₊ := by
      ext n; simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (Nat.floor_le_floor ht.2)⟩, (Nat.le_floor_iff ht0).mp h2⟩
    rw [this, Nat.card_Icc, add_tsub_cancel_right]
  · intro n hn
    rw [mem_Icc] at hn
    exact ⟨by exact_mod_cast hn.1, (Nat.le_floor_iff hx0).mp hn.2⟩

lemma intervalIntegrable_E_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (P.N t - (⌊t⌋₊ : ℝ)) / t) volume a b := by
  have h1 : IntervalIntegrable (fun t => P.N t - (⌊t⌋₊ : ℝ)) volume a b :=
    (P.N_mono.intervalIntegrable).sub
      (Monotone.intervalIntegrable fun s t h => by
        exact_mod_cast Nat.floor_le_floor h)
  have h2 : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc a b) := by
    apply continuousOn_inv₀.mono
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (lt_of_lt_of_le ha ht.1).ne'
  have := h1.mul_continuousOn h2
  simpa [div_eq_mul_inv] using this

/-- **The first error integral of Lemma 5.1**: with `E₁ = N - ⌊·⌋`,
`∫_{[1,x]} log v dE₁(v) = ℓ_N(x) - log ⌊x⌋!` satisfies
`|ℓ_N(x) - log ⌊x⌋!| ≤ d x + c x` if `|E₁(x)| log x ≤ d x` and `|E₁(t)| ≤ c t` on `[1, x]`. -/
theorem abs_ellN_sub_le {x c d : ℝ} (hx : 1 ≤ x)
    (hc : ∀ t ∈ Set.Icc 1 x, |P.N t - ⌊t⌋₊| ≤ c * t)
    (hd : |P.N x - ⌊x⌋₊| * Real.log x ≤ d * x) :
    |P.ellN x - Real.log (⌊x⌋₊.factorial : ℝ)| ≤ d * x + c * x := by
  have hc0 : 0 ≤ c := by
    have := (abs_nonneg _).trans (hc 1 ⟨le_rfl, hx⟩); linarith
  have e : P.ellN x - Real.log (⌊x⌋₊.factorial : ℝ) =
      (P.N x - ⌊x⌋₊) * Real.log x - ∫ t in (1 : ℝ)..x, (P.N t - (⌊t⌋₊ : ℝ)) / t := by
    rw [P.ellN_eq hx, log_factorial_floor_eq hx]
    have hi2 : IntervalIntegrable (fun t => (⌊t⌋₊ : ℝ) / t) volume 1 x := by
      have := (Monotone.intervalIntegrable (μ := volume) (u := fun t : ℝ => (⌊t⌋₊ : ℝ))
          (a := 1) (b := x)
          (fun s t h => by
            show ((⌊s⌋₊ : ℕ) : ℝ) ≤ ⌊t⌋₊; exact_mod_cast Nat.floor_le_floor h)).mul_continuousOn
          (g := fun t : ℝ => t⁻¹) (continuousOn_inv₀.mono (by
            intro t ht; rw [Set.uIcc_of_le hx] at ht
            exact (lt_of_lt_of_le one_pos ht.1).ne'))
      simpa [div_eq_mul_inv] using this
    have hi1 : IntervalIntegrable (fun t => P.N t / t) volume 1 x := by
      refine ((P.intervalIntegrable_E_div one_pos hx).add hi2).congr ?_
      intro t _
      simp only [Pi.add_apply]; ring
    have : (∫ t in (1 : ℝ)..x, (P.N t - (⌊t⌋₊ : ℝ)) / t) =
        (∫ t in (1 : ℝ)..x, P.N t / t) - ∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t := by
      rw [← integral_sub hi1 hi2]
      congr 1; funext t; ring
    rw [this]; ring
  have hint : |∫ t in (1 : ℝ)..x, (P.N t - (⌊t⌋₊ : ℝ)) / t| ≤ c * |x - 1| := by
    have := norm_integral_le_of_norm_le_const (a := 1) (b := x) (C := c)
      (f := fun t => (P.N t - (⌊t⌋₊ : ℝ)) / t) (by
        intro t ht
        rw [Set.uIoc_of_le hx] at ht
        have ht0 : 0 < t := by linarith [ht.1]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
        exact hc t ⟨ht.1.le, ht.2⟩)
    simpa [Real.norm_eq_abs] using this
  rw [e]
  have habs : |x - 1| ≤ x := by rw [abs_of_nonneg (by linarith)]; linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc |(P.N x - ⌊x⌋₊) * Real.log x - ∫ t in (1 : ℝ)..x, (P.N t - (⌊t⌋₊ : ℝ)) / t|
      ≤ |(P.N x - ⌊x⌋₊) * Real.log x| + |∫ t in (1 : ℝ)..x, (P.N t - (⌊t⌋₊ : ℝ)) / t| :=
        abs_sub _ _
    _ ≤ d * x + c * x := by
        rw [abs_mul, abs_of_nonneg hlog]
        nlinarith

end BeurlingSystem

end
