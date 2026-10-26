module

public import RequestProject.Beurling.Weights

/-!
# The absorbed part `Ê_A` and Lemma 4.4(a)

For the absorbed set `A ⊆ ℕ` with forward-window weights `w_a` (Section 4.1, after (14)),

  `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))`.

Given a counting bound `#(A ∩ [1, x]) ≤ x e^{-ς(log x)}` with `ς` nondecreasing (the Rankin
bound of Lemma 6.26, used in the proof of Lemma 4.4), the weight bounds (ii) and (iv) and partial
summation give, for `1 - δ ≤ σ ≤ 2` and `|t| ≥ 2`, with `Y = |t|^{1/(1-b)}`:

  `|Ê_A(s)| ≤ 2.001 (Y^δ e^{-ς(log Y)} + ∫_1^Y v^{δ-1} e^{-ς(log v)} dv) + 5.4 Y^δ e^{-ς(log Y)}`.

This is the estimate in the proof of Lemma 4.4(a) (terms `a ≤ Y` and `a > Y`).
-/

@[expose] public section

open Complex Set Filter MeasureTheory Finset

namespace Absorbed

open scoped Classical

/-- The counting function `#(A ∩ [0, x])` of `A ⊆ ℕ`. -/
noncomputable def countA (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (if k ∈ A then (1 : ℝ) else 0)

/-- The standing hypotheses on the absorbed set: every `a ∈ A` satisfies the hypotheses of the
weight bounds, with `u a = u_a` (`u_a + u_a^b = a`, `a ≥ 10⁶`, `0 < b ≤ 1/4`). -/
structure AbsorbedHyp (b : ℝ) (A : Set ℕ) (u : ℕ → ℝ) : Prop where
  b_pos : 0 < b
  b_le : b ≤ 1 / 4
  weight : ∀ a ∈ A, Weights.WeightHyp b a (u a)

/-- The term `a^{-s} (1 - w_a(s))` of `Ê_A` (zero off `A`). -/
noncomputable def absorbedTerm (b : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if n ∈ A then ((n : ℝ) : ℂ) ^ (-s) * (1 - Weights.weight b n (u n) s) else 0

/-- The absorbed part `Ê_A(s) = ∑_{a ∈ A} a^{-s} (1 - w_a(s))`. -/
noncomputable def absorbedHat (b : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, absorbedTerm b A u s n

/-- The explicit bound of Lemma 4.4(a). -/
noncomputable def absorbedBound (ς : ℝ → ℝ) (δ Y : ℝ) : ℝ :=
  2.001 * (Y ^ δ * Real.exp (-ς (Real.log Y)) +
    ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v))) +
  5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y)))

lemma countA_mono (A : Set ℕ) : Monotone (countA A) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp at hk ⊢; exact hk.trans (Nat.floor_le_floor hxy)
  · intro k _ _; split_ifs <;> norm_num

lemma countA_nonneg (A : Set ℕ) (x : ℝ) : 0 ≤ countA A x :=
  Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

lemma integrableOn_Ioc_of_bdd {f : ℝ → ℝ} {a Y C : ℝ} (hf : Measurable f)
    (hb : ∀ v ∈ Ioc a Y, |f v| ≤ C) : IntegrableOn f (Ioc a Y) := by
  refine Integrable.mono' (g := fun _ => C) (integrableOn_const (by simp))
    hf.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun v hv => ?_
  simpa using hb v hv

lemma measurable_rpow_mul_exp {ς : ℝ → ℝ} (hς : Monotone ς) {p : ℝ} :
    Measurable fun v : ℝ => v ^ p * Real.exp (-ς (Real.log v)) := by
  have := hς.measurable
  fun_prop

/-- Partial summation over `A ∩ (1, Y]` for `k ↦ k^{-γ}`. -/
lemma head_sum_eq (A : Set ℕ) (hA : ∀ a ∈ A, 2 ≤ a) {γ Y : ℝ} (hY : 1 ≤ Y) :
    ∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, (if k ∈ A then (k : ℝ) ^ (-γ) else 0) =
      Y ^ (-γ) * countA A Y + γ * ∫ v in Ioc 1 Y, v ^ (-γ - 1) * countA A v := by
  have hab := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) (fun k => if k ∈ A then (1 : ℝ) else 0)
    (f := fun t : ℝ => t ^ (-γ)) (a := 1) (b := Y) zero_le_one hY
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1]))
    (by
      have : deriv (fun t : ℝ => t ^ (-γ)) = fun x => -γ * x ^ (-γ - 1) := by
        ext x; exact Real.deriv_rpow_const x (-γ)
      rw [this]
      exact (ContinuousOn.mul continuousOn_const (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (by simp at hx ⊢; linarith [hx.1])))).integrableOn_compact
          isCompact_Icc)
  have hN1 : ∑ k ∈ Finset.Icc 0 ⌊(1:ℝ)⌋₊, (if k ∈ A then (1 : ℝ) else 0) = 0 := by
    rw [Nat.floor_one]
    apply Finset.sum_eq_zero
    intro k hk
    simp at hk
    rw [if_neg]; intro hkA; have := hA k hkA; omega
  rw [hN1, Nat.floor_one] at hab
  have hL : ∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, (if k ∈ A then (k : ℝ) ^ (-γ) else 0) =
      ∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, (k : ℝ) ^ (-γ) * (if k ∈ A then (1 : ℝ) else 0) := by
    have hsub : Finset.Ioc 1 ⌊Y⌋₊ ⊆ Finset.Icc 0 ⌊Y⌋₊ := by
      intro k hk; simp at hk ⊢; omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    · intro k hk hk'
      simp at hk hk'
      rw [if_neg]; intro hkA; have := hA k hkA; omega
  rw [hL, hab]
  have hint : ∫ t in Ioc 1 Y, deriv (fun t : ℝ => t ^ (-γ)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k ∈ A then (1 : ℝ) else 0) =
      -γ * ∫ v in Ioc 1 Y, v ^ (-γ - 1) * countA A v := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [Real.deriv_rpow_const, countA]; ring
  rw [hint, countA]; ring

lemma head_sum_le_aux (A : Set ℕ) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {δ Y : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hY : 1 ≤ Y) :
    Y ^ (-(1-δ)) * countA A Y + (1-δ) * ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v ≤
      Y ^ δ * Real.exp (-ς (Real.log Y)) +
        ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
  rw [intervalIntegral.integral_of_le hY]
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ (-(1-δ)) * countA A Y ≤ Y ^ δ * Real.exp (-ς (Real.log Y)) := by
    calc Y ^ (-(1-δ)) * countA A Y ≤ Y ^ (-(1-δ)) * (Y * Real.exp (-ς (Real.log Y))) :=
          mul_le_mul_of_nonneg_left (hN Y hY) (Real.rpow_nonneg hY0.le _)
      _ = (Y ^ (-(1-δ)) * Y ^ (1:ℝ)) * Real.exp (-ς (Real.log Y)) := by
          rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hY0]; ring_nf
  have hgi : IntegrableOn (fun v : ℝ => v ^ (δ - 1) * Real.exp (-ς (Real.log v))) (Ioc 1 Y) := by
    refine integrableOn_Ioc_of_bdd (C := Real.exp (-ς 0)) (measurable_rpow_mul_exp hς)
      fun v hv => ?_
    have hv1 : 1 ≤ v := hv.1.le
    rw [abs_of_nonneg (by positivity)]
    have : v ^ (δ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
    have : Real.exp (-ς (Real.log v)) ≤ Real.exp (-ς 0) := by
      rw [Real.exp_le_exp]; have := hς (Real.log_nonneg hv1); linarith
    have : 0 ≤ Real.exp (-ς (Real.log v)) := by positivity
    nlinarith
  have hfi : IntegrableOn (fun v : ℝ => v ^ (-(1-δ) - 1) * countA A v) (Ioc 1 Y) := by
    refine integrableOn_Ioc_of_bdd (C := countA A Y) ?_ fun v hv => ?_
    · have := (countA_mono A).measurable; fun_prop
    · have hv1 : 1 ≤ v := hv.1.le
      rw [abs_of_nonneg (mul_nonneg (by positivity) (countA_nonneg A v))]
      have : v ^ (-(1-δ) - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
      have := countA_mono A hv.2
      have := countA_nonneg A v
      nlinarith
  have h2 : ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v ≤
      ∫ v in Ioc 1 Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
    refine setIntegral_mono_on hfi hgi measurableSet_Ioc fun v hv => ?_
    have hv0 : 0 < v := by linarith [hv.1]
    calc v ^ (-(1-δ) - 1) * countA A v ≤ v ^ (-(1-δ) - 1) * (v * Real.exp (-ς (Real.log v))) :=
          mul_le_mul_of_nonneg_left (hN v hv.1.le) (Real.rpow_nonneg hv0.le _)
      _ = (v ^ (-(1-δ) - 1) * v ^ (1:ℝ)) * Real.exp (-ς (Real.log v)) := by
          rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hv0]; ring_nf
  have h3 : 0 ≤ ∫ v in Ioc 1 Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) :=
    setIntegral_nonneg measurableSet_Ioc fun v hv => by
      have : 0 < v := by linarith [hv.1]
      positivity
  have h4 : 0 ≤ ∫ v in Ioc 1 Y, v ^ (-(1-δ) - 1) * countA A v :=
    setIntegral_nonneg measurableSet_Ioc fun v hv => by
      have : 0 < v := by linarith [hv.1]
      have := countA_nonneg A v
      positivity
  nlinarith

/-- The head estimate: `∑_{a ∈ A, a ≤ Y} a^{δ-1} ≤ Y^δ e^{-ς(log Y)} + ∫_1^Y v^{δ-1} e^{-ς(log v)}`. -/
lemma head_sum_le (A : Set ℕ) (hA : ∀ a ∈ A, 2 ≤ a) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {δ Y : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) (hY : 1 ≤ Y) :
    ∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, (if k ∈ A then (k : ℝ) ^ (δ - 1) else 0) ≤
      Y ^ δ * Real.exp (-ς (Real.log Y)) +
        ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) := by
  have e := head_sum_eq A hA (γ := 1 - δ) hY
  have key := head_sum_le_aux A hς hN hδ0 hδ hY
  simp only [show -(1 - δ) = δ - 1 by ring] at e key
  linarith

/-- Partial summation over `A ∩ (Y, Z]` for `k ↦ k^{-β}`, `β > 1`. -/
lemma tail_Ioc_le (A : Set ℕ) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y Z : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊Z⌋₊, (k : ℝ) ^ (-β) * (if k ∈ A then (1 : ℝ) else 0) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hder : deriv (fun t : ℝ => t ^ (-β)) = fun x => -β * x ^ (-β - 1) := by
    ext x; exact Real.deriv_rpow_const x (-β)
  have hab := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) (fun k => if k ∈ A then (1 : ℝ) else 0)
    (f := fun t : ℝ => t ^ (-β)) (a := Y) (b := Z) hY0.le hYZ
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1]))
    (by
      rw [hder]
      exact (ContinuousOn.mul continuousOn_const (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (by simp at hx ⊢; linarith [hx.1])))).integrableOn_compact
          isCompact_Icc)
  set C := Real.exp (-ς (Real.log Y))
  have hC : 0 ≤ C := by positivity
  have hint : ∫ t in Ioc Y Z, deriv (fun t : ℝ => t ^ (-β)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k ∈ A then (1 : ℝ) else 0) =
      -β * ∫ v in Ioc Y Z, v ^ (-β - 1) * countA A v := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hder, countA]; ring
  simp only at hab
  rw [hab, hint]
  change Z ^ (-β) * countA A Z - Y ^ (-β) * countA A Y - -β * _ ≤ _
  have hNY : ∀ t ≥ Y, countA A t ≤ C * t := by
    intro t ht
    have := hN t (hY.trans ht)
    have h2 : Real.exp (-ς (Real.log t)) ≤ C := by
      rw [Real.exp_le_exp]; have := hς (Real.log_le_log hY0 ht); linarith
    nlinarith
  have hfi : IntegrableOn (fun v : ℝ => v ^ (-β - 1) * countA A v) (Ioc Y Z) := by
    refine integrableOn_Ioc_of_bdd (C := countA A Z) ?_ fun v hv => ?_
    · have := (countA_mono A).measurable; fun_prop
    · have hv1 : 1 ≤ v := hY.trans hv.1.le
      rw [abs_of_nonneg (mul_nonneg (by positivity) (countA_nonneg A v))]
      have : v ^ (-β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
      have := countA_mono A hv.2
      have := countA_nonneg A v
      nlinarith
  have hgi : IntegrableOn (fun v : ℝ => C * v ^ (-β)) (Ioc Y Z) :=
    ((ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (by simp at hx ⊢; linarith [hx.1]))).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self).const_mul C
  have h2 : ∫ v in Ioc Y Z, v ^ (-β - 1) * countA A v ≤ ∫ v in Ioc Y Z, C * v ^ (-β) := by
    refine setIntegral_mono_on hfi hgi measurableSet_Ioc fun v hv => ?_
    have hv0 : 0 < v := by linarith [hv.1]
    calc v ^ (-β - 1) * countA A v ≤ v ^ (-β - 1) * (C * v) :=
          mul_le_mul_of_nonneg_left (hNY v hv.1.le) (Real.rpow_nonneg hv0.le _)
      _ = C * (v ^ (-β - 1) * v ^ (1:ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hv0]; ring_nf
  have h3 : ∫ v in Ioc Y Z, C * v ^ (-β) = C * ((Z ^ (1 - β) - Y ^ (1 - β)) / (1 - β)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hYZ, integral_rpow]
    · ring_nf
    · right; refine ⟨by linarith, ?_⟩
      simp [Set.uIcc_of_le hYZ]; intro h; linarith
  have hNZ := hNY Z hYZ
  have hNY0 := countA_nonneg A Y
  have hZp : 0 ≤ Z ^ (-β) := Real.rpow_nonneg hZ0.le _
  have hZZ : Z ^ (-β) * (C * Z) = C * Z ^ (1 - β) := by
    rw [show (1 - β) = -β + 1 by ring, Real.rpow_add hZ0, Real.rpow_one]; ring
  have hZb : 0 ≤ Z ^ (1 - β) := Real.rpow_nonneg hZ0.le _
  have hb1 : β - 1 ≠ 0 := by intro h; linarith
  have hb1' : 1 - β ≠ 0 := by intro h; linarith
  have hb0 : 0 < β := by linarith
  have e : β * (C * ((Z ^ (1 - β) - Y ^ (1 - β)) / (1 - β))) =
      β / (β - 1) * C * Y ^ (1 - β) - β / (β - 1) * C * Z ^ (1 - β) := by
    field_simp; ring
  have hfin : Z ^ (-β) * countA A Z ≤ C * Z ^ (1 - β) := by
    rw [← hZZ]; exact mul_le_mul_of_nonneg_left hNZ hZp
  have hYb : 0 ≤ Y ^ (-β) * countA A Y := mul_nonneg (Real.rpow_nonneg hY0.le _) hNY0
  have hβ1 : 1 ≤ β / (β - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
  rw [e] at h4
  have h5 : C * Z ^ (1 - β) ≤ β / (β - 1) * C * Z ^ (1 - β) := by
    have := mul_le_mul_of_nonneg_right hβ1 (mul_nonneg hC hZb)
    linarith
  linarith

/-- The tail estimate: for `β > 1`, the finite sums `∑_{a ∈ A, Y < a < n} a^{-β}` are at most
`β/(β-1) · e^{-ς(log Y)} Y^{1-β}`. -/
lemma tail_partial_le (A : Set ℕ) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) (n : ℕ) :
    ∑ k ∈ Finset.range n, (if k ∈ A ∧ Y < k then (k : ℝ) ^ (-β) else 0) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  set Z := max (n : ℝ) Y
  refine le_trans ?_ (tail_Ioc_le A hς hN hβ hY (le_max_right (n : ℝ) Y))
  have e : ∑ k ∈ Finset.range n, (if k ∈ A ∧ Y < k then (k : ℝ) ^ (-β) else 0) =
      ∑ k ∈ (Finset.range n).filter (fun k : ℕ => Y < k),
        (k : ℝ) ^ (-β) * (if k ∈ A then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : k ∈ A <;> by_cases h2 : Y < k <;> simp [h1, h2]
  rw [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ioc]
    refine ⟨(Nat.floor_lt (by linarith)).mpr hk.2, Nat.le_floor ?_⟩
    exact le_trans (by exact_mod_cast hk.1.le) (le_max_left (n : ℝ) Y)
  · intro k _ _
    have : (0 : ℝ) ≤ (k : ℝ) ^ (-β) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    split_ifs <;> simp [this]

lemma tail_summable (A : Set ℕ) {ς : ℝ → ℝ} (hς : Monotone ς)
    (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) {β Y : ℝ} (hβ : 1 < β)
    (hY : 1 ≤ Y) :
    Summable (fun k : ℕ => if k ∈ A ∧ Y < k then (k : ℝ) ^ (-β) else 0) ∧
    ∑' k : ℕ, (if k ∈ A ∧ Y < k then (k : ℝ) ^ (-β) else 0) ≤
      β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β) := by
  have hnn : ∀ k : ℕ, 0 ≤ (if k ∈ A ∧ Y < k then (k : ℝ) ^ (-β) else 0) := fun k => by
    have : (0 : ℝ) ≤ (k : ℝ) ^ (-β) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    split_ifs <;> simp [this]
  exact ⟨summable_of_sum_range_le hnn (tail_partial_le A hς hN hβ hY),
    Real.tsum_le_of_sum_range_le hnn (tail_partial_le A hς hN hβ hY)⟩

lemma AbsorbedHyp.two_le {b : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (h : AbsorbedHyp b A u) :
    ∀ a ∈ A, 2 ≤ a := by
  intro a ha
  have := (h.weight a ha).a_ge
  by_contra hc
  push_neg at hc
  have : (a : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hc
  linarith

/-- The termwise majorant: `2.001 a^{δ-1}` for `a ≤ Y` (bound (ii)) and `2|t| a^{b+δ-2}` for
`a > Y` (bound (iv)). -/
lemma norm_absorbedTerm_le {b : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (h : AbsorbedHyp b A u)
    {δ : ℝ} {s : ℂ} (hσ1 : 1 - δ ≤ s.re) (hσ2 : s.re ≤ 2) (hσ0 : 0 ≤ s.re)
    (ht : 2 ≤ |s.im|) (Y : ℝ) (n : ℕ) :
    ‖absorbedTerm b A u s n‖ ≤
      (if n ∈ A ∧ (n : ℝ) ≤ Y then 2.001 * (n : ℝ) ^ (δ - 1) else 0) +
        2 * |s.im| * (if n ∈ A ∧ Y < n then (n : ℝ) ^ (-(2 - b - δ)) else 0) := by
  unfold absorbedTerm
  by_cases hn : n ∈ A
  · have hw := h.weight n hn
    have hn1 : (1 : ℝ) ≤ n := by have := hw.a_ge; linarith
    have hn0 : (0 : ℝ) < n := by linarith
    rw [if_pos hn, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hp0 : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg hn0.le _
    by_cases hY : (n : ℝ) ≤ Y
    · rw [if_pos ⟨hn, hY⟩, if_neg (by intro h'; linarith [h'.2])]
      have hw1 := (hw.norm_weight_le hσ0 hσ2)
      have hε := hw.eps_le
      have h1w : ‖1 - Weights.weight b n (u n) s‖ ≤ 2.001 := by
        have := norm_sub_le (1 : ℂ) (Weights.weight b n (u n) s)
        rw [norm_one] at this
        have h2 : 1.02 * s.re * (n : ℝ) ^ (b - 1) ≤ 0.001 := by
          have := hw.eps_pos
          nlinarith
        linarith [hw1.1, hw1.2]
      have := mul_le_mul hpow h1w (norm_nonneg _) (Real.rpow_nonneg hn0.le _)
      linarith
    · push_neg at hY
      rw [if_neg (by intro h'; linarith [h'.2]), if_pos ⟨hn, hY⟩, zero_add]
      have h1w := hw.norm_one_sub_weight_le' hσ0 hσ2 ht
      calc (n : ℝ) ^ (-s.re) * ‖1 - Weights.weight b n (u n) s‖ ≤
            (n : ℝ) ^ (δ - 1) * (2 * |s.im| * (n : ℝ) ^ (b - 1)) :=
            mul_le_mul hpow h1w (norm_nonneg _) (Real.rpow_nonneg hn0.le _)
        _ = 2 * |s.im| * ((n : ℝ) ^ (δ - 1) * (n : ℝ) ^ (b - 1)) := by ring
        _ = 2 * |s.im| * (n : ℝ) ^ (-(2 - b - δ)) := by
            rw [← Real.rpow_add hn0]; ring_nf
  · rw [if_neg hn, if_neg (by tauto), if_neg (by tauto)]; simp

/-- **Lemma 4.4(a), analytic estimate.** For `1 - δ ≤ σ ≤ 2`, `|t| ≥ 2`, `0 ≤ δ ≤ 1/100`, and
`Y = |t|^{1/(1-b)}`: the series `Ê_A(s)` converges absolutely and
`|Ê_A(s)| ≤ absorbedBound ς δ Y`. -/
theorem norm_absorbedHat_le {b : ℝ} {A : Set ℕ} {u : ℕ → ℝ} (h : AbsorbedHyp b A u)
    {ς : ℝ → ℝ} (hς : Monotone ς) (hN : ∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x)))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100) {s : ℂ} (hσ1 : 1 - δ ≤ s.re) (hσ2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) :
    Summable (fun n => ‖absorbedTerm b A u s n‖) ∧
    ‖absorbedHat b A u s‖ ≤ absorbedBound ς δ (|s.im| ^ (1 / (1 - b))) := by
  have hb0 := h.b_pos
  have hb := h.b_le
  set Y := |s.im| ^ (1 / (1 - b)) with hYdef
  have hσ0 : 0 ≤ s.re := by linarith
  have ht0 : 0 < |s.im| := by linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith) (by rw [one_div]; apply inv_nonneg.mpr; linarith)
  have hY0 : 0 < Y := by linarith
  have hYt : Y ^ (1 - b) = |s.im| := by
    rw [hYdef, ← Real.rpow_mul ht0.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
  set β := 2 - b - δ with hβdef
  have hβ : 1 < β := by linarith
  -- the majorant
  set gH : ℕ → ℝ := fun n => if n ∈ A ∧ (n : ℝ) ≤ Y then 2.001 * (n : ℝ) ^ (δ - 1) else 0
  set gT : ℕ → ℝ := fun n => if n ∈ A ∧ Y < n then (n : ℝ) ^ (-β) else 0
  have hgH : HasSum gH (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, gH k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    simp only [Finset.mem_Icc, zero_le, true_and, not_le] at hk
    simp only [gH]
    rw [if_neg]
    rintro ⟨_, hkY⟩
    have := (Nat.floor_lt hY0.le).mp hk
    linarith
  have hgHsum : ∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, gH k =
      2.001 * ∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, (if k ∈ A then (k : ℝ) ^ (δ - 1) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc, zero_le, true_and] at hk
    have hkY : (k : ℝ) ≤ Y := (Nat.le_floor_iff hY0.le).mp hk
    simp only [gH, hkY, and_true]
    split_ifs <;> simp
  obtain ⟨hTs, hTle⟩ := tail_summable A hς hN hβ hY1
  have hg : HasSum (fun n => gH n + 2 * |s.im| * gT n)
      (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, gH k + 2 * |s.im| * ∑' n, gT n) :=
    hgH.add (hTs.hasSum.mul_left _)
  have hbound : ∀ n, ‖absorbedTerm b A u s n‖ ≤ gH n + 2 * |s.im| * gT n :=
    norm_absorbedTerm_le h hσ1 hσ2 hσ0 ht Y
  refine ⟨Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hg.summable, ?_⟩
  refine (tsum_of_norm_bounded hg hbound).trans ?_
  rw [hgHsum]
  have hHead := head_sum_le A h.two_le hς hN hδ0 (by linarith) hY1
  have hC : 0 ≤ Real.exp (-ς (Real.log Y)) := (Real.exp_pos _).le
  have hTail : 2 * |s.im| * ∑' n, gT n ≤ 5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by
    have h1 : 2 * |s.im| * ∑' n, gT n ≤
        2 * |s.im| * (β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β)) :=
      mul_le_mul_of_nonneg_left hTle (by positivity)
    have h2 : |s.im| * Y ^ (1 - β) = Y ^ δ := by
      rw [← hYt, ← Real.rpow_add hY0]; congr 1; rw [hβdef]; ring
    have h3 : β / (β - 1) ≤ 2.7 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hYd : 0 ≤ Y ^ δ := Real.rpow_nonneg hY0.le _
    calc 2 * |s.im| * ∑' n, gT n ≤
        2 * |s.im| * (β / (β - 1) * Real.exp (-ς (Real.log Y)) * Y ^ (1 - β)) := h1
      _ = 2 * (β / (β - 1)) * (Real.exp (-ς (Real.log Y)) * (|s.im| * Y ^ (1 - β))) := by ring
      _ = 2 * (β / (β - 1)) * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by rw [h2]; ring
      _ ≤ 2 * 2.7 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by
          gcongr
      _ = 5.4 * (Y ^ δ * Real.exp (-ς (Real.log Y))) := by ring
  unfold absorbedBound
  linarith

/-- A sufficient condition for `absorbedBound` to be small: if `δ v - ς(v) ≤ -K` on
`0 ≤ v ≤ log Y`, then `absorbedBound ς δ Y ≤ (7.401 + 2.001 log Y) e^{-K}`. -/
lemma absorbedBound_le_of_gap {ς : ℝ → ℝ} (hς : Monotone ς) {δ Y K : ℝ} (hY : 1 ≤ Y)
    (hδ : δ < 1)
    (hgap : ∀ v ∈ Icc 0 (Real.log Y), δ * v - ς v ≤ -K) :
    absorbedBound ς δ Y ≤ (7.401 + 2.001 * Real.log Y) * Real.exp (-K) := by
  have hY0 : 0 < Y := by linarith
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have key : ∀ v, 1 ≤ v → v ≤ Y → v ^ δ * Real.exp (-ς (Real.log v)) ≤ Real.exp (-K) := by
    intro v hv1 hvY
    have hv0 : 0 < v := by linarith
    rw [Real.rpow_def_of_pos hv0, ← Real.exp_add, Real.exp_le_exp]
    have := hgap (Real.log v) ⟨Real.log_nonneg hv1, Real.log_le_log hv0 hvY⟩
    linarith
  have h1 := key Y hY le_rfl
  have hint : ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤
      Real.log Y * Real.exp (-K) := by
    have hle : ∫ v in (1 : ℝ)..Y, v ^ (δ - 1) * Real.exp (-ς (Real.log v)) ≤
        ∫ v in (1 : ℝ)..Y, Real.exp (-K) * v⁻¹ := by
      apply intervalIntegral.integral_mono_on hY
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
        refine integrableOn_Ioc_of_bdd (C := Real.exp (-ς 0)) (measurable_rpow_mul_exp hς)
          fun v hv => ?_
        have hv1 : 1 ≤ v := hv.1.le
        rw [abs_of_nonneg (by positivity)]
        have : v ^ (δ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by linarith)
        have : Real.exp (-ς (Real.log v)) ≤ Real.exp (-ς 0) := by
          rw [Real.exp_le_exp]; have := hς (Real.log_nonneg hv1); linarith
        have : 0 ≤ Real.exp (-ς (Real.log v)) := by positivity
        nlinarith
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.inv₀ continuousOn_id
        intro v hv; rw [Set.uIcc_of_le hY] at hv; simp; linarith [hv.1]
      · intro v hv
        have hv0 : 0 < v := by linarith [hv.1]
        have := key v hv.1 hv.2
        rw [Real.rpow_sub hv0, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hv0]
        calc v ^ δ * Real.exp (-ς (Real.log v)) ≤ Real.exp (-K) := this
          _ = Real.exp (-K) * v⁻¹ * v := by field_simp
    refine hle.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hY0, div_one]
    ring
  unfold absorbedBound
  nlinarith [Real.exp_pos (-K)]

end Absorbed

end
