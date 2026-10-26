module

public import RequestProject.Beurling.MeanValue

/-!
# Mean values of generalised Dirichlet polynomials (proof of Lemma 4.8(ii), the sum `S`)

* `integral_sq_eq_gen` / `mean_value_real` : the mean value theorem (19) for arbitrary real
  frequencies with uniform spacing `δ`:
  `|∫_{T₀}^{T₀+T} |∑ b_r e^{-iλ_r t}|² dt - T ∑ |b_r|²| ≤ (2π/δ) ∑ |b_r|²`.
* `block_mean_square` : the block estimate in the proof of Lemma 4.8(ii). If the reals
  `n_0 ≤ n_1 ≤ … ≤ n_{m-1}` lie in `(N, 2N]` and every window `[u, u+2]` contains at most `K` of
  them, then for all real `σ`, `T₀` and `T ≥ 0`,
  `∫_{T₀}^{T₀+T} |∑_i n_i^{-σ-it}|² dt ≤ K (T + 2π(N+1)) ∑_i n_i^{-2σ}`.
  (The paper has `3π` in place of `2π`.) The proof splits the list into `K` classes by the index
  modulo `K`, applies the mean value theorem to each class, and uses Cauchy–Schwarz.
-/

@[expose] public section

open scoped ComplexConjugate
open Finset Complex MeasureTheory

namespace MeanValue

/-- The integral of `|∑ a_r e^{-iλ_r t}|²` as diagonal plus two Hilbert forms, for arbitrary
real frequencies `λ` that are injective on `S`. -/
lemma integral_sq_eq_gen {α : Type*} [DecidableEq α] (S : Finset α) (lam : α → ℝ)
    (hinj : Set.InjOn lam S) (a : α → ℂ)
    (T₀ T : ℝ) (e : α → ℝ → ℂ) (he : e = fun (n : α) (t : ℝ) => cexp (-I * t * lam n))
    (Q : ℝ → ℂ) (hQ : Q = fun t => ∑ m ∈ S, ∑ n ∈ S, (a m * e m t) * conj (a n * e n t) *
      hk lam m n) :
    ((∫ t in T₀..T₀ + T, ‖∑ n ∈ S, a n * e n t‖ ^ 2 : ℝ) : ℂ) =
      (T : ℂ) * ∑ n ∈ S, ((‖a n‖ ^ 2 : ℝ) : ℂ) + I * (Q (T₀ + T) - Q T₀) := by
  have hcont : ∀ m n : α, Continuous (fun t : ℝ => e m t * conj (e n t)) := by
    intro m n; subst he; fun_prop
  have h1 : ∀ t : ℝ, ((‖∑ n ∈ S, a n * e n t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, a m * conj (a n) * (e m t * conj (e n t)) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [map_mul]; ring
  rw [← intervalIntegral.integral_ofReal]
  simp only [h1]
  rw [intervalIntegral.integral_finset_sum (fun m _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finset_sum _ (fun n _ => continuous_const.mul (hcont m n)))]
  rw [Finset.sum_congr rfl (fun m _ => intervalIntegral.integral_finset_sum (μ := volume)
    (a := T₀) (b := T₀ + T) (f := fun n t => a m * conj (a n) * (e m t * conj (e n t)))
    (fun n _ => ((continuous_const.mul (hcont m n)).intervalIntegrable _ _)))]
  have h2 : ∀ m n : α, ∫ t in T₀..T₀ + T, a m * conj (a n) * (e m t * conj (e n t)) =
      a m * conj (a n) * ((if lam m = lam n then (T : ℂ) else 0) +
        I * hk lam m n * (e m (T₀ + T) * conj (e n (T₀ + T)) -
          e m T₀ * conj (e n T₀))) := by
    intro m n
    rw [intervalIntegral.integral_const_mul]
    congr 1
    subst he
    rw [integral_exp_pair]
    simp only [hk, add_sub_cancel_left]
  simp only [h2]
  have hlog : ∀ m ∈ S, ∀ n ∈ S, (lam m = lam n ↔ m = n) := by
    intro m hm n hn
    exact ⟨fun h => hinj hm hn h, fun h => h ▸ rfl⟩
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.sum_congr rfl (fun n hn => by rw [if_congr (hlog m hm n hn) rfl rfl])]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hm, if_true]
    rw [Complex.ofReal_pow, ← Complex.mul_conj']; ring
  · subst hQ
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro n _
      simp only [map_mul]; ring
    · apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro n _
      simp only [map_mul]; ring

/-- **The mean value theorem (19) with uniform spacing**, for arbitrary real frequencies:
if `|λ_r - λ_s| ≥ δ > 0` for distinct `r, s ∈ S`, then
`|∫_{T₀}^{T₀+T} |∑_{r ∈ S} b_r e^{-iλ_r t}|² dt - T ∑ |b_r|²| ≤ (2π/δ) ∑ |b_r|²`. -/
theorem mean_value_real {α : Type*} [DecidableEq α] (S : Finset α) (lam : α → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) (b : α → ℂ)
    (T₀ T : ℝ) :
    |(∫ t in T₀..T₀ + T, ‖∑ r ∈ S, b r * cexp (-I * t * lam r)‖ ^ 2) -
        T * ∑ r ∈ S, ‖b r‖ ^ 2| ≤ 2 * Real.pi / δ * ∑ r ∈ S, ‖b r‖ ^ 2 := by
  have hinj : Set.InjOn lam S := by
    intro r hr s hs h
    by_contra hrs
    have := hsep r hr s hs hrs
    rw [h, sub_self, abs_zero] at this
    linarith
  set e : α → ℝ → ℂ := fun (n : α) (t : ℝ) => cexp (-I * t * lam n) with he_def
  set Q : ℝ → ℂ := fun t => ∑ m ∈ S, ∑ n ∈ S, (b m * e m t) * conj (b n * e n t) *
    hk lam m n with hQ_def
  have he : ∀ n t, ‖e n t‖ = 1 := by
    intro n t
    simp only [e]
    rw [show -I * (t : ℂ) * ((lam n : ℝ) : ℂ) = ((-(t * lam n) : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hQ : ∀ t, ‖Q t‖ ≤ Real.pi / δ * ∑ n ∈ S, ‖b n‖ ^ 2 := by
    intro t
    have := hilbert_inequality_finset S lam hδ hsep (fun n => b n * e n t)
    simp only [norm_mul, he, mul_one] at this
    exact this
  have hint := integral_sq_eq_gen S lam hinj b T₀ T e he_def Q hQ_def
  have key : (∫ t in T₀..T₀ + T, ‖∑ n ∈ S, b n * e n t‖ ^ 2) - T * ∑ n ∈ S, ‖b n‖ ^ 2 =
      (I * (Q (T₀ + T) - Q T₀)).re := by
    have := congrArg Complex.re hint
    simp only [Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul] at this
    rw [this, ← Complex.ofReal_sum, Complex.ofReal_re]; ring
  rw [key]
  calc |(I * (Q (T₀ + T) - Q T₀)).re| ≤ ‖I * (Q (T₀ + T) - Q T₀)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Q (T₀ + T)‖ + ‖Q T₀‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
    _ ≤ _ := by rw [mul_div_assoc] at *; linarith [hQ (T₀ + T), hQ T₀]

/-! ### The block estimate -/

/-- Elements of one residue class (index modulo `K`) are more than `2` apart. -/
lemma class_gap {m K : ℕ} {n : Fin m → ℝ} (hmono : Monotone n)
    {i j : Fin m} (hwin : (univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card ≤ K)
    (hij : i < j) (hc : i.val % K = j.val % K) : n i + 2 < n j := by
  by_contra h
  push_neg at h
  have hK : i.val + K ≤ j.val := by
    have h1 : K ∣ j.val - i.val := (Nat.modEq_iff_dvd' hij.le).mp hc
    have h2 : 0 < j.val - i.val := by omega
    have := Nat.le_of_dvd h2 h1
    omega
  have hsub : (univ.filter (fun k : Fin m => i ≤ k ∧ k ≤ j)) ⊆
      univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2) := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact ⟨hmono hk.1, (hmono hk.2).trans h⟩
  have hcard : (univ.filter (fun k : Fin m => i ≤ k ∧ k ≤ j)).card = j.val - i.val + 1 := by
    have : (univ.filter (fun k : Fin m => i ≤ k ∧ k ≤ j)) = Finset.Icc i j := by
      ext k; simp
    rw [this, Fin.card_Icc]; omega
  have := (card_le_card hsub).trans hwin
  omega

/-- A gap of more than `2` in `(N, 2N]` gives a gap of at least `1/(N+1)` between logarithms. -/
lemma log_gap {N x y : ℝ} (hN : 0 < N) (hx : N < x) (hx2 : x ≤ 2 * N) (hxy : x + 2 < y) :
    1 / (N + 1) ≤ Real.log y - Real.log x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [← Real.log_div hy0.ne' hx0.ne']
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hx0)
  rw [inv_div] at h
  refine le_trans ?_ h
  rw [one_sub_div hy0.ne', div_le_div_iff₀ (by linarith) hy0]
  nlinarith

lemma cpow_real_eq {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    ((x : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ((x ^ (-σ) : ℝ) : ℂ) * cexp (-I * t * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_cpow hx.le,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1; push_cast; ring

/-- **The block estimate in the proof of Lemma 4.8(ii).** Let `n_0 ≤ … ≤ n_{m-1}` be a list of
reals (repetitions allowed, i.e. counted with multiplicity), and let `s` be a set of indices whose
values lie in `(N, 2N]`, such that for every `i ∈ s` the window `[n_i, n_i + 2]` contains at most
`K ≥ 1` elements of the list. Then for all real `σ`, `T₀` and `T ≥ 0`,
`∫_{T₀}^{T₀+T} |∑_{i ∈ s} n_i^{-σ-it}|² dt ≤ K (T + 2π(N+1)) ∑_{i ∈ s} n_i^{-2σ}`. -/
theorem block_mean_square {m K : ℕ} (hK : 0 < K) {N : ℝ} (hN : 0 < N) {n : Fin m → ℝ}
    (hmono : Monotone n) (s : Finset (Fin m)) (hrange : ∀ i ∈ s, N < n i ∧ n i ≤ 2 * N)
    (hwin : ∀ i ∈ s, (univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card ≤ K)
    (σ T₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in T₀..T₀ + T, ‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 ≤
      K * (T + 2 * Real.pi * (N + 1)) * ∑ i ∈ s, n i ^ (-2 * σ) := by
  have hn0 : ∀ i ∈ s, 0 < n i := fun i hi => by linarith [(hrange i hi).1]
  set b : Fin m → ℂ := fun i => ((n i ^ (-σ) : ℝ) : ℂ) with hb
  set lam : Fin m → ℝ := fun i => Real.log (n i) with hlam
  set cls : ℕ → Finset (Fin m) := fun c => s.filter (fun i : Fin m => i.val % K = c)
  set Sc : ℕ → ℝ → ℂ := fun c t => ∑ i ∈ cls c, b i * cexp (-I * t * lam i) with hSc
  have hterm : ∀ (t : ℝ), ∀ i ∈ s,
      ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) = b i * cexp (-I * t * lam i) :=
    fun t i hi => cpow_real_eq (hn0 i hi) σ t
  have hsum_eq : ∀ t : ℝ, ∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ∑ i ∈ s, b i * cexp (-I * t * lam i) := fun t => Finset.sum_congr rfl (hterm t)
  have hsplit : ∀ t : ℝ, ∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ∑ c ∈ range K, Sc c t := by
    intro t
    rw [hsum_eq]
    simp only [hSc, cls]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun i : Fin m => i.val % K)
      (fun i _ => mem_range.mpr (Nat.mod_lt _ hK))]
  have hbn : ∀ i ∈ s, ‖b i‖ ^ 2 = n i ^ (-2 * σ) := by
    intro i hi
    rw [hb, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hn0 i hi).le _),
      ← Real.rpow_natCast, ← Real.rpow_mul (hn0 i hi).le]
    congr 1; push_cast; ring
  have hpt : ∀ t : ℝ, ‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 ≤
      K * ∑ c ∈ range K, ‖Sc c t‖ ^ 2 := by
    intro t
    rw [hsplit]
    calc ‖∑ c ∈ range K, Sc c t‖ ^ 2 ≤ (∑ c ∈ range K, ‖Sc c t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (range K).card * ∑ c ∈ range K, ‖Sc c t‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = K * ∑ c ∈ range K, ‖Sc c t‖ ^ 2 := by rw [card_range]
  have hcontS : ∀ c, Continuous fun t : ℝ => ‖Sc c t‖ ^ 2 := by
    intro c; simp only [hSc]; fun_prop
  have hδ : (0 : ℝ) < 1 / (N + 1) := by positivity
  have hclass : ∀ c, ∫ t in T₀..T₀ + T, ‖Sc c t‖ ^ 2 ≤
      (T + 2 * Real.pi * (N + 1)) * ∑ i ∈ cls c, n i ^ (-2 * σ) := by
    intro c
    have hsep : ∀ r ∈ cls c, ∀ q ∈ cls c, r ≠ q → 1 / (N + 1) ≤ |lam r - lam q| := by
      intro r hr q hq hrq
      simp only [cls, mem_filter] at hr hq
      rcases lt_or_gt_of_ne hrq with h | h
      · have := log_gap hN (hrange r hr.1).1 (hrange r hr.1).2
          (class_gap hmono (hwin r hr.1) h (hr.2.trans hq.2.symm))
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact this
      · have := log_gap hN (hrange q hq.1).1 (hrange q hq.1).2
          (class_gap hmono (hwin q hq.1) h (hq.2.trans hr.2.symm))
        rw [abs_of_nonneg (by linarith)]; exact this
    have hmv := mean_value_real (cls c) lam hδ hsep b T₀ T
    rw [div_div_eq_mul_div, div_one] at hmv
    have h := (abs_le.mp hmv).2
    rw [Finset.sum_congr rfl (fun i hi => hbn i (mem_filter.mp hi).1)] at h
    simp only [hSc]
    linarith
  calc ∫ t in T₀..T₀ + T, ‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2
      ≤ ∫ t in T₀..T₀ + T, (K : ℝ) * ∑ c ∈ range K, ‖Sc c t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · apply Continuous.intervalIntegrable
          simp only [hsum_eq]; fun_prop
        · apply Continuous.intervalIntegrable
          exact continuous_const.mul (continuous_finset_sum _ fun c _ => hcontS c)
        · intro t _; exact hpt t
    _ = K * ∑ c ∈ range K, ∫ t in T₀..T₀ + T, ‖Sc c t‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum
          (fun c _ => (hcontS c).intervalIntegrable _ _)]
    _ ≤ K * ∑ c ∈ range K, (T + 2 * Real.pi * (N + 1)) * ∑ i ∈ cls c, n i ^ (-2 * σ) := by
        gcongr with c; exact hclass c
    _ = K * (T + 2 * Real.pi * (N + 1)) * ∑ i ∈ s, n i ^ (-2 * σ) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (g := fun i : Fin m => i.val % K)
          (fun i _ => mem_range.mpr (Nat.mod_lt _ hK))]
        ring

end MeanValue

end
