module

public import RequestProject.Beurling.DirichletSum
public import RequestProject.Beurling.Lemma48

/-!
# `L²` norms on the box `Q` (proof of Lemma 4.8(ii))

* `lintegral_box_eq` : Fubini on `Q = [3/4, 5/4] × [a, b]`.
* `box_minkowski` : Minkowski's inequality for the `L²(Q)` norm of a finite sum, in the form
  `∬_Q |∑ g_j|² ≤ (∑ c_j)²` whenever `∬_Q |g_j|² ≤ c_j²`.
* `box_block` : the block estimate integrated over `Q`:
  `∬_Q |∑_i n_i^{-s}|² ≤ (1/2) K (Γ + 1/2 + 2π(N+1)) m N^{-3/2}` for `m` reals in `(N, 2N]`,
  `N ≥ 1`, at most `K` in each window of length `2`.
-/

@[expose] public section

open Complex MeasureTheory Set Finset GoodHeights

namespace GoodHeights

lemma box_eq_preimage (a b : ℝ) :
    box a b = Complex.measurableEquivRealProd ⁻¹' (Icc (3 / 4 : ℝ) (5 / 4) ×ˢ Icc a b) := by
  ext z
  simp only [box, mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
  simp [Complex.measurableEquivRealProd]
  tauto

/-- Fubini on the box `Q = [3/4, 5/4] × [a, b]`. -/
lemma lintegral_box_eq {F : ℂ → ENNReal} (hF : Measurable F) (a b : ℝ) :
    ∫⁻ z in box a b, F z =
      ∫⁻ σ in Icc (3 / 4 : ℝ) (5 / 4), ∫⁻ t in Icc a b, F (σ + t * I) := by
  set e := Complex.measurableEquivRealProd
  have hG : Measurable fun p : ℝ × ℝ => F (p.1 + p.2 * I) := by
    apply hF.comp; fun_prop
  have h1 : ∫⁻ z in box a b, F z = ∫⁻ z in e ⁻¹' (Icc (3 / 4 : ℝ) (5 / 4) ×ˢ Icc a b),
      (fun p : ℝ × ℝ => F (p.1 + p.2 * I)) (e z) := by
    rw [box_eq_preimage]
    congr 1; funext z
    simp [e, Complex.measurableEquivRealProd, Complex.re_add_im]
  rw [h1, Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage
    (measurableSet_Icc.prod measurableSet_Icc) hG]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable]

/-- **Minkowski's inequality on `Q`.** If `∬_Q |g_j|² ≤ c_j²` with `c_j > 0` for each `j` in a
finite set, then `∬_Q |∑_j g_j|² ≤ (∑_j c_j)²`. -/
theorem box_minkowski {ι : Type*} (J : Finset ι) {g : ι → ℂ → ℂ} (hg : ∀ j, Measurable (g j))
    {c : ι → ℝ} (hc : ∀ j ∈ J, 0 < c j) (Q : Set ℂ)
    (hb : ∀ j ∈ J, ∫⁻ z in Q, ENNReal.ofReal (‖g j z‖ ^ 2) ≤ ENNReal.ofReal (c j ^ 2)) :
    ∫⁻ z in Q, ENNReal.ofReal (‖∑ j ∈ J, g j z‖ ^ 2) ≤ ENNReal.ofReal ((∑ j ∈ J, c j) ^ 2) := by
  set C := ∑ j ∈ J, c j
  have hC : 0 ≤ C := Finset.sum_nonneg fun j hj => (hc j hj).le
  have hpt : ∀ z, ENNReal.ofReal (‖∑ j ∈ J, g j z‖ ^ 2) ≤
      ∑ j ∈ J, ENNReal.ofReal (C / c j) * ENNReal.ofReal (‖g j z‖ ^ 2) := by
    intro z
    have h1 : ‖∑ j ∈ J, g j z‖ ^ 2 ≤ C * ∑ j ∈ J, ‖g j z‖ ^ 2 / c j := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq J (fun j => Real.sqrt (c j))
        (fun j => ‖g j z‖ / Real.sqrt (c j))
      have e1 : ∑ j ∈ J, Real.sqrt (c j) * (‖g j z‖ / Real.sqrt (c j)) = ∑ j ∈ J, ‖g j z‖ := by
        apply Finset.sum_congr rfl; intro j hj
        have := Real.sqrt_pos.mpr (hc j hj); field_simp
      have e2 : ∑ j ∈ J, Real.sqrt (c j) ^ 2 = C := by
        apply Finset.sum_congr rfl; intro j hj; exact Real.sq_sqrt (hc j hj).le
      have e3 : ∑ j ∈ J, (‖g j z‖ / Real.sqrt (c j)) ^ 2 = ∑ j ∈ J, ‖g j z‖ ^ 2 / c j := by
        apply Finset.sum_congr rfl; intro j hj; rw [div_pow, Real.sq_sqrt (hc j hj).le]
      rw [e1, e2, e3] at hcs
      calc ‖∑ j ∈ J, g j z‖ ^ 2 ≤ (∑ j ∈ J, ‖g j z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := hcs
    calc ENNReal.ofReal (‖∑ j ∈ J, g j z‖ ^ 2) ≤ ENNReal.ofReal (C * ∑ j ∈ J, ‖g j z‖ ^ 2 / c j) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (∑ j ∈ J, C / c j * ‖g j z‖ ^ 2) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => by
            have := hc j hj; positivity)]
          apply Finset.sum_congr rfl; intro j hj
          rw [ENNReal.ofReal_mul (by have := hc j hj; positivity)]
  have hmeas : ∀ j, Measurable fun z => ENNReal.ofReal (‖g j z‖ ^ 2) := fun j =>
    ENNReal.measurable_ofReal.comp ((hg j).norm.pow_const 2)
  calc ∫⁻ z in Q, ENNReal.ofReal (‖∑ j ∈ J, g j z‖ ^ 2)
      ≤ ∫⁻ z in Q, ∑ j ∈ J, ENNReal.ofReal (C / c j) * ENNReal.ofReal (‖g j z‖ ^ 2) :=
        lintegral_mono hpt
    _ = ∑ j ∈ J, ENNReal.ofReal (C / c j) * ∫⁻ z in Q, ENNReal.ofReal (‖g j z‖ ^ 2) := by
        rw [lintegral_finset_sum _ (fun j _ => (hmeas j).const_mul _)]
        apply Finset.sum_congr rfl; intro j _
        rw [lintegral_const_mul _ (hmeas j)]
    _ ≤ ∑ j ∈ J, ENNReal.ofReal (C / c j) * ENNReal.ofReal (c j ^ 2) := by
        gcongr with j hj; exact hb j hj
    _ = ENNReal.ofReal (∑ j ∈ J, C / c j * c j ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => by have := hc j hj; positivity)]
        apply Finset.sum_congr rfl; intro j hj
        rw [ENNReal.ofReal_mul (by have := hc j hj; positivity)]
    _ = ENNReal.ofReal (C ^ 2) := by
        congr 1
        rw [sq C, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j hj
        have := (hc j hj).ne'; field_simp

/-- **The block estimate on `Q`.** Let `n_0 ≤ … ≤ n_{m-1}` be a list of reals, and `s` a set of
indices with values in `(N, 2N]`, `N ≥ 1`, such that for `i ∈ s` the window `[n_i, n_i + 2]`
contains at most `K ≥ 1` elements of the list. Then for `Γ ≥ 0`:
`∬_Q |∑_{i ∈ s} n_i^{-z}|² ≤ (1/2) K (Γ + 1/2 + 2π(N+1)) |s| N^{-3/2}`, where
`Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`. -/
theorem box_block {m K : ℕ} (hK : 0 < K) {N : ℝ} (hN : 1 ≤ N) {n : Fin m → ℝ}
    (hmono : Monotone n) (s : Finset (Fin m)) (hrange : ∀ i ∈ s, N < n i ∧ n i ≤ 2 * N)
    (hwin : ∀ i ∈ s, (univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card ≤ K)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4),
        ENNReal.ofReal (‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-z)‖ ^ 2) ≤
      ENNReal.ofReal (1 / 2 * (K * (Γ + 1 / 2 + 2 * Real.pi * (N + 1)) *
        (s.card * N ^ (-(3 / 2 : ℝ))))) := by
  have hn0 : ∀ i ∈ s, 0 < n i := fun i hi => by linarith [(hrange i hi).1]
  have hF : Measurable fun z : ℂ => ENNReal.ofReal (‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-z)‖ ^ 2) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    apply Measurable.norm
    refine Finset.measurable_sum _ fun i hi => ?_
    exact (Continuous.measurable (by
      exact continuous_const.cpow continuous_neg (fun _ => Or.inl (by
        simp only [Complex.ofReal_re]; exact hn0 i hi))))
  rw [lintegral_box_eq hF]
  set A : ℝ := K * (Γ + 1 / 2 + 2 * Real.pi * (N + 1)) * (s.card * N ^ (-(3 / 2 : ℝ)))
  have hA : 0 ≤ A := by positivity
  have hinner : ∀ σ ∈ Icc (3 / 4 : ℝ) (5 / 4), ∫⁻ t in Icc (Γ - 1 / 4) (2 * Γ + 1 / 4),
      ENNReal.ofReal (‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2) ≤
        ENNReal.ofReal A := by
    intro σ hσ
    have hcont : Continuous fun t : ℝ =>
        ‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 := by
      have : ∀ t : ℝ, ∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) =
          ∑ i ∈ s, ((n i ^ (-σ) : ℝ) : ℂ) * cexp (-I * t * Real.log (n i)) := fun t =>
        Finset.sum_congr rfl fun i hi => MeanValue.cpow_real_eq (hn0 i hi) σ t
      simp only [this]; fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
      (Filter.Eventually.of_forall fun t => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hb := MeanValue.block_mean_square hK (by linarith) hmono s hrange hwin σ (Γ - 1 / 4)
      (T := Γ + 1 / 2) (by linarith)
    rw [show Γ - 1 / 4 + (Γ + 1 / 2) = 2 * Γ + 1 / 4 by ring] at hb
    refine hb.trans ?_
    have hsum : ∑ i ∈ s, n i ^ (-2 * σ) ≤ s.card * N ^ (-(3 / 2 : ℝ)) := by
      have : ∀ i ∈ s, n i ^ (-2 * σ) ≤ N ^ (-(3 / 2 : ℝ)) := by
        intro i hi
        calc n i ^ (-2 * σ) ≤ N ^ (-2 * σ) :=
              Real.rpow_le_rpow_of_nonpos (by linarith) (hrange i hi).1.le (by linarith [hσ.1])
          _ ≤ N ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith [hσ.1])
      calc ∑ i ∈ s, n i ^ (-2 * σ) ≤ ∑ _i ∈ s, N ^ (-(3 / 2 : ℝ)) := Finset.sum_le_sum this
        _ = _ := by simp
    have : 0 ≤ (K : ℝ) * (Γ + 1 / 2 + 2 * Real.pi * (N + 1)) := by positivity
    exact mul_le_mul_of_nonneg_left hsum this
  calc ∫⁻ σ in Icc (3 / 4 : ℝ) (5 / 4), ∫⁻ t in Icc (Γ - 1 / 4) (2 * Γ + 1 / 4),
        ENNReal.ofReal (‖∑ i ∈ s, ((n i : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2)
      ≤ ∫⁻ σ in Icc (3 / 4 : ℝ) (5 / 4), ENNReal.ofReal A :=
        setLIntegral_mono' measurableSet_Icc hinner
    _ = ENNReal.ofReal (1 / 2 * A) := by
        rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hA]
        congr 1; ring

end GoodHeights

end
