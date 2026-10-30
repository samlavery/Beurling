module

public import Mathlib

/-!
# Hilbert's inequality and the mean value theorem for Dirichlet polynomials

Toward the mean value theorem (19) of Montgomery and Vaughan, used in the proof of Lemma 4.8.

* `hilbert_inequality` : **the Montgomery–Vaughan generalized Hilbert inequality with uniform
  spacing.** If the reals `λ_r` satisfy `|λ_r - λ_s| ≥ δ > 0` for `r ≠ s`, then for all complex
  `x_r`,
  `|∑_{r ≠ s} x_r \bar x_s / (λ_r - λ_s)| ≤ (π/δ) ∑_r |x_r|²`.
* `mean_value_dirichlet` : **the mean value theorem.** For `a_n ∈ ℂ` supported on a finite set
  of integers in `[1, N]`, all `T₀ ∈ ℝ` and `T ∈ ℝ`,
  `|∫_{T₀}^{T₀+T} |∑ a_n n^{-it}|² dt - T ∑ |a_n|²| ≤ 2π N ∑ |a_n|²`.

The proof of Hilbert's inequality is the eigenvector argument of Montgomery and Vaughan. The
form is `x* H x` for the Hermitian matrix `H_{rs} = i/(λ_r - λ_s)`. If `H v = μ v`, then
`|μ|² ∑|v|² = ∑_r |∑_s v_s/(λ_r - λ_s)|²`. Expanding with partial fractions, the cross terms
cancel by the eigenvalue equation. What remains is bounded by
`3 max_s ∑_{r ≠ s} (λ_r - λ_s)^{-2} ≤ 3 · π²/(3δ²)`. So every eigenvalue satisfies `|μ| ≤ π/δ`,
and the spectral theorem gives the inequality. For the mean value theorem, the off-diagonal
terms of `∫|∑ a_n n^{-it}|²` are two Hilbert forms with `λ_n = log n`, whose spacing is at least
`1/N`.

(The weighted form of Montgomery–Vaughan, with `Σ (T + O(n)) |a_n|²`, is not proved here.)
-/

@[expose] public section

open scoped ComplexConjugate
open Finset Complex Matrix MeasureTheory

namespace MeanValue

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The spectral bound for a Hermitian form -/

/-- If every eigenvalue of the Hermitian matrix `A` has absolute value at most `C`, then
`|x* A x| ≤ C ‖x‖²`. -/
lemma hermitian_quad_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {C : ℝ}
    (hC : ∀ j, |hA.eigenvalues j| ≤ C) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ C * ∑ i, ‖x i‖ ^ 2 := by
  set b := hA.eigenvectorBasis
  set X : EuclideanSpace ℂ ι := WithLp.toLp 2 x
  have hX : X.ofLp = x := rfl
  set c : ι → ℂ := fun j => inner ℂ (b j) X
  have hrep : x = ∑ j, c j • (b j).ofLp := by
    have := b.sum_repr' X
    conv_lhs => rw [← hX, ← this]
    simp [c]
  have hAx : A *ᵥ x = ∑ j, (c j * hA.eigenvalues j) • (b j).ofLp := by
    rw [hrep, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, SemigroupAction.mul_smul]
    congr 1
  have hdot : ∀ j, star x ⬝ᵥ (b j).ofLp = conj (c j) := by
    intro j
    simp only [c]
    rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, hX]
    simp [dotProduct_comm]
  have hq : star x ⬝ᵥ (A *ᵥ x) = ∑ j, (hA.eigenvalues j : ℂ) * (‖c j‖ ^ 2 : ℝ) := by
    rw [hAx, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [dotProduct_smul, hdot, smul_eq_mul, Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  have hpars : ∑ j, ‖c j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [b.sum_sq_norm_inner_right X, EuclideanSpace.norm_sq_eq X]
  rw [hq]
  calc ‖∑ j, (hA.eigenvalues j : ℂ) * (‖c j‖ ^ 2 : ℝ)‖
      ≤ ∑ j, ‖(hA.eigenvalues j : ℂ) * (‖c j‖ ^ 2 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ j, C * ‖c j‖ ^ 2 := by
        apply Finset.sum_le_sum; intro j _
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg ‖c j‖)]
        exact mul_le_mul_of_nonneg_right (hC j) (sq_nonneg _)
    _ = C * ∑ i, ‖x i‖ ^ 2 := by rw [← Finset.mul_sum, hpars]

/-! ### The Hilbert kernel -/

/-- `K(r, s) = 1/(λ_r - λ_s)` (zero on the diagonal). -/
noncomputable def hk {α : Type*} (lam : α → ℝ) (r s : α) : ℂ := ((lam r - lam s)⁻¹ : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma hk_self (lam : ι → ℝ) (s : ι) : hk lam s s = 0 := by simp [hk]

omit [Fintype ι] [DecidableEq ι] in
lemma hk_swap (lam : ι → ℝ) (r s : ι) : hk lam s r = - hk lam r s := by
  simp only [hk]; rw [← neg_sub, inv_neg]; push_cast; ring

omit [Fintype ι] [DecidableEq ι] in
lemma hk_conj (lam : ι → ℝ) (r s : ι) : conj (hk lam r s) = hk lam r s := by
  simp [hk, Complex.conj_ofReal]

omit [Fintype ι] in
lemma hk_partial (lam : ι → ℝ) (hinj : Function.Injective lam) {r s t : ι} (hst : s ≠ t) :
    hk lam r s * hk lam r t = hk lam s t * (hk lam r s - hk lam r t) +
      (if r = s then hk lam s t ^ 2 else 0) + (if r = t then hk lam s t ^ 2 else 0) := by
  by_cases hrs : r = s
  · subst hrs; simp [hk_self, hst]; ring
  by_cases hrt : r = t
  · subst hrt; simp [hk_self, hrs, hk_swap lam r s]; ring
  simp only [hrs, hrt, if_false, add_zero]
  have h1 : lam r - lam s ≠ 0 := sub_ne_zero.mpr (fun h => hrs (hinj h))
  have h2 : lam r - lam t ≠ 0 := sub_ne_zero.mpr (fun h => hrt (hinj h))
  have h3 : lam s - lam t ≠ 0 := sub_ne_zero.mpr (fun h => hst (hinj h))
  simp only [hk]
  push_cast
  have h1' : (lam r : ℂ) - lam s ≠ 0 := by exact_mod_cast h1
  have h2' : (lam r : ℂ) - lam t ≠ 0 := by exact_mod_cast h2
  have h3' : (lam s : ℂ) - lam t ≠ 0 := by exact_mod_cast h3
  field_simp
  ring

lemma hk_sum_mul (lam : ι → ℝ) (hinj : Function.Injective lam) (s t : ι) :
    ∑ r, hk lam r s * hk lam r t = hk lam s t * ((∑ r, hk lam r s) - ∑ r, hk lam r t) +
      2 * hk lam s t ^ 2 + (if s = t then ∑ r, hk lam r s ^ 2 else 0) := by
  by_cases hst : s = t
  · subst hst; simp [hk_self, sq]
  rw [Finset.sum_congr rfl (fun r _ => hk_partial lam hinj (r := r) hst)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hst,
    if_false, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- The key identity of the eigenvector argument: if `∑_s v_s/(λ_r - λ_s) = -iμ v_r` for all
`r`, then `∑_r |∑_s v_s/(λ_r - λ_s)|² = ∑_s |v_s|² ∑_r (λ_r - λ_s)^{-2} +
2 ∑_{s,t} (λ_s - λ_t)^{-2} v_s \bar v_t`. -/
lemma quad_identity (lam : ι → ℝ) (hinj : Function.Injective lam) (v : ι → ℂ) (μ : ℝ)
    (hu : ∀ r, ∑ s, hk lam r s * v s = -I * μ * v r) :
    ∑ r, (∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s) =
      ∑ s, v s * conj (v s) * ∑ r, hk lam r s ^ 2 +
        2 * ∑ s, ∑ t, hk lam s t ^ 2 * (v s * conj (v t)) := by
  set c : ι → ℂ := fun s => ∑ r, hk lam r s
  have h1 : ∑ r, (∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s) =
      ∑ s, ∑ t, v s * conj (v t) * ∑ r, hk lam r s * hk lam r t := by
    have : ∀ r, (∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s) =
        ∑ s, ∑ t, v s * conj (v t) * (hk lam r s * hk lam r t) := by
      intro r
      simp only [map_sum, map_mul, hk_conj, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro t _
      ring
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_comm]
  have hA : ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * c s) =
      ∑ s, v s * c s * conj (∑ t, hk lam s t * v t) := by
    apply Finset.sum_congr rfl; intro s _
    simp only [map_sum, map_mul, hk_conj, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _
    ring
  have hB : ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * c t) =
      ∑ t, conj (v t) * c t * ∑ s, hk lam s t * v s := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    ring
  have e2 : ∀ t, ∑ s, hk lam s t * v s = I * μ * v t := by
    intro t
    rw [show (∑ s, hk lam s t * v s) = -(∑ s, hk lam t s * v s) by
      rw [← Finset.sum_neg_distrib]; congr 1; ext s; rw [hk_swap lam t s]; ring, hu t]
    ring
  have hcross : ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * (c s - c t)) = 0 := by
    have e1 : ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * (c s - c t)) =
        ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * c s) -
          ∑ s, ∑ t, v s * conj (v t) * (hk lam s t * c t) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro t _
      ring
    rw [e1, hA, hB]
    simp only [hu, e2, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro s _
    ring
  rw [h1]
  simp only [hk_sum_mul lam hinj, mul_add, Finset.sum_add_distrib]
  rw [hcross, zero_add]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  ring

/-! ### `∑_{r ≠ s} (λ_r - λ_s)^{-2} ≤ π²/(3δ²)` -/

omit [Fintype ι] [DecidableEq ι] in
lemma sum_inv_sq_sep_aux (R : Finset ι) (g : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ r ∈ R, δ ≤ g r) (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → δ ≤ |g r - g r'|) :
    ∑ r ∈ R, (g r)⁻¹ ^ 2 ≤ Real.pi ^ 2 / 6 / δ ^ 2 := by
  set f : ι → ℕ := fun r => ⌊g r / δ⌋₊
  have hf1 : ∀ r ∈ R, 1 ≤ f r := by
    intro r hr
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hδ]; linarith [hg r hr]
  have hfle : ∀ r ∈ R, (f r : ℝ) * δ ≤ g r := by
    intro r hr
    have := Nat.floor_le (div_nonneg (by linarith [hg r hr]) hδ.le : 0 ≤ g r / δ)
    rwa [le_div_iff₀ hδ] at this
  have hinj : Set.InjOn f R := by
    intro r hr r' hr' h
    by_contra hne
    have h1 := hsep r hr r' hr' hne
    have a1 := Nat.floor_le (div_nonneg (by linarith [hg r hr]) hδ.le : 0 ≤ g r / δ)
    have a2 := Nat.lt_floor_add_one (g r / δ)
    have b1 := Nat.floor_le (div_nonneg (by linarith [hg r' hr']) hδ.le : 0 ≤ g r' / δ)
    have b2 := Nat.lt_floor_add_one (g r' / δ)
    simp only [f] at h
    rw [h] at a1 a2
    have : |g r / δ - g r' / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
    linarith
  have hterm : ∀ r ∈ R, (g r)⁻¹ ^ 2 ≤ 1 / (f r : ℝ) ^ 2 / δ ^ 2 := by
    intro r hr
    have h1 : (1 : ℝ) ≤ f r := by exact_mod_cast hf1 r hr
    rw [inv_pow, div_div, ← mul_pow]
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (hfle r hr) 2
  calc ∑ r ∈ R, (g r)⁻¹ ^ 2 ≤ ∑ r ∈ R, 1 / (f r : ℝ) ^ 2 / δ ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ n ∈ R.image f, 1 / (n : ℝ) ^ 2) / δ ^ 2 := by
        rw [Finset.sum_image hinj, Finset.sum_div]
    _ ≤ (Real.pi ^ 2 / 6) / δ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [← hasSum_zeta_two.tsum_eq]
        exact hasSum_zeta_two.summable.sum_le_tsum _ (fun n _ => by positivity)

omit [DecidableEq ι] in
lemma sum_inv_sq_sep (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |lam r - lam s|) (s : ι) :
    ∑ r, ((lam r - lam s)⁻¹) ^ 2 ≤ Real.pi ^ 2 / 3 / δ ^ 2 := by
  classical
  set R := Finset.univ.filter (fun r => lam s < lam r)
  set L := Finset.univ.filter (fun r => lam r < lam s)
  have hsplit : ∑ r, ((lam r - lam s)⁻¹) ^ 2 =
      ∑ r ∈ R, ((lam r - lam s)⁻¹) ^ 2 + ∑ r ∈ L, ((lam s - lam r)⁻¹) ^ 2 := by
    have h1 : ∑ r, ((lam r - lam s)⁻¹) ^ 2 = ∑ r ∈ R, ((lam r - lam s)⁻¹) ^ 2 +
        ∑ r ∈ Finset.univ.filter (fun r => ¬ lam s < lam r), ((lam r - lam s)⁻¹) ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [h1]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun r => ¬ lam s < lam r))
      (fun r => lam r < lam s)]
    have h2 : ∑ r ∈ (Finset.univ.filter (fun r => ¬ lam s < lam r)).filter
        (fun r => ¬ lam r < lam s), ((lam r - lam s)⁻¹) ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro r hr
      simp only [Finset.mem_filter] at hr
      have : lam r = lam s := by linarith [not_lt.mp hr.1.2, not_lt.mp hr.2]
      simp [this]
    rw [h2, add_zero]
    have h3 : (Finset.univ.filter (fun r => ¬ lam s < lam r)).filter
        (fun r => lam r < lam s) = L := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, L]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨not_lt.mpr h.le, h⟩
    rw [h3]
    apply Finset.sum_congr rfl; intro r _
    rw [← neg_sub, inv_neg, neg_sq]
  have hR := sum_inv_sq_sep_aux R (fun r => lam r - lam s) hδ
    (by
      intro r hr
      simp only [R, Finset.mem_filter] at hr
      have hne : r ≠ s := by rintro rfl; exact lt_irrefl _ hr.2
      have := hsep r s hne
      rwa [abs_of_pos (by linarith [hr.2])] at this)
    (by intro r _ r' _ hne; simp only [sub_sub_sub_cancel_right]; exact hsep r r' hne)
  have hL := sum_inv_sq_sep_aux L (fun r => lam s - lam r) hδ
    (by
      intro r hr
      simp only [L, Finset.mem_filter] at hr
      have hne : r ≠ s := by rintro rfl; exact lt_irrefl _ hr.2
      have := hsep r s hne
      rwa [abs_of_neg (by linarith [hr.2]), neg_sub] at this)
    (by
      intro r _ r' _ hne
      simp only [sub_sub_sub_cancel_left]
      rw [abs_sub_comm]; exact hsep r r' hne)
  rw [hsplit]
  have : Real.pi ^ 2 / 3 / δ ^ 2 = Real.pi ^ 2 / 6 / δ ^ 2 + Real.pi ^ 2 / 6 / δ ^ 2 := by ring
  rw [this]
  exact add_le_add hR hL

/-! ### The eigenvalue bound and Hilbert's inequality -/

/-- Every solution of `∑_s v_s/(λ_r - λ_s) = -iμ v_r` has `μ² ∑|v|² ≤ (π/δ)² ∑|v|²`. -/
lemma eigen_bound (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |lam r - lam s|) (v : ι → ℂ) (μ : ℝ)
    (hu : ∀ r, ∑ s, hk lam r s * v s = -I * μ * v r) :
    μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ (Real.pi / δ) ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
  have hinj : Function.Injective lam := by
    intro r s h; by_contra hne; have := hsep r s hne; rw [h, sub_self, abs_zero] at this; linarith
  set w : ι → ι → ℝ := fun s t => ((lam s - lam t)⁻¹) ^ 2
  have hw_symm : ∀ s t, w s t = w t s := by
    intro s t; simp only [w]; rw [← neg_sub, inv_neg, neg_sq]
  have hk2 : ∀ s t, hk lam s t ^ 2 = (w s t : ℂ) := by intro s t; simp [hk, w]
  have hS : ∀ s, ∑ r, w r s ≤ Real.pi ^ 2 / 3 / δ ^ 2 := fun s => sum_inv_sq_sep lam hδ hsep s
  have hq := quad_identity lam hinj v μ hu
  simp only [hu, hk2] at hq
  have hre := congrArg Complex.re hq
  have hL : (∑ r, -I * μ * v r * conj (-I * μ * v r)).re = μ ^ 2 * ∑ r, ‖v r‖ ^ 2 := by
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  have hR1 : (∑ s, v s * conj (v s) * ((∑ r, (w r s : ℂ)))).re =
      ∑ s, ‖v s‖ ^ 2 * ∑ r, w r s := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  have hR2 : (2 * ∑ s, ∑ t, (w s t : ℂ) * (v s * conj (v t))).re ≤
      2 * ∑ s, ‖v s‖ ^ 2 * ∑ r, w r s := by
    have h1 : (2 * ∑ s, ∑ t, (w s t : ℂ) * (v s * conj (v t))).re =
        2 * ∑ s, ∑ t, w s t * (v s * conj (v t)).re := by
      simp [Complex.re_sum, Complex.mul_re]
    rw [h1]
    have h2 : ∀ s t, w s t * (v s * conj (v t)).re ≤
        w s t * ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) := by
      intro s t
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have := Complex.re_le_norm (v s * conj (v t))
      rw [norm_mul, Complex.norm_conj] at this
      nlinarith [sq_nonneg (‖v s‖ - ‖v t‖)]
    have h3 : ∑ s, ∑ t, w s t * ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) =
        ∑ s, ‖v s‖ ^ 2 * ∑ r, w r s := by
      have e : ∀ s t, w s t * ((‖v s‖ ^ 2 + ‖v t‖ ^ 2) / 2) =
          w s t * ‖v s‖ ^ 2 / 2 + w s t * ‖v t‖ ^ 2 / 2 := by intro s t; ring
      simp only [e, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun s t => w s t * ‖v t‖ ^ 2 / 2)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _
      rw [hw_symm t s]; ring
    have := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
      Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h2 s t))
    linarith
  rw [Complex.add_re] at hre
  have hmain : μ ^ 2 * ∑ r, ‖v r‖ ^ 2 ≤ 3 * ∑ s, ‖v s‖ ^ 2 * ∑ r, w r s := by
    linarith
  have hfin : ∑ s, ‖v s‖ ^ 2 * ∑ r, w r s ≤ ∑ s, ‖v s‖ ^ 2 * (Real.pi ^ 2 / 3 / δ ^ 2) :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hS s) (sq_nonneg _))
  rw [← Finset.sum_mul] at hfin
  have : (Real.pi / δ) ^ 2 * ∑ r, ‖v r‖ ^ 2 =
      3 * ((∑ s, ‖v s‖ ^ 2) * (Real.pi ^ 2 / 3 / δ ^ 2)) := by
    field_simp
  rw [this]
  linarith

/-- **Hilbert's inequality (Montgomery–Vaughan, uniform spacing).** If `|λ_r - λ_s| ≥ δ > 0`
for `r ≠ s`, then `|∑_{r ≠ s} x_r \bar x_s/(λ_r - λ_s)| ≤ (π/δ) ∑ |x_r|²`. -/
theorem hilbert_inequality (lam : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |lam r - lam s|) (x : ι → ℂ) :
    ‖∑ r, ∑ s, x r * conj (x s) * hk lam r s‖ ≤ Real.pi / δ * ∑ r, ‖x r‖ ^ 2 := by
  set H : Matrix ι ι ℂ := fun r s => I * hk lam r s
  have hH : H.IsHermitian := by
    ext r s
    rw [Matrix.conjTranspose_apply]
    simp only [H, star_mul', Complex.star_def, Complex.conj_I,
      hk_conj, hk_swap lam s r]
    ring
  have heig : ∀ j, |hH.eigenvalues j| ≤ Real.pi / δ := by
    intro j
    set v := (hH.eigenvectorBasis j).ofLp
    have hv := hH.mulVec_eigenvectorBasis j
    have hu : ∀ r, ∑ s, hk lam r s * v s = -I * (hH.eigenvalues j : ℝ) * v r := by
      intro r
      have := congrFun hv r
      simp only [Matrix.mulVec, dotProduct, H, Pi.smul_apply, Complex.real_smul] at this
      have e : ∑ s, hk lam r s * v s = -I * ∑ s, I * hk lam r s * v s := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _
        ring_nf; rw [Complex.I_sq]; ring
      rw [e, this]; ring
    have hb := eigen_bound lam hδ hsep v _ hu
    have hn : ∑ r, ‖v r‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, (hH.eigenvectorBasis).orthonormal.1 j, one_pow]
    rw [hn, mul_one, mul_one] at hb
    have := sq_le_sq.mp hb
    rwa [abs_of_pos (div_pos Real.pi_pos hδ)] at this
  have hq := hermitian_quad_le hH heig x
  have e : star x ⬝ᵥ (H *ᵥ x) = -I * ∑ r, ∑ s, x r * conj (x s) * hk lam r s := by
    simp only [Matrix.mulVec, dotProduct, H, Pi.star_apply, Complex.star_def, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    rw [hk_swap lam s r]; ring
  rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul] at hq
  exact hq

/-- Hilbert's inequality for a family indexed by a finset. -/
theorem hilbert_inequality_finset {α : Type*} [DecidableEq α] (S : Finset α) (lam : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |lam r - lam s|) (x : α → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S, x r * conj (x s) * hk lam r s‖ ≤ Real.pi / δ * ∑ r ∈ S, ‖x r‖ ^ 2 := by
  have := hilbert_inequality (ι := S) (fun r => lam r) hδ
    (fun r s hrs => hsep r r.2 s s.2 (fun h => hrs (Subtype.ext h))) (fun r => x r)
  have e1 : ∑ r : S, ∑ s : S, x r * conj (x s) * hk (fun r : S => lam r) r s =
      ∑ r ∈ S, ∑ s ∈ S, x r * conj (x s) * hk lam r s := by
    rw [← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl; intro r _
    rw [← Finset.sum_coe_sort S]
    rfl
  have e2 : ∑ r : S, ‖x r‖ ^ 2 = ∑ r ∈ S, ‖x r‖ ^ 2 := Finset.sum_coe_sort S (fun r => ‖x r‖ ^ 2)
  rw [e1, e2] at this
  exact this

/-! ### The mean value theorem -/

/-- `∫_{T₀}^{T₁} e^{-iλt} \overline{e^{-iμt}} dt`. -/
lemma integral_exp_pair (l m T₀ T₁ : ℝ) :
    ∫ t in T₀..T₁, cexp (-I * t * l) * conj (cexp (-I * t * m)) =
      (if l = m then ((T₁ - T₀ : ℝ) : ℂ) else 0) +
        I * ((l - m)⁻¹ : ℝ) * (cexp (-I * T₁ * l) * conj (cexp (-I * T₁ * m)) -
          cexp (-I * T₀ * l) * conj (cexp (-I * T₀ * m))) := by
  have e : ∀ t : ℝ, cexp (-I * t * l) * conj (cexp (-I * t * m)) =
      cexp ((-I * (l - m)) * t) := by
    intro t
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [e]
  by_cases hlm : l = m
  · subst hlm; simp
  · rw [if_neg hlm, zero_add, integral_exp_mul_complex]
    · have h1 : (l : ℂ) - m ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hlm
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    · have h1 : (l : ℂ) - m ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hlm
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) h1

/-- `|log m - log n| ≥ 1/N` for distinct `m, n ∈ [1, N]`. -/
lemma log_sep {N m n : ℕ} (hm : 1 ≤ m ∧ m ≤ N) (hn : 1 ≤ n ∧ n ≤ N) (hmn : m ≠ n) :
    1 / (N : ℝ) ≤ |Real.log m - Real.log n| := by
  wlog h : m < n generalizing m n
  · rw [abs_sub_comm]; exact this hn hm (Ne.symm hmn) (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
  rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.log_le_log hm0 (by linarith : (m:ℝ) ≤ n)]),
    ← Real.log_div hn0.ne' hm0.ne']
  have := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hm0)
  rw [inv_div] at this
  have h2 : 1 / (N : ℝ) ≤ 1 - m / n := by
    rw [one_sub_div hn0.ne', div_le_div_iff₀ (by linarith) hn0]
    nlinarith
  linarith

lemma cpow_neg_mul_I {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(t * I)) = cexp (-I * t * Real.log n) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : n ≠ 0)),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1; ring

/-- The integral of `|∑ a_n e^{-it log n}|²` as diagonal plus two Hilbert forms. -/
lemma integral_sq_eq (S : Finset ℕ) {N : ℕ} (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N) (a : ℕ → ℂ)
    (T₀ T : ℝ) (e : ℕ → ℝ → ℂ) (he : e = fun (n : ℕ) (t : ℝ) => cexp (-I * t * Real.log n))
    (Q : ℝ → ℂ) (hQ : Q = fun t => ∑ m ∈ S, ∑ n ∈ S, (a m * e m t) * conj (a n * e n t) *
      hk (fun k : ℕ => Real.log k) m n) :
    ((∫ t in T₀..T₀ + T, ‖∑ n ∈ S, a n * e n t‖ ^ 2 : ℝ) : ℂ) =
      (T : ℂ) * ∑ n ∈ S, ((‖a n‖ ^ 2 : ℝ) : ℂ) + I * (Q (T₀ + T) - Q T₀) := by
  have hcont : ∀ m n : ℕ, Continuous (fun t : ℝ => e m t * conj (e n t)) := by
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
  have h2 : ∀ m n : ℕ, ∫ t in T₀..T₀ + T, a m * conj (a n) * (e m t * conj (e n t)) =
      a m * conj (a n) * ((if Real.log m = Real.log n then (T : ℂ) else 0) +
        I * hk (fun k : ℕ => Real.log k) m n * (e m (T₀ + T) * conj (e n (T₀ + T)) -
          e m T₀ * conj (e n T₀))) := by
    intro m n
    rw [intervalIntegral.integral_const_mul]
    congr 1
    subst he
    rw [integral_exp_pair]
    simp only [hk, add_sub_cancel_left]
  simp only [h2]
  have hlog : ∀ m ∈ S, ∀ n ∈ S, (Real.log m = Real.log n ↔ m = n) := by
    intro m hm n hn
    constructor
    · intro h
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast (hS m hm).1 : (0:ℝ) < m))
        (Set.mem_Ioi.mpr (by exact_mod_cast (hS n hn).1 : (0:ℝ) < n)) h
      exact_mod_cast this
    · rintro rfl; rfl
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

/-- **The mean value theorem for Dirichlet polynomials.** For coefficients `a_n` supported on a
finite set `S ⊆ [1, N]`, and all real `T₀`, `T`:
`|∫_{T₀}^{T₀+T} |∑_{n ∈ S} a_n n^{-it}|² dt - T ∑ |a_n|²| ≤ 2π N ∑ |a_n|²`. -/
theorem mean_value_dirichlet (S : Finset ℕ) {N : ℕ} (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (a : ℕ → ℂ) (T₀ T : ℝ) :
    |(∫ t in T₀..T₀ + T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) -
        T * ∑ n ∈ S, ‖a n‖ ^ 2| ≤ 2 * Real.pi * N * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : S = ∅ := by
      ext n; simp only [Finset.notMem_empty, iff_false]; intro hn; have := hS n hn; omega
    subst this; simp
  set e : ℕ → ℝ → ℂ := fun (n : ℕ) (t : ℝ) => cexp (-I * t * Real.log n) with he_def
  have hF : ∀ t : ℝ, ∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I)) = ∑ n ∈ S, a n * e n t := by
    intro t; apply Finset.sum_congr rfl; intro n hn; rw [cpow_neg_mul_I (hS n hn).1]
  simp only [hF]
  set Q : ℝ → ℂ := fun t => ∑ m ∈ S, ∑ n ∈ S, (a m * e m t) * conj (a n * e n t) *
    hk (fun k : ℕ => Real.log k) m n with hQ_def
  have he : ∀ n t, ‖e n t‖ = 1 := by
    intro n t
    simp only [e]
    rw [show -I * (t : ℂ) * ((Real.log n : ℝ) : ℂ) = ((-(t * Real.log n) : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hQ : ∀ t, ‖Q t‖ ≤ Real.pi * N * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    intro t
    have hδ : (0 : ℝ) < 1 / N := by positivity
    have := hilbert_inequality_finset S (fun k : ℕ => Real.log k) hδ
      (fun r hr s hs hrs => log_sep (hS r hr) (hS s hs) hrs) (fun n => a n * e n t)
    simp only [norm_mul, he, mul_one] at this
    rw [div_div_eq_mul_div, div_one] at this
    exact this
  have hint := integral_sq_eq S hS a T₀ T e he_def Q hQ_def
  have key : (∫ t in T₀..T₀ + T, ‖∑ n ∈ S, a n * e n t‖ ^ 2) - T * ∑ n ∈ S, ‖a n‖ ^ 2 =
      (I * (Q (T₀ + T) - Q T₀)).re := by
    have := congrArg Complex.re hint
    simp only [Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul] at this
    rw [this, ← Complex.ofReal_sum, Complex.ofReal_re]; ring
  rw [key]
  calc |(I * (Q (T₀ + T) - Q T₀)).re| ≤ ‖I * (Q (T₀ + T) - Q T₀)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Q (T₀ + T)‖ + ‖Q T₀‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
    _ ≤ _ := by linarith [hQ (T₀ + T), hQ T₀]

end MeanValue

end
