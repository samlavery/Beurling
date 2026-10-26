module

public import RequestProject.Beurling.MeanValue

/-!
# The weighted Hilbert inequality and the mean value theorem `∑ (T + O(n)) |a_n|²`

A weighted form of the eigenvector argument of `MeanValue`. Let `ω_r > 0` be weights and write
`w(r,s) = (λ_r - λ_s)^{-2}` for `r ≠ s`. Suppose that for every `s`,
`2 ω_s ∑_r ω_r w(r,s) + ∑_t ω_t² w(s,t) ≤ M`. Then
`|∑_{r ≠ s} x_r \bar x_s/(λ_r - λ_s)| ≤ √M ∑ |x_r|²/ω_r` (`hilbert_weighted`).

For `λ_n = log n` and `ω_n = 1/n` this holds with `M = 26`. The mean value theorem then follows
in the form of Montgomery and Vaughan (`mean_value_weighted`):
`|∫_{T₀}^{T₀+T} |∑ a_n n^{-it}|² dt - T ∑ |a_n|²| ≤ 2√26 ∑ n |a_n|²`.
-/

@[expose] public section

open scoped ComplexConjugate
open Finset Complex Matrix MeasureTheory

namespace MeanValue

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hk_sum_mul_w (lam : ι → ℝ) (hinj : Function.Injective lam) (ω : ι → ℂ) (s t : ι) :
    ∑ r, ω r * (hk lam r s * hk lam r t) =
      hk lam s t * ((∑ r, ω r * hk lam r s) - ∑ r, ω r * hk lam r t) +
      (ω s + ω t) * hk lam s t ^ 2 + (if s = t then ∑ r, ω r * hk lam r s ^ 2 else 0) := by
  by_cases hst : s = t
  · subst hst; simp [hk_self, sq]
  rw [Finset.sum_congr rfl (fun r _ => by rw [hk_partial lam hinj (r := r) hst])]
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hst, if_false, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
  have h1 : ∑ x, ω x * (hk lam s t * hk lam x s) = ∑ i, hk lam s t * (ω i * hk lam i s) := by
    apply Finset.sum_congr rfl; intro r _; ring
  have h2 : ∑ x, ω x * (hk lam s t * hk lam x t) = ∑ i, hk lam s t * (ω i * hk lam i t) := by
    apply Finset.sum_congr rfl; intro r _; ring
  rw [h1, h2]; ring

/-- The weighted identity of the eigenvector argument. -/
lemma quad_identity_w (lam : ι → ℝ) (hinj : Function.Injective lam) (ω : ι → ℝ)
    (v : ι → ℂ) (μ : ℝ)
    (hu : ∀ r, ∑ s, hk lam r s * v s = -I * μ * v r / ω r) :
    ∑ r, (ω r : ℂ) * ((∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s)) =
      ∑ s, v s * conj (v s) * ∑ r, (ω r : ℂ) * hk lam r s ^ 2 +
        ∑ s, ∑ t, ((ω s : ℂ) + ω t) * hk lam s t ^ 2 * (v s * conj (v t)) := by
  set c : ι → ℂ := fun s => ∑ r, (ω r : ℂ) * hk lam r s
  have h1 : ∑ r, (ω r : ℂ) * ((∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s)) =
      ∑ s, ∑ t, v s * conj (v t) * ∑ r, (ω r : ℂ) * (hk lam r s * hk lam r t) := by
    have : ∀ r, (ω r : ℂ) * ((∑ s, hk lam r s * v s) * conj (∑ s, hk lam r s * v s)) =
        ∑ s, ∑ t, v s * conj (v t) * ((ω r : ℂ) * (hk lam r s * hk lam r t)) := by
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
  have e2 : ∀ t, ∑ s, hk lam s t * v s = I * μ * v t / ω t := by
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
    simp only [hu, e2, map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro s _
    ring
  rw [h1]
  simp only [hk_sum_mul_w lam hinj, mul_add, Finset.sum_add_distrib]
  rw [hcross, zero_add]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

/-- The weighted eigenvalue bound. -/
lemma eigen_bound_w (lam : ι → ℝ) (hinj : Function.Injective lam) (ω : ι → ℝ)
    (hω : ∀ r, 0 < ω r) {M : ℝ}
    (hM : ∀ s, 2 * ω s * (∑ r, ω r * ((lam r - lam s)⁻¹) ^ 2) +
      ∑ t, ω t ^ 2 * ((lam s - lam t)⁻¹) ^ 2 ≤ M)
    (v : ι → ℂ) (μ : ℝ) (hu : ∀ r, ∑ s, hk lam r s * v s = -I * μ * v r / ω r) :
    μ ^ 2 * ∑ r, ‖v r‖ ^ 2 / ω r ≤ M * ∑ r, ‖v r‖ ^ 2 / ω r := by
  set w : ι → ι → ℝ := fun s t => ((lam s - lam t)⁻¹) ^ 2 with hw_def
  have hw_symm : ∀ s t, w s t = w t s := by
    intro s t; simp only [w]; rw [← neg_sub, inv_neg, neg_sq]
  have hw0 : ∀ s t, 0 ≤ w s t := fun s t => sq_nonneg _
  have hk2 : ∀ s t, hk lam s t ^ 2 = (w s t : ℂ) := by intro s t; simp [hk, w]
  set D : ι → ℝ := fun s => ∑ r, ω r * w r s with hD
  set E : ι → ℝ := fun s => ∑ t, ω t ^ 2 * w s t with hE
  have hq := quad_identity_w lam hinj ω v μ hu
  simp only [hu, hk2] at hq
  have hre := congrArg Complex.re hq
  have hL : (∑ r, (ω r : ℂ) * (-I * μ * v r / ω r * conj (-I * μ * v r / ω r))).re =
      μ ^ 2 * ∑ r, ‖v r‖ ^ 2 / ω r := by
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    have hr := (hω r).ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hω r)]
    field_simp
    try rw [sq_abs]
    ring
  have hR1 : (∑ s, v s * conj (v s) * ∑ r, (ω r : ℂ) * (w r s : ℂ)).re =
      ∑ s, ‖v s‖ ^ 2 * D s := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [D, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hR2 : (∑ s, ∑ t, ((ω s : ℂ) + ω t) * (w s t : ℂ) * (v s * conj (v t))).re ≤
      ∑ s, ‖v s‖ ^ 2 / ω s * (ω s * D s + E s) := by
    have h1 : (∑ s, ∑ t, ((ω s : ℂ) + ω t) * (w s t : ℂ) * (v s * conj (v t))).re =
        ∑ s, ∑ t, (ω s + ω t) * w s t * (v s * conj (v t)).re := by
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro t _
      rw [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    rw [h1]
    have h2 : ∀ s t, (ω s + ω t) * w s t * (v s * conj (v t)).re ≤
        (ω s + ω t) * w s t * ((‖v s‖ ^ 2 * (ω t / ω s) + ‖v t‖ ^ 2 * (ω s / ω t)) / 2) := by
      intro s t
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith [hω s, hω t]) (hw0 s t))
      have := Complex.re_le_norm (v s * conj (v t))
      rw [norm_mul, Complex.norm_conj] at this
      have hs := hω s; have ht := hω t
      have e : ‖v s‖ ^ 2 * (ω t / ω s) + ‖v t‖ ^ 2 * (ω s / ω t) - 2 * (‖v s‖ * ‖v t‖) =
          (‖v s‖ * ω t - ‖v t‖ * ω s) ^ 2 / (ω s * ω t) := by
        field_simp; ring
      have : 0 ≤ (‖v s‖ * ω t - ‖v t‖ * ω s) ^ 2 / (ω s * ω t) := by positivity
      linarith
    have h3 : ∑ s, ∑ t, (ω s + ω t) * w s t *
        ((‖v s‖ ^ 2 * (ω t / ω s) + ‖v t‖ ^ 2 * (ω s / ω t)) / 2) =
        ∑ s, ‖v s‖ ^ 2 / ω s * (ω s * D s + E s) := by
      have e1 : ∀ s t, (ω s + ω t) * w s t *
          ((‖v s‖ ^ 2 * (ω t / ω s) + ‖v t‖ ^ 2 * (ω s / ω t)) / 2) =
          (ω s + ω t) * w s t * (‖v s‖ ^ 2 * (ω t / ω s)) / 2 +
            (ω s + ω t) * w s t * (‖v t‖ ^ 2 * (ω s / ω t)) / 2 := by intro s t; ring
      simp only [e1, Finset.sum_add_distrib]
      rw [Finset.sum_comm
        (f := fun s t => (ω s + ω t) * w s t * (‖v t‖ ^ 2 * (ω s / ω t)) / 2)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _
      rw [← Finset.sum_add_distrib, hD, hE]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _
      have hs := (hω s).ne'
      have ht := (hω t).ne'
      rw [hw_symm t s]
      field_simp
      ring
    have := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
      Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => h2 s t))
    linarith
  rw [Complex.add_re] at hre
  have hfin : ∑ s, ‖v s‖ ^ 2 * D s + ∑ s, ‖v s‖ ^ 2 / ω s * (ω s * D s + E s) ≤
      M * ∑ r, ‖v r‖ ^ 2 / ω r := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro s _
    have hs := hω s
    have : ‖v s‖ ^ 2 * D s + ‖v s‖ ^ 2 / ω s * (ω s * D s + E s) =
        ‖v s‖ ^ 2 / ω s * (2 * ω s * D s + E s) := by field_simp; ring
    rw [this, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM s) (by positivity)
  linarith

/-- **The weighted Hilbert inequality.** If `2 ω_s ∑_r ω_r (λ_r - λ_s)^{-2} +
∑_t ω_t² (λ_s - λ_t)^{-2} ≤ M` for every `s` (sums over `r, t ≠ s`), then
`|∑_{r ≠ s} x_r \bar x_s/(λ_r - λ_s)| ≤ √M ∑ |x_r|²/ω_r`. -/
theorem hilbert_weighted (lam : ι → ℝ) (hinj : Function.Injective lam) (ω : ι → ℝ)
    (hω : ∀ r, 0 < ω r) {M : ℝ}
    (hM : ∀ s, 2 * ω s * (∑ r, ω r * ((lam r - lam s)⁻¹) ^ 2) +
      ∑ t, ω t ^ 2 * ((lam s - lam t)⁻¹) ^ 2 ≤ M) (x : ι → ℂ) :
    ‖∑ r, ∑ s, x r * conj (x s) * hk lam r s‖ ≤ Real.sqrt M * ∑ r, ‖x r‖ ^ 2 / ω r := by
  set q : ι → ℝ := fun r => Real.sqrt (ω r)
  have hq0 : ∀ r, 0 < q r := fun r => Real.sqrt_pos.mpr (hω r)
  have hqq : ∀ r, q r * q r = ω r := fun r => Real.mul_self_sqrt (hω r).le
  set H : Matrix ι ι ℂ := fun r s => I * ((q r * q s : ℝ) : ℂ) * hk lam r s
  have hH : H.IsHermitian := by
    ext r s
    simp only [H, Matrix.conjTranspose_apply, star_mul', Complex.star_def, Complex.conj_I,
      hk_conj, hk_swap lam s r, Complex.conj_ofReal]
    push_cast
    ring
  have heig : ∀ j, |hH.eigenvalues j| ≤ Real.sqrt M := by
    intro j
    set v := (hH.eigenvectorBasis j).ofLp
    have hv := hH.mulVec_eigenvectorBasis j
    set x' : ι → ℂ := fun s => (q s : ℂ) * v s
    have hu : ∀ r, ∑ s, hk lam r s * x' s = -I * (hH.eigenvalues j : ℝ) * x' r / ω r := by
      intro r
      have := congrFun hv r
      simp only [Matrix.mulVec, dotProduct, H, Pi.smul_apply, Complex.real_smul] at this
      have hr : (q r : ℂ) ≠ 0 := by exact_mod_cast (hq0 r).ne'
      have hωr : ((ω r : ℝ) : ℂ) = (q r : ℂ) * q r := by rw [← hqq r]; push_cast; ring
      have e : ∑ s, hk lam r s * x' s = -I / q r * ∑ s, I * ((q r * q s : ℝ) : ℂ) *
          hk lam r s * v s := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _
        simp only [x']
        push_cast
        field_simp
        ring_nf; rw [Complex.I_sq]; ring
      rw [e, this, hωr]
      simp only [x']
      field_simp
      rfl
    have hb := eigen_bound_w lam hinj ω hω hM x' _ hu
    have hn : ∑ r, ‖x' r‖ ^ 2 / ω r = 1 := by
      have : ∀ r, ‖x' r‖ ^ 2 / ω r = ‖v r‖ ^ 2 := by
        intro r
        simp only [x', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 r)]
        rw [mul_pow, ← hqq r]
        have := (hq0 r).ne'
        field_simp
      simp only [this]
      rw [← EuclideanSpace.norm_sq_eq, (hH.eigenvectorBasis).orthonormal.1 j, one_pow]
    rw [hn, mul_one, mul_one] at hb
    exact Real.abs_le_sqrt hb
  set y : ι → ℂ := fun r => x r / q r
  have hq := hermitian_quad_le hH heig y
  have e : star y ⬝ᵥ (H *ᵥ y) = -I * ∑ r, ∑ s, x r * conj (x s) * hk lam r s := by
    simp only [Matrix.mulVec, dotProduct, H, Pi.star_apply, Complex.star_def, Finset.mul_sum, y]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    have hr : (q r : ℂ) ≠ 0 := by exact_mod_cast (hq0 r).ne'
    have hs : (q s : ℂ) ≠ 0 := by exact_mod_cast (hq0 s).ne'
    rw [hk_swap lam s r]
    simp only [map_div₀, Complex.conj_ofReal]
    push_cast
    field_simp
    try ring
  have hy : ∑ r, ‖y r‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 / ω r := by
    apply Finset.sum_congr rfl; intro r _
    simp only [y, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 r), div_pow]
    rw [show q r ^ 2 = ω r by rw [sq, hqq r]]
  rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul, hy] at hq
  exact hq

/-- Hilbert's weighted inequality for a family indexed by a finset. -/
theorem hilbert_weighted_finset {α : Type*} [DecidableEq α] (S : Finset α) (lam : α → ℝ)
    (hinj : Set.InjOn lam S) (ω : α → ℝ) (hω : ∀ r ∈ S, 0 < ω r) {M : ℝ}
    (hM : ∀ s ∈ S, 2 * ω s * (∑ r ∈ S, ω r * ((lam r - lam s)⁻¹) ^ 2) +
      ∑ t ∈ S, ω t ^ 2 * ((lam s - lam t)⁻¹) ^ 2 ≤ M) (x : α → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S, x r * conj (x s) * hk lam r s‖ ≤
      Real.sqrt M * ∑ r ∈ S, ‖x r‖ ^ 2 / ω r := by
  have := hilbert_weighted (ι := S) (fun r => lam r)
    (fun r s h => Subtype.ext (hinj r.2 s.2 h)) (fun r => ω r) (fun r => hω r r.2)
    (M := M) (fun s => by
      have h := hM s s.2
      rw [← Finset.sum_coe_sort S, ← Finset.sum_coe_sort S] at h
      exact h) (fun r => x r)
  have e1 : ∑ r : S, ∑ s : S, x r * conj (x s) * hk (fun r : S => lam r) r s =
      ∑ r ∈ S, ∑ s ∈ S, x r * conj (x s) * hk lam r s := by
    rw [← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl; intro r _
    rw [← Finset.sum_coe_sort S]
    rfl
  have e2 : ∑ r : S, ‖x r‖ ^ 2 / ω r = ∑ r ∈ S, ‖x r‖ ^ 2 / ω r :=
    Finset.sum_coe_sort S (fun r => ‖x r‖ ^ 2 / ω r)
  rw [e1, e2] at this
  exact this

/-! ### The constants for `λ_n = log n`, `ω_n = 1/n` -/

lemma log_sub_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have hb : 0 < b := by linarith
  rw [← Real.log_div hb.ne' ha.ne']
  have := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [inv_div] at this
  have e : (b - a) / b = 1 - a / b := by field_simp
  linarith

lemma termD_lt {s r : ℕ} (hr : 1 ≤ r) (hrs : r < s) :
    (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2 ≤
      1 / (r : ℝ) + 1 / ((s : ℝ) - r) + s / ((s : ℝ) - r) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrs' : (r : ℝ) < s := by exact_mod_cast hrs
  have hsr : 0 < (s : ℝ) - r := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have h1 := log_sub_ge hr0 hrs'.le
  have hq : 0 < ((s : ℝ) - r) / s := div_pos hsr hs0
  have hl : 0 < Real.log s - Real.log r := lt_of_lt_of_le hq h1
  rw [← neg_sub, inv_neg, neg_sq]
  have h2 : ((Real.log s - Real.log r)⁻¹) ^ 2 ≤ ((s : ℝ) / (s - r)) ^ 2 := by
    apply pow_le_pow_left₀ (inv_nonneg.mpr hl.le)
    rw [inv_le_comm₀ hl (div_pos hs0 hsr), inv_div]; exact h1
  calc (1 / (r : ℝ)) * ((Real.log s - Real.log r)⁻¹) ^ 2 ≤
        (1 / (r : ℝ)) * ((s : ℝ) / (s - r)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / (r : ℝ) + 1 / ((s : ℝ) - r) + s / ((s : ℝ) - r) ^ 2 := by
        field_simp; ring

lemma termD_succ {s : ℕ} (hs : 1 ≤ s) :
    (1 / ((s + 1 : ℕ) : ℝ)) * ((Real.log ((s + 1 : ℕ) : ℝ) - Real.log s)⁻¹) ^ 2 ≤ s + 1 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 := log_sub_ge hs0 (by push_cast; linarith : (s : ℝ) ≤ ((s + 1 : ℕ) : ℝ))
  push_cast at h1 ⊢
  have e : ((s : ℝ) + 1 - s) / (s + 1) = 1 / (s + 1) := by ring
  rw [e] at h1
  have hl : 0 < Real.log ((s : ℝ) + 1) - Real.log s := lt_of_lt_of_le (by positivity) h1
  have h2 : ((Real.log ((s : ℝ) + 1) - Real.log s)⁻¹) ≤ s + 1 := by
    rw [inv_le_comm₀ hl (by positivity)]; simpa using h1
  have h3 : ((Real.log ((s : ℝ) + 1) - Real.log s)⁻¹) ^ 2 ≤ ((s : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hl.le) h2 2
  calc 1 / ((s : ℝ) + 1) * ((Real.log ((s : ℝ) + 1) - Real.log s)⁻¹) ^ 2
      ≤ 1 / ((s : ℝ) + 1) * ((s : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = s + 1 := by field_simp

lemma termD_tele {s r : ℕ} (hs : 1 ≤ s) (hr : s + 2 ≤ r) :
    (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2 ≤
      (Real.log ((r - 1 : ℕ) : ℝ) - Real.log s)⁻¹ - (Real.log r - Real.log s)⁻¹ := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hr1]
  have hr' : (s : ℝ) + 2 ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have ha := log_sub_ge hs0 (by linarith : (s : ℝ) ≤ r - 1)
  have hb := log_sub_ge (by linarith : (0:ℝ) < r - 1) (by linarith : (r : ℝ) - 1 ≤ r)
  set a := Real.log ((r : ℝ) - 1) - Real.log s
  set b := Real.log (r : ℝ) - Real.log s
  have ha0 : 0 < a := lt_of_lt_of_le (div_pos (by linarith) (by linarith)) ha
  have hba : b - a = Real.log r - Real.log (r - 1) := by simp only [a, b]; ring
  have hba' : 1 / (r : ℝ) ≤ b - a := by
    rw [hba]; convert hb using 1; field_simp; ring
  have hb0 : a ≤ b := by linarith [div_pos one_pos hr0]
  have hb0' : 0 < b := by linarith
  calc (1 / (r : ℝ)) * (b⁻¹) ^ 2 = (1 / r) / b ^ 2 := by field_simp
    _ ≤ (b - a) / b ^ 2 := div_le_div_of_nonneg_right hba' (by positivity)
    _ ≤ (b - a) / (a * b) := by
        apply div_le_div_of_nonneg_left (by linarith) (mul_pos ha0 hb0')
        rw [sq]; exact mul_le_mul_of_nonneg_right hb0 hb0'.le
    _ = a⁻¹ - b⁻¹ := by field_simp

lemma termE_gt {s t : ℕ} (hs : 1 ≤ s) (hst : s < t) :
    (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2 ≤ 1 / ((t - s : ℕ) : ℝ) ^ 2 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  have ht0 : (0 : ℝ) < t := by linarith
  have hts : 0 < (t : ℝ) - s := by linarith
  rw [Nat.cast_sub hst.le]
  have h1 := log_sub_ge hs0 hst'.le
  have hl : 0 < Real.log t - Real.log s := lt_of_lt_of_le (div_pos hts ht0) h1
  rw [← neg_sub, inv_neg, neg_sq]
  have h2 : ((Real.log t - Real.log s)⁻¹) ^ 2 ≤ ((t : ℝ) / (t - s)) ^ 2 := by
    apply pow_le_pow_left₀ (inv_nonneg.mpr hl.le)
    rw [inv_le_comm₀ hl (div_pos ht0 hts), inv_div]; exact h1
  calc (1 / (t : ℝ)) ^ 2 * ((Real.log t - Real.log s)⁻¹) ^ 2 ≤
        (1 / (t : ℝ)) ^ 2 * ((t : ℝ) / (t - s)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / ((t : ℝ) - s) ^ 2 := by field_simp

lemma termE_lt {s t : ℕ} (ht : 1 ≤ t) (hts : t < s) :
    (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2 ≤
      2 * (1 / (t : ℝ) ^ 2) + 2 * (1 / ((s - t : ℕ) : ℝ) ^ 2) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hts' : (t : ℝ) < s := by exact_mod_cast hts
  have hst : 0 < (s : ℝ) - t := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  rw [Nat.cast_sub hts.le]
  have h1 := log_sub_ge ht0 hts'.le
  have hl : 0 < Real.log s - Real.log t := lt_of_lt_of_le (div_pos hst hs0) h1
  have h2 : ((Real.log s - Real.log t)⁻¹) ^ 2 ≤ ((s : ℝ) / (s - t)) ^ 2 := by
    apply pow_le_pow_left₀ (inv_nonneg.mpr hl.le)
    rw [inv_le_comm₀ hl (div_pos hs0 hst), inv_div]; exact h1
  calc (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2 ≤
        (1 / (t : ℝ)) ^ 2 * ((s : ℝ) / (s - t)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 / (t : ℝ) + 1 / ((s : ℝ) - t)) ^ 2 := by field_simp; ring
    _ ≤ 2 * (1 / (t : ℝ) ^ 2) + 2 * (1 / ((s : ℝ) - t) ^ 2) := by
        have := sq_nonneg (1 / (t : ℝ) - 1 / ((s : ℝ) - t))
        have e1 : (1 / (t : ℝ)) ^ 2 = 1 / (t : ℝ) ^ 2 := by rw [_root_.one_div_pow]
        have e2 : (1 / ((s : ℝ) - t)) ^ 2 = 1 / ((s : ℝ) - t) ^ 2 := by rw [_root_.one_div_pow]
        nlinarith

/-- `∑_{t ∈ T} 1/φ(t)² ≤ 2` for `φ` injective on `T`. -/
lemma sum_inv_sq_inj_le {T : Finset ℕ} (φ : ℕ → ℕ) (hφ : Set.InjOn φ T) :
    ∑ t ∈ T, 1 / ((φ t : ℕ) : ℝ) ^ 2 ≤ 2 := by
  rw [← Finset.sum_image (f := fun j : ℕ => 1 / (j : ℝ) ^ 2) hφ]
  calc ∑ j ∈ T.image φ, 1 / (j : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
        rw [← hasSum_zeta_two.tsum_eq]
        exact hasSum_zeta_two.summable.sum_le_tsum _ (fun n _ => by positivity)
    _ ≤ 2 := by
        have h1 := Real.pi_lt_d2
        have h2 := Real.pi_pos
        nlinarith

lemma telescope_g {s : ℕ} (hs : 1 ≤ s) {N : ℕ} (hN : s + 1 ≤ N) :
    ∑ r ∈ Finset.Ioc (s + 1) N, (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2 ≤
      (Real.log ((s + 1 : ℕ) : ℝ) - Real.log s)⁻¹ - (Real.log N - Real.log s)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have := termD_tele hs (r := M + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linarith

lemma inv_log_succ_le {s : ℕ} (hs : 1 ≤ s) :
    (Real.log ((s + 1 : ℕ) : ℝ) - Real.log s)⁻¹ ≤ s + 1 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 := log_sub_ge hs0 (by push_cast; linarith : (s : ℝ) ≤ ((s + 1 : ℕ) : ℝ))
  push_cast at h1 ⊢
  have e : ((s : ℝ) + 1 - s) / (s + 1) = 1 / (s + 1) := by ring
  rw [e] at h1
  have hl : 0 < Real.log ((s : ℝ) + 1) - Real.log s := lt_of_lt_of_le (by positivity) h1
  rw [inv_le_comm₀ hl (by positivity)]; simpa using h1

/-- `∑_{r ∈ S} (1/r) (log r - log s)^{-2} ≤ 8s`. -/
lemma sumD_le (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) {s : ℕ} (hs : 1 ≤ s) :
    ∑ r ∈ S, (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2 ≤ 8 * (s : ℝ) := by
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set F : ℕ → ℝ := fun r => (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2 with hFdef
  have hF0 : ∀ r, 0 ≤ F r := fun r => mul_nonneg (by positivity) (sq_nonneg _)
  have hFs : F s = 0 := by simp [F]
  set N := max (S.sup id) (s + 1)
  have hSN : ∀ r ∈ S, r ≤ N := fun r hr =>
    le_trans (Finset.le_sup (f := id) hr) (le_max_left _ _)
  have hN : s + 1 ≤ N := le_max_right _ _
  have h1 : ∑ r ∈ S, F r = ∑ r ∈ S.filter (· < s), F r + ∑ r ∈ S.filter (¬ · < s), F r :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the part `r ≥ s`
  have hB : ∑ r ∈ S.filter (¬ · < s), F r ≤ 2 * (s : ℝ) + 2 := by
    have h2 : S.filter (¬ · < s) ⊆ insert s (insert (s + 1) (Finset.Ioc (s + 1) N)) := by
      intro r hr
      simp only [Finset.mem_filter, not_lt] at hr
      simp only [Finset.mem_insert, Finset.mem_Ioc]
      have := hSN r hr.1
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg h2 (fun r _ _ => hF0 r)).trans ?_
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), hFs, zero_add]
    have ht := telescope_g hs hN
    have hN0 : 0 ≤ (Real.log N - Real.log s)⁻¹ := by
      apply inv_nonneg.mpr; rw [sub_nonneg]
      apply Real.log_le_log (by linarith); exact_mod_cast (by omega : s ≤ N)
    have hsc := termD_succ hs
    have hi := inv_log_succ_le hs
    simp only [F] at ht ⊢
    linarith
  -- the part `r < s`
  have hA : ∑ r ∈ S.filter (· < s), F r ≤ 4 * (s : ℝ) := by
    have hle : ∀ r ∈ S.filter (· < s), F r ≤ 2 + s * (1 / ((s - r : ℕ) : ℝ) ^ 2) := by
      intro r hr
      simp only [Finset.mem_filter] at hr
      have hr1 := hS r hr.1
      have h := termD_lt hr1 hr.2
      have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hsr : ((s - r : ℕ) : ℝ) = s - r := by rw [Nat.cast_sub hr.2.le]
      have hsr1 : (1 : ℝ) ≤ s - r := by
        rw [← hsr]; exact_mod_cast (by omega : 1 ≤ s - r)
      rw [hsr]
      have a1 : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hr0
      have a2 : 1 / ((s : ℝ) - r) ≤ 1 := by rw [div_le_one (by linarith)]; exact hsr1
      have a3 : (s : ℝ) / ((s : ℝ) - r) ^ 2 = s * (1 / ((s : ℝ) - r) ^ 2) := by ring
      simp only [F]; linarith
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
    have hc : ((S.filter (· < s)).card : ℝ) ≤ s := by
      have : (S.filter (· < s)) ⊆ Finset.range s := by
        intro r hr; simp only [Finset.mem_filter] at hr; simpa using hr.2
      exact_mod_cast (Finset.card_le_card this).trans (by simp)
    have hinj : Set.InjOn (fun r => s - r) (S.filter (· < s) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    have hq := sum_inv_sq_inj_le (T := S.filter (· < s)) (fun r => s - r) hinj
    nlinarith
  rw [h1]; linarith

/-- `∑_{t ∈ S} t^{-2} (log s - log t)^{-2} ≤ 10`. -/
lemma sumE_le (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) {s : ℕ} (hs : 1 ≤ s) :
    ∑ t ∈ S, (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2 ≤ 10 := by
  set G : ℕ → ℝ := fun t => (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2
  have hG0 : ∀ t, 0 ≤ G t := fun t => mul_nonneg (by positivity) (sq_nonneg _)
  have h1 : ∑ t ∈ S, G t = ∑ t ∈ S.filter (· < s), G t + ∑ t ∈ S.filter (¬ · < s), G t :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hB : ∑ t ∈ S.filter (¬ · < s), G t ≤ 2 := by
    have hle : ∀ t ∈ S.filter (¬ · < s), G t ≤ 1 / ((t - s : ℕ) : ℝ) ^ 2 := by
      intro t ht
      simp only [Finset.mem_filter, not_lt] at ht
      rcases ht.2.lt_or_eq with h | h
      · exact termE_gt hs h
      · subst h; simp [G]
    refine (Finset.sum_le_sum hle).trans ?_
    apply sum_inv_sq_inj_le (fun t => t - s)
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, not_lt] at ha hb
    simp only at hab; omega
  have hA : ∑ t ∈ S.filter (· < s), G t ≤ 8 := by
    have hle : ∀ t ∈ S.filter (· < s), G t ≤
        2 * (1 / ((id t : ℕ) : ℝ) ^ 2) + 2 * (1 / ((s - t : ℕ) : ℝ) ^ 2) := by
      intro t ht
      simp only [Finset.mem_filter] at ht
      exact termE_lt (hS t ht.1) ht.2
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have q1 := sum_inv_sq_inj_le (T := S.filter (· < s)) id (Set.injOn_id _)
    have q2 := sum_inv_sq_inj_le (T := S.filter (· < s)) (fun t => s - t) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega)
    linarith
  rw [h1]; linarith

/-- The hypothesis of `hilbert_weighted` holds for `λ_n = log n`, `ω_n = 1/n`, `M = 26`. -/
lemma weight_bound_log (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) {s : ℕ} (hs : 1 ≤ s) :
    2 * (1 / (s : ℝ)) * (∑ r ∈ S, (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2) +
      ∑ t ∈ S, (1 / (t : ℝ)) ^ 2 * ((Real.log s - Real.log t)⁻¹) ^ 2 ≤ 26 := by
  have hD := sumD_le S hS hs
  have hE := sumE_le S hS hs
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have : 2 * (1 / (s : ℝ)) * (∑ r ∈ S, (1 / (r : ℝ)) * ((Real.log r - Real.log s)⁻¹) ^ 2)
      ≤ 2 * (1 / (s : ℝ)) * (8 * s) := mul_le_mul_of_nonneg_left hD (by positivity)
  have e : 2 * (1 / (s : ℝ)) * (8 * s) = 16 := by field_simp; ring
  linarith

/-- **Montgomery–Vaughan mean value theorem** (weighted form). For a finite set `S` of positive
integers and any coefficients `a_n`,
`|∫_{T₀}^{T₀+T} |∑_{n ∈ S} a_n n^{-it}|² dt - T ∑ |a_n|²| ≤ 2√26 ∑ n |a_n|²`. -/
theorem mean_value_weighted (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) (T₀ T : ℝ) :
    |(∫ t in T₀..T₀ + T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) -
        T * ∑ n ∈ S, ‖a n‖ ^ 2| ≤ 2 * Real.sqrt 26 * ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
  set N := S.sup id
  have hSN : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N := fun n hn => ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  set e : ℕ → ℝ → ℂ := fun (n : ℕ) (t : ℝ) => cexp (-I * t * Real.log n) with he_def
  have hF : ∀ t : ℝ, ∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I)) = ∑ n ∈ S, a n * e n t := by
    intro t; apply Finset.sum_congr rfl; intro n hn; rw [cpow_neg_mul_I (hS n hn)]
  simp only [hF]
  set Q : ℝ → ℂ := fun t => ∑ m ∈ S, ∑ n ∈ S, (a m * e m t) * conj (a n * e n t) *
    hk (fun k : ℕ => Real.log k) m n with hQ_def
  have he : ∀ n t, ‖e n t‖ = 1 := by
    intro n t
    simp only [e]
    rw [show -I * (t : ℂ) * ((Real.log n : ℝ) : ℂ) = ((-(t * Real.log n) : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hinj : Set.InjOn (fun k : ℕ => Real.log k) (S : Set ℕ) := by
    intro m hm n hn h
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hS m hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hS n hn
    exact_mod_cast Real.log_injOn_pos hm0 hn0 h
  have hQ : ∀ t, ‖Q t‖ ≤ Real.sqrt 26 * ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
    intro t
    have := hilbert_weighted_finset S (fun k : ℕ => Real.log k) hinj (fun n => 1 / (n : ℝ))
      (fun r hr => by have : (0 : ℝ) < r := by exact_mod_cast hS r hr
                      positivity)
      (M := 26) (fun s hs => weight_bound_log S hS (hS s hs)) (fun n => a n * e n t)
    simp only [norm_mul, he, mul_one, div_div_eq_mul_div, div_one] at this
    convert this using 3 with n
    ring
  have hint := integral_sq_eq S hSN a T₀ T e he_def Q hQ_def
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
