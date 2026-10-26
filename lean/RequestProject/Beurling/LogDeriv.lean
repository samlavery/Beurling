module

public import RequestProject.Beurling.Basic

/-!
# The logarithmic derivative of `ζ_P`

For `Re s > 1` (under `N_P(x) = O(x)` and `ψ_P(x) = O(x)`):

* `ζ_P'(s) = -∑_n log n · n^{-s}` (termwise differentiation);
* `∑_n log n · n^{-s} = Λ_P(s) ζ_P(s)` where `Λ_P(s) = ∑_{j,k≥1} log p_j · p_j^{-ks}`
  (the identity `log n = ∑_{p_j^k ∣ n} log p_j`, i.e. a Dirichlet convolution).

Hence `-ζ_P'/ζ_P = Λ_P`.
-/

@[expose] public section

open Filter Topology Complex

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `Λ_P(s) = ∑_{j, k ≥ 0} log p_j · (p_j^{k+1})^{-s}`, the Dirichlet series of `ψ_P`. -/
noncomputable def lam (s : ℂ) : ℂ :=
  ∑' jk : ℕ × ℕ, (Real.log (P.p jk.1) : ℂ) * ((P.p jk.1 ^ (jk.2 + 1) : ℝ) : ℂ) ^ (-s)

/-- `∑_n log n · n^{-s}`. -/
noncomputable def logZeta (s : ℂ) : ℂ :=
  ∑' e : ℕ →₀ ℕ, (Real.log (P.val e) : ℂ) * ((P.val e : ℝ) : ℂ) ^ (-s)

/-- The pairs `(n, (j, k))` with `p_j^{k+1} ∣ n`, i.e. `k + 1 ≤ e j`. -/
def DivPairs : Set ((ℕ →₀ ℕ) × (ℕ × ℕ)) := {q | q.2.2 + 1 ≤ q.1 q.2.1}

/-- `((j, k), f) ↦ (f + (k+1)·δ_j, (j, k))` is a bijection onto `DivPairs`. -/
noncomputable def divPairsEquiv : (ℕ × ℕ) × (ℕ →₀ ℕ) ≃ DivPairs where
  toFun x := ⟨(x.2 + Finsupp.single x.1.1 (x.1.2 + 1), x.1), by
    simp [DivPairs]; omega⟩
  invFun q := (q.1.2, q.1.1 - Finsupp.single q.1.2.1 (q.1.2.2 + 1))
  left_inv x := by
    simp
  right_inv q := by
    obtain ⟨⟨e, j, k⟩, hq⟩ := q
    have : Finsupp.single j (k + 1) ≤ e := by
      rw [Finsupp.single_le_iff]; exact hq
    apply Subtype.ext
    change (e - Finsupp.single j (k + 1) + Finsupp.single j (k + 1), (j, k)) = (e, (j, k))
    rw [tsub_add_cancel_of_le this]

lemma divPairsEquiv_injective :
    Function.Injective fun x => (divPairsEquiv x : (ℕ →₀ ℕ) × (ℕ × ℕ)) :=
  Subtype.val_injective.comp divPairsEquiv.injective

lemma divPairsEquiv_range {q : (ℕ →₀ ℕ) × (ℕ × ℕ)} (hq : q ∈ DivPairs) :
    q ∈ Set.range fun x => (divPairsEquiv x : (ℕ →₀ ℕ) × (ℕ × ℕ)) :=
  ⟨divPairsEquiv.symm ⟨q, hq⟩, by simp⟩

lemma hasSum_divPairs_iff {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {F : (ℕ →₀ ℕ) × (ℕ × ℕ) → α} {a : α}
    (hF : ∀ q ∉ DivPairs, F q = 0) :
    HasSum (fun x => F (divPairsEquiv x : (ℕ →₀ ℕ) × (ℕ × ℕ))) a ↔ HasSum F a :=
  divPairsEquiv_injective.hasSum_iff fun q hq =>
    hF q fun h => hq (divPairsEquiv_range h)

lemma summable_divPairs_iff {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {F : (ℕ →₀ ℕ) × (ℕ × ℕ) → α}
    (hF : ∀ q ∉ DivPairs, F q = 0) :
    Summable (fun x => F (divPairsEquiv x : (ℕ →₀ ℕ) × (ℕ × ℕ))) ↔ Summable F :=
  divPairsEquiv_injective.summable_iff fun q hq =>
    hF q fun h => hq (divPairsEquiv_range h)

/-- `∑_{(j,k) : k+1 ≤ e j} log p_j = log (val e)`. -/
lemma tsum_divisors_log (e : ℕ →₀ ℕ) :
    ∑' jk : ℕ × ℕ, (if jk.2 + 1 ≤ e jk.1 then Real.log (P.p jk.1) else 0) =
      Real.log (P.val e) := by
  have hs : Summable fun jk : ℕ × ℕ =>
      (if jk.2 + 1 ≤ e jk.1 then Real.log (P.p jk.1) else 0) := by
    apply summable_of_finite_support
    refine (Finset.finite_toSet (e.support ×ˢ Finset.range (e.support.sup e))).subset ?_
    rintro ⟨j, k⟩ h
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    have hj : j ∈ e.support := by rw [Finsupp.mem_support_iff]; omega
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Finset.mem_coe, Set.mem_Iio]
    exact ⟨hj, lt_of_lt_of_le (by omega) (Finset.le_sup (f := e) hj)⟩
  rw [hs.tsum_prod]
  have inner : ∀ j, ∑' k : ℕ, (if k + 1 ≤ e j then Real.log (P.p j) else 0) =
      e j * Real.log (P.p j) := by
    intro j
    rw [tsum_eq_sum (s := Finset.range (e j))]
    · rw [Finset.sum_ite_of_true (fun k hk => by simp at hk; omega)]
      simp
    · intro k hk; simp at hk; rw [if_neg (by omega)]
  simp only [inner]
  rw [tsum_eq_sum (s := e.support), log_val, Finsupp.sum]
  intro j hj; simp [Finsupp.notMem_support_iff.mp hj]

/-- **Convolution identity**: `∑ log n · n^{-s} = Λ_P(s) ζ_P(s)` under absolute convergence. -/
lemma logZeta_eq_lam_mul_zeta {s : ℂ}
    (hZ : Summable fun e : ℕ →₀ ℕ => P.val e ^ (-s.re))
    (hL : Summable fun jk : ℕ × ℕ => Real.log (P.p jk.1) * (P.p jk.1 ^ (jk.2 + 1)) ^ (-s.re)) :
    P.logZeta s = P.lam s * P.zeta s := by
  set b : ℕ × ℕ → ℂ := fun jk =>
    (Real.log (P.p jk.1) : ℂ) * ((P.p jk.1 ^ (jk.2 + 1) : ℝ) : ℂ) ^ (-s)
  set a : (ℕ →₀ ℕ) → ℂ := fun e => ((P.val e : ℝ) : ℂ) ^ (-s)
  have hb : Summable fun jk => ‖b jk‖ := by
    refine hL.congr fun jk => ?_
    have h0 : 0 < P.p jk.1 ^ (jk.2 + 1) := pow_pos (P.p_pos _) _
    simp only [b, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos h0,
      Real.norm_of_nonneg (Real.log_nonneg (P.one_lt jk.1).le), neg_re]
  have ha : Summable fun e => ‖a e‖ := by
    refine hZ.congr fun e => ?_
    simp only [a, Complex.norm_cpow_eq_rpow_re_of_pos (P.val_pos e), neg_re]
  -- the product family, reindexed over `DivPairs`
  set F : (ℕ →₀ ℕ) × (ℕ × ℕ) → ℂ := fun q =>
    ((if q.2.2 + 1 ≤ q.1 q.2.1 then Real.log (P.p q.2.1) else 0 : ℝ) : ℂ) *
      ((P.val q.1 : ℝ) : ℂ) ^ (-s)
  have hFE : ∀ x, F (divPairsEquiv x : (ℕ →₀ ℕ) × (ℕ × ℕ)) = b x.1 * a x.2 := by
    rintro ⟨⟨j, k⟩, f⟩
    simp only [F, divPairsEquiv, Equiv.coe_fn_mk, b, a]
    rw [if_pos (by simp), P.val_add, P.val_single, mul_assoc]
    congr 1
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (P.val_pos f).le (pow_pos (P.p_pos j) _).le, mul_comm]
  have hF0 : ∀ q ∉ DivPairs, F q = 0 := by
    intro q hq
    simp only [DivPairs, Set.mem_setOf_eq] at hq
    simp only [F, if_neg hq, Complex.ofReal_zero, zero_mul]
  have hsum : HasSum F (P.lam s * P.zeta s) := by
    rw [← hasSum_divPairs_iff hF0]
    simp only [hFE]
    have := (summable_mul_of_summable_norm hb ha).hasSum
    rwa [← tsum_mul_tsum_of_summable_norm hb ha] at this
  rw [← hsum.tsum_eq, hsum.summable.tsum_prod]
  refine tsum_congr fun e => ?_
  simp only [F]
  rw [tsum_mul_right, ← Complex.ofReal_tsum, tsum_divisors_log]

/-- Termwise differentiation: `ζ_P'(s) = -∑ log n · n^{-s}` for `Re s > 1`, provided
`N_P(x) = O(x)`. -/
lemma hasDerivAt_zeta (h : AbelMellin.Hyp P.val (fun _ => (1 : ℝ)) 1) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt P.zeta (-P.logZeta s) s := by
  set σ₀ : ℝ := (1 + s.re) / 2
  set δ : ℝ := (σ₀ - 1) / 2
  have hδ : 0 < δ := by simp only [δ, σ₀]; linarith
  have hσ₀s : σ₀ < s.re := by simp only [σ₀]; linarith
  have hu : Summable fun e : ℕ →₀ ℕ => Real.log (P.val e) * P.val e ^ (-σ₀) := by
    have hs := AbelMellin.summable_rpow h (σ := σ₀ - δ) (by simp only [δ, σ₀]; linarith)
      (by simp only [δ, σ₀]; linarith)
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) (hs.mul_left (1 / δ))
    · exact mul_nonneg (Real.log_nonneg (P.one_le_val e)) (Real.rpow_nonneg (P.val_pos e).le _)
    · have h1 := Real.log_le_rpow_div (P.val_pos e).le hδ
      have h2 : 0 ≤ P.val e ^ (-σ₀) := Real.rpow_nonneg (P.val_pos e).le _
      calc Real.log (P.val e) * P.val e ^ (-σ₀) ≤ P.val e ^ δ / δ * P.val e ^ (-σ₀) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = 1 / δ * (1 * P.val e ^ (-(σ₀ - δ))) := by
            rw [one_mul, show -(σ₀ - δ) = δ + -σ₀ by ring, Real.rpow_add (P.val_pos e)]
            ring
  have hderiv : ∀ (e : ℕ →₀ ℕ) (z : ℂ), HasDerivAt (fun z => ((P.val e : ℝ) : ℂ) ^ (-z))
      (-(Real.log (P.val e) : ℂ) * ((P.val e : ℝ) : ℂ) ^ (-z)) z := by
    intro e z
    have hne : ((P.val e : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (P.val_pos e).ne'
    have := (hasDerivAt_neg z).const_cpow (c := ((P.val e : ℝ) : ℂ)) (Or.inl hne)
    convert this using 1
    rw [← Complex.ofReal_log (P.val_pos e).le]
    ring
  have hopen : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {z : ℂ | σ₀ < z.re} := (convex_halfSpace_re_gt σ₀).isPreconnected
  have hs0 : Summable fun e : ℕ →₀ ℕ => ((P.val e : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm ?_
    have := AbelMellin.summable_rpow h (σ := s.re) (by linarith) hs
    refine this.congr fun e => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (P.val_pos e)]
    simp
  have := hasDerivAt_tsum_of_isPreconnected hu hopen hconn (fun e z _ => hderiv e z)
    (fun e z hz => ?_) (show s ∈ {z : ℂ | σ₀ < z.re} from hσ₀s) hs0
    (show s ∈ {z : ℂ | σ₀ < z.re} from hσ₀s)
  · unfold logZeta
    rw [← tsum_neg]
    convert this using 2
    ext e
    ring
  · simp only [Set.mem_setOf_eq] at hz
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (P.val_pos e),
      Real.norm_of_nonneg (Real.log_nonneg (P.one_le_val e))]
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (P.one_le_val e))
    apply Real.rpow_le_rpow_of_exponent_le (P.one_le_val e)
    simp only [neg_re]; linarith

end BeurlingSystem

end
