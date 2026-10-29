module

public import RequestProject.Beurling.LocalPNT.Defs

/-!
# Finite Euler products of a Beurling system

For a finite set `J` of prime indices, `ζ_J(s) = ∏_{j ∈ J} (1 - p_j^{-s})^{-1}` (`zetaF`) and its
real version `zetaFR`.

* `hasSum_zetaF`, `hasSum_zetaFR` : `ζ_J(s) = ∑_{supp e ⊆ J} (val e)^{-s}` for `Re s > 0`.
* `norm_zetaF_le`, `norm_inv_zetaF_le` : `|ζ_J(s)|, |ζ_J(s)^{-1}| ≤ ζ_J(σ)`.
* `logDeriv_zetaF` : `ζ_J'/ζ_J = -∑_{j ∈ J} log p_j · p_j^{-s}/(1 - p_j^{-s})`, and
  `hasSum_logFactor` expands each term as a Dirichlet series with nonnegative coefficients.
* `support_subset_primesLe` : an element `≤ y` only involves primes `≤ y`.
-/

@[expose] public section

open Complex Finset

namespace LocalPNT

/-- `ζ_J(s) = ∏_{j ∈ J} (1 - p_j^{-s})^{-1}`. -/
noncomputable def zetaF (P : BeurlingSystem) (J : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ J, (1 - ((P.p j : ℝ) : ℂ) ^ (-s))⁻¹

/-- `ζ_J(σ)` on the real axis. -/
noncomputable def zetaFR (P : BeurlingSystem) (J : Finset ℕ) (σ : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - P.p j ^ (-σ))⁻¹

section factor

variable (P : BeurlingSystem)

lemma p_rpow_neg_lt_one (j : ℕ) {σ : ℝ} (hσ : 0 < σ) : P.p j ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)

lemma norm_p_cpow_neg (j : ℕ) (s : ℂ) : ‖((P.p j : ℝ) : ℂ) ^ (-s)‖ = P.p j ^ (-s.re) := by
  rw [norm_cpow_eq_rpow_re_of_pos (P.p_pos j), neg_re]

lemma norm_p_cpow_neg_lt_one (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖((P.p j : ℝ) : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_p_cpow_neg]; exact p_rpow_neg_lt_one P j hs

lemma one_sub_p_cpow_ne_zero (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    1 - ((P.p j : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 := norm_sub_norm_le (1 : ℂ) (((P.p j : ℝ) : ℂ) ^ (-s))
  rw [h, norm_zero, norm_one] at h1
  linarith [norm_p_cpow_neg_lt_one P j hs]

lemma factorR_pos (j : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < (1 - P.p j ^ (-σ))⁻¹ :=
  inv_pos.mpr (by linarith [p_rpow_neg_lt_one P j hσ])

lemma norm_factor_le (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖(1 - ((P.p j : ℝ) : ℂ) ^ (-s))⁻¹‖ ≤ (1 - P.p j ^ (-s.re))⁻¹ := by
  have h1 := norm_sub_norm_le (1 : ℂ) (((P.p j : ℝ) : ℂ) ^ (-s))
  rw [norm_one, norm_p_cpow_neg] at h1
  rw [norm_inv]
  exact inv_anti₀ (by linarith [p_rpow_neg_lt_one P j hs]) h1

lemma norm_inv_factor_le (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖1 - ((P.p j : ℝ) : ℂ) ^ (-s)‖ ≤ (1 - P.p j ^ (-s.re))⁻¹ := by
  have h0 := p_rpow_neg_lt_one P j hs
  have hx : 0 ≤ P.p j ^ (-s.re) := Real.rpow_nonneg (P.p_pos j).le _
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_p_cpow_neg, ← one_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- `(p_j^m)^{-s} = (p_j^{-s})^m`. -/
lemma pow_cpow_neg (j m : ℕ) (s : ℂ) :
    ((P.p j ^ m : ℝ) : ℂ) ^ (-s) = (((P.p j : ℝ) : ℂ) ^ (-s)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (P.p j), ofReal_mul,
      mul_cpow_ofReal_nonneg (pow_nonneg (P.p_pos j).le _) (P.p_pos j).le, ih, pow_succ]

end factor

/-! ## The Dirichlet series of `ζ_J` -/

section series

variable (P : BeurlingSystem)

/-- The exponent vectors supported in `J`. -/
def suppIn (J : Finset ℕ) : Set (ℕ →₀ ℕ) := {e | e.support ⊆ J}

/-- `{e : supp e ⊆ insert j J} ≃ ℕ × {e : supp e ⊆ J}`, `e = single j m + e'`. -/
noncomputable def insertEquiv {j : ℕ} {J : Finset ℕ} (hj : j ∉ J) :
    ℕ × suppIn J ≃ suppIn (insert j J) where
  toFun x := ⟨Finsupp.single j x.1 + x.2.1, by
    refine Finsupp.support_add.trans (Finset.union_subset
      (Finsupp.support_single_subset.trans (by simp)) (x.2.2.trans (subset_insert _ _)))⟩
  invFun e := (e.1 j, ⟨e.1.erase j, by
    intro i hi
    rw [Finsupp.support_erase, Finset.mem_erase] at hi
    have := e.2 hi.2
    rw [Finset.mem_insert] at this
    exact this.resolve_left hi.1⟩)
  left_inv x := by
    obtain ⟨m, e, he⟩ := x
    have hje : e j = 0 := Finsupp.notMem_support_iff.1 fun h => hj (he h)
    have hje' : j ∉ e.support := fun h => hj (he h)
    ext1
    · simp [hje]
    · ext1
      simp [Finsupp.erase_add, Finsupp.erase_of_notMem_support hje']
  right_inv e := by
    ext1
    simp [Finsupp.single_add_erase]

lemma val_insertEquiv {j : ℕ} {J : Finset ℕ} (hj : j ∉ J) (x : ℕ × suppIn J) :
    P.val (insertEquiv hj x).1 = P.p j ^ x.1 * P.val x.2.1 := by
  simp [insertEquiv, BeurlingSystem.val_add, BeurlingSystem.val_single]

/-- The terms `(val e)^{-s}` of the Dirichlet series of `ζ_J`. -/
noncomputable def term (J : Finset ℕ) (s : ℂ) (e : suppIn J) : ℂ := ((P.val e.1 : ℝ) : ℂ) ^ (-s)

lemma term_insertEquiv {j : ℕ} {J : Finset ℕ} (hj : j ∉ J) (s : ℂ) :
    term P (insert j J) s ∘ insertEquiv hj =
      fun x => (((P.p j : ℝ) : ℂ) ^ (-s)) ^ x.1 * term P J s x.2 := by
  funext x
  rw [Function.comp_apply, term, term, val_insertEquiv, ofReal_mul,
    mul_cpow_ofReal_nonneg (pow_nonneg (P.p_pos j).le _) (P.val_pos _).le, pow_cpow_neg]

lemma hasSum_term_empty (s : ℂ) :
    HasSum (term P ∅ s) (zetaF P ∅ s) ∧ Summable fun e => ‖term P ∅ s e‖ := by
  have h0 : ∀ e : suppIn ∅, e = ⟨0, by simp [suppIn]⟩ := fun e =>
    Subtype.ext (Finsupp.support_eq_empty.1 (Finset.subset_empty.1 e.2))
  haveI : Unique (suppIn ∅) := ⟨⟨⟨0, by simp [suppIn]⟩⟩, h0⟩
  refine ⟨?_, (hasSum_unique _).summable⟩
  have : term P ∅ s default = 1 := by
    rw [h0 default]; simp [term, BeurlingSystem.val]
  rw [zetaF, prod_empty, ← this]
  exact hasSum_unique _

lemma hasSum_term_insert {j : ℕ} {J : Finset ℕ} (hj : j ∉ J) {s : ℂ} (hs : 0 < s.re)
    (hb : HasSum (term P J s) (zetaF P J s)) (hb' : Summable fun e => ‖term P J s e‖) :
    HasSum (term P (insert j J) s) (zetaF P (insert j J) s) ∧
      Summable fun e => ‖term P (insert j J) s e‖ := by
  have hξ := norm_p_cpow_neg_lt_one P j hs
  have ha := hasSum_geometric_of_norm_lt_one hξ
  have ha' : Summable fun m : ℕ => ‖(((P.p j : ℝ) : ℂ) ^ (-s)) ^ m‖ := by
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hξ
  have hm := summable_mul_of_summable_norm ha' hb'
  constructor
  · rw [← (insertEquiv hj).hasSum_iff, term_insertEquiv, zetaF, prod_insert hj]
    exact ha.mul hb hm
  · rw [← (insertEquiv hj).summable_iff]
    have : (fun e => ‖term P (insert j J) s e‖) ∘ insertEquiv hj =
        fun x => ‖(((P.p j : ℝ) : ℂ) ^ (-s)) ^ x.1‖ * ‖term P J s x.2‖ := by
      funext x
      rw [Function.comp_apply, ← Function.comp_apply (f := term P (insert j J) s),
        term_insertEquiv, norm_mul]
    rw [this]
    exact summable_mul_of_summable_norm (f := fun m : ℕ => ‖(((P.p j : ℝ) : ℂ) ^ (-s)) ^ m‖)
      (g := fun e => ‖term P J s e‖) (by simpa using ha') (by simpa using hb')

lemma hasSum_term (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (term P J s) (zetaF P J s) ∧ Summable fun e => ‖term P J s e‖ := by
  induction J using Finset.induction_on with
  | empty => exact hasSum_term_empty P s
  | insert j J hj ih => exact hasSum_term_insert P hj hs ih.1 ih.2

theorem hasSum_zetaF (P : BeurlingSystem) (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun e : ℕ →₀ ℕ => if e.support ⊆ J then ((P.val e : ℝ) : ℂ) ^ (-s) else 0)
      (zetaF P J s) := by
  have h := hasSum_subtype_iff_indicator (f := fun e : ℕ →₀ ℕ => ((P.val e : ℝ) : ℂ) ^ (-s))
    (s := suppIn J) |>.1 (hasSum_term P J hs).1
  convert h using 1
  funext e
  simp only [Set.indicator_apply, suppIn, Set.mem_setOf_eq]

lemma zetaF_ofReal (J : Finset ℕ) (σ : ℝ) : zetaF P J σ = (zetaFR P J σ : ℂ) := by
  simp only [zetaF, zetaFR, ofReal_prod, ofReal_inv, ofReal_sub, ofReal_one]
  refine prod_congr rfl fun j _ => ?_
  rw [← ofReal_neg, ofReal_cpow (P.p_pos j).le]

theorem hasSum_zetaFR (P : BeurlingSystem) (J : Finset ℕ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun e : ℕ →₀ ℕ => if e.support ⊆ J then P.val e ^ (-σ) else 0) (zetaFR P J σ) := by
  have h := hasSum_zetaF P J (s := σ) (by simpa using hσ)
  rw [zetaF_ofReal] at h
  refine Complex.hasSum_ofReal.1 ?_
  convert h using 2 with e
  split_ifs
  · rw [← ofReal_neg, ofReal_cpow (P.val_pos e).le]
  · simp

/-- `p_j^{-s}/(1 - p_j^{-s}) = ∑_{m ≥ 1} (p_j^m)^{-s}`. -/
theorem hasSum_logFactor (P : BeurlingSystem) (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun m : ℕ => ((P.p j ^ (m + 1) : ℝ) : ℂ) ^ (-s))
      (((P.p j : ℝ) : ℂ) ^ (-s) / (1 - ((P.p j : ℝ) : ℂ) ^ (-s))) := by
  have h := (hasSum_geometric_of_norm_lt_one (norm_p_cpow_neg_lt_one P j hs)).mul_left
    (((P.p j : ℝ) : ℂ) ^ (-s))
  convert h using 1
  funext m; rw [pow_cpow_neg, pow_succ']

end series

/-! ## Bounds -/

section bounds

variable (P : BeurlingSystem)

theorem support_subset_primesLe (P : BeurlingSystem) {y : ℝ} {e : ℕ →₀ ℕ} (he : P.val e ≤ y) :
    e.support ⊆ P.primesLe y := by
  intro j hj
  rw [BeurlingSystem.mem_primesLe]
  exact (le_self_pow₀ (P.one_lt j).le (Finsupp.mem_support_iff.1 hj)).trans
    ((P.pow_le_val e j).trans he)

theorem zetaFR_pos (J : Finset ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < zetaFR P J σ :=
  prod_pos fun j _ => factorR_pos P j hσ

theorem norm_zetaF_le (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖zetaF P J s‖ ≤ zetaFR P J s.re := by
  rw [zetaF, norm_prod]
  exact prod_le_prod (fun j _ => norm_nonneg _) fun j _ => norm_factor_le P j hs

theorem norm_inv_zetaF_le (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖(zetaF P J s)⁻¹‖ ≤ zetaFR P J s.re := by
  rw [zetaF, ← prod_inv_distrib, norm_prod]
  simp only [inv_inv]
  exact prod_le_prod (fun j _ => norm_nonneg _) fun j _ => norm_inv_factor_le P j hs

theorem zetaF_ne_zero (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) : zetaF P J s ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => inv_ne_zero (one_sub_p_cpow_ne_zero P j hs)

theorem zetaFR_antitoneOn (J : Finset ℕ) : AntitoneOn (zetaFR P J) (Set.Ioi 0) := by
  intro σ hσ τ _ hστ
  have hτ : 0 < τ := lt_of_lt_of_le (Set.mem_Ioi.1 hσ) hστ
  refine prod_le_prod (fun j _ => (factorR_pos P j hτ).le) fun j _ => ?_
  have h1 := p_rpow_neg_lt_one P j (Set.mem_Ioi.1 hσ)
  exact inv_anti₀ (by linarith) (by
    linarith [Real.rpow_le_rpow_of_exponent_le (P.one_lt j).le (neg_le_neg hστ)])

end bounds

/-! ## Holomorphy and the logarithmic derivative -/

section deriv

variable (P : BeurlingSystem)

lemma hasDerivAt_factor (j : ℕ) (s : ℂ) :
    HasDerivAt (fun z => 1 - ((P.p j : ℝ) : ℂ) ^ (-z))
      (Real.log (P.p j) * ((P.p j : ℝ) : ℂ) ^ (-s)) s := by
  have hp : ((P.p j : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (P.p_pos j).ne'
  have h := ((hasDerivAt_id s).neg.const_cpow (c := ((P.p j : ℝ) : ℂ)) (Or.inl hp)).const_sub 1
  convert h using 1
  rw [ofReal_log (P.p_pos j).le]
  simp only [Pi.neg_apply, id_eq]
  ring

lemma differentiableAt_factor (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => (1 - ((P.p j : ℝ) : ℂ) ^ (-z))⁻¹) s :=
  (hasDerivAt_factor P j s).differentiableAt.inv (one_sub_p_cpow_ne_zero P j hs)

theorem differentiableOn_zetaF (J : Finset ℕ) :
    DifferentiableOn ℂ (zetaF P J) {s | 0 < s.re} := by
  intro s hs
  have : zetaF P J = fun z => ∏ j ∈ J, (1 - ((P.p j : ℝ) : ℂ) ^ (-z))⁻¹ := rfl
  rw [this]
  exact (DifferentiableAt.fun_finset_prod fun j _ =>
    differentiableAt_factor P j hs).differentiableWithinAt

theorem logDeriv_zetaF (J : Finset ℕ) {s : ℂ} (hs : 0 < s.re) :
    deriv (zetaF P J) s / zetaF P J s = -∑ j ∈ J, (Real.log (P.p j) : ℂ) *
      ((P.p j : ℝ) : ℂ) ^ (-s) / (1 - ((P.p j : ℝ) : ℂ) ^ (-s)) := by
  rw [← logDeriv_apply]
  have : zetaF P J = fun z => ∏ j ∈ J, (1 - ((P.p j : ℝ) : ℂ) ^ (-z))⁻¹ := rfl
  rw [this, logDeriv_prod (fun j _ => inv_ne_zero (one_sub_p_cpow_ne_zero P j hs))
    fun j _ => differentiableAt_factor P j hs, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h : deriv (fun z => (1 - ((P.p j : ℝ) : ℂ) ^ (-z))⁻¹) s = _ :=
    ((hasDerivAt_factor P j s).inv (one_sub_p_cpow_ne_zero P j hs)).deriv
  rw [logDeriv_apply, h]
  have := one_sub_p_cpow_ne_zero P j hs
  field_simp

end deriv

end LocalPNT
