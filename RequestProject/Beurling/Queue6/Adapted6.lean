module

public import RequestProject.Beurling.Queue6.Defs6
public import RequestProject.Beurling.Model.MeasIter
public import RequestProject.Beurling.Model.WinLink

/-!
# The counts of §6.3 are adapted (Lemma 3.2, Lemma 3.5, (F2))

"These are `ℱ_q`-measurable: `n = q^a m` with `m` decided before `q`, and absorption is decided
by `q < y(n)`" (§6.3). For the constructed model at the clamped jitters (Model/Stage.lean: the
slot starts and decisions at relative slot `k + 1` are `ℱ_k`-measurable, the landing point is
`ℱ_{k+1}`-measurable):

* `Queue6.xcount_adapted` : `X⁽ⁿ⁾_q([α, β))` of the prime decided at relative slot `k + 1` is
  `ℱ_{k+1}`-measurable (a count over the exponent vectors with latest prime `k`, each condition
  reading only the primes decided at slots `≤ k + 1`);
* `Queue6.x2count_adapted`, `Queue6.Xt_adapted`, `Queue6.Ind2_adapted`;
* `Queue6.landInd_adapted` : the landing indicator of Lemma 6.1.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueMono
  Greedy SlotModel AbsorbEmpty

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### Counting measurably -/

/-- The number of elements of a finite set, as a measurable function of the parameter, when
membership of each element is measurable. -/
lemma measurable_ncard {α Ω : Type*} [Countable α] {m : MeasurableSpace Ω} (s : Ω → Set α)
    (hfin : ∀ ω, (s ω).Finite) (hmeas : ∀ a, MeasurableSet {ω | a ∈ s ω}) :
    Measurable fun ω => ((s ω).ncard : ℝ) := by
  classical
  have e : ∀ ω, ((s ω).ncard : ℝ) =
      (∑' a, (if a ∈ s ω then (1 : ENNReal) else 0)).toReal := by
    intro ω
    rw [tsum_eq_sum (s := (hfin ω).toFinset) (fun a ha => by
      rw [Set.Finite.mem_toFinset] at ha; simp [ha])]
    rw [Finset.sum_congr rfl (fun a ha => by
      rw [Set.Finite.mem_toFinset] at ha; simp [ha] : ∀ a ∈ (hfin ω).toFinset,
        (if a ∈ s ω then (1 : ENNReal) else 0) = 1)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card _ (hfin ω)]
    simp
  simp_rw [e]
  refine ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun a => ?_)
  exact Measurable.ite (hmeas a) measurable_const measurable_const

/-! ### The counts over the fixed index set -/

/-- The latest jittered index of an exponent vector over `PIdx X₀`. -/
noncomputable def latP (e : PIdx X₀ →₀ ℕ) : ℕ := sSup {j | e (Sum.inr j) ≠ 0}

variable (θ X₀) in
/-- The prime data of the clamped construction. -/
noncomputable abbrev DD (ω : JitterΩ) : PrimeData := DM (CM θ X₀ ω) (Ucl ω)

variable (θ X₀) in
/-- `X⁽ⁿ⁾_q` over the fixed index set: live composites in `[α, β)`, with a jittered prime, not in
`𝒜`, latest prime decided at relative slot `k + 1`, exponent `P` there. -/
def xsetP (α β : ℝ) (k : ℕ) (P : ℕ → Prop) (ω : JitterΩ) : Set (PIdx X₀ →₀ ℕ) :=
  {e | Live (DD θ X₀ ω) e ∧ 2 ≤ e.sum (fun _ n => n) ∧ α ≤ eval (DD θ X₀ ω) e ∧
    eval (DD θ X₀ ω) e < β ∧ (∃ j, e (Sum.inr j) ≠ 0) ∧
    ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e) ∧
      (DD θ X₀ ω).v (latP e) < absorbY X₀ (eval (DD θ X₀ ω) e)) ∧
    latP e = k ∧ P (e (Sum.inr k))}

lemma latP_mapE {M : SlotModel X₀} (f : RealisedIdx M →₀ ℕ) : latP (mapE M f) = latk M f := by
  classical
  unfold latP latk
  congr 1
  ext j
  simp only [mem_setOf_eq, jitIdx, mapE_apply_inr]
  constructor
  · intro h
    split_ifs at h with hj
    · exact ⟨hj, h⟩
    · exact absurd rfl h
  · rintro ⟨hj, h⟩; rw [dif_pos hj]; exact h

lemma ratOnly_iff_mapE {M : SlotModel X₀} (f : RealisedIdx M →₀ ℕ) :
    ¬ RatOnly f ↔ ∃ j, mapE M f (Sum.inr j) ≠ 0 := by
  classical
  unfold RatOnly
  push_neg
  constructor
  · rintro ⟨⟨j, hj⟩, h⟩; exact ⟨j, by rw [mapE_apply_inr, dif_pos hj]; exact h⟩
  · rintro ⟨j, h⟩
    rw [mapE_apply_inr] at h
    split_ifs at h with hj
    · exact ⟨⟨j, hj⟩, h⟩
    · exact absurd rfl h

lemma mult_mapE {M : SlotModel X₀} (f : RealisedIdx M →₀ ℕ) (k : ℕ) :
    mult M f k = mapE M f (Sum.inr k) := by
  classical
  unfold mult; rw [mapE_apply_inr]

/-- `X⁽ⁿ⁾_q` and `X⁽²⁾_q` are counts over the fixed index set. -/
lemma ncard_xset (α β : ℝ) (k : ℕ) (P : ℕ → Prop) (ω : JitterΩ) :
    {f | f ∈ cjitSet (CM θ X₀ ω) (Ucl ω) α β ∧ latk (CM θ X₀ ω) f = k ∧
      P (mult (CM θ X₀ ω) f k)}.ncard = (xsetP θ X₀ α β k P ω).ncard := by
  refine ncard_eq_of_mapE (U := Ucl ω) (fun f => ?_) (fun e he => he.1)
  have h1 := sum_mapE (CM θ X₀ ω) f
  have h2 := eval_mapE (CM θ X₀ ω) (Ucl ω) f
  have h3 := latP_mapE (M := CM θ X₀ ω) f
  have h4 := mult_mapE (M := CM θ X₀ ω) f k
  have h5 := ratOnly_iff_mapE (M := CM θ X₀ ω) f
  simp only [mem_setOf_eq, xsetP, cjitSet, compositeSet, OwnAbs]
  rw [h1, h2, h3, ← h4, ← h5]
  constructor
  · rintro ⟨⟨⟨h2, h1, h3⟩, hr, hA⟩, hk, hP⟩
    refine ⟨live_mapE _ _ f, h2, h1, h3, hr, fun ⟨hl, hy⟩ => hA ⟨hl, hr, hy⟩, hk, hP⟩
  · rintro ⟨-, h2, h1, h3, hr, hA, hk, hP⟩
    exact ⟨⟨⟨h2, h1, h3⟩, hr, fun ⟨hl, _, hy⟩ => hA ⟨hl, hy⟩⟩, hk, hP⟩

/-! ### Measurability -/

section Meas

variable (hc : Cond θ X₀)
include hc

omit hc in
lemma latP_le {e : PIdx X₀ →₀ ℕ} {j : ℕ} (hj : e (Sum.inr j) ≠ 0) : j ≤ latP e := by
  classical
  apply le_csSup _ hj
  refine ((e.support.image fun i => match i with
    | Sum.inl _ => 0
    | Sum.inr k => k).finite_toSet.subset fun k hk => ?_).bddAbove
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff]
  exact ⟨Sum.inr k, hk, rfl⟩

omit hc in
lemma absorbY_monotone (hX : 10 ^ 8 ≤ Real.log X₀) : Monotone (absorbY X₀) := by
  intro a b hab
  have hX0 : (0 : ℝ) < X₀ := by have := one_lt_of_logX (Nat.cast_nonneg _) hX; linarith
  unfold absorbY
  exact absorbYAt_mono (Nat.cast_nonneg _) hX (le_dyadicScale hX0 (le_max_left _ _))
    (dyadicScale_mono hX0 (lt_of_lt_of_le hX0 (le_max_left _ _)) (max_le_max le_rfl hab))

/-- The value of a prime index, for the clamped construction, is `ℱ_{k+1}`-measurable when the
index is rational or decided at a slot `≤ k`. -/
lemma pval_meas {k : ℕ} (i : PIdx X₀) (hi : ∀ j, i = Sum.inr j → j ≤ k) :
    Measurable[jitterFiltration (k + 1)] fun ω => pval (DD θ X₀ ω) i := by
  cases i with
  | inl p => exact measurable_const
  | inr j =>
    have hjk : j + 1 ≤ k + 1 := by have := hi j rfl; omega
    exact (valF_adapted hc (stageMeas hc) j).mono (jitterFiltration.mono hjk) le_rfl

lemma eval_meas {k : ℕ} (e : PIdx X₀ →₀ ℕ) (he : ∀ j, e (Sum.inr j) ≠ 0 → j ≤ k) :
    Measurable[jitterFiltration (k + 1)] fun ω => eval (DD θ X₀ ω) e := by
  unfold eval Finsupp.prod
  refine Finset.measurable_prod _ fun i hi =>
    ((continuous_pow (e i)).measurable).comp (pval_meas hc i fun j hj => ?_)
  subst hj; exact he j (Finsupp.mem_support_iff.mp hi)

/-- **Membership in `X⁽ⁿ⁾_q` is `ℱ_{k+1}`-measurable.** -/
lemma xsetP_meas (α β : ℝ) (k : ℕ) (P : ℕ → Prop) (e : PIdx X₀ →₀ ℕ) :
    MeasurableSet[jitterFiltration (k + 1)] {ω | e ∈ xsetP θ X₀ α β k P ω} := by
  classical
  by_cases hk : latP e = k
  · have he : ∀ j, e (Sum.inr j) ≠ 0 → j ≤ k := fun j hj => hk ▸ latP_le hj
    have hev := eval_meas hc e he
    have hS : {j | e (Sum.inr j) ≠ 0}.Finite := by
      refine (e.support.image fun i => match i with
        | Sum.inl _ => 0
        | Sum.inr k => k).finite_toSet.subset fun k hk => ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff]
      exact ⟨Sum.inr k, hk, rfl⟩
    have hlive : MeasurableSet[jitterFiltration (k + 1)] {ω | Live (DD θ X₀ ω) e} := by
      have : {ω | Live (DD θ X₀ ω) e} = ⋂ j ∈ {j | e (Sum.inr j) ≠ 0}, placedF θ X₀ j := by
        ext ω; simp only [Live, mem_setOf_eq, mem_iInter]; rfl
      rw [this]
      exact hS.measurableSet_biInter fun j hj =>
        jitterFiltration.mono (show j ≤ k + 1 by have := he j hj; omega) _
          (placedF_adapted hc (stageMeas hc) j)
    have hv : Measurable[jitterFiltration (k + 1)] fun ω => (DD θ X₀ ω).v (latP e) := by
      rw [hk]
      exact (valF_adapted hc (stageMeas hc) k)
    have hy : Measurable[jitterFiltration (k + 1)] fun ω => absorbY X₀ (eval (DD θ X₀ ω) e) :=
      (absorbY_monotone hc.hX).measurable.comp hev
    have hlog : Measurable[jitterFiltration (k + 1)] fun ω =>
        Real.log (eval (DD θ X₀ ω) e) := Real.measurable_log.comp hev
    unfold xsetP
    simp only [mem_setOf_eq]
    refine hlive.inter (MeasurableSet.const _ |>.inter
      ((measurableSet_le measurable_const hev).inter
      ((measurableSet_lt hev measurable_const).inter (MeasurableSet.const _ |>.inter
        (((measurableSet_le measurable_const hlog).inter
          (measurableSet_lt hv hy)).compl.inter (MeasurableSet.const _ |>.inter
            (MeasurableSet.const _)))))))
  · have : {ω | e ∈ xsetP θ X₀ α β k P ω} = ∅ := by
      ext ω; simp only [xsetP, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, -, -, -, h, -⟩; exact hk h
    rw [this]; exact @MeasurableSet.empty _ (jitterFiltration (k + 1))

lemma xsetP_finite (α β : ℝ) (k : ℕ) (P : ℕ → Prop) (ω : JitterΩ) :
    (xsetP θ X₀ α β k P ω).Finite := by
  have hU : ∀ j, Ucl ω j ∈ Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  refine (finite_elems_gt (locFinD_DM hc.hX hU (CM θ X₀ ω)) β).subset fun e he => ?_
  refine ⟨he.1, fun i hi => ?_, he.2.2.2.1.le⟩
  cases i with
  | inl p =>
    show (1 : ℝ) < (p.1 : ℝ)
    exact_mod_cast p.2.1.one_lt
  | inr j =>
    have hj : placedAt (CM θ X₀ ω) j := he.1 j (Finsupp.mem_support_iff.mp hi)
    show (1 : ℝ) < valF θ X₀ j ω
    have h1 := valF_ge_78 hc j ω
    have h2 := slotF_ge hc j ω
    have := two_pow_le_of_logX (Nat.cast_nonneg _) hc.hX (X₀ := (X₀ : ℝ))
    linarith

/-- **`X⁽ⁿ⁾_q([α, β))` is `ℱ_{k+1}`-measurable.** -/
theorem xcount_adapted (α β : ℝ) (k n : ℕ) :
    Measurable[jitterFiltration (k + 1)] fun ω => Xcount (CM θ X₀ ω) (Ucl ω) α β k n := by
  have e : (fun ω => Xcount (CM θ X₀ ω) (Ucl ω) α β k n) =
      fun ω => ((xsetP θ X₀ α β k (· = n) ω).ncard : ℝ) := by
    funext ω; unfold Xcount xset; exact_mod_cast ncard_xset α β k (· = n) ω
  rw [e]
  exact measurable_ncard _ (xsetP_finite hc α β k _) (xsetP_meas hc α β k _)

/-- **`X⁽²⁾_q([α, β))` is `ℱ_{k+1}`-measurable.** -/
theorem x2count_adapted (α β : ℝ) (k : ℕ) :
    Measurable[jitterFiltration (k + 1)] fun ω => X2count (CM θ X₀ ω) (Ucl ω) α β k := by
  have e : (fun ω => X2count (CM θ X₀ ω) (Ucl ω) α β k) =
      fun ω => ((xsetP θ X₀ α β k (2 ≤ ·) ω).ncard : ℝ) := by
    funext ω; unfold X2count x2set; exact_mod_cast ncard_xset α β k (2 ≤ ·) ω
  rw [e]
  exact measurable_ncard _ (xsetP_finite hc α β k _) (xsetP_meas hc α β k _)

theorem Xt_adapted (m : ℕ) (a b : ℤ) (k : ℕ) :
    StronglyMeasurable[jitterFiltration (k + 1)] (Xt θ X₀ m a b k) :=
  ((xcount_adapted hc a b k 1).min measurable_const).stronglyMeasurable

theorem Ind2_adapted (a b : ℤ) (k : ℕ) :
    StronglyMeasurable[jitterFiltration (k + 1)] (Ind2 θ X₀ a b k) := by
  have h := measurableSet_le (measurable_const (a := (1 : ℝ))) (x2count_adapted hc (a : ℝ) b k)
  exact (Measurable.ite h measurable_const measurable_const).stronglyMeasurable

/-- **The landing indicator of Lemma 6.1 is `ℱ_{k+1}`-measurable.** -/
theorem landInd_adapted (m i j k : ℕ) :
    StronglyMeasurable[jitterFiltration (k + 1)] (landInd θ X₀ m i j k) := by
  have hs : Measurable[jitterFiltration (k + 1)] (slotF θ X₀ k) :=
    (slotF_adapted hc (stageMeas hc) k).mono (jitterFiltration.mono (Nat.le_succ k)) le_rfl
  have hH : Measurable[jitterFiltration (k + 1)] (HF θ X₀ k) :=
    (HF_adapted hc (stageMeas hc) k).mono (jitterFiltration.mono (Nat.le_succ k)) le_rfl
  have hv := valF_adapted hc (stageMeas hc) k
  have hp : MeasurableSet[jitterFiltration (k + 1)] (placedF θ X₀ k) :=
    jitterFiltration.mono (Nat.le_succ k) _ (placedF_adapted hc (stageMeas hc) k)
  have hset : MeasurableSet[jitterFiltration (k + 1)] {ω |
      placedAt (CM θ X₀ ω) k ∧
      Jlo X₀ m i - capH X₀ ((CM θ X₀ ω).slot (k + 1)) / 2 ≤ (CM θ X₀ ω).slot (k + 1) ∧
      (CM θ X₀ ω).slot (k + 1) ≤ Jhi X₀ m j + capH X₀ ((CM θ X₀ ω).slot (k + 1)) / 2 ∧
      Jlo X₀ m i ≤ primeValueOf (CM θ X₀ ω) (capH X₀) (Ucl ω) k ∧
      primeValueOf (CM θ X₀ ω) (capH X₀) (Ucl ω) k < Jhi X₀ m j} := by
    refine hp.inter ((measurableSet_le (measurable_const.sub (hH.div_const 2)) hs).inter
      ((measurableSet_le hs (measurable_const.add (hH.div_const 2))).inter
        ((measurableSet_le measurable_const hv).inter (measurableSet_lt hv measurable_const))))
  exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable

end Meas

end Queue6

end
