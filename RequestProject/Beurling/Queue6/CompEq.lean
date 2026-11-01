module

public import RequestProject.Beurling.Queue6.CondEq

/-!
# The compensator identification, two-sided (§5.3, "`Comp` is the predictable compensator")

For the prime decided at relative slot `k + 1` and a window `[α, β)`:

* `ncard_xsetP_eq` : on `A_k`, `X_q([α, β)) = Φᴬ_k(ω, q)` exactly (the composites `n = q m`,
  `q ‖ n`, with latest prime `q` are in bijection with the cofactors `m ∈ cofP k`,
  `m ↦ m + e_q`): the equality form of `Xt_le_PhiA`;
* `boxMean_eq_compTerm` : `G_k = ∫_{[α, β)} c_k` exactly (the equality form of
  `boxMean_le_compTerm`);
* `condExp_X3_eq` : `E[min(X_q, C) | 𝓕_k] = 1_{A_k} H_k⁻¹ ∫_{box} min(Φᴬ_k, C)` a.s.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction RankFull CaplLink QueueMono
  Absorbed SlotModel AbsorbEmpty Target
open scoped ENNReal

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

omit hc in
/-- `latP (e' + e_k) = k` when every jittered prime of `e'` is decided before `k`. -/
lemma latP_add_single {e : PIdx X₀ →₀ ℕ} {k : ℕ}
    (he : ∀ j, e (Sum.inr j) ≠ 0 → j < k) :
    latP (e + Finsupp.single (Sum.inr k) 1) = k := by
  classical
  apply le_antisymm
  · apply csSup_le ⟨k, by simp⟩
    intro j hj
    simp only [mem_setOf_eq, Finsupp.coe_add, Pi.add_apply] at hj
    by_cases hjk : j = k
    · exact hjk.le
    · rw [Finsupp.single_apply, if_neg (fun h => hjk (Sum.inr_injective h).symm),
        add_zero] at hj
      exact (he j hj).le
  · apply latP_le
    simp

/-- **`X_q([α, β)) = Φᴬ_k(ω, q)`** on `A_k`. -/
theorem ncard_xsetP_eq (a b : ℝ) (k : ℕ) {ω : JitterΩ} (hA : ω ∈ lawA θ X₀ k) :
    ((xsetP θ X₀ a b k (· = 1) ω).ncard : ℝ≥0∞) = PhiA θ X₀ k a b (ω, valF θ X₀ k ω) := by
  classical
  set Xs := xsetP θ X₀ a b k (· = 1) ω with hXs
  have hval : valF θ X₀ k ω = (DD θ X₀ ω).v k := rfl
  have hq0 : 0 < valF θ X₀ k ω := valF_pos hc k ω
  set S : Set (PIdx X₀ →₀ ℕ) := {e' | e' ∈ cofP θ X₀ k ω ∧
    a ≤ eval (DD θ X₀ ω) e' * valF θ X₀ k ω ∧ eval (DD θ X₀ ω) e' * valF θ X₀ k ω < b ∧
    ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) e' * valF θ X₀ k ω) ∧
      valF θ X₀ k ω < absorbY X₀ (eval (DD θ X₀ ω) e' * valF θ X₀ k ω))}
  have hSfin : S.Finite := by
    refine (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
      (b / valF θ X₀ k ω)).subset fun e' he' => ?_
    refine ⟨he'.1.1, pval_gt_one hc he'.1.1, ?_⟩
    rw [le_div_iff₀ hq0]; exact he'.2.2.1.le
  have hPhi : PhiA θ X₀ k a b (ω, valF θ X₀ k ω) = (S.ncard : ℝ≥0∞) := by
    unfold PhiA
    rw [if_pos (valF_ge_Xm hc k ω)]
    rw [← tsum_ite_eq_ncard hSfin]
    exact tsum_congr fun e => by
      by_cases h : e ∈ S
      · rw [if_pos h]; exact if_pos h
      · rw [if_neg h]; exact if_neg h
  rw [hPhi]
  set g : (PIdx X₀ →₀ ℕ) → (PIdx X₀ →₀ ℕ) := fun e => e + Finsupp.single (Sum.inr k) 1
  have hplaced : placedAt (CM θ X₀ ω) k := hA.1
  have hmaps : Set.MapsTo g S Xs := by
    intro e he
    obtain ⟨⟨hlive, hne, hlt⟩, h1, h2, h3⟩ := he
    have hk0 : e (Sum.inr k) = 0 := by
      by_contra h0; exact lt_irrefl k (hlt k h0)
    have hev : eval (DD θ X₀ ω) (g e) = eval (DD θ X₀ ω) e * valF θ X₀ k ω := by
      simp only [g]; rw [eval_add_single, pow_one]; rfl
    have hlat := latP_add_single hlt
    refine ⟨fun j hj => ?_, ?_, by rw [hev]; exact h1, by rw [hev]; exact h2,
      ⟨k, by simp [g]⟩, ?_, hlat, by simp [g, hk0]⟩
    · by_cases hjk : j = k
      · subst hjk; exact hplaced
      · apply hlive j
        simp only [g] at hj
        rw [Finsupp.add_apply, Finsupp.single_apply,
          if_neg (fun h => hjk (Sum.inr_injective h).symm), add_zero] at hj
        exact hj
    · have hs : 1 ≤ e.sum (fun _ n => n) := by
        obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
          by_contra h; push_neg at h; exact hne (Finsupp.ext h)
        have : e i ≤ e.sum (fun _ n => n) := by
          unfold Finsupp.sum
          exact Finset.single_le_sum (f := fun i => e i) (fun _ _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.mpr hi)
        omega
      simp only [g]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
      omega
    · rw [hlat, hev]; exact h3
  have hinj : Set.InjOn g S := fun e1 _ e2 _ h => by
    simpa [g] using h
  have hsurj : Set.SurjOn g S Xs := by
    intro e he
    have hk : e (Sum.inr k) = 1 := he.2.2.2.2.2.2.2
    set e' := e - Finsupp.single (Sum.inr k) 1
    have hsplit : e = e' + Finsupp.single (Sum.inr k) 1 := by
      ext i
      simp only [e', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases hi : i = Sum.inr k
      · subst hi; simp [hk]
      · simp [Ne.symm hi]
    refine ⟨e', ?_, hsplit.symm⟩
    have hev : eval (DD θ X₀ ω) e = eval (DD θ X₀ ω) e' * valF θ X₀ k ω := by
      conv_lhs => rw [hsplit]
      rw [eval_add_single, pow_one]; rfl
    refine ⟨⟨fun j hj => he.1 j ?_, ?_, fun j hj => ?_⟩, ?_, ?_⟩
    · intro h0; apply hj
      simp only [e', Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
    · intro h0
      have hs := he.2.1
      rw [hsplit, h0, zero_add, Finsupp.sum_single_index rfl] at hs
      omega
    · have hj' : e (Sum.inr j) ≠ 0 := by
        intro h0; apply hj
        simp only [e', Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
      have hle := latP_le hj'
      rw [he.2.2.2.2.2.2.1] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · subst h
        exfalso; apply hj
        simp [e', hk]
    · rw [← hev]; exact he.2.2.1
    · refine ⟨by rw [← hev]; exact he.2.2.2.1, ?_⟩
      rw [← hev]
      have h6 := he.2.2.2.2.2.1
      rwa [he.2.2.2.2.2.2.1] at h6
  have himg : g '' S = Xs := Set.Subset.antisymm (Set.image_subset_iff.mpr hmaps) hsurj
  rw [← himg, hinj.ncard_image]

/-- **`ofReal(X_q) = 1_{A_k} Φᴬ_k(·, q)`** on the good stage `k`. -/
theorem Xcount_eq_PhiA (a b : ℝ) (k : ℕ) {ω : JitterΩ} (hω : ω ∈ stageGood θ X₀ k) :
    ENNReal.ofReal (Xcount (CM θ X₀ ω) (Ucl ω) a b k 1) =
      (lawA θ X₀ k).indicator (fun ω => PhiA θ X₀ k a b (ω, valF θ X₀ k ω)) ω := by
  classical
  have hX : Xcount (CM θ X₀ ω) (Ucl ω) a b k 1 = ((xsetP θ X₀ a b k (· = 1) ω).ncard : ℝ) := by
    unfold Xcount xset
    exact_mod_cast ncard_xset (θ := θ) (X₀ := X₀) a b k (· = 1) ω
  rw [hX, ENNReal.ofReal_natCast]
  by_cases hA : ω ∈ lawA θ X₀ k
  · rw [Set.indicator_of_mem hA]; exact ncard_xsetP_eq hc a b k hA
  · rw [Set.indicator_of_notMem hA]
    have hne : xsetP θ X₀ a b k (· = 1) ω = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro e he
      apply hA
      have h1 := he.1 k (by rw [he.2.2.2.2.2.2.2]; norm_num)
      exact ⟨h1, hω⟩
    rw [hne, Set.ncard_empty]; simp

include hc in
/-- **`G_k = ∫_{[α, β)} c_k`** (the equality form of `boxMean_le_compTerm`). -/
theorem boxMean_eq_compTerm (hev : Even X₀) (k : ℕ) (a b : ℝ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiA θ X₀ k a b) ω =
      ∫⁻ y in Ico a b, compTerm θ X₀ k ω y := by
  classical
  unfold boxMean compTerm
  by_cases hA : ω ∈ lawA θ X₀ k
  swap
  · show (lawA θ X₀ k).indicator _ ω = _
    rw [indicator_of_notMem hA]
    symm
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    show (lawA θ X₀ k).indicator _ ω = 0
    rw [indicator_of_notMem hA]
  show (lawA θ X₀ k).indicator _ ω = _
  simp only [indicator_of_mem hA]
  set H := HF θ X₀ k ω
  set B := RankFull.box (slotF θ X₀ k ω) H
  have hB : MeasurableSet B := measurableSet_Ico
  rw [lintegral_const_mul _ (by
    refine Measurable.ennreal_tsum fun w => ?_
    have hd : Measurable fun y : ℝ => y / eval (DD θ X₀ ω) w := measurable_id.div_const _
    refine Measurable.ite ?_ ((measurable_one.indicator hB).comp hd |>.mul measurable_const)
      measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl))]
  congr 1
  -- expand both sides over the cofactors
  have hL : ∫⁻ t in B, PhiA θ X₀ k a b (ω, t) = ∑' w : PIdx X₀ →₀ ℕ, ∫⁻ t, B.indicator
      (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧ a ≤ eval (DD θ X₀ ω) w * t ∧
        eval (DD θ X₀ ω) w * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
          t < absorbY X₀ (eval (DD θ X₀ ω) w * t))) then (1 : ℝ≥0∞) else 0) t := by
    rw [← lintegral_indicator hB, ← lintegral_tsum]
    · refine lintegral_congr fun t => ?_
      unfold PhiA
      by_cases ht : t ∈ B
      · simp only [indicator_of_mem ht]
        by_cases hX : Xm X₀ ≤ t
        · rw [if_pos hX]
          exact tsum_congr fun w => by
            by_cases h : w ∈ cofP θ X₀ k ω ∧ a ≤ eval (DD θ X₀ ω) w * t ∧
                eval (DD θ X₀ ω) w * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
                  t < absorbY X₀ (eval (DD θ X₀ ω) w * t))
            · rw [if_pos h, if_pos ⟨hX, h⟩]
            · rw [if_neg h, if_neg fun h' => h h'.2]
        · rw [if_neg hX]
          symm; exact ENNReal.tsum_eq_zero.mpr fun w => if_neg fun h' => hX h'.1
      · simp only [indicator_of_notMem ht, tsum_zero]
    · intro w
      refine (Measurable.indicator ?_ hB).aemeasurable
      have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) w * t := measurable_const.mul measurable_id
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_le measurable_const measurable_id).inter ((MeasurableSet.const _).inter
        ((measurableSet_le measurable_const hm).inter ((measurableSet_lt hm measurable_const).inter
          ((measurableSet_le measurable_const (Real.measurable_log.comp hm)).inter
            (measurableSet_lt measurable_id ((absorbY_monotone hc.hX).measurable.comp hm))).compl)))
  change ∫⁻ t in B, PhiA θ X₀ k a b (ω, t) = _
  rw [hL, lintegral_tsum]
  swap
  · intro w
    have hd : Measurable fun y : ℝ => y / eval (DD θ X₀ ω) w := measurable_id.div_const _
    refine (Measurable.ite ?_ ((measurable_one.indicator hB).comp hd |>.mul measurable_const)
      measurable_const).aemeasurable
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl)
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ cofP θ X₀ k ω
  swap
  · have : (fun t => B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧
        a ≤ eval (DD θ X₀ ω) w * t ∧ eval (DD θ X₀ ω) w * t < b ∧
        ¬ (10 ^ 7 ≤ Real.log (eval (DD θ X₀ ω) w * t) ∧
          t < absorbY X₀ (eval (DD θ X₀ ω) w * t))) then (1 : ℝ≥0∞) else 0) t) = 0 := by
      funext t
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, if_neg fun h => hw h.2.1]; rfl
      · rw [indicator_of_notMem ht]; rfl
    rw [this, lintegral_zero_fun]
    symm
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    show (if w ∈ cofP θ X₀ k ω ∧ _ then _ else _) = 0
    rw [if_neg fun h => hw h.1]
  set e := eval (DD θ X₀ ω) w with he
  have he0 : 0 < e := eval_pos hc hw.1
  set h : ℝ → ℝ≥0∞ := (Ico a b).indicator fun y => if Xm X₀ ≤ y / e ∧
    ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y) then B.indicator 1 (y / e) else 0 with hh
  have hhm : Measurable h := by
    have hd : Measurable fun y : ℝ => y / e := measurable_id.div_const _
    refine Measurable.indicator (Measurable.ite ?_ ((measurable_one.indicator hB).comp hd)
      measurable_const) measurableSet_Ico
    exact (measurableSet_le measurable_const hd).inter
      ((measurableSet_le measurable_const Real.measurable_log).inter
        (measurableSet_lt hd (absorbY_monotone hc.hX).measurable)).compl
  have hpt : ∀ t, B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧
      a ≤ e * t ∧ e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))) then
        (1 : ℝ≥0∞) else 0) t = h (e * t) := by
    intro t
    have hdiv : e * t / e = t := by field_simp
    rw [hh]
    by_cases hI : e * t ∈ Ico a b
    · rw [indicator_of_mem hI]
      simp only [hdiv]
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        by_cases hc' : Xm X₀ ≤ t ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))
        · rw [if_pos ⟨hc'.1, hw, hI.1, hI.2, hc'.2⟩, if_pos hc']; rfl
        · rw [if_neg fun h' => hc' ⟨h'.1, h'.2.2.2.2⟩, if_neg hc']
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]; split_ifs <;> rfl
    · rw [indicator_of_notMem hI]
      by_cases ht : t ∈ B
      · rw [indicator_of_mem ht, if_neg fun h' => hI ⟨h'.2.2.1, h'.2.2.2.1⟩]
      · rw [indicator_of_notMem ht]
  calc ∫⁻ t, B.indicator (fun t => if Xm X₀ ≤ t ∧ (w ∈ cofP θ X₀ k ω ∧ a ≤ e * t ∧
        e * t < b ∧ ¬ (10 ^ 7 ≤ Real.log (e * t) ∧ t < absorbY X₀ (e * t))) then
          (1 : ℝ≥0∞) else 0) t
      = ∫⁻ t, h (e * t) := lintegral_congr hpt
    _ = ENNReal.ofReal e⁻¹ * ∫⁻ y, h y := BModel.lintegral_comp_mul he0 hhm
    _ = ∫⁻ y in Ico a b, (if w ∈ cofP θ X₀ k ω ∧ Xm X₀ ≤ y / e ∧
          ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y) then
          B.indicator 1 (y / e) * ENNReal.ofReal e⁻¹ else 0) := by
        rw [← lintegral_const_mul _ hhm, hh, ← lintegral_indicator measurableSet_Ico]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ Ico a b
        · rw [indicator_of_mem hy, indicator_of_mem hy]
          by_cases hc' : Xm X₀ ≤ y / e ∧ ¬ (10 ^ 7 ≤ Real.log y ∧ y / e < absorbY X₀ y)
          · rw [if_pos hc', if_pos ⟨hw, hc'⟩, mul_comm]
          · rw [if_neg hc', if_neg fun h' => hc' h'.2, mul_zero]
        · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]


end Queue6

end
