module

public import RequestProject.Beurling.Model.Stage

/-!
# The event `𝒩₌` of ties is null (§3.4)

"`𝒩₌` is null for every `ϑ_s`: after cancelling common factors, the latest-decided prime of such a
pair divides one side only, so it would have to land on a point fixed by the past, which has
probability `0` by the box-uniform landing law."

Formalized:
* `tie_pattern` : a tie between two distinct elements gives, after cancelling the common factor, a
  *pattern* `(k, a, r, g)`: the prime decided at relative slot `k + 1` (the latest one) satisfies
  `q_k^a · val(r) = val(g)`, where `r`, `g` only use rational primes and primes decided at earlier
  slots; if no jittered prime is involved, the two elements are integers and unique factorization
  applies (`num_inj`);
* `patEvent_null` : each pattern has probability `0` (`lintegral_landing`: given `F_k`, `q_k` has a
  density, and `{t > 0 : t^a c = d}` has at most one point);
* `tiesEvent_null` : `𝒩₌` is a countable union of such events (and the null event that a jitter
  leaves `[0, 1]`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The data `D_ω` of the constructed model. -/
noncomputable def DF (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) : PrimeData := DM (Mcl θ X₀ ω) (Ucl ω)

/-- Only earlier slots appear in `r`. -/
def EarlyIdx (k : ℕ) (r : PIdx X₀ →₀ ℕ) : Prop := ∀ j, r (Sum.inr j) ≠ 0 → j < k

/-- **The event of a tie pattern** `(k, a, r, g)`: a prime is placed at relative slot `k + 1`, the
elements `r`, `g` are live, and `q_k^a · val(r) = val(g)`. -/
def patEvent (θ : ℝ) (X₀ : ℕ) (k a : ℕ) (r g : PIdx X₀ →₀ ℕ) : Set JitterΩ :=
  {ω | ω ∈ placedF θ X₀ k ∧ Live (DF θ X₀ ω) r ∧ Live (DF θ X₀ ω) g ∧
    valF θ X₀ k ω ^ a * eval (DF θ X₀ ω) r = eval (DF θ X₀ ω) g}

lemma valF_pos (hc : Cond θ X₀) (k : ℕ) (ω : JitterΩ) : 0 < valF θ X₀ k ω := by
  have h := primeValueOf_ge (hc.std ω).limModel (U := Ucl ω) (fun j => clamp01_mem (ω j))
    hc.hX ((hc.std ω).limModel_low) k
  unfold valF; rw [Mcl_eq hc]
  linarith [X₀_ge_two_pow hc.hX, h.1, h.2]

/-- The root set `{(ω, t) : t > 0, t^a c(ω) = d(ω)}` is measurable for `m ⊗ Borel`. -/
lemma jmeas_root {Ω : Type*} {m : MeasurableSpace Ω} {c d : Ω → ℝ} (hc : Measurable c)
    (hd : Measurable d) (a : ℕ) :
    JMeas m ({p : Ω × ℝ | 0 < p.2 ∧ p.2 ^ a * c p.1 = d p.1}.indicator 1) := by
  unfold JMeas
  refine measurable_one.indicator ?_
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_eq_fun ((measurable_snd.pow_const a).mul (hc.comp measurable_fst))
      (hd.comp measurable_fst))

section Null

variable (hc : Cond θ X₀) (hm : StageMeas θ X₀)
include hc hm

lemma pval_adapted {k : ℕ} {i : PIdx X₀} (hi : ∀ j, i = Sum.inr j → j < k) :
    Measurable[jitterFiltration k] fun ω => pval (DF θ X₀ ω) i := by
  cases i with
  | inl p => exact measurable_const
  | inr j => exact valF_adapted_lt hc hm (hi j rfl)

lemma eval_adapted {k : ℕ} {r : PIdx X₀ →₀ ℕ} (hr : EarlyIdx k r) :
    Measurable[jitterFiltration k] fun ω => eval (DF θ X₀ ω) r := by
  unfold eval Finsupp.prod
  refine Finset.measurable_prod _ fun i hi => ?_
  refine (pval_adapted hc hm fun j hj => ?_).pow_const _
  subst hj
  exact hr j (Finsupp.mem_support_iff.mp hi)

lemma live_adapted {k : ℕ} {r : PIdx X₀ →₀ ℕ} (hr : EarlyIdx k r) :
    MeasurableSet[jitterFiltration k] {ω | Live (DF θ X₀ ω) r} := by
  classical
  have : {ω | Live (DF θ X₀ ω) r} = ⋂ j ∈ (r.support.preimage Sum.inr
      Sum.inr_injective.injOn : Finset ℕ), placedF θ X₀ j := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, Finset.mem_preimage, Finsupp.mem_support_iff]
    exact ⟨fun h j hj => h j hj, fun h j hj => h j hj⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  simp only [Finset.mem_preimage, Finsupp.mem_support_iff] at hj
  exact placedF_adapted_le hc hm (hr j hj).le

/-- **Each tie pattern has probability `0`.** -/
theorem patEvent_null {k a : ℕ} (ha : 1 ≤ a) {r g : PIdx X₀ →₀ ℕ} (hr : EarlyIdx k r)
    (hg : EarlyIdx k g) : jitterMeasure (patEvent θ X₀ k a r g) = 0 := by
  classical
  have hA : MeasurableSet[jitterFiltration k]
      (placedF θ X₀ k ∩ {ω | Live (DF θ X₀ ω) r}) :=
    (placedF_adapted hc hm k).inter (live_adapted hc hm hr)
  have hΦ := jmeas_root (eval_adapted hc hm hr) (eval_adapted hc hm hg) a
  set A := placedF θ X₀ k ∩ {ω | Live (DF θ X₀ ω) r}
  set B : Set (JitterΩ × ℝ) := {p | 0 < p.2 ∧ p.2 ^ a * eval (DF θ X₀ p.1) r =
    eval (DF θ X₀ p.1) g}
  set Φ : JitterΩ × ℝ → ℝ≥0∞ := B.indicator 1
  have hsub : patEvent θ X₀ k a r g ⊆
      {ω | A.indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω = 1} := by
    rintro ω ⟨hp, hlr, -, heq⟩
    have hωA : ω ∈ A := ⟨hp, hlr⟩
    have hpos : 0 < valF θ X₀ k ω := valF_pos hc k ω
    simp only [mem_setOf_eq, indicator_of_mem hωA, Φ]
    exact indicator_of_mem (show (ω, valF θ X₀ k ω) ∈ B from ⟨hpos, heq⟩) _
  have hint := lintegral_landing k (slotF_adapted hc hm k) (HF_adapted hc hm k) (HF_pos hc k)
    hA hΦ
  have hzero : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
      ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)) ω ∂jitterMeasure = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, Pi.zero_apply]
      have hc1 : 0 < eval (DF θ X₀ ω) r := lt_of_lt_of_le one_pos (one_le_eval
        (pos2_DM hc.hX (U := Ucl ω) (fun j => clamp01_mem (ω j)) (by rw [Mcl_eq hc]; exact
          (hc.std ω).limModel_low)).pos hω.2)
      have hsing : {t : ℝ | (ω, t) ∈ B}.Subsingleton := by
        rintro t ⟨ht0, ht⟩ t' ⟨ht0', ht'⟩
        have h1 : t ^ a = t' ^ a := mul_right_cancel₀ hc1.ne' (ht.trans ht'.symm)
        exact (pow_left_inj₀ ht0.le ht0'.le (by omega)).mp h1
      have hnull : volume {t : ℝ | (ω, t) ∈ B} = 0 := hsing.measure_zero _
      have : ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t) = 0 := by
        refine le_antisymm ?_ (zero_le _)
        calc ∫⁻ t in box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)
            ≤ ∫⁻ t, Φ (ω, t) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ t, {t : ℝ | (ω, t) ∈ B}.indicator 1 t := by
              congr 1
          _ = volume {t : ℝ | (ω, t) ∈ B} :=
              lintegral_indicator_one₀ (NullMeasurableSet.of_null hnull)
          _ = 0 := hnull
      rw [this, mul_zero]
    · simp [indicator_of_notMem hω]
  rw [hzero] at hint
  have hmeasf : Measurable fun ω => A.indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω := by
    have hv := valF_measurable hc hm k
    have hcg : Measurable fun ω => eval (DF θ X₀ ω) r :=
      (eval_adapted hc hm hr).mono (jitterFiltration.le k) le_rfl
    have hdg : Measurable fun ω => eval (DF θ X₀ ω) g :=
      (eval_adapted hc hm hg).mono (jitterFiltration.le k) le_rfl
    have hset : MeasurableSet {ω | 0 < valF θ X₀ k ω ∧
        valF θ X₀ k ω ^ a * eval (DF θ X₀ ω) r = eval (DF θ X₀ ω) g} :=
      (measurableSet_lt measurable_const hv).inter
        (measurableSet_eq_fun ((hv.pow_const a).mul hcg) hdg)
    have h1 : (fun ω => Φ (ω, valF θ X₀ k ω)) = {ω | 0 < valF θ X₀ k ω ∧
        valF θ X₀ k ω ^ a * eval (DF θ X₀ ω) r = eval (DF θ X₀ ω) g}.indicator 1 := by
      funext ω; simp [Φ, B, Set.indicator]
    rw [h1]
    exact (measurable_one.indicator hset).indicator (jitterFiltration.le k _ hA)
  have hzero' : ∫⁻ ω, A.indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω ∂jitterMeasure = 0 := by
    rw [← hint]; rfl
  rw [lintegral_eq_zero_iff hmeasf] at hzero'
  refine measure_mono_null (fun ω hω => hsub hω) (measure_eq_zero_iff_ae_notMem.mpr ?_)
  filter_upwards [hzero'] with ω hω
  simp only [Pi.zero_apply] at hω ⊢
  rw [hω]; exact zero_ne_one

end Null

/-! ### Ties give patterns -/

lemma idxVal_add (M : SlotModel X₀) (U : ℕ → ℝ) (e f : RealisedIdx M →₀ ℕ) :
    idxVal M (capH X₀) U (e + f) = idxVal M (capH X₀) U e * idxVal M (capH X₀) U f := by
  unfold idxVal
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- The decision key of a realised index (rational primes first). -/
def rkey {M : SlotModel X₀} : RealisedIdx M → ℕ
  | Sum.inl _ => 0
  | Sum.inr k => k.1 + 1

/-- **A tie gives a pattern** (cancel the common factor; the latest prime divides one side). -/
theorem tie_pattern (hc : Cond θ X₀) {ω : JitterΩ}
    (hT : ¬ TieFree (Mcl θ X₀ ω) (Ucl ω)) :
    ∃ k a : ℕ, ∃ r g : PIdx X₀ →₀ ℕ, 1 ≤ a ∧ EarlyIdx k r ∧ EarlyIdx k g ∧
      ω ∈ patEvent θ X₀ k a r g := by
  classical
  set M := Mcl θ X₀ ω with hMdef
  set U := Ucl ω
  have hlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    rw [hMdef, Mcl_eq hc]; exact (hc.std ω).limModel_low
  have hv2 : ∀ i, 2 ≤ realisedVal M (capH X₀) U i :=
    realisedVal_ge_two (fun j => clamp01_mem (ω j)) hc.hX hlow
  unfold TieFree at hT
  push_neg at hT
  obtain ⟨e, e', hval, hne⟩ := hT
  set c₀ := e ⊓ e'
  set g := e - c₀
  set g' := e' - c₀
  have he : e = c₀ + g := by
    ext i; simp only [g, c₀, Finsupp.coe_add, Finsupp.coe_tsub, Finsupp.inf_apply,
      Pi.add_apply, Pi.sub_apply]; omega
  have he' : e' = c₀ + g' := by
    ext i; simp only [g', c₀, Finsupp.coe_add, Finsupp.coe_tsub, Finsupp.inf_apply,
      Pi.add_apply, Pi.sub_apply]; omega
  have hdisj : ∀ i, g i = 0 ∨ g' i = 0 := by
    intro i; simp only [g, g', c₀, Finsupp.coe_tsub, Finsupp.inf_apply, Pi.sub_apply]; omega
  have hc0 : 0 < idxVal M (capH X₀) U c₀ := by
    unfold idxVal Finsupp.prod
    exact Finset.prod_pos fun i _ => pow_pos (by linarith [hv2 i]) _
  have hgg : idxVal M (capH X₀) U g = idxVal M (capH X₀) U g' := by
    rw [he, he', idxVal_add, idxVal_add] at hval
    exact mul_left_cancel₀ hc0.ne' hval
  have hgne : g ≠ g' := fun h => hne (by rw [he, he', h])
  -- some jittered prime is involved
  by_cases hrat : RatOnly g ∧ RatOnly g'
  · exfalso
    apply hgne
    refine num_inj hrat.1 hrat.2 ?_
    have := hgg
    rw [idxVal_ratOnly _ _ hrat.1, idxVal_ratOnly _ _ hrat.2] at this
    exact_mod_cast this
  -- the latest prime
  have hSne : (g + g').support.Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at h0
    apply hrat
    constructor <;> intro k <;> have := congrArg (fun f => f (Sum.inr k)) h0 <;>
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this <;>
      omega
  obtain ⟨i₀, hi₀, hmax⟩ := (g + g').support.exists_max_image rkey hSne
  have hnr : ∃ k, g (Sum.inr k) ≠ 0 ∨ g' (Sum.inr k) ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hrat ⟨fun k => (hc' k).1, fun k => (hc' k).2⟩
  obtain ⟨k₁, hk₁⟩ := hnr
  have hk₁s : Sum.inr k₁ ∈ (g + g').support := by
    rw [Finsupp.mem_support_iff]
    simp only [Finsupp.coe_add, Pi.add_apply]; omega
  obtain ⟨K, rfl⟩ : ∃ K, i₀ = Sum.inr K := by
    cases i₀ with
    | inl p =>
      have := hmax _ hk₁s
      simp [rkey] at this
    | inr K => exact ⟨K, rfl⟩
  have hle : ∀ j, (g (Sum.inr j) ≠ 0 ∨ g' (Sum.inr j) ≠ 0) → j.1 ≤ K.1 := by
    intro j hj
    have hjs : Sum.inr j ∈ (g + g').support := by
      rw [Finsupp.mem_support_iff]
      simp only [Finsupp.coe_add, Pi.add_apply]; omega
    have := hmax _ hjs
    simp only [rkey] at this
    omega
  -- orient the pair
  obtain ⟨G, G', hGG, hGK, hG'K, hGle, hG'le⟩ : ∃ G G' : RealisedIdx M →₀ ℕ,
      idxVal M (capH X₀) U G = idxVal M (capH X₀) U G' ∧ G (Sum.inr K) ≠ 0 ∧
      G' (Sum.inr K) = 0 ∧ (∀ j, G (Sum.inr j) ≠ 0 → j.1 ≤ K.1) ∧
      (∀ j, G' (Sum.inr j) ≠ 0 → j.1 ≤ K.1) := by
    have hKs := Finsupp.mem_support_iff.mp hi₀
    simp only [Finsupp.coe_add, Pi.add_apply] at hKs
    by_cases hgK : g (Sum.inr K) ≠ 0
    · refine ⟨g, g', hgg, hgK, ?_, fun j hj => hle j (Or.inl hj),
        fun j hj => hle j (Or.inr hj)⟩
      rcases hdisj (Sum.inr K) with h | h
      · exact absurd h hgK
      · exact h
    · push_neg at hgK
      refine ⟨g', g, hgg.symm, by omega, hgK, fun j hj => hle j (Or.inr hj),
        fun j hj => hle j (Or.inl hj)⟩
  set a := G (Sum.inr K)
  set R := G - Finsupp.single (Sum.inr K) a
  have hGR : G = R + Finsupp.single (Sum.inr K) a := by
    ext i
    simp only [R, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hi : i = Sum.inr K
    · subst hi; simp [a]
    · simp [Ne.symm hi]
  have hRK : R (Sum.inr K) = 0 := by simp [R, a]
  refine ⟨K.1, a, mapE M R, mapE M G', Nat.one_le_iff_ne_zero.mpr hGK, ?_, ?_, ?_⟩
  · intro j hj
    rw [mapE_apply_inr] at hj
    split_ifs at hj with hpl
    · have hGj : G (Sum.inr ⟨j, hpl⟩) ≠ 0 := by
        intro h0
        apply hj
        simp only [R, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
      have h1 := hGle _ hGj
      have h2 : (⟨j, hpl⟩ : {k // placedAt M k}) ≠ K := by
        rintro rfl; exact hj hRK
      have h3 : j ≠ K.1 := fun h => h2 (Subtype.ext h)
      exact lt_of_le_of_ne h1 h3
    · exact absurd rfl hj
  · intro j hj
    rw [mapE_apply_inr] at hj
    split_ifs at hj with hpl
    · have h1 := hG'le _ hj
      have h3 : j ≠ K.1 := by
        intro h
        have : (⟨j, hpl⟩ : {k // placedAt M k}) = K := Subtype.ext h
        rw [this] at hj; exact hj hG'K
      exact lt_of_le_of_ne h1 h3
    · exact absurd rfl hj
  · refine ⟨K.2, live_mapE M U R, live_mapE M U G', ?_⟩
    show primeValueOf M (capH X₀) U K.1 ^ a * eval (DM M U) (mapE M R) =
      eval (DM M U) (mapE M G')
    rw [eval_mapE, eval_mapE, ← hGG, hGR, idxVal_add]
    have : idxVal M (capH X₀) U (Finsupp.single (Sum.inr K) a) =
        primeValueOf M (capH X₀) U K.1 ^ a := by
      simp [idxVal, Finsupp.prod_single_index]; rfl
    rw [this, mul_comm]

/-- **`𝒩₌` is null** (given the measurability of the construction, `StageMeas`). -/
theorem tiesEvent_null (hc : Cond θ X₀) (hm : StageMeas θ X₀) :
    jitterMeasure (tiesEvent θ X₀) = 0 := by
  classical
  have hS : jitterMeasure {ω : JitterΩ | ¬ ∀ j, ω j ∈ Icc (0 : ℝ) 1} = 0 := by
    have := ae_jitter_mem
    rwa [Filter.Eventually, mem_ae_iff] at this
  have hsub : tiesEvent θ X₀ ⊆ {ω : JitterΩ | ¬ ∀ j, ω j ∈ Icc (0 : ℝ) 1} ∪
      ⋃ p : ℕ × ℕ × (PIdx X₀ →₀ ℕ) × (PIdx X₀ →₀ ℕ),
        ⋃ (_ : 1 ≤ p.2.1 ∧ EarlyIdx p.1 p.2.2.1 ∧ EarlyIdx p.1 p.2.2.2),
          patEvent θ X₀ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    rintro ω ⟨-, hT⟩
    by_cases hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1
    · right
      have hT' : ¬ TieFree (Mcl θ X₀ ω) (Ucl ω) := by
        unfold Mcl; rw [Ucl_eq hω]; exact hT
      obtain ⟨k, a, r, g, ha, hr, hg, hp⟩ := tie_pattern hc hT'
      exact mem_iUnion.mpr ⟨(k, a, r, g), mem_iUnion.mpr ⟨⟨ha, hr, hg⟩, hp⟩⟩
    · exact Or.inl hω
  refine measure_mono_null hsub (measure_union_null hS (measure_iUnion_null fun p => ?_))
  refine measure_iUnion_null fun hp => ?_
  exact patEvent_null hc hm hp.1 hp.2.1 hp.2.2

end BModel

end
