module

public import RequestProject.Beurling.Queue6.TruncAll
public import RequestProject.Beurling.Queue6.WinCount

/-!
# The compensator of the E3 counts is `∫_W c` (two-sided), on the cluster event

For a window `W = [a, b)` of `𝒲'_u` and the truncated counts `X̃_k = min(X_q(W), 2M₁(u))`
(`X3`) of Lemma 5.22:

* `condExp_X3_eq` : `E[X̃_k | 𝓕_k] = 1_{A_k} H_k⁻¹ ∫_{box} min(Φᴬ_k, 2M₁)` a.s. (`condExp_eq_boxMean`
  with the exact count `Xcount_eq_PhiA`);
* `compE3_eq` : a.s., on the cluster event at the height `u`, `X̃_k = X_q(W)` for every `k`
  and, for all large `n`, `∑_{k<n} E[X̃_k | 𝓕_k] = Comp(W) = ∫_W c` (truncation is inactive at
  every offset, `PhiA_le_trunc`; `boxMean_eq_compTerm`; the slots above `2b + 2` contribute
  nothing).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction RankFull CaplLink QueueMono
  Absorbed SlotModel AbsorbEmpty
open scoped ENNReal

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)

/-- `S`-restrictions of `min(Φ, c)` are jointly measurable. -/
lemma jmeas_min (k : ℕ) {Φ : JitterΩ × ℝ → ℝ≥0∞}
    (hΦ : ∀ S, MeasurableSet[jitterFiltration k] S →
      JMeas (jitterFiltration k) fun p => S.indicator 1 p.1 * Φ p) (c : ℝ≥0∞) :
    ∀ S, MeasurableSet[jitterFiltration k] S →
      JMeas (jitterFiltration k) fun p => S.indicator 1 p.1 * min (Φ p) c := by
  intro S hS
  have h1 := hΦ S hS
  have h0 := hΦ univ MeasurableSet.univ
  unfold JMeas at h1 h0 ⊢
  letI mP : MeasurableSpace (JitterΩ × ℝ) :=
    @Prod.instMeasurableSpace JitterΩ ℝ (jitterFiltration k) _
  have hfst : @Measurable _ _ mP (jitterFiltration k) Prod.fst :=
    @measurable_fst _ _ (jitterFiltration k) _
  have hi : Measurable[jitterFiltration k] (S.indicator (1 : JitterΩ → ℝ≥0∞)) :=
    measurable_const.indicator hS
  have hind : Measurable fun p : JitterΩ × ℝ => S.indicator (1 : JitterΩ → ℝ≥0∞) p.1 :=
    hi.comp hfst
  have e : (fun p : JitterΩ × ℝ => S.indicator 1 p.1 * min (Φ p) c) =
      fun p => S.indicator 1 p.1 * min ((univ : Set JitterΩ).indicator 1 p.1 * Φ p) c := by
    funext p; simp
  rw [e]
  exact hind.mul (h0.min measurable_const)

include hc hev in
/-- **`E[X̃_k | 𝓕_k] = 1_{A_k} H_k⁻¹ ∫_{box} min(Φᴬ_k, 2M₁)`** a.s. -/
theorem condExp_X3_eq (m : ℕ) {a b : ℤ} (hab : (a : ℝ) ≤ b) (k : ℕ) :
    jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k] =ᵐ[jitterMeasure]
      fun ω => (boxMean (constructionLaw hc hev) k
        (fun p => min (PhiA θ X₀ k a b p) (ENNReal.ofReal (2 * capM1 X₀ (uS X₀ m)))) ω).toReal := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hu := X₀_le_uS (X₀ := X₀) (by linarith [one_lt_of_logX hX0 hc.hX]) m
  have hC : 0 ≤ 2 * capM1 X₀ (uS X₀ m) := by
    have := QueueBound.one_le_capM1 hX0 hc.hX hu; linarith
  set C := 2 * capM1 X₀ (uS X₀ m)
  refine condExp_eq_boxMean hc hev k hC (fun ω => le_min (Nat.cast_nonneg _) hC)
    (fun ω => min_le_right _ _)
    (((xcount_adapted hc a b k 1).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    (jmeas_min k (fun S hS => PhiA_jmeas hc k a b S hS) _) ?_ ?_
  · filter_upwards [ae_stageGood hc] with ω hω
    have h := Xcount_eq_PhiA hc a b k (hω k)
    unfold Xcount at h
    show ENNReal.ofReal (min _ _) = _
    rw [ENNReal.ofReal_min, h]
    by_cases hA : ω ∈ lawA θ X₀ k
    · simp [Set.indicator_of_mem hA]
    · simp [Set.indicator_of_notMem hA]
  · intro ω
    unfold boxMean
    by_cases hA : ω ∈ (constructionLaw hc hev).A k
    · rw [Set.indicator_of_mem hA]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _ in box ((constructionLaw hc hev).c k ω)
        ((constructionLaw hc hev).H k ω), ENNReal.ofReal C) ?_
        (lintegral_mono fun t => min_le_right _ _)
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
        unfold box; rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    · rw [Set.indicator_of_notMem hA]; exact ENNReal.zero_ne_top

include hc in
lemma boxMean_min_ne_top (k : ℕ) (C : ℝ) (ω : JitterΩ) {a b : ℝ} :
    boxMean (constructionLaw hc hev) k
      (fun p => min (PhiA θ X₀ k a b p) (ENNReal.ofReal C)) ω ≠ ∞ := by
  unfold boxMean
  by_cases hA : ω ∈ (constructionLaw hc hev).A k
  · rw [Set.indicator_of_mem hA]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in box ((constructionLaw hc hev).c k ω)
      ((constructionLaw hc hev).H k ω), ENNReal.ofReal C) ?_
      (lintegral_mono fun t => min_le_right _ _)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      unfold box; rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  · rw [Set.indicator_of_notMem hA]; exact ENNReal.zero_ne_top

include hc in
/-- `Φᴬ_k(ω, ·) = 0` on the box of a slot above `2b + 2`. -/
lemma PhiA_zero_high (k : ℕ) (a b : ℝ) (ω : JitterΩ) (hk : 2 * b + 2 < slotF θ X₀ k ω) {t : ℝ}
    (ht : t ∈ box (slotF θ X₀ k ω) (HF θ X₀ k ω)) : PhiA θ X₀ k a b (ω, t) = 0 := by
  classical
  have hH := capH_le_div hc.hX (slotF_ge hc k ω)
  have hs0 : 0 ≤ slotF θ X₀ k ω := by linarith [slotF_ge hc k ω, Nat.cast_nonneg (α := ℝ) X₀]
  have htb : b + 1 < t := by
    have h1 := ht.1
    unfold HF at h1
    linarith
  unfold PhiA
  split_ifs with hX
  · refine ENNReal.tsum_eq_zero.mpr fun e => if_neg ?_
    rintro ⟨⟨hlive, hne, -⟩, -, h2, -⟩
    have h1 := one_lt_eval hc hlive hne
    have ht0 : 0 < t := by
      have h3 := ht.1
      unfold HF at h3
      have := X₀_ge_two_pow hc.hX
      have := slotF_ge hc k ω
      linarith
    have : t < eval (DD θ X₀ ω) e * t := by nlinarith
    linarith
  · rfl

set_option maxHeartbeats 800000 in
include hc hev in
/-- **The compensator of the E3 counts is `Comp(W) = ∫_W c`**, a.s. on the cluster event at the
height `u`, and the truncation is inactive there. -/
theorem compE3_eq {m : ℕ} {a b : ℤ} (hW : AdmW X₀ m a b) :
    ∀ᵐ ω ∂jitterMeasure, ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (capM1 X₀ (uS X₀ m)) →
      (∀ k, X3 θ X₀ m a b k ω = Xcount (CM θ X₀ ω) (Ucl ω) a b k 1) ∧
      ∃ N, ∀ n ≥ N, ∑ k ∈ Finset.range n,
        (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω =
          ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hu := X₀_le_uS (X₀ := X₀) (by linarith [one_lt_of_logX hX0 hc.hX]) m
  have hab : (a : ℝ) ≤ b := by have := hW.2.1; exact_mod_cast this.le
  have hC : 0 ≤ 2 * capM1 X₀ (uS X₀ m) := by
    have := QueueBound.one_le_capM1 hX0 hc.hX hu; linarith
  set C := 2 * capM1 X₀ (uS X₀ m)
  set J := constructionLaw hc hev
  filter_upwards [ae_all_iff.mpr (condExp_X3_eq hc hev m hab), ae_stageGood hc]
    with ω hω hsg hcl
  have htr := PhiA_le_trunc hc hW ω
  -- the truncation is inactive
  have hX3 : ∀ k, X3 θ X₀ m a b k ω = Xcount (CM θ X₀ ω) (Ucl ω) a b k 1 := by
    intro k
    have h := Xcount_eq_PhiA hc a b k (hsg k)
    have hle : Xcount (CM θ X₀ ω) (Ucl ω) a b k 1 ≤ C := by
      have : ENNReal.ofReal (Xcount (CM θ X₀ ω) (Ucl ω) a b k 1) ≤ ENNReal.ofReal C := by
        rw [h]
        by_cases hA : ω ∈ lawA θ X₀ k
        · rw [Set.indicator_of_mem hA]; exact htr k hcl _
        · rw [Set.indicator_of_notMem hA]; exact zero_le _
      exact (ENNReal.ofReal_le_ofReal_iff hC).mp this
    unfold X3; exact min_eq_left hle
  refine ⟨hX3, ?_⟩
  -- each conditional mean is the compensator mass of its slot
  have hbm : ∀ k, boxMean J k (fun p => min (PhiA θ X₀ k a b p) (ENNReal.ofReal C)) ω =
      ∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y := by
    intro k
    rw [← boxMean_eq_compTerm hc hev k a b ω]
    unfold boxMean
    by_cases hA : ω ∈ J.A k
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
      congr 1
      exact lintegral_congr fun t => min_eq_left (htr k hcl t)
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
  have hfin : ∀ k, ∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y ≠ ∞ := by
    intro k
    rw [← hbm k]
    exact boxMean_min_ne_top hc hev k C ω
  -- the slots above `2b + 2` contribute nothing
  set K := (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * (b : ℝ) + 2)).toFinset
  have hzero : ∀ k ∉ K, ∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y = 0 := by
    intro k hk
    have hk' : 2 * (b : ℝ) + 2 < slotF θ X₀ k ω := by
      simp only [K, Set.Finite.mem_toFinset, mem_setOf_eq, not_le] at hk
      exact hk
    rw [← boxMean_eq_compTerm hc hev k a b ω]
    unfold boxMean
    by_cases hA : ω ∈ J.A k
    · rw [Set.indicator_of_mem hA]
      have : ∫⁻ t in box (J.c k ω) (J.H k ω), PhiA θ X₀ k a b (ω, t) = 0 := by
        have h0 : ∀ t ∈ box (J.c k ω) (J.H k ω), PhiA θ X₀ k a b (ω, t) = 0 :=
          fun t ht => PhiA_zero_high hc k a b ω hk' ht
        rw [setLIntegral_congr_fun (show MeasurableSet (box (J.c k ω) (J.H k ω)) from
          measurableSet_Ico) h0]
        simp
      rw [this, mul_zero]
    · rw [Set.indicator_of_notMem hA]
  refine ⟨K.sup id + 1, fun n hn => ?_⟩
  have hK : ∀ k ∈ K, k ∈ Finset.range n := fun k hk => by
    have := Finset.le_sup (f := id) hk
    exact Finset.mem_range.mpr (by simp only [id] at this; omega)
  have hdm : Measurable (compDen θ X₀ ω) :=
    Measurable.ennreal_tsum fun k => compTerm_meas hc k ω
  set K' := 2 * ∑ w ∈ (cof_finite hc (b : ℝ) ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK' : K' ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  have hden : ∀ y ∈ Ico (a : ℝ) b, compDen θ X₀ ω y ≤ K' := fun y hy =>
    compDen_le hc hev ω hy.2.le
  have hsum : ∫⁻ y in Ico (a : ℝ) b, compDen θ X₀ ω y =
      ∑ k ∈ Finset.range n, ∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y := by
    unfold compDen
    rw [lintegral_tsum fun k => (compTerm_meas hc k ω).aemeasurable]
    refine tsum_eq_sum fun k hk => hzero k fun hkK => hk (hK k hkK)
  calc ∑ k ∈ Finset.range n, (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω
      = ∑ k ∈ Finset.range n, (∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y).toReal :=
        Finset.sum_congr rfl fun k _ => by rw [hω k, hbm k]
    _ = (∑ k ∈ Finset.range n, ∫⁻ y in Ico (a : ℝ) b, compTerm θ X₀ k ω y).toReal :=
        (ENNReal.toReal_sum fun k _ => hfin k).symm
    _ = (∫⁻ y in Ico (a : ℝ) b, compDen θ X₀ ω y).toReal := by rw [hsum]
    _ = ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := by
        rw [intervalIntegral.integral_of_le hab, ← setIntegral_congr_set Ico_ae_eq_Ioc,
          integral_toReal hdm.aemeasurable.restrict]
        refine (ae_restrict_iff' measurableSet_Ico).mpr (Filter.Eventually.of_forall
          fun y hy => lt_of_le_of_lt (hden y hy) (lt_top_iff_ne_top.mpr hK'))

end Queue6

end
