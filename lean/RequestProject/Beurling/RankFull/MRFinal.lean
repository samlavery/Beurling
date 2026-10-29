module

public import RequestProject.Beurling.RankFull.MRCount
public import RequestProject.Beurling.RankFull.ModelJitter

/-!
# `SkeletonBound` for every run structure (Lemma A.5 + Theorem A.10, `C = B'`)

* `RankFull.Config.skelCount_le_ZS` : on `G_{<s_max}`, the realised count of the tuples with
  skeleton `(E, l)` is at most the labelled sum `ZS (K-1)` of the recursion (each tuple maps
  injectively to its labels and contents, and its term is `∏_j (q_j/τ_j)^{s_j-1} ≥ 1`);
* `RankFull.Config.skeletonBound_all` : **`SkeletonBound` for all run structures**, from
  `multiRun_chain`. In particular `MultiRunSkeletonBound` holds.
-/

@[expose] public section

open Finset MeasureTheory RankFull.Runs BSCert.StageRows
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θE : ℝ≥0∞}

lemma exp_rowLog (E : Matrix (Fin K) (Fin K) ℕ) (q : Fin K → ℝ) (hq : ∀ j, 0 < q j)
    (y : Fin K) : Real.exp (RankFull.rowLog E (fun j => Real.log (q j)) y) =
      ∏ j, q j ^ E y j := by
  unfold RankFull.rowLog
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Real.exp_nat_mul, Real.exp_log (hq j)]

/-- The term of a realised tuple: `∏_j q_j^{-1} ∏_y ∏_j q_j^{E_yj} ∏_j τ_j^{-(s_j-1)} ≥ 1`. -/
lemma term_ge_one (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (q τ : Fin K → ℝ)
    (hτ1 : ∀ j, 1 ≤ τ j) (hqτ : ∀ j, τ j ≤ q j) :
    1 ≤ (∏ j, (q j)⁻¹) * (∏ y, ∏ j, q j ^ E y j) * patternWeight τ E := by
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le (by linarith [hτ1 j]) (hqτ j)
  have h1 : (∏ y, ∏ j, q j ^ E y j) = ∏ j, q j ^ (∑ y, E y j) := by
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => Finset.prod_pow_eq_pow_sum _ _ _
  rw [h1, patternWeight, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have := Finset.prod_le_prod (s := univ) (f := fun _ => (1 : ℝ))
    (g := fun j => (q j)⁻¹ * q j ^ (∑ y, E y j) * (τ j)⁻¹ ^ ((∑ y, E y j) - 1))
    (fun _ _ => zero_le_one) (fun j _ => by
      have hs := RankFull.one_le_colSum hE j
      have e : (q j)⁻¹ * q j ^ (∑ y, E y j) * (τ j)⁻¹ ^ ((∑ y, E y j) - 1) =
          (q j / τ j) ^ ((∑ y, E y j) - 1) := by
        have : q j ^ (∑ y, E y j) = q j * q j ^ ((∑ y, E y j) - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hs]
        rw [this, div_pow, inv_pow]
        field_simp [(hq0 j).ne']
      show (1 : ℝ) ≤ (q j)⁻¹ * q j ^ (∑ y, E y j) * (τ j)⁻¹ ^ ((∑ y, E y j) - 1)
      rw [e]
      exact one_le_pow₀ ((one_le_div (by linarith [hτ1 j])).mpr (hqτ j)))
  simpa using this

lemma PhiC_top (J : JitterLaw Ω P θE) {l : List ℕ} {A Eu : ℝ} {r : ℕ} (hr : r + 1 = l.length)
    (ω : Ω) (u : ℕ) : PhiC (N := N) J l A Eu r ω u = 1 := by
  unfold PhiC
  rw [hr, List.drop_length]
  simp [GRun]

/-- **The realised count is dominated by the labelled sum of the recursion** (pathwise, on
`G_{<s_max}`), for any run structure. -/
theorem skelCount_le_ZS {k : ℕ} (J : JitterLaw Ω P θE) (G : ℕ → Set Ω)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ)
    (hE : (Ereal E).det ≠ 0) (l : List ℕ) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = k + 1)
    (τ : Fin (k + 1) → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (A Eu : ℝ)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin (k + 1),
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (ω : Ω) (hω : ω ∈ G smax) :
    skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E l ≤
      ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu k ω := by
  set S := windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw with hS
  set T := (rankTuples (k + 1) S).filter fun t => skel t = (E, l) with hT
  set tl := tailOf (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw with htl
  set gN : (Fin (k + 1) → Fin N → ℕ) → Fin (k + 1) → ℕ := fun t =>
    if h : (pivs t).card = k + 1 then fun j => (pivSlot t h j : ℕ) else 0 with hgN
  set gC : (Fin (k + 1) → Fin N → ℕ) → Fin (k + 1) → (Fin N → ℕ) × ℕ := fun t i =>
    (fun n => if n ∈ pivSet t then 0 else t i n, tl (t i)) with hgC
  set F : (Fin (k + 1) → ℕ) × (Fin (k + 1) → (Fin N → ℕ) × ℕ) → ℝ≥0∞ := fun y =>
    if ConsM E l smax (k + 1) y.1 y.2 then
      (J.A (y.1 (Fin.last k))).indicator 1 ω *
        Ffull J E l τ Jw G A Eu k ω (Fin.init y.1) (y.1 (Fin.last k)) y.2
          (J.q (y.1 (Fin.last k)) ω) else 0 with hF
  have hfacts : ∀ t ∈ T, ∃ hk : (pivs t).card = k + 1, (∀ i, t i ∈ S) ∧
      pattern t = E ∧ runList t = l := by
    intro t ht
    obtain ⟨ht1, hskel⟩ := Finset.mem_filter.mp ht
    obtain ⟨htS, -, hli⟩ := Finset.mem_filter.mp ht1
    obtain ⟨h1, h2⟩ := Prod.mk.inj hskel
    exact ⟨card_pivs hli, Fintype.mem_piFinset.mp htS, h1, h2⟩
  have hgN' : ∀ t (hk : (pivs t).card = k + 1), gN t = fun j => (pivSlot t hk j : ℕ) :=
    fun t hk => by simp only [hgN, dif_pos hk]
  have hmemC : ∀ t ∈ T, gC t ∈ contents (k + 1) N D Dmax X₀ := by
    intro t ht
    obtain ⟨hk, hS', -, -⟩ := hfacts t ht
    rw [contents, Fintype.mem_piFinset]
    intro i
    have hel := tailOf_mem (hS' i)
    obtain ⟨hel1, -⟩ := Finset.mem_filter.mp hel
    obtain ⟨hv, hd⟩ := Finset.mem_product.mp hel1
    refine Finset.mem_product.mpr ⟨?_, hd⟩
    rw [Fintype.mem_piFinset] at hv ⊢
    intro n
    have := hv n
    simp only [hgC, Finset.mem_range] at this ⊢
    split_ifs
    · omega
    · exact this
  have hF1 : ∀ t ∈ T, 1 ≤ F (gN t, gC t) := by
    intro t ht
    obtain ⟨hk, hS', hpat, hrun⟩ := hfacts t ht
    set p := pivSlot t hk with hp
    have hpdec : ∀ j, ω ∈ J.A (p j) := by
      intro j
      obtain ⟨i, hi⟩ := pivSlot_mem_colSupp t hk j
      exact (Finset.mem_filter.mp (windowVecs_supp (hS' i) (p j) hi)).2
    have hsm : ∀ j, (p j : ℕ) ≤ smax := by
      intro j
      obtain ⟨i, hi⟩ := pivSlot_mem_colSupp t hk j
      have hel := tailOf_mem (hS' i)
      obtain ⟨hel1, hsupp, -, hval⟩ := Finset.mem_filter.mp hel
      refine hsmax ω (p j) (hpdec j) _ hval ?_
      refine elemVal_ge (q := qOf J ω) (x := (t i, tl (t i))) ?_ (fun n hn => ?_) hi
      · exact smooth_pos (Finset.mem_product.mp hel1).2
      · exact (hq ω n (Finset.mem_filter.mp (hsupp n hn)).2).le
    have hC := cons_tuple t hk hpat hrun hsum hpos (Nat.succ_pos k) hsm tl
    rw [← hgN' t hk] at hC
    simp only [hF]
    rw [if_pos hC, ZS_term_eq, hgN' t hk]
    -- the factors
    have hA1 : ∏ j, (J.A (p j : ℕ)).indicator (1 : Ω → ℝ≥0∞) ω = 1 :=
      Finset.prod_eq_one fun j _ => by rw [Set.indicator_of_mem (hpdec j)]; rfl
    have hdec : ω ∈ decSet J (gC t) := by
      intro i n hn
      simp only [hgC] at hn
      split_ifs at hn with h
      · exact absurd rfl hn
      · exact (Finset.mem_filter.mp (windowVecs_supp (hS' i) n hn)).2
    have hGl : ω ∈ G (p (Fin.last k) : ℕ) := hG _ _ (hsm _) hω
    have hlen : runNum l k + 1 = l.length := by
      have h1 := runNum_tuple t hk hrun hsum ⟨k, Nat.lt_succ_self k⟩
      have e : Fin.rev (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = ⟨0, Nat.succ_pos k⟩ :=
        Fin.ext (by simp)
      rw [e, stageOf_pk_zero t hk (Nat.succ_pos k)] at h1
      have hT1 := stageOf_le_numRuns (cfgMat t) (pk t hk ⟨0, Nat.succ_pos k⟩)
      rw [stageOf_pk_zero t hk (Nat.succ_pos k)] at hT1
      have hl : l.length = numRuns (cfgMat t) := by rw [← hrun]; simp [runList]
      simp only at h1
      omega
    have hphi := PhiC_top (N := N) J (A := A) (Eu := Eu) hlen ω
      (((p ·) : Fin (k + 1) → ℕ) ⟨runFirst l k, Nat.lt_succ_of_le (runFirst_le l k)⟩)
    have hq0 : ∀ j, 0 < J.q (p j : ℕ) ω := fun j => by linarith [hq ω _ (hpdec j)]
    have hinv : ∏ j, invq (J.q (p j : ℕ) ω) = ENNReal.ofReal (∏ j, (J.q (p j : ℕ) ω)⁻¹) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (inv_pos.mpr (hq0 j)).le)]
      refine Finset.prod_congr rfl fun j _ => ?_
      unfold invq
      rw [Set.indicator_of_mem (show J.q (p j : ℕ) ω ∈ Set.Ioi (0 : ℝ) from hq0 j)]
    -- the integral over no processed pivot
    have hIz : IzM J E Jw (k + 1) (fun j => (p j : ℕ)) ω (gC t) =
        ENNReal.ofReal (∏ y, ∏ j, J.q (p j : ℕ) ω ^ E y j) := by
      unfold IzM
      have hz : ∀ z : Fin (k + 1 - (k + 1)) → ℝ, mergeL (K := k + 1) (k + 1 - (k + 1)) z
          (uvec J (k + 1) (fun j => (p j : ℕ)) ω) = fun j => Real.log (J.q (p j : ℕ) ω) := by
        intro z
        funext j
        unfold mergeL uvec
        rw [dif_neg (by omega), dif_pos j.isLt]
      rw [lintegral_congr fun z => by rw [hz z], lintegral_const]
      have hvol : MeasureTheory.volume (Set.univ : Set (Fin (k + 1 - (k + 1)) → ℝ)) = 1 := by
        rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
        refine Finset.prod_eq_one fun i _ => ?_
        exact absurd i.isLt (by omega)
      rw [hvol, mul_one]
      unfold Lcore
      rw [ENNReal.ofReal_prod_of_nonneg (fun y _ => Finset.prod_nonneg fun j _ =>
        pow_nonneg (hq0 j).le _)]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [exp_rowLog E (fun j => J.q (p j : ℕ) ω) hq0 y]
      have hwin : cvs J ω (gC t) y * ∏ j, J.q (p j : ℕ) ω ^ E y j ∈ Jw := by
        have hel := tailOf_mem (hS' y)
        have hval := (Finset.mem_filter.mp hel).2.2.2
        convert hval using 1
        unfold cvs cval elemVal
        simp only [hgC]
        rw [prod_split t hk (qOf J ω) (t y)]
        have hre : ∏ j, J.q (p j : ℕ) ω ^ E y j =
            ∏ j, J.q (pivSlot t hk j : ℕ) ω ^ t y (pivSlot t hk j) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← hpat, pattern_eq t hk]
        rw [hre]
        simp only [qOf]
        ring
      rw [Set.indicator_of_mem hwin, Pi.one_apply, mul_one]
    rw [hA1, Set.indicator_of_mem hdec, Set.indicator_of_mem hGl, hphi, hinv, hIz]
    simp only [Pi.one_apply, one_mul, mul_one]
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (inv_pos.mpr (hq0 j)).le),
      ← ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun j _ =>
        (inv_pos.mpr (hq0 j)).le) (Finset.prod_nonneg fun y _ => Finset.prod_nonneg fun j _ =>
          pow_nonneg (hq0 j).le _))]
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (term_ge_one E hE _ τ hτ1 fun j => ?_)
    -- the caps
    refine hτ ω _ (hpdec j) j ?_
    have hsub : (Finset.Iio j).image p ⊆ (decOf J ω).filter (· < p j) := by
      intro n hn
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpdec j'⟩,
        (pivSlot_strictMono t hk) (Finset.mem_Iio.mp hj')⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (pivSlot_strictMono t hk).injective, Fin.card_Iio] at this
    exact this
  have hinj : Set.InjOn (fun t => (gN t, gC t)) T := by
    intro t ht t' ht' h
    obtain ⟨hk, -, hpat, -⟩ := hfacts t ht
    obtain ⟨hk', -, hpat', -⟩ := hfacts t' ht'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hpp : ∀ j, pivSlot t hk j = pivSlot t' hk' j := by
      intro j
      have := congrFun h1 j
      rw [hgN' t hk, hgN' t' hk'] at this
      exact Fin.ext this
    have hset : pivSet t = pivSet t' := by
      rw [pivSet_eq_image t hk, pivSet_eq_image t' hk']
      congr 1; funext j; exact hpp j
    funext i n
    by_cases hn : n ∈ pivSet t
    · obtain ⟨j, rfl⟩ := (mem_pivSet t hk n).mp hn
      rw [← pattern_eq t hk, hpat, hpp j, ← pattern_eq t' hk', hpat']
    · have := congrArg Prod.fst (congrFun h2 i)
      have := congrFun this n
      simp only [hgC, if_neg hn, ← hset] at this
      exact this
  have hcount : skelCount S E l = ∑ t ∈ T, (1 : ℝ≥0∞) := by simp [skelCount, hT]
  rw [hcount]
  unfold ZS
  calc ∑ t ∈ T, (1 : ℝ≥0∞) ≤ ∑ t ∈ T, F (gN t, gC t) := Finset.sum_le_sum hF1
    _ = ∑ y ∈ T.image fun t => (gN t, gC t), F y :=
        (Finset.sum_image (f := F) hinj).symm
    _ ≤ ∑ y ∈ T.image gN ×ˢ contents (k + 1) N D Dmax X₀, F y := by
        refine Finset.sum_le_sum_of_subset fun y hy => ?_
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, hmemC t ht⟩
    _ = ∑ lab ∈ T.image gN, ∑ c ∈ contents (k + 1) N D Dmax X₀, F (lab, c) :=
        Finset.sum_product _ _ _
    _ ≤ ∑' lab, ∑ c ∈ contents (k + 1) N D Dmax X₀, F (lab, c) := ENNReal.sum_le_tsum _

lemma ereal_det_ne {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} (hE : E ∈ InvPattern K) :
    (Ereal E).det ≠ 0 := by
  have h2 : (Ereal E).det = (((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) : ℝ) := by
    have := RingHom.map_det (Rat.castHom ℝ) (E.map (Nat.cast : ℕ → ℚ))
    change (((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) : ℝ) = _ at this
    rw [this]
    congr 1
  rw [h2]
  have : ((E.map (Nat.cast : ℕ → ℚ)).det : ℚ) ≠ 0 := hE
  exact_mod_cast this

/-- **`SkeletonBound` for every run structure** (Lemma A.5 + Theorem A.10 with `C = B'`; the
input `hbound` of Theorem A.12 and Proposition 6.11), in the window model over a jitter process,
under:
* the model hypotheses `hq` (decided values `> 1`), `hsmax` (a decided value below a point of
  the window has slot `≤ s_max`), `hτ` (the caps of (A.tau));
* nested adapted good events `G` with `Good ⊆ G_{<s_max}`;
* the sure top bound (S3)(d): `Eu_s(u) = Eu ∏_{decided n < u} (1 - 1/q_n)^{-1} ≤ A` on
  `G_{<u}` for `u ≤ s_max`, with the tails bounded by `Eu` (`∑ 1/d ≤ Eu = Eu_rat`). -/
theorem skeletonBound_all {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) {r₀ : ℕ}
    (hr0 : 1 ≤ r₀) (τ : Fin r₀ → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ)
    (X₀ D Dmax : ℕ) {A Eu : ℝ} (hEu : 0 < Eu) (htail : tailSum Dmax X₀ ≤ Eu)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r₀,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) :
    SkeletonBound P Good r₀ θ δ A Eu τ
      (fun E l ω => skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E l) := by
  obtain ⟨k, rfl⟩ : ∃ k, r₀ = k + 1 := ⟨r₀ - 1, by omega⟩
  intro E hE l hl
  obtain ⟨hpos, hsum⟩ := (mem_comps _ _).mp hl
  have hEr := ereal_det_ne hE
  have h1 : ∫⁻ ω in Good, skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw)
      E l ∂P ≤ ∫⁻ ω, ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu k ω ∂P := by
    refine le_trans ?_ (setLIntegral_le_lintegral Good _)
    refine setLIntegral_mono' hGood fun ω hω => ?_
    exact skelCount_le_ZS J G hG E hEr l hpos hsum τ hτ1 Jw D Dmax X₀ smax A Eu hq hsmax hτ ω
      (hGoodG hω)
  have h2 := multiRun_chain (N := N) (J := J) (E := E) (l := l) (τ := τ) (Jw := Jw) (D := D)
    (Dmax := Dmax) (X₀ := X₀) (smax := smax) (G := G) (A := A) (Eu := Eu) hJw hq hEu hEr hpos
    hsum (Nat.succ_pos k) hGm hG hS3 hJ hδ htail hτ1
  have hpw : 0 ≤ patternWeight τ E := Finset.prod_nonneg fun j _ =>
    pow_nonneg (inv_nonneg.mpr (by linarith [hτ1 j])) _
  calc _ ≤ ∫⁻ ω, ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu k ω ∂P := h1
    _ ≤ θE ^ (k + 1) * ENNReal.ofReal (finG A l Eu * δ ^ (k + 1) * patternWeight τ E) := h2
    _ ≤ ENNReal.ofReal θ ^ (k + 1) *
          ENNReal.ofReal (finG A l Eu * δ ^ (k + 1) * patternWeight τ E) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow hθ0, ← ENNReal.ofReal_mul (pow_nonneg hθ0 _)]
        congr 1; ring

/-- **`MultiRunSkeletonBound` holds** (the residual of `skeletonBound_jitter`). -/
theorem multiRunSkeletonBound {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) {r₀ : ℕ}
    (hr0 : 1 ≤ r₀) (τ : Fin r₀ → ℝ) (hτ1 : ∀ j, 1 ≤ τ j) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ)
    (X₀ D Dmax : ℕ) {A Eu : ℝ} (hEu : 0 < Eu) (htail : tailSum Dmax X₀ ≤ Eu)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw, J.q n ω ≤ y → (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r₀,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → τ j ≤ J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) :
    MultiRunSkeletonBound P Good r₀ θ δ A Eu τ
      (fun E l ω => skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw) E l) :=
  fun E hE l hl _ => skeletonBound_all J hθ0 hθ hGood G hGm hG smax hGoodG hr0 τ hτ1 hJw hJ hδ
    X₀ D Dmax hEu htail hq hsmax hτ hS3 E hE l hl

/-- The input `hbound` of `prop_6_11_window` for the window model over a jitter process
(`dec = decOf J`, `q = qOf J`, `τ = tauSlot`): every window has its `SkeletonBound`. -/
theorem hbound_window {ι : Type*} {θE : ℝ≥0∞} (J : JitterLaw Ω P θE) [IsProbabilityMeasure P]
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θE ≤ ENNReal.ofReal θ) {Good : Set Ω}
    (hGood : MeasurableSet Good) (G : ℕ → Set Ω) (hGm : ∀ u, MeasurableSet[J.F u] (G u))
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (smax : ℕ) (hGoodG : Good ⊆ G smax) {r₀ : ℕ}
    (hr0 : 1 ≤ r₀) {H : ℝ → ℝ} {X₀r : ℝ} (hH : SlotHyp H X₀r) (W : Finset ι)
    (Jw : ι → Set ℝ) (hJw : ∀ J ∈ W, MeasurableSet (Jw J)) (aw : ι → ℝ) {δ : ℝ}
    (hJ : ∀ J ∈ W, Jw J ⊆ Set.Ico (aw J) (aw J + δ)) (hδ : 0 ≤ δ) (X₀ D Dmax : ℕ) {A Eu : ℝ}
    (hEu : 0 < Eu) (htail : tailSum Dmax X₀ ≤ Eu)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hsmax : ∀ Jx ∈ W, ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ y ∈ Jw Jx, J.q n ω ≤ y →
      (n : ℕ) ≤ smax)
    (hτ : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → ∀ j : Fin r₀,
      (j : ℕ) ≤ ((decOf (N := N) J ω).filter (· < n)).card → tauSlot H X₀r j ≤ J.q n ω)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) :
    ∀ Jx ∈ W, SkeletonBound P Good r₀ θ δ A Eu (fun j => tauSlot H X₀r j)
      (fun E l ω => skelCount (windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax (Jw Jx))
        E l) :=
  fun Jx hJx => skeletonBound_all J hθ0 hθ hGood G hGm hG smax hGoodG hr0 _
    (fun j => one_le_tauSlot hH j) (hJw Jx hJx) (hJ Jx hJx) hδ X₀ D Dmax hEu htail hq
    (hsmax Jx hJx) hτ hS3

end RankFull.Config
