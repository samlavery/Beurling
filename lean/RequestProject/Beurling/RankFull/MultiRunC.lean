module

public import RequestProject.Beurling.RankFull.BlockModelC

/-!
# Proposition 6.19 (Cover Bound): the pivot-by-pivot recursion for a cover

The recursion of `MultiRun.lean`, for a configuration with a cover `C` (`cd.Cd`) of its rows:
* the integrand is `LcoreC` (the density of the rows of `C` only; every row keeps its window);
* the weight is `cd.Wc = ∏_i τ_i^{-e_i}`, `e_i = s^C_i - 1`;
* the carried functions `Φ_t` use the join list `cd.lg` of the cover (`joinC`), with
  `K_t = |C ∩ R≤t|` chain rows;
* the rows outside the cover are fixed by (s4): their exponent at a free slot is the (s4)
  monomial at the rank of the slot among the slots of `P(C)` (`cd.mono`), their tail is fixed
  (`cd.tailR`), and every slot of the content occurs in a row of `C` (`ExtraC`).

* `RankFull.Config.hnext_lastC` : the last pivot of a run, the block (S3)(a) with the chain rows
  `SR(m+1) ∩ C` (`blockSumEC_gen`);
* `RankFull.Config.hnext_finalC` : the end step; the rows of `R` cost `vol(J)/z` each;
* `RankFull.Config.multiRunC_chain` :
  `E[Z_0] ≤ θ^K Fin(A, joinC E C l, Eu) δ^K z^{-(K-|C|)} ∏_i τ_i^{-e_i}`.
-/

@[expose] public section

open Finset MeasureTheory RankFull.Runs
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θE : ℝ≥0∞}

/-- The data of a cover skeleton used by the recursion. -/
structure CovD (K : ℕ) where
  /-- the rows of the cover `C` -/
  Cd : Finset (Fin K)
  /-- the join list of the cover (the list of the chain recursion) -/
  lg : List ℕ
  /-- the pivot weight `∏_i τ_i^{-e_i}` -/
  Wc : ℝ
  /-- the (s4) monomial of a row outside the cover, by rank -/
  mono : Fin K → ℕ → ℕ
  /-- the (s4) tail of a row outside the cover -/
  tailR : Fin K → ℕ

/-- The rank of a slot among the slots of `P(C)` decided before it (the unprocessed pivot
labels and the slots of the remaining content occurring in rows of `C`). -/
noncomputable def rankC {K : ℕ} (cd : CovD K) (u : ℕ) (lab : Fin u → ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) (g : Fin N) : ℕ :=
  (univ.filter fun j : Fin u => lab j < g).card +
    (univ.filter fun g' : Fin N => g' < g ∧ ∃ y ∈ cd.Cd, (c y).1 g' ≠ 0).card

/-- The rows outside the cover are fixed by (s4), and every slot occurs in a row of `C`. -/
def ExtraC {K : ℕ} (cd : CovD K) (u : ℕ) (lab : Fin u → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    Prop :=
  (∀ g, (∃ y, (c y).1 g ≠ 0) → ∃ y ∈ cd.Cd, (c y).1 g ≠ 0) ∧
  (∀ y ∉ cd.Cd, ∀ g, (c y).1 g =
    if ∃ y' ∈ cd.Cd, (c y').1 g ≠ 0 then cd.mono y (rankC cd u lab c g) else 0) ∧
  (∀ y ∉ cd.Cd, (c y).2 = cd.tailR y)

/-- The constraints of the cover recursion. -/
def ConsC {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (l : List ℕ) (smax : ℕ) (cd : CovD K)
    (u : ℕ) (lab : Fin u → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) : Prop :=
  ConsM E l smax u lab c ∧ ExtraC cd u lab c

section Defs

variable (J : JitterLaw Ω P θE) {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (l : List ℕ)
  (cd : CovD K) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (G : ℕ → Set Ω) (A Eu : ℝ)

/-- The integral over the processed pivots, with the current column at log-value `x`. -/
noncomputable def IzXC (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ)
    (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Fin (K - (m + 1)) → ℝ,
    LcoreC E Jw cd.Cd (cvs J ω c) (mergeL (K - (m + 1)) z (uvecX J m lab ω x))

/-- The integral over the processed pivots at the level with `m` unprocessed pivots. -/
noncomputable def IzMC (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ℝ≥0∞ :=
  ∫⁻ z : Fin (K - m) → ℝ, LcoreC E Jw cd.Cd (cvs J ω c) (mergeL (K - m) z (uvec J m lab ω))

/-- The term of `ZM (m+1)` (and of `ΦM m n`) for the labels `snoc lab n`, the current column at
value `t`. -/
noncomputable def FfullC (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (n : ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) (t : ℝ) : ℝ≥0∞ :=
  (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω * (G n).indicator 1 ω *
    PhiC (N := N) J cd.lg A Eu (runNum l m) ω ((Fin.snoc lab n : Fin (m + 1) → ℕ)
      ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) *
    (∏ j, invq (J.q (lab j) ω)) * invq t * IzXC J E cd Jw m lab ω c (Real.log t) *
    ENNReal.ofReal (cd.Wc)

/-- The good-event and carried factor after the pivot at column `m` (label replacement). -/
noncomputable def GammaBarC (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ℝ≥0∞ :=
  if h : runFirst l m < m then
    (G (lab ⟨m - 1, by omega⟩)).indicator 1 ω *
      PhiC (N := N) J cd.lg A Eu (runNum l m) ω (lab ⟨runFirst l m, h⟩)
  else
    (if h1 : 1 ≤ m then (G (lab ⟨m - 1, by omega⟩)).indicator 1 ω else 1) *
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uOf c)) *
      PhiC (N := N) J cd.lg A Eu (runNum l m) ω (uOf c)

/-- The dominating term (independent of the label of column `m`). -/
noncomputable def FbarC (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
    GammaBarC J l cd smax G A Eu m ω lab c *
    (∏ j, invq (J.q (lab j) ω)) * invq t * IzXC J E cd Jw m lab ω c (Real.log t) *
    ENNReal.ofReal (cd.Wc)

/-- The adapted integrand at the pivot of column `m` with label `n`. -/
noncomputable def PhiMC (m n : ℕ) (x : Ω × ℝ) : ℝ≥0∞ :=
  ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ConsC E l smax cd (m + 1) (Fin.snoc lab n) c then FfullC J E l cd Jw G A Eu m x.1 lab n c x.2
    else 0

/-- The dominating integrand at the pivot of column `m`. -/
noncomputable def PhiBarMC (m : ℕ) (x : Ω × ℝ) : ℝ≥0∞ :=
  ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ∃ n, ConsC E l smax cd (m + 1) (Fin.snoc lab n) c then
      FbarC J E l cd Jw smax G A Eu m x.1 lab c x.2 else 0

/-- The pending quantity with `m + 1` unprocessed pivots. -/
noncomputable def ZSC (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑' lab : Fin (m + 1) → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ConsC E l smax cd (m + 1) lab c then
      (J.A (lab (Fin.last m))).indicator 1 ω *
        FfullC J E l cd Jw G A Eu m ω (Fin.init lab) (lab (Fin.last m)) c (J.q (lab (Fin.last m)) ω)
    else 0

end Defs

section Steps

variable (J : JitterLaw Ω P θE) {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (l : List ℕ)
  (cd : CovD K) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (G : ℕ → Set Ω) (A Eu : ℝ)

/-- **The pivot step**: `ZSC m` is the label sum over the column `m`. -/
theorem ZSC_eq (m : ℕ) (ω : Ω) :
    ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m ω = ∑' n, (J.A n).indicator
      (fun ω => PhiMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m n (ω, J.q n ω)) ω := by
  unfold ZSC
  rw [← (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun n => ?_
  by_cases hA : ω ∈ J.A n
  · rw [Set.indicator_of_mem hA]
    unfold PhiMC
    refine tsum_congr fun lab => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ) (n, lab) = Fin.snoc lab n from rfl]
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs
    · rw [Set.indicator_of_mem hA, Pi.one_apply, one_mul]
    · rfl
  · rw [Set.indicator_of_notMem hA]
    refine ENNReal.tsum_eq_zero.mpr fun lab => Finset.sum_eq_zero fun c _ => ?_
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ) (n, lab) = Fin.snoc lab n from rfl]
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs
    · rw [Set.indicator_of_notMem hA, zero_mul]
    · rfl

variable {J E l cd Jw D Dmax X₀ smax G A Eu}

/-- **Label replacement** (step (i) of Lemma A.5), for the column `m`. -/
lemma gammaC_le (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) {m n : ℕ} {lab : Fin m → ℕ}
    {c : Fin K → (Fin N → ℕ) × ℕ} (hC : ConsC E l smax cd (m + 1) (Fin.snoc lab n) c) (ω : Ω) :
    (G n).indicator 1 ω * PhiC (N := N) J cd.lg A Eu (runNum l m) ω
      ((Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) ≤
      GammaBarC J l cd smax G A Eu m ω lab c := by
  obtain ⟨hmono, hlab, hc, -⟩ := hC.1
  have hlast : (Fin.snoc lab n : Fin (m + 1) → ℕ) (Fin.last m) = n := Fin.snoc_last _ _
  -- the previous label is before `n`
  have hprev : ∀ h : 1 ≤ m, lab ⟨m - 1, by omega⟩ < n := by
    intro h
    have := hmono (show (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) < Fin.last m from
      Fin.castSucc_lt_last _)
    rw [Fin.snoc_castSucc, hlast] at this
    exact this
  unfold GammaBarC
  by_cases hω : ω ∈ G n
  · rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul]
    split_ifs with h1 h2
    · have hmem : ω ∈ G (lab ⟨m - 1, by omega⟩) := hG _ _ (hprev (by omega)).le hω
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      have : (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
          (runFirst_le l m)⟩ = lab ⟨runFirst l m, h1⟩ := by
        have := Fin.snoc_castSucc (α := fun _ => ℕ) (p := lab) (x := n) ⟨runFirst l m, h1⟩
        simpa using this
      rw [this]
    all_goals
      have hfirst : runFirst l m = m := le_antisymm (runFirst_le l m) (not_lt.mp h1)
      have hn : (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
          (runFirst_le l m)⟩ = n := by
        rw [← hlast]; congr 1; exact Fin.ext (by simp [hfirst])
      have hu : uOf c ≤ n := by
        rw [uOf_le_iff]
        intro y g hg
        have := (hc y g hg).1 (Nat.succ_pos m)
        simp only [Nat.add_sub_cancel] at this
        rwa [hn] at this
      have hns : n ≤ smax := by
        have := (hlab (Fin.last m)).2; rwa [hlast] at this
      have hchi : chiB smax (fun u => ω ∈ G u) (uOf c) = 1 := by
        unfold chiB; rw [if_pos ⟨hu.trans hns, hG _ _ hu hω⟩]
      rw [hn, hchi, ENNReal.ofReal_one, mul_one]
    · have hmem : ω ∈ G (lab ⟨m - 1, by omega⟩) := hG _ _ (hprev h2).le hω
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      exact PhiC_anti hq hEu _ ω hu
    · rw [one_mul]
      exact PhiC_anti hq hEu _ ω hu
  · rw [Set.indicator_of_notMem hω, zero_mul]; exact zero_le _

/-- **Domination** of the adapted integrands by the label-free one. -/
theorem PhiMC_le (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (m n : ℕ) (x : Ω × ℝ) :
    PhiMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m n x ≤
      PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m x := by
  unfold PhiMC PhiBarMC
  refine ENNReal.tsum_le_tsum fun lab => Finset.sum_le_sum fun c _ => ?_
  by_cases hC : ConsC E l smax cd (m + 1) (Fin.snoc lab n) c
  · rw [if_pos hC, if_pos ⟨n, hC⟩]
    unfold FfullC FbarC
    have hγ := gammaC_le (A := A) hq hEu hG hC x.1
    calc (∏ j, (J.A (lab j)).indicator 1 x.1) * (decSet J c).indicator 1 x.1 *
          (G n).indicator 1 x.1 *
          PhiC (N := N) J cd.lg A Eu (runNum l m) x.1 ((Fin.snoc lab n : Fin (m + 1) → ℕ)
            ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) *
          (∏ j, invq (J.q (lab j) x.1)) * invq x.2 * IzXC J E cd Jw m lab x.1 c (Real.log x.2) *
          ENNReal.ofReal (cd.Wc)
        = (∏ j, (J.A (lab j)).indicator 1 x.1) * (decSet J c).indicator 1 x.1 *
          ((G n).indicator 1 x.1 *
          PhiC (N := N) J cd.lg A Eu (runNum l m) x.1 ((Fin.snoc lab n : Fin (m + 1) → ℕ)
            ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩)) *
          (∏ j, invq (J.q (lab j) x.1)) * invq x.2 * IzXC J E cd Jw m lab x.1 c (Real.log x.2) *
          ENNReal.ofReal (cd.Wc) := by ring
      _ ≤ _ := by gcongr
  · rw [if_neg hC]; exact zero_le _

end Steps

section MeasC

lemma measurable_coreC {α : Type*} [MeasurableSpace α] {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (Cd : Finset (Fin K)) (a : α → ℝ≥0∞) (ha : Measurable a)
    (cv : α → Fin K → ℝ) (hcv : ∀ y, Measurable fun ω => cv ω y) (m : ℕ) (u : α → Fin K → ℝ)
    (hu : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => u ω j) (i : ℕ) :
    Measurable fun x : α × ℝ => a x.1 * invq x.2 * ∫⁻ z : Fin i → ℝ, LcoreC E Jw Cd (cv x.1)
      (mergeL i z (fun j => if (j : ℕ) = m then Real.log x.2 else u x.1 j)) := by
  set U : α × ℝ → Fin K → ℝ :=
    fun x j => if (j : ℕ) = m then Real.log x.2 else u x.1 j with hUdef
  have hU : Measurable U := by
    rw [measurable_pi_iff]
    intro j
    simp only [hUdef]
    split_ifs with h
    · exact Real.measurable_log.comp measurable_snd
    · exact (hu j h).comp measurable_fst
  have hcv' : Measurable fun x : α × ℝ => cv x.1 := by
    rw [measurable_pi_iff]; intro y; exact (hcv y).comp measurable_fst
  set F : (α × ℝ) × (Fin i → ℝ) → ℝ≥0∞ :=
    fun p => LcoreC E Jw Cd (cv p.1.1) (mergeL i p.2 (U p.1)) with hFdef
  have hF : Measurable F := by
    have h1 : Measurable fun p : (α × ℝ) × (Fin i → ℝ) => (cv p.1.1, mergeL i p.2 (U p.1)) :=
      (hcv'.comp measurable_fst).prodMk
        ((measurable_mergeL2 (K := K) i).comp (measurable_snd.prodMk (hU.comp measurable_fst)))
    have h2 := (RankFull.measurable_LcoreC2 E hJw Cd).comp h1
    exact h2
  have hI : Measurable fun x : α × ℝ => ∫⁻ z : Fin i → ℝ, F (x, z) :=
    Measurable.lintegral_prod_right' hF
  have h3 := ((ha.comp measurable_fst).mul (measurable_invq.comp measurable_snd)).mul hI
  exact h3

lemma measurable_coreC' {α : Type*} [MeasurableSpace α] {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (Cd : Finset (Fin K)) (a : α → ℝ≥0∞)
    (ha : Measurable a)
    (cv : α → Fin K → ℝ) (hcv : ∀ y, Measurable fun ω => cv ω y) (m : ℕ) (u : α → Fin K → ℝ)
    (hu : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => u ω j) (i : ℕ) (W : ℝ≥0∞) :
    Measurable fun x : α × ℝ => a x.1 * invq x.2 * (∫⁻ z : Fin i → ℝ, LcoreC E Jw Cd (cv x.1)
      (mergeL i z (fun j => if (j : ℕ) = m then Real.log x.2 else u x.1 j))) * W :=
  (measurable_coreC E hJw Cd a ha cv hcv m u hu i).mul_const W

end MeasC

section MeasSpecific

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

/-- **Adaptedness** of the integrand at the pivot of column `m` with label `n`. -/
theorem PhiMC_jmeas (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hJw : MeasurableSet Jw) (m n : ℕ) :
    JMeas (J.F n) (PhiMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m n) := by
  unfold JMeas PhiMC
  refine @measurable_tsum_sum_ite (Ω × ℝ) _ _ (@Prod.instMeasurableSpace Ω ℝ (J.F n) _) _
    (contents K N D Dmax X₀) _ _ ?_
  intro lab c hC
  obtain ⟨hlab, hu, hu0⟩ := cons_facts hC.1
  set u0 := (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
    (runFirst_le l m)⟩ with hu0def
  set a : Ω → ℝ≥0∞ := fun ω => (∏ j, (J.A (lab j)).indicator 1 ω) *
    (decSet J c).indicator 1 ω * (G n).indicator 1 ω *
    PhiC (N := N) J cd.lg A Eu (runNum l m) ω u0 * (∏ j, invq (J.q (lab j) ω)) with ha
  set uu : Ω → Fin K → ℝ := fun ω j =>
    if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0 with huu
  have hform : (fun x : Ω × ℝ => FfullC J E l cd Jw G A Eu m x.1 lab n c x.2) = fun x =>
      a x.1 * invq x.2 * (∫⁻ z : Fin (K - (m + 1)) → ℝ, LcoreC E Jw cd.Cd (cvs J x.1 c)
        (mergeL (K - (m + 1)) z (fun j => if (j : ℕ) = m then Real.log x.2 else uu x.1 j))) *
        ENNReal.ofReal (cd.Wc) := by
    funext x
    simp only [FfullC, IzXC, uvecX_eq, ha, huu, hu0def]
  rw [hform]
  have hFn : ∀ g, (g : ℕ) < n → J.F (g + 1) ≤ J.F n := fun g hg => J.F_mono (by omega)
  have hqm : ∀ g : ℕ, g < n → Measurable[J.F n] (J.q g) := fun g hg =>
    (J.q_meas g).mono (hFn g hg) le_rfl
  have hAm : ∀ g : ℕ, g ≤ n → MeasurableSet[J.F n] (J.A g) := fun g hg =>
    J.F_mono hg _ (J.A_meas g)
  have ha_m : Measurable[J.F n] a := by
    refine @measurable_mul5 Ω (J.F n) _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · exact @measurable_prod_ind Ω (J.F n) _ _ (fun j => J.A (lab j))
        (fun j => hAm _ (hlab j).le)
    · exact @measurable_ind Ω (J.F n) _ (J.F_mono hu _ (measurableSet_decSet J c _ le_rfl))
    · exact @measurable_ind Ω (J.F n) _ (hGm n)
    · exact @measurable_PhiC_gen N Ω (J.F n) (fun g => J.A g) (fun g ω => J.q g ω)
        (fun ω g h => hq ω g h) Eu hEu u0 (fun g hg => hAm _ (by omega))
        (fun g hg => hqm _ (by omega)) A _ _
    · exact @measurable_prod_invq Ω (J.F n) _ _ (fun j ω => J.q (lab j) ω)
        (fun j => hqm _ (hlab j))
  have hcv : ∀ y, Measurable[J.F n] fun ω => cvs J ω c y := by
    intro y
    have : (fun ω => cvs J ω c y) = fun ω => cvalLt J n ω (c y) := by
      funext ω; simp only [cvs]; rw [cvalLt_eq hu y]
    rw [this]
    exact @measurable_cvalLt N Ω (J.F n) (fun g ω => J.q g ω) n
      (fun g hg => hqm _ hg) (c y)
  have hum : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable[J.F n] fun ω => uu ω j := by
    intro j _
    simp only [huu]
    split_ifs with h
    · exact @Measurable.comp Ω ℝ ℝ (J.F n) _ _ _ _ Real.measurable_log (hqm _ (hlab _))
    · exact @measurable_const ℝ Ω _ (J.F n) 0
  exact @measurable_coreC' Ω (J.F n) K E Jw hJw cd.Cd a ha_m (fun ω => cvs J ω c) hcv m uu hum
    (K - (m + 1)) _

lemma measurable_GammaBarC (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (m : ℕ) (lab : Fin m → ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) :
    Measurable fun ω => GammaBarC J l cd smax G A Eu m ω lab c := by
  have hG' : ∀ u, MeasurableSet (G u) := fun u => J.F_le u _ (hGm u)
  unfold GammaBarC
  split_ifs with h h1
  · exact (measurable_ind _ (hG' _)).mul (measurable_PhiC hq hEu _ _)
  · refine ((measurable_ind _ (hG' _)).mul ?_).mul (measurable_PhiC hq hEu _ _)
    refine ENNReal.measurable_ofReal.comp ?_
    unfold chiB
    by_cases hs : uOf c ≤ smax
    · have : (fun ω => if uOf c ≤ smax ∧ ω ∈ G (uOf c) then (1 : ℝ) else 0) =
          (G (uOf c)).indicator 1 := by
        funext ω; by_cases hω : ω ∈ G (uOf c) <;> simp [hs, hω]
      rw [this]; exact measurable_one.indicator (hG' _)
    · simp only [hs, false_and, if_false]; exact measurable_const
  · refine (measurable_const.mul ?_).mul (measurable_PhiC hq hEu _ _)
    refine ENNReal.measurable_ofReal.comp ?_
    unfold chiB
    by_cases hs : uOf c ≤ smax
    · have : (fun ω => if uOf c ≤ smax ∧ ω ∈ G (uOf c) then (1 : ℝ) else 0) =
          (G (uOf c)).indicator 1 := by
        funext ω; by_cases hω : ω ∈ G (uOf c) <;> simp [hs, hω]
      rw [this]; exact measurable_one.indicator (hG' _)
    · simp only [hs, false_and, if_false]; exact measurable_const

/-- The dominating integrand is measurable. -/
theorem PhiBarMC_meas (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hJw : MeasurableSet Jw) (m : ℕ) :
    Measurable (PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m) := by
  unfold PhiBarMC
  refine measurable_tsum_sum_ite (contents K N D Dmax X₀) _ _ ?_
  intro lab c _
  set a : Ω → ℝ≥0∞ := fun ω => (∏ j, (J.A (lab j)).indicator 1 ω) *
    (decSet J c).indicator 1 ω * GammaBarC J l cd smax G A Eu m ω lab c *
      (∏ j, invq (J.q (lab j) ω)) with ha
  set uu : Ω → Fin K → ℝ := fun ω j =>
    if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0 with huu
  have hform : (fun x : Ω × ℝ => FbarC J E l cd Jw smax G A Eu m x.1 lab c x.2) = fun x =>
      a x.1 * invq x.2 * (∫⁻ z : Fin (K - (m + 1)) → ℝ, LcoreC E Jw cd.Cd (cvs J x.1 c)
        (mergeL (K - (m + 1)) z (fun j => if (j : ℕ) = m then Real.log x.2 else uu x.1 j))) *
        ENNReal.ofReal (cd.Wc) := by
    funext x
    simp only [FbarC, IzXC, uvecX_eq, ha, huu]
  rw [hform]
  have ha_m : Measurable a := by
    refine (((measurable_prod_ind _ fun j => J.A_meas' _).mul
      (measurable_ind _ (J.F_le _ _ (measurableSet_decSet J c _ le_rfl)))).mul
      (measurable_GammaBarC hq hEu hGm m lab c)).mul ?_
    exact measurable_prod_invq _ fun j => J.q_meas' _
  have hcv : ∀ y, Measurable fun ω => cvs J ω c y := by
    intro y
    unfold cvs cval
    exact measurable_const.mul (Finset.measurable_prod _ fun g _ => (J.q_meas' _).pow_const _)
  have hum : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => uu ω j := by
    intro j _
    simp only [huu]
    split_ifs with h
    · exact Real.measurable_log.comp (J.q_meas' _)
    · exact measurable_const
  exact measurable_coreC' E hJw cd.Cd a ha_m (fun ω => cvs J ω c) hcv m uu hum (K - (m + 1)) _

end MeasSpecific

section Integral

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma measurable_IzXC (hJw : MeasurableSet Jw) (m : ℕ) (lab : Fin m → ℕ) (ω : Ω)
    (c : Fin K → (Fin N → ℕ) × ℕ) : Measurable fun x => IzXC J E cd Jw m lab ω c x := by
  unfold IzXC
  have hU : Measurable fun x : ℝ => uvecX (K := K) J m lab ω x := by
    rw [measurable_pi_iff]; intro j
    unfold uvecX
    split_ifs
    · exact measurable_const
    · exact measurable_id
    · exact measurable_const
  have hF : Measurable fun p : ℝ × (Fin (K - (m + 1)) → ℝ) =>
      LcoreC E Jw cd.Cd (cvs J ω c) (mergeL (K - (m + 1)) p.2 (uvecX J m lab ω p.1)) := by
    have h1 : Measurable fun p : ℝ × (Fin (K - (m + 1)) → ℝ) =>
        (cvs J ω c, mergeL (K - (m + 1)) p.2 (uvecX J m lab ω p.1)) :=
      measurable_const.prodMk ((measurable_mergeL2 (K := K) _).comp
        (measurable_snd.prodMk (hU.comp measurable_fst)))
    have h2 := (RankFull.measurable_LcoreC2 E hJw cd.Cd).comp h1
    exact h2
  exact hF.lintegral_prod_right'

/-- The integral over the current pivot (in log coordinates) adds it to the processed pivots. -/
lemma lintegral_IzXC (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (lab : Fin m → ℕ)
    (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ∫⁻ t, invq t * IzXC J E cd Jw m lab ω c (Real.log t) = IzMC J E cd Jw m lab ω c := by
  have h1 : (fun t => invq t * IzXC J E cd Jw m lab ω c (Real.log t)) =
      (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹ * IzXC J E cd Jw m lab ω c
        (Real.log t)) := by
    funext t
    unfold invq
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [h1, lintegral_log_subst]
  obtain ⟨p, hp⟩ : ∃ p, K = m + 1 + p := ⟨K - (m + 1), by omega⟩
  have hKm : K - m = p + 1 := by omega
  have hKm1 : K - (m + 1) = p := by omega
  unfold IzMC IzXC
  rw [hKm, hKm1]
  have hmeas : Measurable fun s : Fin (p + 1) → ℝ =>
      LcoreC E Jw cd.Cd (cvs J ω c) (mergeL (K := K) (p + 1) s (uvec J m lab ω)) :=
    (RankFull.measurable_LcoreC E hJw cd.Cd _).comp (measurable_mergeL _ _)
  rw [lintegral_fin_succ _ hmeas]
  refine lintegral_congr fun x => lintegral_congr fun z => ?_
  rw [mergeL_cons hp]

lemma measurable_FbarC_t (hJw : MeasurableSet Jw) (m : ℕ) (ω : Ω) (lab : Fin m → ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) :
    Measurable fun t => FbarC J E l cd Jw smax G A Eu m ω lab c t := by
  unfold FbarC
  exact (((measurable_const.mul (measurable_invq)).mul
    ((measurable_IzXC hJw m lab ω c).comp Real.measurable_log)).mul measurable_const)

lemma lintegral_FbarC (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (ω : Ω)
    (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ∫⁻ t, FbarC J E l cd Jw smax G A Eu m ω lab c t =
      (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
        GammaBarC J l cd smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) *
        IzMC J E cd Jw m lab ω c * ENNReal.ofReal (cd.Wc) := by
  set a := (∏ j, (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω) * (decSet J c).indicator 1 ω *
    GammaBarC J l cd smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) with ha
  have : (fun t => FbarC J E l cd Jw smax G A Eu m ω lab c t) = fun t =>
      (a * ENNReal.ofReal (cd.Wc)) * (invq t * IzXC J E cd Jw m lab ω c (Real.log t)) := by
    funext t; simp only [FbarC, ha]; ring
  have hf : Measurable fun t => invq t * IzXC J E cd Jw m lab ω c (Real.log t) :=
    measurable_invq.mul ((measurable_IzXC hJw m lab ω c).comp Real.measurable_log)
  rw [this, lintegral_const_mul _ hf, lintegral_IzXC hJw hm, ha]
  ring

/-- `∫ Φ̄_m(ω, t) dt` as a sum over the labels and contents. -/
lemma lintegral_PhiBarMC (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (ω : Ω) :
    ∫⁻ t, PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m (ω, t) =
      ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
        if ∃ n, ConsC E l smax cd (m + 1) (Fin.snoc lab n) c then
          (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
            GammaBarC J l cd smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) *
            IzMC J E cd Jw m lab ω c * ENNReal.ofReal (cd.Wc)
        else 0 := by
  unfold PhiBarMC
  have hterm : ∀ (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ), Measurable fun t =>
      (if ∃ n, ConsC E l smax cd (m + 1) (Fin.snoc lab n) c then
        FbarC J E l cd Jw smax G A Eu m ω lab c t else 0) := by
    intro lab c
    split_ifs
    · exact measurable_FbarC_t hJw m ω lab c
    · exact measurable_const
  rw [lintegral_tsum fun lab => (Finset.measurable_sum _ fun c _ => hterm lab c).aemeasurable]
  refine tsum_congr fun lab => ?_
  rw [lintegral_finset_sum _ fun c _ => hterm lab c]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · exact lintegral_FbarC hJw hm ω lab c
  · exact lintegral_zero

end Integral


section ExtraLemmas

variable {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ} {smax : ℕ} {cd : CovD K}

lemma card_snoc_lt {m : ℕ} (lab : Fin m → ℕ) (n : ℕ) (g : ℕ) (hng : g < n) :
    (univ.filter fun j : Fin (m + 1) => (Fin.snoc lab n : Fin (m + 1) → ℕ) j < g).card =
      (univ.filter fun j : Fin m => lab j < g).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [if_neg (by omega), add_zero]

lemma rankC_snoc {m : ℕ} (lab : Fin m → ℕ) (n : ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) (g : Fin N)
    (hng : (g : ℕ) < n) : rankC cd (m + 1) (Fin.snoc lab n) c g = rankC cd m lab c g := by
  unfold rankC; rw [card_snoc_lt lab n g hng]

/-- The constraints pass to the next level inside a run (cover version). -/
lemma cons_nonlastC {m n : ℕ} {lab : Fin m → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hnl : runFirst l m < m) (hC : ConsC E l smax cd (m + 1) (Fin.snoc lab n) c) :
    ConsC E l smax cd m lab c := by
  refine ⟨cons_nonlast hnl hC.1, hC.2.1, fun y hy g => ?_, hC.2.2.2⟩
  rw [hC.2.2.1 y hy g]
  split_ifs with h
  · obtain ⟨y', -, hy'⟩ := h
    obtain ⟨-, -, hu0⟩ := cons_facts hC.1
    have hg := (hC.1.2.2.1 y' g hy').1 (Nat.succ_pos m)
    simp only [Nat.add_sub_cancel] at hg
    rw [rankC_snoc lab n c g (lt_of_lt_of_le hg hu0)]
  · rfl

end ExtraLemmas

section NonLast

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

theorem hnext_nonlastC (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 2 ≤ K)
    (hnl : runFirst l (m + 1) < m + 1) (ω : Ω) :
    ∫⁻ t, PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (m + 1) (ω, t) ≤
      ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m ω := by
  rw [lintegral_PhiBarMC hJw (by omega)]
  unfold ZSC
  refine ENNReal.tsum_le_tsum fun lab => Finset.sum_le_sum fun c _ => ?_
  by_cases hC : ∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c
  · obtain ⟨n, hn⟩ := hC
    have hC' := cons_nonlastC hnl hn
    rw [if_pos ⟨n, hn⟩, if_pos hC']
    refine le_of_eq ?_
    unfold FfullC GammaBarC
    rw [dif_pos hnl]
    have hrn := runNum_pred_of_not_first l hnl
    simp only [Nat.add_sub_cancel] at hrn
    have e1 : (Fin.snoc (Fin.init lab) (lab (Fin.last m)) : Fin (m + 1) → ℕ) = lab :=
      Fin.snoc_init_self lab
    have e2 : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    rw [e1, e2, hrn.1]
    have e3 : ∀ h, lab ⟨runFirst l m, h⟩ = lab ⟨runFirst l (m + 1), hnl⟩ :=
      fun h => congrArg lab (Fin.ext hrn.2)
    simp only [e3]
    have hIz : IzXC J E cd Jw m (Fin.init lab) ω c (Real.log (J.q (lab (Fin.last m)) ω)) =
        IzMC J E cd Jw (m + 1) lab ω c := by
      unfold IzXC IzMC; rw [uvecX_init]
    rw [hIz, Fin.prod_univ_castSucc (fun j => (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω),
      Fin.prod_univ_castSucc (fun j => invq (J.q (lab j) ω))]
    simp only [Fin.init]
    ring
  · rw [if_neg hC]; exact zero_le _

end NonLast

section Harvest

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {smax : ℕ}

/-- **The harvest of the block** `F_t` at the last pivot of the run `P_t`. -/
theorem IzMC_split (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    {m n : ℕ} (hmK : m + 1 ≤ K) {lab : Fin (m + 1) → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hC : ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) {ω : Ω} (hω : ω ∈ decSet J c) :
    IzMC J E cd Jw (m + 1) lab ω c =
      ENNReal.ofReal (∏ g ∈ suppW (hiC (lab (Fin.last m)) c),
        (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, hiC (lab (Fin.last m)) c y g)) *
      IzMC J E cd Jw (m + 1) lab ω (loC (lab (Fin.last m)) c) := by
  set b0 := lab (Fin.last m) with hb0
  set S := suppW (hiC b0 c) with hS
  set Pset : Set (Fin K) := {j | m + 1 ≤ (j : ℕ)} with hP
  set v : Fin N → Fin K → ℝ := fun g => vch E Pset (colW (hiC b0 c) g) with hv
  have hmem : ∀ g ∈ S, colW (hiC b0 c) g ∈ SpanSet E Pset := fun g hg =>
    (last_hi_mem hC.1 hg).2
  have hQ : ∀ g ∈ S, 0 < J.q g ω := by
    intro g hg
    obtain ⟨-, y, hy⟩ := mem_suppW_hiC.mp hg
    linarith [hq ω g (hω y g hy)]
  have hvW : ∀ g ∈ S, ∀ y, (hiC b0 c y g : ℝ) = ∑ j, (E y j : ℝ) * v g j := by
    intro g hg y
    exact (vch_spec (hmem g hg)).2 y
  have hsupp : ∀ g ∈ S, ∀ j : Fin K, (j : ℕ) < K - (K - (m + 1)) → v g j = 0 := by
    intro g hg j hj
    exact (vch_spec (hmem g hg)).1 j (by simp only [hP, Set.mem_setOf_eq]; omega)
  have hcv : cvs J ω c = fun y => cvs J ω (loC b0 c) y *
      ∏ g ∈ S, J.q g ω ^ (hiC b0 c y g) := by
    funext y
    exact cval_split (fun g => J.q g ω) (last_ne hC.1) y
  unfold IzMC
  rw [hcv]
  exact lintegral_LcoreC_shift E hJw cd.Cd (by omega) (uvec J (m + 1) lab ω) S (fun g => J.q g ω)
    hQ v
    (hiC b0 c) hvW hsupp (cvs J ω (loC b0 c))

end Harvest


section LastConsC

variable {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ} {smax : ℕ} {cd : CovD K}
variable {m n : ℕ} {lab : Fin (m + 1) → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}

/-- The number of slots of `P(C)` in a content. -/
noncomputable def nC (cd : CovD K) (c : Fin K → (Fin N → ℕ) × ℕ) : ℕ :=
  (univ.filter fun g' : Fin N => ∃ y ∈ cd.Cd, (c y).1 g' ≠ 0).card

lemma lab_lt_n (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) (j : Fin (m + 1)) :
    lab j < n := by
  have := hC.1 (Fin.castSucc_lt_last j)
  rwa [snoc_cs, Fin.snoc_last] at this

lemma slot_lt_n (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) {y : Fin K} {g : Fin N}
    (hg : (c y).1 g ≠ 0) : (g : ℕ) < n := by
  have := (hC.2.2.1 y g hg).1 (Nat.succ_pos _)
  simp only [Nat.add_sub_cancel] at this
  have e : (⟨runFirst l (m + 1), lt_of_le_of_lt (runFirst_le l (m + 1)) (by omega)⟩ :
      Fin (m + 1 + 1)) = Fin.last (m + 1) := Fin.ext (by simp [hfirst])
  rw [e, Fin.snoc_last] at this
  exact this

lemma last_loC (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) :
    ConsC E l smax cd (m + 1) lab (loC (lab (Fin.last m)) c) := by
  have hb0n := lab_lt_n hC.1 (Fin.last m)
  refine ⟨last_lo hfirst hC.1, fun g hg => ?_, fun y hy g => ?_, fun y hy => hC.2.2.2 y hy⟩
  · obtain ⟨y, hy⟩ := hg
    simp only [loC] at hy
    split_ifs at hy with hlt
    · obtain ⟨y', hy'C, hy'⟩ := hC.2.1 g ⟨y, hy⟩
      exact ⟨y', hy'C, by simp only [loC, if_pos hlt]; exact hy'⟩
    · exact absurd rfl hy
  · simp only [loC]
    by_cases hlt : (g : ℕ) < lab (Fin.last m)
    · rw [if_pos hlt, hC.2.2.1 y hy g]
      have hiff : (∃ y' ∈ cd.Cd, (c y').1 g ≠ 0) ↔
          ∃ y' ∈ cd.Cd, (if (g : ℕ) < lab (Fin.last m) then (c y').1 g else 0) ≠ 0 := by
        simp [hlt]
      by_cases h : ∃ y' ∈ cd.Cd, (c y').1 g ≠ 0
      · rw [if_pos h, if_pos (hiff.mp h)]
        congr 1
        rw [rankC_snoc lab n c g (by omega)]
        unfold rankC
        congr 1
        congr 1
        ext g'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, loC]
        constructor
        · rintro ⟨h1, y', hy'C, hy'⟩
          exact ⟨h1, y', hy'C, by rw [if_pos (by omega)]; exact hy'⟩
        · rintro ⟨h1, y', hy'C, hy'⟩
          refine ⟨h1, y', hy'C, ?_⟩
          rwa [if_pos (by omega)] at hy'
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · rw [if_neg hlt, if_neg]
      rintro ⟨y', -, hy'⟩
      simp only [if_neg hlt] at hy'
      exact hy' rfl

/-- The rank of a slot of the block just completed. -/
lemma rank_hi (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) {g : Fin N}
    (hg : g ∈ suppW (hiC (lab (Fin.last m)) c)) :
    rankC cd (m + 1 + 1) (Fin.snoc lab n) c g =
      m + 1 + nC cd (loC (lab (Fin.last m)) c) +
        ((suppW (hiC (lab (Fin.last m)) c)).filter (· < g)).card := by
  obtain ⟨hb, y₀, hy₀⟩ := mem_suppW_hiC.mp hg
  have hgn : (g : ℕ) < n := slot_lt_n hfirst hC.1 hy₀
  have hle : ∀ j : Fin (m + 1), lab j ≤ lab (Fin.last m) := fun j => by
    have := hC.1.1.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
    rwa [snoc_cs, snoc_cs] at this
  unfold rankC
  have h1 : (univ.filter fun j : Fin (m + 1 + 1) =>
      (Fin.snoc lab n : Fin (m + 1 + 1) → ℕ) j < g).card
      = m + 1 := by
    rw [Finset.card_filter, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [if_neg (by omega), add_zero]
    have : ∀ j : Fin (m + 1), (if lab j < (g : ℕ) then 1 else 0) = 1 := fun j => by
      rw [if_pos (lt_of_le_of_lt (hle j) hb)]
    simp [this]
  have hne := last_ne hC.1
  have hset : (univ.filter fun g' : Fin N => g' < g ∧ ∃ y ∈ cd.Cd, (c y).1 g' ≠ 0) =
      (univ.filter fun g' : Fin N => ∃ y ∈ cd.Cd, (loC (lab (Fin.last m)) c y).1 g' ≠ 0) ∪
        (suppW (hiC (lab (Fin.last m)) c)).filter (· < g) := by
    ext g'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, loC]
    constructor
    · rintro ⟨h1, y, hyC, hy⟩
      by_cases hlt : (g' : ℕ) < lab (Fin.last m)
      · exact Or.inl ⟨y, hyC, by rw [if_pos hlt]; exact hy⟩
      · have hne' := hne y g' hy
        exact Or.inr ⟨mem_suppW_hiC.mpr ⟨by omega, y, hy⟩, h1⟩
    · rintro (⟨y, hyC, hy⟩ | ⟨hg', h1⟩)
      · split_ifs at hy with hlt
        · exact ⟨Fin.lt_def.mpr (by omega), y, hyC, hy⟩
        · exact absurd rfl hy
      · obtain ⟨-, y, hy⟩ := mem_suppW_hiC.mp hg'
        exact ⟨h1, hC.2.1 g' ⟨y, hy⟩⟩
  rw [h1, hset, Finset.card_union_of_disjoint]
  · unfold nC; ring
  · rw [Finset.disjoint_left]
    intro g' h1 h2
    obtain ⟨y, -, hy⟩ := (Finset.mem_filter.mp h1).2
    simp only [loC] at hy
    split_ifs at hy with hlt
    · have := (mem_suppW_hiC.mp (Finset.mem_filter.mp h2).1).1
      omega
    · exact hy rfl

end LastConsC

section LastC

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}


lemma prod_inv_eq_suppC (q : Fin N → ℝ) (W : Fin K → Fin N → ℕ) :
    ∏ g, (q g)⁻¹ ^ (∑ y ∈ cd.Cd, W y g) = ∏ g ∈ suppW W, (q g)⁻¹ ^ (∑ y ∈ cd.Cd, W y g) := by
  refine (Finset.prod_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
  have : ∑ y ∈ cd.Cd, W y g = 0 := Finset.sum_eq_zero fun y _ => by
    by_contra h; exact hg (mem_suppW.mpr ⟨y, h⟩)
  rw [this, pow_zero]

lemma ZSC_term_eq (m : ℕ) (ω : Ω) (lab : Fin (m + 1) → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    (J.A (lab (Fin.last m))).indicator 1 ω *
      FfullC J E l cd Jw G A Eu m ω (Fin.init lab) (lab (Fin.last m)) c (J.q (lab (Fin.last m)) ω) =
    (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
      ((G (lab (Fin.last m))).indicator 1 ω * PhiC (N := N) J cd.lg A Eu (runNum l m) ω
        (lab ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩)) *
      (∏ j, invq (J.q (lab j) ω)) * IzMC J E cd Jw (m + 1) lab ω c *
      ENNReal.ofReal (cd.Wc) := by
  unfold FfullC
  have e1 : (Fin.snoc (Fin.init lab) (lab (Fin.last m)) : Fin (m + 1) → ℕ) = lab :=
    Fin.snoc_init_self lab
  have hIz : IzXC J E cd Jw m (Fin.init lab) ω c (Real.log (J.q (lab (Fin.last m)) ω)) =
      IzMC J E cd Jw (m + 1) lab ω c := by
    unfold IzXC IzMC; rw [uvecX_init]
  rw [e1, hIz, Fin.prod_univ_castSucc (fun j => (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω),
    Fin.prod_univ_castSucc (fun j => invq (J.q (lab j) ω))]
  simp only [Fin.init]
  ring

/-- **(S3)(a)** for a block whose columns are in the span of the pivots `≥ p`, completing the
run `r` (general form). -/
theorem blockSumEC_gen [NeZero N] (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (lg : List ℕ) (r : ℕ) (hrlen : r < lg.length) (R : Finset (Fin K))
    (hRC : R ⊆ cd.Cd) (hdsum : (lg.drop r).sum = R.card)
    (Col : Finset (Fin N) → Fin N → Set (Fin K → ℕ))
    (hinj : ∀ S g, ∀ w ∈ Col S g, ∀ w' ∈ Col S g, (∀ y ∈ R, w y = w' y) → w = w')
    (hnz : ∀ S g, ∀ w ∈ Col S g, ∃ y ∈ R, w y ≠ 0) (ω : Ω)
    (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) (b : ℕ) :
    ∑ W ∈ Wset K N D, (if BlockOKC (fun g : Fin N => ω ∈ J.A g) b Col W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J lg A Eu r ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, W y g)) else 0) ≤
      ENNReal.ofReal (GRun A (lg.drop r) (EuSω (N := N) J Eu ω b) /
        EuSω (N := N) J Eu ω b ^ (lg.drop r).sum) := by
  have hdrop : lg.drop r = lg[r] :: lg.drop (r + 1) := List.drop_eq_getElem_cons hrlen
  have hcard : R.card = (lg.drop (r + 1)).sum + lg[r] := by
    rw [← hdsum, hdrop, List.sum_cons]; ring
  obtain ⟨hG0, hGanti⟩ := GRun_nonneg_antitone A (lg.drop (r + 1))
  have bs := blockSum_leC D R cd.Cd hRC Col hinj hnz
    (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) (fun g hg => hq ω g hg) hEu b smax
    (fun u => ω ∈ G u) hS3 hcard hG0 hGanti
  -- the left side as `ofReal` of the real sum
  have hterm : ∀ W ∈ Wset K N D, (if BlockOKC (fun g : Fin N => ω ∈ J.A g) b Col W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J lg A Eu r ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, W y g)) else 0) =
      ENNReal.ofReal (if BlockOKC (fun g : Fin N => ω ∈ J.A g) b Col W then
        chiB smax (fun u => ω ∈ G u) (uW W) *
          (GRun A (lg.drop (r + 1))
            (EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W)) /
            EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W) ^
              (lg.drop (r + 1)).sum) *
          ∏ g : Fin N, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, W y g) else 0) := by
    intro W _
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      have hc0 : 0 ≤ chiB smax (fun u => ω ∈ G u) (uW W) := by
        unfold chiB; split_ifs <;> norm_num
      have hp0 : 0 ≤ ∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, W y g) :=
        Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
          linarith [hq ω g (hB.2 g hg).1])) _
      rw [prod_inv_eq_suppC (fun g => J.q g ω) W, PhiC, EuSω]
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (mul_nonneg hc0
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _)))]
    · simp
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun W _ => by
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      refine mul_nonneg (mul_nonneg (by unfold chiB; split_ifs <;> norm_num)
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _))) ?_
      rw [prod_inv_eq_suppC (fun g => J.q g ω) W]
      exact Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
        linarith [hq ω g (hB.2 g hg).1])) _
    · exact le_rfl)]
  unfold EuSω
  rw [hdrop, GRun_cons, List.sum_cons]
  refine ENNReal.ofReal_le_ofReal (le_trans bs (le_of_eq ?_))
  rw [hcard]
  ring_nf

theorem hnext_lastC (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K)
    (hlg : cd.lg = joinC E cd.Cd l)
    {m : ℕ} (hm : m + 2 ≤ K) (hfirst : runFirst l (m + 1) = m + 1) (ω : Ω)
    (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) :
    ∫⁻ t, PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (m + 1) (ω, t) ≤
      ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu m ω := by
  rw [lintegral_PhiBarMC hJw (by omega)]
  unfold ZSC
  refine ENNReal.tsum_le_tsum fun lab => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- no slots: no admissible labels
    refine le_of_eq_of_le (Finset.sum_eq_zero fun c _ => ?_) (zero_le _)
    rw [if_neg]
    rintro ⟨n, hn⟩
    have := (hn.1.2.1 0).1
    omega
  haveI : NeZero N := ⟨by omega⟩
  set b0 := lab (Fin.last m) with hb0
  set b := lab ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩ with hb
  set W := ENNReal.ofReal (cd.Wc) with hW
  set Col : (Fin K → (Fin N → ℕ) × ℕ) → Finset (Fin N) → Fin N → Set (Fin K → ℕ) :=
    fun c' S g => {w | w ∈ SpanSet E {j : Fin K | m + 1 ≤ (j : ℕ)} ∧ (∃ y ∈ cd.Cd, w y ≠ 0) ∧
      ∀ y ∉ cd.Cd, w y = cd.mono y (m + 1 + nC cd c' + (S.filter (· < g)).card)} with hCol
  set X : (Fin K → (Fin N → ℕ) × ℕ) → ℝ≥0∞ := fun c' =>
    (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c').indicator 1 ω *
      (G b0).indicator 1 ω * (∏ j, invq (J.q (lab j) ω)) * IzMC J E cd Jw (m + 1) lab ω c' * W
    with hX
  set Y : (Fin K → (Fin N → ℕ) × ℕ) → (Fin K → Fin N → ℕ) → ℝ≥0∞ := fun c' Wc =>
    if BlockOKC (fun g : Fin N => ω ∈ J.A g) b (Col c') Wc then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW Wc)) *
        PhiC (N := N) J cd.lg A Eu (runNum l (m + 1)) ω (uW Wc) *
        ENNReal.ofReal (∏ g ∈ suppW Wc, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, Wc y g)) else 0 with hY
  set sC := (contents K N D Dmax X₀).filter (ConsC E l smax cd (m + 1) lab) with hsC
  -- each term factors through the split
  have hfac : ∀ c ∈ contents K N D Dmax X₀,
      (if ∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c then
        (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
          GammaBarC J l cd smax G A Eu (m + 1) ω lab c * (∏ j, invq (J.q (lab j) ω)) *
          IzMC J E cd Jw (m + 1) lab ω c * W else 0) ≤
      if (∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c then
        X (loC b0 c) * Y (loC b0 c) (hiC b0 c) else 0 := by
    intro c _
    by_cases hC : ∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c
    · obtain ⟨n, hn⟩ := hC
      rw [if_pos ⟨n, hn⟩]
      by_cases hω : ω ∈ decSet J c
      · rw [if_pos ⟨⟨n, hn⟩, hω⟩]
        have hωlo : ω ∈ decSet J (loC b0 c) := by
          intro y g hg
          simp only [loC] at hg
          split_ifs at hg with h
          · exact hω y g hg
          · exact absurd rfl hg
        have hBlk : BlockOKC (fun g : Fin N => ω ∈ J.A g) b (Col (loC b0 c)) (hiC b0 c) := by
          refine ⟨last_hi_ne hfirst hn.1, fun g hg => ?_⟩
          obtain ⟨hb1, hcol⟩ := last_hi_mem hn.1 hg
          obtain ⟨hgb, y, hy⟩ := mem_suppW_hiC.mp hg
          refine ⟨hω y g hy, hb1, hcol, ?_, fun y' hy' => ?_⟩
          · obtain ⟨y', hy'C, hy'⟩ := hn.2.1 g ⟨y, hy⟩
            exact ⟨y', hy'C, by simp only [colW, hiC, if_pos hgb]; exact hy'⟩
          · simp only [colW, hiC, if_pos hgb]
            rw [hn.2.2.1 y' hy' g, if_pos (hn.2.1 g ⟨y, hy⟩), rank_hi hfirst hn hg]
        have hnot : ¬ runFirst l (m + 1) < m + 1 := by omega
        unfold GammaBarC
        rw [dif_neg hnot, dif_pos (by omega), IzMC_split hJw hq (by omega) hn hω,
          last_uOf hfirst hn.1]
        simp only [hX, hY, if_pos hBlk, Set.indicator_of_mem hω, Set.indicator_of_mem hωlo]
        have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
        rw [e]
        refine le_of_eq ?_
        ring
      · rw [if_neg (fun h => hω h.2), Set.indicator_of_notMem hω]; simp
    · rw [if_neg hC]; exact zero_le _
  refine (Finset.sum_le_sum hfac).trans ?_
  -- the injection into pairs
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun c => (loC b0 c, hiC b0 c))
      (↑((contents K N D Dmax X₀).filter fun c =>
        (∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c) :
          Set (Fin K → (Fin N → ℕ) × ℕ)) := by
    intro c hc c' hc' h
    obtain ⟨⟨n, hn⟩, -⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨⟨n', hn'⟩, -⟩ := (Finset.mem_filter.mp hc').2
    exact split_inj (last_ne hn.1) (last_ne hn'.1) (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hmaps : ∀ c ∈ (contents K N D Dmax X₀).filter (fun c =>
      (∃ n, ConsC E l smax cd (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c),
      (loC b0 c, hiC b0 c) ∈ sC ×ˢ Wset K N D := by
    intro c hc
    obtain ⟨hc1, ⟨n, hn⟩, -⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨loC_mem hc1, last_loC hfirst hn⟩,
      hiC_mem hc1⟩
  have h1 := sumE_comp_le_of_injOn _ _ _ hmaps hinj (fun p => X p.1 * Y p.1 p.2)
  refine h1.trans ?_
  rw [Finset.sum_product]
  have hblk : ∀ c', ∑ Wc ∈ Wset K N D, Y c' Wc ≤
      PhiC (N := N) J cd.lg A Eu (runNum l m) ω b := by
    intro c'
    set r := runNum l (m + 1) with hr
    have hr' : runNum l m + 1 = r := by
      have := runNum_pred_of_first l (j := m + 1) (by omega) (by omega) hfirst hpos
      simpa using this
    have hrlen : r < l.length := runNum_lt_length l (by omega)
    have htake : (l.take r).sum = m + 1 := by
      have h1 := sum_drop_runNum l (j := m + 1) (by omega)
      have h2 := List.sum_take_add_sum_drop l r
      rw [hfirst, ← hr] at h1
      have h4 : m + 1 ≤ l.sum := by omega
      omega
    set R := SR E cd.Cd (m + 1) ∩ cd.Cd with hR
    have hdsum : (cd.lg.drop r).sum = R.card := by
      rw [hlg, joinC_drop_sum E hE cd.Cd l hsum hrlen.le, htake]; rfl
    have hbs := blockSumEC_gen (D := D) (G := G) (A := A) (smax := smax) (cd := cd) hq hEu
      cd.lg r (by rw [hlg, joinC_length]; exact hrlen) R Finset.inter_subset_right hdsum
      (Col c') (fun S g w hw w' hw' hagree => by
        obtain ⟨hw1, -, hw3⟩ := hw
        obtain ⟨hw1', -, hw3'⟩ := hw'
        refine SR_det E hE cd.Cd (m + 1) hw1 hw1' fun y hy => ?_
        by_cases hyC : y ∈ cd.Cd
        · exact hagree y (Finset.mem_inter.mpr ⟨hy, hyC⟩)
        · rw [hw3 y hyC, hw3' y hyC])
      (fun S g w hw => by
        obtain ⟨hw1, hw2, -⟩ := hw
        obtain ⟨y, hy, hyw⟩ := SR_cover E cd.Cd (m + 1) hw1 hw2
        exact ⟨y, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).2, (Finset.mem_inter.mp hy).1⟩,
          hyw⟩) ω hS3 b
    refine le_trans hbs (le_of_eq ?_)
    unfold PhiC
    rw [hr']
  calc ∑ c' ∈ sC, ∑ Wc ∈ Wset K N D, X (c', Wc).1 * Y (c', Wc).1 (c', Wc).2
      = ∑ c' ∈ sC, X c' * ∑ Wc ∈ Wset K N D, Y c' Wc := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ c' ∈ sC, X c' * PhiC (N := N) J cd.lg A Eu (runNum l m) ω b :=
        Finset.sum_le_sum fun c' _ => mul_le_mul_left' (hblk c') _
    _ = _ := by
        rw [hsC, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c' _ => ?_
        split_ifs
        · rw [ZSC_term_eq, hX]
          ring
        · rfl

end LastC

section FinalC

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma lintegral_LcoreC_full (hE : (Ereal E).det ≠ 0) (hJw : MeasurableSet Jw) (d : Fin K → ℝ)
    (hd : ∀ y, 0 < d y) {z : ℝ} (hz : 0 < z) (hJz : Jw ⊆ Set.Ici z) (u : Fin K → ℝ) :
    ∫⁻ zz : Fin (K - 0) → ℝ, LcoreC E Jw cd.Cd d (mergeL (K - 0) zz u) ≤
      ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (if y ∈ cd.Cd then
        ENNReal.ofReal (d y)⁻¹ * MeasureTheory.volume Jw
        else ENNReal.ofReal z⁻¹ * MeasureTheory.volume Jw) := by
  simp_rw [mergeL_full]
  exact final_volumeC E hE hJw cd.Cd d hd hz hJz

/-- The FAC shift of all the free slots, at the end (cover version). -/
theorem IzMC_final (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    {lab : Fin 0 → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hspan : ∀ g ∈ suppW (freeW c), colW (freeW c) g ∈ SpanSet E {j | 0 ≤ (j : ℕ)})
    {ω : Ω} (hω : ω ∈ decSet J c) :
    IzMC J E cd Jw 0 lab ω c = ENNReal.ofReal (∏ g ∈ suppW (freeW c),
        (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, freeW c y g)) *
      ∫⁻ zz : Fin (K - 0) → ℝ, LcoreC E Jw cd.Cd (fun y => (tailsC c y : ℝ))
        (mergeL (K - 0) zz (uvec J 0 lab ω)) := by
  set S := suppW (freeW c) with hS
  set v : Fin N → Fin K → ℝ := fun g => vch E {j | 0 ≤ (j : ℕ)} (colW (freeW c) g) with hv
  have hQ : ∀ g ∈ S, 0 < J.q g ω := by
    intro g hg
    obtain ⟨y, hy⟩ := mem_suppW.mp hg
    linarith [hq ω g (hω y g hy)]
  have hvW : ∀ g ∈ S, ∀ y, (freeW c y g : ℝ) = ∑ j, (E y j : ℝ) * v g j := fun g hg y =>
    (vch_spec (hspan g hg)).2 y
  have hcv : cvs J ω c = fun y => (tailsC c y : ℝ) * ∏ g ∈ S, J.q g ω ^ (freeW c y g) := by
    funext y
    unfold cvs cval
    congr 1
    refine (Finset.prod_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
    have : (c y).1 g = 0 := by by_contra h; exact hg (mem_suppW.mpr ⟨y, h⟩)
    simp [freeW, this]
  unfold IzMC
  rw [hcv]
  exact lintegral_LcoreC_shift E hJw cd.Cd (by omega) (uvec J 0 lab ω) S (fun g => J.q g ω) hQ
    v (freeW c) hvW (fun g _ j hj => by omega) (fun y => (tailsC c y : ℝ))

lemma prod_ite_memC {K : ℕ} (Cd : Finset (Fin K)) (a b : ℝ≥0∞) :
    ∏ y, (if y ∈ Cd then a else b) = a ^ Cd.card * b ^ (K - Cd.card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_not,
    Finset.card_sdiff]
  simp

lemma rank_final {lab : Fin 0 → ℕ} {n : ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hC : ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c) {g : Fin N} {y : Fin K}
    (hy : (c y).1 g ≠ 0) :
    rankC cd (0 + 1) (Fin.snoc lab n) c g = ((suppW (freeW c)).filter (· < g)).card := by
  have hg := (hC.1.2.2.1 y g hy).1 (Nat.succ_pos 0)
  have e : (⟨runFirst l (0 + 1 - 1), lt_of_le_of_lt (runFirst_le l (0 + 1 - 1)) (by omega)⟩ :
      Fin (0 + 1)) = Fin.last 0 := Fin.ext (by have := runFirst_le l 0; simp at this ⊢; omega)
  rw [e, Fin.snoc_last] at hg
  rw [rankC_snoc lab n c g hg]
  unfold rankC
  simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, zero_add]
  congr 1
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suppW, freeW]
  constructor
  · rintro ⟨h1, y', -, hy'⟩; exact ⟨⟨y', hy'⟩, h1⟩
  · rintro ⟨⟨y', hy'⟩, h1⟩; exact ⟨h1, hC.2.1 g' ⟨y', hy'⟩⟩

/-- **The end step** (cover version): the FAC shift of all the free slots, the Volume Lemma
with the rows outside `C` costing `vol(J)/z`, the early block and the tails. -/
theorem hnext_finalC (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K)
    (hlg : cd.lg = joinC E cd.Cd l)
    (hK : 1 ≤ K) (ω : Ω) (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    {a δ z : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) (hz : 0 < z)
    (hJz : Jw ⊆ Set.Ici z) (htail : tailSum Dmax X₀ ≤ Eu) (hWc : 0 ≤ cd.Wc) :
    ∫⁻ t, PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu 0 (ω, t) ≤
      ENNReal.ofReal (finG A cd.lg Eu * δ ^ K * z⁻¹ ^ (K - cd.Cd.card) * cd.Wc) := by
  rw [lintegral_PhiBarMC hJw (by omega)]
  rw [tsum_eq_single (Fin.elim0 : Fin 0 → ℕ) (fun b hb => absurd (Subsingleton.elim b _) hb)]
  set lab : Fin 0 → ℕ := Fin.elim0
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun c _ => ?_) (zero_le _)
    rw [if_neg]
    rintro ⟨n, hn⟩
    have := (hn.1.2.1 0).1
    omega
  haveI : NeZero N := ⟨by omega⟩
  set W := ENNReal.ofReal (cd.Wc) with hW
  set Col : Finset (Fin N) → Fin N → Set (Fin K → ℕ) := fun S g =>
    {w | w ∈ SpanSet E {j : Fin K | 0 ≤ (j : ℕ)} ∧ (∃ y ∈ cd.Cd, w y ≠ 0) ∧
      ∀ y ∉ cd.Cd, w y = cd.mono y ((S.filter (· < g)).card)} with hCol
  set Ywt : (Fin K → Fin N → ℕ) → ℝ≥0∞ := fun Wc =>
    ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW Wc)) *
      PhiC (N := N) J cd.lg A Eu 0 ω (uW Wc) *
      ENNReal.ofReal (∏ g ∈ suppW Wc, (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, Wc y g)) with hYwt
  set Zt : (Fin K → ℕ) → ℝ≥0∞ := fun d =>
    ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (if y ∈ cd.Cd then
      ENNReal.ofReal ((d y : ℝ))⁻¹ * MeasureTheory.volume Jw
      else ENNReal.ofReal z⁻¹ * MeasureTheory.volume Jw) with hZt
  set WF := (Wset K N D).filter fun Wc => Wc = 0 ∨ BlockOKC (fun g : Fin N => ω ∈ J.A g) 0 Col Wc
    with hWF
  set TS := Fintype.piFinset fun y : Fin K =>
    if y ∈ cd.Cd then Nat.smoothNumbersUpTo Dmax X₀ else {cd.tailR y} with hTS
  have hrn0 : runNum l 0 = 0 := runNum_zero l hpos
  -- each term is bounded through the split into the free part and the tails
  have hfac : ∀ c ∈ contents K N D Dmax X₀,
      (if ∃ n, ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c then
        (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
          GammaBarC J l cd smax G A Eu 0 ω lab c * (∏ j, invq (J.q (lab j) ω)) *
          IzMC J E cd Jw 0 lab ω c * W else 0) ≤
      if (∃ n, ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c then
        Ywt (freeW c) * Zt (tailsC c) * W else 0 := by
    intro c hc
    by_cases hC : ∃ n, ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c
    · obtain ⟨n, hn⟩ := hC
      rw [if_pos ⟨n, hn⟩]
      by_cases hω : ω ∈ decSet J c
      · rw [if_pos ⟨⟨n, hn⟩, hω⟩]
        have hspan : ∀ g ∈ suppW (freeW c), colW (freeW c) g ∈
            SpanSet E {j : Fin K | 0 ≤ (j : ℕ)} := by
          intro g hg
          obtain ⟨y, hy⟩ := mem_suppW.mp hg
          exact SpanSet_mono (fun j _ => Nat.zero_le _) ((hn.1.2.2.1 y g hy).2.2)
        have hd : ∀ y, 0 < (tailsC c y : ℝ) := by
          intro y
          rw [contents, Fintype.mem_piFinset] at hc
          have := (Finset.mem_product.mp (hc y)).2
          exact_mod_cast smooth_pos this
        unfold GammaBarC
        rw [dif_neg (by omega), dif_neg (by omega), IzMC_final hJw hq hspan hω, hrn0]
        simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, mul_one,
          Set.indicator_of_mem hω, Pi.one_apply, hYwt, hZt]
        have huw : uOf c = uW (freeW c) := rfl
        rw [huw]
        have hint := lintegral_LcoreC_full (cd := cd) hE hJw (fun y => (tailsC c y : ℝ)) hd hz
          hJz (uvec J 0 lab ω)
        calc ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW (freeW c))) *
              PhiC (N := N) J cd.lg A Eu 0 ω (uW (freeW c)) *
              (ENNReal.ofReal (∏ g ∈ suppW (freeW c),
                (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, freeW c y g)) *
                ∫⁻ zz : Fin (K - 0) → ℝ, LcoreC E Jw cd.Cd (fun y => (tailsC c y : ℝ))
                  (mergeL (K - 0) zz (uvec J 0 lab ω))) * W
            ≤ ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW (freeW c))) *
              PhiC (N := N) J cd.lg A Eu 0 ω (uW (freeW c)) *
              (ENNReal.ofReal (∏ g ∈ suppW (freeW c),
                (J.q g ω)⁻¹ ^ (∑ y ∈ cd.Cd, freeW c y g)) *
                (ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (if y ∈ cd.Cd then
                  ENNReal.ofReal ((tailsC c y : ℝ))⁻¹ * MeasureTheory.volume Jw
                  else ENNReal.ofReal z⁻¹ * MeasureTheory.volume Jw))) * W := by gcongr
          _ = _ := by ring
      · rw [if_neg (fun h => hω h.2), Set.indicator_of_notMem hω]; simp
    · rw [if_neg hC]; exact zero_le _
  refine (Finset.sum_le_sum hfac).trans ?_
  rw [← Finset.sum_filter]
  -- the injection into pairs (free part, tails)
  have hinj : Set.InjOn (fun c => (freeW c, tailsC c))
      (↑((contents K N D Dmax X₀).filter fun c =>
        (∃ n, ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c) :
          Set (Fin K → (Fin N → ℕ) × ℕ)) := by
    intro c _ c' _ h
    funext y
    have h1 := congrFun (congrArg Prod.fst h) y
    have h2 := congrFun (congrArg Prod.snd h) y
    exact Prod.ext (funext fun g => congrFun h1 g) h2
  have hmaps : ∀ c ∈ (contents K N D Dmax X₀).filter (fun c =>
      (∃ n, ConsC E l smax cd (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c),
      (freeW c, tailsC c) ∈ WF ×ˢ TS := by
    intro c hc
    obtain ⟨hc1, ⟨n, hn⟩, hω⟩ := Finset.mem_filter.mp hc
    rw [contents, Fintype.mem_piFinset] at hc1
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Wset, Fintype.mem_piFinset]
      intro y
      have := (Finset.mem_product.mp (hc1 y)).1
      rw [Fintype.mem_piFinset] at this ⊢
      exact this
    · by_cases h0 : freeW c = 0
      · exact Or.inl h0
      · refine Or.inr ⟨?_, fun g hg => ?_⟩
        · by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          apply h0
          funext y g
          by_contra h
          have : g ∈ suppW (freeW c) := mem_suppW.mpr ⟨y, h⟩
          rw [hne] at this; exact absurd this (Finset.notMem_empty _)
        · obtain ⟨y, hy⟩ := mem_suppW.mp hg
          refine ⟨hω y g hy, Nat.zero_le _,
            SpanSet_mono (fun j _ => Nat.zero_le _) ((hn.1.2.2.1 y g hy).2.2), ?_, ?_⟩
          · exact hn.2.1 g ⟨y, hy⟩
          · intro y' hy'
            simp only [colW, freeW]
            rw [hn.2.2.1 y' hy' g, if_pos (hn.2.1 g ⟨y, hy⟩), rank_final hn hy]
    · rw [hTS, Fintype.mem_piFinset]
      intro y
      by_cases hy : y ∈ cd.Cd
      · rw [if_pos hy]; exact (Finset.mem_product.mp (hc1 y)).2
      · rw [if_neg hy, Finset.mem_singleton]; exact hn.2.2.2 y hy
  have h1 := sumE_comp_le_of_injOn _ _ _ hmaps hinj (fun p => Ywt p.1 * Zt p.2 * W)
  refine h1.trans ?_
  rw [Finset.sum_product]
  have hsplit : ∑ Wc ∈ WF, ∑ d ∈ TS, Ywt (Wc, d).1 * Zt (Wc, d).2 * W =
      (∑ Wc ∈ WF, Ywt Wc) * (∑ d ∈ TS, Zt d) * W := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Wc _ => ?_
    rw [Finset.sum_mul]
  rw [hsplit]
  -- the tails
  have hdet : ENNReal.ofReal |(Ereal E).det⁻¹| ≤ 1 := by
    have := RankFull.Config.one_le_abs_det hE
    rw [abs_inv]
    exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ this)
  have hvol : MeasureTheory.volume Jw ≤ ENNReal.ofReal δ := by
    calc MeasureTheory.volume Jw ≤ MeasureTheory.volume (Set.Ico a (a + δ)) :=
          MeasureTheory.measure_mono hJ
      _ = ENNReal.ofReal δ := by rw [Real.volume_Ico]; congr 1; ring
  set f : Fin K → ℕ → ℝ≥0∞ := fun y e => if y ∈ cd.Cd then
    ENNReal.ofReal ((e : ℝ))⁻¹ * ENNReal.ofReal δ else ENNReal.ofReal z⁻¹ * ENNReal.ofReal δ
    with hf
  have htails : ∑ d ∈ TS, Zt d ≤ (ENNReal.ofReal Eu * ENNReal.ofReal δ) ^ cd.Cd.card *
      (ENNReal.ofReal z⁻¹ * ENNReal.ofReal δ) ^ (K - cd.Cd.card) := by
    calc ∑ d ∈ TS, Zt d ≤ ∑ d ∈ TS, ∏ y, f y (d y) := by
          refine Finset.sum_le_sum fun d _ => ?_
          simp only [hZt]
          calc _ ≤ 1 * ∏ y, f y (d y) := by
                refine mul_le_mul' hdet (Finset.prod_le_prod' fun y _ => ?_)
                simp only [hf]
                split_ifs
                · exact mul_le_mul_left' hvol _
                · exact mul_le_mul_left' hvol _
            _ = _ := one_mul _
      _ = ∏ y, ∑ e ∈ (if y ∈ cd.Cd then Nat.smoothNumbersUpTo Dmax X₀ else {cd.tailR y}),
            f y e := by rw [hTS, Finset.prod_univ_sum]
      _ ≤ ∏ y, (if y ∈ cd.Cd then ENNReal.ofReal Eu * ENNReal.ofReal δ
            else ENNReal.ofReal z⁻¹ * ENNReal.ofReal δ) := by
          refine Finset.prod_le_prod' fun y _ => ?_
          by_cases hy : y ∈ cd.Cd
          · simp only [hf, if_pos hy]
            rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
            gcongr
            exact htail
          · simp only [hf, if_neg hy, Finset.sum_singleton, le_refl]
      _ = _ := prod_ite_memC cd.Cd _ _
  -- the free part: the empty content and the non-empty contents
  have h0mem : (0 : Fin K → Fin N → ℕ) ∈ Wset K N D := by
    rw [Wset, Fintype.mem_piFinset]; intro y; rw [Fintype.mem_piFinset]; intro g; simp
  have hsupp0 : suppW (0 : Fin K → Fin N → ℕ) = ∅ := by
    ext g; simp [mem_suppW]
  have hnot0 : ¬ BlockOKC (fun g : Fin N => ω ∈ J.A g) 0 Col (0 : Fin K → Fin N → ℕ) := by
    rintro ⟨hne, -⟩; rw [hsupp0] at hne; exact Finset.not_nonempty_empty hne
  have hWF : WF = insert 0 ((Wset K N D).filter
      (BlockOKC (fun g : Fin N => ω ∈ J.A g) 0 Col)) := by
    ext Wc
    simp only [hWF, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hm, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hm, h⟩
    · rintro (rfl | ⟨hm, h⟩)
      · exact ⟨h0mem, Or.inl rfl⟩
      · exact ⟨hm, Or.inr h⟩
  have hnotin : (0 : Fin K → Fin N → ℕ) ∉ (Wset K N D).filter
      (BlockOKC (fun g : Fin N => ω ∈ J.A g) 0 Col) := fun h =>
    hnot0 (Finset.mem_filter.mp h).2
  rw [hWF, Finset.sum_insert hnotin]
  have hEu0 : EuSω (N := N) J Eu ω 0 = Eu := by
    simp [EuSω, EuS]
  have hlen : 0 < cd.lg.length := by
    rw [hlg, joinC_length]
    cases l with
    | nil => simp at hsum; omega
    | cons a l' => simp
  have hlgsum : cd.lg.sum = cd.Cd.card := by rw [hlg]; exact joinC_sum E hE cd.Cd l hsum
  set R := SR E cd.Cd 0 ∩ cd.Cd with hR
  have hdsum : (cd.lg.drop 0).sum = R.card := by
    rw [hlg, joinC_drop_sum E hE cd.Cd l hsum (Nat.zero_le _)]; rfl
  have hblk := blockSumEC_gen (D := D) (G := G) (A := A) (smax := smax) (cd := cd) hq hEu
    cd.lg 0 hlen R Finset.inter_subset_right hdsum Col
    (fun S g w hw w' hw' hagree => by
      obtain ⟨hw1, -, hw3⟩ := hw
      obtain ⟨hw1', -, hw3'⟩ := hw'
      refine SR_det E hE cd.Cd 0 hw1 hw1' fun y hy => ?_
      by_cases hyC : y ∈ cd.Cd
      · exact hagree y (Finset.mem_inter.mpr ⟨hy, hyC⟩)
      · rw [hw3 y hyC, hw3' y hyC])
    (fun S g w hw => by
      obtain ⟨hw1, hw2, -⟩ := hw
      obtain ⟨y, hy, hyw⟩ := SR_cover E cd.Cd 0 hw1 hw2
      exact ⟨y, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).2, (Finset.mem_inter.mp hy).1⟩,
        hyw⟩) ω hS3 0
  rw [← Finset.sum_filter] at hblk
  have hY0 : Ywt 0 = ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) 0) *
      ENNReal.ofReal (GRun A (cd.lg.drop 1) Eu / Eu ^ (cd.lg.drop 1).sum) := by
    simp only [hYwt, uW, hsupp0, Finset.sup_empty, Finset.prod_empty, ENNReal.ofReal_one,
      mul_one, PhiC, zero_add]
    rw [show (⊥ : ℕ) = 0 from rfl, hEu0]
  rw [hY0]
  rw [hEu0, List.drop_zero, hlgsum] at hblk
  -- the end step
  obtain ⟨j, rest, hjr⟩ : ∃ j rest, cd.lg = j :: rest := by
    cases h : cd.lg with
    | nil => rw [h] at hlen; simp at hlen
    | cons j rest => exact ⟨j, rest, rfl⟩
  have hdrop1 : cd.lg.drop 1 = rest := by rw [hjr]; rfl
  rw [hdrop1]
  set c := cd.Cd.card with hc
  set χ0 := chiB smax (fun u => ω ∈ G u) 0 with hχ0
  set GT := GRun A cd.lg Eu with hGT
  set GT1 := GRun A rest Eu with hGT1
  have hχ01 : 0 ≤ χ0 ∧ χ0 ≤ 1 := by
    simp only [hχ0, chiB]; split_ifs <;> norm_num
  obtain ⟨hG0, -⟩ := GRun_nonneg_antitone A rest
  obtain ⟨hG0', -⟩ := GRun_nonneg_antitone A cd.lg
  have hGT1n : 0 ≤ GT1 := hG0 _ hEu
  have hGT0 : 0 ≤ GT := hG0' _ hEu
  have hsum' : c = rest.sum + j := by
    have := hlgsum; rw [hjr, List.sum_cons] at this; omega
  have hend := end_step (K := c) (m := rest.sum) (j := j) hsum' hEu
    (S := GT / Eu ^ c) le_rfl hχ01.2 hGT1n
  have hfin : finG A cd.lg Eu = GT + Eu ^ j * GT1 := by rw [hGT, hGT1, hjr]; rfl
  have hcK : c ≤ K := by
    have := Finset.card_le_univ cd.Cd; simpa [Fintype.card_fin] using this
  have hS0 : 0 ≤ χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ c :=
    add_nonneg (mul_nonneg hχ01.1 (div_nonneg hGT1n (pow_nonneg hEu.le _)))
      (div_nonneg hGT0 (pow_nonneg hEu.le _))
  have hz0 : 0 ≤ z⁻¹ := inv_nonneg.mpr hz.le
  calc (ENNReal.ofReal χ0 * ENNReal.ofReal (GT1 / Eu ^ rest.sum) +
          ∑ Wc ∈ (Wset K N D).filter (BlockOKC (fun g : Fin N => ω ∈ J.A g) 0 Col), Ywt Wc) *
        (∑ d ∈ TS, Zt d) * W
      ≤ (ENNReal.ofReal χ0 * ENNReal.ofReal (GT1 / Eu ^ rest.sum) +
          ENNReal.ofReal (GT / Eu ^ c)) *
        ((ENNReal.ofReal Eu * ENNReal.ofReal δ) ^ c *
          (ENNReal.ofReal z⁻¹ * ENNReal.ofReal δ) ^ (K - c)) * W := by
        refine mul_le_mul_right' (mul_le_mul' (add_le_add le_rfl ?_) htails) _
        convert hblk using 2
    _ = ENNReal.ofReal ((χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ c) *
          ((Eu * δ) ^ c * (z⁻¹ * δ) ^ (K - c)) * cd.Wc) := by
        rw [← ENNReal.ofReal_mul hχ01.1, ← ENNReal.ofReal_add (mul_nonneg hχ01.1
          (div_nonneg hGT1n (pow_nonneg hEu.le _))) (div_nonneg hGT0 (pow_nonneg hEu.le _)),
          ← ENNReal.ofReal_mul hEu.le, ← ENNReal.ofReal_pow (mul_nonneg hEu.le hδ),
          ← ENNReal.ofReal_mul hz0, ← ENNReal.ofReal_pow (mul_nonneg hz0 hδ),
          ← ENNReal.ofReal_mul (pow_nonneg (mul_nonneg hEu.le hδ) _),
          ← ENNReal.ofReal_mul hS0, hW, ← ENNReal.ofReal_mul]
        exact mul_nonneg hS0 (mul_nonneg (pow_nonneg (mul_nonneg hEu.le hδ) _)
          (pow_nonneg (mul_nonneg hz0 hδ) _))
    _ ≤ ENNReal.ofReal (finG A cd.lg Eu * δ ^ K * z⁻¹ ^ (K - c) * cd.Wc) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hfin]
        have hle : (χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ c) * Eu ^ c ≤
            GT + Eu ^ j * GT1 := by
          have := hend; linarith
        have hδK : δ ^ K = δ ^ c * δ ^ (K - c) := by
          rw [← pow_add, Nat.add_sub_cancel' hcK]
        have hrest : 0 ≤ δ ^ K * z⁻¹ ^ (K - c) * cd.Wc :=
          mul_nonneg (mul_nonneg (pow_nonneg hδ _) (pow_nonneg hz0 _)) hWc
        calc (χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ c) *
              ((Eu * δ) ^ c * (z⁻¹ * δ) ^ (K - c)) * cd.Wc
            = ((χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ c) * Eu ^ c) *
                (δ ^ K * z⁻¹ ^ (K - c) * cd.Wc) := by
              rw [hδK, mul_pow, mul_pow]; ring
          _ ≤ (GT + Eu ^ j * GT1) * (δ ^ K * z⁻¹ ^ (K - c) * cd.Wc) :=
              mul_le_mul_of_nonneg_right hle hrest
          _ = _ := by ring

end FinalC

section ChainC

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {cd : CovD K} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

/-- **Prop 6.19 / Lemma A.5, the cover recursion over all `K` pivots** (any run structure):
`E[Z_0] ≤ θ^K Fin(A, l_C, Eu) δ^K z^{-(K-|C|)} W`, where `l_C = joinC E C l` is the join list
of the cover and `Z_0 = ZSC (K-1)` is the labelled sum over all pivots, contents and tails. -/
theorem multiRunC_chain [IsProbabilityMeasure P] (hJw : MeasurableSet Jw)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K) (hK : 1 ≤ K)
    (hlg : cd.lg = joinC E cd.Cd l)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hG : ∀ u u', u ≤ u' → G u' ⊆ G u)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    {a δ z : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) (hz : 0 < z)
    (hJz : Jw ⊆ Set.Ici z) (htail : tailSum Dmax X₀ ≤ Eu) (hWc : 0 ≤ cd.Wc) :
    ∫⁻ ω, ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (K - 1) ω ∂P ≤
      θE ^ K * ENNReal.ofReal (finG A cd.lg Eu * δ ^ K * z⁻¹ ^ (K - cd.Cd.card) * cd.Wc) := by
  set C := ENNReal.ofReal (finG A cd.lg Eu * δ ^ K * z⁻¹ ^ (K - cd.Cd.card) * cd.Wc) with hC
  set Z : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    if i < K then ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (K - 1 - i) ω else C with hZ
  set Φ : ℕ → ℕ → Ω × ℝ → ℝ≥0∞ := fun i n =>
    PhiMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (K - 1 - i) n with hΦ
  set Φbar : ℕ → Ω × ℝ → ℝ≥0∞ := fun i =>
    PhiBarMC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (K - 1 - i) with hΦbar
  have h := J.pil_chain K Z Φ (fun i n => PhiMC_jmeas hq hEu hGm hJw _ n) Φbar
    (fun i => PhiBarMC_meas hq hEu hGm hJw _) (fun i n x => PhiMC_le hq hEu hG _ n x)
    (fun i hi ω => by
      simp only [hZ, if_pos hi, hΦ]
      exact (ZSC_eq J E l cd Jw D Dmax X₀ smax G A Eu _ ω).le)
    (fun i hi ω => by
      simp only [hΦbar, hZ]
      by_cases hi1 : i + 1 < K
      · rw [if_pos hi1]
        obtain ⟨m, hm⟩ : ∃ m, K - 1 - i = m + 1 := ⟨K - 2 - i, by omega⟩
        have hm' : K - 1 - (i + 1) = m := by omega
        rw [hm, hm']
        by_cases hnl : runFirst l (m + 1) < m + 1
        · exact hnext_nonlastC hJw (by omega) hnl ω
        · exact hnext_lastC hJw hq hEu hE hpos hsum hlg (by omega)
            (le_antisymm (runFirst_le l _) (not_lt.mp hnl)) ω (hS3 ω)
      · rw [if_neg hi1]
        have h0 : K - 1 - i = 0 := by omega
        rw [h0]
        exact hnext_finalC hJw hq hEu hE hpos hsum hlg hK ω (hS3 ω) hJ hδ hz hJz htail hWc)
  have hZ0 : Z 0 = fun ω => ZSC (N := N) J E l cd Jw D Dmax X₀ smax G A Eu (K - 1) ω := by
    funext ω; simp [hZ, show 0 < K by omega]
  have hZK : Z K = fun _ => C := by funext ω; simp [hZ]
  rw [hZ0, hZK] at h
  simpa [lintegral_const, measure_univ] using h

end ChainC

end RankFull.Config
