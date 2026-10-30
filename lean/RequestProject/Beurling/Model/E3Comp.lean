module

public import RequestProject.Beurling.Model.TBoundE1
public import RequestProject.Beurling.Queue6.Noise3
public import RequestProject.Beurling.Queue6.Adapted6
public import RequestProject.Beurling.Model.CondBox

/-!
# The variance input of Lemma 5.22: `Comp(W) ≤ 50 log(2u) |W|` (`E3CompBound`)

For the prime decided at relative slot `k + 1` (value `q`), every composite `n = q m` of `W`
with latest prime `q`, `q ‖ n`, has a cofactor `m ≠ 1` all of whose primes are decided before
`q` (`cofP k`). So `X̃_q(W) ≤ #{m ∈ cofP k : m q ∈ W}`, a function of `q` and of the past
(`ℱ_k`). By (F2) (`law_dens`), `E[X̃_q(W) | ℱ_k] ≤ H⁻¹ ∫_{box} #{m : m t ∈ W} dt`; summing over
the slots and using (F1) (`law_slots`: the box weights at a point sum to `≤ 2`),
`Comp(W) ≤ 2 |W| ∑_{1 < m ≤ b/X₀⁻} 1/m`. The harmonic sum over the realised elements is bounded
by dyadic blocks with the sure count `N(w) ≤ 7w` at heights `w ≤ 8u/X₀`, which holds on the
queue constraints and the cluster events of time `< t(W)` (the lag bound `lag_local` and
`T ≤ 3x`, `tB_all_of_QE`). This is the paper's argument (Lemma 5.22, "The variance bound holds
on `Good(< t(W))`") with the cruder constants `ρ̃ ≤ 2` and `N(w) ≤ 7w`, which still give
`50 log(2u)`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed Queue6
  SlotModel
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The cofactors of the prime decided at relative slot `k + 1` -/

variable (θ X₀) in
/-- The cofactors available to the prime decided at relative slot `k + 1`: live, non-trivial
exponent vectors whose jittered primes are decided at earlier slots. -/
def cofP (k : ℕ) (ω : JitterΩ) : Set (PIdx X₀ →₀ ℕ) :=
  {e | Live (DD θ X₀ ω) e ∧ e ≠ 0 ∧ ∀ j, e (Sum.inr j) ≠ 0 → j < k}

open Classical in
variable (θ X₀) in
/-- `Φ_k(ω, t) = #{m ∈ cofP k : α ≤ m t < β}` for `t ≥ X₀⁻` (as an extended real; `0` below
`X₀⁻`, where no jittered prime lands). -/
noncomputable def PhiC (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' e : PIdx X₀ →₀ ℕ, if e ∈ cofP θ X₀ k p.1 ∧
    α ≤ eval (DD θ X₀ p.1) e * p.2 ∧ eval (DD θ X₀ p.1) e * p.2 < β then 1 else 0 else 0

section Meas

variable (hc : Cond θ X₀)
include hc

lemma pval_meas_lt {k : ℕ} (i : PIdx X₀) (hi : ∀ j, i = Sum.inr j → j < k) :
    Measurable[jitterFiltration k] fun ω => pval (DD θ X₀ ω) i := by
  cases i with
  | inl p => exact measurable_const
  | inr j =>
    have hjk : j + 1 ≤ k := hi j rfl
    exact (valF_adapted hc (stageMeas hc) j).mono (jitterFiltration.mono hjk) le_rfl

lemma eval_meas_lt {k : ℕ} (e : PIdx X₀ →₀ ℕ) (he : ∀ j, e (Sum.inr j) ≠ 0 → j < k) :
    Measurable[jitterFiltration k] fun ω => eval (DD θ X₀ ω) e := by
  unfold eval Finsupp.prod
  refine Finset.measurable_prod _ fun i hi =>
    ((continuous_pow (e i)).measurable).comp (pval_meas_lt hc i fun j hj => ?_)
  subst hj; exact he j (Finsupp.mem_support_iff.mp hi)

lemma cofP_meas (k : ℕ) (e : PIdx X₀ →₀ ℕ) :
    MeasurableSet[jitterFiltration k] {ω | e ∈ cofP θ X₀ k ω} := by
  classical
  by_cases he : ∀ j, e (Sum.inr j) ≠ 0 → j < k
  · have hS : {j | e (Sum.inr j) ≠ 0}.Finite := by
      refine (e.support.image fun i => match i with
        | Sum.inl _ => 0
        | Sum.inr k => k).finite_toSet.subset fun k hk => ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff]
      exact ⟨Sum.inr k, hk, rfl⟩
    have hlive : MeasurableSet[jitterFiltration k] {ω | Live (DD θ X₀ ω) e} := by
      have : {ω | Live (DD θ X₀ ω) e} = ⋂ j ∈ {j | e (Sum.inr j) ≠ 0}, placedF θ X₀ j := by
        ext ω; simp only [Live, mem_setOf_eq, mem_iInter]; rfl
      rw [this]
      exact hS.measurableSet_biInter fun j hj =>
        jitterFiltration.mono (show j ≤ k by have := he j hj; omega) _
          (placedF_adapted hc (stageMeas hc) j)
    have e1 : {ω | e ∈ cofP θ X₀ k ω} = {ω | Live (DD θ X₀ ω) e} ∩ {_ω | e ≠ 0} := by
      ext ω; simp only [cofP, mem_setOf_eq, mem_inter_iff]; tauto
    rw [e1]
    exact hlive.inter (MeasurableSet.const _)
  · have : {ω | e ∈ cofP θ X₀ k ω} = ∅ := by
      ext ω; simp only [cofP, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, -, h⟩; exact he h
    rw [this]; exact @MeasurableSet.empty _ (jitterFiltration k)

lemma PhiC_jmeas (k : ℕ) (α β : ℝ) (S : Set JitterΩ) (hS : MeasurableSet[jitterFiltration k] S) :
    RankFull.JMeas (jitterFiltration k) (fun p => S.indicator 1 p.1 * PhiC θ X₀ k α β p) := by
  classical
  unfold RankFull.JMeas
  letI mP : MeasurableSpace (JitterΩ × ℝ) :=
    @Prod.instMeasurableSpace JitterΩ ℝ (jitterFiltration k) _
  have hfst : @Measurable _ _ mP (jitterFiltration k) Prod.fst :=
    @measurable_fst _ _ (jitterFiltration k) _
  have hsnd : @Measurable _ _ mP _ Prod.snd := @measurable_snd _ _ (jitterFiltration k) _
  refine Measurable.mul (m := mP) ?_ ?_
  · exact (measurable_const.indicator hS).comp hfst
  · unfold PhiC
    refine Measurable.ite (m := mP) (measurableSet_le measurable_const hsnd) ?_ measurable_const
    refine Measurable.ennreal_tsum (mα := mP) fun e => ?_
    by_cases he : ∀ j, e (Sum.inr j) ≠ 0 → j < k
    · have hev : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ => eval (DD θ X₀ p.1) e * p.2 :=
        ((eval_meas_lt hc e he).comp hfst).mul hsnd
      have hset : @MeasurableSet _ mP {p : JitterΩ × ℝ | p.1 ∈ {ω | e ∈ cofP θ X₀ k ω} ∧
          α ≤ eval (DD θ X₀ p.1) e * p.2 ∧ eval (DD θ X₀ p.1) e * p.2 < β} :=
        (hfst (cofP_meas hc k e)).inter
          ((measurableSet_le measurable_const hev).inter (measurableSet_lt hev measurable_const))
      exact Measurable.ite (m := mP) hset measurable_const measurable_const
    · have : (fun p : JitterΩ × ℝ => if e ∈ cofP θ X₀ k p.1 ∧ α ≤ eval (DD θ X₀ p.1) e * p.2 ∧
          eval (DD θ X₀ p.1) e * p.2 < β then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
        funext p
        rw [if_neg]
        rintro ⟨⟨-, -, h⟩, -⟩; exact he h
      rw [this]; exact measurable_const

end Meas

/-! ### The domination `X̃_q(W) ≤ Φ_k(ω, q)` -/

open Classical in
lemma tsum_ite_eq_ncard {α : Type*} {S : Set α} (hS : S.Finite) :
    (∑' e : α, (if e ∈ S then (1 : ℝ≥0∞) else 0)) = (S.ncard : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := hS.toFinset) (fun a ha => by
    rw [Set.Finite.mem_toFinset] at ha; simp [ha])]
  rw [Finset.sum_congr rfl (fun a ha => by
    rw [Set.Finite.mem_toFinset] at ha; simp [ha] : ∀ a ∈ hS.toFinset,
      (if a ∈ S then (1 : ℝ≥0∞) else 0) = 1)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card _ hS]

lemma eval_add_single (D : PrimeData) (e : PIdx X₀ →₀ ℕ) (i : PIdx X₀) (a : ℕ) :
    eval D (e + Finsupp.single i a) = eval D e * pval D i ^ a := by
  unfold eval
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  congr 1
  exact Finsupp.prod_single_index (pow_zero _)

section Dom

variable (hc : Cond θ X₀)
include hc

lemma pval_gt_one {ω : JitterΩ} {e : PIdx X₀ →₀ ℕ} (he : Live (DD θ X₀ ω) e) :
    ∀ i ∈ e.support, 1 < pval (DD θ X₀ ω) i := by
  intro i hi
  cases i with
  | inl p =>
    show (1 : ℝ) < (p.1 : ℝ)
    exact_mod_cast p.2.1.one_lt
  | inr j =>
    show (1 : ℝ) < valF θ X₀ j ω
    have h1 := valF_ge_78 hc j ω
    have h2 := slotF_ge hc j ω
    have := two_pow_le_of_logX (Nat.cast_nonneg _) hc.hX (X₀ := (X₀ : ℝ))
    linarith

/-- **`X̃_q(W) ≤ Φ_k(ω, q)`** on the good stage: every composite counted by `X_q(W)` is
`q m` with a cofactor `m ∈ cofP k`. -/
theorem X3_le_PhiC (m : ℕ) (a b : ℤ) (k : ℕ) {ω : JitterΩ} (hω : ω ∈ stageGood θ X₀ k) :
    ENNReal.ofReal (X3 θ X₀ m a b k ω) ≤
      (lawA θ X₀ k).indicator (fun ω => PhiC θ X₀ k a b (ω, valF θ X₀ k ω)) ω := by
  classical
  set Xs := xsetP θ X₀ (a : ℝ) (b : ℝ) k (· = 1) ω with hXs
  have hX3 : X3 θ X₀ m a b k ω ≤ (Xs.ncard : ℝ) := by
    unfold X3
    refine (min_le_left _ _).trans (le_of_eq ?_)
    unfold Xcount xset
    exact_mod_cast ncard_xset (θ := θ) (X₀ := X₀) a b k (· = 1) ω
  have hval : valF θ X₀ k ω = (DD θ X₀ ω).v k := rfl
  have hq0 : 0 < valF θ X₀ k ω := valF_pos hc k ω
  set S : Set (PIdx X₀ →₀ ℕ) := {e' | e' ∈ cofP θ X₀ k ω ∧
    (a : ℝ) ≤ eval (DD θ X₀ ω) e' * valF θ X₀ k ω ∧ eval (DD θ X₀ ω) e' * valF θ X₀ k ω < b}
  have hSfin : S.Finite := by
    refine (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
      (b / valF θ X₀ k ω)).subset fun e' he' => ?_
    refine ⟨he'.1.1, pval_gt_one hc he'.1.1, ?_⟩
    rw [le_div_iff₀ hq0]; exact he'.2.2.le
  by_cases hne : Xs.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty] at hX3
    push_cast at hX3
    rw [ENNReal.ofReal_eq_zero.mpr hX3]; exact zero_le
  obtain ⟨e0, he0⟩ := hne
  have hplaced : placedAt (CM θ X₀ ω) k := by
    have h1 := he0.1 k (by rw [he0.2.2.2.2.2.2.2]; norm_num)
    exact h1
  have hA : ω ∈ lawA θ X₀ k := ⟨hplaced, hω⟩
  rw [indicator_of_mem hA]
  have hPhi : PhiC θ X₀ k a b (ω, valF θ X₀ k ω) = (S.ncard : ℝ≥0∞) := by
    unfold PhiC
    rw [if_pos (valF_ge_Xm hc k ω)]
    rw [← tsum_ite_eq_ncard hSfin]
    exact tsum_congr fun e => by
      by_cases h : e ∈ S
      · rw [if_pos h]; exact if_pos h
      · rw [if_neg h]; exact if_neg h
  rw [hPhi]
  -- the injection `e ↦ e - q`
  set f : (PIdx X₀ →₀ ℕ) → (PIdx X₀ →₀ ℕ) := fun e => e - Finsupp.single (Sum.inr k) 1
  have hsplit : ∀ e ∈ Xs, e = f e + Finsupp.single (Sum.inr k) 1 := by
    intro e he
    have hk : e (Sum.inr k) = 1 := he.2.2.2.2.2.2.2
    ext i
    simp only [f, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hi : i = Sum.inr k
    · subst hi; simp [hk]
    · simp [Finsupp.single_apply, Ne.symm hi]
  have hmaps : Set.MapsTo f Xs S := by
    intro e he
    have hk : e (Sum.inr k) = 1 := he.2.2.2.2.2.2.2
    have heq := hsplit e he
    have hev : eval (DD θ X₀ ω) e = eval (DD θ X₀ ω) (f e) * valF θ X₀ k ω := by
      conv_lhs => rw [heq]
      rw [eval_add_single, pow_one]; rfl
    refine ⟨⟨fun j hj => he.1 j ?_, ?_, fun j hj => ?_⟩, ?_, ?_⟩
    · intro h0; apply hj
      simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
    · intro h0
      have hs := he.2.1
      rw [heq, h0, zero_add, Finsupp.sum_single_index rfl] at hs
      omega
    · have hj' : e (Sum.inr j) ≠ 0 := by
        intro h0; apply hj
        simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
      have hle := latP_le hj'
      rw [he.2.2.2.2.2.2.1] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · subst h
        exfalso; apply hj
        simp [f, hk]
    · rw [← hev]; exact he.2.2.1
    · rw [← hev]; exact he.2.2.2.1
  have hinj : Set.InjOn f Xs := by
    intro e1 h1 e2 h2 h12
    rw [hsplit e1 h1, hsplit e2 h2, h12]
  have hcard := Set.ncard_le_ncard_of_injOn f hmaps hinj hSfin
  calc ENNReal.ofReal (X3 θ X₀ m a b k ω) ≤ ENNReal.ofReal (Xs.ncard : ℝ) :=
        ENNReal.ofReal_le_ofReal hX3
    _ = (Xs.ncard : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast]
    _ ≤ (S.ncard : ℝ≥0∞) := by exact_mod_cast hcard

end Dom

/-! ### The sure count `N(w) ≤ 7w` below the horizon -/

section Count

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc in
/-- `x^{λ(θ)} ≤ 10⁻⁴ x` for `x ≥ X₀`. -/
lemma rpow_lag_le {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : x ^ lagExponent θ ≤ x / 10000 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hx1 : 1 ≤ x := by linarith
  have hθ := hc.hθ
  have hl : lagExponent θ ≤ 1 / 4 := by
    unfold lagExponent
    have := min_le_left θ (1 / 2 - θ)
    have := min_le_right θ (1 / 2 - θ)
    linarith [hθ.1, hθ.2]
  have h1 : x ^ lagExponent θ ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hl
  have hxb : 10 ^ 8 ≤ x := by
    have h1 : Real.exp (10 ^ 8) ≤ x := by
      rw [← Real.exp_log (by linarith : 0 < x)]
      exact Real.exp_le_exp.mpr (hc.hX.trans (Real.log_le_log (by linarith) hx))
    have := Real.add_one_le_exp (10 ^ 8 : ℝ); linarith
  -- `x^{1/4} ≤ x/10⁴` iff `10⁴ ≤ x^{3/4}`
  have hx0 : 0 < x := by linarith
  have e : x = x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h34 : (10000 : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
    have : ((10 : ℝ) ^ 8) ^ (3 / 4 : ℝ) ≤ x ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hxb (by norm_num)
    have h6 : ((10 : ℝ) ^ 8) ^ (3 / 4 : ℝ) = 10 ^ (6 : ℝ) := by
      rw [show (10 : ℝ) ^ 8 = (10 : ℝ) ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h6] at this
    have : (10 : ℝ) ^ (6 : ℝ) = 1000000 := by norm_num
    linarith
  have hp : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have : x ^ (1 / 4 : ℝ) * 10000 ≤ x := by
    calc x ^ (1 / 4 : ℝ) * 10000 ≤ x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h34 hp
      _ = x := e.symm
  linarith

include hc hev in
/-- **The sure count at a height `v ≥ X₀`** below the horizon: `N(v) ≤ 3.0001 v`, from the lag
bound (queue at the slot of `v`) and `T(v) ≤ 3v`. -/
theorem NCount_le_high {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {v : ℝ}
    (hv : (X₀ : ℝ) ≤ v) (hvt : v + 26 * Real.log v + 2 < t) {n : ℕ}
    (hvn : v ≤ 2 ^ n * (X₀ : ℝ) / 2) (hnt : ttB X₀ n ≤ t) :
    NCount X₀ (DF θ X₀ ω) v ≤ 3.0001 * v := by
  obtain ⟨hU, hSG, hnt'⟩ := hN
  have hX := hc.hX
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  have hX1 := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hX
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt' ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have hlag := lag_local M hc.hθ.1 hc.hθ.2 hX (realisedSystem M (capH X₀) ω).N Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hv
    (queue_of_QE hc hQC h0 hv hvt)
  have hTB := tB_all_of_QE hc hev hQC hE1 ⟨hU, hSG, hnt'⟩ n hnt v hv hvn
  rw [Mcl_eq_lim hc h0] at hTB
  have hDF : DF θ X₀ ω = DM M ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [hDF, ← realisedSystem_N hok]
  have h4 := rpow_lag_le hc hv
  have := (abs_le.mp hlag).2
  linarith

include hc hev in
/-- **The sure count `N(w) ≤ 7w`** at every height `1 ≤ w` below the horizon. -/
theorem NCount_le_seven {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {w : ℝ} (hw1 : 1 ≤ w)
    (hwt : max w X₀ + 26 * Real.log (max w X₀) + 2 < t) {n : ℕ}
    (hwn : max w X₀ ≤ 2 ^ n * (X₀ : ℝ) / 2) (hnt : ttB X₀ n ≤ t) :
    NCount X₀ (DF θ X₀ ω) w ≤ 7 * w := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  rcases le_or_gt (X₀ : ℝ) w with hw | hw
  · have := NCount_le_high hc hev hQC hE1 hN hw (by rwa [max_eq_left hw] at hwt)
      (by rwa [max_eq_left hw] at hwn) hnt
    linarith
  · have hmX : max w (X₀ : ℝ) = X₀ := max_eq_right hw.le
    rw [hmX] at hwt hwn
    have hX := NCount_le_high hc hev hQC hE1 hN le_rfl hwt hwn hnt
    obtain ⟨hU, -, -⟩ := hN
    have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
    have hok := limModel_realisedOK h0
    have hDF : DF θ X₀ ω = DM h0.limModel ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
    rw [hDF, ← realisedSystem_N hok] at hX ⊢
    set P := realisedSystem h0.limModel (capH X₀) ω
    have h4H := four_capH_le hX0 hc.hX (le_refl (X₀ : ℝ))
    rcases lt_or_ge w ((X₀ : ℝ) - capH X₀ X₀ / 2) with hlow | hmid
    · rw [realised_floor_eq hok hU hc.hX h0.limModel_low hw1 hlow]
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ w)
      linarith
    · have hmono := P.N_mono hw.le
      linarith

include hc hev in
/-- `N(w) ≤ 7w`, with the horizon needed only at heights `w ≥ X₀⁻` (below `X₀⁻`, `N = ⌊·⌋`). -/
theorem NCount_le_seven' {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {w : ℝ} (hw1 : 1 ≤ w)
    (hhor : (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ w →
      max w X₀ + 26 * Real.log (max w X₀) + 2 < t ∧
        ∃ n, max w X₀ ≤ 2 ^ n * (X₀ : ℝ) / 2 ∧ ttB X₀ n ≤ t) :
    NCount X₀ (DF θ X₀ ω) w ≤ 7 * w := by
  rcases lt_or_ge w ((X₀ : ℝ) - capH X₀ X₀ / 2) with hlow | hmid
  · obtain ⟨hU, -, -⟩ := hN
    have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
    have hok := limModel_realisedOK h0
    have hDF : DF θ X₀ ω = DM h0.limModel ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
    rw [hDF, ← realisedSystem_N hok, realised_floor_eq hok hU hc.hX h0.limModel_low hw1 hlow]
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ w)
    linarith
  · obtain ⟨h1, n, h2, h3⟩ := hhor hmid
    exact NCount_le_seven hc hev hQC hE1 hN hw1 h1 h2 h3

end Count

/-! ### Dyadic harmonic sums -/

lemma inv_le_dyadic {x : ℝ} (hx : 1 < x) : ∀ J : ℕ, x ≤ 2 ^ J →
    1 / x ≤ ∑ j ∈ Finset.range J, (if x ≤ 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0) := by
  intro J
  induction J with
  | zero => intro h; norm_num at h; linarith
  | succ J ih =>
    intro hJ
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ (if x ≤ 2 ^ (J + 1) then (1 / 2 : ℝ) ^ J else 0) := by
      split_ifs <;> positivity
    by_cases h : x ≤ 2 ^ J
    · linarith [ih h]
    · push_neg at h
      rw [if_pos hJ]
      have hs : 0 ≤ ∑ j ∈ Finset.range J, (if x ≤ 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0) :=
        Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
      have : 1 / x ≤ (1 / 2 : ℝ) ^ J := by
        rw [one_div_pow, div_le_div_iff₀ (by linarith) (by positivity)]; linarith
      linarith

/-- **The dyadic harmonic bound**: if every value lies in `(1, 2^J]` and at most `c 2^{j+1}`
values are `≤ 2^{j+1}`, the harmonic sum is at most `2cJ`. -/
lemma harmonic_dyadic {ι : Type*} (F : Finset ι) (val : ι → ℝ) (hval : ∀ i ∈ F, 1 < val i)
    (J : ℕ) (hJ : ∀ i ∈ F, val i ≤ 2 ^ J) {c : ℝ}
    (hcnt : ∀ j < J, ((F.filter fun i => val i ≤ 2 ^ (j + 1)).card : ℝ) ≤ c * 2 ^ (j + 1)) :
    ∑ i ∈ F, 1 / val i ≤ 2 * c * J := by
  classical
  calc ∑ i ∈ F, 1 / val i
      ≤ ∑ i ∈ F, ∑ j ∈ Finset.range J,
          (if val i ≤ 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0) :=
        Finset.sum_le_sum fun i hi => inv_le_dyadic (hval i hi) J (hJ i hi)
    _ = ∑ j ∈ Finset.range J, ((F.filter fun i => val i ≤ 2 ^ (j + 1)).card : ℝ) *
          (1 / 2 : ℝ) ^ j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range J, c * 2 ^ (j + 1) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hcnt j (Finset.mem_range.mp hj)) (by positivity)
    _ = 2 * c * J := by
        rw [Finset.sum_congr rfl (fun j _ => show c * 2 ^ (j + 1) * (1 / 2 : ℝ) ^ j = 2 * c by
          rw [pow_succ, one_div_pow]; field_simp)]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### The pathwise majorant `Φ̄` -/

open Classical in
variable (θ X₀) in
/-- `Φ̄(ω, t) = #{m live, m ≠ 1 : α ≤ m t < β}` for `t ≥ X₀⁻`; it dominates every `Φ_k`. -/
noncomputable def PhiBar (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' e : PIdx X₀ →₀ ℕ, if (Live (DD θ X₀ p.1) e ∧ e ≠ 0) ∧
    α ≤ eval (DD θ X₀ p.1) e * p.2 ∧ eval (DD θ X₀ p.1) e * p.2 < β then 1 else 0 else 0

lemma PhiC_le_PhiBar (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) :
    PhiC θ X₀ k α β p ≤ PhiBar θ X₀ α β p := by
  classical
  unfold PhiC PhiBar
  split_ifs with h
  · refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases h1 : e ∈ cofP θ X₀ k p.1 ∧ α ≤ eval (DD θ X₀ p.1) e * p.2 ∧
        eval (DD θ X₀ p.1) e * p.2 < β
    · rw [if_pos h1, if_pos ⟨⟨h1.1.1, h1.1.2.1⟩, h1.2⟩]
    · rw [if_neg h1]; exact zero_le
  · exact le_rfl

lemma PhiBar_meas (α β : ℝ) (ω : JitterΩ) : Measurable fun t => PhiBar θ X₀ α β (ω, t) := by
  classical
  unfold PhiBar
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  refine Measurable.ennreal_tsum fun e => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) e * t := measurable_const.mul measurable_id
  exact ((MeasurableSet.const ((Live (DD θ X₀ ω) e ∧ e ≠ 0))).inter
    ((measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)) :)

section Bar

variable (hc : Cond θ X₀)
include hc

/-- The cofactors that can meet `[α, β)` from `[X₀⁻, ∞)`. -/
lemma cof_finite (β : ℝ) (ω : JitterΩ) :
    {e : PIdx X₀ →₀ ℕ | (Live (DD θ X₀ ω) e ∧ e ≠ 0) ∧ eval (DD θ X₀ ω) e ≤ β / Xm X₀}.Finite :=
  (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
    (β / Xm X₀)).subset fun e he => ⟨he.1.1, pval_gt_one hc he.1.1, he.2⟩

lemma eval_pos {ω : JitterΩ} {e : PIdx X₀ →₀ ℕ} (he : Live (DD θ X₀ ω) e) :
    0 < eval (DD θ X₀ ω) e := by
  unfold eval Finsupp.prod
  exact Finset.prod_pos fun i hi => pow_pos (lt_trans one_pos (pval_gt_one hc he i hi)) _

/-- **`∫ Φ̄(ω, t) dt ≤ (β - α) ∑_m 1/m`** over the live `m ≠ 1` with `m ≤ β/X₀⁻`. -/
theorem lintegral_PhiBar_le {α β : ℝ} (hαβ : α ≤ β) (ω : JitterΩ) :
    ∫⁻ t, PhiBar θ X₀ α β (ω, t) ≤ ENNReal.ofReal ((β - α) *
      ∑ e ∈ (cof_finite hc β ω).toFinset, 1 / eval (DD θ X₀ ω) e) := by
  classical
  have hXm := Queue6.Xm_pos hc
  set F := (cof_finite hc β ω).toFinset with hF
  have hpt : ∀ t, PhiBar θ X₀ α β (ω, t) ≤ ∑ e ∈ F,
      (Ico (α / eval (DD θ X₀ ω) e) (β / eval (DD θ X₀ ω) e)).indicator 1 t := by
    intro t
    unfold PhiBar
    split_ifs with ht
    swap; · exact zero_le
    rw [tsum_eq_sum (s := F) (fun e he => by
      rw [Set.Finite.mem_toFinset] at he
      refine if_neg fun h1 => he ⟨h1.1, ?_⟩
      have hev := eval_pos hc h1.1.1
      rw [le_div_iff₀ (by linarith)]
      have : eval (DD θ X₀ ω) e * Xm X₀ ≤ eval (DD θ X₀ ω) e * t :=
        mul_le_mul_of_nonneg_left ht hev.le
      linarith [h1.2.2])]
    refine Finset.sum_le_sum fun e he => ?_
    by_cases h1 : (Live (DD θ X₀ ω) e ∧ e ≠ 0) ∧ α ≤ eval (DD θ X₀ ω) e * t ∧
        eval (DD θ X₀ ω) e * t < β
    · rw [if_pos h1]
      have hev := eval_pos hc h1.1.1
      have hmem : t ∈ Ico (α / eval (DD θ X₀ ω) e) (β / eval (DD θ X₀ ω) e) := by
        constructor
        · rw [div_le_iff₀ hev]; linarith [h1.2.1]
        · rw [lt_div_iff₀ hev]; linarith [h1.2.2]
      rw [indicator_of_mem hmem]; rfl
    · rw [if_neg h1]; exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_finset_sum _ (fun e _ => measurable_one.indicator measurableSet_Ico)]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun e he => by
    rw [Set.Finite.mem_toFinset] at he
    have := eval_pos hc he.1.1
    have : 0 ≤ β - α := by linarith
    positivity)]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico]
  apply le_of_eq
  congr 1
  ring

lemma one_lt_eval {ω : JitterΩ} {e : PIdx X₀ →₀ ℕ} (he : Live (DD θ X₀ ω) e) (he0 : e ≠ 0) :
    1 < eval (DD θ X₀ ω) e := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
  have hi' : i ∈ e.support := Finsupp.mem_support_iff.mpr hi
  unfold eval Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ hi']
  have h1 : 1 < pval (DD θ X₀ ω) i ^ e i :=
    one_lt_pow₀ (pval_gt_one hc he i hi') hi
  have h2 : 1 ≤ ∏ x ∈ e.support.erase i, pval (DD θ X₀ ω) x ^ e x :=
    Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun x hx =>
        one_le_pow₀ (pval_gt_one hc he x (Finset.mem_of_mem_erase hx)).le
  nlinarith

lemma boxMean_PhiC_ne_top (hev : Even X₀) {a b : ℝ} (hab : a ≤ b) (k : ℕ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiC θ X₀ k a b) ω ≠ ∞ := by
  unfold boxMean
  by_cases hA : ω ∈ (constructionLaw hc hev).A k
  · rw [indicator_of_mem hA]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := (b - a) *
        ∑ e ∈ (cof_finite hc b ω).toFinset, 1 / eval (DD θ X₀ ω) e)) ?_)
    calc ∫⁻ t in RankFull.box _ _, PhiC θ X₀ k a b (ω, t)
        ≤ ∫⁻ t, PhiC θ X₀ k a b (ω, t) := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ t, PhiBar θ X₀ a b (ω, t) := lintegral_mono fun t => PhiC_le_PhiBar k a b _
      _ ≤ _ := lintegral_PhiBar_le hc hab ω
  · rw [indicator_of_notMem hA]; exact ENNReal.zero_ne_top

end Bar

/-! ### `E3CompBound` -/

section Main

variable (hc : Cond θ X₀)

include hc in
lemma Xm_half : (X₀ : ℝ) / 2 ≤ Xm X₀ := by
  have h4H := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX (le_refl (X₀ : ℝ))
  unfold Xm; linarith

include hc in
lemma log_le_lin {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 100 + 98 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
  linarith

include hc in
/-- **The horizon for the counts read by `Comp(W)`**: a height `w ≥ X₀⁻` with `w ≤ 8u/X₀` is
certified on `QC(< b) ∩ {E1 of time < b}` (`u ≤ a < b`). -/
lemma horizon_of {m : ℕ} {a b : ℤ} (hua : uS X₀ m ≤ a) (hab : a < b) {w : ℝ}
    (hwX : (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ w) (hwu : w ≤ 8 * uS X₀ m / X₀) :
    max w X₀ + 26 * Real.log (max w X₀) + 2 < b.toNat ∧
      ∃ n, max w X₀ ≤ 2 ^ n * (X₀ : ℝ) / 2 ∧ ttB X₀ n ≤ b.toNat := by
  set u := uS X₀ m with hu
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXX : (X₀ : ℝ) / 2 ≤ w := (Xm_half hc).trans hwX
  have hu2 : (X₀ : ℝ) ^ 2 / 16 ≤ u := by
    have h1 : (X₀ : ℝ) / 2 ≤ 8 * u / X₀ := hXX.trans hwu
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith
  have hmax : max w (X₀ : ℝ) ≤ u / 2 := by
    refine max_le ?_ ?_
    · have : 8 * u / X₀ ≤ u / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
      linarith
    · nlinarith
  have hmax0 : 0 < max w (X₀ : ℝ) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hb0 : (0 : ℤ) ≤ b := by
    have : (0 : ℝ) < b := by
      have : (u : ℝ) ≤ a := hua
      have : (a : ℝ) < b := by exact_mod_cast hab
      nlinarith
    exact_mod_cast this.le
  have hbt : ((b.toNat : ℕ) : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb0
  have hab1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hua' : u ≤ (a : ℝ) := hua
  refine ⟨?_, m, ?_, ?_⟩
  · have h1 := Real.log_le_log hmax0 hmax
    have h2 := log_le_lin hc (show 0 < u / 2 by nlinarith)
    rw [hbt]
    nlinarith
  · show max w (X₀ : ℝ) ≤ 2 ^ m * (X₀ : ℝ) / 2
    have : 2 ^ m * (X₀ : ℝ) = u := rfl
    linarith
  · unfold ttB
    have h1 : ((⌈2 ^ m * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) ≤ b := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ m * (X₀ : ℝ) / 2 by positivity)
      have : 2 ^ m * (X₀ : ℝ) = u := rfl
      nlinarith
    rw [← hbt] at h1
    exact_mod_cast h1

lemma two_pow_ceil_logb {y : ℝ} (hy0 : 0 < y) : y ≤ 2 ^ ⌈Real.logb 2 y⌉₊ := by
  rw [← Real.rpow_natCast]
  calc y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) hy0).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)

lemma two_pow_lt_of_lt_ceil {y : ℝ} (hy0 : 0 < y) {j : ℕ} (hj : j < ⌈Real.logb 2 y⌉₊) :
    (2 : ℝ) ^ (j + 1) < 2 * y := by
  have hpos : 0 < ⌈Real.logb 2 y⌉₊ := by omega
  have hl : 0 < Real.logb 2 y := by
    by_contra h; push_neg at h; rw [Nat.ceil_eq_zero.mpr h] at hpos; omega
  have h1 : ((j + 1 : ℕ) : ℝ) ≤ ⌈Real.logb 2 y⌉₊ := by exact_mod_cast hj
  have h2 : (⌈Real.logb 2 y⌉₊ : ℝ) < Real.logb 2 y + 1 := Nat.ceil_lt_add_one hl.le
  have h3 : (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) < 2 ^ (Real.logb 2 y + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num)
    (by norm_num) hy0, Real.rpow_one] at h3
  linarith

variable (hev : Even X₀)

include hc hev in
/-- **The cofactor harmonic sum** `∑_{1 < m ≤ b/X₀⁻} 1/m ≤ 14 ⌈log₂(b/X₀⁻)⌉`, on the queue
constraints and the cluster events of time `< b`. -/
theorem harm_le {m : ℕ} {a b : ℤ} (hua : uS X₀ m ≤ a) (hab : a < b) (hb2 : (b : ℝ) ≤ 2 * uS X₀ m)
    {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat)
    (hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) :
    ∑ e ∈ (cof_finite hc (b : ℝ) ω).toFinset, 1 / eval (DD θ X₀ ω) e ≤
      2 * 7 * ⌈Real.logb 2 ((b : ℝ) / Xm X₀)⌉₊ := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXm := Queue6.Xm_pos hc
  have hXmX := Xm_half hc
  have hXb : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  have hb0 : (0 : ℝ) < b := by
    have : (uS X₀ m : ℝ) ≤ a := hua
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  set y := (b : ℝ) / Xm X₀ with hy
  have hy0 : 0 < y := div_pos hb0 (by linarith)
  refine harmonic_dyadic _ (fun e => eval (DD θ X₀ ω) e) (fun e he => ?_) _
    (fun e he => ?_) (fun j hj => ?_)
  · rw [Set.Finite.mem_toFinset] at he
    exact one_lt_eval hc he.1.1 he.1.2
  · rw [Set.Finite.mem_toFinset] at he
    exact he.2.trans (two_pow_ceil_logb hy0)
  · set w : ℝ := 2 ^ (j + 1)
    have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
    have hwy := two_pow_lt_of_lt_ceil hy0 hj
    have hEf : (elemsLe X₀ (DF θ X₀ ω) w).Finite :=
      (finite_elems_gt (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω)) w).subset
        fun e he => ⟨he.1, pval_gt_one hc he.1, he.2⟩
    have hcard : (((cof_finite hc (b : ℝ) ω).toFinset.filter
        fun e => eval (DD θ X₀ ω) e ≤ w).card : ℝ) ≤ NCount X₀ (DF θ X₀ ω) w := by
      unfold NCount
      have : (((cof_finite hc (b : ℝ) ω).toFinset.filter
          fun e => eval (DD θ X₀ ω) e ≤ w) : Set (PIdx X₀ →₀ ℕ)) ⊆ elemsLe X₀ (DF θ X₀ ω) w := by
        intro e he
        rw [Finset.coe_filter, mem_setOf_eq, Set.Finite.mem_toFinset] at he
        exact ⟨he.1.1.1, he.2⟩
      have h := Set.ncard_le_ncard this hEf
      rw [Set.ncard_coe_finset] at h
      exact_mod_cast h
    refine hcard.trans (NCount_le_seven' hc hev hQC hE1 hN hw1 fun hwX => ?_)
    refine horizon_of hc hua hab hwX ?_
    have : y ≤ 2 * uS X₀ m / Xm X₀ := div_le_div_of_nonneg_right hb2 (by linarith)
    have : 2 * uS X₀ m / Xm X₀ ≤ 4 * uS X₀ m / X₀ := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have : 4 * uS X₀ m / X₀ = (8 * uS X₀ m / X₀) / 2 := by ring
    linarith

include hc hev in
/-- **The variance input of Lemma 5.22** (`Queue6.E3CompBound`, "The variance bound holds on
`Good(< t(W))`": `Comp(W) ≤ 50 log(2u) |W|`), on the queue constraints and the cluster events of
time `< t(W)`. -/
theorem e3CompBound : E3CompBound θ X₀ := by
  classical
  intro m a b hW
  obtain ⟨hua, hab, hb2, -⟩ := hW
  set J := constructionLaw hc hev with hJ
  obtain ⟨huX, hlu, hHu, hM1⟩ := uS_facts hc m
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set C := 2 * capM1 X₀ (uS X₀ m) with hC
  have hC0 : 0 ≤ C := by linarith
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hk : ∀ k, jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k] ≤ᵐ[jitterMeasure]
      fun ω => min C (boxMean J k (PhiC θ X₀ k a b) ω).toReal := by
    intro k
    have hX30 : ∀ ω, 0 ≤ X3 θ X₀ m a b k ω := fun ω => le_min (Nat.cast_nonneg _) hC0
    have hX3C : ∀ ω, X3 θ X₀ m a b k ω ≤ C := fun ω => min_le_right _ _
    have hX3m : Measurable (X3 θ X₀ m a b k) :=
      (((xcount_adapted hc a b k 1).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    have hfΦ : ∀ᵐ ω ∂jitterMeasure, ENNReal.ofReal (X3 θ X₀ m a b k ω) ≤
        (J.A k).indicator (fun ω => PhiC θ X₀ k a b (ω, J.q k ω)) ω := by
      filter_upwards [ae_stageGood hc] with ω hω
      exact X3_le_PhiC hc m a b k (hω k)
    exact condExp_le_boxMean J k hC0 hX30 hX3C hX3m
      (fun S hS => PhiC_jmeas hc k a b S hS) hfΦ
      (fun ω => boxMean_PhiC_ne_top hc hev hab' k ω)
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  filter_upwards [ae_all_iff.mpr hk, hnice] with ω hω hN hG n
  obtain ⟨hQC, hE1⟩ := hG
  set Hs := ∑ e ∈ (cof_finite hc (b : ℝ) ω).toFinset, 1 / eval (DD θ X₀ ω) e with hHs
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun e he => by
    rw [Set.Finite.mem_toFinset] at he
    have := eval_pos hc he.1.1; positivity
  have hfin : ∀ k, boxMean J k (PhiC θ X₀ k a b) ω ≠ ∞ := fun k =>
    boxMean_PhiC_ne_top hc hev hab' k ω
  have hsum : ∑' k, boxMean J k (PhiC θ X₀ k a b) ω ≤ 2 * ENNReal.ofReal ((b - a) * Hs) :=
    (sum_boxMean_le J (fun k => PhiC θ X₀ k a b) (PhiBar θ X₀ a b) ω (PhiBar_meas a b ω)
      (fun k t => PhiC_le_PhiBar k a b _)).trans
      (mul_le_mul_right (lintegral_PhiBar_le hc hab' ω) 2)
  have hrhs : 0 ≤ 2 * ((b - a) * Hs) := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  have hcomp : ∑ k ∈ Finset.range n, (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω ≤
      2 * ((b - a) * Hs) := by
    refine (Finset.sum_le_sum fun k _ => (hω k).trans (min_le_right _ _)).trans ?_
    rw [← ENNReal.toReal_sum fun k _ => hfin k]
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((b - a) * Hs) =
        ENNReal.ofReal (2 * ((b - a) * Hs)) := by
      rw [ENNReal.ofReal_mul (p := 2) (by norm_num)]; norm_num
    calc (∑ k ∈ Finset.range n, boxMean J k (PhiC θ X₀ k a b) ω).toReal
        ≤ (ENNReal.ofReal (2 * ((b - a) * Hs))).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [← h2]
          exact (ENNReal.sum_le_tsum _).trans hsum
      _ = 2 * ((b - a) * Hs) := ENNReal.toReal_ofReal hrhs
  have hH := harm_le hc hev hua hab hb2 hQC hE1 hN
  rw [← hHs] at hH
  -- numerics: `28 ⌈log₂(b/X₀⁻)⌉ ≤ 50 log(2u)`
  set J' := ⌈Real.logb 2 ((b : ℝ) / Xm X₀)⌉₊ with hJ'
  have hXm := Queue6.Xm_pos hc
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hb0 : (0 : ℝ) < b := by
    have : (uS X₀ m : ℝ) ≤ a := hua
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have hJ'le : (J' : ℝ) ≤ Real.log (2 * uS X₀ m) / Real.log 2 + 1 := by
    by_cases hJ0 : J' = 0
    · rw [hJ0]; push_cast
      have : 0 ≤ Real.log (2 * uS X₀ m) / Real.log 2 :=
        div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
      linarith
    · have hl : 0 < Real.logb 2 ((b : ℝ) / Xm X₀) := by
        by_contra h; push_neg at h; exact hJ0 (Nat.ceil_eq_zero.mpr h)
      have h1 : (J' : ℝ) < Real.logb 2 ((b : ℝ) / Xm X₀) + 1 := Nat.ceil_lt_add_one hl.le
      have h2 : Real.logb 2 ((b : ℝ) / Xm X₀) ≤ Real.log (2 * uS X₀ m) / Real.log 2 := by
        unfold Real.logb
        refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by norm_num))
        refine Real.log_le_log (div_pos hb0 (by linarith)) ?_
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
  have hl2 : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : 10 ^ 8 ≤ Real.log (2 * uS X₀ m) :=
    hlu.trans (Real.log_le_log (by linarith) (by linarith))
  have hJ'2 : (J' : ℝ) ≤ Real.log (2 * uS X₀ m) / 0.69 + 1 := by
    refine hJ'le.trans (by
      have := div_le_div_of_nonneg_left (show 0 ≤ Real.log (2 * uS X₀ m) by linarith)
        (by norm_num) hl2
      linarith)
  have hba : ((b - a : ℤ) : ℝ) = (b : ℝ) - a := by push_cast; ring
  rw [hba]
  have hW0 : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hfin' : 2 * 7 * (J' : ℝ) * 2 ≤ 50 * Real.log (2 * uS X₀ m) := by
    have : Real.log (2 * uS X₀ m) / 0.69 = Real.log (2 * uS X₀ m) * (100 / 69) := by ring
    nlinarith
  calc _ ≤ 2 * (((b : ℝ) - a) * Hs) := hcomp
    _ ≤ 2 * (((b : ℝ) - a) * (2 * 7 * J')) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hW0) (by norm_num)
    _ = (2 * 7 * (J' : ℝ) * 2) * ((b : ℝ) - a) := by ring
    _ ≤ 50 * Real.log (2 * uS X₀ m) * ((b : ℝ) - a) := mul_le_mul_of_nonneg_right hfin' hW0

end Main

end BModel
