module

public import RequestProject.Beurling.Model.E3Comp
public import RequestProject.Beurling.Queue6.S2E2

/-!
# Eq. (s2) of Lemma 5.22: `Comp⁽²⁾(I) ≤ s₂ |I|`, for every window

For the prime decided at relative slot `k + 1` (value `q`), every composite `n` of `W` with
latest prime `q` and `q^c ‖ n`, `c ≥ 2`, is `n = q^c m` with a cofactor `m` (possibly `1`) all of
whose primes are decided before `q` (`cofP2 k`). So `min(X⁽²⁾_q(W), C) ≤ #{(m, c) : c ≥ 2,
m ∈ cofP2 k, m q^c ∈ W}`, a function of `q` and the past. By (F2) and (F1) (`law_dens`,
`law_slots`, `ρ̃ ≤ 2`), the compensator is at most
`2 |W| ∑_{c ≥ 2} ∑_m 1/(c m X₀⁻^{c-1})` (`vol{t ≥ X₀⁻ : m t^c ∈ W} ≤ |W|/(c m X₀⁻^{c-1})`,
`volume_pow_window_le`). With `∑_{c ≥ 2} X₀⁻^{-(c-1)}/c ≤ (1/2 + 2/X₀⁻)/X₀⁻` and the sure count
`N(w) ≤ 3.0001 w` below the horizon (`NCount_le_three`) in the dyadic harmonic bound, this is the
paper's **first bound** (04d-noise.tex, "First bound": `Comp⁽²⁾(I)/|I| ≤ 0.73 L_u/X₀⁻`, here
`≤ 9 L_u/X₀⁻`), which is (s2) when `½√(L_u log L_u) ≤ log X₀⁻`.

The **second bound** (04d-noise.tex, "Second bound, for `σ > log X₀⁻`"), which uses the
Dickman-quality smooth-element bound (Lemma smooth-v, 04a-setup.tex, under (H_BS)), is the named
hypothesis `S2SecondBranch`.

* `S2Core` : (s2) for every window `[a, b)` with `v/4 ≤ a < b ≤ 2v`, `v ≥ X₀`, for the truncated
  counts `min(X⁽²⁾_q, C)`, on the queue constraints and the cluster events of time `< b`;
* `s2Core_of` : `S2Core` from `S2SecondBranch`;
* `e3S2Bound_of` : the field `E3S2Bound` (windows of `𝒲'_u`, `X̃⁽²⁾ = min(X⁽²⁾, b₂)`);
* `e2S2Bound_of` : the field `E2S2Bound` (windows of `𝓘_u`, `1[X⁽²⁾ ≥ 1] ≤ min(X⁽²⁾, 1)`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed Queue6
  SlotModel
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The volume of `{t ≥ X : α ≤ m t^c < β}` -/

lemma pow_sub_pow_ge {X s t : ℝ} (hX : 0 ≤ X) (hs : X ≤ s) (hst : s ≤ t) (c : ℕ) :
    (c : ℝ) * X ^ (c - 1) * (t - s) ≤ t ^ c - s ^ c := by
  have h := (Commute.all t s).geom_sum₂_mul c
  rw [← h]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have : ∀ i ∈ Finset.range c, X ^ (c - 1) ≤ t ^ i * s ^ (c - 1 - i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e : X ^ (c - 1) = X ^ i * X ^ (c - 1 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ hX (hs.trans hst) _) (pow_le_pow_left₀ hX hs _)
      (pow_nonneg hX _) (pow_nonneg (hX.trans (hs.trans hst)) _)
  calc (c : ℝ) * X ^ (c - 1) = ∑ i ∈ Finset.range c, X ^ (c - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum this

/-- **`vol{t ≥ X : α ≤ m t^c < β} ≤ (β - α)/(c m X^{c-1})`** for `m, X > 0`, `c ≥ 1`. -/
lemma volume_pow_window_le {X m α β : ℝ} (hX : 0 < X) (hm : 0 < m) {c : ℕ} (hc : 1 ≤ c)
    (hαβ : α ≤ β) :
    volume {t : ℝ | X ≤ t ∧ α ≤ m * t ^ c ∧ m * t ^ c < β} ≤
      ENNReal.ofReal ((β - α) / (c * m * X ^ (c - 1))) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun x hx y hy => ?_)
  have hD : 0 < (c : ℝ) * m * X ^ (c - 1) := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    positivity
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `|x - y| ≤ (β - α)/(c m X^{c-1})`
  have key : ∀ s t : ℝ, s ∈ {t : ℝ | X ≤ t ∧ α ≤ m * t ^ c ∧ m * t ^ c < β} →
      t ∈ {t : ℝ | X ≤ t ∧ α ≤ m * t ^ c ∧ m * t ^ c < β} → s ≤ t →
      t - s ≤ (β - α) / (c * m * X ^ (c - 1)) := by
    intro s t hs ht hst
    rw [le_div_iff₀ hD]
    have h := pow_sub_pow_ge hX.le hs.1 hst c
    have : m * ((c : ℝ) * X ^ (c - 1) * (t - s)) ≤ m * (t ^ c - s ^ c) :=
      mul_le_mul_of_nonneg_left h hm.le
    nlinarith [hs.2.1, ht.2.2]
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact key x y hx hy h
  · rw [abs_of_nonneg (by linarith)]; exact key y x hy hx h

/-- `∑_{j < K} r^{j+1}/(j+2) ≤ r/2 + 2r²` for `0 ≤ r ≤ 1/2`. -/
lemma sum_pow_div_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (K : ℕ) :
    ∑ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) ≤ r / 2 + 2 * r ^ 2 := by
  have hterm : ∀ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) ≤
      (if j = 0 then r / 2 else 0) + r ^ 2 * r ^ (j - 1) * (if j = 0 then 0 else 1) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [if_neg hj.ne', if_neg hj.ne', zero_add, mul_one]
      have e : r ^ (j + 1) = r ^ 2 * r ^ (j - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      have : (0 : ℝ) ≤ r ^ 2 * r ^ (j - 1) := by positivity
      have h2 : (1 : ℝ) ≤ (j : ℝ) + 2 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      exact div_le_self this h2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range K, (if j = 0 then r / 2 else 0) ≤ r / 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> linarith
  have h2 : ∑ j ∈ Finset.range K, r ^ 2 * r ^ (j - 1) * (if j = 0 then (0 : ℝ) else 1) ≤
      2 * r ^ 2 := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp; positivity
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, mul_one, Nat.add_sub_cancel, if_true, mul_zero,
      add_zero]
    rw [← Finset.mul_sum]
    have hg := RankFull.geom_partial_le hr0 (by linarith : r < 1) K'
    have : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hr2 : 0 ≤ r ^ 2 := by positivity
    nlinarith
  linarith

/-! ### The cofactors of `q^c`, `c ≥ 2` -/

variable (θ X₀) in
/-- The cofactors available to the power `q^c` of the prime decided at relative slot `k + 1`:
live exponent vectors (possibly `0`) whose jittered primes are decided at earlier slots. -/
def cofP2 (k : ℕ) (ω : JitterΩ) : Set (PIdx X₀ →₀ ℕ) :=
  {e | Live (DD θ X₀ ω) e ∧ ∀ j, e (Sum.inr j) ≠ 0 → j < k}

open Classical in
variable (θ X₀) in
/-- `Φ⁽²⁾_k(ω, t) = #{(m, c) : c ≥ 2, m ∈ cofP2 k, α ≤ m t^c < β}` for `t ≥ X₀⁻`. -/
noncomputable def PhiC2 (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' ec : (PIdx X₀ →₀ ℕ) × ℕ, if 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧
    α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    then 1 else 0 else 0

open Classical in
variable (θ X₀) in
/-- The pathwise majorant: as `PhiC2`, over all live cofactors. -/
noncomputable def PhiBar2 (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' ec : (PIdx X₀ →₀ ℕ) × ℕ, if 2 ≤ ec.2 ∧ Live (DD θ X₀ p.1) ec.1 ∧
    α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    then 1 else 0 else 0

lemma PhiC2_le_PhiBar2 (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) :
    PhiC2 θ X₀ k α β p ≤ PhiBar2 θ X₀ α β p := by
  classical
  unfold PhiC2 PhiBar2
  split_ifs with h
  · refine ENNReal.tsum_le_tsum fun ec => ?_
    by_cases h1 : 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧
        α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1.1, h1.2.2⟩]
    · rw [if_neg h1]; exact zero_le
  · exact le_rfl

lemma PhiBar2_meas (α β : ℝ) (ω : JitterΩ) : Measurable fun t => PhiBar2 θ X₀ α β (ω, t) := by
  classical
  unfold PhiBar2
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  refine Measurable.ennreal_tsum fun ec => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) ec.1 * t ^ ec.2 :=
    measurable_const.mul (measurable_id.pow_const _)
  exact ((MeasurableSet.const (2 ≤ ec.2)).inter ((MeasurableSet.const
    (Live (DD θ X₀ ω) ec.1)).inter ((measurableSet_le measurable_const hm).inter
      (measurableSet_lt hm measurable_const))) :)

section Meas2

variable (hc : Cond θ X₀)
include hc

lemma cofP2_meas (k : ℕ) (e : PIdx X₀ →₀ ℕ) :
    MeasurableSet[jitterFiltration k] {ω | e ∈ cofP2 θ X₀ k ω} := by
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
    have e1 : {ω | e ∈ cofP2 θ X₀ k ω} = {ω | Live (DD θ X₀ ω) e} := by
      ext ω; simp only [cofP2, mem_setOf_eq]; tauto
    rw [e1]; exact hlive
  · have : {ω | e ∈ cofP2 θ X₀ k ω} = ∅ := by
      ext ω; simp only [cofP2, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, h⟩; exact he h
    rw [this]; exact @MeasurableSet.empty _ (jitterFiltration k)

lemma PhiC2_jmeas (k : ℕ) (α β : ℝ) (S : Set JitterΩ)
    (hS : MeasurableSet[jitterFiltration k] S) :
    RankFull.JMeas (jitterFiltration k) (fun p => S.indicator 1 p.1 * PhiC2 θ X₀ k α β p) := by
  classical
  unfold RankFull.JMeas
  letI mP : MeasurableSpace (JitterΩ × ℝ) :=
    @Prod.instMeasurableSpace JitterΩ ℝ (jitterFiltration k) _
  have hfst : @Measurable _ _ mP (jitterFiltration k) Prod.fst :=
    @measurable_fst _ _ (jitterFiltration k) _
  have hsnd : @Measurable _ _ mP _ Prod.snd := @measurable_snd _ _ (jitterFiltration k) _
  refine Measurable.mul (m := mP) ?_ ?_
  · exact (measurable_const.indicator hS).comp hfst
  · unfold PhiC2
    refine Measurable.ite (m := mP) (measurableSet_le measurable_const hsnd) ?_ measurable_const
    refine Measurable.ennreal_tsum (mα := mP) fun ec => ?_
    by_cases he : ∀ j, ec.1 (Sum.inr j) ≠ 0 → j < k
    · have hev : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ =>
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 :=
        ((eval_meas_lt hc ec.1 he).comp hfst).mul (hsnd.pow_const _)
      have hset : @MeasurableSet _ mP {p : JitterΩ × ℝ | 2 ≤ ec.2 ∧
          p.1 ∈ {ω | ec.1 ∈ cofP2 θ X₀ k ω} ∧
          α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β} :=
        (MeasurableSet.const _).inter ((hfst (cofP2_meas hc k ec.1)).inter
          ((measurableSet_le measurable_const hev).inter (measurableSet_lt hev measurable_const)))
      exact Measurable.ite (m := mP) hset measurable_const measurable_const
    · have : (fun p : JitterΩ × ℝ => if 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧
          α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
        funext p
        rw [if_neg]
        rintro ⟨-, ⟨-, h⟩, -⟩; exact he h
      rw [this]; exact measurable_const

end Meas2

section Dom2

variable (hc : Cond θ X₀)
include hc

lemma one_le_evalD {ω : JitterΩ} {e : PIdx X₀ →₀ ℕ} (he : Live (DD θ X₀ ω) e) :
    1 ≤ eval (DD θ X₀ ω) e := by
  by_cases h0 : e = 0
  · subst h0; simp [eval]
  · exact (one_lt_eval hc he h0).le

/-- **`min(X⁽²⁾_q(W), C) ≤ Φ⁽²⁾_k(ω, q)`** on the good stage: every composite counted by
`X⁽²⁾_q(W)` is `q^c m` with `c ≥ 2` and a cofactor `m ∈ cofP2 k`. -/
theorem X2_le_PhiC2 (a b : ℝ) (C : ℝ) (k : ℕ) {ω : JitterΩ} (hω : ω ∈ stageGood θ X₀ k) :
    ENNReal.ofReal (min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C) ≤
      (lawA θ X₀ k).indicator (fun ω => PhiC2 θ X₀ k a b (ω, valF θ X₀ k ω)) ω := by
  classical
  set Xs := xsetP θ X₀ a b k (2 ≤ ·) ω with hXs
  have hX2 : min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C ≤ (Xs.ncard : ℝ) := by
    refine (min_le_left _ _).trans (le_of_eq ?_)
    unfold X2count x2set
    exact_mod_cast ncard_xset (θ := θ) (X₀ := X₀) a b k (2 ≤ ·) ω
  set q := valF θ X₀ k ω with hq
  have hq0 : 0 < q := valF_pos hc k ω
  have hqXm : Xm X₀ ≤ q := valF_ge_Xm hc k ω
  have hXm := Queue6.Xm_pos hc
  have hq1 : 1 < q := by linarith
  set S : Set ((PIdx X₀ →₀ ℕ) × ℕ) := {ec | 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k ω ∧
    a ≤ eval (DD θ X₀ ω) ec.1 * q ^ ec.2 ∧ eval (DD θ X₀ ω) ec.1 * q ^ ec.2 < b}
  have hSfin : S.Finite := by
    have hF1 := finite_elems_gt (X₀ := X₀)
      (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω)) (b / q ^ 2)
    refine (hF1.prod (Set.finite_Iio ⌈b⌉₊)).subset fun ec hec => ?_
    obtain ⟨hc2, ⟨hlive, -⟩, -, hlt⟩ := hec
    have hev1 := one_le_evalD hc hlive
    have hqc : q ^ 2 ≤ q ^ ec.2 := pow_le_pow_right₀ hq1.le hc2
    have hq2 : 0 < q ^ 2 := by positivity
    refine ⟨⟨hlive, pval_gt_one hc hlive, ?_⟩, ?_⟩
    · show eval (DD θ X₀ ω) ec.1 ≤ b / q ^ 2
      rw [le_div_iff₀ hq2]
      have : eval (DD θ X₀ ω) ec.1 * q ^ 2 ≤ eval (DD θ X₀ ω) ec.1 * q ^ ec.2 :=
        mul_le_mul_of_nonneg_left hqc (by linarith)
      linarith
    · -- `c ≤ q^c < b`
      show ec.2 < ⌈b⌉₊
      have h1 : (ec.2 : ℝ) < q ^ ec.2 := by
        have := Nat.lt_pow_self (show 1 < 2 by norm_num) (n := ec.2)
        have h2 : ((2 : ℕ) : ℝ) ^ ec.2 ≤ q ^ ec.2 := pow_le_pow_left₀ (by norm_num)
          (by
            have h1 := Xm_half hc
            have h2 := X₀_ge_two_pow hc.hX
            have h3 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
            push_cast; linarith) _
        have : ((ec.2 : ℕ) : ℝ) < ((2 ^ ec.2 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this h2; linarith
      have h2 : q ^ ec.2 ≤ eval (DD θ X₀ ω) ec.1 * q ^ ec.2 := by
        have : 0 ≤ q ^ ec.2 := by positivity
        nlinarith
      have h3 : (ec.2 : ℝ) < b := by linarith
      exact_mod_cast lt_of_lt_of_le h3 (Nat.le_ceil b)
  by_cases hne : Xs.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty] at hX2
    push_cast at hX2
    rw [ENNReal.ofReal_eq_zero.mpr hX2]; exact zero_le
  obtain ⟨e0, he0⟩ := hne
  have hplaced : placedAt (CM θ X₀ ω) k := by
    have hk2 : 2 ≤ e0 (Sum.inr k) := he0.2.2.2.2.2.2.2
    exact he0.1 k (by omega)
  have hA : ω ∈ lawA θ X₀ k := ⟨hplaced, hω⟩
  rw [indicator_of_mem hA]
  have hPhi : PhiC2 θ X₀ k a b (ω, q) = (S.ncard : ℝ≥0∞) := by
    unfold PhiC2
    rw [if_pos hqXm]
    rw [← tsum_ite_eq_ncard hSfin]
    exact tsum_congr fun ec => by
      by_cases h : ec ∈ S
      · rw [if_pos h]; exact if_pos h
      · rw [if_neg h]; exact if_neg h
  rw [hPhi]
  set f : (PIdx X₀ →₀ ℕ) → (PIdx X₀ →₀ ℕ) × ℕ := fun e =>
    (e - Finsupp.single (Sum.inr k) (e (Sum.inr k)), e (Sum.inr k))
  have hsplit : ∀ e : PIdx X₀ →₀ ℕ,
      e = (f e).1 + Finsupp.single (Sum.inr k) (e (Sum.inr k)) := by
    intro e
    ext i
    simp only [f, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hi : i = Sum.inr k
    · subst hi; simp
    · simp [Finsupp.single_apply, Ne.symm hi]
  have hmaps : Set.MapsTo f Xs S := by
    intro e he
    have hk2 : 2 ≤ e (Sum.inr k) := he.2.2.2.2.2.2.2
    have hev : eval (DD θ X₀ ω) e = eval (DD θ X₀ ω) (f e).1 * q ^ (f e).2 := by
      conv_lhs => rw [hsplit e]
      rw [eval_add_single]; rfl
    refine ⟨hk2, ⟨fun j hj => he.1 j ?_, fun j hj => ?_⟩, ?_, ?_⟩
    · intro h0; apply hj
      simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
    · have hj' : e (Sum.inr j) ≠ 0 := by
        intro h0; apply hj
        simp only [f, Finsupp.coe_tsub, Pi.sub_apply, h0, zero_tsub]
      have hle := latP_le hj'
      rw [he.2.2.2.2.2.2.1] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · subst h
        exfalso; apply hj
        simp [f]
    · rw [← hev]; exact he.2.2.1
    · rw [← hev]; exact he.2.2.2.1
  have hinj : Set.InjOn f Xs := by
    intro e1 _ e2 _ h12
    rw [hsplit e1, hsplit e2]
    have h1 : (f e1).1 = (f e2).1 := congrArg Prod.fst h12
    have h2 : e1 (Sum.inr k) = e2 (Sum.inr k) := congrArg Prod.snd h12
    rw [h1, h2]
  have hcard := Set.ncard_le_ncard_of_injOn f hmaps hinj hSfin
  calc ENNReal.ofReal (min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C)
      ≤ ENNReal.ofReal (Xs.ncard : ℝ) := ENNReal.ofReal_le_ofReal hX2
    _ = (Xs.ncard : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast]
    _ ≤ (S.ncard : ℝ≥0∞) := by exact_mod_cast hcard

end Dom2

section Bar2

variable (hc : Cond θ X₀)
include hc

/-- The cofactors of value `≤ β/X₀⁻²` (including `1`). -/
lemma cof2_finite (β : ℝ) (ω : JitterΩ) :
    {e : PIdx X₀ →₀ ℕ | Live (DD θ X₀ ω) e ∧ eval (DD θ X₀ ω) e ≤ β / Xm X₀ ^ 2}.Finite :=
  (finite_elems_gt (X₀ := X₀) (locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) (CM θ X₀ ω))
    (β / Xm X₀ ^ 2)).subset fun e he => ⟨he.1, pval_gt_one hc he.1, he.2⟩

/-- **`∫ Φ̄⁽²⁾(ω, t) dt ≤ (β - α) ∑_m ∑_{c ≥ 2} 1/(c m X₀⁻^{c-1})`**, `m ≤ β/X₀⁻²`. -/
theorem lintegral_PhiBar2_le {α β : ℝ} (hαβ : α ≤ β) (ω : JitterΩ) :
    ∫⁻ t, PhiBar2 θ X₀ α β (ω, t) ≤ ENNReal.ofReal ((β - α) *
      ∑ e ∈ (cof2_finite hc β ω).toFinset, ∑ j ∈ Finset.range ⌈β⌉₊,
        1 / (((j : ℝ) + 2) * eval (DD θ X₀ ω) e * Xm X₀ ^ (j + 1))) := by
  classical
  have hXm := Queue6.Xm_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  have hXm2 : 2 ≤ Xm X₀ := by
    have h1 := Xm_half hc
    have h2 := X₀_ge_two_pow hc.hX
    have h3 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
    linarith
  set G := (cof2_finite hc β ω).toFinset with hG
  set K := ⌈β⌉₊ with hK
  set I : (PIdx X₀ →₀ ℕ) → ℕ → Set ℝ := fun e c =>
    {t : ℝ | Xm X₀ ≤ t ∧ α ≤ eval (DD θ X₀ ω) e * t ^ c ∧ eval (DD θ X₀ ω) e * t ^ c < β}
    with hI
  have hImeas : ∀ e c, MeasurableSet (I e c) := by
    intro e c
    have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) e * t ^ c :=
      measurable_const.mul (measurable_id.pow_const _)
    exact (measurableSet_le measurable_const measurable_id).inter
      ((measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const))
  set T := G ×ˢ ((Finset.range K).image (· + 2)) with hT
  have hpt : ∀ t, PhiBar2 θ X₀ α β (ω, t) ≤
      ∑ e ∈ G, ∑ j ∈ Finset.range K, (I e (j + 2)).indicator 1 t := by
    intro t
    unfold PhiBar2
    split_ifs with ht
    swap; · exact zero_le
    rw [tsum_eq_sum (s := T) (fun ec hec => by
      refine if_neg fun h1 => hec ?_
      obtain ⟨hc2, hlive, hα, hβ⟩ := h1
      have hev1 := one_le_evalD hc hlive
      have hpow : Xm X₀ ^ ec.2 ≤ t ^ ec.2 := pow_le_pow_left₀ hXm0.le ht _
      have h1 : eval (DD θ X₀ ω) ec.1 * Xm X₀ ^ ec.2 < β := by
        have := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ eval (DD θ X₀ ω) ec.1)
        linarith
      rw [hT, Finset.mem_product, Finset.mem_image]
      refine ⟨?_, ec.2 - 2, Finset.mem_range.mpr ?_, by omega⟩
      · rw [hG, Set.Finite.mem_toFinset]
        refine ⟨hlive, ?_⟩
        rw [le_div_iff₀ (by positivity)]
        have : Xm X₀ ^ 2 ≤ Xm X₀ ^ ec.2 := pow_le_pow_right₀ (by linarith) hc2
        nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤
          eval (DD θ X₀ ω) ec.1)]
      · -- `c < 2^c ≤ X₀⁻^c ≤ β`
        have h2 : ((2 : ℕ) : ℝ) ^ ec.2 ≤ Xm X₀ ^ ec.2 :=
          pow_le_pow_left₀ (by norm_num) (by push_cast; linarith) _
        have h3 : ((ec.2 : ℕ) : ℝ) < ((2 ^ ec.2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_pow_self (show 1 < 2 by norm_num)
        push_cast at h2 h3
        have h4 : Xm X₀ ^ ec.2 ≤ eval (DD θ X₀ ω) ec.1 * Xm X₀ ^ ec.2 := by
          have : 0 ≤ Xm X₀ ^ ec.2 := by positivity
          nlinarith
        have h5 : (ec.2 : ℝ) < β := by linarith
        have h6 : ec.2 < K := by exact_mod_cast lt_of_lt_of_le h5 (Nat.le_ceil β)
        omega)]
    rw [hT, Finset.sum_product]
    refine Finset.sum_le_sum fun e he => ?_
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases h1 : 2 ≤ (e, j + 2).2 ∧ Live (DD θ X₀ (ω, t).1) (e, j + 2).1 ∧
        α ≤ eval (DD θ X₀ (ω, t).1) (e, j + 2).1 * (ω, t).2 ^ (e, j + 2).2 ∧
        eval (DD θ X₀ (ω, t).1) (e, j + 2).1 * (ω, t).2 ^ (e, j + 2).2 < β
    · rw [if_pos h1, indicator_of_mem (show t ∈ I e (j + 2) from ⟨ht, h1.2.2.1, h1.2.2.2⟩)]
      rfl
    · rw [if_neg h1]; exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_finset_sum _ (fun e _ => Finset.measurable_sum _ fun j _ =>
    measurable_one.indicator (hImeas e (j + 2)))]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun e he => by
    rw [hG, Set.Finite.mem_toFinset] at he
    have := one_le_evalD hc he.1
    have : 0 ≤ β - α := by linarith
    exact mul_nonneg this (Finset.sum_nonneg fun j _ => by positivity))]
  refine Finset.sum_le_sum fun e he => ?_
  rw [hG, Set.Finite.mem_toFinset] at he
  have hev := one_le_evalD hc he.1
  rw [lintegral_finset_sum _ (fun j _ => measurable_one.indicator (hImeas e (j + 2))),
    Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      have : 0 ≤ β - α := by linarith
      positivity)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [lintegral_indicator_one (hImeas e (j + 2))]
  refine (volume_pow_window_le hXm0 (by linarith : 0 < eval (DD θ X₀ ω) e)
    (show 1 ≤ j + 2 by omega) hαβ).trans (le_of_eq ?_)
  congr 1
  rw [show j + 2 - 1 = j + 1 by omega]
  push_cast
  field_simp

end Bar2

section Fin2

variable (hc : Cond θ X₀)
include hc

lemma boxMean_PhiC2_ne_top (hev : Even X₀) {a b : ℝ} (hab : a ≤ b) (k : ℕ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiC2 θ X₀ k a b) ω ≠ ∞ := by
  unfold boxMean
  by_cases hA : ω ∈ (constructionLaw hc hev).A k
  · rw [indicator_of_mem hA]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := (b - a) *
        ∑ e ∈ (cof2_finite hc b ω).toFinset, ∑ j ∈ Finset.range ⌈b⌉₊,
          1 / (((j : ℝ) + 2) * eval (DD θ X₀ ω) e * Xm X₀ ^ (j + 1)))) ?_)
    calc ∫⁻ t in RankFull.box _ _, PhiC2 θ X₀ k a b (ω, t)
        ≤ ∫⁻ t, PhiC2 θ X₀ k a b (ω, t) := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ t, PhiBar2 θ X₀ a b (ω, t) := lintegral_mono fun t => PhiC2_le_PhiBar2 k a b _
      _ ≤ _ := lintegral_PhiBar2_le hc hab ω
  · rw [indicator_of_notMem hA]; exact ENNReal.zero_ne_top

end Fin2

/-! ### The sure count `N(w) ≤ 3.0001 w` below the horizon -/

section Count3

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- `N(X₀) ≤ 1.0001 X₀` (the lag bound at `X₀`, `T(X₀) = X₀`). -/
theorem NCount_X₀_le {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) (hXt : (X₀ : ℝ) + 26 * Real.log X₀ + 2 < t) :
    NCount X₀ (DF θ X₀ ω) X₀ ≤ 1.0001 * X₀ := by
  obtain ⟨hU, -, hnt'⟩ := hN
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
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) le_rfl
    (queue_of_QE hc hQC h0 le_rfl hXt)
  have hTX := h0.limModel_T_X₀
  have hDF : DF θ X₀ ω = DM M ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [hDF, ← realisedSystem_N hok]
  have h4 := rpow_lag_le hc (le_refl (X₀ : ℝ))
  have := (abs_le.mp hlag).2
  rw [hTX] at this
  linarith

include hc hev in
/-- **The sure count `N(w) ≤ 3.0001 w`** at every height `1 ≤ w`, with the horizon needed only
at heights `w ≥ X₀⁻`. -/
theorem NCount_le_three {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {w : ℝ} (hw1 : 1 ≤ w)
    (hhor : (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ w →
      max w X₀ + 26 * Real.log (max w X₀) + 2 < t ∧
        ∃ n, max w X₀ ≤ 2 ^ n * (X₀ : ℝ) / 2 ∧ ttB X₀ n ≤ t) :
    NCount X₀ (DF θ X₀ ω) w ≤ 3.0001 * w := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  obtain ⟨hU, hSG, hnt⟩ := hN
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
  have hok := limModel_realisedOK h0
  have hDF : DF θ X₀ ω = DM h0.limModel ω := by unfold DF; rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rcases lt_or_ge w ((X₀ : ℝ) - capH X₀ X₀ / 2) with hlow | hmid
  · rw [hDF, ← realisedSystem_N hok, realised_floor_eq hok hU hc.hX h0.limModel_low hw1 hlow]
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ w)
    linarith
  · obtain ⟨h1, n, h2, h3⟩ := hhor hmid
    rcases le_or_gt (X₀ : ℝ) w with hw | hw
    · rw [max_eq_left hw] at h1 h2
      exact NCount_le_high hc hev hQC hE1 ⟨hU, hSG, hnt⟩ hw h1 h2 h3
    · rw [max_eq_right hw.le] at h1
      have hNX := NCount_X₀_le hc hev hQC ⟨hU, hSG, hnt⟩ h1
      have h4H := four_capH_le hX0 hc.hX (le_refl (X₀ : ℝ))
      rw [hDF, ← realisedSystem_N hok] at hNX ⊢
      have hmono := (realisedSystem h0.limModel (capH X₀) ω).N_mono hw.le
      linarith

end Count3

/-! ### The horizon for the cofactors of `q^c` -/

section Hor2

variable (hc : Cond θ X₀)
include hc

/-- **The horizon for the counts read by `Comp⁽²⁾(W)`**: a height `w ≥ X₀⁻` with
`w ≤ 2b/X₀⁻²` is certified on `QC(< b) ∩ {E1 of time < b}`. -/
lemma horizon2 {b : ℤ} {w : ℝ} (hwX : (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ w)
    (hwb : w ≤ 2 * b / Xm X₀ ^ 2) :
    max w X₀ + 26 * Real.log (max w X₀) + 2 < b.toNat ∧
      ∃ n, max w X₀ ≤ 2 ^ n * (X₀ : ℝ) / 2 ∧ ttB X₀ n ≤ b.toNat := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXmX := Xm_half hc
  have hXX : (X₀ : ℝ) / 2 ≤ w := hXmX.trans hwX
  have hXm0 : 0 < Xm X₀ := by linarith
  have hb0 : (0 : ℝ) < b := by
    have : 0 < 2 * (b : ℝ) / Xm X₀ ^ 2 := by linarith
    have h2 : 0 < Xm X₀ ^ 2 := by positivity
    by_contra h; push_neg at h
    have : 2 * (b : ℝ) / Xm X₀ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
    linarith
  -- `w ≤ 8b/X₀²`, so `b ≥ X₀³/16`
  have hXm2 : (X₀ : ℝ) ^ 2 / 4 ≤ Xm X₀ ^ 2 := by nlinarith
  have hw8 : w ≤ 8 * b / (X₀ : ℝ) ^ 2 := by
    refine hwb.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hbig : (X₀ : ℝ) ^ 3 / 16 ≤ b := by
    have h1 : (X₀ : ℝ) / 2 ≤ 8 * b / (X₀ : ℝ) ^ 2 := hXX.trans hw8
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set M := max w (X₀ : ℝ) with hM
  have hMb : M ≤ b / 8 := by
    refine max_le ?_ ?_
    · have : 8 * (b : ℝ) / (X₀ : ℝ) ^ 2 ≤ b / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have h64 : (64 : ℝ) ≤ (X₀ : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h64 hb0.le]
      linarith
    · nlinarith
  have hM0 : 0 < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hMX : (X₀ : ℝ) ≤ M := le_max_right _ _
  have hb0' : (0 : ℤ) ≤ b := by exact_mod_cast hb0.le
  have hbt : ((b.toNat : ℕ) : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb0'
  -- the scale
  have hex : ∃ n : ℕ, M ≤ 2 ^ n * (X₀ : ℝ) / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * M / X₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith
  set n := Nat.find hex with hn
  have hnM : M ≤ 2 ^ n * (X₀ : ℝ) / 2 := Nat.find_spec hex
  have hn2 : 2 ^ n * (X₀ : ℝ) / 2 ≤ 2 * M := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp; linarith
    · obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hlt := Nat.find_min hex (show n' < n by omega)
      push_neg at hlt
      rw [hn', pow_succ]
      linarith
  refine ⟨?_, n, hnM, ?_⟩
  · have hlog := log_le_lin hc hM0
    rw [hbt]
    nlinarith
  · unfold ttB
    have h1 : ((⌈2 ^ n * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) ≤ b := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ n * (X₀ : ℝ) / 2 by positivity)
      nlinarith
    rw [← hbt] at h1
    exact_mod_cast h1

end Hor2

/-! ### The harmonic sum of the cofactors of `q^c` -/

section Harm2

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- `∑_{m ≤ b/X₀⁻², m live} 1/m ≤ 1 + 6.0002 ⌈log₂(b/X₀⁻²)⌉` (the cofactor `1` and the
dyadic bound with `N(w) ≤ 3.0001 w`), on the queue constraints and the cluster events of time
`< b`. -/
theorem harm2_le {b : ℤ} (hb0 : 0 < b) {ω : JitterΩ}
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat)
    (hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) :
    ∑ e ∈ (cof2_finite hc (b : ℝ) ω).toFinset, 1 / eval (DD θ X₀ ω) e ≤
      1 + 2 * 3.0001 * ⌈Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2)⌉₊ := by
  classical
  set G := (cof2_finite hc (b : ℝ) ω).toFinset with hG
  have hXm := Queue6.Xm_pos hc
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  have hy0 : 0 < (b : ℝ) / Xm X₀ ^ 2 := div_pos hb (by positivity)
  rw [← Finset.sum_filter_add_sum_filter_not G (fun e => e = 0)]
  refine add_le_add ?_ ?_
  · -- the cofactor `1`
    have hcard : (G.filter fun e => e = 0).card ≤ 1 :=
      Finset.card_le_one.mpr fun x hx y hy => by
        rw [Finset.mem_filter] at hx hy; rw [hx.2, hy.2]
    have hle : ∀ e ∈ G.filter (fun e => e = 0), 1 / eval (DD θ X₀ ω) e ≤ 1 := by
      intro e he
      rw [Finset.mem_filter, hG, Set.Finite.mem_toFinset] at he
      have := one_le_evalD hc he.1.1
      rw [div_le_one (by linarith)]; exact this
    calc ∑ e ∈ G.filter (fun e => e = 0), 1 / eval (DD θ X₀ ω) e
        ≤ ∑ _e ∈ G.filter (fun e => e = 0), (1 : ℝ) := Finset.sum_le_sum hle
      _ = ((G.filter fun e => e = 0).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  · refine harmonic_dyadic _ (fun e => eval (DD θ X₀ ω) e) (fun e he => ?_) _
      (fun e he => ?_) (fun j hj => ?_)
    · rw [Finset.mem_filter, hG, Set.Finite.mem_toFinset] at he
      exact one_lt_eval hc he.1.1 he.2
    · rw [Finset.mem_filter, hG, Set.Finite.mem_toFinset] at he
      exact he.1.2.trans (two_pow_ceil_logb hy0)
    · set w : ℝ := 2 ^ (j + 1)
      have hw1 : 1 ≤ w := one_le_pow₀ (by norm_num)
      have hwy := two_pow_lt_of_lt_ceil hy0 hj
      have hEf : (elemsLe X₀ (DF θ X₀ ω) w).Finite :=
        (finite_elems_gt (X₀ := X₀) (locFinD_DM hc.hX (fun j => clamp01_mem (ω j))
          (CM θ X₀ ω)) w).subset fun e he => ⟨he.1, pval_gt_one hc he.1, he.2⟩
      have hcard : (((G.filter fun e => ¬ e = 0).filter
          fun e => eval (DD θ X₀ ω) e ≤ w).card : ℝ) ≤ NCount X₀ (DF θ X₀ ω) w := by
        unfold NCount
        have : (((G.filter fun e => ¬ e = 0).filter fun e => eval (DD θ X₀ ω) e ≤ w) :
            Set (PIdx X₀ →₀ ℕ)) ⊆ elemsLe X₀ (DF θ X₀ ω) w := by
          intro e he
          rw [Finset.coe_filter, mem_setOf_eq, Finset.mem_filter, hG,
            Set.Finite.mem_toFinset] at he
          exact ⟨he.1.1.1, he.2⟩
        have h := Set.ncard_le_ncard this hEf
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
      refine hcard.trans (NCount_le_three hc hev hQC hE1 hN hw1 fun hwX => ?_)
      exact horizon2 hc hwX (by rw [mul_div_assoc]; exact hwy.le)

end Harm2

/-! ### Eq. (s2) -/

variable (θ X₀) in
/-- **Eq. (s2) for every window** (Lemma 5.22, "Together, for every window `I`"): for a
truncation level `C ≥ 0`, a window `[a, b)` with `v/4 ≤ a < b ≤ 2v`, `v ≥ X₀`, a.s. on the queue
constraints and the cluster events of time `< b`, the partial compensators of
`min(X⁽²⁾_q(W), C)` are at most `s₂(v) |W|`. -/
def S2Core : Prop :=
  ∀ (C : ℝ), 0 ≤ C → ∀ (a b : ℤ) (v : ℝ), (X₀ : ℝ) ≤ v → 0 < b → a < b → v / 4 ≤ (a : ℝ) →
    (b : ℝ) ≤ 2 * v →
    ∀ᵐ ω ∂jitterMeasure, ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat →
      (∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) → ∀ n,
        ∑ k ∈ Finset.range n, (jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C |
          jitterFiltration k]) ω ≤ s2E3 X₀ v * ((b : ℝ) - a)

variable (θ X₀) in
/-- **The second bound of (s2)** (named hypothesis; 04d-noise.tex, "Second bound, for
`σ > log X₀⁻`": `Comp⁽²⁾(I)/|I| ≤ 0.73 L_u e^{-σ}`, `σ = ½√(L_u log L_u)`, from the
Dickman-quality bound of Lemma smooth-v, 04a-setup.tex, under (H_BS)): `S2Core` at the heights
`v` with `log X₀⁻ < σ(v)`. -/
def S2SecondBranch : Prop :=
  ∀ (C : ℝ), 0 ≤ C → ∀ (a b : ℤ) (v : ℝ), (X₀ : ℝ) ≤ v → 0 < b → a < b → v / 4 ≤ (a : ℝ) →
    (b : ℝ) ≤ 2 * v →
    Real.log (Xm X₀) < Real.sqrt (Real.log v * Real.log (Real.log v)) / 2 →
    ∀ᵐ ω ∂jitterMeasure, ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat →
      (∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) → ∀ n,
        ∑ k ∈ Finset.range n, (jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C |
          jitterFiltration k]) ω ≤ s2E3 X₀ v * ((b : ℝ) - a)

section First

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **The first bound of (s2)** (04d-noise.tex, "First bound"): `S2Core` at the heights `v` with
`σ(v) ≤ log X₀⁻`, where `s₂(v) = 9 L_v/X₀⁻`. -/
theorem s2_first {C : ℝ} (hC0 : 0 ≤ C) {a b : ℤ} {v : ℝ} (hv : (X₀ : ℝ) ≤ v) (hb0 : 0 < b)
    (hab : a < b) (hb2 : (b : ℝ) ≤ 2 * v)
    (hσ : Real.sqrt (Real.log v * Real.log (Real.log v)) / 2 ≤ Real.log (Xm X₀)) :
    ∀ᵐ ω ∂jitterMeasure, ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat →
      (∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) → ∀ n,
        ∑ k ∈ Finset.range n, (jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C |
          jitterFiltration k]) ω ≤ s2E3 X₀ v * ((b : ℝ) - a) := by
  classical
  set J := constructionLaw hc hev with hJ
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hk : ∀ k, jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C |
      jitterFiltration k] ≤ᵐ[jitterMeasure]
      fun ω => min C (boxMean J k (PhiC2 θ X₀ k a b) ω).toReal := by
    intro k
    have hf0 : ∀ ω, 0 ≤ min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C := fun ω =>
      le_min (Nat.cast_nonneg _) hC0
    have hfC : ∀ ω, min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C ≤ C := fun ω => min_le_right _ _
    have hfm : Measurable fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C :=
      (((x2count_adapted hc a b k).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    have hfΦ : ∀ᵐ ω ∂jitterMeasure, ENNReal.ofReal (min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C) ≤
        (J.A k).indicator (fun ω => PhiC2 θ X₀ k a b (ω, J.q k ω)) ω := by
      filter_upwards [ae_stageGood hc] with ω hω
      exact X2_le_PhiC2 hc a b C k (hω k)
    exact condExp_le_boxMean J k hC0 hf0 hfC hfm
      (fun S hS => PhiC2_jmeas hc k a b S hS) hfΦ
      (fun ω => boxMean_PhiC2_ne_top hc hev hab' k ω)
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  filter_upwards [ae_all_iff.mpr hk, hnice] with ω hω hN hQC hE1 n
  have hXm := Queue6.Xm_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  have hXmX := Xm_half hc
  have hXb := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  set G := (cof2_finite hc (b : ℝ) ω).toFinset with hG
  set K := ⌈(b : ℝ)⌉₊
  set S := ∑ e ∈ G, ∑ j ∈ Finset.range K,
    1 / (((j : ℝ) + 2) * eval (DD θ X₀ ω) e * Xm X₀ ^ (j + 1)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e he => Finset.sum_nonneg fun j _ => by
    rw [hG, Set.Finite.mem_toFinset] at he
    have := one_le_evalD hc he.1
    positivity
  have hfin : ∀ k, boxMean J k (PhiC2 θ X₀ k a b) ω ≠ ∞ := fun k =>
    boxMean_PhiC2_ne_top hc hev hab' k ω
  have hsum : ∑' k, boxMean J k (PhiC2 θ X₀ k a b) ω ≤ 2 * ENNReal.ofReal ((b - a) * S) :=
    (sum_boxMean_le J (fun k => PhiC2 θ X₀ k a b) (PhiBar2 θ X₀ a b) ω (PhiBar2_meas a b ω)
      (fun k t => PhiC2_le_PhiBar2 k a b _)).trans
      (mul_le_mul_right (lintegral_PhiBar2_le hc hab' ω) 2)
  have hrhs : 0 ≤ 2 * ((b - a) * S) := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  have hcomp : ∑ k ∈ Finset.range n, (jitterMeasure[fun ω =>
      min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C | jitterFiltration k]) ω ≤
      2 * ((b - a) * S) := by
    refine (Finset.sum_le_sum fun k _ => (hω k).trans (min_le_right _ _)).trans ?_
    rw [← ENNReal.toReal_sum fun k _ => hfin k]
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((b - a) * S) =
        ENNReal.ofReal (2 * ((b - a) * S)) := by
      rw [ENNReal.ofReal_mul (p := 2) (by norm_num)]; norm_num
    calc (∑ k ∈ Finset.range n, boxMean J k (PhiC2 θ X₀ k a b) ω).toReal
        ≤ (ENNReal.ofReal (2 * ((b - a) * S))).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [← h2]
          exact (ENNReal.sum_le_tsum _).trans hsum
      _ = 2 * ((b - a) * S) := ENNReal.toReal_ofReal hrhs
  -- `S = (∑ 1/m)(∑_j r^{j+1}/(j+2))`, `r = 1/X₀⁻`
  set r := 1 / Xm X₀ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 1 / 2 := by
    rw [hr]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  set Hs := ∑ e ∈ G, 1 / eval (DD θ X₀ ω) e with hHs
  have hSeq : S = Hs * ∑ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) := by
    rw [hS, hHs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG, Set.Finite.mem_toFinset] at he
    have := one_le_evalD hc he.1
    rw [hr, one_div_pow]
    field_simp
  have hQ := sum_pow_div_le hr0 hr2 K
  have hH := harm2_le hc hev hb0 hQC hE1 hN
  rw [← hG, ← hHs] at hH
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun e he => by
    rw [hG, Set.Finite.mem_toFinset] at he
    have := one_le_evalD hc he.1
    positivity
  -- numerics
  set J'' := ⌈Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2)⌉₊ with hJ''
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  have hlv : 10 ^ 8 ≤ Real.log v := hc.hX.trans (Real.log_le_log (by linarith) hv)
  have hl2 : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hJ'' : (J'' : ℝ) ≤ (Real.log v + 0.7) / 0.69 + 1 := by
    by_cases hJ0 : J'' = 0
    · rw [hJ0]; push_cast
      have : 0 ≤ (Real.log v + 0.7) / 0.69 := by positivity
      linarith
    · have hl : 0 < Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2) := by
        by_contra h; push_neg at h; exact hJ0 (Nat.ceil_eq_zero.mpr h)
      have h1 : (J'' : ℝ) < Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2) + 1 := Nat.ceil_lt_add_one hl.le
      have h2 : Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2) ≤ (Real.log v + 0.7) / 0.69 := by
        unfold Real.logb
        have hy0 : 0 < (b : ℝ) / Xm X₀ ^ 2 := div_pos hb (by positivity)
        have h3 : Real.log ((b : ℝ) / Xm X₀ ^ 2) ≤ Real.log v + 0.7 := by
          have h4 : (b : ℝ) / Xm X₀ ^ 2 ≤ 2 * v := by
            refine le_trans ?_ hb2
            rw [div_le_iff₀ (by positivity)]
            have : (1 : ℝ) ≤ Xm X₀ ^ 2 := by nlinarith
            nlinarith
          have h5 := Real.log_le_log hy0 h4
          rw [Real.log_mul (by norm_num) (by linarith)] at h5
          linarith
        have h6 : 0 < Real.log ((b : ℝ) / Xm X₀ ^ 2) := by
          have := Real.logb_pos_iff (b := 2) (by norm_num) hy0 |>.mp hl
          exact Real.log_pos this
        calc Real.log ((b : ℝ) / Xm X₀ ^ 2) / Real.log 2
            ≤ Real.log ((b : ℝ) / Xm X₀ ^ 2) / 0.69 :=
              div_le_div_of_nonneg_left h6.le (by norm_num) hl2
          _ ≤ (Real.log v + 0.7) / 0.69 := div_le_div_of_nonneg_right h3 (by norm_num)
      linarith
  have hs2 : s2E3 X₀ v = 9 * Real.log v / Xm X₀ := by
    unfold s2E3
    rw [max_eq_left hσ, Real.exp_neg, Real.exp_log hXm0]
    ring
  rw [hs2]
  have hW0 : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hQ' : ∑ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) ≤
      (1 / 2 + 2 / Xm X₀) / Xm X₀ := by
    refine hQ.trans (le_of_eq ?_)
    rw [hr]; field_simp
  have hQ0 : 0 ≤ ∑ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hS' : S ≤ (1 + 2 * 3.0001 * J'') * ((1 / 2 + 2 / Xm X₀) / Xm X₀) := by
    rw [hSeq]
    exact mul_le_mul hH hQ' hQ0 (by positivity)
  have hfinal : 2 * ((1 + 2 * 3.0001 * J'') * ((1 / 2 + 2 / Xm X₀) / Xm X₀)) ≤
      9 * Real.log v / Xm X₀ := by
    rw [show 2 * ((1 + 2 * 3.0001 * (J'' : ℝ)) * ((1 / 2 + 2 / Xm X₀) / Xm X₀)) =
      ((1 + 2 * 3.0001 * (J'' : ℝ)) * (1 + 4 / Xm X₀)) / Xm X₀ by ring]
    refine div_le_div_of_nonneg_right ?_ hXm0.le
    have h4 : 4 / Xm X₀ ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ hXm0 (by norm_num)]; linarith
    have hJ0 : (0 : ℝ) ≤ J'' := Nat.cast_nonneg _
    have e69 : (Real.log v + 0.7) / 0.69 = (Real.log v + 0.7) * (100 / 69) := by ring
    set A := 1 + 2 * 3.0001 * (J'' : ℝ) with hA
    have hA0 : 0 ≤ A := by positivity
    have hAb : A ≤ 1 + 2 * 3.0001 * ((Real.log v + 0.7) * (100 / 69) + 1) := by
      rw [hA, ← e69]; linarith
    have h1 : A * (1 + 4 / Xm X₀) ≤ A * (1 + 1 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) hA0
    have h2 : A * (1 + 1 / 1000) ≤
        (1 + 2 * 3.0001 * ((Real.log v + 0.7) * (100 / 69) + 1)) * (1 + 1 / 1000) :=
      mul_le_mul_of_nonneg_right hAb (by norm_num)
    linarith
  calc _ ≤ 2 * (((b : ℝ) - a) * S) := hcomp
    _ ≤ 2 * (((b : ℝ) - a) * ((1 + 2 * 3.0001 * J'') * ((1 / 2 + 2 / Xm X₀) / Xm X₀))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS' hW0) (by norm_num)
    _ = (2 * ((1 + 2 * 3.0001 * J'') * ((1 / 2 + 2 / Xm X₀) / Xm X₀))) * ((b : ℝ) - a) := by
        ring
    _ ≤ 9 * Real.log v / Xm X₀ * ((b : ℝ) - a) := mul_le_mul_of_nonneg_right hfinal hW0

end First

/-! ### (s2) and the two fields -/

section Fields

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **Eq. (s2) for every window**, from its second bound (`S2SecondBranch`); the first bound is
proved (`s2_first`). -/
theorem s2Core_of (hS : S2SecondBranch θ X₀) : S2Core θ X₀ := by
  intro C hC a b v hv hb0 hab hva hb2
  by_cases hσ : Real.sqrt (Real.log v * Real.log (Real.log v)) / 2 ≤ Real.log (Xm X₀)
  · exact s2_first hc hev hC hv hb0 hab hb2 hσ
  · exact hS C hC a b v hv hb0 hab hva hb2 (lt_of_not_ge hσ)

/-- **The field `E3S2Bound`** (eq. (s2) for the windows of `𝒲'_u`, `X̃⁽²⁾ = min(X⁽²⁾, b₂)`). -/
theorem e3S2Bound_of (h : S2Core θ X₀) : E3S2Bound θ X₀ := by
  intro m a b hW
  obtain ⟨hua, hab, hb2, -⟩ := hW
  obtain ⟨huX, -, -, hM1⟩ := uS_facts hc m
  have hb2C : 0 ≤ b2E3 X₀ (uS X₀ m) := by unfold b2E3; positivity
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := by
      have h1 := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
      have : (a : ℝ) < b := by exact_mod_cast hab
      linarith
    exact_mod_cast this
  have hva : uS X₀ m / 4 ≤ (a : ℝ) := by
    have h0 : 0 ≤ uS X₀ m := (Nat.cast_nonneg X₀).trans huX
    linarith
  filter_upwards [h _ hb2C a b (uS X₀ m) huX hb0 hab hva hb2] with ω hω hG n
  have hba : ((b - a : ℤ) : ℝ) = (b : ℝ) - a := by push_cast; ring
  rw [hba]
  exact hω hG.1 hG.2 n

/-- **The field `E2S2Bound`** (eq. (s2) for the windows of `𝓘_u`, through
`1[X⁽²⁾ ≥ 1] ≤ min(X⁽²⁾, 1)`, at the scale `v = 2u`). -/
theorem e2S2Bound_of (h : S2Core θ X₀) : E2S2Bound θ X₀ := by
  intro m a b hadm
  obtain ⟨hub, hb3, hab, hWl⟩ := hadm
  obtain ⟨huX, -, -, -⟩ := uS_facts hc m
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hs2I : s2E3 X₀ (2 * uS X₀ m) ≤ s2I X₀ m :=
    (le_max_right _ _).trans (le_max_right _ _)
  rcases hab.lt_or_eq with hab | rfl
  swap
  · -- the empty window
    refine Filter.Eventually.of_forall fun ω _ n => ?_
    have hz : ∀ k, Ind2 θ X₀ a a k = fun _ => 0 := by
      intro k; funext ω
      unfold Ind2
      rw [if_neg]
      have h0 : X2count (CM θ X₀ ω) (Ucl ω) a a k = 0 := by
        unfold X2count x2set
        rw [ncard_xset (θ := θ) (X₀ := X₀) a a k (2 ≤ ·) ω]
        have : xsetP θ X₀ (a : ℝ) (a : ℝ) k (2 ≤ ·) ω = ∅ := by
          ext e; simp only [xsetP, mem_setOf_eq, mem_empty_iff_false, iff_false]
          rintro ⟨-, -, h1, h2, -⟩; linarith
        rw [this, Set.ncard_empty]; simp
      rw [h0]; norm_num
    have hz0 : ∀ k, jitterMeasure[Ind2 θ X₀ a a k | jitterFiltration k] = 0 := by
      intro k; rw [hz k]; exact condExp_zero
    simp only [hz0, Pi.zero_apply, Finset.sum_const_zero, sub_self, mul_zero, le_refl]
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := by linarith
    exact_mod_cast this
  have hb4 : (b : ℝ) ≤ 2 * (2 * uS X₀ m) := by linarith
  have hmono : ∀ k, jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k] ≤ᵐ[jitterMeasure]
      jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) 1 | jitterFiltration k] := by
    intro k
    have hI := (Ind2_adapted hc a b k).mono (jitterFiltration.le _)
    have hmm : Measurable fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) 1 :=
      (((x2count_adapted hc a b k).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    have hI01 : ∀ ω, 0 ≤ Ind2 θ X₀ a b k ω ∧ Ind2 θ X₀ a b k ω ≤ 1 := by
      intro ω; unfold Ind2; split_ifs <;> norm_num
    refine condExp_mono ?_ ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact Integrable.of_bound hI.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hI01 ω).1]; exact (hI01 ω).2)
    · refine Integrable.of_bound hmm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => ?_)
      have h0 : 0 ≤ X2count (CM θ X₀ ω) (Ucl ω) a b k := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min h0 zero_le_one)]
      exact min_le_right _ _
    · show Ind2 θ X₀ a b k ω ≤ min (X2count (CM θ X₀ ω) (Ucl ω) a b k) 1
      have h0 : 0 ≤ X2count (CM θ X₀ ω) (Ucl ω) a b k := Nat.cast_nonneg _
      unfold Ind2
      split_ifs with h1
      · exact le_min h1 le_rfl
      · exact le_min h0 zero_le_one
  have hva : 2 * uS X₀ m / 4 ≤ (a : ℝ) := by
    have hWq := Queue6.Wlen_le_quarter hX0 hc.hX huX
    have : ((b - a : ℤ) : ℝ) = (b : ℝ) - a := by push_cast; ring
    rw [this] at hWl
    linarith
  filter_upwards [h 1 zero_le_one a b (2 * uS X₀ m) (by linarith) hb0 hab hva hb4,
    ae_all_iff.mpr hmono] with ω hω hm hG n
  have hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat := hG.1
  have hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n := fun n hn =>
    mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have hW0 : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  calc ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω
      ≤ ∑ k ∈ Finset.range n, (jitterMeasure[fun ω =>
          min (X2count (CM θ X₀ ω) (Ucl ω) a b k) 1 | jitterFiltration k]) ω :=
        Finset.sum_le_sum fun k _ => hm k
    _ ≤ s2E3 X₀ (2 * uS X₀ m) * ((b : ℝ) - a) := hω hQC hE1 n
    _ ≤ s2I X₀ m * ((b : ℝ) - a) := mul_le_mul_of_nonneg_right hs2I hW0

end Fields

end BModel
