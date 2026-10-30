module

public import RequestProject.Beurling.Model.E3S2
public import RequestProject.Beurling.Model.S2Hbs

/-!
# The second bound of (s2) (04d-noise.tex, "Second bound, for `σ > log X₀⁻`")

For the prime `q` decided at relative slot `k + 1`, the cofactor `m` of a composite `q^c m`
(`c ≥ 2`) counted by `X⁽²⁾_q(W)` has all its primes decided before `q`, hence of value
`≤ 2q` (`pval_le_two`: the slot starts are non-decreasing and `H(s) ≤ s/4`). So the majorant
`Φ⁽³⁾` of `Φ⁽²⁾` (`E3S2.lean`) may also require `P⁺(m) ≤ 2t`. For `m ∈ (Y, 2Y]`, `t ≥ X₀⁻` and
`a ≤ m t^c < b ≤ 2v`, `a ≥ v/4`:

* `t ≥ e^{s_Y}`, `s_Y = max(log X₀⁻, log(v/(8Y))/c)`, so `vol ≤ |W|/(c m e^{(c-1)s_Y})`;
* `P⁺(m) ≤ 2t < z = 2(2v/Y)^{1/c}`, and the block is empty unless `Y < 2v/X₀⁻^c`.

The block sums `∑_{m ∈ (Y, 2Y], P⁺(m) ≤ z} 1/m` are the quantity `v(log Y, z)` of Lemma 5.3
(smooth-v) for the realised system (`sum_le_vSmooth`), which satisfies (H_BS) up to
`4v/X₀⁻²` on `QC(< b) ∩ {E1 of time < b}` (`hbs_QE`). The bound per block,
`e^{-(c-1)s_Y} v(log Y, z) ≤ 3 e^{-σ} X₀⁻^{-(c-2)/2}` (the two cases `u' ≤ log z`,
`u' > log z` of the paper), is `BlockBound` (proved in `S2Block.lean`). With `≤ log₂(2v/X₀⁻²) + 2`
blocks and `∑_c X₀⁻^{-(c-2)/2}/c ≤ 1/2 + 2X₀⁻^{-1/2}`, `ρ̃ ≤ 2` gives
`Comp⁽²⁾(W) ≤ 9 L_v e^{-σ} |W|`.

The windows read are `v/4 ≤ a < b ≤ 2v` (both consumers: `𝒲'_u`, `a ≥ u = v`; `𝓘_u`,
`a ≥ b - W_len(u) ≥ 3u/4`, `v = 2u`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed Queue6
  SlotModel
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The decision order: cofactor primes are `≤ 2q` -/

section Order

variable (hc : Cond θ X₀)
include hc

lemma valF_le_two {j k : ℕ} (hjk : j < k) (ω : JitterΩ) :
    valF θ X₀ j ω ≤ 2 * valF θ X₀ k ω := by
  have h1 : valF θ X₀ j ω ≤ slotF θ X₀ j ω + HF θ X₀ j ω / 2 := by
    rw [valF_eq]; exact (landing_mem_box (HF_pos hc j ω).le (clamp01_mem _)).2
  have h2 : 4 * HF θ X₀ j ω ≤ slotF θ X₀ j ω :=
    four_capH_le (Nat.cast_nonneg _) hc.hX (slotF_ge hc j ω)
  have h3 : slotF θ X₀ j ω ≤ slotF θ X₀ k ω :=
    (Mcl θ X₀ ω).slot_mono (show j + 1 ≤ k + 1 by omega)
  have h4 := valF_ge_78 hc k ω
  have h5 := slotF_ge hc j ω
  linarith

/-- **The cofactor primes of `q^c` are `≤ 2q`**: the primes decided before slot `k + 1` (and
the rational primes `p < X₀`) have value `≤ 2 q_k`. -/
lemma pval_le_two {k : ℕ} (ω : JitterΩ) (e : PIdx X₀ →₀ ℕ)
    (he : ∀ j, e (Sum.inr j) ≠ 0 → j < k) :
    ∀ i ∈ e.support, pval (DD θ X₀ ω) i ≤ 2 * valF θ X₀ k ω := by
  intro i hi
  cases i with
  | inl p =>
    show (p.1 : ℝ) ≤ _
    have h1 : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
    have h2 := Xm_half hc
    have h3 := valF_ge_Xm hc k ω
    linarith
  | inr j => exact valF_le_two hc (he j (Finsupp.mem_support_iff.mp hi)) ω

end Order

/-! ### The smooth majorants -/

variable (θ X₀) in
/-- The cofactor `e` is `2t`-smooth: all its prime values are `≤ 2t`. -/
def Sm2 (ω : JitterΩ) (e : PIdx X₀ →₀ ℕ) (t : ℝ) : Prop :=
  ∀ i ∈ e.support, pval (DD θ X₀ ω) i ≤ 2 * t

open Classical in
variable (θ X₀) in
/-- `Φ⁽³⁾_k(ω, t)`: as `PhiC2`, with the cofactors `2t`-smooth. -/
noncomputable def PhiC3 (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' ec : (PIdx X₀ →₀ ℕ) × ℕ, if 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧
    Sm2 θ X₀ p.1 ec.1 p.2 ∧
    α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    then 1 else 0 else 0

open Classical in
variable (θ X₀) in
/-- The pathwise majorant: as `PhiC3`, over all live `2t`-smooth cofactors. -/
noncomputable def PhiBar3 (α β : ℝ) (p : JitterΩ × ℝ) : ℝ≥0∞ :=
  if Xm X₀ ≤ p.2 then ∑' ec : (PIdx X₀ →₀ ℕ) × ℕ, if 2 ≤ ec.2 ∧ Live (DD θ X₀ p.1) ec.1 ∧
    Sm2 θ X₀ p.1 ec.1 p.2 ∧
    α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    then 1 else 0 else 0

lemma PhiC3_le_PhiBar3 (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) :
    PhiC3 θ X₀ k α β p ≤ PhiBar3 θ X₀ α β p := by
  classical
  unfold PhiC3 PhiBar3
  split_ifs with h
  · refine ENNReal.tsum_le_tsum fun ec => ?_
    by_cases h1 : 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧ Sm2 θ X₀ p.1 ec.1 p.2 ∧
        α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1.1, h1.2.2⟩]
    · rw [if_neg h1]; exact zero_le
  · exact le_rfl

lemma PhiC3_le_PhiC2 (k : ℕ) (α β : ℝ) (p : JitterΩ × ℝ) :
    PhiC3 θ X₀ k α β p ≤ PhiC2 θ X₀ k α β p := by
  classical
  unfold PhiC3 PhiC2
  split_ifs with h
  · refine ENNReal.tsum_le_tsum fun ec => ?_
    by_cases h1 : 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧ Sm2 θ X₀ p.1 ec.1 p.2 ∧
        α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.2⟩]
    · rw [if_neg h1]; exact zero_le
  · exact le_rfl

lemma measurableSet_Sm2 (ω : JitterΩ) (e : PIdx X₀ →₀ ℕ) :
    MeasurableSet {t : ℝ | Sm2 θ X₀ ω e t} := by
  have : {t : ℝ | Sm2 θ X₀ ω e t} = ⋂ i ∈ e.support, {t | pval (DD θ X₀ ω) i ≤ 2 * t} := by
    ext t; simp [Sm2]
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ =>
    measurableSet_le measurable_const (measurable_const.mul measurable_id)

lemma PhiBar3_meas (α β : ℝ) (ω : JitterΩ) : Measurable fun t => PhiBar3 θ X₀ α β (ω, t) := by
  classical
  unfold PhiBar3
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  refine Measurable.ennreal_tsum fun ec => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) ec.1 * t ^ ec.2 :=
    measurable_const.mul (measurable_id.pow_const _)
  exact ((MeasurableSet.const (2 ≤ ec.2)).inter ((MeasurableSet.const
    (Live (DD θ X₀ ω) ec.1)).inter ((measurableSet_Sm2 ω ec.1).inter
      ((measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)))) :)

section Meas3

variable (hc : Cond θ X₀)
include hc

lemma PhiC3_jmeas (k : ℕ) (α β : ℝ) (S : Set JitterΩ)
    (hS : MeasurableSet[jitterFiltration k] S) :
    RankFull.JMeas (jitterFiltration k) (fun p => S.indicator 1 p.1 * PhiC3 θ X₀ k α β p) := by
  classical
  unfold RankFull.JMeas
  letI mP : MeasurableSpace (JitterΩ × ℝ) :=
    @Prod.instMeasurableSpace JitterΩ ℝ (jitterFiltration k) _
  have hfst : @Measurable _ _ mP (jitterFiltration k) Prod.fst :=
    @measurable_fst _ _ (jitterFiltration k) _
  have hsnd : @Measurable _ _ mP _ Prod.snd := @measurable_snd _ _ (jitterFiltration k) _
  refine Measurable.mul (m := mP) ?_ ?_
  · exact (measurable_const.indicator hS).comp hfst
  · unfold PhiC3
    refine Measurable.ite (m := mP) (measurableSet_le measurable_const hsnd) ?_ measurable_const
    refine Measurable.ennreal_tsum (mα := mP) fun ec => ?_
    by_cases he : ∀ j, ec.1 (Sum.inr j) ≠ 0 → j < k
    · have hev : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ =>
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 :=
        ((eval_meas_lt hc ec.1 he).comp hfst).mul (hsnd.pow_const _)
      have hsm : @MeasurableSet _ mP {p : JitterΩ × ℝ | Sm2 θ X₀ p.1 ec.1 p.2} := by
        have : {p : JitterΩ × ℝ | Sm2 θ X₀ p.1 ec.1 p.2} =
            ⋂ i ∈ ec.1.support, {p : JitterΩ × ℝ | pval (DD θ X₀ p.1) i ≤ 2 * p.2} := by
          ext p; simp [Sm2]
        rw [this]
        refine Finset.measurableSet_biInter _ fun i hi => ?_
        have hpi : @Measurable _ ℝ mP _ fun p : JitterΩ × ℝ => pval (DD θ X₀ p.1) i :=
          (pval_meas_lt hc i fun j hj => by
            subst hj; exact he j (Finsupp.mem_support_iff.mp hi)).comp hfst
        exact measurableSet_le hpi (measurable_const.mul hsnd)
      have hset : @MeasurableSet _ mP {p : JitterΩ × ℝ | 2 ≤ ec.2 ∧
          p.1 ∈ {ω | ec.1 ∈ cofP2 θ X₀ k ω} ∧ Sm2 θ X₀ p.1 ec.1 p.2 ∧
          α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β} :=
        (MeasurableSet.const _).inter ((hfst (cofP2_meas hc k ec.1)).inter (hsm.inter
          ((measurableSet_le measurable_const hev).inter (measurableSet_lt hev measurable_const))))
      exact Measurable.ite (m := mP) hset measurable_const measurable_const
    · have : (fun p : JitterΩ × ℝ => if 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k p.1 ∧
          Sm2 θ X₀ p.1 ec.1 p.2 ∧ α ≤ eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 ∧
          eval (DD θ X₀ p.1) ec.1 * p.2 ^ ec.2 < β then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
        funext p
        rw [if_neg]
        rintro ⟨-, ⟨-, h⟩, -⟩; exact he h
      rw [this]; exact measurable_const

/-- At `t = q_k`, the smoothness condition is automatic (`pval_le_two`). -/
lemma PhiC2_eq_PhiC3 (k : ℕ) (α β : ℝ) (ω : JitterΩ) :
    PhiC2 θ X₀ k α β (ω, valF θ X₀ k ω) = PhiC3 θ X₀ k α β (ω, valF θ X₀ k ω) := by
  classical
  unfold PhiC2 PhiC3
  split_ifs with h
  · refine tsum_congr fun ec => ?_
    by_cases h1 : 2 ≤ ec.2 ∧ ec.1 ∈ cofP2 θ X₀ k ω ∧
        α ≤ eval (DD θ X₀ ω) ec.1 * valF θ X₀ k ω ^ ec.2 ∧
        eval (DD θ X₀ ω) ec.1 * valF θ X₀ k ω ^ ec.2 < β
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, pval_le_two hc ω ec.1 h1.2.1.2, h1.2.2⟩]
    · rw [if_neg h1, if_neg fun h2 => h1 ⟨h2.1, h2.2.1, h2.2.2.2⟩]
  · rfl

/-- **`min(X⁽²⁾_q(W), C) ≤ Φ⁽³⁾_k(ω, q)`** on the good stage. -/
theorem X2_le_PhiC3 (a b : ℝ) (C : ℝ) (k : ℕ) {ω : JitterΩ} (hω : ω ∈ stageGood θ X₀ k) :
    ENNReal.ofReal (min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C) ≤
      (lawA θ X₀ k).indicator (fun ω => PhiC3 θ X₀ k a b (ω, valF θ X₀ k ω)) ω := by
  have h := X2_le_PhiC2 hc a b C k hω
  have e : (fun ω => PhiC2 θ X₀ k a b (ω, valF θ X₀ k ω)) =
      fun ω => PhiC3 θ X₀ k a b (ω, valF θ X₀ k ω) := funext fun ω => PhiC2_eq_PhiC3 hc k a b ω
  rwa [e] at h

lemma boxMean_PhiC3_ne_top (hev : Even X₀) {a b : ℝ} (hab : a ≤ b) (k : ℕ) (ω : JitterΩ) :
    boxMean (constructionLaw hc hev) k (PhiC3 θ X₀ k a b) ω ≠ ∞ := by
  refine ne_top_of_le_ne_top (boxMean_PhiC2_ne_top hc hev hab k ω) ?_
  unfold boxMean
  by_cases hA : ω ∈ (constructionLaw hc hev).A k
  · rw [indicator_of_mem hA, indicator_of_mem hA]
    exact mul_le_mul_right (lintegral_mono fun t => PhiC3_le_PhiC2 k a b _) _
  · rw [indicator_of_notMem hA, indicator_of_notMem hA]

end Meas3

/-! ### `∫ Φ̄⁽³⁾` by the volumes of the cofactor windows -/

variable (θ X₀) in
/-- The window `{t ≥ X₀⁻ : m(e) 2t-smooth, α ≤ m t^c < β}`. -/
def I3 (ω : JitterΩ) (α β : ℝ) (e : PIdx X₀ →₀ ℕ) (c : ℕ) : Set ℝ :=
  {t | Xm X₀ ≤ t ∧ Sm2 θ X₀ ω e t ∧ α ≤ eval (DD θ X₀ ω) e * t ^ c ∧
    eval (DD θ X₀ ω) e * t ^ c < β}

lemma measurableSet_I3 (ω : JitterΩ) (α β : ℝ) (e : PIdx X₀ →₀ ℕ) (c : ℕ) :
    MeasurableSet (I3 θ X₀ ω α β e c) := by
  have hm : Measurable fun t : ℝ => eval (DD θ X₀ ω) e * t ^ c :=
    measurable_const.mul (measurable_id.pow_const _)
  exact (measurableSet_le measurable_const measurable_id).inter ((measurableSet_Sm2 ω e).inter
    ((measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)))

section Bar3

variable (hc : Cond θ X₀)
include hc

/-- **`∫ Φ̄⁽³⁾(ω, t) dt ≤ ∑_m ∑_{c ≥ 2} B(m, c)`** for any bounds `vol(I3 m c) ≤ B(m, c)`. -/
theorem lintegral_PhiBar3_le {α β : ℝ} (ω : JitterΩ) (B : (PIdx X₀ →₀ ℕ) → ℕ → ℝ)
    (hB0 : ∀ e ∈ (cof2_finite hc β ω).toFinset, ∀ c, 0 ≤ B e c)
    (hB : ∀ e ∈ (cof2_finite hc β ω).toFinset, ∀ c, 2 ≤ c →
      volume (I3 θ X₀ ω α β e c) ≤ ENNReal.ofReal (B e c)) :
    ∫⁻ t, PhiBar3 θ X₀ α β (ω, t) ≤ ENNReal.ofReal
      (∑ e ∈ (cof2_finite hc β ω).toFinset, ∑ j ∈ Finset.range ⌈β⌉₊, B e (j + 2)) := by
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
  set T := G ×ˢ ((Finset.range K).image (· + 2)) with hT
  have hpt : ∀ t, PhiBar3 θ X₀ α β (ω, t) ≤
      ∑ e ∈ G, ∑ j ∈ Finset.range K, (I3 θ X₀ ω α β e (j + 2)).indicator 1 t := by
    intro t
    unfold PhiBar3
    split_ifs with ht
    swap; · exact zero_le
    rw [tsum_eq_sum (s := T) (fun ec hec => by
      refine if_neg fun h1 => hec ?_
      obtain ⟨hc2, hlive, -, hα, hβ⟩ := h1
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
      · have h2 : ((2 : ℕ) : ℝ) ^ ec.2 ≤ Xm X₀ ^ ec.2 :=
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
        Sm2 θ X₀ (ω, t).1 (e, j + 2).1 (ω, t).2 ∧
        α ≤ eval (DD θ X₀ (ω, t).1) (e, j + 2).1 * (ω, t).2 ^ (e, j + 2).2 ∧
        eval (DD θ X₀ (ω, t).1) (e, j + 2).1 * (ω, t).2 ^ (e, j + 2).2 < β
    · rw [if_pos h1, indicator_of_mem
        (show t ∈ I3 θ X₀ ω α β e (j + 2) from ⟨ht, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩)]
      rfl
    · rw [if_neg h1]; exact zero_le
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_finset_sum _ (fun e _ => Finset.measurable_sum _ fun j _ =>
    measurable_one.indicator (measurableSet_I3 ω α β e (j + 2)))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun e he => Finset.sum_nonneg fun j _ => hB0 e he _)]
  refine Finset.sum_le_sum fun e he => ?_
  rw [lintegral_finset_sum _ (fun j _ => measurable_one.indicator
      (measurableSet_I3 ω α β e (j + 2))),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hB0 e he _)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [lintegral_indicator_one (measurableSet_I3 ω α β e (j + 2))]
  exact hB e he (j + 2) (by omega)

end Bar3

/-! ### The volume of a cofactor window in a dyadic block -/

variable (X₀) in
/-- `s_Y = max(log X₀⁻, log(v/(8Y))/c)`: `t ≥ e^{s_Y}` on the windows of the block `(Y, 2Y]`. -/
noncomputable def sY (v Y : ℝ) (c : ℕ) : ℝ :=
  max (Real.log (Xm X₀)) (Real.log (v / (8 * Y)) / c)

/-- `z = 2(2v/Y)^{1/c}`: the smoothness bound of the cofactors of the block `(Y, 2Y]`. -/
noncomputable def zY (v Y : ℝ) (c : ℕ) : ℝ := 2 * (2 * v / Y) ^ (1 / (c : ℝ))

open Classical in
variable (θ X₀) in
/-- The bound for the window of the cofactor `e` in the block `(Y, 2Y]`. -/
noncomputable def blk (ω : JitterΩ) (v α β : ℝ) (e : PIdx X₀ →₀ ℕ) (Y : ℝ) (c : ℕ) : ℝ :=
  if Y < 2 * v / Xm X₀ ^ c ∧ ∀ i ∈ e.support, pval (DD θ X₀ ω) i ≤ zY v Y c then
    (β - α) / (c * eval (DD θ X₀ ω) e * Real.exp ((c - 1 : ℝ) * sY X₀ v Y c)) else 0

section Vol3

variable (hc : Cond θ X₀)
include hc

lemma blk_nonneg (ω : JitterΩ) {v α β : ℝ} (hαβ : α ≤ β) {e : PIdx X₀ →₀ ℕ}
    (he : 1 ≤ eval (DD θ X₀ ω) e) (Y : ℝ) (c : ℕ) : 0 ≤ blk θ X₀ ω v α β e Y c := by
  unfold blk
  split_ifs
  · have : 0 ≤ β - α := by linarith
    positivity
  · exact le_rfl

/-- **The volume of a cofactor window**: for `m(e) ∈ (Y, 2Y]`, `c ≥ 2`, `v/4 ≤ α ≤ β ≤ 2v`,
`vol(I3 e c) ≤ blk e Y c`. -/
theorem vol_I3_le (ω : JitterΩ) {v α β : ℝ} (hv : 0 < v) (hα : v / 4 ≤ α) (hβ : β ≤ 2 * v)
    (hαβ : α ≤ β) {e : PIdx X₀ →₀ ℕ} (he : 1 ≤ eval (DD θ X₀ ω) e) {Y : ℝ} (hY0 : 0 < Y)
    (hY1 : Y < eval (DD θ X₀ ω) e) (hY2 : eval (DD θ X₀ ω) e ≤ 2 * Y) {c : ℕ} (hc2 : 2 ≤ c) :
    volume (I3 θ X₀ ω α β e c) ≤ ENNReal.ofReal (blk θ X₀ ω v α β e Y c) := by
  classical
  have hXm := Queue6.Xm_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  set m := eval (DD θ X₀ ω) e with hm
  have hm0 : 0 < m := by linarith
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  by_cases hcond : Y < 2 * v / Xm X₀ ^ c ∧ ∀ i ∈ e.support, pval (DD θ X₀ ω) i ≤ zY v Y c
  · unfold blk
    rw [if_pos hcond]
    set X := Real.exp (sY X₀ v Y c) with hX
    have hsub : I3 θ X₀ ω α β e c ⊆ {t : ℝ | X ≤ t ∧ α ≤ m * t ^ c ∧ m * t ^ c < β} := by
      rintro t ⟨ht, -, h1, h2⟩
      refine ⟨?_, h1, h2⟩
      have ht0 : 0 < t := lt_of_lt_of_le hXm0 ht
      rw [hX, ← Real.exp_log ht0]
      refine Real.exp_le_exp.mpr (max_le (Real.log_le_log hXm0 ht) ?_)
      rw [div_le_iff₀ hc0]
      have h8 : v / (8 * Y) ≤ t ^ c := by
        rw [div_le_iff₀ (by positivity)]
        have : v / 4 ≤ m * t ^ c := hα.trans h1
        have htc : 0 ≤ t ^ c := by positivity
        nlinarith
      have := Real.log_le_log (by positivity) h8
      rw [Real.log_pow] at this
      linarith
    refine (measure_mono hsub).trans ((volume_pow_window_le (Real.exp_pos _) hm0
      (show 1 ≤ c by omega) hαβ).trans (le_of_eq ?_))
    congr 1
    rw [← Real.exp_nat_mul]
    congr 3
    push_cast [Nat.cast_sub (show 1 ≤ c by omega)]
    ring
  · have hempty : I3 θ X₀ ω α β e c = ∅ := by
      ext t
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨ht, hsm, h1, h2⟩
      apply hcond
      have ht0 : 0 < t := lt_of_lt_of_le hXm0 ht
      have hmt : m * t ^ c < 2 * v := lt_of_lt_of_le h2 hβ
      refine ⟨?_, fun i hi => (hsm i hi).trans ?_⟩
      · rw [lt_div_iff₀ (by positivity)]
        have : Xm X₀ ^ c ≤ t ^ c := pow_le_pow_left₀ hXm0.le ht c
        have h0 : 0 < Xm X₀ ^ c := by positivity
        nlinarith
      · unfold zY
        have htc : t ^ c ≤ 2 * v / Y := by
          rw [le_div_iff₀ hY0]
          have : 0 ≤ t ^ c := by positivity
          nlinarith
        have := Real.rpow_le_rpow (by positivity) htc (show (0 : ℝ) ≤ 1 / (c : ℝ) by positivity)
        rw [one_div, Real.pow_rpow_inv_natCast ht0.le (by omega)] at this
        rw [one_div]
        linarith
    rw [hempty, measure_empty]; exact zero_le

end Vol3

/-! ### The dyadic block of a cofactor -/

lemma block_of_ceil {m : ℝ} (hm : 1 ≤ m) :
    (2 : ℝ) ^ ⌈Real.logb 2 m⌉₊ / 2 < m ∧ m ≤ 2 * ((2 : ℝ) ^ ⌈Real.logb 2 m⌉₊ / 2) := by
  have hm0 : 0 < m := by linarith
  refine ⟨?_, by have := two_pow_ceil_logb hm0; linarith⟩
  have hl : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) hm
  have h1 : (⌈Real.logb 2 m⌉₊ : ℝ) < Real.logb 2 m + 1 := Nat.ceil_lt_add_one hl
  have h3 : (2 : ℝ) ^ ((⌈Real.logb 2 m⌉₊ : ℕ) : ℝ) < 2 ^ (Real.logb 2 m + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num)
    (by norm_num) hm0, Real.rpow_one] at h3
  linarith

/-- `∑_{j < K} r^j/(j+2) ≤ 1/2 + 2r` for `0 < r ≤ 1/2`. -/
lemma sum_pow_div_le' {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) (K : ℕ) :
    ∑ j ∈ Finset.range K, r ^ j / ((j : ℝ) + 2) ≤ 1 / 2 + 2 * r := by
  have h := sum_pow_div_le hr0.le hr K
  have e : ∑ j ∈ Finset.range K, r ^ (j + 1) / ((j : ℝ) + 2) =
      r * ∑ j ∈ Finset.range K, r ^ j / ((j : ℝ) + 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]; ring
  rw [e] at h
  have : r * ∑ j ∈ Finset.range K, r ^ j / ((j : ℝ) + 2) ≤ r * (1 / 2 + 2 * r) := by
    linarith
  exact le_of_mul_le_mul_left this hr0


/-- The number of dyadic blocks: `⌈log₂(b/X₀⁻²)⌉ ≤ (log v + 0.7)/0.69 + 1` for `0 < b ≤ 2v`,
`1 ≤ v`. -/
lemma ceil_logb_le (hc : Cond θ X₀) {b v : ℝ} (hb : 0 < b) (hb2 : b ≤ 2 * v) (hv1 : 1 ≤ v) :
    (⌈Real.logb 2 (b / Xm X₀ ^ 2)⌉₊ : ℝ) ≤ (Real.log v + 0.7) / 0.69 + 1 := by
  have hXm := Queue6.Xm_pos hc
  have hl2 : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL0 : 0 ≤ Real.log v := Real.log_nonneg hv1
  set J'' := ⌈Real.logb 2 (b / Xm X₀ ^ 2)⌉₊
  by_cases hJ0 : J'' = 0
  · rw [hJ0]; push_cast
    have : 0 ≤ (Real.log v + 0.7) / 0.69 := by positivity
    linarith
  · have hl : 0 < Real.logb 2 (b / Xm X₀ ^ 2) := by
      by_contra h; push_neg at h; exact hJ0 (Nat.ceil_eq_zero.mpr h)
    have h1 : (J'' : ℝ) < Real.logb 2 (b / Xm X₀ ^ 2) + 1 := Nat.ceil_lt_add_one hl.le
    have h2 : Real.logb 2 (b / Xm X₀ ^ 2) ≤ (Real.log v + 0.7) / 0.69 := by
      unfold Real.logb
      have hy0 : 0 < b / Xm X₀ ^ 2 := div_pos hb (by positivity)
      have h3 : Real.log (b / Xm X₀ ^ 2) ≤ Real.log v + 0.7 := by
        have h4 : b / Xm X₀ ^ 2 ≤ 2 * v := by
          refine le_trans ?_ hb2
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ Xm X₀ ^ 2 := by nlinarith
          nlinarith
        have h5 := Real.log_le_log hy0 h4
        rw [Real.log_mul (by norm_num) (by linarith)] at h5
        have := Real.log_two_lt_d9
        linarith
      have h6 : 0 < Real.log (b / Xm X₀ ^ 2) := by
        have := Real.logb_pos_iff (b := 2) (by norm_num) hy0 |>.mp hl
        exact Real.log_pos this
      calc Real.log (b / Xm X₀ ^ 2) / Real.log 2
          ≤ Real.log (b / Xm X₀ ^ 2) / 0.69 :=
            div_le_div_of_nonneg_left h6.le (by norm_num) hl2
        _ ≤ (Real.log v + 0.7) / 0.69 := div_le_div_of_nonneg_right h3 (by norm_num)
    linarith

/-! ### The second bound of (s2) -/

variable (X₀) in
/-- **The block bound** (04d-noise.tex, "Second bound, for `σ > log X₀⁻`", both cases
`u' ≤ log z` and `u' > log z`, from Lemma 5.3 (smooth-v, 04a-setup.tex) and
`ρ(u) e^{a} ≤ 2 e^{-0.7 u log u}`): for a Beurling system with (H_BS) on `[1, Z]`,
`4v/X₀⁻² ≤ Z`, `log X₀⁻ < σ(v) = ½√(L log L)`, `c ≥ 2` and a block `(Y, 2Y]` with
`1/2 ≤ Y < 2v/X₀⁻^c`: `e^{-(c-1)s_Y} v(log Y, z) ≤ 3 e^{-σ} X₀⁻^{-(c-2)/2}`. -/
def BlockBound : Prop :=
  ∀ (P : BeurlingSystem) (Z : ℝ), P.HBS (Xm X₀) Z (1 / 1000) (1 / 1000) (hbsEps X₀) →
    10 ^ 8 - 1 ≤ Real.log (Xm X₀) → ∀ v : ℝ, Xm X₀ ≤ v →
    Real.log (Xm X₀) < Real.sqrt (Real.log v * Real.log (Real.log v)) / 2 →
    4 * v / Xm X₀ ^ 2 ≤ Z → ∀ c : ℕ, 2 ≤ c → ∀ Y : ℝ, 1 / 2 ≤ Y → Y < 2 * v / Xm X₀ ^ c →
      Real.exp (-((c - 1 : ℝ) * sY X₀ v Y c)) * P.vSmooth Y (zY v Y c) ≤
        3 * Real.exp (-(Real.sqrt (Real.log v * Real.log (Real.log v)) / 2)) *
          Xm X₀ ^ (-((c - 2 : ℝ) / 2))

section Second

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **The second bound of (s2)** (04d-noise.tex, "Second bound, for `σ > log X₀⁻`"), from the
block bound. -/
theorem s2_second_of_block (hBB : BlockBound X₀) : S2SecondBranch θ X₀ := by
  intro C hC0 a b v hv hb0 hab hva hb2 hσ
  classical
  set J := constructionLaw hc hev with hJ
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hk : ∀ k, jitterMeasure[fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C |
      jitterFiltration k] ≤ᵐ[jitterMeasure]
      fun ω => min C (boxMean J k (PhiC3 θ X₀ k a b) ω).toReal := by
    intro k
    have hf0 : ∀ ω, 0 ≤ min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C := fun ω =>
      le_min (Nat.cast_nonneg _) hC0
    have hfC : ∀ ω, min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C ≤ C := fun ω => min_le_right _ _
    have hfm : Measurable fun ω => min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C :=
      (((x2count_adapted hc a b k).min measurable_const).mono (jitterFiltration.le _) le_rfl)
    have hfΦ : ∀ᵐ ω ∂jitterMeasure, ENNReal.ofReal (min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C) ≤
        (J.A k).indicator (fun ω => PhiC3 θ X₀ k a b (ω, J.q k ω)) ω := by
      filter_upwards [ae_stageGood hc] with ω hω
      exact X2_le_PhiC3 hc a b C k (hω k)
    exact condExp_le_boxMean J k hC0 hf0 hfC hfm
      (fun S hS => PhiC3_jmeas hc k a b S hS) hfΦ
      (fun ω => boxMean_PhiC3_ne_top hc hev hab' k ω)
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  filter_upwards [ae_all_iff.mpr hk, hnice] with ω hω hN hQC hE1 n
  clear hk hnice
  have hU := hN.1
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
  have hok := limModel_realisedOK h0
  have hDD : DD θ X₀ ω = DM h0.limModel ω := by
    show DM (Mcl θ X₀ ω) (Ucl ω) = _
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  -- the parameters
  have hXm := Queue6.Xm_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  have hXmh := Xm_half hc
  have hXb := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_ge_one hX0 hc.hX (le_refl (X₀ : ℝ)); unfold Xm; linarith
  have hv0 : 0 < v := by linarith
  set ℓ := Real.log (Xm X₀) with hℓdef
  set L := Real.log v with hLdef
  set σ := Real.sqrt (L * Real.log L) / 2 with hσdef
  have hℓ : 10 ^ 8 - 1 ≤ ℓ := by
    have h1 : Real.log ((X₀ : ℝ) / 2) ≤ ℓ := Real.log_le_log (by linarith) hXmh
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have := Real.log_two_lt_d9
    linarith [hc.hX]
  have hL : 10 ^ 8 ≤ L := hc.hX.trans (Real.log_le_log (by linarith) hv)
  have hL4 : 4 * ℓ ≤ L := by
    by_contra h
    push_neg at h
    have hlogL : Real.log L ≤ Real.log (4 * ℓ) := Real.log_le_log (by linarith) h.le
    have hl4 : Real.log (4 * ℓ) ≤ 4 * ℓ / 100 + 98 := log_le_lin hc (by linarith)
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have hLl : L * Real.log L ≤ 4 * ℓ * (4 * ℓ / 100 + 98) :=
      mul_le_mul h.le (hlogL.trans hl4) hlogL0 (by linarith)
    have h2 : 2 * ℓ < Real.sqrt (L * Real.log L) := by linarith
    have h3 : (2 * ℓ) ^ 2 < L * Real.log L := (Real.lt_sqrt (by linarith)).mp h2
    nlinarith
  have hvXm4 : Xm X₀ ^ 4 ≤ v := by
    have : Real.log (Xm X₀ ^ 4) ≤ Real.log v := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff (by positivity) hv0).mp this
  have hXm2big : (10 : ℝ) ^ 6 ≤ Xm X₀ := by
    have := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log (by linarith)] at this
    linarith [hc.hX]
  set Z := 4 * v / Xm X₀ ^ 2 with hZdef
  have hZX : (X₀ : ℝ) ≤ Z := by
    rw [hZdef, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hXm0 2, pow_pos hXm0 3]
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  have hab'' : (a : ℝ) < b := by exact_mod_cast hab
  have hbt : ((b.toNat : ℕ) : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb0.le
  have hZt : 4 * Z + 2 ≤ (b.toNat : ℝ) := by
    rw [hbt]
    have hZ : Z ≤ v / 1000 := by
      rw [hZdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h2 : (4000 : ℝ) ≤ Xm X₀ ^ 2 := by nlinarith
      nlinarith
    have : (1000 : ℝ) ≤ v := by nlinarith [pow_pos hXm0 2, pow_pos hXm0 3]
    have : (a : ℝ) < b := hab''
    linarith
  have hH := hbs_QE hc hev hQC hE1 hN h0 hZX hZt
  set P := realisedSystem h0.limModel (capH X₀) ω with hP
  -- the sum over the cofactors
  set G := (cof2_finite hc (b : ℝ) ω).toFinset with hG
  set K := ⌈(b : ℝ)⌉₊ with hK
  have hGm : ∀ e ∈ G, Live (DD θ X₀ ω) e ∧ eval (DD θ X₀ ω) e ≤ b / Xm X₀ ^ 2 := by
    intro e he; rw [hG, Set.Finite.mem_toFinset] at he; exact he
  have hG1 : ∀ e ∈ G, 1 ≤ eval (DD θ X₀ ω) e := fun e he => one_le_evalD hc (hGm e he).1
  set g : (PIdx X₀ →₀ ℕ) → ℕ := fun e => ⌈Real.logb 2 (eval (DD θ X₀ ω) e)⌉₊ with hg
  set Bf : (PIdx X₀ →₀ ℕ) → ℕ → ℝ := fun e c =>
    blk θ X₀ ω v a b e ((2 : ℝ) ^ g e / 2) c with hBf
  have hB0 : ∀ e ∈ G, ∀ c, 0 ≤ Bf e c := fun e he c => blk_nonneg hc ω hab' (hG1 e he) _ c
  have hBv : ∀ e ∈ G, ∀ c, 2 ≤ c →
      volume (I3 θ X₀ ω a b e c) ≤ ENNReal.ofReal (Bf e c) := by
    intro e he c hc2
    obtain ⟨hb1, hb2'⟩ := block_of_ceil (hG1 e he)
    exact vol_I3_le hc ω hv0 hva hb2 hab' (hG1 e he) (by positivity) hb1 hb2' hc2
  set S := ∑ e ∈ G, ∑ j ∈ Finset.range K, Bf e (j + 2) with hS
  have hint := lintegral_PhiBar3_le hc ω Bf hB0 hBv
  rw [← hG, ← hK, ← hS] at hint
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e he => Finset.sum_nonneg fun j _ => hB0 e he _
  have hfin : ∀ k, boxMean J k (PhiC3 θ X₀ k a b) ω ≠ ∞ := fun k =>
    boxMean_PhiC3_ne_top hc hev hab' k ω
  have hsum : ∑' k, boxMean J k (PhiC3 θ X₀ k a b) ω ≤ 2 * ENNReal.ofReal S :=
    (sum_boxMean_le J (fun k => PhiC3 θ X₀ k a b) (PhiBar3 θ X₀ a b) ω (PhiBar3_meas a b ω)
      (fun k t => PhiC3_le_PhiBar3 k a b _)).trans (mul_le_mul_right hint 2)
  have hcomp : ∑ k ∈ Finset.range n, (jitterMeasure[fun ω =>
      min (X2count (CM θ X₀ ω) (Ucl ω) a b k) C | jitterFiltration k]) ω ≤ 2 * S := by
    refine (Finset.sum_le_sum fun k _ => (hω k).trans (min_le_right _ _)).trans ?_
    rw [← ENNReal.toReal_sum fun k _ => hfin k]
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal S = ENNReal.ofReal (2 * S) := by
      rw [ENNReal.ofReal_mul (p := 2) (by norm_num)]; norm_num
    calc (∑ k ∈ Finset.range n, boxMean J k (PhiC3 θ X₀ k a b) ω).toReal
        ≤ (ENNReal.ofReal (2 * S)).toReal := by
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          rw [← h2]
          exact (ENNReal.sum_le_tsum _).trans hsum
      _ = 2 * S := ENNReal.toReal_ofReal (by positivity)
  clear hω hsum hint hfin
  -- the blocks
  set J' := ⌈Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2)⌉₊ + 1 with hJ'
  have hmaps : ∀ e ∈ G, g e ∈ Finset.range J' := by
    intro e he
    rw [Finset.mem_range, hJ']
    have h1 : g e ≤ ⌈Real.logb 2 ((b : ℝ) / Xm X₀ ^ 2)⌉₊ :=
      Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) (by linarith [hG1 e he])
        (hGm e he).2)
    omega
  set E := Real.exp (-σ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hW0 : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hblock : ∀ c, 2 ≤ c → ∑ e ∈ G, Bf e c ≤
      J' * (((b : ℝ) - a) / c * (3 * E * Xm X₀ ^ (-((c - 2 : ℝ) / 2)))) := by
    intro c hc2
    have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
    have hR0 : 0 ≤ ((b : ℝ) - a) / c * (3 * E * Xm X₀ ^ (-((c - 2 : ℝ) / 2))) := by
      have := Real.rpow_nonneg hXm0.le (-((c - 2 : ℝ) / 2))
      positivity
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine (Finset.sum_le_sum fun i _ => ?_).trans (le_of_eq (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
    set Y : ℝ := (2 : ℝ) ^ i / 2 with hY
    have hY12 : 1 / 2 ≤ Y := by
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      linarith
    have hfib : ∑ e ∈ G with g e = i, Bf e c = ∑ e ∈ G with g e = i, blk θ X₀ ω v a b e Y c :=
      Finset.sum_congr rfl fun e he => by
        show blk θ X₀ ω v a b e ((2 : ℝ) ^ g e / 2) c = _
        rw [(Finset.mem_filter.mp he).2]
    rw [hfib]
    by_cases hYc : Y < 2 * v / Xm X₀ ^ c
    swap
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun e _ => ?_)) hR0
      unfold blk; rw [if_neg fun h => hYc h.1]
    set F := (G.filter fun e => g e = i).filter
      fun e => ∀ j ∈ e.support, pval (DD θ X₀ ω) j ≤ zY v Y c with hF
    set Eb := Real.exp ((c - 1 : ℝ) * sY X₀ v Y c) with hEb
    have hEb0 : 0 < Eb := Real.exp_pos _
    have h1 : ∑ e ∈ G with g e = i, blk θ X₀ ω v a b e Y c =
        ((b : ℝ) - a) / (c * Eb) * ∑ e ∈ F, 1 / eval (DD θ X₀ ω) e := by
      have hterm : ∀ e ∈ G.filter (fun e => g e = i), blk θ X₀ ω v a b e Y c =
          ((b : ℝ) - a) / (c * Eb) * (if ∀ j ∈ e.support, pval (DD θ X₀ ω) j ≤ zY v Y c
            then 1 / eval (DD θ X₀ ω) e else 0) := by
        intro e he
        have hm1 := hG1 e (Finset.mem_filter.mp he).1
        unfold blk
        by_cases hsm : ∀ j ∈ e.support, pval (DD θ X₀ ω) j ≤ zY v Y c
        · rw [if_pos ⟨hYc, hsm⟩, if_pos hsm]
          field_simp
          rw [hEb]
        · rw [if_neg fun h => hsm h.2, if_neg hsm, mul_zero]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hF,
        Finset.sum_filter (s := G.filter fun e => g e = i)]
    have h2 : ∑ e ∈ F, 1 / eval (DD θ X₀ ω) e ≤ P.vSmooth Y (zY v Y c) := by
      rw [hDD]
      refine sum_le_vSmooth hok F fun e he => ?_
      rw [hF, Finset.mem_filter, Finset.mem_filter] at he
      obtain ⟨⟨heG, hgi⟩, hsm⟩ := he
      obtain ⟨hb1, hb2'⟩ := block_of_ceil (hG1 e heG)
      have hgi' : ⌈Real.logb 2 (eval (DD θ X₀ ω) e)⌉₊ = i := hgi
      rw [hgi'] at hb1 hb2'
      rw [← hDD]
      exact ⟨(hGm e heG).1, hb1, hb2', hsm⟩
    have h3 := hBB P Z hH hℓ v (hXmX.trans hv) hσ le_rfl c hc2 Y hY12 hYc
    rw [h1]
    have hW' : 0 ≤ ((b : ℝ) - a) / c := div_nonneg hW0 hc0.le
    calc ((b : ℝ) - a) / (c * Eb) * ∑ e ∈ F, 1 / eval (DD θ X₀ ω) e
        ≤ ((b : ℝ) - a) / (c * Eb) * P.vSmooth Y (zY v Y c) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((b : ℝ) - a) / c *
          (Real.exp (-((c - 1 : ℝ) * sY X₀ v Y c)) * P.vSmooth Y (zY v Y c)) := by
          rw [Real.exp_neg, ← hEb]; field_simp
      _ ≤ ((b : ℝ) - a) / c * (3 * E * Xm X₀ ^ (-((c - 2 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left h3 hW'
  -- `r = X₀⁻^{-1/2}`
  set r := Xm X₀ ^ (-(1 / 2 : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hXm0 _
  have hr2 : r ^ 2 = (Xm X₀)⁻¹ := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hXm0.le]
    norm_num [Real.rpow_neg_one]
  have hrs : r ≤ 1 / 1000 := by
    have : (Xm X₀)⁻¹ ≤ 1 / 10 ^ 6 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hXm2big
    have h2 : r ^ 2 ≤ (1 / 1000) ^ 2 := by
      rw [hr2]; exact this.trans (by norm_num)
    exact (pow_le_pow_iff_left₀ hr0.le (by norm_num) (by norm_num)).mp h2
  have hrj : ∀ j : ℕ, Xm X₀ ^ (-((((j + 2 : ℕ) : ℝ) - 2) / 2)) = r ^ j := by
    intro j
    rw [show -((((j + 2 : ℕ) : ℝ) - 2) / 2) = (-(1 / 2 : ℝ)) * j by push_cast; ring,
      Real.rpow_mul hXm0.le, Real.rpow_natCast]
  have hSb : S ≤ J' * (((b : ℝ) - a) * (3 * E)) * (1 / 2 + 2 * r) := by
    rw [hS, Finset.sum_comm]
    calc ∑ j ∈ Finset.range K, ∑ e ∈ G, Bf e (j + 2)
        ≤ ∑ j ∈ Finset.range K, (J' * (((b : ℝ) - a) / ((j + 2 : ℕ) : ℝ) *
            (3 * E * Xm X₀ ^ (-((((j + 2 : ℕ) : ℝ) - 2) / 2))))) :=
          Finset.sum_le_sum fun j _ => hblock (j + 2) (by omega)
      _ = J' * (((b : ℝ) - a) * (3 * E)) * ∑ j ∈ Finset.range K, r ^ j / ((j : ℝ) + 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hrj]; push_cast; ring
      _ ≤ J' * (((b : ℝ) - a) * (3 * E)) * (1 / 2 + 2 * r) :=
          mul_le_mul_of_nonneg_left (sum_pow_div_le' hr0 (by linarith) K) (by positivity)
  -- the number of blocks
  have hl2 : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hJ'' : (J' : ℝ) ≤ (L + 0.7) / 0.69 + 2 := by
    rw [hJ', Nat.cast_add, Nat.cast_one]
    have := ceil_logb_le hc hb hb2 (hX1.le.trans hv)
    rw [← hLdef] at this
    linarith
  -- numerics
  have hs2 : s2E3 X₀ v = 9 * L * E := by
    unfold s2E3
    rw [max_eq_right hσ.le]
  rw [hs2]
  have hJ0 : (0 : ℝ) ≤ J' := Nat.cast_nonneg _
  have hfin' : 2 * ((J' : ℝ) * (3 * (1 / 2 + 2 * r))) ≤ 9 * L := by
    have h1 : (J' : ℝ) * (3 * (1 / 2 + 2 * r)) ≤
        ((L + 0.7) / 0.69 + 2) * (3 * (1 / 2 + 2 / 1000)) :=
      mul_le_mul hJ'' (by linarith) (by positivity) (by positivity)
    have e69 : (L + 0.7) / 0.69 = (L + 0.7) * (100 / 69) := by ring
    rw [e69] at h1
    nlinarith
  calc _ ≤ 2 * S := hcomp
    _ ≤ 2 * (J' * (((b : ℝ) - a) * (3 * E)) * (1 / 2 + 2 * r)) := by linarith
    _ = (2 * ((J' : ℝ) * (3 * (1 / 2 + 2 * r)))) * E * ((b : ℝ) - a) := by ring
    _ ≤ 9 * L * E * ((b : ℝ) - a) := by
        refine mul_le_mul_of_nonneg_right ?_ hW0
        exact mul_le_mul_of_nonneg_right hfin' hE0.le

end Second

end BModel
