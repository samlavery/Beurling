module

public import RequestProject.Beurling.RankFull.Volume

/-!
# Lemma A.5 (Pivot-Integration Lemma): the probabilistic core, over an abstract filtration

## The abstract jitter law (`JitterLaw`)

An abstract process on a measure space `(Ω, P)` with a filtration `F n` (`F n` = the information
before the decision at slot `n`, the paper's `𝓕_{s-}`), and for each slot `n`:
* the event `A n ∈ F n` that a prime is decided at slot `n` (standing fact (F2): "whether a prime
  is decided at slot `s` … is `𝓕_{s-}`-measurable");
* its position `q n`, `F (n+1)`-measurable;
* the box centre `c n` and width `H n > 0`, `F n`-measurable;
* **(F2), the conditional law**: given `F n`, on `A n`, `q n` has density `≤ 1/H n` on the box
  `W n = [c n - H n/2, c n + H n/2)` (`dens`, stated in integrated form: for every
  `F n ⊗ Borel`-measurable `Φ ≥ 0`, `E[1_{A n} Φ(·, q n)] ≤ E[1_{A n} H_n⁻¹ ∫_{W n} Φ(·, t) dt]`);
* **(F1), the slot count**: `∑_n 1_{A n} 1_{W n}(t)/H n ≤ θ` for every `ω` and `t` (`slots`).

No independence between slots is assumed.

## Results

* `RankFull.JitterLaw.pivot_step` : **the pivot step** of the proof of Lemma A.5 (density + label
  sum): for adapted integrands `Φ n` (`F n ⊗ Borel`-measurable) dominated by a measurable `Φ̄`,
  `E[∑_n 1_{A n} Φ n(·, q n)] ≤ θ E[∫ Φ̄(·, t) dt]`.
* `RankFull.JitterLaw.iterated_pivots` : **Lemma A.5 for one run** (all free data decided before
  the earliest pivot, no late blocks: the case `T = 1`): for `k` pivots at slots
  `N > n₁ > n₂ > ⋯ > n_k` (latest first, labels summed), with an integrand `Ψ m` depending on the
  past of the earliest pivot `m = n_k` (`F m ⊗ Borel`-measurable) and dominated by a measurable
  `Ψ̄`, `E[∑_{labels} ∏_i 1_{A n_i} Ψ_{n_k}(·, q_{n_1}, …, q_{n_k})] ≤ θ^k E[∫_{ℝ^k} Ψ̄]`.
* `RankFull.JitterLaw.pil_volume` : combined with the Volume Lemma (Lemma A.2): for fixed
  cofactors `c_i > 0`, an invertible pattern `E_P` and the caps `q_j ≥ Xm ≥ 1`, the expected
  number of labelled pivot `k`-tuples with all `n_i = c_i ∏_j q_j^{E_ij} ∈ J` is at most
  `θ^k vol(J)^k/(|det E_P| ∏ c_i Xm^{M-k})`.

What is **not** formalized here is the multi-run recursion of Lemma A.5 (the label replacement
`s_t ↦ u_t` of step (i) and the interleaved block bounds (iii)); its deterministic pieces are
`block_bound`, `end_step` (`BlockBound.lean`). Each pivot step of that recursion is an instance of
`pivot_step`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace RankFull

/-- Joint measurability of `f : Ω × β → ℝ≥0∞` for the σ-algebra `m ⊗ Borel`. -/
def JMeas {Ω β : Type*} (m : MeasurableSpace Ω) [MeasurableSpace β] (f : Ω × β → ℝ≥0∞) : Prop :=
  @Measurable (Ω × β) ℝ≥0∞ (@Prod.instMeasurableSpace Ω β m _) _ f

lemma JMeas.mono {Ω β : Type*} {m m' : MeasurableSpace Ω} [MeasurableSpace β]
    {f : Ω × β → ℝ≥0∞} (hf : JMeas m f) (h : m ≤ m') : JMeas m' f := by
  unfold JMeas at *
  refine @Measurable.mono _ _ (@Prod.instMeasurableSpace Ω β m _) _ _ _ f hf ?_ le_rfl
  exact sup_le_sup_right (MeasurableSpace.comap_mono h) _

/-- The box `W = [c - H/2, c + H/2)`. -/
def box (c H : ℝ) : Set ℝ := Ico (c - H / 2) (c + H / 2)

/-- **The abstract jitter law**: standing facts (F1) and (F2) of Section 6.1. -/
structure JitterLaw (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (θ : ℝ≥0∞) where
  F : ℕ → MeasurableSpace Ω
  F_mono : Monotone F
  F_le : ∀ n, F n ≤ mΩ
  A : ℕ → Set Ω
  q : ℕ → Ω → ℝ
  c : ℕ → Ω → ℝ
  H : ℕ → Ω → ℝ
  A_meas : ∀ n, MeasurableSet[F n] (A n)
  q_meas : ∀ n, Measurable[F (n + 1)] (q n)
  c_meas : ∀ n, Measurable[F n] (c n)
  H_meas : ∀ n, Measurable[F n] (H n)
  H_pos : ∀ n ω, 0 < H n ω
  /-- (F2): the conditional density of `q n` given `F n` is `≤ 1/H n` on the box. -/
  dens : ∀ n (Φ : Ω × ℝ → ℝ≥0∞), JMeas (F n) Φ →
    ∫⁻ ω, (A n).indicator (fun ω => Φ (ω, q n ω)) ω ∂P ≤
      ∫⁻ ω, (A n).indicator (fun ω => ENNReal.ofReal (H n ω)⁻¹ *
        ∫⁻ t in box (c n ω) (H n ω), Φ (ω, t)) ω ∂P
  /-- (F1): the slot count. -/
  slots : ∀ ω t, ∑' n, (A n).indicator (fun ω => ENNReal.ofReal (H n ω)⁻¹ *
    (box (c n ω) (H n ω)).indicator 1 t) ω ≤ θ

namespace JitterLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {θ : ℝ≥0∞}
  (J : JitterLaw Ω P θ)

lemma A_meas' (n : ℕ) : MeasurableSet (J.A n) := J.F_le n _ (J.A_meas n)

lemma q_meas' (n : ℕ) : Measurable (J.q n) := (J.q_meas n).mono (J.F_le _) le_rfl

lemma c_meas' (n : ℕ) : Measurable (J.c n) := (J.c_meas n).mono (J.F_le _) le_rfl

lemma H_meas' (n : ℕ) : Measurable (J.H n) := (J.H_meas n).mono (J.F_le _) le_rfl

lemma measurableSet_box_graph (n : ℕ) :
    MeasurableSet {x : Ω × ℝ | x.2 ∈ box (J.c n x.1) (J.H n x.1)} := by
  have hc := J.c_meas' n
  have hH := J.H_meas' n
  simp only [box, mem_Ico, setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le ((hc.comp measurable_fst).sub ((hH.comp measurable_fst).div_const 2))
      measurable_snd
  · exact measurableSet_lt measurable_snd
      ((hc.comp measurable_fst).add ((hH.comp measurable_fst).div_const 2))

lemma measurable_box_ind (n : ℕ) :
    Measurable fun x : Ω × ℝ => (box (J.c n x.1) (J.H n x.1)).indicator (1 : ℝ → ℝ≥0∞) x.2 := by
  have : (fun x : Ω × ℝ => (box (J.c n x.1) (J.H n x.1)).indicator (1 : ℝ → ℝ≥0∞) x.2) =
      {x : Ω × ℝ | x.2 ∈ box (J.c n x.1) (J.H n x.1)}.indicator 1 := by
    funext x; simp [Set.indicator]
  rw [this]
  exact measurable_one.indicator (J.measurableSet_box_graph n)

/-- **The pivot step** of the proof of Lemma A.5: density (F2) and label sum (F1). -/
theorem pivot_step (Φ : ℕ → Ω × ℝ → ℝ≥0∞) (hΦ : ∀ n, JMeas (J.F n) (Φ n))
    (Φbar : Ω × ℝ → ℝ≥0∞) (hbar : Measurable Φbar) (hdom : ∀ n x, Φ n x ≤ Φbar x) :
    ∫⁻ ω, ∑' n, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω ∂P ≤
      θ * ∫⁻ ω, (∫⁻ t, Φbar (ω, t)) ∂P := by
  have hΦa : ∀ n, Measurable (Φ n) := fun n => (hΦ n).mono (J.F_le n)
  have hmeas_n : ∀ n, Measurable fun ω => (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω :=
    fun n => ((hΦa n).comp (measurable_id.prodMk (J.q_meas' n))).indicator (J.A_meas' n)
  -- the bound after (F2), in a form measurable in `ω`
  set g : ℕ → Ω → ℝ≥0∞ := fun n ω => (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
    ∫⁻ t, (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t * Φbar (ω, t)) ω with hg
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    refine Measurable.indicator ?_ (J.A_meas' n)
    refine (ENNReal.measurable_ofReal.comp ((J.H_meas' n).inv)).mul ?_
    exact ((J.measurable_box_ind n).mul hbar).lintegral_prod_right'
  have hstep : ∀ n, ∫⁻ ω, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω ∂P ≤
      ∫⁻ ω, g n ω ∂P := by
    intro n
    refine (J.dens n (Φ n) (hΦ n)).trans (lintegral_mono fun ω => ?_)
    simp only [hg]
    by_cases hω : ω ∈ J.A n
    · simp only [Set.indicator_of_mem hω]
      refine mul_le_mul_right ?_ _
      have hbox : MeasurableSet (box (J.c n ω) (J.H n ω)) := measurableSet_Ico
      calc ∫⁻ t in box (J.c n ω) (J.H n ω), Φ n (ω, t)
          ≤ ∫⁻ t in box (J.c n ω) (J.H n ω), Φbar (ω, t) := lintegral_mono fun t => hdom n _
        _ = ∫⁻ t, (box (J.c n ω) (J.H n ω)).indicator (fun t => Φbar (ω, t)) t :=
            (lintegral_indicator hbox _).symm
        _ = ∫⁻ t, (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t * Φbar (ω, t) :=
            lintegral_congr fun t => by
              by_cases ht : t ∈ box (J.c n ω) (J.H n ω) <;> simp [ht]
    · simp [Set.indicator_of_notMem hω]
  have hpt : ∀ ω, ∑' n, g n ω ≤ θ * ∫⁻ t, Φbar (ω, t) := by
    intro ω
    have hm : ∀ n, Measurable fun t => (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
        (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) := by
      intro n
      refine Measurable.mul ?_ (hbar.comp (measurable_const.prodMk measurable_id))
      by_cases hω : ω ∈ J.A n
      · simp only [Set.indicator_of_mem hω]
        exact measurable_const.mul (measurable_one.indicator measurableSet_Ico)
      · simp only [Set.indicator_of_notMem hω]; exact measurable_const
    calc ∑' n, g n ω
        = ∑' n, ∫⁻ t, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
            (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) := by
          refine tsum_congr fun n => ?_
          simp only [hg]
          by_cases hω : ω ∈ J.A n
          · simp only [Set.indicator_of_mem hω]
            rw [← lintegral_const_mul']
            · exact lintegral_congr fun t => by ring
            · exact ENNReal.ofReal_ne_top
          · simp [Set.indicator_of_notMem hω]
      _ = ∫⁻ t, ∑' n, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
            (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω * Φbar (ω, t) :=
          (lintegral_tsum fun n => (hm n).aemeasurable).symm
      _ = ∫⁻ t, (∑' n, (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
            (box (J.c n ω) (J.H n ω)).indicator (1 : ℝ → ℝ≥0∞) t) ω) * Φbar (ω, t) := by
          refine lintegral_congr fun t => ?_
          rw [ENNReal.tsum_mul_right]
      _ ≤ ∫⁻ t, θ * Φbar (ω, t) := lintegral_mono fun t => by
          gcongr; exact J.slots ω t
      _ = θ * ∫⁻ t, Φbar (ω, t) :=
          lintegral_const_mul θ (hbar.comp (measurable_const.prodMk measurable_id))
  calc ∫⁻ ω, ∑' n, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω ∂P
      = ∑' n, ∫⁻ ω, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω ∂P :=
        lintegral_tsum fun n => (hmeas_n n).aemeasurable
    _ ≤ ∑' n, ∫⁻ ω, g n ω ∂P := ENNReal.tsum_le_tsum hstep
    _ = ∫⁻ ω, ∑' n, g n ω ∂P := (lintegral_tsum fun n => (hgm n).aemeasurable).symm
    _ ≤ ∫⁻ ω, θ * (∫⁻ t, Φbar (ω, t)) ∂P := lintegral_mono hpt
    _ = θ * ∫⁻ ω, (∫⁻ t, Φbar (ω, t)) ∂P :=
        lintegral_const_mul θ hbar.lintegral_prod_right'

end JitterLaw

/-! ## `k` pivots of one run -/

lemma measurable_fin_cons {α : Type*} [MeasurableSpace α] {k : ℕ} {f : α → ℝ}
    {g : α → Fin k → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => (Fin.cons (f x) (g x) : Fin (k + 1) → ℝ) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using (measurable_pi_apply j).comp hg

/-- `∫ over ℝ^{k+1}` as an iterated integral (first coordinate outside). -/
lemma lintegral_fin_succ {k : ℕ} (f : (Fin (k + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s = ∫⁻ t, ∫⁻ t' : Fin k → ℝ, f (Fin.cons t t') := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have e := hmp.lintegral_map_equiv (fun x : ℝ × (Fin k → ℝ) => f (Fin.cons x.1 x.2))
  have h1 : ∀ s : Fin (k + 1) → ℝ, (fun x : ℝ × (Fin k → ℝ) => f (Fin.cons x.1 x.2))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0 s) = f s := by
    intro s
    simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv,
      Equiv.coe_fn_symm_mk]
    congr 1
    exact Fin.cons_self_tail s
  simp_rw [h1] at e
  rw [← e]
  exact lintegral_prod _ (hf.comp (measurable_fin_cons measurable_fst measurable_snd)).aemeasurable

lemma lintegral_fin_zero (f : (Fin 0 → ℝ) → ℝ≥0∞) : ∫⁻ t, f t = f Fin.elim0 := by
  have : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac Fin.elim0 := by
    rw [volume_pi, Measure.pi_of_empty]
    congr 1
  rw [this, lintegral_dirac]

namespace JitterLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θ : ℝ≥0∞}
  (J : JitterLaw Ω P θ)

/-- The labelled sum over `k` pivots at slots `b > n₁ > ⋯ > n_k` (latest first) of
`∏_i 1_{A n_i} Ψ_{n_k}(ω, p, (q_{n_1}, …, q_{n_k}))` (with an outer parameter `p`): the
quantity `X_𝔰` of Lemma A.5 for one run, the integrand depending on the past of the earliest
pivot. -/
noncomputable def Zs : (k : ℕ) → {Par : Type} → (b : ℕ) →
    (ℕ → Ω → Par → (Fin k → ℝ) → ℝ≥0∞) → Ω → Par → ℝ≥0∞
  | 0, _, b, Ψ => fun ω p => Ψ b ω p Fin.elim0
  | k + 1, _, b, Ψ => fun ω p => ∑' n, if n < b then (J.A n).indicator (fun ω =>
      Zs k n (fun m ω (pt : _ × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) ω (p, J.q n ω)) ω else 0

/-- Measurability of `Zs` for adapted integrands: `Zs k b Ψ` is `F b ⊗ Par`-measurable when each
`Ψ m` is `F m ⊗ (Par ⊗ Borel)`-measurable. -/
theorem Zs_meas : ∀ (k : ℕ) {Par : Type} [MeasurableSpace Par] (b : ℕ)
    (Ψ : ℕ → Ω → Par → (Fin k → ℝ) → ℝ≥0∞),
    (∀ m, JMeas (J.F m) (fun x : Ω × (Par × (Fin k → ℝ)) => Ψ m x.1 x.2.1 x.2.2)) →
    JMeas (J.F b) (fun x : Ω × Par => J.Zs k b Ψ x.1 x.2)
  | 0, Par, _, b, Ψ, hΨ => by
    unfold JMeas at *
    letI := J.F b
    have := hΨ b
    exact this.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  | k + 1, Par, mP, b, Ψ, hΨ => by
    have hΨ' : ∀ m, JMeas (J.F m) (fun x : Ω × ((Par × ℝ) × (Fin k → ℝ)) =>
        (fun m ω (pt : Par × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) m x.1 x.2.1 x.2.2) := by
      intro m
      unfold JMeas at *
      letI := J.F m
      exact (hΨ m).comp (measurable_fst.prodMk ((measurable_fst.comp (measurable_fst.comp
        measurable_snd)).prodMk (measurable_fin_cons (measurable_snd.comp (measurable_fst.comp
          measurable_snd)) (measurable_snd.comp measurable_snd))))
    have ih := fun n => Zs_meas k (Par := Par × ℝ) n
      (fun m ω (pt : Par × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) hΨ'
    unfold JMeas at *
    show @Measurable (Ω × Par) ℝ≥0∞ (@Prod.instMeasurableSpace Ω Par (J.F b) mP) _
      fun x : Ω × Par => ∑' n, if n < b then (J.A n).indicator (fun ω =>
      J.Zs k n (fun m ω (pt : Par × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) ω (x.2, J.q n ω))
        x.1 else 0
    set A' := J.A with hA'
    set q' := J.q with hq'
    set Z' : ℕ → Ω → Par × ℝ → ℝ≥0∞ := fun n =>
      J.Zs k n (fun m ω (pt : Par × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) with hZ'
    have hG : ∀ n, n < b → @Measurable (Ω × (Par × ℝ)) ℝ≥0∞
        (@Prod.instMeasurableSpace Ω (Par × ℝ) (J.F b) _) _ fun x => Z' n x.1 x.2 := fun n hn =>
      @Measurable.mono _ _ (@Prod.instMeasurableSpace Ω (Par × ℝ) (J.F n) _) _ _ _ _ (ih n)
        (sup_le_sup_right (MeasurableSpace.comap_mono (J.F_mono hn.le)) _) le_rfl
    have hq : ∀ n, n < b → @Measurable Ω ℝ (J.F b) _ (q' n) := fun n hn =>
      (J.q_meas n).mono (J.F_mono hn) le_rfl
    have hA : ∀ n, n < b → MeasurableSet[J.F b] (A' n) := fun n hn =>
      J.F_mono hn.le _ (J.A_meas n)
    letI := J.F b
    refine Measurable.ennreal_tsum fun n => ?_
    by_cases hn : n < b
    · simp only [if_pos hn]
      have hcomp : Measurable fun x : Ω × Par => Z' n x.1 (x.2, q' n x.1) :=
        (hG n hn).comp (measurable_fst.prodMk (measurable_snd.prodMk ((hq n hn).comp
          measurable_fst)))
      have hset : MeasurableSet {x : Ω × Par | x.1 ∈ A' n} := measurable_fst (hA n hn)
      have : (fun x : Ω × Par => (A' n).indicator (fun ω => Z' n ω (x.2, q' n ω)) x.1) =
          {x : Ω × Par | x.1 ∈ A' n}.indicator (fun x => Z' n x.1 (x.2, q' n x.1)) := by
        funext x; by_cases h : x.1 ∈ A' n <;> simp [Set.indicator, h]
      rw [this]
      exact hcomp.indicator hset
    · simp only [if_neg hn]; exact measurable_const

lemma Zs_mono_bound (k : ℕ) {Par : Type} {b b' : ℕ} (h : b ≤ b')
    (Ψ : ℕ → Ω → Par → (Fin (k + 1) → ℝ) → ℝ≥0∞) (ω : Ω) (p : Par) :
    J.Zs (k + 1) b Ψ ω p ≤ J.Zs (k + 1) b' Ψ ω p := by
  simp only [Zs]
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hn : n < b
  · rw [if_pos hn, if_pos (lt_of_lt_of_le hn h)]
  · rw [if_neg hn]; exact zero_le _

/-- **Lemma A.5 for one run** (`k` pivots, labels summed, integrand adapted to the past of the
earliest pivot and dominated by a measurable `Ψ̄`):
`E[Zs k N Ψ (·, p)] ≤ θ^k E[∫_{ℝ^k} Ψ̄(·, p, t) dt]`. -/
theorem iterated_pivots [SFinite P] : ∀ (k : ℕ) {Par : Type} [MeasurableSpace Par] (N : ℕ)
    (Ψ : ℕ → Ω → Par → (Fin (k + 1) → ℝ) → ℝ≥0∞),
    (∀ m, JMeas (J.F m) (fun x : Ω × (Par × (Fin (k + 1) → ℝ)) => Ψ m x.1 x.2.1 x.2.2)) →
    ∀ (Ψbar : Ω → Par → (Fin (k + 1) → ℝ) → ℝ≥0∞),
    Measurable (fun x : Ω × (Par × (Fin (k + 1) → ℝ)) => Ψbar x.1 x.2.1 x.2.2) →
    (∀ m ω p t, Ψ m ω p t ≤ Ψbar ω p t) → ∀ p : Par,
    ∫⁻ ω, J.Zs (k + 1) N Ψ ω p ∂P ≤ θ ^ (k + 1) * ∫⁻ ω, (∫⁻ t, Ψbar ω p t) ∂P
  | 0, Par, _, N, Ψ, hΨ, Ψbar, hbar, hdom, p => by
    -- one pivot: `pivot_step`
    set Φ : ℕ → Ω × ℝ → ℝ≥0∞ := fun n x =>
      if n < N then Ψ n x.1 p (Fin.cons x.2 Fin.elim0) else 0 with hΦ
    have hΦm : ∀ n, JMeas (J.F n) (Φ n) := by
      intro n
      by_cases hn : n < N
      · simp only [hΦ, if_pos hn]
        unfold JMeas at *
        letI := J.F n
        exact (hΨ n).comp (measurable_fst.prodMk (measurable_const.prodMk
          (measurable_fin_cons measurable_snd measurable_const)))
      · simp only [hΦ, if_neg hn]
        unfold JMeas
        exact @measurable_const _ _ _ (@Prod.instMeasurableSpace Ω ℝ (J.F n) _) _
    have hbar' : Measurable fun x : Ω × ℝ => Ψbar x.1 p (Fin.cons x.2 Fin.elim0) :=
      hbar.comp (measurable_fst.prodMk (measurable_const.prodMk
        (measurable_fin_cons measurable_snd measurable_const)))
    have hstep := J.pivot_step Φ hΦm (fun x => Ψbar x.1 p (Fin.cons x.2 Fin.elim0)) hbar'
      (fun n x => by
        simp only [hΦ]
        split_ifs
        · exact hdom n x.1 p _
        · exact zero_le _)
    have hZ : ∀ ω, J.Zs 1 N Ψ ω p = ∑' n, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω := by
      intro ω
      simp only [Zs, hΦ]
      refine tsum_congr fun n => ?_
      by_cases hn : n < N
      · simp only [if_pos hn]
      · simp [hn]
    simp_rw [hZ]
    refine hstep.trans (le_of_eq ?_)
    rw [pow_one]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [lintegral_fin_succ (fun s => Ψbar ω p s) (hbar.comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id)))]
    exact lintegral_congr fun t => (lintegral_fin_zero (fun t' => Ψbar ω p (Fin.cons t t'))).symm
  | k + 1, Par, mP, N, Ψ, hΨ, Ψbar, hbar, hdom, p => by
    set Ψ' : ℕ → Ω → Par × ℝ → (Fin (k + 1) → ℝ) → ℝ≥0∞ :=
      fun m ω pt t' => Ψ m ω pt.1 (Fin.cons pt.2 t') with hΨ'def
    have hΨ' : ∀ m, JMeas (J.F m) (fun x : Ω × ((Par × ℝ) × (Fin (k + 1) → ℝ)) =>
        Ψ' m x.1 x.2.1 x.2.2) := by
      intro m
      unfold JMeas at *
      letI := J.F m
      exact (hΨ m).comp (measurable_fst.prodMk ((measurable_fst.comp (measurable_fst.comp
        measurable_snd)).prodMk (measurable_fin_cons (measurable_snd.comp (measurable_fst.comp
          measurable_snd)) (measurable_snd.comp measurable_snd))))
    set Ψbar' : Ω → Par × ℝ → (Fin (k + 1) → ℝ) → ℝ≥0∞ :=
      fun ω pt t' => Ψbar ω pt.1 (Fin.cons pt.2 t') with hΨbar'def
    have hbar'm : Measurable (fun x : Ω × ((Par × ℝ) × (Fin (k + 1) → ℝ)) =>
        Ψbar' x.1 x.2.1 x.2.2) :=
      hbar.comp (measurable_fst.prodMk ((measurable_fst.comp (measurable_fst.comp
        measurable_snd)).prodMk (measurable_fin_cons (measurable_snd.comp (measurable_fst.comp
          measurable_snd)) (measurable_snd.comp measurable_snd))))
    have ih := iterated_pivots k (Par := Par × ℝ) N Ψ' hΨ' Ψbar' hbar'm
      (fun m ω pt t' => hdom m ω pt.1 _)
    -- the pivot step for the latest pivot
    have hG := fun n => J.Zs_meas (k + 1) (Par := Par × ℝ) n Ψ' hΨ'
    set Φ : ℕ → Ω × ℝ → ℝ≥0∞ := fun n x =>
      if n < N then J.Zs (k + 1) n Ψ' x.1 (p, x.2) else 0 with hΦ
    have hΦm : ∀ n, JMeas (J.F n) (Φ n) := by
      intro n
      by_cases hn : n < N
      · simp only [hΦ, if_pos hn]
        have hGn := hG n
        unfold JMeas at *
        letI := J.F n
        exact hGn.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      · simp only [hΦ, if_neg hn]
        unfold JMeas
        exact @measurable_const _ _ _ (@Prod.instMeasurableSpace Ω ℝ (J.F n) _) _
    set Φbar : Ω × ℝ → ℝ≥0∞ := fun x => J.Zs (k + 1) N Ψ' x.1 (p, x.2) with hΦbar
    have hΦbarm : Measurable Φbar := by
      have := (hG N).mono (J.F_le N)
      exact this.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hstep := J.pivot_step Φ hΦm Φbar hΦbarm (fun n x => by
      simp only [hΦ, hΦbar]
      split_ifs with hn
      · exact J.Zs_mono_bound k hn.le Ψ' x.1 (p, x.2)
      · exact zero_le _)
    have hZ : ∀ ω, J.Zs (k + 2) N Ψ ω p =
        ∑' n, (J.A n).indicator (fun ω => Φ n (ω, J.q n ω)) ω := by
      intro ω
      conv_lhs => simp only [Zs]
      refine tsum_congr fun n => ?_
      by_cases hn : n < N
      · simp only [if_pos hn, hΦ]
        rfl
      · simp [hn, hΦ]
    simp_rw [hZ]
    refine hstep.trans ?_
    -- Tonelli and the induction hypothesis
    have hswap : ∫⁻ ω, (∫⁻ t, Φbar (ω, t)) ∂P = ∫⁻ t, ∫⁻ ω, Φbar (ω, t) ∂P :=
      lintegral_lintegral_swap (hΦbarm.comp measurable_id).aemeasurable
    have hbarm2 : Measurable fun x : Ω × ℝ => ∫⁻ t' : Fin (k + 1) → ℝ, Ψbar' x.1 (p, x.2) t' := by
      have hG2 : Measurable fun y : (Ω × ℝ) × (Fin (k + 1) → ℝ) => Ψbar' y.1.1 (p, y.1.2) y.2 :=
        hbar'm.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_const.prodMk
          (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
      exact hG2.lintegral_prod_right'
    calc θ * ∫⁻ ω, (∫⁻ t, Φbar (ω, t)) ∂P
        = θ * ∫⁻ t, ∫⁻ ω, Φbar (ω, t) ∂P := by rw [hswap]
      _ ≤ θ * ∫⁻ t, θ ^ (k + 1) * ∫⁻ ω, (∫⁻ t', Ψbar' ω (p, t) t') ∂P := by
          gcongr with t
          exact ih (p, t)
      _ = θ * (θ ^ (k + 1) * ∫⁻ t, ∫⁻ ω, (∫⁻ t', Ψbar' ω (p, t) t') ∂P) := by
          rw [lintegral_const_mul]
          exact (hbarm2.comp measurable_swap).lintegral_prod_right'
      _ = θ ^ (k + 2) * ∫⁻ ω, (∫⁻ t, Ψbar ω p t) ∂P := by
          rw [← mul_assoc, ← pow_succ']
          congr 1
          rw [lintegral_lintegral_swap (f := fun t ω => ∫⁻ t', Ψbar' ω (p, t) t')
            (hbarm2.comp measurable_swap).aemeasurable]
          refine lintegral_congr fun ω => ?_
          rw [lintegral_fin_succ (fun s => Ψbar ω p s) (hbar.comp (measurable_const.prodMk
            (measurable_const.prodMk measurable_id)))]


/-- **Lemma A.5 for one run, with the Volume Lemma** (Lemma A.2): for fixed cofactors `c_i > 0`,
an invertible pattern `E_P`, caps `q_j ≥ Xm ≥ 1` and a measurable window `J`, the expected number
of labelled pivot `(k+1)`-tuples (slots `< N`) whose rows `n_i = c_i ∏_j q_j^{E_ij}` all lie in
`J` is at most `θ^{k+1} vol(J)^{k+1}/(|det E_P| ∏ c_i Xm^{M-(k+1)})`. -/
theorem pil_volume [IsProbabilityMeasure P] {k : ℕ} {c : Fin (k + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℕ} (hE : (Ereal E).det ≠ 0) {Xm : ℝ} (hXm : 1 ≤ Xm)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (N : ℕ) :
    ∫⁻ ω, J.Zs (k + 1) N (fun _ _ (_ : Unit) t =>
        {t : Fin (k + 1) → ℝ | (∀ j, Xm ≤ t j) ∧ ∀ i, nmap c E t i ∈ Jw}.indicator 1 t) ω () ∂P ≤
      θ ^ (k + 1) * (volume (Set.univ.pi fun _ : Fin (k + 1) => Jw) /
        ENNReal.ofReal (|(Ereal E).det| * (∏ i, c i) * Xm ^ ((∑ i, ∑ j, E i j) - (k + 1)))) := by
  set S := {t : Fin (k + 1) → ℝ | (∀ j, Xm ≤ t j) ∧ ∀ i, nmap c E t i ∈ Jw} with hS
  have hnm : ∀ i, Measurable fun t : Fin (k + 1) → ℝ => nmap c E t i := by
    intro i
    unfold nmap
    exact (continuous_const.mul (continuous_finset_prod _ fun j _ =>
      (continuous_apply j).pow _)).measurable
  have hSm : MeasurableSet S := by
    rw [hS, Set.setOf_and]
    refine MeasurableSet.inter ?_ ?_
    · rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)
    · rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => (hnm i) hJw
  have hind : Measurable (S.indicator (1 : (Fin (k + 1) → ℝ) → ℝ≥0∞)) :=
    measurable_one.indicator hSm
  have hmeasΨ : ∀ m, JMeas (J.F m) (fun x : Ω × (Unit × (Fin (k + 1) → ℝ)) =>
      S.indicator (1 : (Fin (k + 1) → ℝ) → ℝ≥0∞) x.2.2) := by
    intro m
    unfold JMeas
    letI := J.F m
    exact hind.comp (measurable_snd.comp measurable_snd)
  have h := J.iterated_pivots k (Par := Unit) N (fun _ _ _ t => S.indicator 1 t) hmeasΨ
    (fun _ _ t => S.indicator 1 t) (hind.comp (measurable_snd.comp measurable_snd))
    (fun _ _ _ _ => le_rfl) ()
  refine h.trans ?_
  rw [lintegral_const, measure_univ, mul_one, lintegral_indicator_one hSm]
  gcongr
  exact volume_bound hc hE hSm hXm (fun q hq => hq.1) Jw (fun q hq => hq.2)

end JitterLaw

end RankFull
