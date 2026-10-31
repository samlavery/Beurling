module

public import RequestProject.Beurling.Model.MeasGen
public import RequestProject.Beurling.Model.Valid

/-!
# Measurability of the objects read from measurable prime data

For a family of prime data `D : Ω → PrimeData` with measurable decisions and values (`DFam`),
locally finite with values `≥ 2`:

* the values `eval (D ω) e` and the conditions defining the elements are measurable;
* `N(x)` (`NCount`), the counting function `#(A ∩ [1, x])` of the absorbed set (5) and the capped
  absorbed density `ρ̄_A(v)` are jointly measurable in `(ω, x)`;
* for measurable amplitudes and heights `α, γ : Ω → ℕ → ℝ`, the oscillation `R(x)` and the
  target (6) are jointly measurable (`measurable_target_fam`).
-/

@[expose] public section

open MeasureTheory Set Real Target Oscillation Absorbed Construction DesignedZero Decomp
  AbsorbEmpty CaplLink QueueMono

namespace BModel

variable {Ω : Type*} [MeasurableSpace Ω] {X₀ : ℕ}

/-- **Measurable prime data**: the decisions and values are measurable. -/
structure DFam (D : Ω → PrimeData) : Prop where
  live : ∀ k, MeasurableSet {ω | (D ω).live k}
  v : ∀ k, Measurable fun ω => (D ω).v k

namespace DFam

variable {D : Ω → PrimeData} (hD : DFam D)
include hD

lemma pval (i : PIdx X₀) : Measurable fun ω => pval (D ω) i := by
  cases i with
  | inl p => exact measurable_const
  | inr k => exact hD.v k

lemma eval (e : PIdx X₀ →₀ ℕ) : Measurable fun ω => eval (D ω) e := by
  unfold BModel.eval Finsupp.prod
  exact Finset.measurable_prod _ fun i _ => (hD.pval i).pow_const _

lemma live_e (e : PIdx X₀ →₀ ℕ) : MeasurableSet {ω | Live (D ω) e} := by
  classical
  have : {ω | Live (D ω) e} = ⋂ k, ({ω | e (Sum.inr k) = 0} ∪ {ω | (D ω).live k}) := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, mem_union, Live]
    exact ⟨fun h k => by by_cases hk : e (Sum.inr k) = 0 <;> simp_all,
      fun h k hk => (h k).resolve_left hk⟩
  rw [this]
  exact MeasurableSet.iInter fun k => (MeasurableSet.const _).union (hD.live k)

lemma gt1 (e : PIdx X₀ →₀ ℕ) : MeasurableSet {ω | ∀ i ∈ e.support, 1 < BModel.pval (D ω) i} := by
  have : {ω | ∀ i ∈ e.support, 1 < BModel.pval (D ω) i} =
      ⋂ i ∈ e.support, {ω | 1 < BModel.pval (D ω) i} := by ext; simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ => measurableSet_lt measurable_const (hD.pval i)

lemma latest (e : PIdx X₀ →₀ ℕ) {y : Ω → ℝ} (hy : Measurable y) :
    MeasurableSet {ω | LatestBelow (D ω) e (y ω)} := by
  classical
  have : {ω | LatestBelow (D ω) e (y ω)} = ⋃ k, (if e (Sum.inr k) ≠ 0 ∧
      (∀ k', e (Sum.inr k') ≠ 0 → k' ≤ k) then {ω | (D ω).v k < y ω} else ∅) := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, LatestBelow]
    constructor
    · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, by rw [if_pos ⟨h1, h2⟩]; exact h3⟩
    · rintro ⟨k, hk⟩
      split_ifs at hk with h
      · exact ⟨k, h.1, h.2, hk⟩
      · exact absurd hk (notMem_empty _)
  rw [this]
  refine MeasurableSet.iUnion fun k => ?_
  split_ifs
  · exact measurableSet_lt (hD.v k) hy
  · exact MeasurableSet.empty

end DFam

/-- `y(n)` is non-decreasing in `n`, hence measurable. -/
lemma measurable_absorbY (hX : 10 ^ 8 ≤ Real.log X₀) : Measurable (absorbY X₀) := by
  apply Monotone.measurable
  intro a b hab
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  unfold absorbY
  have h1 : (X₀ : ℝ) ≤ dyadicScale X₀ (max X₀ a) := le_dyadicScale (by linarith) (le_max_left _ _)
  exact absorbYAt_mono hX0 hX h1
    (dyadicScale_mono (by linarith) (by linarith [le_max_left (X₀ : ℝ) a])
      (max_le_max le_rfl hab))

/-- The defining condition of an element of the absorbed set (5). -/
def AbsQ (X₀ : ℕ) (D : PrimeData) (e : PIdx X₀ →₀ ℕ) : Prop :=
  10 ^ 7 ≤ Real.log (eval D e) ∧ Live D e ∧ (∀ i ∈ e.support, 1 < pval D i) ∧
    LatestBelow D e (absorbY X₀ (eval D e))

lemma absSet_eq_image (D : PrimeData) : absSet X₀ D = eval D '' {e | AbsQ X₀ D e} := by
  ext n
  constructor
  · rintro ⟨hlog, e, h1, h2, rfl, h3⟩; exact ⟨e, ⟨hlog, h1, h2, h3⟩, rfl⟩
  · rintro ⟨e, ⟨hlog, h1, h2, h3⟩, rfl⟩; exact ⟨hlog, e, h1, h2, rfl, h3⟩

lemma DFam.absQ {D : Ω → PrimeData} (hD : DFam D) (hX : 10 ^ 8 ≤ Real.log X₀)
    (e : PIdx X₀ →₀ ℕ) : MeasurableSet {ω | AbsQ X₀ (D ω) e} := by
  have he := hD.eval e
  refine (measurableSet_le measurable_const (Real.measurable_log.comp he)).inter
    ((hD.live_e e).inter ((hD.gt1 e).inter (hD.latest e ((measurable_absorbY hX).comp he))))

/-! ### Counting functions -/

section Counts

variable {D : Ω → PrimeData} (hD : DFam D) (hL : ∀ ω, LocFinD (D ω)) (hP : ∀ ω, Pos2 (D ω))
include hD hL hP

omit [MeasurableSpace Ω] hD in
lemma finite_le (ω : Ω) (x : ℝ) : (elemsLe X₀ (D ω) x).Finite :=
  (finite_elems_gt (hL ω) x).subset fun e he =>
    ⟨he.1, fun i hi => by linarith [pval_ge_two (hP ω) he.1 hi], he.2⟩

/-- **`N(x)` is jointly measurable.** -/
theorem measurable_NCount :
    Measurable fun p : Ω × ℝ => NCount X₀ (D p.1) p.2 := by
  unfold NCount
  refine measurable_ncard (S := fun p : Ω × ℝ => elemsLe X₀ (D p.1) p.2) (fun e => ?_)
    (fun p => finite_le hL hP p.1 p.2)
  exact ((hD.live_e e).preimage measurable_fst).inter
    (measurableSet_le ((hD.eval e).comp measurable_fst) measurable_snd)

/-- **`#(A ∩ [1, x])` is jointly measurable.** -/
theorem measurable_countA (hX : 10 ^ 8 ≤ Real.log X₀) :
    Measurable fun p : Ω × ℝ => countA (absSet X₀ (D p.1)) p.2 := by
  unfold countA
  have he : ∀ p : Ω × ℝ, absSet X₀ (D p.1) ∩ Icc 1 p.2 =
      eval (D p.1) '' {e | AbsQ X₀ (D p.1) e ∧ eval (D p.1) e ∈ Icc 1 p.2} := by
    intro p
    rw [absSet_eq_image]
    ext n
    simp only [mem_inter_iff, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hn⟩; exact ⟨e, ⟨he, hn⟩, rfl⟩
    · rintro ⟨e, ⟨he, hn⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hn⟩
  simp_rw [he]
  refine measurable_ncard_image (S := fun p : Ω × ℝ =>
      {e | AbsQ X₀ (D p.1) e ∧ eval (D p.1) e ∈ Icc 1 p.2}) (fun e => ?_)
    (fun e => (hD.eval e).comp measurable_fst) (fun p => ?_)
  · exact ((hD.absQ hX e).preimage measurable_fst).inter
      ((measurableSet_le measurable_const ((hD.eval e).comp measurable_fst)).inter
        (measurableSet_le ((hD.eval e).comp measurable_fst) measurable_snd))
  · exact (finite_le hL hP p.1 p.2).subset fun e he => ⟨he.1.2.1, he.2.2⟩

end Counts

/-! ### The absorbed density -/

lemma solveU_neg {b n : ℝ} (hn : n < 0) : solveU b n = 0 := by
  unfold solveU
  rw [dif_neg]
  rintro ⟨u, hu, hu'⟩
  have := Real.rpow_nonneg hu b
  linarith

/-- `u_a` is non-decreasing in `a`, hence measurable. -/
lemma solveU_mono {b : ℝ} (hb : 0 < b) : Monotone (solveU b) := by
  intro n n' hnn
  rcases lt_or_ge n 0 with hn | hn
  · rw [solveU_neg hn]; exact solveU_nonneg b n'
  · obtain ⟨h0, h1⟩ := solveU_spec hb hn
    obtain ⟨h0', h1'⟩ := solveU_spec hb (hn.trans hnn)
    by_contra hlt
    push_neg at hlt
    have := Real.rpow_le_rpow h0' hlt.le hb.le
    linarith

lemma measurable_uA {θ : ℝ} (hθ : 0 < θ) : Measurable (uA θ) :=
  (solveU_mono (thetaB_pos (by linarith))).measurable

/-- The bump `1[u_a ≤ v ≤ a] v^{-b}` is jointly measurable. -/
lemma measurable_bump {θ : ℝ} (hθ : 0 < θ) :
    Measurable (Function.uncurry fun a v : ℝ =>
      (Icc (uA θ a) a).indicator (fun w => w ^ (-(thetaB θ))) v) := by
  have hS : MeasurableSet {p : ℝ × ℝ | uA θ p.1 ≤ p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_le ((measurable_uA hθ).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have : (Function.uncurry fun a v : ℝ =>
      (Icc (uA θ a) a).indicator (fun w => w ^ (-(thetaB θ))) v) =
      {p : ℝ × ℝ | uA θ p.1 ≤ p.2 ∧ p.2 ≤ p.1}.indicator fun p => p.2 ^ (-(thetaB θ)) := by
    funext p; simp [Set.indicator, Function.uncurry]
  rw [this]
  exact (measurable_snd.pow_const _).indicator hS

section Density

variable {D : Ω → PrimeData} (hD : DFam D) (hL : ∀ ω, LocFinD (D ω)) (hP : ∀ ω, Pos2 (D ω))
include hD hL hP

/-- **The capped absorbed density `ρ̄_A(v)` is jointly measurable.** -/
theorem measurable_rhoCap (hX : 10 ^ 8 ≤ Real.log X₀) {θ : ℝ} (hθ : 0 < θ) :
    Measurable fun p : Ω × ℝ =>
      absorbedDensityCap (thetaB θ) (absSet X₀ (D p.1)) (uA θ) p.2 := by
  classical
  unfold absorbedDensityCap absorbedDensity absorbedBump
  refine Measurable.min ?_ (measurable_const.div (Real.measurable_log.comp measurable_snd))
  simp_rw [absSet_eq_image]
  refine measurable_tsum_image (S := fun ω => {e | AbsQ X₀ (D ω) e}) (hD.absQ hX)
    (fun e => hD.eval e) (measurable_bump hθ) (fun ω v => ?_)
  refine (finite_le hL hP ω (v + v ^ (thetaB θ))).subset ?_
  rintro e ⟨hq, hF⟩
  refine ⟨hq.2.1, ?_⟩
  have hmem : v ∈ Icc (uA θ (eval (D ω) e)) (eval (D ω) e) := by
    by_contra hc
    exact hF (indicator_of_notMem hc _)
  have hpos : 0 ≤ eval (D ω) e := le_trans zero_le_one (one_le_eval (hP ω).pos hq.2.1)
  have hb : 0 < thetaB θ := thetaB_pos (by linarith)
  obtain ⟨h0, h1⟩ := solveU_spec hb hpos
  have hv0 : 0 ≤ v := h0.trans hmem.1
  have := Real.rpow_le_rpow h0 hmem.1 hb.le
  simp only [uA] at hmem
  linarith [hmem.1]

end Density

/-- **The integral of a jointly measurable function over `[X₀, x]` is jointly measurable.** -/
lemma measurable_intervalIntegral {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (a : ℝ) : Measurable fun p : Ω × ℝ => ∫ v in a..p.2, f p.1 v := by
  have hI : ∀ (g : Ω × ℝ → Set ℝ), MeasurableSet {q : (Ω × ℝ) × ℝ | q.2 ∈ g q.1} →
      Measurable fun p : Ω × ℝ => ∫ v, (g p).indicator (f p.1) v := by
    intro g hg
    have hm : Measurable fun q : (Ω × ℝ) × ℝ => (g q.1).indicator (f q.1.1) q.2 := by
      have : (fun q : (Ω × ℝ) × ℝ => (g q.1).indicator (f q.1.1) q.2) =
          {q : (Ω × ℝ) × ℝ | q.2 ∈ g q.1}.indicator fun q => f q.1.1 q.2 := by
        funext q; simp [Set.indicator]
      rw [this]
      exact (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hg
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have e : (fun p : Ω × ℝ => ∫ v in a..p.2, f p.1 v) = fun p =>
      (∫ v, (Ioc a p.2).indicator (f p.1) v) - ∫ v, (Ioc p.2 a).indicator (f p.1) v := by
    funext p
    rw [intervalIntegral, integral_indicator measurableSet_Ioc,
      integral_indicator measurableSet_Ioc]
  rw [e]
  refine (hI _ ?_).sub (hI _ ?_)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  · exact (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

/-- The rigid density is measurable. -/
lemma measurable_rhoDet (X₀ : ℕ) (κ : ℝ) : Measurable (rhoDet X₀ κ) := by
  classical
  unfold rhoDet rigidCount
  refine Measurable.div ?_ (measurable_const.mul measurable_id)
  have he : ∀ u : ℝ, (((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter
      fun n : ℕ => u ≤ (n : ℝ)).card : ℝ) =
      (({n : ℕ | n ∈ Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀ ∧ u ≤ (n : ℝ)}).ncard : ℝ) := by
    intro u
    rw [← Set.ncard_coe_finset]; congr 2; ext n; simp
  simp_rw [he]
  refine measurable_ncard (fun n => ?_) (fun u => ?_)
  · have h1 : MeasurableSet {u : ℝ | n ∈ Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀} :=
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id))
        (MeasurableSet.of_discrete (s := {m : ℕ | n ∈ Nat.smoothNumbersUpTo m X₀}))
    exact h1.inter (measurableSet_le measurable_id measurable_const)
  · exact (Finset.finite_toSet _).subset fun n hn => by simpa using hn.1

/-- The count of rigid integers is measurable. -/
lemma measurable_smoothCount (X₀ : ℕ) : Measurable fun x : ℝ => (Rankin.smoothCount X₀ x : ℝ) := by
  unfold Rankin.smoothCount
  exact (measurable_from_nat (f := fun n : ℕ => ((Nat.smoothNumbersUpTo n X₀).card : ℝ))).comp
    Nat.measurable_floor

/-- A switched-on oscillation term at `x` has `x⁺_j < |x|`. -/
lemma lt_abs_of_oscTerm_ne {θ α γ xp x : ℝ} (hxp : 0 < xp) (h : oscTerm θ α γ xp x ≠ 0) :
    xp < |x| := by
  by_contra hc
  push_neg at hc
  apply h
  unfold oscTerm
  have : Real.log (x / xp) ≤ 0 := by
    rw [← Real.log_abs, abs_div, abs_of_pos hxp]
    rcases (abs_nonneg x).lt_or_eq with h0 | h0
    · exact Real.log_nonpos (div_nonneg h0.le hxp.le) ((div_le_one hxp).mpr hc)
    · rw [← h0]; simp
  rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

/-- **The oscillation is jointly measurable** in measurable amplitudes and heights. -/
theorem measurable_osc_fam {θ : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) {α γ : Ω → ℕ → ℝ}
    (hα : ∀ j, Measurable fun ω => α ω j) (hγ : ∀ j, Measurable fun ω => γ ω j) :
    Measurable fun p : Ω × ℝ => osc θ (α p.1) (γ p.1) (switchOn X₀) p.2 := by
  have hX1 : (1 : ℝ) ≤ X₀ := (one_lt_of_logX (Nat.cast_nonneg _) hX).le
  unfold osc
  refine measurable_tsum_of_finite_support (fun j => ?_) (fun p => ?_)
  · unfold oscTerm
    refine ((((hα j).comp measurable_fst).mul (measurable_snd.pow_const θ)).mul
      (Real.measurable_cos.comp (((hγ j).comp measurable_fst).mul
        (Real.measurable_log.comp measurable_snd)))).mul ?_
    exact Real.smoothTransition.continuous.measurable.comp
      (Real.measurable_log.comp (measurable_snd.div_const _))
  · refine (Set.finite_lt_nat ⌈|p.2|⌉₊).subset fun j hj => ?_
    have h1 := lt_abs_of_oscTerm_ne (switchOn_pos _ j) hj
    have h2 := nat_lt_switchOn hX1 j
    have h3 := Nat.le_ceil |p.2|
    simp only [mem_setOf_eq]
    exact_mod_cast (show (j : ℝ) < ⌈|p.2|⌉₊ by linarith)

/-- **The target (6) is jointly measurable** in jointly measurable data. -/
theorem measurable_target_fam (X₀ : ℕ) (κ : ℝ) {cnt rho R : Ω → ℝ → ℝ}
    (hcnt : Measurable fun p : Ω × ℝ => cnt p.1 p.2)
    (hrho : Measurable fun p : Ω × ℝ => rho p.1 p.2)
    (hR : Measurable fun p : Ω × ℝ => R p.1 p.2) :
    Measurable fun p : Ω × ℝ => target X₀ κ (cnt p.1) (rho p.1) (R p.1) p.2 := by
  unfold target
  refine Measurable.ite (measurableSet_lt measurable_snd measurable_const)
    ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor.comp measurable_snd)) ?_
  have hdet : Measurable fun p : Ω × ℝ => ∫ u in (X₀ : ℝ)..p.2, rhoDet X₀ κ u :=
    measurable_intervalIntegral (f := fun (_ : Ω) u => rhoDet X₀ κ u)
      ((measurable_rhoDet X₀ κ).comp measurable_snd) _
  have hint : Measurable fun p : Ω × ℝ => ∫ u in (X₀ : ℝ)..p.2, rho p.1 u :=
    measurable_intervalIntegral (f := rho) hrho _
  have hRX : Measurable fun p : Ω × ℝ => R p.1 X₀ :=
    hR.comp (measurable_fst.prodMk measurable_const)
  exact (((measurable_const.add (((measurable_smoothCount X₀).comp measurable_snd).sub
    measurable_const)).add hcnt).add ((((measurable_snd.sub measurable_const).sub hdet).sub
      hint).add (hR.sub hRX)))

end BModel

end
