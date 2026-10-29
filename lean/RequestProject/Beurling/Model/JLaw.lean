module

public import RequestProject.Beurling.Model.TiesProof
public import RequestProject.Beurling.Model.Init

/-!
# The construction as an instance of the abstract jitter law (`RankFull.JitterLaw`)

For admissible `θ`, even `X₀` with `log X₀ ≥ 10⁸` and (84) from `X₀` on, the jitter space with
the filtration `F_n = σ(U_j, j ≤ n)` and, for each relative slot `n + 1`:

* `c n = s_{n+1}`, `H n = H(s_{n+1})`, `q n = s_{n+1} + H(s_{n+1})(U_{n+1} - 1/2)`;
* `A n` = "a prime is placed at relative slot `n + 1`, and `s_{n+1}` carries a unit jump of `T`"
  (`G n`: `s_{n+1}` is not both a rigid integer and an element of `A`; `G n` holds off `𝒩₌`);

is an instance of `RankFull.JitterLaw` with `θ = 2` (`constructionLaw`):
* (F2) `dens` is the box-uniform law of the latest jitter given the past (`lintegral_landing`);
* (F1) `slots`: a point `t` lies in at most `1.01 · 1.01 H + 3` boxes of placed slots, each of
  weight `1/H` (the window count of §3.4 at the placed slot starts, `window_count_on`, and the
  slow variation of `H`, `capH_lip2`).

The nested good events `Good t = ⋂_{n < t} G n` are `F_t`-measurable, decreasing and of
probability `1` (`good_meas`, `good_anti`, `good_compl_null`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The good event of stage `n`: a unit jump of `T` at `s_{n+1}`. -/
def stageGood (θ : ℝ) (X₀ : ℕ) (n : ℕ) : Set JitterΩ :=
  {ω | UnitJumpAt X₀ (DF θ X₀ ω) (slotF θ X₀ n ω)}

/-- The event of the abstract law: a prime is placed and the stage is good. -/
def lawA (θ : ℝ) (X₀ : ℕ) (n : ℕ) : Set JitterΩ := placedF θ X₀ n ∩ stageGood θ X₀ n

/-- **The nested good events** `Good(< t) = ⋂_{n < t} G n`. -/
def goodLt (θ : ℝ) (X₀ : ℕ) (t : ℕ) : Set JitterΩ := ⋂ n ∈ Finset.range t, stageGood θ X₀ n

section Law

variable (hc : Cond θ X₀)
include hc

lemma measurableSet_mem_absSet (x : JitterΩ → ℝ) (hx : Measurable x) :
    MeasurableSet {ω | x ω ∈ absSet X₀ (DF θ X₀ ω)} := by
  have hD := DF_dfam hc
  have : {ω | x ω ∈ absSet X₀ (DF θ X₀ ω)} =
      ⋃ e : PIdx X₀ →₀ ℕ, {ω | AbsQ X₀ (DF θ X₀ ω) e ∧ eval (DF θ X₀ ω) e = x ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, absSet_eq_image, mem_image]
  rw [this]
  exact MeasurableSet.iUnion fun e =>
    (hD.absQ hc.hX e).inter (measurableSet_eq_fun (hD.eval e) hx)

lemma stageGood_measurable (n : ℕ) : MeasurableSet (stageGood θ X₀ n) := by
  classical
  have hs := slotF_measurable (stageMeas hc) n
  have : (stageGood θ X₀ n)ᶜ = ⋃ k : ℕ, ({ω | (k : ℝ) = slotF θ X₀ n ω} ∩
      (if (X₀ : ℝ) < k ∧ k ∈ Nat.smoothNumbers X₀ then
        {ω | (k : ℝ) ∈ absSet X₀ (DF θ X₀ ω)} else ∅)) := by
    ext ω
    simp only [stageGood, UnitJumpAt, mem_compl_iff, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    push_neg
    constructor
    · rintro ⟨k, h1, h2, h3, h4⟩
      exact ⟨k, h1, by rw [if_pos ⟨h2, h3⟩]; exact h4⟩
    · rintro ⟨k, h1, h2⟩
      split_ifs at h2 with h
      · exact ⟨k, h1, h.1, h.2, h2⟩
      · exact absurd h2 (notMem_empty _)
  rw [← compl_compl (stageGood θ X₀ n), this]
  refine (MeasurableSet.iUnion fun k => ?_).compl
  refine (measurableSet_eq_fun measurable_const hs).inter ?_
  split_ifs
  · exact measurableSet_mem_absSet hc (fun _ => (k : ℝ)) measurable_const
  · exact MeasurableSet.empty

/-- **The good event of stage `n` is `F_n`-measurable.** -/
theorem stageGood_adapted (n : ℕ) :
    MeasurableSet[jitterFiltration n] (stageGood θ X₀ n) := by
  have hmeas : Measurable ((stageGood θ X₀ n).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator (stageGood_measurable hc n)
  have hiff : ∀ ω ω' : JitterΩ, (∀ j ≤ n, ω j = ω' j) →
      (ω ∈ stageGood θ X₀ n ↔ ω' ∈ stageGood θ X₀ n) := by
    intro ω ω' hω
    have hs : slotF θ X₀ n ω = slotF θ X₀ n ω' := (Mcl_stage_congr hc hω).1 (n + 1) le_rfl
    have hA : ∀ x ≤ slotF θ X₀ n ω, (x ∈ absSet X₀ (DF θ X₀ ω) ↔
        x ∈ absSet X₀ (DF θ X₀ ω')) := by
      intro x hx
      unfold DF
      rw [Mcl_eq hc, Mcl_eq hc]
      unfold slotF at hx; rw [Mcl_eq hc] at hx
      exact limModel_absSet_congr (hc.std ω) (hc.std ω')
        (fun j hj => by simp only [Ucl, hω j hj]) hx
    simp only [stageGood, UnitJumpAt, mem_setOf_eq]
    rw [← hs]
    constructor
    · intro h k hk h1 h2 h3
      exact h k hk h1 h2 ((hA _ (le_of_eq hk)).mpr h3)
    · intro h k hk h1 h2 h3
      exact h k hk h1 h2 ((hA _ (le_of_eq hk)).mp h3)
  have h := measurable_filtration_of_congr hmeas n fun ω ω' hω => by
    by_cases h1 : ω ∈ stageGood θ X₀ n
    · rw [indicator_of_mem h1, indicator_of_mem ((hiff ω ω' hω).mp h1)]
    · rw [indicator_of_notMem h1, indicator_of_notMem fun h2 => h1 ((hiff ω ω' hω).mpr h2)]
  have : stageGood θ X₀ n = ((stageGood θ X₀ n).indicator fun _ => (1 : ℝ)) ⁻¹' {1} := by
    ext ω; by_cases h1 : ω ∈ stageGood θ X₀ n <;> simp [h1]
  rw [this]
  exact h (measurableSet_singleton _)

theorem lawA_adapted (n : ℕ) : MeasurableSet[jitterFiltration n] (lawA θ X₀ n) :=
  (placedF_adapted hc (stageMeas hc) n).inter (stageGood_adapted hc n)

/-- **(F2) for the construction.** -/
theorem law_dens (n : ℕ) (Φ : JitterΩ × ℝ → ℝ≥0∞) (hΦ : JMeas (jitterFiltration n) Φ) :
    ∫⁻ ω, (lawA θ X₀ n).indicator (fun ω => Φ (ω, valF θ X₀ n ω)) ω ∂jitterMeasure ≤
      ∫⁻ ω, (lawA θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
        ∫⁻ t in box (slotF θ X₀ n ω) (HF θ X₀ n ω), Φ (ω, t)) ω ∂jitterMeasure :=
  le_of_eq (lintegral_landing n (slotF_adapted hc (stageMeas hc) n)
    (HF_adapted hc (stageMeas hc) n) (HF_pos hc n) (lawA_adapted hc n) hΦ)

/-- The slots of a box around `t` start within `1.01 H₀ + 1` of the first one. -/
lemma box_spread {s₀ s t : ℝ} (hs₀ : (X₀ : ℝ) ≤ s₀) (hss : s₀ ≤ s)
    (ht₀ : t ∈ box s₀ (capH X₀ s₀)) (ht : t ∈ box s (capH X₀ s)) :
    s - s₀ ≤ 1.01 * capH X₀ s₀ + 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hH := log_le_capH hX0 hc.hX hs₀
  have hl : 0 ≤ Real.log s₀ := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
  have hH0 : 200 ≤ capH X₀ s₀ := by linarith
  have hlip := capH_lip2 hc.hX hs₀ hss
  unfold box at ht₀ ht
  have h1 := ht₀.2
  have h2 := ht.1
  set d := s - s₀
  set H₀ := capH X₀ s₀
  have hd : d ≤ H₀ + d / (4 * H₀) + 1 / 8 := by
    have : d / (2 * H₀) / 2 = d / (4 * H₀) := by field_simp; ring
    linarith
  have hd' : 4 * H₀ * d ≤ 4 * H₀ ^ 2 + d + H₀ / 2 := by
    have e : 4 * H₀ * (d / (4 * H₀)) = d := by field_simp
    nlinarith
  nlinarith

variable (hev : Even X₀)
include hev

/-- **(F1) for the construction**: every point lies in at most `2` units of box weight. -/
theorem law_slots (ω : JitterΩ) (t : ℝ) :
    ∑' n, (lawA θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 t) ω ≤ 2 := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set N := {n | ω ∈ lawA θ X₀ n ∧ t ∈ box (slotF θ X₀ n ω) (HF θ X₀ n ω)} with hN
  have hf : ∀ n, (lawA θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 t) ω =
      if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0 := by
    intro n
    by_cases h1 : ω ∈ lawA θ X₀ n
    · by_cases h2 : t ∈ box (slotF θ X₀ n ω) (HF θ X₀ n ω)
      · simp [hN, h1, h2]
      · simp [hN, h2]
    · simp [hN, h1]
  simp_rw [hf]
  rcases N.eq_empty_or_nonempty with hN0 | hNne
  · simp [hN0]
  -- the first box
  have hex : ∃ n, n ∈ N := hNne
  set n₀ := Nat.find hex
  have hn₀ : n₀ ∈ N := Nat.find_spec hex
  set s₀ := slotF θ X₀ n₀ ω
  have hs₀X : (X₀ : ℝ) ≤ s₀ := slotF_ge hc n₀ ω
  set H₀ := capH X₀ s₀
  have hH0 : 200 ≤ H₀ := by
    have := log_le_capH hX0 hc.hX hs₀X
    have : 0 ≤ Real.log s₀ := Real.log_nonneg (by linarith [X₀_ge_two_pow hc.hX])
    linarith
  -- every box start in `N` is within `1.01 H₀ + 1` of `s₀`
  have hmono : ∀ n ∈ N, s₀ ≤ slotF θ X₀ n ω := fun n hn =>
    (Mcl θ X₀ ω).slot_mono (by have := Nat.find_min' hex hn; omega)
  have hspread : ∀ n ∈ N, slotF θ X₀ n ω ≤ s₀ + (1.01 * H₀ + 1) := fun n hn => by
    have := box_spread hc hs₀X (hmono n hn) hn₀.2 hn.2
    linarith
  have hHn : ∀ n ∈ N, H₀ ≤ HF θ X₀ n ω := fun n hn =>
    capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hs₀X) (mem_Ici.mpr (slotF_ge hc n ω)) (hmono n hn)
  -- the window count
  set S₀ := {m | ω ∈ lawA θ X₀ m}
  have hS₀ : ∀ m ∈ S₀, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1)) := by
    intro m hm
    have h1 := hm.1
    have h2 := hm.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨h1, h2⟩
  have hwin := window_count_on (winFacts h) S₀ hS₀ (limModel_slot_one h hev).1
    (a := s₀ - 1) (b := s₀ + (1.01 * H₀ + 1)) (by linarith)
  have hNsub : N ⊆ {m | m ∈ S₀ ∧ s₀ - 1 < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (1.01 * H₀ + 1)} := by
    intro n hn
    have h1 := hmono n hn
    have h2 := hspread n hn
    simp only [slotF] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨hn.1, by linarith, h2⟩
  have hWfin : {m | m ∈ S₀ ∧ s₀ - 1 < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (1.01 * H₀ + 1)}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hNfin : N.Finite := hWfin.subset hNsub
  have hc1 : (N.ncard : ℝ) ≤ ({m | m ∈ S₀ ∧ s₀ - 1 < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (1.01 * H₀ + 1)}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hNsub hWfin
  have hcard : (N.ncard : ℝ) ≤ 1.01 * ((s₀ + (1.01 * H₀ + 1)) - (s₀ - 1)) + 1 :=
    hc1.trans hwin
  -- the sum
  have hsum : ∑' n, (if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0) ≤
      ∑' n, (if n ∈ N then ENNReal.ofReal H₀⁻¹ else 0) := by
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs with hn
    · exact ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith) (hHn n hn))
    · exact le_rfl
  refine hsum.trans ?_
  rw [tsum_eq_sum (s := hNfin.toFinset) (fun n hn => by
    simp only [Set.Finite.mem_toFinset] at hn; simp [hn])]
  rw [Finset.sum_congr rfl (fun b hb => if_pos ((Set.Finite.mem_toFinset _).mp hb)),
    Finset.sum_const, nsmul_eq_mul]
  rw [← Set.ncard_eq_toFinset_card N hNfin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have : (N.ncard : ℝ) * H₀⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith
  calc ENNReal.ofReal ((N.ncard : ℝ) * H₀⁻¹) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
    _ = 2 := by simp

/-- **The construction is an instance of the abstract jitter law** `RankFull.JitterLaw`, with
`θ = 2` (§6.1, standing facts (F1) and (F2)). -/
noncomputable def constructionLaw : JitterLaw JitterΩ jitterMeasure 2 where
  F n := jitterFiltration n
  F_mono := fun _ _ h => jitterFiltration.mono h
  F_le n := jitterFiltration.le n
  A := lawA θ X₀
  q := valF θ X₀
  c := slotF θ X₀
  H := HF θ X₀
  A_meas := lawA_adapted hc
  q_meas := valF_adapted hc (stageMeas hc)
  c_meas := slotF_adapted hc (stageMeas hc)
  H_meas := HF_adapted hc (stageMeas hc)
  H_pos := HF_pos hc
  dens := law_dens hc
  slots := law_slots hc hev

omit hev in
/-- The good events are `F_t`-measurable. -/
theorem good_meas (t : ℕ) : MeasurableSet[jitterFiltration t] (goodLt θ X₀ t) := by
  refine Finset.measurableSet_biInter _ fun n hn => ?_
  exact jitterFiltration.mono (Finset.mem_range.mp hn).le _ (stageGood_adapted hc n)

omit hc hev in
/-- The good events are decreasing. -/
theorem good_anti : Antitone (goodLt θ X₀) := by
  intro s t hst ω hω
  simp only [goodLt, mem_iInter] at hω ⊢
  exact fun n hn => hω n (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hst))

omit hev in
/-- **The good events have probability `1`** (a failure is a tie, `𝒩₌` is null). -/
theorem good_compl_null (t : ℕ) : jitterMeasure (goodLt θ X₀ t)ᶜ = 0 := by
  have hS : jitterMeasure {ω : JitterΩ | ¬ ∀ j, ω j ∈ Icc (0 : ℝ) 1} = 0 := by
    have := ae_jitter_mem
    rwa [Filter.Eventually, mem_ae_iff] at this
  have hT := tiesEvent_null hc (stageMeas hc)
  refine measure_mono_null ?_ (measure_union_null hS hT)
  intro ω hω
  by_cases hU : ∀ j, ω j ∈ Icc (0 : ℝ) 1
  · right
    refine ⟨⟨hc.hθ, hc.hX, hU, hc.hHB⟩, fun htf => hω ?_⟩
    simp only [goodLt, mem_iInter]
    intro n _
    have hM : Mcl θ X₀ ω = constructedModel θ X₀ ω := by unfold Mcl; rw [Ucl_eq hU]
    have := unitJumps_of_tieFree (M := Mcl θ X₀ ω) (U := Ucl ω) (by
      rw [hM, Ucl_eq hU]; exact htf)
    exact this.at _
  · exact Or.inl hU

end Law

end BModel

end
