module

public import RequestProject.Beurling.Model.MeasTarget
public import RequestProject.Beurling.Model.Stage

/-!
# Measurability of the construction in the jitters, stage by stage

For fixed `θ`, `X₀` with (84) from `X₀` on (`Cond`):

* `measurable_slot_fam` : the slot starts of a family of slot models with measurable targets are
  measurable (`s_k ≤ c ⟺ T(c) ≥ k + ϑ_s`, by right-continuity);
* `measurable_greedyPrime` : the decisions of the greedy rule are measurable in the arrivals;
* `iterD_dfam` : every iterate `M_n` of the construction, at the clamped jitters, has measurable
  prime data, targets, slot starts and arrivals (induction on `n`: the target of measurable data
  is measurable, `measurable_targetD`; the arrivals are counts of composites between measurable
  slot starts);
* `stageMeas` : **the slot starts and decisions of the constructed model are measurable**
  (`StageMeas`); the limit reads the iterates at finite horizons.
-/

@[expose] public section

open MeasureTheory Set Real Target Oscillation Absorbed Construction DesignedZero Decomp
  AbsorbEmpty CaplLink QueueMono SlotModel Greedy

namespace BModel

variable {Ω : Type*} [MeasurableSpace Ω] {θ : ℝ} {X₀ : ℕ}

/-- **The slot starts of measurable targets are measurable.** -/
theorem measurable_slot_fam {M : Ω → SlotModel X₀} {ϑ : ℝ} (hϑ : ∀ ω, (M ω).ϑ = ϑ)
    (hT : ∀ x, Measurable fun ω => (M ω).T x) (k : ℕ) :
    Measurable fun ω => (M ω).slot k := by
  apply measurable_of_Iic
  intro c
  by_cases hc : 1 ≤ c
  · have : (fun ω => (M ω).slot k) ⁻¹' Iic c =
        {ω | (X₀ : ℝ) - 1 + k + ϑ ≤ (M ω).T c} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_setOf_eq]
      constructor
      · intro h
        have h1 := (M ω).level_le_T_slot k
        have h2 := (M ω).T_mono h
        unfold SlotModel.level at h1
        rw [hϑ] at h1
        linarith
      · intro h
        apply (M ω).slot_le
        refine ⟨hc, ?_⟩
        unfold SlotModel.level; rw [hϑ]; exact h
    rw [this]
    exact measurableSet_le measurable_const (hT c)
  · push_neg at hc
    have : (fun ω => (M ω).slot k) ⁻¹' Iic c = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hc ((M ω).one_le_slot k)
    rw [this]; exact MeasurableSet.empty

/-- The greedy queue is measurable in the arrivals. -/
lemma measurable_greedyQueue {A : Ω → ℕ → ℤ} (hA : ∀ i, Measurable fun ω => A ω i) (j : ℕ) :
    Measurable fun ω => greedyQueue (A ω) j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [greedyQueue]
    have h2 : Measurable fun ω => (greedyQueue (A ω) j, A ω (j + 1)) := ih.prodMk (hA (j + 1))
    have hg : Measurable fun p : ℤ × ℤ => p.1 + p.2 + max 0 (1 - p.1 - p.2) - 1 :=
      measurable_of_countable _
    exact hg.comp h2

/-- **The decisions of the greedy rule are measurable in the arrivals.** -/
lemma measurable_greedyPrime {A : Ω → ℕ → ℤ} (hA : ∀ i, Measurable fun ω => A ω i) (j : ℕ) :
    Measurable fun ω => greedyPrime (A ω) j := by
  unfold greedyPrime
  have h2 : Measurable fun ω => (greedyQueue (A ω) j, A ω (j + 1)) :=
    (measurable_greedyQueue hA j).prodMk (hA (j + 1))
  have hg : Measurable fun p : ℤ × ℤ => max 0 (1 - p.1 - p.2) := measurable_of_countable _
  exact hg.comp h2

lemma measurableSet_placed {M : Ω → SlotModel X₀} (hA : ∀ i, Measurable fun ω => (M ω).arr i)
    (k : ℕ) : MeasurableSet {ω | placedAt (M ω) k} :=
  (measurable_greedyPrime hA k) (measurableSet_singleton 1)

section Iter

variable (hc : Cond θ X₀)
include hc

omit hc in
lemma measurable_Ucl (j : ℕ) : Measurable fun ω : JitterΩ => Ucl ω j :=
  measurable_clamp01.comp (measurable_pi_apply j)

/-- The data of the next step from a measurable family of slot models. -/
lemma dfam_DM {M : JitterΩ → SlotModel X₀} (hϑ : ∀ ω, (M ω).ϑ = 1 / 2)
    (hT : ∀ x, Measurable fun ω => (M ω).T x) (hA : ∀ i, Measurable fun ω => (M ω).arr i)
    (hlow : ∀ ω, ∀ x : ℝ, x < X₀ → (M ω).T x = ⌊x⌋₊) :
    DFam fun ω => DM (M ω) (Ucl ω) := by
  refine ⟨fun k => measurableSet_placed hA k, fun k => ?_⟩
  show Measurable fun ω => primeValueOf (M ω) (capH X₀) (Ucl ω) k
  have hs := measurable_slot_fam hϑ hT (k + 1)
  have hH : Measurable fun ω => capH X₀ ((M ω).slot (k + 1)) := by
    have : (fun ω => capH X₀ ((M ω).slot (k + 1))) =
        fun ω => capH X₀ (max ((M ω).slot (k + 1)) X₀) := by
      funext ω
      rw [max_eq_left (GreedyRun.slot_ge ⟨M ω, capH X₀, Ucl ω, hlow ω⟩ (k + 1))]
    rw [this]
    exact (measurable_capH_max hc.hX).comp hs
  unfold primeValueOf landing
  exact hs.add (hH.mul ((measurable_Ucl (k + 1)).sub_const _))

/-- The step `Phi` maps measurable data to a measurable family of slot models. -/
lemma measurable_phi {D : JitterΩ → PrimeData} (hD : DFam D) (hL : ∀ ω, LocFinD (D ω))
    (hP : ∀ ω, Pos2 (D ω)) :
    (∀ x, Measurable fun ω => (Phi θ X₀ (D ω)).T x) ∧
      ∀ i, Measurable fun ω => (Phi θ X₀ (D ω)).arr i := by
  have hv : ∀ ω, TValid X₀ (targetD θ X₀ (D ω)) := fun ω =>
    tvalid_targetD hc.hθ hc.hX hc.hHB (D ω) (hL ω)
  have hTt := measurable_targetD hc.hθ hc.hX hc.hHB hD hL hP
  have hT : ∀ x, Measurable fun ω => (Phi θ X₀ (D ω)).T x := by
    intro x
    have : (fun ω => (Phi θ X₀ (D ω)).T x) = fun ω => targetD θ X₀ (D ω) x := by
      funext ω; rw [Phi_T (hv ω)]
    rw [this]
    exact hTt.comp (f := fun ω => (ω, x)) (measurable_id.prodMk measurable_const)
  refine ⟨hT, fun i => ?_⟩
  have hs : ∀ k, Measurable fun ω => (Phi θ X₀ (D ω)).slot k :=
    measurable_slot_fam (fun ω => Phi_ϑ θ (D ω)) hT
  have e : (fun ω => (Phi θ X₀ (D ω)).arr i) = fun ω => if i = 0 then 0 else
      compCount X₀ (D ω) ((Phi θ X₀ (D ω)).slot i) ((Phi θ X₀ (D ω)).slot (i + 1)) := by
    funext ω
    rw [Phi_arr (hv ω)]
    unfold arrOf
    rw [slot_eq_slotOf, slot_eq_slotOf, Phi_T (hv ω), Phi_ϑ]
  rw [e]
  split_ifs
  · exact measurable_const
  · unfold compCount
    have hm : Measurable fun ω =>
        ((compSet X₀ (D ω) ((Phi θ X₀ (D ω)).slot i) ((Phi θ X₀ (D ω)).slot (i + 1))).ncard :
          ℝ) := by
      refine measurable_ncard (fun e => ?_) (fun ω => ?_)
      · exact (hD.live_e e).inter ((MeasurableSet.const _).inter
          ((measurableSet_le (hs i) (hD.eval e)).inter (measurableSet_lt (hD.eval e) (hs (i + 1)))))
      · exact (finite_le hL hP ω ((Phi θ X₀ (D ω)).slot (i + 1))).subset
          fun e he => ⟨he.1, he.2.2.2.le⟩
    have : (fun ω => ((compSet X₀ (D ω) ((Phi θ X₀ (D ω)).slot i)
        ((Phi θ X₀ (D ω)).slot (i + 1))).ncard : ℤ)) =
        (fun r : ℝ => (⌊r⌋ : ℤ)) ∘ fun ω => ((compSet X₀ (D ω) ((Phi θ X₀ (D ω)).slot i)
          ((Phi θ X₀ (D ω)).slot (i + 1))).ncard : ℝ) := by
      funext ω; simp
    rw [this]
    exact Int.measurable_floor.comp hm

/-- **Every iterate of the construction is measurable in the jitters.** -/
theorem iterD_dfam (n : ℕ) : DFam fun ω => iterD θ X₀ (Ucl ω) n := by
  induction n with
  | zero => exact ⟨fun _ => MeasurableSet.const _, fun _ => measurable_const⟩
  | succ n ih =>
    have hL : ∀ ω, LocFinD (iterD θ X₀ (Ucl ω) n) := fun ω => (hc.std ω).locFinD_iterD n
    have hP : ∀ ω, Pos2 (iterD θ X₀ (Ucl ω) n) := by
      intro ω
      cases n with
      | zero => intro k hk; exact absurd hk (by simp [iterD, D0])
      | succ n => exact pos2_DM hc.hX (fun j => clamp01_mem _) ((hc.std ω).iterM_low n)
    obtain ⟨hT, hA⟩ := measurable_phi hc ih hL hP
    exact dfam_DM hc (M := fun ω => iterM θ X₀ (Ucl ω) n) (fun ω => Phi_ϑ θ _) hT hA
      (fun ω => (hc.std ω).iterM_low n)

lemma iterM_meas (n : ℕ) :
    (∀ x, Measurable fun ω => (iterM θ X₀ (Ucl ω) n).T x) ∧
      ∀ i, Measurable fun ω => (iterM θ X₀ (Ucl ω) n).arr i := by
  have hL : ∀ ω, LocFinD (iterD θ X₀ (Ucl ω) n) := fun ω => (hc.std ω).locFinD_iterD n
  have hP : ∀ ω, Pos2 (iterD θ X₀ (Ucl ω) n) := by
    intro ω
    cases n with
    | zero => intro k hk; exact absurd hk (by simp [iterD, D0])
    | succ n => exact pos2_DM hc.hX (fun j => clamp01_mem _) ((hc.std ω).iterM_low n)
  exact measurable_phi hc (iterD_dfam hc n) hL hP

lemma Mcl_T_meas (x : ℝ) : Measurable fun ω => (Mcl θ X₀ ω).T x := by
  have : (fun ω => (Mcl θ X₀ ω).T x) = fun ω => (iterM θ X₀ (Ucl ω) (nT X₀ x)).T x := by
    funext ω; rw [Mcl_eq hc]; rfl
  rw [this]; exact (iterM_meas hc _).1 x

lemma Mcl_arr_meas (i : ℕ) : Measurable fun ω => (Mcl θ X₀ ω).arr i := by
  have : (fun ω => (Mcl θ X₀ ω).arr i) = fun ω => (iterM θ X₀ (Ucl ω) (nA X₀ i)).arr i := by
    funext ω; rw [Mcl_eq hc]; rfl
  rw [this]; exact (iterM_meas hc _).2 i

lemma Mcl_ϑ (ω : JitterΩ) : (Mcl θ X₀ ω).ϑ = 1 / 2 := by rw [Mcl_eq hc]; rfl

/-- **The slot starts and decisions of the constructed model are measurable.** -/
theorem stageMeas : StageMeas θ X₀ :=
  ⟨measurable_slot_fam (Mcl_ϑ hc) (Mcl_T_meas hc), measurableSet_placed (Mcl_arr_meas hc)⟩

/-- **The prime data of the constructed model are measurable.** -/
theorem DF_dfam : DFam fun ω => DM (Mcl θ X₀ ω) (Ucl ω) :=
  dfam_DM hc (Mcl_ϑ hc) (Mcl_T_meas hc) (Mcl_arr_meas hc) fun ω => by
    rw [Mcl_eq hc]; exact (hc.std ω).limModel_low

end Iter

end BModel

end
