module

public import RequestProject.Beurling.Model.Causal2
public import RequestProject.Beurling.Model.Law
public import RequestProject.Beurling.Model.TopS

/-!
# The construction as an adapted process on the jitter space

For fixed admissible `θ`, `X₀` with (84) from `X₀` on (`Cond`), the constructed model is
evaluated at the clamped jitters `Ucl ω = (clamp₀₁ ω_j)_j` (equal to `ω` almost surely), so that
it is the fixed point `limModel` for **every** `ω` (`Mcl`). The data of the decision at the
relative slot `n + 1`:

* `slotF n ω = s_{n+1}`, `HF n ω = H(s_{n+1})`, the event `placedF n` that a prime is placed;
* `valF n ω = s_{n+1} + H(s_{n+1})(U_{n+1} - 1/2)`, the landing point.

Given the measurability of the slot starts and decisions (`StageMeas`), the causality of
`limModel_stage_congr` makes them **adapted**: `slotF n`, `HF n`, `placedF n` are
`F_n`-measurable, `valF n` is `F_{n+1}`-measurable (`F_n` = σ(U_j, j ≤ n), `jitterFiltration`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The fixed conditions of the construction. -/
structure Cond (θ : ℝ) (X₀ : ℕ) : Prop where
  hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)
  hX : 10 ^ 8 ≤ Real.log X₀
  hHB : ShortIntervalPNTFrom X₀

/-- The clamped jitters. -/
def Ucl (ω : JitterΩ) : ℕ → ℝ := fun j => clamp01 (ω j)

lemma Ucl_eq {ω : JitterΩ} (hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1) : Ucl ω = ω := by
  funext j; exact clamp01_eq (hω j)

lemma Cond.std (hc : Cond θ X₀) (ω : JitterΩ) : Std θ X₀ (Ucl ω) :=
  ⟨hc.hθ, hc.hX, fun _ => clamp01_mem _, hc.hHB⟩

/-- The constructed model at the clamped jitters. -/
noncomputable def Mcl (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) : SlotModel X₀ :=
  constructedModel θ X₀ (Ucl ω)

lemma Mcl_eq (hc : Cond θ X₀) (ω : JitterΩ) : Mcl θ X₀ ω = (hc.std ω).limModel :=
  constructedModel_eq _

/-- The slot start `s_{n+1}`. -/
noncomputable def slotF (θ : ℝ) (X₀ : ℕ) (n : ℕ) (ω : JitterΩ) : ℝ := (Mcl θ X₀ ω).slot (n + 1)

/-- The jitter width `H(s_{n+1})`. -/
noncomputable def HF (θ : ℝ) (X₀ : ℕ) (n : ℕ) (ω : JitterΩ) : ℝ := capH X₀ (slotF θ X₀ n ω)

/-- The event that a prime is placed at relative slot `n + 1`. -/
def placedF (θ : ℝ) (X₀ : ℕ) (n : ℕ) : Set JitterΩ := {ω | placedAt (Mcl θ X₀ ω) n}

/-- The landing point of the prime decided at relative slot `n + 1`. -/
noncomputable def valF (θ : ℝ) (X₀ : ℕ) (n : ℕ) (ω : JitterΩ) : ℝ :=
  primeValueOf (Mcl θ X₀ ω) (capH X₀) (Ucl ω) n

lemma valF_eq (n : ℕ) (ω : JitterΩ) :
    valF θ X₀ n ω = landing (slotF θ X₀ n ω) (HF θ X₀ n ω) (clamp01 (ω (n + 1))) := rfl

lemma slotF_ge (hc : Cond θ X₀) (n : ℕ) (ω : JitterΩ) : (X₀ : ℝ) ≤ slotF θ X₀ n ω := by
  unfold slotF; rw [Mcl_eq hc]
  exact GreedyRun.slot_ge ⟨_, capH X₀, Ucl ω, (hc.std ω).limModel_low⟩ (n + 1)

lemma HF_pos (hc : Cond θ X₀) (n : ℕ) (ω : JitterΩ) : 0 < HF θ X₀ n ω :=
  lt_of_lt_of_le one_pos (capH_ge_one (Nat.cast_nonneg _) hc.hX (slotF_ge hc n ω))

/-- **Measurability of the slot starts and decisions** (proved in `Model/MeasIter.lean`). -/
structure StageMeas (θ : ℝ) (X₀ : ℕ) : Prop where
  slot : ∀ k, Measurable fun ω => (Mcl θ X₀ ω).slot k
  placed : ∀ k, MeasurableSet {ω | placedAt (Mcl θ X₀ ω) k}

/-- `s ↦ H(max(s, X₀))` is measurable (`H` is non-decreasing on `[X₀, ∞)`). -/
lemma measurable_capH_max (hX : 10 ^ 8 ≤ Real.log X₀) :
    Measurable fun s => capH X₀ (max s X₀) := by
  apply Monotone.measurable
  intro a b hab
  exact capH_monotoneOn (Nat.cast_nonneg _) hX (mem_Ici.mpr (le_max_right _ _))
    (mem_Ici.mpr (le_max_right _ _)) (max_le_max hab le_rfl)

/-- **Stage `n` reads only the jitters `≤ n`.** -/
theorem Mcl_stage_congr (hc : Cond θ X₀) {n : ℕ} {ω ω' : JitterΩ}
    (h : ∀ j ≤ n, ω j = ω' j) :
    (∀ k ≤ n + 1, (Mcl θ X₀ ω).slot k = (Mcl θ X₀ ω').slot k) ∧
      (∀ k ≤ n + 1, (Mcl θ X₀ ω).arr k = (Mcl θ X₀ ω').arr k) ∧
      (∀ k ≤ n, placedAt (Mcl θ X₀ ω) k ↔ placedAt (Mcl θ X₀ ω') k) := by
  rw [Mcl_eq hc, Mcl_eq hc]
  exact limModel_stage_congr (hc.std ω) (hc.std ω') fun j hj => by
    simp only [Ucl, h j hj]

section Adapted

variable (hc : Cond θ X₀) (hm : StageMeas θ X₀)
include hc hm

omit hc in
lemma slotF_measurable (n : ℕ) : Measurable (slotF θ X₀ n) := hm.slot (n + 1)

lemma HF_measurable (n : ℕ) : Measurable (HF θ X₀ n) := by
  have : HF θ X₀ n = fun ω => capH X₀ (max (slotF θ X₀ n ω) X₀) := by
    funext ω; unfold HF; rw [max_eq_left (slotF_ge hc n ω)]
  rw [this]
  exact (measurable_capH_max hc.hX).comp (slotF_measurable hm n)

lemma valF_measurable (n : ℕ) : Measurable (valF θ X₀ n) := by
  have : valF θ X₀ n = fun ω => landing (slotF θ X₀ n ω) (HF θ X₀ n ω)
      (clamp01 (ω (n + 1))) := rfl
  rw [this]
  unfold landing
  exact (slotF_measurable hm n).add ((HF_measurable hc hm n).mul
    ((measurable_clamp01.comp (measurable_pi_apply _)).sub_const _))

/-- `s_{n+1}` is `F_n`-measurable. -/
theorem slotF_adapted (n : ℕ) : Measurable[jitterFiltration n] (slotF θ X₀ n) :=
  measurable_filtration_of_congr (slotF_measurable hm n) n fun _ _ h =>
    (Mcl_stage_congr hc h).1 (n + 1) le_rfl

/-- `H(s_{n+1})` is `F_n`-measurable. -/
theorem HF_adapted (n : ℕ) : Measurable[jitterFiltration n] (HF θ X₀ n) :=
  measurable_filtration_of_congr (HF_measurable hc hm n) n fun ω ω' h => by
    unfold HF slotF; rw [(Mcl_stage_congr hc h).1 (n + 1) le_rfl]

/-- The decision at relative slot `n + 1` is `F_n`-measurable. -/
theorem placedF_adapted (n : ℕ) : MeasurableSet[jitterFiltration n] (placedF θ X₀ n) := by
  have hmeas : Measurable ((placedF θ X₀ n).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator (hm.placed n)
  have h := measurable_filtration_of_congr hmeas n fun ω ω' hω => by
    have hiff := (Mcl_stage_congr hc hω).2.2 n le_rfl
    by_cases h1 : ω ∈ placedF θ X₀ n
    · have h2 : ω' ∈ placedF θ X₀ n := hiff.mp h1
      rw [indicator_of_mem h1, indicator_of_mem h2]
    · have h2 : ω' ∉ placedF θ X₀ n := fun h2 => h1 (hiff.mpr h2)
      rw [indicator_of_notMem h1, indicator_of_notMem h2]
  have : placedF θ X₀ n = ((placedF θ X₀ n).indicator fun _ => (1 : ℝ)) ⁻¹' {1} := by
    ext ω
    by_cases h1 : ω ∈ placedF θ X₀ n <;> simp [h1]
  rw [this]
  exact h (measurableSet_singleton _)

/-- The landing point `q_n` is `F_{n+1}`-measurable. -/
theorem valF_adapted (n : ℕ) : Measurable[jitterFiltration (n + 1)] (valF θ X₀ n) :=
  measurable_filtration_of_congr (valF_measurable hc hm n) (n + 1) fun ω ω' h => by
    rw [valF_eq, valF_eq, h (n + 1) le_rfl]
    unfold HF slotF
    rw [(Mcl_stage_congr hc fun j hj => h j (by omega)).1 (n + 1) le_rfl]

/-- The decisions at earlier slots are `F_n`-measurable. -/
theorem placedF_adapted_le {j n : ℕ} (hjn : j ≤ n) :
    MeasurableSet[jitterFiltration n] (placedF θ X₀ j) :=
  jitterFiltration.mono hjn _ (placedF_adapted hc hm j)

/-- The earlier landing points are `F_n`-measurable. -/
theorem valF_adapted_lt {j n : ℕ} (hjn : j < n) :
    Measurable[jitterFiltration n] (valF θ X₀ j) :=
  (valF_adapted hc hm j).mono (jitterFiltration.mono (by omega)) le_rfl

end Adapted

end BModel

end
