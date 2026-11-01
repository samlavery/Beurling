module

public import RequestProject.Beurling.Model.JLaw
public import RequestProject.Beurling.Model.SlotsSharp

/-!
# The construction as a jitter law with the paper's slot constant `θ = 1 + 1/Λ`

The stopped process of §3 (Remark "the stopped process"): a slot counts as decided for the
abstract law only while the target is still controlled at its start. The event of the law at
relative slot `n + 1` is

  `lawB n` = "a prime is placed, `s_{n+1}` carries a unit jump, and `T(s_{n+1}) ≤ 3 s_{n+1}`",

which is `F_n`-measurable. With it:

* `constructionLaw2` : an instance of `RankFull.JitterLaw` with `θ = 1 + 1/Λ`, `Λ = log X₀`
  (standing fact (F1): at most `H(1 + κ₊/log) + 3` decided boxes contain a point, each of weight
  `1/H`; here from the sharp slot density `window_count_sharp`);
* the hypotheses of `RankFull.Config.skeletonBound_jitter`: decided values `> 1` (`law2_hq`), a
  decided value below `V` has slot index `≤ 24V/7` (`law2_hsmax`), the label bound
  `τ_j ≤ q_n` when `j` decided slots precede `n` (`law2_hτ`, `τ_j = max(X₀⁻, (j + 1)/2)`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Construction RankFull CaplLink SlotModel Greedy
  QueueMono
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The target is controlled at the start of relative slot `n + 1`. -/
def tStage (θ : ℝ) (X₀ : ℕ) (n : ℕ) : Set JitterΩ :=
  {ω | (Mcl θ X₀ ω).T (slotF θ X₀ n ω) ≤ 3 * slotF θ X₀ n ω}

/-- **The event of the stopped law.** -/
def lawB (θ : ℝ) (X₀ : ℕ) (n : ℕ) : Set JitterΩ := lawA θ X₀ n ∩ tStage θ X₀ n

section Law2

variable (hc : Cond θ X₀)
include hc

lemma measurable_McT : Measurable fun p : JitterΩ × ℝ => (Mcl θ X₀ p.1).T p.2 :=
  measurable_uncurry_of_rcont (f := fun ω x => (Mcl θ X₀ ω).T x) (Mcl_T_meas hc)
    fun ω x => (Mcl θ X₀ ω).T_rcont x

lemma tStage_measurable (n : ℕ) : MeasurableSet (tStage θ X₀ n) := by
  have hs := slotF_measurable (stageMeas hc) n
  have hT : Measurable fun ω => (Mcl θ X₀ ω).T (slotF θ X₀ n ω) :=
    (measurable_McT hc).comp (measurable_id.prodMk hs)
  exact measurableSet_le hT (hs.const_mul 3)

lemma tStage_adapted (n : ℕ) : MeasurableSet[jitterFiltration n] (tStage θ X₀ n) := by
  have hmeas : Measurable ((tStage θ X₀ n).indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator (tStage_measurable hc n)
  have hiff : ∀ ω ω' : JitterΩ, (∀ j ≤ n, ω j = ω' j) →
      (ω ∈ tStage θ X₀ n ↔ ω' ∈ tStage θ X₀ n) := by
    intro ω ω' hω
    have hs : slotF θ X₀ n ω = slotF θ X₀ n ω' := (Mcl_stage_congr hc hω).1 (n + 1) le_rfl
    have hT : (Mcl θ X₀ ω).T (slotF θ X₀ n ω) = (Mcl θ X₀ ω').T (slotF θ X₀ n ω) := by
      rw [Mcl_eq hc, Mcl_eq hc]
      refine limModel_T_congr (n := n) (hc.std ω) (hc.std ω')
        (fun j (hj : j ≤ n) => by simp only [Ucl, hω j hj]) ?_
      unfold slotF; rw [Mcl_eq hc]
    simp only [tStage, mem_setOf_eq]
    rw [hT, hs]
  have h := measurable_filtration_of_congr hmeas n fun ω ω' hω => by
    by_cases h1 : ω ∈ tStage θ X₀ n
    · rw [indicator_of_mem h1, indicator_of_mem ((hiff ω ω' hω).mp h1)]
    · rw [indicator_of_notMem h1, indicator_of_notMem fun h2 => h1 ((hiff ω ω' hω).mpr h2)]
  have : tStage θ X₀ n = ((tStage θ X₀ n).indicator fun _ => (1 : ℝ)) ⁻¹' {1} := by
    ext ω; by_cases h1 : ω ∈ tStage θ X₀ n <;> simp [h1]
  rw [this]
  exact h (measurableSet_singleton _)

theorem lawB_adapted (n : ℕ) : MeasurableSet[jitterFiltration n] (lawB θ X₀ n) :=
  (lawA_adapted hc n).inter (tStage_adapted hc n)

theorem law2_dens (n : ℕ) (Φ : JitterΩ × ℝ → ℝ≥0∞) (hΦ : JMeas (jitterFiltration n) Φ) :
    ∫⁻ ω, (lawB θ X₀ n).indicator (fun ω => Φ (ω, valF θ X₀ n ω)) ω ∂jitterMeasure ≤
      ∫⁻ ω, (lawB θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
        ∫⁻ t in box (slotF θ X₀ n ω) (HF θ X₀ n ω), Φ (ω, t)) ω ∂jitterMeasure :=
  le_of_eq (lintegral_landing n (slotF_adapted hc (stageMeas hc) n)
    (HF_adapted hc (stageMeas hc) n) (HF_pos hc n) (lawB_adapted hc n) hΦ)

/-- The decided boxes containing a point start within `H₀ + 1` of the first one. -/
lemma box_spread2 {s₀ s t : ℝ} (hs₀ : (X₀ : ℝ) ≤ s₀) (hss : s₀ ≤ s)
    (ht₀ : t ∈ box s₀ (capH X₀ s₀)) (ht : t ∈ box s (capH X₀ s)) :
    s - s₀ ≤ capH X₀ s₀ + 1 := by
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

/-- **(F1) with `θ = 1 + 1/Λ`.** -/
theorem law2_slots (ω : JitterΩ) (t : ℝ) :
    ∑' n, (lawB θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 t) ω ≤
        ENNReal.ofReal (1 + 1 / Real.log X₀) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hΛ : 10 ^ 8 ≤ Real.log X₀ := hc.hX
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set N := {n | ω ∈ lawB θ X₀ n ∧ t ∈ box (slotF θ X₀ n ω) (HF θ X₀ n ω)} with hN
  have hf : ∀ n, (lawB θ X₀ n).indicator (fun ω => ENNReal.ofReal (HF θ X₀ n ω)⁻¹ *
      (box (slotF θ X₀ n ω) (HF θ X₀ n ω)).indicator 1 t) ω =
      if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0 := by
    intro n
    by_cases h1 : ω ∈ lawB θ X₀ n
    · by_cases h2 : t ∈ box (slotF θ X₀ n ω) (HF θ X₀ n ω)
      · simp [hN, h1, h2]
      · simp [hN, h2]
    · simp [hN, h1]
  simp_rw [hf]
  rcases N.eq_empty_or_nonempty with hN0 | hNne
  · simp [hN0]
  have hex : ∃ n, n ∈ N := hNne
  set n₀ := Nat.find hex
  have hn₀ : n₀ ∈ N := Nat.find_spec hex
  set s₀ := slotF θ X₀ n₀ ω
  have hs₀X : (X₀ : ℝ) ≤ s₀ := slotF_ge hc n₀ ω
  set H₀ := capH X₀ s₀
  have hH0 : 200 * Real.log X₀ + 200 ≤ H₀ := by
    have := log_le_capH hX0 hc.hX hs₀X
    have : Real.log X₀ ≤ Real.log s₀ :=
      Real.log_le_log (by linarith [X₀_ge_two_pow hc.hX]) hs₀X
    linarith
  have hmono : ∀ n ∈ N, s₀ ≤ slotF θ X₀ n ω := fun n hn =>
    (Mcl θ X₀ ω).slot_mono (by have := Nat.find_min' hex hn; omega)
  have hspread : ∀ n ∈ N, slotF θ X₀ n ω ≤ s₀ + (H₀ + 1) := fun n hn => by
    have := box_spread2 hc hs₀X (hmono n hn) hn₀.2 hn.2
    linarith
  have hHn : ∀ n ∈ N, H₀ ≤ HF θ X₀ n ω := fun n hn =>
    capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hs₀X) (mem_Ici.mpr (slotF_ge hc n ω)) (hmono n hn)
  set S₀ := {m | ω ∈ lawB θ X₀ m}
  have hS₀ : ∀ m ∈ S₀, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1)) := by
    intro m hm
    have h1 := hm.1.1
    have h2 := hm.1.2
    simp only [placedF, stageGood, DF, slotF, mem_setOf_eq] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨h1, h2⟩
  -- the window `(a, s₀ + H₀ + 1]`, `a = max(s₀ - 1, X₀)`
  set a := max (s₀ - 1) (X₀ : ℝ)
  have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hslot1 := (limModel_slot_one h hev).1
  have hNsub : N ⊆ {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (H₀ + 1)} := by
    intro n hn
    have h1 := hmono n hn
    have h2 := hspread n hn
    have h3 : (X₀ : ℝ) < h.limModel.slot (n + 1) :=
      lt_of_lt_of_le hslot1 (h.limModel.slot_mono (by omega))
    simp only [slotF] at h1 h2
    rw [hMe] at h1 h2
    exact ⟨hn.1, max_lt (by linarith) h3, h2⟩
  have hab : a ≤ s₀ + (H₀ + 1) := max_le (by linarith) (by linarith [capH_nonneg (X₀ : ℝ) s₀])
  have hwin := window_count_sharp h S₀ hS₀ haX hab
  have hWfin : {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (H₀ + 1)}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hNfin : N.Finite := hWfin.subset hNsub
  have hc1 : (N.ncard : ℝ) ≤ ({m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ s₀ + (H₀ + 1)}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hNsub hWfin
  have hlen : s₀ + (H₀ + 1) - a ≤ H₀ + 2 := by
    have := le_max_left (s₀ - 1) (X₀ : ℝ); linarith
  have hla : Real.log X₀ ≤ Real.log a :=
    Real.log_le_log (by linarith [X₀_ge_two_pow hc.hX]) haX
  have hcoef : 0.02 / Real.log a ≤ 0.02 / Real.log X₀ :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hla
  have hcard : (N.ncard : ℝ) ≤ (1 + 0.02 / Real.log X₀) * (H₀ + 2) + 1 := by
    have h0 : 0 ≤ s₀ + (H₀ + 1) - a := by linarith
    have : (1 + 0.02 / Real.log a) * (s₀ + (H₀ + 1) - a) ≤
        (1 + 0.02 / Real.log X₀) * (H₀ + 2) :=
      mul_le_mul (by linarith) hlen h0 (by positivity)
    linarith
  have hsum : ∑' n, (if n ∈ N then ENNReal.ofReal (HF θ X₀ n ω)⁻¹ else 0) ≤
      ∑' n, (if n ∈ N then ENNReal.ofReal H₀⁻¹ else 0) := by
    refine ENNReal.tsum_le_tsum fun n => ?_
    split_ifs with hn
    · exact ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ X₀
        by linarith [X₀_ge_two_pow hc.hX])]) (hHn n hn))
    · exact le_rfl
  refine hsum.trans ?_
  rw [tsum_eq_sum (s := hNfin.toFinset) (fun n hn => by
    simp only [Set.Finite.mem_toFinset] at hn; simp [hn])]
  rw [Finset.sum_congr rfl (fun b hb => if_pos ((Set.Finite.mem_toFinset _).mp hb)),
    Finset.sum_const, nsmul_eq_mul]
  rw [← Set.ncard_eq_toFinset_card N hNfin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hH0' : 0 < H₀ := by nlinarith
  rw [← div_eq_mul_inv, div_le_iff₀ hH0']
  -- `((1 + 0.02/Λ)(H₀ + 2) + 1) ≤ (1 + 1/Λ) H₀`
  have e1 : (1 + 0.02 / Real.log X₀) * (H₀ + 2) + 1 =
      H₀ + 3 + 0.02 * H₀ / Real.log X₀ + 0.04 / Real.log X₀ := by ring
  have e2 : (1 + 1 / Real.log X₀) * H₀ = H₀ + H₀ / Real.log X₀ := by ring
  have h3 : 3 + 0.04 / Real.log X₀ ≤ 0.98 * H₀ / Real.log X₀ := by
    have e : 0.98 * H₀ / Real.log X₀ - (3 + 0.04 / Real.log X₀) =
        (0.98 * H₀ - 3 * Real.log X₀ - 0.04) / Real.log X₀ := by field_simp; ring
    have : 0 ≤ (0.98 * H₀ - 3 * Real.log X₀ - 0.04) / Real.log X₀ :=
      div_nonneg (by nlinarith) hΛ0.le
    linarith
  have h4 : 0.02 * H₀ / Real.log X₀ + 0.98 * H₀ / Real.log X₀ = H₀ / Real.log X₀ := by ring
  linarith

/-- **The construction as a jitter law with `θ = 1 + 1/Λ`** (§6.1, (F1)–(F2)). -/
noncomputable def constructionLaw2 :
    JitterLaw JitterΩ jitterMeasure (ENNReal.ofReal (1 + 1 / Real.log X₀)) where
  F n := jitterFiltration n
  F_mono := fun _ _ h => jitterFiltration.mono h
  F_le n := jitterFiltration.le n
  A := lawB θ X₀
  q := valF θ X₀
  c := slotF θ X₀
  H := HF θ X₀
  A_meas := lawB_adapted hc
  q_meas := valF_adapted hc (stageMeas hc)
  c_meas := slotF_adapted hc (stageMeas hc)
  H_meas := HF_adapted hc (stageMeas hc)
  H_pos := HF_pos hc
  dens := law2_dens hc
  slots := law2_slots hc hev

end Law2

end BModel

end
