module

public import RequestProject.Beurling.Queue6.ClusterX
public import RequestProject.Beurling.Noise.TauNearProofLoc

/-!
# The decision order and the local count of the realised system (fields of `KR.TNP.Hyp`)

For the realised system `P(ω) = realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)` of the
construction (prime `j` of `P` is the realised prime `e(j)` of the enumeration
`RealisedOK.equiv`, labelled by the rational prime `qp j`, as in `Saias59.labelVal_qp`):

* `decT` : **the decision time** of a realised prime: `t(p) = p` for a rational prime `p < X₀`
  (all rational primes are decided before the first slot `s_1 > X₀`), and `t(q) = s_{k+1}`, the
  slot start, for the jittered prime decided at relative slot `k + 1`;
* `twR` : the decision time on the labels, `twR (qp j) = t(p_j)` (the convention of
  `KR.TNP.Hyp`: `tw` is evaluated at `qp j`);
* `Hc X₀ x = H(max(x, X₀))` : the jitter width `H = capH X₀`, frozen at `H(X₀)` below `X₀`
  (the slots, and so all jitter boxes, are at heights `≥ X₀`).

With `X₀⁻ = X₀ - H(X₀)/2` (`Xm X₀`):

* `dec_lo_R` : `t(p) = p` for the primes `p < X₀⁻/2` (they are rational);
* `dec_hi_R` : `|t(p) - p| ≤ H(p)` for all primes (the landing point of a jittered prime lies in
  its box `[s - H(s)/2, s + H(s)/2]`, and `H(s) ≤ H(q) + 1/4`);
* `count_R` : **Corollary 6.3(ii) in the form of `TNP.Hyp.count`**: for `p₀ ≥ X₀⁻/2`, at most
  `46 H(p₀)` primes of `P(ω)` lie in `|p - p₀| ≤ 1.71 H(p₀)`, for every `ω` all of whose stages
  are good (`SG`, an almost sure event): rational primes by the integer count, jittered primes by
  the sharp slot count `window_count_sharp` (each placed slot of a good stage has a unit jump).

The decision-order fields hold for every `ω`; the count holds on `SG` (in particular on
`Good(< t)` off a null set, at every height).
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono SlotModel Greedy
open BeurlingSystem (qp qp_injective)

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The decision time -/

/-- The decision time of a realised prime: `p` for a rational prime, the slot start `s_{k+1}`
for the jittered prime decided at relative slot `k + 1`. -/
noncomputable def decT (M : SlotModel X₀) : RealisedIdx M → ℝ
  | Sum.inl p => (p.1 : ℝ)
  | Sum.inr k => M.slot (k.1 + 1)

open Classical in
/-- The decision time on the labels `qp j` of the realised system. -/
noncomputable def twR {M : SlotModel X₀} {U : ℕ → ℝ} (h : RealisedOK M (capH X₀) U)
    (n : ℕ) : ℝ :=
  if hn : ∃ j, qp j = n then decT M (h.equiv hn.choose) else 0

lemma twR_qp {M : SlotModel X₀} {U : ℕ → ℝ} (h : RealisedOK M (capH X₀) U) (j : ℕ) :
    twR h (qp j) = decT M (h.equiv j) := by
  classical
  have hn : ∃ j', qp j' = qp j := ⟨j, rfl⟩
  unfold twR
  rw [dif_pos hn]
  congr 2
  exact qp_injective hn.choose_spec

/-- The jitter width frozen below `X₀`: `H(max(x, X₀))`. -/
noncomputable def Hc (X₀ : ℕ) (x : ℝ) : ℝ := capH X₀ (max x X₀)

section Real

variable (hc : Cond θ X₀) (ω : JitterΩ)

include hc in
/-- `RealisedOK` for the construction at every `ω`. -/
lemma hokR : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω) := by
  rw [Mcl_eq hc]; exact limModel_realisedOK (hc.std ω)

/-- The realised system of the construction. -/
noncomputable abbrev PR (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) : BeurlingSystem :=
  realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)

include hc in
lemma PR_p (j : ℕ) :
    (PR θ X₀ ω).p j = realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) ((hokR hc ω).equiv j) :=
  realisedSystem_p (hokR hc ω) j

include hc in
/-- **`dec_lo`**: the primes below `X₀⁻/2` are rational, decided at their value. -/
theorem dec_lo_R (j : ℕ) (hj : (PR θ X₀ ω).p j < Xm X₀ / 2) :
    twR (hokR hc ω) (qp j) = (PR θ X₀ ω).p j := by
  rw [twR_qp, PR_p hc ω]
  rw [PR_p hc ω] at hj
  rcases hi : (hokR hc ω).equiv j with p | k
  · rfl
  · exfalso
    rw [hi] at hj
    have h1 : Xm X₀ ≤ valF θ X₀ k.1 ω := valF_ge_Xm hc k.1 ω
    have h2 : 1 < Xm X₀ := Xm_pos hc
    simp only [realisedVal] at hj
    change valF θ X₀ k.1 ω < Xm X₀ / 2 at hj
    linarith

include hc in
/-- `H(s) ≤ H(q) + 1/4` for a slot `s ≥ X₀` whose box floor is below `q`. -/
lemma H_slot_le {s q : ℝ} (hs : (X₀ : ℝ) ≤ s) (hsq : s - capH X₀ s / 2 ≤ q) :
    capH X₀ s ≤ Hc X₀ q + 1 / 4 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  unfold Hc
  set x := max q (X₀ : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := le_max_right _ _
  rcases le_or_gt s x with h | h
  · have := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hs) (mem_Ici.mpr hxX) h
    linarith
  · have hsx : s - capH X₀ s / 2 ≤ x := le_trans hsq (le_max_left _ _)
    exact JitterRegular.capH_regular hX0 hc.hX hxX h.le hsx

include hc in
/-- **`dec_hi`**: `|t(p) - p| ≤ H(p)` for every prime of `P(ω)`. -/
theorem dec_hi_R (j : ℕ) :
    |twR (hokR hc ω) (qp j) - (PR θ X₀ ω).p j| ≤ Hc X₀ ((PR θ X₀ ω).p j) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rw [twR_qp, PR_p hc ω]
  rcases (hokR hc ω).equiv j with p | k
  · simp only [decT, realisedVal, sub_self, abs_zero]
    unfold Hc
    exact capH_nonneg _ _
  · simp only [decT, realisedVal]
    change |slotF θ X₀ k.1 ω - valF θ X₀ k.1 ω| ≤ Hc X₀ (valF θ X₀ k.1 ω)
    have hs := slotF_ge hc k.1 ω
    have hbox := landing_mem_box (s := slotF θ X₀ k.1 ω) (HF_pos hc k.1 ω).le
      (clamp01_mem (ω (k.1 + 1)))
    rw [← valF_eq] at hbox
    have hlo := hbox.1
    have hhi := hbox.2
    have hH := H_slot_le hc hs hlo
    have hH1 : 1 ≤ Hc X₀ (valF θ X₀ k.1 ω) := by
      unfold Hc; exact capH_ge_one hX0 hc.hX (le_max_right _ _)
    unfold HF at hlo hhi
    rw [abs_le]
    constructor <;> linarith

end Real

/-! ### The local count -/

section Count

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc in
/-- The width at a jittered prime of the window `|q - p₀| ≤ 1.71 H(p₀)` is at most
`2.5 H(p₀) + 1`. -/
lemma HF_le_window {p₀ : ℝ} (ω : JitterΩ) (k : ℕ)
    (hq : valF θ X₀ k ω ≤ p₀ + 1.71 * Hc X₀ p₀) :
    HF θ X₀ k ω ≤ 2.5 * Hc X₀ p₀ + 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set x := max p₀ (X₀ : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := le_max_right _ _
  set H₀ := Hc X₀ p₀
  have hH₀ : H₀ = capH X₀ x := rfl
  have hH1 : 1 ≤ H₀ := by rw [hH₀]; exact capH_ge_one hX0 hc.hX hxX
  set s := slotF θ X₀ k ω
  have hs : (X₀ : ℝ) ≤ s := slotF_ge hc k ω
  have hbox := landing_mem_box (s := s) (HF_pos hc k ω).le (clamp01_mem (ω (k + 1)))
  rw [← valF_eq] at hbox
  unfold HF
  rcases le_or_gt s x with h | h
  · have := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hs) (mem_Ici.mpr hxX) h
    rw [hH₀]; linarith
  · have hlip := capH_lip hX0 hc.hX hxX h.le
    have hhi := hbox.1
    unfold HF at hhi
    have hp : p₀ ≤ x := le_max_left _ _
    rw [← hH₀] at hlip
    linarith

/-- The jittered primes of the window `|q - p₀| ≤ 1.71 H(p₀)`. -/
def jitWin (θ : ℝ) (X₀ : ℕ) (p₀ : ℝ) (ω : JitterΩ) : Set ℕ :=
  {k : ℕ | placedAt (Mcl θ X₀ ω) k ∧ p₀ - 1.71 * Hc X₀ p₀ ≤ valF θ X₀ k ω ∧
    valF θ X₀ k ω ≤ p₀ + 1.71 * Hc X₀ p₀}

include hc in
lemma jitWin_finite (p₀ : ℝ) (ω : JitterΩ) : (jitWin θ X₀ p₀ ω).Finite := by
  refine (finite_slot_succ_le (M := Mcl θ X₀ ω) (p₀ + 1.71 * Hc X₀ p₀ +
    (2.5 * Hc X₀ p₀ + 1))).subset fun k hk => ?_
  obtain ⟨-, -, hq⟩ := hk
  have hHF := HF_le_window hc ω k hq
  have hbox := landing_mem_box (s := slotF θ X₀ k ω) (HF_pos hc k ω).le
    (clamp01_mem (ω (k + 1)))
  rw [← valF_eq] at hbox
  have hH0 := (HF_pos hc k ω).le
  show slotF θ X₀ k ω ≤ _
  linarith [hbox.1]

include hc hev in
/-- **The jittered primes of the window**: at most `2 (3.42 H(p₀) + 2(2.5 H(p₀) + 1)) + 1`,
on `SG` (the sharp slot count, `window_count_sharp`). -/
theorem jit_count_le {p₀ : ℝ} {ω : JitterΩ} (hSG : ω ∈ SG (θ := θ) (X₀ := X₀)) :
    ((jitWin θ X₀ p₀ ω).ncard : ℝ) ≤
      2 * (3.42 * Hc X₀ p₀ + 2 * (2.5 * Hc X₀ p₀ + 1)) + 1 := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set h := hc.std ω
  have hMe : Mcl θ X₀ ω = h.limModel := Mcl_eq hc ω
  set H₀ := Hc X₀ p₀
  have hH1 : 1 ≤ H₀ := by
    show 1 ≤ Hc X₀ p₀
    unfold Hc; exact capH_ge_one hX0 hc.hX (le_max_right _ _)
  have hR0 : 0 ≤ 2 * (3.42 * H₀ + 2 * (2.5 * H₀ + 1)) + 1 := by linarith
  have hH₀e : Hc X₀ p₀ = H₀ := rfl
  rcases (jitWin θ X₀ p₀ ω).eq_empty_or_nonempty with he | ⟨k0, hk0⟩
  · rw [he, Set.ncard_empty]; push_cast; linarith
  set Hm := 2.5 * H₀ + 1 with hHm
  set a := max (X₀ : ℝ) (p₀ - 1.71 * H₀ - Hm) with ha
  set b := p₀ + 1.71 * H₀ + Hm with hb
  have haX : (X₀ : ℝ) ≤ a := le_max_left _ _
  -- the slots of the window
  have hslot : ∀ k ∈ jitWin θ X₀ p₀ ω, a < slotF θ X₀ k ω ∧ slotF θ X₀ k ω ≤ b := by
    intro k hk
    obtain ⟨-, hq1, hq2⟩ := hk
    have hHF := HF_le_window hc ω k hq2
    rw [hH₀e] at hq1 hq2 hHF
    have hbox := landing_mem_box (s := slotF θ X₀ k ω) (HF_pos hc k ω).le
      (clamp01_mem (ω (k + 1)))
    rw [← valF_eq] at hbox
    have hH0 := HF_pos hc k ω
    have hX1 : (X₀ : ℝ) < slotF θ X₀ k ω := by
      have h1 := (limModel_slot_one h hev).1
      have h2 : h.limModel.slot 1 ≤ h.limModel.slot (k + 1) :=
        h.limModel.slot_mono (by omega)
      show (X₀ : ℝ) < (Mcl θ X₀ ω).slot (k + 1)
      rw [hMe]; linarith
    refine ⟨max_lt hX1 (by linarith [hbox.2]), by linarith [hbox.1]⟩
  have hab : a ≤ b := by
    have := hslot k0 hk0; linarith
  set S₀ := {m | placedAt h.limModel m ∧
    UnitJumpAt X₀ (DM h.limModel (Ucl ω)) (h.limModel.slot (m + 1))}
  have hsub : jitWin θ X₀ p₀ ω ⊆ {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b} := by
    intro k hk
    have hsl := hslot k hk
    have h1 := hk.1
    have h2 : ω ∈ stageGood θ X₀ k := by
      simp only [SG, mem_iInter] at hSG; exact hSG k
    simp only [stageGood, DF, slotF, mem_setOf_eq] at h2
    simp only [slotF] at hsl
    rw [hMe] at h1 h2 hsl
    exact ⟨⟨h1, h2⟩, hsl.1, hsl.2⟩
  have hwin := window_count_sharp h S₀ (fun m hm => hm) haX hab
  have hWfin : {m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b}.Finite :=
    (finite_slot_succ_le (M := h.limModel) _).subset fun m hm => hm.2.2
  have hc1 : ((jitWin θ X₀ p₀ ω).ncard : ℝ) ≤ ({m | m ∈ S₀ ∧ a < h.limModel.slot (m + 1) ∧
      h.limModel.slot (m + 1) ≤ b}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hWfin
  have hla : Real.log X₀ ≤ Real.log a :=
    Real.log_le_log (by linarith [X₀_ge_two_pow hc.hX]) haX
  have hlga : 10 ^ 8 ≤ Real.log a := le_trans hc.hX hla
  have hcoef : 0.02 / Real.log a ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hba : b - a ≤ 3.42 * H₀ + 2 * Hm := by
    have := le_max_right (X₀ : ℝ) (p₀ - 1.71 * H₀ - Hm); linarith
  have hba0 : 0 ≤ b - a := by linarith
  have : (1 + 0.02 / Real.log a) * (b - a) ≤ 2 * (3.42 * H₀ + 2 * Hm) := by
    have h0 : 0 ≤ 0.02 / Real.log a := div_nonneg (by norm_num) (by linarith)
    nlinarith
  linarith

include hc hev in
/-- **`count` of `KR.TNP.Hyp`** (Corollary 6.3(ii) in the form used by Lemma 5.20): on `SG`,
for every `p₀`, at most `46 H(p₀)` primes of `P(ω)` lie in `|p - p₀| ≤ 1.71 H(p₀)`. -/
theorem count_R {ω : JitterΩ} (hSG : ω ∈ SG (θ := θ) (X₀ := X₀)) (p₀ : ℝ) (hp₀ : 0 ≤ p₀) :
    (((((PR θ X₀ ω).primesLe (p₀ + 1.71 * Hc X₀ p₀)).filter
      (fun j => p₀ - 1.71 * Hc X₀ p₀ ≤ (PR θ X₀ ω).p j)).card : ℕ) : ℝ) ≤ 46 * Hc X₀ p₀ := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set H₀ := Hc X₀ p₀
  have hH1 : 1 ≤ H₀ := by
    show 1 ≤ Hc X₀ p₀
    unfold Hc; exact capH_ge_one hX0 hc.hX (le_max_right _ _)
  set S := ((PR θ X₀ ω).primesLe (p₀ + 1.71 * H₀)).filter
    (fun j => p₀ - 1.71 * H₀ ≤ (PR θ X₀ ω).p j)
  set e := (hokR hc ω).equiv
  set g : ℕ → ℕ := fun j => Sum.elim (fun p => p.1) (fun k => k.1) (e j)
  have hmem : ∀ j ∈ S, p₀ - 1.71 * H₀ ≤ (PR θ X₀ ω).p j ∧
      (PR θ X₀ ω).p j ≤ p₀ + 1.71 * H₀ := by
    intro j hj
    rw [Finset.mem_filter, BeurlingSystem.mem_primesLe] at hj
    exact ⟨hj.2, hj.1⟩
  set SL := S.filter (fun j => (e j).isLeft)
  set SR := S.filter (fun j => ¬ (e j).isLeft)
  have hsplit : S.card = SL.card + SR.card :=
    (Finset.card_filter_add_card_filter_not (s := S) (fun j => (e j).isLeft)).symm
  set lo := p₀ - 1.71 * H₀ with hlo_def
  set hi := p₀ + 1.71 * H₀ with hhi_def
  have hhi : 0 ≤ hi := by linarith
  -- the rational primes
  have hL : SL.card ≤ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).card := by
    refine Finset.card_le_card_of_injOn g (fun j hj => ?_) (fun j hj j' hj' hjj => ?_)
    · obtain ⟨hjS, hjl⟩ := Finset.mem_filter.mp hj
      obtain ⟨h1, h2⟩ := hmem j hjS
      rw [PR_p hc ω] at h1 h2
      rcases hej : e j with p | k
      · rw [hej] at h1 h2
        simp only [realisedVal] at h1 h2
        simp only [g, hej, Sum.elim_inl, Finset.coe_Icc, Set.mem_Icc, Finset.mem_Icc]
        exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
      · rw [hej] at hjl; simp at hjl
    · obtain ⟨-, hjl⟩ := Finset.mem_filter.mp hj
      obtain ⟨-, hjl'⟩ := Finset.mem_filter.mp hj'
      apply e.injective
      rcases hej : e j with p | k
      · rcases hej' : e j' with p' | k'
        · simp only [g, hej, hej', Sum.elim_inl] at hjj
          rw [Subtype.ext hjj]
        · rw [hej'] at hjl'; simp at hjl'
      · rw [hej] at hjl; simp at hjl
  have hIcc : ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).card : ℝ) ≤ hi - lo + 1 := by
    rw [Nat.card_Icc]
    have h1 := Nat.floor_le hhi
    have h2 := Nat.le_ceil lo
    rcases le_or_gt ⌈lo⌉₊ (⌊hi⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast
      rcases le_or_gt 0 lo with hlo | hlo
      · linarith
      · have : ⌈lo⌉₊ = 0 := Nat.ceil_eq_zero.mpr hlo.le
        rw [this]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
  -- the jittered primes
  have hR : (SR.card : ℝ) ≤ ((jitWin θ X₀ p₀ ω).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    have := Set.ncard_le_ncard_of_injOn g (s := (SR : Set ℕ)) (t := jitWin θ X₀ p₀ ω)
      (fun j hj => ?_) (fun j hj j' hj' hjj => ?_) (jitWin_finite hc p₀ ω)
    · exact_mod_cast this
    · obtain ⟨hjS, hjl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      obtain ⟨h1, h2⟩ := hmem j hjS
      rw [PR_p hc ω] at h1 h2
      rcases hej : e j with p | k
      · rw [hej] at hjl; simp at hjl
      · rw [hej] at h1 h2
        simp only [realisedVal] at h1 h2
        simp only [g, hej, Sum.elim_inr]
        exact ⟨k.2, h1, h2⟩
    · obtain ⟨-, hjl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
      obtain ⟨-, hjl'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hj')
      apply e.injective
      rcases hej : e j with p | k
      · rw [hej] at hjl; simp at hjl
      · rcases hej' : e j' with p' | k'
        · rw [hej'] at hjl'; simp at hjl'
        · simp only [g, hej, hej', Sum.elim_inr] at hjj
          rw [Subtype.ext hjj]
  have hJ := jit_count_le hc hev (p₀ := p₀) hSG
  have hc' : (S.card : ℝ) = SL.card + SR.card := by exact_mod_cast hsplit
  have hL' : (SL.card : ℝ) ≤ hi - lo + 1 := le_trans (by exact_mod_cast hL) hIcc
  show (S.card : ℝ) ≤ 46 * H₀
  have : hi - lo = 3.42 * H₀ := by simp only [hi, lo]; ring
  linarith

/-! ### The fields of `KR.TNP.Hyp` -/

include hc hev in
/-- **`KR.TNP.Hyp` for the realised system of the construction**, with `H = Hc X₀`,
`tw = twR`, `X₀⁻ = Xm X₀`: the fields `dec_hi`, `dec_lo`, `count` are proved (on `SG` for
`count`), and `hXm` from `log X₀ ≥ 10⁸ + 1`; the remaining inputs are (HBS) on `[1, Z]` and the
width hypotheses `PaperWidth`. -/
theorem tnpHyp_R {ω : JitterΩ} (hSG : ω ∈ SG (θ := θ) (X₀ := X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {Z η1 η2 ε θ' : ℝ}
    {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1)
    (hwidth : KR.PaperWidth (Hc X₀) (Xm X₀) ε θ') :
    KR.TNP.Hyp (PR θ X₀ ω) (Hc X₀) (twR (hokR hc ω)) (Xm X₀) Z η1 η2 ε1 ε θ' where
  hbs := hbs
  hXm := by
    have h1 := log_Xm_ge (hc := hc)
    have h2 : Real.exp (-0.98 * Real.log X₀) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hc.hX]
    linarith
  width := hwidth
  dec_hi := fun j _ => dec_hi_R hc ω j
  dec_lo := fun j hj => dec_lo_R hc ω j hj
  count := fun p0 hp0 => count_R hc hev hSG p0 (by
    have := Xm_pos hc; linarith)

end Count

end Queue6

end
