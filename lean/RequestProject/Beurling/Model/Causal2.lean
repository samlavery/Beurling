module

public import RequestProject.Beurling.Model.Fix

/-!
# Causality in the jitters: the decision at a slot reads only the earlier jitters

Lemma 3.5 and Lemma 3.2 say that the decision at slot `j` and the slot start `s_j` are
`𝓕_{s_j-}`-measurable: they read only the jitters of the earlier slots. Here this is proved
pathwise for the constructed model (`limModel_stage_congr`): if two jitter sequences agree on the
indices `≤ n`, the constructed models have the same slot starts `s_1, …, s_{n+1}`, the same
arrivals `A_1, …, A_{n+1}` and the same decisions at the relative slots `1, …, n + 1`.

The step is a refinement of `causal` with two jitter sequences (`causal2`): the prime data are
compared only below the cut `y - H(y)` (`cut2`), which is enough for the target up to `y + 1`
(the gaps `2H` of `x⁺_k` and `H(s)/2` of the landing box), and only reads the jitters of the slots
starting below the cut.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono

namespace BModel

variable {X₀ : ℕ}

/-- The cut `y - max(H(y), 13 log y)` below which the prime data are compared. -/
noncomputable def cut2 (X₀ : ℕ) (y : ℝ) : ℝ := y - max (capH X₀ y) (13 * Real.log y)

/-- The height up to which the prime data agree. -/
noncomputable def height2 (X₀ : ℕ) (y : ℝ) : ℝ := boxFloor X₀ (max (cut2 X₀ y) X₀) - 1 / 8

/-- `H(s) ≤ H(x) + (s - x)/(2H(x)) + 1/4` for `X₀ ≤ x ≤ s`. -/
theorem capH_lip2 (hX : 10 ^ 8 ≤ Real.log X₀) {x s : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxs : x ≤ s) :
    capH X₀ s ≤ capH X₀ x + (s - x) / (2 * capH X₀ x) + 1 / 4 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hH1 := capH_ge_one hX0 hX hx
  set n := ⌈(s - x) / (capH X₀ x / 2)⌉₊ with hn
  have hn1 : (s - x) / (capH X₀ x / 2) ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < (s - x) / (capH X₀ x / 2) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) (by linarith))
  have hsle : s ≤ x + n * (capH X₀ x / 2) := by
    rw [div_le_iff₀ (by linarith)] at hn1; linarith
  have h := capH_steps hX0 hX hx n s hxs hsle
  have e : (s - x) / (capH X₀ x / 2) / 4 = (s - x) / (2 * capH X₀ x) := by
    field_simp; ring
  linarith

/-- **Agreeing models with jitters agreeing below the cut have agreeing prime data.** -/
theorem dagree2 (hX : 10 ^ 8 ≤ Real.log X₀) {U U' : ℕ → ℝ}
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hU' : ∀ j, U' j ∈ Icc (0 : ℝ) 1) {M M' : SlotModel X₀}
    (hM : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (hM' : ∀ x : ℝ, x < X₀ → M'.T x = ⌊x⌋₊)
    {y : ℝ} (hy : 1 ≤ y) (h : MAgree M M' y)
    (hUU : ∀ k, M.slot (k + 1) ≤ cut2 X₀ y → U (k + 1) = U' (k + 1)) :
    DAgree (DM M U) (DM M' U') (height2 X₀ y) := by
  classical
  obtain ⟨hϑ, hT, harr⟩ := h
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  set w := cut2 X₀ y with hw
  have hwy : w ≤ y - 13 * Real.log y := by
    rw [hw]; unfold cut2; linarith [le_max_right (capH X₀ y) (13 * Real.log y)]
  set m := max w X₀ with hm
  have hK := slots_unbounded M w
  set K := Nat.find hK with hKdef
  have hlt : ∀ k < K, M.slot (k + 1) ≤ w := fun k hk => by
    have := Nat.find_min hK hk; push_neg at this; exact this
  have hfloor : ∀ (N : SlotModel X₀) (V : ℕ → ℝ), (∀ j, V j ∈ Icc (0 : ℝ) 1) →
      (∀ x : ℝ, x < X₀ → N.T x = ⌊x⌋₊) → ∀ k,
      w < N.slot (k + 1) → height2 X₀ y ≤ primeValueOf N (capH X₀) V k := by
    intro N V hV hN k hk
    have hs : (X₀ : ℝ) ≤ N.slot (k + 1) := GreedyRun.slot_ge ⟨N, capH X₀, V, hN⟩ (k + 1)
    have hms : m ≤ N.slot (k + 1) := max_le hk.le hs
    have h1 := (landing_mem_box (s := N.slot (k + 1)) (capH_nonneg X₀ (N.slot (k + 1)))
      (hV (k + 1))).1
    have h2 := floor_quasi_mono hX0 hX (le_max_right w (X₀ : ℝ)) hms
    unfold height2 boxFloor
    unfold primeValueOf
    rw [← hw, ← hm]
    linarith
  refine ⟨K, fun k hk => ?_, fun k hk _ => ?_, fun k hk _ => ?_⟩
  · have hsk := hlt k hk
    have hsy : M.slot (k + 1) ≤ y := hsk.trans (by linarith)
    have he := slot_congr hϑ hT hsy
    refine ⟨?_, ?_⟩
    · show placedAt M k ↔ placedAt M' k
      unfold placedAt
      rw [greedyPrime_congr (A := M.arr) (A' := M'.arr) fun i hi =>
        harr i ((M.slot_mono hi).trans (hsk.trans hwy))]
    · show primeValueOf M (capH X₀) U k = primeValueOf M' (capH X₀) U' k
      unfold primeValueOf
      rw [he, hUU k hsk]
  · have : w < M.slot (k + 1) := by
      have h1 := Nat.find_spec hK
      exact lt_of_lt_of_le h1 (M.slot_mono (by omega))
    exact hfloor M U hU hM k this
  · have : w < M'.slot (k + 1) := by
      by_contra hc
      push_neg at hc
      have he := slot_congr hϑ.symm (fun x hx => (hT x hx).symm) (k := k + 1) (by linarith)
      have h1 := Nat.find_spec hK
      have h2 : M.slot (K + 1) ≤ M.slot (k + 1) := M.slot_mono (by omega)
      rw [he] at h2
      linarith
    exact hfloor M' U' hU' hM' k this

section Heights

variable (hX : 10 ^ 8 ≤ Real.log X₀)
include hX

lemma cut2_eq {y : ℝ} (hy : (X₀ : ℝ) ≤ y) : cut2 X₀ y = y - capH X₀ y := by
  have := log_le_capH (Nat.cast_nonneg _) hX hy
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith [X₀_ge_two_pow hX])
  unfold cut2; rw [max_eq_left (by linarith)]

/-- `z/2 + 1/8 ≤ height2 (z - 1) ≤ z`. -/
lemma height2_bounds {z : ℝ} (hz : (X₀ : ℝ) ≤ z) :
    z / 2 + 1 / 8 ≤ height2 X₀ (z - 1) ∧ height2 X₀ (z - 1) ≤ z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hX
  set m := max (cut2 X₀ (z - 1)) (X₀ : ℝ) with hm
  have hmX : (X₀ : ℝ) ≤ m := le_max_right _ _
  have hb := boxFloor_ge hX hmX
  have hH := capH_nonneg (X₀ : ℝ) m
  have hlz : 0 ≤ Real.log (z - 1) := Real.log_nonneg (by linarith)
  have hcut : cut2 X₀ (z - 1) ≤ z - 1 := by
    unfold cut2; linarith [le_max_right (capH X₀ (z - 1)) (13 * Real.log (z - 1))]
  have hmz : m ≤ z := max_le (by linarith) hz
  -- `m ≥ 3(z-1)/4`
  have hm34 : 3 / 4 * (z - 1) ≤ m := by
    rcases le_or_gt (X₀ : ℝ) (z - 1) with h1 | h1
    · have h4 := four_capH_le hX0 hX h1
      obtain ⟨hl8, -, -⟩ := logs_of_ge hX0 hX h1
      have hlog := one_add_log_le (by linarith) hl8
      have : cut2 X₀ (z - 1) ≥ 3 / 4 * (z - 1) := by
        unfold cut2
        have := max_le (show capH X₀ (z - 1) ≤ (z - 1) / 4 by linarith)
          (show 13 * Real.log (z - 1) ≤ (z - 1) / 4 by linarith)
        linarith
      exact this.trans (le_max_left _ _)
    · linarith
  unfold height2
  rw [← hm]
  constructor
  · nlinarith
  · unfold boxFloor; linarith

/-- **The heights read by the oscillation are below `height2`**. -/
theorem gap_gamma2 {a xp z : ℝ} (ha : (X₀ : ℝ) ≤ a) (haH : a + 2 * capH X₀ a ≤ xp + 3)
    (hxz : xp < z) : a < height2 X₀ (z - 1) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hX
  have hH1 := log_le_capH hX0 hX ha
  have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  set y := z - 1 with hy
  have hya : a ≤ y := by linarith
  have hyX : (X₀ : ℝ) ≤ y := ha.trans hya
  have hlip := capH_lip2 hX ha hya
  have hHa : 200 ≤ capH X₀ a := by linarith
  have hfrac : (y - a) / (2 * capH X₀ a) ≤ (y - a) / 400 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have hcut : a ≤ y - capH X₀ y := by nlinarith
  set m := max (y - capH X₀ y) (X₀ : ℝ) with hm
  have hma : y - capH X₀ y ≤ m := le_max_left _ _
  have hq := floor_quasi_mono hX0 hX ha (hcut.trans hma)
  unfold height2 boxFloor
  rw [cut2_eq hX hyX, ← hm]
  nlinarith

end Heights

/-- **Causality with two jitter sequences.** -/
theorem causal2 {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 2) (hX : 10 ^ 8 ≤ Real.log X₀)
    {U U' : ℕ → ℝ} (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hU' : ∀ j, U' j ∈ Icc (0 : ℝ) 1)
    (hV : ValidHyp θ X₀) (hS : SlopeHyp θ X₀)
    {M M' : SlotModel X₀} (hM : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊)
    (hM' : ∀ x : ℝ, x < X₀ → M'.T x = ⌊x⌋₊) {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
    (h : MAgree M M' (z - 1))
    (hUU : ∀ k, M.slot (k + 1) ≤ cut2 X₀ (z - 1) → U (k + 1) = U' (k + 1)) :
    MAgree (Phi θ X₀ (DM M U)) (Phi θ X₀ (DM M' U')) z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hX
  set D := DM M U with hD
  set D' := DM M' U' with hD'
  have hy : 1 ≤ z - 1 := by linarith
  have hDA := dagree2 hX hU hU' hM hM' hy h hUU
  obtain ⟨hY1, hY2⟩ := height2_bounds hX hz
  have hP := pos2_DM hX hU hM
  have hP' := pos2_DM hX hU' hM'
  have hzθ : z ^ (θ / 2) ≤ z := by
    have : z ^ (θ / 2) ≤ z ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rwa [Real.rpow_one] at this
  have hzθ0 : 0 ≤ z ^ (θ / 2) := Real.rpow_nonneg (by linarith) _
  have hTeq : ∀ x ≤ z, targetD θ X₀ D x = targetD θ X₀ D' x := by
    intro x hx
    refine targetD_congr hθ0 hX hP.pos hP'.pos hDA (by linarith) hY2 le_rfl (fun n hn => ?_)
      (fun j hj => ?_) hx
    · have h1 := absorbY_le_sqrt hX0 hX (x := z + z ^ (θ / 2)) (by linarith) hn
      have h2 := rpow_half_le (x := z + z ^ (θ / 2)) (z := z) (by linarith) (by linarith)
      linarith
    · obtain ⟨hXa, -, -, -⟩ := constructionScale_spec hX0 hX j
      exact gap_gamma2 hX hXa (scale_add_two_capH_le hX0 hX j) hj
  have hLD := locFinD_DM hX hU M
  have hLD' := locFinD_DM hX hU' M'
  have hv := hV D hLD
  have hv' := hV D' hLD'
  refine ⟨by rw [Phi_ϑ, Phi_ϑ], fun x hx => by rw [Phi_T hv, Phi_T hv']; exact hTeq x hx,
    fun i hi => ?_⟩
  have hTz : ∀ x ≤ z, (Phi θ X₀ D).T x = (Phi θ X₀ D').T x := fun x hx => by
    rw [Phi_T hv, Phi_T hv']; exact hTeq x hx
  have hϑ : (Phi θ X₀ D).ϑ = (Phi θ X₀ D').ϑ := by rw [Phi_ϑ, Phi_ϑ]
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hsi : (Phi θ X₀ D).slot i ≤ z := by linarith
  have hsi1 := slot_succ_le hX hS hLD hv hz hi
  have he0 := slot_congr hϑ hTz hsi
  have he1 := slot_congr hϑ hTz hsi1
  rw [Phi_arr hv, Phi_arr hv']
  unfold arrOf
  split_ifs with hi0
  · rfl
  · have e0 : slotOf X₀ (1 / 2) (targetD θ X₀ D) i = (Phi θ X₀ D).slot i := by
      rw [slot_eq_slotOf, Phi_T hv, Phi_ϑ]
    have e1 : slotOf X₀ (1 / 2) (targetD θ X₀ D) (i + 1) = (Phi θ X₀ D).slot (i + 1) := by
      rw [slot_eq_slotOf, Phi_T hv, Phi_ϑ]
    have e0' : slotOf X₀ (1 / 2) (targetD θ X₀ D') i = (Phi θ X₀ D').slot i := by
      rw [slot_eq_slotOf, Phi_T hv', Phi_ϑ]
    have e1' : slotOf X₀ (1 / 2) (targetD θ X₀ D') (i + 1) = (Phi θ X₀ D').slot (i + 1) := by
      rw [slot_eq_slotOf, Phi_T hv', Phi_ϑ]
    rw [e0, e1, e0', e1', he0, he1]
    exact compCount_eq_of_agree2 hDA hP hP' (by linarith)

/-! ### The constructed model reads the jitters causally -/

section Stage

variable {θ : ℝ} {U U' : ℕ → ℝ} (h : Std θ X₀ U) (h' : Std θ X₀ U')

include h in
/-- The limit model agrees with its next step at every height. -/
lemma limModel_fix_agree {y : ℝ} (hy : 13 ≤ y) :
    MAgree h.limModel (Phi θ X₀ (DM h.limModel U)) y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (y - X₀ + 2)
  have hy' : y ≤ hor X₀ (n + 1) := by unfold hor; push_cast; linarith
  exact ((h.limModel_step_agree n).symm (by linarith)).mono hy hy'

include h h' in
/-- **The constructed models of two jitter sequences agreeing on the indices `≤ n` agree up to
height `s_{n+1} + H(s_{n+1})/2`.** -/
theorem limModel_agree_jitters {n : ℕ} (hUU : ∀ j ≤ n, U j = U' j) :
    ∀ m : ℕ, hor X₀ m ≤ h.limModel.slot (n + 1) + capH X₀ (h.limModel.slot (n + 1)) / 2 →
      MAgree h.limModel h'.limModel (hor X₀ m) := by
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := h.X₀_big
  have hsX : (X₀ : ℝ) ≤ h.limModel.slot (n + 1) :=
    GreedyRun.slot_ge ⟨h.limModel, capH X₀, U, h.limModel_low⟩ (n + 1)
  intro m
  induction m with
  | zero =>
    intro _
    have he : hor X₀ 0 = (X₀ : ℝ) - 1 := by simp [hor]
    refine ⟨by rw [h.limModel_ϑ, h'.limModel_ϑ], fun x hx => ?_, fun i hi => ?_⟩
    · rw [he] at hx
      rw [h.limModel_low x (by linarith), h'.limModel_low x (by linarith)]
    · exfalso
      have hs : (X₀ : ℝ) ≤ h.limModel.slot i :=
        GreedyRun.slot_ge ⟨h.limModel, capH X₀, U, h.limModel_low⟩ i
      rw [he] at hi
      have : 0 ≤ Real.log ((X₀ : ℝ) - 1) := Real.log_nonneg (by linarith)
      linarith
  | succ m ih =>
    intro hm
    have hmm : hor X₀ m ≤ hor X₀ (m + 1) := by unfold hor; push_cast; linarith
    have IH := ih (hmm.trans hm)
    have hz : (X₀ : ℝ) ≤ hor X₀ (m + 1) := by unfold hor; push_cast; linarith
    have e : hor X₀ (m + 1) - 1 = hor X₀ m := by unfold hor; push_cast; ring
    have hUU' : ∀ k, h.limModel.slot (k + 1) ≤ cut2 X₀ (hor X₀ (m + 1) - 1) →
        U (k + 1) = U' (k + 1) := by
      intro k hk
      apply hUU
      by_contra hkn
      push_neg at hkn
      have hsk : h.limModel.slot (n + 1) ≤ h.limModel.slot (k + 1) :=
        h.limModel.slot_mono (by omega)
      have hcut : cut2 X₀ (hor X₀ (m + 1) - 1) < h.limModel.slot (n + 1) := by
        rw [e]
        rcases le_or_gt (hor X₀ m) (h.limModel.slot (n + 1)) with h1 | h1
        · have : 0 < max (capH X₀ (hor X₀ m)) (13 * Real.log (hor X₀ m)) :=
            lt_of_lt_of_le (Real.exp_pos _) ((le_max_left _ _).trans (le_max_left _ _))
          unfold cut2; linarith
        · have hHm := capH_monotoneOn hX0 hX (mem_Ici.mpr hsX)
            (mem_Ici.mpr (hsX.trans h1.le)) h1.le
          unfold cut2
          have := le_max_left (capH X₀ (hor X₀ m)) (13 * Real.log (hor X₀ m))
          have hH1 := capH_ge_one hX0 hX hsX
          have hm2 : hor X₀ m ≤ h.limModel.slot (n + 1) +
              capH X₀ (h.limModel.slot (n + 1)) / 2 - 1 := by
            have := hm; unfold hor at this ⊢; push_cast at this; linarith
          linarith
      linarith
    have hstep := causal2 (by linarith [h.hθ.1]) (by linarith [h.hθ.2]) hX h.hU h'.hU h.hV h.hS
      h.limModel_low h'.limModel_low hz (by rw [e]; exact IH) hUU'
    have hz13 : 13 ≤ hor X₀ (m + 1) := by linarith
    exact ((limModel_fix_agree h hz13).trans (by linarith) hstep).trans (by linarith)
      ((limModel_fix_agree h' hz13).symm (by linarith))

include h h' in
/-- **Stage `n` of the constructed model reads only the jitters of index `≤ n`**: the slot starts
`s_k`, `k ≤ n + 1`, the arrivals `A_k`, `k ≤ n + 1`, and the decisions at the relative slots
`k + 1 ≤ n + 1` agree. -/
theorem limModel_stage_congr {n : ℕ} (hUU : ∀ j ≤ n, U j = U' j) :
    (∀ k ≤ n + 1, h.limModel.slot k = h'.limModel.slot k) ∧
      (∀ k ≤ n + 1, h.limModel.arr k = h'.limModel.arr k) ∧
      (∀ k ≤ n, placedAt h.limModel k ↔ placedAt h'.limModel k) := by
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := h.X₀_big
  set M := h.limModel
  set M' := h'.limModel
  set s := M.slot (n + 1) with hsdef
  have hsX : (X₀ : ℝ) ≤ s := GreedyRun.slot_ge ⟨M, capH X₀, U, h.limModel_low⟩ (n + 1)
  have hH := log_le_capH hX0 hX hsX
  have hls : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  set m := ⌊s + capH X₀ s / 2 - X₀ + 1⌋₊ with hmdef
  have hm0 : 0 ≤ s + capH X₀ s / 2 - X₀ + 1 := by linarith [capH_nonneg (X₀ : ℝ) s]
  have hm1 : hor X₀ m ≤ s + capH X₀ s / 2 := by
    unfold hor; have := Nat.floor_le hm0; linarith
  have hm2 : s + capH X₀ s / 2 < hor X₀ m + 1 := by
    unfold hor; have := Nat.lt_floor_add_one (s + capH X₀ s / 2 - X₀ + 1); linarith
  have hag := limModel_agree_jitters h h' hUU m hm1
  obtain ⟨hϑ, hT, harr⟩ := hag
  set y := hor X₀ m
  -- `s ≤ y - 13 log y`
  have hy13 : s ≤ y - 13 * Real.log y := by
    have hyX : (X₀ : ℝ) ≤ y := by linarith
    have hly : Real.log y ≤ Real.log (s + capH X₀ s) :=
      Real.log_le_log (by linarith) (by linarith [capH_nonneg (X₀ : ℝ) s])
    have hl2 : Real.log (s + capH X₀ s) ≤ Real.log (2 * s) :=
      Real.log_le_log (by linarith) (by linarith [four_capH_le hX0 hX hsX])
    rw [Real.log_mul (by norm_num) (by linarith)] at hl2
    have : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hsl : ∀ k ≤ n + 1, M.slot k ≤ y - 13 * Real.log y := fun k hk =>
    (M.slot_mono hk).trans hy13
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  refine ⟨fun k hk => (slot_congr hϑ hT (by linarith [hsl k hk])).symm,
    fun k hk => harr k (hsl k hk), fun k hk => ?_⟩
  unfold placedAt
  rw [greedyPrime_congr (A := M.arr) (A' := M'.arr) fun i hi => harr i (hsl i (by omega))]

include h h' in
/-- **The absorbed set below `s_{n+1}` reads only the jitters of index `≤ n`.** -/
theorem limModel_absSet_congr {n : ℕ} (hUU : ∀ j ≤ n, U j = U' j) {x : ℝ}
    (hx : x ≤ h.limModel.slot (n + 1)) :
    x ∈ absSet X₀ (DM h.limModel U) ↔ x ∈ absSet X₀ (DM h'.limModel U') := by
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := h.X₀_big
  set s := h.limModel.slot (n + 1) with hsdef
  have hsX : (X₀ : ℝ) ≤ s := GreedyRun.slot_ge ⟨h.limModel, capH X₀, U, h.limModel_low⟩ (n + 1)
  have hH := log_le_capH hX0 hX hsX
  have hls : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  set m := ⌊s + capH X₀ s / 2 - X₀ + 1⌋₊ with hmdef
  have hm0 : 0 ≤ s + capH X₀ s / 2 - X₀ + 1 := by linarith [capH_nonneg (X₀ : ℝ) s]
  have hm1 : hor X₀ m ≤ s + capH X₀ s / 2 := by
    unfold hor; have := Nat.floor_le hm0; linarith
  have hm2 : s + capH X₀ s / 2 < hor X₀ m + 1 := by
    unfold hor; have := Nat.lt_floor_add_one (s + capH X₀ s / 2 - X₀ + 1); linarith
  have hag := limModel_agree_jitters h h' hUU m hm1
  set y := hor X₀ m
  have hyX : (X₀ : ℝ) ≤ y := by linarith
  have hUU' : ∀ k, h.limModel.slot (k + 1) ≤ cut2 X₀ y → U (k + 1) = U' (k + 1) := by
    intro k hk
    apply hUU
    by_contra hkn
    push_neg at hkn
    have hsk : s ≤ h.limModel.slot (k + 1) := h.limModel.slot_mono (by omega)
    have hcut : cut2 X₀ y < s := by
      rw [cut2_eq hX hyX]
      rcases le_or_gt y s with h1 | h1
      · have := capH_ge_one hX0 hX hyX; linarith
      · have hHm := capH_monotoneOn hX0 hX (mem_Ici.mpr hsX) (mem_Ici.mpr hyX) h1.le
        have := capH_ge_one hX0 hX hsX
        linarith
    linarith
  have hDA := dagree2 hX h.hU h'.hU h.limModel_low h'.limModel_low (by linarith) hag hUU'
  refine absSet_iff_of_agree hDA ?_
  obtain ⟨hY1, -⟩ := height2_bounds hX (z := y + 1) (by linarith)
  simp only [add_sub_cancel_right] at hY1
  have h1 := absorbY_le_sqrt hX0 hX hsX (n := x) hx
  have h2 := rpow_half_le (x := s) (z := s) (by linarith) (by linarith)
  linarith

end Stage

end BModel

end
