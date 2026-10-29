module

public import RequestProject.Beurling.Model.Slope

/-!
# The modulus of the rigid density

§5, eq. (osc), second bullet: `o_det ≤ (2.04 H(u) + 2) X₀^{5/12}/u`, from the linear window of
length `κu` in eq. (rhodet) and the unit spacing of the rigid set. We prove the underlying
modulus: for `1 ≤ s ≤ t`,
`|ρ_det(s) - ρ_det(t)| ≤ (5 (t - s) + 3)/(κ s)` (`rhoDet_sub_le`).
-/

@[expose] public section

open Finset

namespace BModel

/-- A natural subtraction bounded through its real counterpart. -/
lemma natSub_cast_le {a b : ℕ} {c : ℝ} (h : (b : ℝ) - a ≤ c) (hc : 0 ≤ c) :
    ((b - a : ℕ) : ℝ) ≤ c := by
  rcases le_total a b with hab | hab
  · rw [Nat.cast_sub hab]; exact h
  · rw [Nat.sub_eq_zero_of_le hab]; simpa using hc

/-- The rigid set in the window `[v, (1+κ)v]`. -/
noncomputable def rigidSet (X₀ : ℕ) (κ v : ℝ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo ⌊(1 + κ) * v⌋₊ X₀).filter fun n : ℕ => v ≤ (n : ℝ)

lemma rigidCount_eq (X₀ : ℕ) (κ v : ℝ) :
    Target.rigidCount X₀ v ((1 + κ) * v) = (rigidSet X₀ κ v).card := by
  classical
  unfold Target.rigidCount rigidSet
  congr 1

section

variable (X₀ : ℕ) {κ s t : ℝ} (hκ : 0 < κ) (hs : 1 ≤ s) (hst : s ≤ t)
include hκ hs hst

omit hs in
lemma rigidSet_sub_left :
    rigidSet X₀ κ s ⊆ rigidSet X₀ κ t ∪ Finset.Ico ⌈s⌉₊ ⌈t⌉₊ := by
  intro n hn
  simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
  obtain ⟨⟨hnN, hsm⟩, hsn⟩ := hn
  rw [Finset.mem_union]
  rcases le_or_gt t (n : ℝ) with htn | htn
  · left
    simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    exact ⟨⟨hnN.trans (Nat.floor_mono (by nlinarith)), hsm⟩, htn⟩
  · right
    rw [Finset.mem_Ico]
    exact ⟨Nat.ceil_le.mpr hsn, Nat.lt_ceil.mpr htn⟩

omit hκ hs in
lemma rigidSet_sub_right :
    rigidSet X₀ κ t ⊆ rigidSet X₀ κ s ∪ Finset.Ioc ⌊(1 + κ) * s⌋₊ ⌊(1 + κ) * t⌋₊ := by
  intro n hn
  simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
  obtain ⟨⟨hnN, hsm⟩, htn⟩ := hn
  rw [Finset.mem_union]
  rcases le_or_gt n ⌊(1 + κ) * s⌋₊ with hns | hns
  · left
    simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    exact ⟨⟨hns, hsm⟩, hst.trans htn⟩
  · right
    rw [Finset.mem_Ioc]
    exact ⟨hns, hnN⟩

omit hst in
lemma rigidSet_card_le : ((rigidSet X₀ κ s).card : ℝ) ≤ κ * s + 1 := by
  have hsub : rigidSet X₀ κ s ⊆ Finset.Icc ⌈s⌉₊ ⌊(1 + κ) * s⌋₊ := by
    intro n hn
    simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hn.2, hn.1.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : ((⌊(1 + κ) * s⌋₊ + 1 - ⌈s⌉₊ : ℕ) : ℝ) ≤ κ * s + 1 := by
    apply natSub_cast_le _ (by nlinarith)
    have := Nat.floor_le (show 0 ≤ (1 + κ) * s by nlinarith)
    have := Nat.le_ceil s
    push_cast
    nlinarith
  exact (Nat.cast_le.mpr h1).trans h2

lemma rigidSet_card_left :
    ((rigidSet X₀ κ s).card : ℝ) ≤ (rigidSet X₀ κ t).card + (t - s + 1) := by
  have h1 := (Finset.card_le_card (rigidSet_sub_left X₀ hκ hst)).trans
    (Finset.card_union_le _ _)
  rw [Nat.card_Ico] at h1
  have h2 : ((⌈t⌉₊ - ⌈s⌉₊ : ℕ) : ℝ) ≤ t - s + 1 := by
    apply natSub_cast_le _ (by linarith)
    have := Nat.ceil_lt_add_one (show 0 ≤ t by linarith)
    have := Nat.le_ceil s
    linarith
  have h3 : ((rigidSet X₀ κ s).card : ℝ) ≤
      (rigidSet X₀ κ t).card + ((⌈t⌉₊ - ⌈s⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

lemma rigidSet_card_right :
    ((rigidSet X₀ κ t).card : ℝ) ≤ (rigidSet X₀ κ s).card + ((1 + κ) * (t - s) + 1) := by
  have h1 := (Finset.card_le_card (rigidSet_sub_right X₀ (κ := κ) hst)).trans
    (Finset.card_union_le _ _)
  rw [Nat.card_Ioc] at h1
  have h2 : ((⌊(1 + κ) * t⌋₊ - ⌊(1 + κ) * s⌋₊ : ℕ) : ℝ) ≤ (1 + κ) * (t - s) + 1 := by
    apply natSub_cast_le _ (by nlinarith)
    have := Nat.floor_le (show 0 ≤ (1 + κ) * t by nlinarith)
    have := Nat.lt_floor_add_one ((1 + κ) * s)
    linarith
  have h3 : ((rigidSet X₀ κ t).card : ℝ) ≤ (rigidSet X₀ κ s).card +
      ((⌊(1 + κ) * t⌋₊ - ⌊(1 + κ) * s⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

end

/-- **The rigid modulus** (§5, eq. (osc), the bound on `o_det`; the window `[u, (1+κ)u]` of
eq. (rhodet) and the unit spacing of the rigid set): for `1 ≤ s ≤ t`,
`|ρ_det(s) - ρ_det(t)| ≤ (5 (t - s) + 3)/(κ s)`. -/
theorem rhoDet_sub_le (X₀ : ℕ) {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hs : 1 ≤ s)
    (hst : s ≤ t) :
    |Target.rhoDet X₀ κ s - Target.rhoDet X₀ κ t| ≤ (5 * (t - s) + 3) / (κ * s) := by
  unfold Target.rhoDet
  rw [rigidCount_eq, rigidCount_eq]
  have hL := rigidSet_card_left X₀ hκ hs hst
  have hR := rigidSet_card_right X₀ hκ hs hst
  have hT := rigidSet_card_le X₀ hκ (hs.trans hst)
  set Ns : ℝ := ((rigidSet X₀ κ s).card : ℝ)
  set Nt : ℝ := ((rigidSet X₀ κ t).card : ℝ)
  have hNt0 : 0 ≤ Nt := Nat.cast_nonneg _
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have e : Ns / (κ * s) - Nt / (κ * t) = ((Ns - Nt) * t + Nt * (t - s)) / (κ * s * t) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (show 0 < κ * s * t by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : 0 ≤ t - s := by linarith
  have hX : |(Ns - Nt) * t + Nt * (t - s)| ≤
      (2 * (t - s) + 2) * t + (κ * t + 1) * (t - s) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos ht0, abs_mul, abs_of_nonneg hNt0, abs_of_nonneg hd]
    have h1 : |Ns - Nt| ≤ 2 * (t - s) + 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have h2 : Nt * (t - s) ≤ (κ * t + 1) * (t - s) := mul_le_mul_of_nonneg_right hT hd
    nlinarith
  have hks : 0 < κ * s := by positivity
  calc |(Ns - Nt) * t + Nt * (t - s)| * (κ * s)
      ≤ ((2 * (t - s) + 2) * t + (κ * t + 1) * (t - s)) * (κ * s) :=
        mul_le_mul_of_nonneg_right hX hks.le
    _ ≤ (5 * (t - s) + 3) * (κ * s * t) := by
        have : (2 * (t - s) + 2) * t + (κ * t + 1) * (t - s) ≤ (5 * (t - s) + 3) * t := by
          nlinarith [mul_nonneg hd (show 0 ≤ 1 - κ by linarith), mul_nonneg hd ht0.le]
        nlinarith

/-- `rhoDet_sub_le` at `κ = κ(X₀)`, for `X₀ ≤ s ≤ t`. -/
theorem rhoDet_kappa_sub_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {s t : ℝ} (hs : (X₀ : ℝ) ≤ s)
    (hst : s ≤ t) :
    |Target.rhoDet X₀ (Construction.kappaParam X₀) s -
        Target.rhoDet X₀ (Construction.kappaParam X₀) t| ≤
      (5 * (t - s) + 3) / (Construction.kappaParam X₀ * s) := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  obtain ⟨hκ0, hκ1⟩ := kappa_facts hX
  exact rhoDet_sub_le X₀ hκ0 hκ1 (by linarith) hst

end BModel
