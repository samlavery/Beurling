module

public import RequestProject.Beurling.Model.Width

/-!
# One step of the construction and its causality (Lemmas 3.2 and 3.5, Remark horizon)

From prime data `D`, one step of the construction builds the slot model whose target is the
target (6) of `D` (`targetD`), with offset `ϑ_s = 1/2`, and whose arrivals in each slot are the
composites of `D` in that slot (`arrOf`): `Phi θ X₀ D`. From a slot model `M` and the jitters
`U`, the prime data are the decisions of the greedy rule and the landing points
`s + H(s)(U - 1/2)` (`DM M U`). The construction of §3 is a fixed point of `M ↦ Phi (DM M U)`.

The fixed point exists because the step is **causal**: `MAgree M M' y` (the targets agree on
`(-∞, y]` and the arrivals agree on the slots starting below `y - 13 log y`) implies
`MAgree (Phi (DM M U)) (Phi (DM M' U)) (y + 1)` (`causal`). This is the paper's resolution of the
circularity (decisions at a slot read only data below the slot, Lemma 3.5; `T` on `[1, u]` is read
by slots `≤ u - H(u)`, Lemma 3.2 and the term `2H` in `x⁺_k`):

* `dagree_of_magree`: agreeing models have agreeing prime data below
  `f(y - 13 log y) - 1/8`, `f(s) = s - H(s)/2` (box-centred landing, `floor_quasi_mono`);
* the targets of the data agree up to `y + 1` (`targetD_congr`: `y(n) ≤ n^{1/2}`, and
  `a_j + 2H(a_j) ≤ x⁺_j + 3`, `gap_gamma`);
* the composites in a slot `[s_i, s_{i+1}) ⊆ (-∞, y + 1)` agree (`compCount_eq_of_agree2`), as
  the slots of the new target agree and are at most `13 log` apart (`slot_succ_le`, from the
  slope bound of Lemma 3.3).

The two analytic inputs about the targets (`ValidHyp`: the target is a valid slot-model target;
`SlopeHyp`: its slope is at least `0.08/log`) are Lemma 3.3 and are discharged in
`Model/Valid.lean`.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono

namespace BModel

variable {X₀ : ℕ}

/-! ### Slot models from a target -/

/-- The slot start `s_k = min{x ≥ 1 : T(x) ≥ X₀ - 1 + k + ϑ}` of a target `T`. -/
noncomputable def slotOf (X₀ : ℕ) (ϑ : ℝ) (T : ℝ → ℝ) (k : ℕ) : ℝ :=
  sInf {x : ℝ | 1 ≤ x ∧ (X₀ : ℝ) - 1 + k + ϑ ≤ T x}

lemma slot_eq_slotOf (M : SlotModel X₀) (k : ℕ) : M.slot k = slotOf X₀ M.ϑ M.T k := rfl

/-- The conditions on a target in a slot model. -/
structure TValid (X₀ : ℕ) (T : ℝ → ℝ) : Prop where
  mono : Monotone T
  rcont : ∀ x, ContinuousWithinAt T (Ici x) x
  unbdd : ∀ y, ∃ x, y ≤ T x
  start : (X₀ : ℝ) ≤ T X₀

/-- The count `V` of Lemma 3.6 from the arrivals. -/
def Vof (X₀ : ℕ) (arr : ℕ → ℤ) : ℕ → ℤ
  | 0 => X₀
  | k + 1 => Vof X₀ arr k + arr (k + 1) + greedyPrime arr k

/-- The slot model with target `T`, offset `ϑ_s = 1/2` and arrivals `arr`. -/
noncomputable def mkModel (T : ℝ → ℝ) (hT : TValid X₀ T) (arr : ℕ → ℤ) (harr : ∀ k, 0 ≤ arr k) :
    SlotModel X₀ where
  ϑ := 1 / 2
  T := T
  arr := arr
  V := Vof X₀ arr
  hϑ0 := by norm_num
  hϑ := le_rfl
  T_mono := hT.mono
  T_rcont := hT.rcont
  T_unbdd := hT.unbdd
  T_start := hT.start
  arr_nonneg := harr
  V_zero := rfl
  V_step := fun _ => rfl

lemma tvalid_id : TValid X₀ id where
  mono := monotone_id
  rcont := fun _ => continuous_id.continuousWithinAt
  unbdd := fun y => ⟨y, le_rfl⟩
  start := le_rfl

/-- A fixed slot model (used only when the conditions of the construction fail). -/
noncomputable def idModel : SlotModel X₀ := mkModel id tvalid_id (fun _ => 0) (fun _ => le_rfl)

/-- **The arrivals of the data in the slots of `T`**: the composites of value in `[s_k, s_{k+1})`
(none at the paper's slot `j₀ - 1`). -/
noncomputable def arrOf (X₀ : ℕ) (D : PrimeData) (T : ℝ → ℝ) (k : ℕ) : ℤ :=
  if k = 0 then 0 else compCount X₀ D (slotOf X₀ (1 / 2) T k) (slotOf X₀ (1 / 2) T (k + 1))

lemma arrOf_nonneg (X₀ : ℕ) (D : PrimeData) (T : ℝ → ℝ) (k : ℕ) : 0 ≤ arrOf X₀ D T k := by
  unfold arrOf compCount; split_ifs <;> positivity

open Classical in
/-- **One step of the construction**: the slot model of the target of `D`, with the composites of
`D` as arrivals. -/
noncomputable def Phi (θ : ℝ) (X₀ : ℕ) (D : PrimeData) : SlotModel X₀ :=
  if h : TValid X₀ (targetD θ X₀ D) then
    mkModel (targetD θ X₀ D) h (arrOf X₀ D (targetD θ X₀ D)) (arrOf_nonneg X₀ D _)
  else idModel

lemma Phi_ϑ (θ : ℝ) (D : PrimeData) : (Phi θ X₀ D).ϑ = 1 / 2 := by
  unfold Phi; split_ifs <;> rfl

lemma Phi_T {θ : ℝ} {D : PrimeData} (h : TValid X₀ (targetD θ X₀ D)) :
    (Phi θ X₀ D).T = targetD θ X₀ D := by
  unfold Phi; rw [dif_pos h]; rfl

lemma Phi_arr {θ : ℝ} {D : PrimeData} (h : TValid X₀ (targetD θ X₀ D)) :
    (Phi θ X₀ D).arr = arrOf X₀ D (targetD θ X₀ D) := by
  unfold Phi; rw [dif_pos h]; rfl

/-- The target of the data is `⌊x⌋` below `X₀`. -/
lemma targetD_low (θ : ℝ) (D : PrimeData) {x : ℝ} (hx : x < X₀) :
    targetD θ X₀ D x = ⌊x⌋₊ := by
  unfold targetD target; rw [if_pos hx]

/-- **The prime data of a slot model**: the decisions of the greedy rule and the landing points
of the decided primes, with jitter width `H = capH X₀` and jitters `U`. -/
noncomputable def DM (M : SlotModel X₀) (U : ℕ → ℝ) : PrimeData :=
  ⟨placedAt M, primeValueOf M (capH X₀) U⟩

/-- The two analytic inputs of Lemma 3.3: the target of any data is a valid slot-model target. -/
def ValidHyp (θ : ℝ) (X₀ : ℕ) : Prop := ∀ D : PrimeData, TValid X₀ (targetD θ X₀ D)

/-- The slope bound of Lemma 3.3: `T(x') - T(x) ≥ 0.08 (x' - x)/log x'` on `[X₀, ∞)`. -/
def SlopeHyp (θ : ℝ) (X₀ : ℕ) : Prop :=
  ∀ (D : PrimeData) (x x' : ℝ), (X₀ : ℝ) ≤ x → x ≤ x' →
    0.08 * (x' - x) / Real.log x' ≤ targetD θ X₀ D x' - targetD θ X₀ D x

/-! ### Agreement of slot models -/

/-- **Agreement up to height `y`**: the targets agree on `(-∞, y]` and the arrivals agree on the
slots starting below `y - 13 log y`. -/
def MAgree (M M' : SlotModel X₀) (y : ℝ) : Prop :=
  M.ϑ = M'.ϑ ∧ (∀ x ≤ y, M.T x = M'.T x) ∧
    ∀ i, M.slot i ≤ y - 13 * Real.log y → M.arr i = M'.arr i

/-- Slots below the agreement height agree. -/
lemma slot_congr {M M' : SlotModel X₀} {y : ℝ} (hϑ : M.ϑ = M'.ϑ)
    (hT : ∀ x ≤ y, M.T x = M'.T x) {k : ℕ} (hk : M.slot k ≤ y) : M'.slot k = M.slot k := by
  have h1 : M'.slot k ≤ M.slot k := by
    apply M'.slot_le
    refine ⟨M.one_le_slot k, ?_⟩
    rw [← hT _ hk]
    unfold SlotModel.level
    rw [← hϑ]
    exact M.level_le_T_slot k
  have h2 : M.slot k ≤ M'.slot k := by
    apply M.slot_le
    refine ⟨M'.one_le_slot k, ?_⟩
    rw [hT _ (h1.trans hk)]
    unfold SlotModel.level
    rw [hϑ]
    exact M'.level_le_T_slot k
  linarith

/-- `y ↦ y - 13 log y` is monotone on `[13, ∞)`. -/
lemma sub_log_mono {y y' : ℝ} (h13 : 13 ≤ y') (hy : y' ≤ y) :
    y' - 13 * Real.log y' ≤ y - 13 * Real.log y := by
  have hy0 : 0 < y' := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < y) hy0)
  rw [Real.log_div (by linarith) hy0.ne'] at h
  have h2 : y / y' - 1 ≤ (y - y') / 13 := by
    rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 (by norm_num)]
    nlinarith
  linarith

lemma MAgree.symm {M M' : SlotModel X₀} {y : ℝ} (hy : 1 ≤ y) (h : MAgree M M' y) :
    MAgree M' M y := by
  obtain ⟨hϑ, hT, harr⟩ := h
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  refine ⟨hϑ.symm, fun x hx => (hT x hx).symm, fun i hi => ?_⟩
  have he := slot_congr hϑ.symm (fun x hx => (hT x hx).symm) (k := i) (by linarith)
  exact (harr i (by rw [he]; exact hi)).symm

lemma MAgree.trans {M₁ M₂ M₃ : SlotModel X₀} {y : ℝ} (hy : 1 ≤ y) (h₁ : MAgree M₁ M₂ y)
    (h₂ : MAgree M₂ M₃ y) : MAgree M₁ M₃ y := by
  obtain ⟨hϑ₁, hT₁, harr₁⟩ := h₁
  obtain ⟨hϑ₂, hT₂, harr₂⟩ := h₂
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  refine ⟨hϑ₁.trans hϑ₂, fun x hx => (hT₁ x hx).trans (hT₂ x hx), fun i hi => ?_⟩
  have he := slot_congr hϑ₁ hT₁ (k := i) (by linarith)
  exact (harr₁ i hi).trans (harr₂ i (by rw [he]; exact hi))

lemma MAgree.mono {M M' : SlotModel X₀} {y y' : ℝ} (h13 : 13 ≤ y') (hyy : y' ≤ y)
    (h : MAgree M M' y) : MAgree M M' y' := by
  obtain ⟨hϑ, hT, harr⟩ := h
  exact ⟨hϑ, fun x hx => hT x (hx.trans hyy),
    fun i hi => harr i (hi.trans (sub_log_mono h13 hyy))⟩

lemma MAgree.refl (M : SlotModel X₀) (y : ℝ) : MAgree M M y :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ### The greedy rule only reads the past -/

lemma greedyQueue_congr {A A' : ℕ → ℤ} {k : ℕ} (h : ∀ i ≤ k, A i = A' i) :
    greedyQueue A k = greedyQueue A' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [greedyQueue]
    rw [ih (fun i hi => h i (by omega)), h (k + 1) le_rfl]

lemma greedyPrime_congr {A A' : ℕ → ℤ} {k : ℕ} (h : ∀ i ≤ k + 1, A i = A' i) :
    greedyPrime A k = greedyPrime A' k := by
  unfold greedyPrime
  rw [greedyQueue_congr (fun i hi => h i (by omega)), h (k + 1) le_rfl]

/-! ### Agreeing models have agreeing prime data -/

/-- The box floor `f(s) = s - H(s)/2`. -/
noncomputable def boxFloor (X₀ : ℕ) (s : ℝ) : ℝ := s - capH X₀ s / 2

/-- The height below which agreeing models have agreeing prime data. -/
noncomputable def dataHeight (X₀ : ℕ) (y : ℝ) : ℝ :=
  boxFloor X₀ (max (y - 13 * Real.log y) X₀) - 1 / 8

lemma slots_unbounded (M : SlotModel X₀) (w : ℝ) : ∃ k, w < M.slot (k + 1) := by
  by_contra hc
  push_neg at hc
  obtain ⟨n, hn⟩ := exists_nat_gt (M.T w - X₀)
  have h1 := M.level_le_T_slot (n + 1)
  have h2 := M.T_mono (hc n)
  unfold SlotModel.level at h1
  push_cast at h1
  linarith [M.hϑ0]

/-- **Agreeing models have agreeing prime data** (box-centred landing: a prime decided at a slot
`s ≥ s₀` lands at `≥ f(s) ≥ f(s₀) - 1/8`). -/
theorem dagree_of_magree (hX : 10 ^ 8 ≤ Real.log X₀) {U : ℕ → ℝ}
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) {M M' : SlotModel X₀}
    (hM : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (hM' : ∀ x : ℝ, x < X₀ → M'.T x = ⌊x⌋₊)
    {y : ℝ} (hy : 1 ≤ y) (h : MAgree M M' y) :
    DAgree (DM M U) (DM M' U) (dataHeight X₀ y) := by
  classical
  obtain ⟨hϑ, hT, harr⟩ := h
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  set w := y - 13 * Real.log y with hw
  set m := max w X₀ with hm
  have hK := slots_unbounded M w
  set K := Nat.find hK with hKdef
  have hlt : ∀ k < K, M.slot (k + 1) ≤ w := fun k hk => by
    have := Nat.find_min hK hk; push_neg at this; exact this
  -- the floor bound for slots beyond `w`
  have hfloor : ∀ (N : SlotModel X₀), (∀ x : ℝ, x < X₀ → N.T x = ⌊x⌋₊) → ∀ k,
      w < N.slot (k + 1) → dataHeight X₀ y ≤ primeValueOf N (capH X₀) U k := by
    intro N hN k hk
    have hs : (X₀ : ℝ) ≤ N.slot (k + 1) := GreedyRun.slot_ge ⟨N, capH X₀, U, hN⟩ (k + 1)
    have hms : m ≤ N.slot (k + 1) := max_le hk.le hs
    have h1 := (landing_mem_box (s := N.slot (k + 1)) (capH_nonneg X₀ (N.slot (k + 1)))
      (hU (k + 1))).1
    have h2 := floor_quasi_mono hX0 hX (le_max_right w (X₀ : ℝ)) hms
    unfold dataHeight boxFloor
    unfold primeValueOf
    rw [← hm]
    linarith
  refine ⟨K, fun k hk => ?_, fun k hk _ => ?_, fun k hk _ => ?_⟩
  · have hsk := hlt k hk
    have hsy : M.slot (k + 1) ≤ y := hsk.trans (by linarith)
    have he := slot_congr hϑ hT hsy
    refine ⟨?_, ?_⟩
    · show placedAt M k ↔ placedAt M' k
      unfold placedAt
      rw [greedyPrime_congr (A := M.arr) (A' := M'.arr) fun i hi =>
        harr i ((M.slot_mono hi).trans hsk)]
    · show primeValueOf M (capH X₀) U k = primeValueOf M' (capH X₀) U k
      unfold primeValueOf
      rw [he]
  · have : w < M.slot (k + 1) := by
      have h1 := Nat.find_spec hK
      exact lt_of_lt_of_le h1 (M.slot_mono (by omega))
    exact hfloor M hM k this
  · have : w < M'.slot (k + 1) := by
      by_contra hc
      push_neg at hc
      have he := slot_congr hϑ.symm (fun x hx => (hT x hx).symm) (k := k + 1) (by linarith)
      have h1 := Nat.find_spec hK
      have h2 : M.slot (K + 1) ≤ M.slot (k + 1) := M.slot_mono (by omega)
      rw [he] at h2
      linarith
    exact hfloor M' hM' k this

/-- The prime data of a model with the target `⌊x⌋` below `X₀` have values `≥ 2`. -/
lemma pos2_DM (hX : 10 ^ 8 ≤ Real.log X₀) {U : ℕ → ℝ} (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    {M : SlotModel X₀} (hM : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) : Pos2 (DM M U) := by
  intro k _
  obtain ⟨h1, h2⟩ := primeValueOf_ge M hU hX hM k
  have h40 := two_pow_forty_le_of_logX (Nat.cast_nonneg _) hX
  show 2 ≤ primeValueOf M (capH X₀) U k
  have : (2 : ℝ) ^ (40 : ℕ) ≥ 3 := by norm_num
  linarith

/-! ### Numerical facts for the causality step -/

/-- `1 + 13 log z ≤ z/100` for `log z ≥ 10⁸`. -/
lemma one_add_log_le {z : ℝ} (hz0 : 0 < z) (hz : 10 ^ 8 ≤ Real.log z) :
    1 + 13 * Real.log z ≤ z / 100 := by
  have hz1 : 10 ^ 8 + 1 ≤ z := by
    have := Real.add_one_le_exp (Real.log z)
    rw [Real.exp_log hz0] at this; linarith
  have he := exp_ten_ge
  have h := Real.log_le_sub_one_of_pos (show 0 < z / Real.exp 10 by positivity)
  rw [Real.log_div hz0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have h2 : z / Real.exp 10 ≤ z / 17073 := div_le_div_of_nonneg_left hz0.le (by norm_num) he
  linarith

section Heights

variable (hX : 10 ^ 8 ≤ Real.log X₀)
include hX

lemma X₀_ge_two_pow : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := two_pow_le_of_logX (Nat.cast_nonneg _) hX

/-- The agreement height `w = (z - 1) - 13 log(z - 1)` is at least `0.99 z`. -/
lemma sub_log_ge {z : ℝ} (hz : (X₀ : ℝ) ≤ z) :
    99 / 100 * z ≤ (z - 1) - 13 * Real.log (z - 1) ∧ (z - 1) - 13 * Real.log (z - 1) ≤ z := by
  have h16 := X₀_ge_two_pow hX
  obtain ⟨hlz, -, -⟩ := logs_of_ge (Nat.cast_nonneg _) hX hz
  have hz0 : 0 < z := by linarith
  have h1 := one_add_log_le hz0 hlz
  have h2 : Real.log (z - 1) ≤ Real.log z := Real.log_le_log (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (z - 1) := Real.log_nonneg (by linarith)
  constructor <;> linarith

lemma boxFloor_ge {m : ℝ} (hm : (X₀ : ℝ) ≤ m) : 7 / 8 * m ≤ boxFloor X₀ m := by
  have := four_capH_le (Nat.cast_nonneg _) hX hm
  unfold boxFloor; linarith

/-- `0.86 z ≤ dataHeight (z - 1) ≤ z`. -/
lemma dataHeight_bounds {z : ℝ} (hz : (X₀ : ℝ) ≤ z) :
    86 / 100 * z ≤ dataHeight X₀ (z - 1) ∧ dataHeight X₀ (z - 1) ≤ z := by
  obtain ⟨h1, h2⟩ := sub_log_ge hX hz
  have h16 := X₀_ge_two_pow hX
  set m := max ((z - 1) - 13 * Real.log (z - 1)) (X₀ : ℝ) with hm
  have hmX : (X₀ : ℝ) ≤ m := le_max_right _ _
  have hmw : (z - 1) - 13 * Real.log (z - 1) ≤ m := le_max_left _ _
  have hmz : m ≤ z := max_le h2 hz
  have hb := boxFloor_ge hX hmX
  have hH := capH_nonneg (X₀ : ℝ) m
  unfold dataHeight
  rw [← hm]
  constructor
  · nlinarith
  · unfold boxFloor; linarith

/-- **The heights read by the oscillation are below the data height** (the term `2H` in
`x⁺_k = x_k + 2H(x_k)`): if `a ≥ X₀`, `a + 2H(a) ≤ x + 3` and `x < z`, then
`a < dataHeight (z - 1)`. -/
theorem gap_gamma {a xp z : ℝ} (ha : (X₀ : ℝ) ≤ a) (haH : a + 2 * capH X₀ a ≤ xp + 3)
    (hxz : xp < z) : a < dataHeight X₀ (z - 1) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hX
  have hH1 := log_le_capH hX0 hX ha
  have hH4 := four_capH_le hX0 hX ha
  have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hz : (X₀ : ℝ) ≤ z := by linarith
  obtain ⟨hw1, -⟩ := sub_log_ge hX hz
  set w := (z - 1) - 13 * Real.log (z - 1) with hw
  set m := max w (X₀ : ℝ) with hm
  have hmw : w ≤ m := le_max_left _ _
  unfold dataHeight boxFloor
  rw [← hw, ← hm]
  rcases le_or_gt z (4 * a) with h4 | h4
  · -- `z ≤ 4a`: `13 log(z - 1) ≤ H(a)/10`
    have hlog : Real.log (z - 1) ≤ Real.log a + 1.39 := by
      have h1 : Real.log (z - 1) ≤ Real.log (4 * a) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      linarith [log4_bounds.2]
    have hwa : a + 19 / 10 * capH X₀ a - 4 ≤ w := by rw [hw]; nlinarith
    have hma : a ≤ m := by linarith
    have hq := floor_quasi_mono hX0 hX ha hma
    nlinarith
  · -- `z > 4a`: `m ≥ 2a`
    have hma : 2 * a ≤ m := by nlinarith
    have hq := floor_quasi_mono hX0 hX ha (by linarith : a ≤ m)
    nlinarith

end Heights

/-- **Consecutive slots of the new target are at most `13 log z` apart** (from the slope
`T' ≥ 0.08/log` of Lemma 3.3). -/
lemma slot_succ_le {θ : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) (hS : SlopeHyp θ X₀) {D : PrimeData}
    (hv : TValid X₀ (targetD θ X₀ D)) {i : ℕ} {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
    (hi : (Phi θ X₀ D).slot i ≤ z - 13 * Real.log z) : (Phi θ X₀ D).slot (i + 1) ≤ z := by
  set M := Phi θ X₀ D
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := fun x hx => by
    rw [Phi_T hv]; exact targetD_low θ D hx
  have hs : (X₀ : ℝ) ≤ M.slot i := GreedyRun.slot_ge ⟨M, capH X₀, fun _ => 0, hTlow⟩ i
  obtain ⟨hlz, -, -⟩ := logs_of_ge (Nat.cast_nonneg _) hX hz
  have hlz0 : 0 < Real.log z := by linarith
  have hsz : M.slot i ≤ z := by linarith
  have hslope := hS D (M.slot i) z hs hsz
  have h1 : 0.08 * (13 * Real.log z) / Real.log z ≤ 0.08 * (z - M.slot i) / Real.log z :=
    div_le_div_of_nonneg_right (by linarith) hlz0.le
  have h2 : 0.08 * (13 * Real.log z) / Real.log z = 1.04 := by field_simp; norm_num
  have hlev := M.level_le_T_slot i
  have hT : M.T = targetD θ X₀ D := Phi_T hv
  have hϑ : M.ϑ = 1 / 2 := Phi_ϑ θ D
  apply M.slot_le
  refine ⟨by linarith [X₀_ge_two_pow hX], ?_⟩
  unfold SlotModel.level at hlev ⊢
  rw [hT] at hlev ⊢
  push_cast
  linarith

/-! ### Causality of one step -/

/-- `x^{1/2} ≤ z/2` for `z ≤ x ≤ 2z`, `z ≥ 8`. -/
lemma rpow_half_le {x z : ℝ} (hz : 8 ≤ z) (hx : x ≤ 2 * z) :
    x ^ (1 / 2 : ℝ) ≤ z / 2 := by
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- **Causality of one step of the construction** (Lemma 3.2, Lemma 3.5): if two slot models
(with target `⌊x⌋` below `X₀`) agree up to height `z - 1`, the next step agrees up to `z`. -/
theorem causal {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 2) (hX : 10 ^ 8 ≤ Real.log X₀) {U : ℕ → ℝ}
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hV : ValidHyp θ X₀) (hS : SlopeHyp θ X₀)
    {M M' : SlotModel X₀} (hM : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊)
    (hM' : ∀ x : ℝ, x < X₀ → M'.T x = ⌊x⌋₊) {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
    (h : MAgree M M' (z - 1)) :
    MAgree (Phi θ X₀ (DM M U)) (Phi θ X₀ (DM M' U)) z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h16 := X₀_ge_two_pow hX
  set D := DM M U with hD
  set D' := DM M' U with hD'
  have hy : 1 ≤ z - 1 := by linarith
  have hDA := dagree_of_magree hX hU hM hM' hy h
  set Y := dataHeight X₀ (z - 1) with hY
  obtain ⟨hY1, hY2⟩ := dataHeight_bounds hX hz
  have hP := pos2_DM hX hU hM
  have hP' := pos2_DM hX hU hM'
  -- the targets agree up to `z`
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
      exact gap_gamma hX hXa (scale_add_two_capH_le hX0 hX j) hj
  have hv := hV D
  have hv' := hV D'
  refine ⟨by rw [Phi_ϑ, Phi_ϑ], fun x hx => by rw [Phi_T hv, Phi_T hv']; exact hTeq x hx,
    fun i hi => ?_⟩
  -- the arrivals agree on the slots starting below `z - 13 log z`
  have hTz : ∀ x ≤ z, (Phi θ X₀ D).T x = (Phi θ X₀ D').T x := fun x hx => by
    rw [Phi_T hv, Phi_T hv']; exact hTeq x hx
  have hϑ : (Phi θ X₀ D).ϑ = (Phi θ X₀ D').ϑ := by rw [Phi_ϑ, Phi_ϑ]
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hsi : (Phi θ X₀ D).slot i ≤ z := by linarith
  have hsi1 := slot_succ_le hX hS hv hz hi
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

end BModel

end
