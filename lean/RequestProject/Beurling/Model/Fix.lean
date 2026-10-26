module

public import RequestProject.Beurling.Model.Valid

/-!
# The construction of §3 as a fixed point (Remark horizon)

The circularity of §3 (the target reads `A` and the heights `γ_k`, which read the realised system,
which reads the slots of the target) is resolved causally: decisions at a height only read data
below it (`causal`). Here the fixed point is built by iteration from any start:

* `iterM n` : the `n`-th iterate `M_{n+1} = Phi (DM M_n U)`;
* `iter_agree_le` : `M_n` and `M_m` (`n ≤ m`) agree up to height `X₀ - 1 + n` (induction on `n`,
  with `causal` as the step: the horizon grows by `1` per iteration);
* `limModel` : the limit, `T(x) := T_n(x)` and `A_k := A_{n,k}` for `n` large; it is a slot model,
  and it agrees with `M_n` up to `X₀ - 1 + n`;
* `limModel_T`, `limModel_arr` : **the fixed-point equations**: the target of the limit is the
  target (6) of its own prime data, and its arrivals are the composites of its own prime data in
  its own slots.

`constructedModel θ X₀ U` is the limit when the standing conditions `Std` hold (admissible `θ`,
`log X₀ ≥ 10⁸`, jitters in `[0, 1]`, and (84) from `X₀` on, the input of Lemma 3.3), and a fixed
slot model otherwise; it is defined for every `ω`.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono Filter Topology

namespace BModel

variable {θ : ℝ} {X₀ : ℕ} {U : ℕ → ℝ}

/-- The standing conditions of the construction: admissible `θ`, `log X₀ ≥ 10⁸`, jitters in
`[0, 1]`, and (84) from `X₀` on (the input of Lemma 3.3). -/
structure Std (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) : Prop where
  hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)
  hX : 10 ^ 8 ≤ Real.log X₀
  hU : ∀ j, U j ∈ Icc (0 : ℝ) 1
  hHB : ShortIntervalPNTFrom X₀

lemma Std.hV (h : Std θ X₀ U) : ValidHyp θ X₀ := validHyp_of_HB h.hθ h.hX h.hHB

lemma Std.hS (h : Std θ X₀ U) : SlopeHyp θ X₀ := slopeHyp_of_HB h.hθ h.hX h.hHB

/-- The empty prime data (the start of the iteration). -/
def D0 : PrimeData := ⟨fun _ => False, fun _ => 0⟩

/-- The prime data of the iterates. -/
noncomputable def iterD (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) : ℕ → PrimeData
  | 0 => D0
  | n + 1 => DM (Phi θ X₀ (iterD θ X₀ U n)) U

/-- **The iterates** `M_n`, `M_{n+1} = Phi (DM M_n U)`. -/
noncomputable def iterM (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) (n : ℕ) : SlotModel X₀ :=
  Phi θ X₀ (iterD θ X₀ U n)

lemma iterM_succ (n : ℕ) : iterM θ X₀ U (n + 1) = Phi θ X₀ (DM (iterM θ X₀ U n) U) := rfl

/-- The horizon `X₀ - 1 + n` of the `n`-th iterate. -/
def hor (X₀ : ℕ) (n : ℕ) : ℝ := (X₀ : ℝ) - 1 + n

namespace Std

variable (h : Std θ X₀ U)
include h

lemma X₀_big : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := X₀_ge_two_pow h.hX

omit h in
lemma hor_ge (n : ℕ) : (X₀ : ℝ) - 1 ≤ hor X₀ n := by
  unfold hor; linarith [Nat.cast_nonneg (α := ℝ) n]

lemma hor_ge13 (n : ℕ) : 13 ≤ hor X₀ n := by
  have := h.X₀_big; have := hor_ge (X₀ := X₀) n; linarith

lemma phi_T (D : PrimeData) : (Phi θ X₀ D).T = targetD θ X₀ D := Phi_T (h.hV D)

lemma phi_low (D : PrimeData) : ∀ x : ℝ, x < X₀ → (Phi θ X₀ D).T x = ⌊x⌋₊ := fun x hx => by
  rw [h.phi_T]; exact targetD_low θ D hx

lemma phi_linear (D : PrimeData) :
    ∀ x, (X₀ : ℝ) ≤ x → 7 / 10 * x - X₀ - 1 ≤ (Phi θ X₀ D).T x := fun x hx => by
  rw [h.phi_T]; exact targetD_ge_linear (by linarith [h.hθ.2]) h.hX D hx

lemma iterM_low (n : ℕ) : ∀ x : ℝ, x < X₀ → (iterM θ X₀ U n).T x = ⌊x⌋₊ := h.phi_low _

/-- The base case: any two iterates agree up to `X₀ - 1`. -/
lemma agree_base (D D' : PrimeData) : MAgree (Phi θ X₀ D) (Phi θ X₀ D') (hor X₀ 0) := by
  have h16 := h.X₀_big
  have he : hor X₀ 0 = (X₀ : ℝ) - 1 := by simp [hor]
  refine ⟨by rw [Phi_ϑ, Phi_ϑ], fun x hx => ?_, fun i hi => ?_⟩
  · rw [he] at hx
    rw [h.phi_low D x (by linarith), h.phi_low D' x (by linarith)]
  · exfalso
    have hs : (X₀ : ℝ) ≤ (Phi θ X₀ D).slot i :=
      GreedyRun.slot_ge ⟨Phi θ X₀ D, capH X₀, U, h.phi_low D⟩ i
    rw [he] at hi
    have : 0 ≤ Real.log ((X₀ : ℝ) - 1) := Real.log_nonneg (by linarith)
    linarith

/-- **Consecutive iterates agree up to the horizon** `X₀ - 1 + n`. -/
theorem iter_agree (n : ℕ) : MAgree (iterM θ X₀ U n) (iterM θ X₀ U (n + 1)) (hor X₀ n) := by
  induction n with
  | zero => exact h.agree_base _ _
  | succ n ih =>
    rw [iterM_succ (n + 1), iterM_succ n]
    have hz : (X₀ : ℝ) ≤ hor X₀ (n + 1) := by unfold hor; push_cast; linarith
    have e : hor X₀ (n + 1) - 1 = hor X₀ n := by unfold hor; push_cast; ring
    refine causal (by linarith [h.hθ.1]) (by linarith [h.hθ.2]) h.hX h.hU h.hV h.hS
      (h.iterM_low n) (h.iterM_low (n + 1)) hz ?_
    rw [e]; exact ih

/-- **All later iterates agree with `M_n` up to its horizon.** -/
theorem iter_agree_le {n m : ℕ} (hnm : n ≤ m) :
    MAgree (iterM θ X₀ U n) (iterM θ X₀ U m) (hor X₀ n) := by
  induction m, hnm using Nat.le_induction with
  | base => exact MAgree.refl _ _
  | succ m hnm ih =>
    have hmono : hor X₀ n ≤ hor X₀ m := by
      unfold hor; have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith
    exact ih.trans (by linarith [h.hor_ge13 n])
      ((h.iter_agree m).mono (h.hor_ge13 n) hmono)

/-- Agreement of two iterates up to the smaller horizon. -/
theorem iter_agree_min (n m : ℕ) :
    MAgree (iterM θ X₀ U n) (iterM θ X₀ U m) (hor X₀ (min n m)) := by
  rcases le_total n m with hnm | hmn
  · rw [min_eq_left hnm]; exact h.iter_agree_le hnm
  · rw [min_eq_right hmn]
    exact (h.iter_agree_le hmn).symm (by linarith [h.hor_ge13 m])

end Std

/-! ### The limit -/

/-- The index of an iterate whose horizon passes `x + 1`. -/
noncomputable def nT (X₀ : ℕ) (x : ℝ) : ℕ := ⌈x - X₀ + 2⌉₊

lemma le_hor_nT (x : ℝ) : x + 1 ≤ hor X₀ (nT X₀ x) := by
  unfold hor nT
  have := Nat.le_ceil (x - X₀ + 2)
  linarith

/-- The bound `2 (2X₀ + i + 1)` on the slot starts of the iterates (`slot_le_linear`). -/
def slotB (X₀ : ℕ) (i : ℕ) : ℝ := 2 * (2 * X₀ + i + 1)

/-- The index of an iterate whose horizon covers the slot `i`. -/
noncomputable def nA (X₀ : ℕ) (i : ℕ) : ℕ := ⌈2 * slotB X₀ i⌉₊

/-- The limit target. -/
noncomputable def limT (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) (x : ℝ) : ℝ :=
  (iterM θ X₀ U (nT X₀ x)).T x

/-- The limit arrivals. -/
noncomputable def limArr (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) (i : ℕ) : ℤ :=
  (iterM θ X₀ U (nA X₀ i)).arr i

namespace Std

variable (h : Std θ X₀ U)
include h

lemma limT_eq {n : ℕ} {x : ℝ} (hx : x ≤ hor X₀ n) : limT θ X₀ U x = (iterM θ X₀ U n).T x := by
  unfold limT
  refine (h.iter_agree_min (nT X₀ x) n).2.1 x ?_
  rcases le_total (nT X₀ x) n with hle | hle
  · rw [min_eq_left hle]; linarith [le_hor_nT (X₀ := X₀) x]
  · rw [min_eq_right hle]; exact hx

lemma slot_iter_le (n i : ℕ) : (iterM θ X₀ U n).slot i ≤ slotB X₀ i :=
  slot_le_linear h.hX (h.phi_linear _) i

/-- The horizon of `nA i` covers `slotB i`. -/
lemma slotB_le_nA (i : ℕ) :
    slotB X₀ i ≤ hor X₀ (nA X₀ i) - 13 * Real.log (hor X₀ (nA X₀ i)) := by
  have h16 := h.X₀_big
  have hX0 : (X₀ : ℝ) ≤ hor X₀ (nA X₀ i) + 1 := by
    unfold hor; linarith [Nat.cast_nonneg (α := ℝ) (nA X₀ i)]
  have hB : 0 ≤ slotB X₀ i := by unfold slotB; positivity
  have hn : 2 * slotB X₀ i ≤ nA X₀ i := Nat.le_ceil _
  obtain ⟨h1, -⟩ := sub_log_ge h.hX hX0
  simp only [add_sub_cancel_right] at h1
  unfold hor at h1 ⊢
  linarith

lemma limT_valid : TValid X₀ (limT θ X₀ U) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_, fun y => ?_, ?_⟩
  · have hx : x ≤ hor X₀ (nT X₀ x + nT X₀ y) := by
      have := le_hor_nT (X₀ := X₀) x
      unfold hor at this ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (nT X₀ y)]
    have hy : y ≤ hor X₀ (nT X₀ x + nT X₀ y) := by
      have := le_hor_nT (X₀ := X₀) y
      unfold hor at this ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (nT X₀ x)]
    rw [h.limT_eq hx, h.limT_eq hy]
    exact (iterM θ X₀ U _).T_mono hxy
  · have hx1 := le_hor_nT (X₀ := X₀) x
    apply ((iterM θ X₀ U (nT X₀ x)).T_rcont x).congr_of_eventuallyEq
    · filter_upwards [inter_mem_nhdsWithin (Ici x) (Iio_mem_nhds (show x < x + 1 by linarith))]
        with z hz
      have := hz.2
      simp only [mem_Iio] at this
      exact h.limT_eq (by linarith)
    · exact h.limT_eq (by linarith)
  · set x := max (X₀ : ℝ) (10 / 7 * (y + X₀ + 1))
    have hm : (X₀ : ℝ) ≤ x := le_max_left _ _
    refine ⟨x, ?_⟩
    rw [limT]
    have := h.phi_linear (iterD θ X₀ U (nT X₀ x)) x hm
    have h2 := le_max_right (X₀ : ℝ) (10 / 7 * (y + X₀ + 1))
    unfold iterM
    linarith
  · rw [limT]; exact (iterM θ X₀ U _).T_start

omit h in
lemma limArr_nonneg (i : ℕ) : 0 ≤ limArr θ X₀ U i := (iterM θ X₀ U _).arr_nonneg i

/-- **The limit slot model.** -/
noncomputable def limModel : SlotModel X₀ :=
  mkModel (limT θ X₀ U) h.limT_valid (limArr θ X₀ U) (limArr_nonneg (θ := θ) (U := U) (X₀ := X₀))

lemma limModel_T : h.limModel.T = limT θ X₀ U := rfl

lemma limModel_low : ∀ x : ℝ, x < X₀ → h.limModel.T x = ⌊x⌋₊ := fun x hx => by
  rw [h.limModel_T, limT]; exact h.iterM_low _ x hx

/-- **The limit agrees with every iterate up to its horizon.** -/
theorem limModel_agree (n : ℕ) : MAgree h.limModel (iterM θ X₀ U n) (hor X₀ n) := by
  have hT : ∀ x ≤ hor X₀ n, h.limModel.T x = (iterM θ X₀ U n).T x := fun x hx =>
    h.limT_eq hx
  have hϑ : h.limModel.ϑ = (iterM θ X₀ U n).ϑ := by
    show (1 / 2 : ℝ) = (Phi θ X₀ _).ϑ; rw [Phi_ϑ]
  refine ⟨hϑ, hT, fun i hi => ?_⟩
  show (iterM θ X₀ U (nA X₀ i)).arr i = (iterM θ X₀ U n).arr i
  have hl : 0 ≤ Real.log (hor X₀ n) := Real.log_nonneg (by linarith [h.hor_ge13 n])
  have hsl : h.limModel.slot i ≤ hor X₀ n := by linarith
  have he := slot_congr hϑ hT hsl
  rcases le_total (nA X₀ i) n with hle | hle
  · have hag := h.iter_agree_le hle
    refine hag.2.2 i ?_
    exact (h.slot_iter_le _ i).trans (h.slotB_le_nA i)
  · have hag := h.iter_agree_le hle
    exact (hag.2.2 i (by rw [he]; exact hi)).symm

/-- The next step from the limit agrees with the limit up to every horizon. -/
theorem limModel_step_agree (n : ℕ) :
    MAgree (Phi θ X₀ (DM h.limModel U)) h.limModel (hor X₀ (n + 1)) := by
  have hz : (X₀ : ℝ) ≤ hor X₀ (n + 1) := by unfold hor; push_cast; linarith
  have e : hor X₀ (n + 1) - 1 = hor X₀ n := by unfold hor; push_cast; ring
  have h1 : MAgree (Phi θ X₀ (DM h.limModel U)) (iterM θ X₀ U (n + 1)) (hor X₀ (n + 1)) := by
    rw [iterM_succ]
    refine causal (by linarith [h.hθ.1]) (by linarith [h.hθ.2]) h.hX h.hU h.hV h.hS
      h.limModel_low (h.iterM_low n) hz ?_
    rw [e]; exact h.limModel_agree n
  exact h1.trans (by linarith [h.hor_ge13 (n + 1)])
    ((h.limModel_agree (n + 1)).symm (by linarith [h.hor_ge13 (n + 1)]))

/-- **The fixed-point equation for the target**: the target of the limit is the target (6) of
its own prime data. -/
theorem limModel_T_eq (x : ℝ) : h.limModel.T x = targetD θ X₀ (DM h.limModel U) x := by
  have hx := le_hor_nT (X₀ := X₀) x
  have hag := h.limModel_step_agree (nT X₀ x)
  have hxn : x ≤ hor X₀ (nT X₀ x + 1) := by
    unfold hor at hx ⊢; push_cast; linarith
  rw [← hag.2.1 x hxn, h.phi_T]

lemma limModel_ϑ : h.limModel.ϑ = 1 / 2 := rfl

/-- The slots of the limit are the slots of the target of its own prime data. -/
lemma limModel_slot (k : ℕ) :
    h.limModel.slot k = slotOf X₀ (1 / 2) (targetD θ X₀ (DM h.limModel U)) k := by
  rw [slot_eq_slotOf, h.limModel_ϑ]
  congr 1
  funext x
  exact h.limModel_T_eq x

/-- **The fixed-point equation for the arrivals**: the arrivals of the limit at relative slot
`k + 1` are the composites of its own prime data in its own slot `[s_{k+1}, s_{k+2})`. -/
theorem limModel_arr (k : ℕ) :
    h.limModel.arr (k + 1) =
      compCount X₀ (DM h.limModel U) (h.limModel.slot (k + 1)) (h.limModel.slot (k + 2)) := by
  set i := k + 1
  have hag := (h.limModel_step_agree (nA X₀ i)).symm (by linarith [h.hor_ge13 (nA X₀ i + 1)])
  have hsl : h.limModel.slot i ≤ hor X₀ (nA X₀ i + 1) - 13 * Real.log (hor X₀ (nA X₀ i + 1)) := by
    have hlin : ∀ x, (X₀ : ℝ) ≤ x → 7 / 10 * x - X₀ - 1 ≤ h.limModel.T x := fun x hx => by
      rw [h.limModel_T_eq x]; exact targetD_ge_linear (by linarith [h.hθ.2]) h.hX _ hx
    have h1 : h.limModel.slot i ≤ slotB X₀ i := slot_le_linear h.hX hlin i
    have h2 := h.slotB_le_nA i
    have h3 : hor X₀ (nA X₀ i) - 13 * Real.log (hor X₀ (nA X₀ i)) ≤
        hor X₀ (nA X₀ i + 1) - 13 * Real.log (hor X₀ (nA X₀ i + 1)) :=
      sub_log_mono (h.hor_ge13 _) (by unfold hor; push_cast; linarith)
    linarith
  rw [hag.2.2 i hsl, Phi_arr (h.hV _)]
  unfold arrOf
  rw [if_neg (Nat.succ_ne_zero k), ← h.limModel_slot, ← h.limModel_slot]

end Std

open Classical in
/-- **The constructed slot model of §3**: the fixed point of the construction when the standing
conditions hold (a fixed slot model otherwise). Defined for every `θ`, `X₀` and jitters `U`. -/
noncomputable def constructedModel (θ : ℝ) (X₀ : ℕ) (U : ℕ → ℝ) : SlotModel X₀ :=
  if h : Std θ X₀ U then h.limModel else idModel

lemma constructedModel_eq (h : Std θ X₀ U) : constructedModel θ X₀ U = h.limModel := by
  unfold constructedModel; rw [dif_pos h]

end BModel

end
