module

public import RequestProject.Beurling.Model.Identify

/-!
# Placed slot starts in a window (§3.4, proof of Corollary 3.8)

For the constructed model, off the event that a rigid integer `d > X₀` is also in `A` (part of
the null event `𝒩₌` of §3.4: then all jumps of `T` are unit jumps), the window count
`PlacedWindowCount` holds:

* `placed_level` : a slot receiving a prime is a continuous slot, `T(s_j-) = j + ϑ_s`. Off a jump
  this is `T(s_j) ≥ j + ϑ_s`; a jump of `T` at `s_j` sits at a composite element of value `s_j`
  (a rigid integer, or an element of `A`), which would be an arrival of slot `j` unless the slot
  is empty, and then the unit jump reaches the next level;
* `placed_gap` : between two placed slot starts the continuous part `C` of `T` gains at least one
  unit (the jumps in between are at most the levels in between, minus one);
* `limModel_window` : with `C' ≤ 1.01` (Lemma 3.3), a window `(a, b]` holds at most
  `1.01 (b - a) + 1` placed slot starts.
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono

namespace BModel

variable {X₀ : ℕ}

/-! ### The jump part at a point -/

section Jumps

variable (D : PrimeData)

lemma jumpD_floor {x y : ℝ} (hxy : ⌊x⌋₊ = ⌊y⌋₊) (hA : countA (absSet X₀ D) x =
    countA (absSet X₀ D) y) : jumpD X₀ D x = jumpD X₀ D y := by
  unfold jumpD jumpPart Rankin.smoothCount; rw [hxy, hA]

/-- The jump part just below `s`: the rigid integers `< s` and `#(A ∩ [1, s))`. -/
noncomputable def jumpL (X₀ : ℕ) (D : PrimeData) (s : ℝ) : ℝ :=
  ((Rankin.smoothCount X₀ ((⌈s⌉₊ : ℝ) - 1) : ℝ) - Rankin.smoothCount X₀ X₀) +
    countAlt (absSet X₀ D) s

lemma one_le_ceil {s : ℝ} (hs : 0 < s) : 1 ≤ ⌈s⌉₊ := Nat.one_le_iff_ne_zero.mpr
  (by rw [Ne, Nat.ceil_eq_zero, not_le]; exact hs)

lemma ceil_sub_one_cast {s : ℝ} (hs : 0 < s) : (⌈s⌉₊ : ℝ) - 1 = ((⌈s⌉₊ - 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub (one_le_ceil hs)]; simp

lemma ceil_sub_one_lt {s : ℝ} (hs : 0 < s) : (⌈s⌉₊ : ℝ) - 1 < s := by
  linarith [Nat.ceil_lt_add_one hs.le]

/-- On `[⌈s⌉ - 1, s)` the rigid count is that of `⌈s⌉ - 1`. -/
lemma floor_eq_of_ceil {s x : ℝ} (hs : 0 < s) (hx : (⌈s⌉₊ : ℝ) - 1 ≤ x) (hxs : x < s) :
    ⌊x⌋₊ = ⌊(⌈s⌉₊ : ℝ) - 1⌋₊ := by
  rw [ceil_sub_one_cast hs, Nat.floor_natCast]
  rw [ceil_sub_one_cast hs] at hx
  rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hx)]
  refine ⟨hx, ?_⟩
  rw [← ceil_sub_one_cast hs]
  linarith [Nat.le_ceil s]

/-- **The left limit of the jump part**: `J = J(s-)` on `[ℓ, s)` for some `ℓ < s`. -/
lemma jumpD_lconst (hD : LocFinD D) {s : ℝ} (hs : 0 < s) :
    ∃ ℓ < s, ∀ x, ℓ ≤ x → x < s → jumpD X₀ D x = jumpL X₀ D s := by
  obtain ⟨δ, hδ, hc⟩ := countA_lconst (absSet_locFin (X₀ := X₀) hD) s
  refine ⟨max ((⌈s⌉₊ : ℝ) - 1) (s - δ), max_lt (ceil_sub_one_lt hs) (by linarith),
    fun x hx hxs => ?_⟩
  unfold jumpD jumpPart jumpL Rankin.smoothCount
  rw [floor_eq_of_ceil hs ((le_max_left _ _).trans hx) hxs,
    hc x ((le_max_right _ _).trans hx) hxs]

lemma jumpD_int (x : ℝ) : ∃ z : ℤ, jumpD X₀ D x = z := by
  unfold jumpD jumpPart countA
  exact ⟨(Rankin.smoothCount X₀ x : ℤ) - Rankin.smoothCount X₀ X₀ +
    (absSet X₀ D ∩ Set.Icc 1 x).ncard, by push_cast; ring⟩

lemma jumpL_int (s : ℝ) : ∃ z : ℤ, jumpL X₀ D s = z := by
  unfold jumpL countAlt
  exact ⟨(Rankin.smoothCount X₀ ((⌈s⌉₊ : ℝ) - 1) : ℤ) - Rankin.smoothCount X₀ X₀ +
    (absSet X₀ D ∩ Set.Ico 1 s).ncard, by push_cast; ring⟩

lemma card_smoothUpTo_succ (n : ℕ) :
    ((Nat.smoothNumbersUpTo (n + 1) X₀).card : ℝ) =
      (Nat.smoothNumbersUpTo n X₀).card + if n + 1 ∈ Nat.smoothNumbers X₀ then 1 else 0 := by
  classical
  unfold Nat.smoothNumbersUpTo
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]; push_cast; ring
  · simp

open Classical in
/-- The jump of the rigid count at `s`: `[s is an `X₀`-smooth integer]`. -/
lemma smoothCount_jump {s : ℝ} (hs : 0 < s) :
    (Rankin.smoothCount X₀ s : ℝ) - Rankin.smoothCount X₀ ((⌈s⌉₊ : ℝ) - 1) =
      if ∃ n : ℕ, (n : ℝ) = s ∧ n ∈ Nat.smoothNumbers X₀ then 1 else 0 := by
  classical
  set n := ⌈s⌉₊ with hn
  have hn1 := one_le_ceil hs
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : (n : ℝ) - 1 = m := by rw [hm]; push_cast; ring
  unfold Rankin.smoothCount
  rw [hc, Nat.floor_natCast]
  by_cases hns : (n : ℝ) = s
  · rw [← hns, hm]
    have h1 : ⌊((m + 1 : ℕ) : ℝ)⌋₊ = m + 1 := Nat.floor_natCast _
    rw [h1, card_smoothUpTo_succ]
    have e : (∃ k : ℕ, (k : ℝ) = ((m + 1 : ℕ) : ℝ) ∧ k ∈ Nat.smoothNumbers X₀) ↔
        m + 1 ∈ Nat.smoothNumbers X₀ := by
      constructor
      · rintro ⟨k, hk, hks⟩
        have : k = m + 1 := by exact_mod_cast hk
        rwa [← this]
      · intro h; exact ⟨m + 1, rfl, h⟩
    simp only [e]
    ring
  · have hfl : ⌊s⌋₊ = m := by
      rw [Nat.floor_eq_iff hs.le]
      have hlt : s < n := lt_of_le_of_ne (Nat.le_ceil s) (Ne.symm hns)
      constructor
      · have := ceil_sub_one_lt hs
        rw [← hn, hc] at this; exact this.le
      · rw [hm] at hlt; push_cast at hlt; exact hlt
    rw [hfl, if_neg]
    · ring
    rintro ⟨k, hk, -⟩
    apply hns
    rw [hn, ← hk, Nat.ceil_natCast]

open Classical in
/-- **The jump of `T` at a point** `s > 0`: `J(s) - J(s-) = [s is an X₀-smooth integer] +
[s ∈ A]`. -/
lemma jumpD_sub_jumpL (hD : LocFinD D) {s : ℝ} (hs : 0 < s) :
    jumpD X₀ D s - jumpL X₀ D s =
      (if ∃ n : ℕ, (n : ℝ) = s ∧ n ∈ Nat.smoothNumbers X₀ then 1 else 0) +
        (if s ∈ absSet X₀ D then 1 else 0) := by
  have hc := countA_eq_countAlt_add (absSet_locFin (X₀ := X₀) hD) s
  have hj := smoothCount_jump (X₀ := X₀) hs
  have e : (if s ∈ absSet X₀ D ∧ 1 ≤ s then (1 : ℝ) else 0) =
      if s ∈ absSet X₀ D then 1 else 0 := by
    by_cases hA : s ∈ absSet X₀ D
    · have hl : 10 ^ 7 ≤ Real.log s := hA.1
      have h1 : 1 ≤ s := by
        by_contra h1
        push_neg at h1
        have := Real.log_nonpos hs.le h1.le
        linarith
      simp [hA, h1]
    · simp [hA]
  unfold jumpD jumpPart jumpL
  rw [hc, e]
  linarith

end Jumps

/-! ### Elements at the jumps -/

/-- A placed slot has no arrivals. -/
lemma placed_arr_zero {M : SlotModel X₀} {m : ℕ} (hm : placedAt M m) : M.arr (m + 1) = 0 := by
  have hq := greedyQueue_nonneg M.arr m
  have ha := M.arr_nonneg (m + 1)
  unfold placedAt greedyPrime at hm
  omega

/-- A rigid integer `n` is the value of a product of rational primes. -/
lemma exists_rat_elem (M : SlotModel X₀) (U : ℕ → ℝ) {n : ℕ}
    (hn : n ∈ Nat.smoothNumbers X₀) :
    ∃ e : RealisedIdx M →₀ ℕ, idxVal M (capH X₀) U e = n ∧
      ∀ i ∈ e.support, ∃ p, i = Sum.inl p := by
  classical
  obtain ⟨hn0, hp⟩ := Nat.mem_smoothNumbers.mp hn
  set F := n.factorization with hF
  have hsupp : ∀ q ∈ F.support, q.Prime ∧ q < X₀ := by
    intro q hq
    rw [Nat.support_factorization] at hq
    exact ⟨Nat.prime_of_mem_primeFactors hq,
      hp q (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hq)⟩
  set g : {p : ℕ // p.Prime ∧ p < X₀} →₀ ℕ :=
    Finsupp.comapDomain Subtype.val F Subtype.val_injective.injOn with hg
  have hgF : Finsupp.mapDomain Subtype.val g = F := by
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro q hq
    exact ⟨⟨q, hsupp q hq⟩, rfl⟩
  refine ⟨Finsupp.mapDomain Sum.inl g, ?_, fun i hi => ?_⟩
  · unfold idxVal
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have e1 : (g.prod fun p k => realisedVal M (capH X₀) U (Sum.inl p) ^ k) =
        g.prod fun p k => ((p.1 : ℕ) : ℝ) ^ k := rfl
    rw [e1]
    have e2 : (g.prod fun p k => ((p.1 : ℕ) : ℝ) ^ k) =
        (Finsupp.mapDomain Subtype.val g).prod fun q k => ((q : ℕ) : ℝ) ^ k := by
      rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rw [e2, hgF]
    have e3 : (F.prod fun q k => ((q : ℕ) : ℝ) ^ k) = ((F.prod fun q k => q ^ k : ℕ) : ℝ) := by
      rw [Nat.cast_finsuppProd]; push_cast; rfl
    rw [e3, hF, Nat.prod_factorization_pow_eq_self hn0]
  · have := Finsupp.mapDomain_support hi
    simp only [Finset.mem_image] at this
    obtain ⟨p, -, rfl⟩ := this
    exact ⟨p, rfl⟩

/-! ### The constructed model -/

section Constructed

variable {θ : ℝ} {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- Unit jumps: no rigid integer `n > X₀` lies in `A` (off `𝒩₌`). -/
def UnitJumps (X₀ : ℕ) (D : PrimeData) : Prop :=
  ∀ n : ℕ, (X₀ : ℝ) < n → n ∈ Nat.smoothNumbers X₀ → (n : ℝ) ∉ absSet X₀ D

/-- A unit jump at `s`: `s` is not both a rigid integer `> X₀` and an element of `A`. -/
def UnitJumpAt (X₀ : ℕ) (D : PrimeData) (s : ℝ) : Prop :=
  ∀ n : ℕ, (n : ℝ) = s → (X₀ : ℝ) < n → n ∈ Nat.smoothNumbers X₀ → (n : ℝ) ∉ absSet X₀ D

omit h in
lemma UnitJumps.at {D : PrimeData} (h : UnitJumps X₀ D) (s : ℝ) : UnitJumpAt X₀ D s :=
  fun n _ hn hs => h n hn hs

lemma limModel_split {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    h.limModel.T x = X₀ + jumpD X₀ (DM h.limModel U) x + contD θ X₀ (DM h.limModel U) x := by
  rw [h.limModel_T_eq x, targetD_split θ _ hx]

lemma contD_mono' {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    contD θ X₀ (DM h.limModel U) x ≤ contD θ X₀ (DM h.limModel U) x' := by
  have h1 := contD_lower h.hθ h.hX h.hHB (DM h.limModel U) (locFinD_DM h.hX h.hU _) hx hxx
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) h.hX
  have hl : 0 ≤ Real.log x' := Real.log_nonneg (by linarith)
  have : 0 ≤ 0.08 * (x' - x) / Real.log x' := div_nonneg (by linarith) hl
  linarith

/-- A jump of the target sits at a composite element. -/
lemma comp_at_jump {s : ℝ} (hsX : (X₀ : ℝ) < s)
    (hj : (∃ n : ℕ, (n : ℝ) = s ∧ n ∈ Nat.smoothNumbers X₀) ∨ s ∈ absSet X₀ (DM h.limModel U)) :
    ∃ e : RealisedIdx h.limModel →₀ ℕ, 2 ≤ e.sum (fun _ n => n) ∧
      idxVal h.limModel (capH X₀) U e = s := by
  classical
  set M := h.limModel
  have h16 := X₀_ge_two_pow h.hX
  rcases hj with ⟨n, rfl, hsm⟩ | hA
  · have hn := hsX
    obtain ⟨e, hv, hrat⟩ := exists_rat_elem M U hsm
    refine ⟨e, ?_, hv⟩
    by_contra hlt
    push_neg at hlt
    interval_cases hs : e.sum (fun _ n => n)
    · rw [(finsupp_sum_eq_zero_iff e).mp hs, idxVal_zero] at hv
      linarith
    · obtain ⟨i, rfl⟩ := (finsupp_sum_eq_one_iff e).mp hs
      obtain ⟨p, rfl⟩ := hrat i (by simp)
      rw [idxVal_single] at hv
      have hp : ((p.1 : ℕ) : ℝ) < X₀ := by exact_mod_cast p.2.2
      simp only [realisedVal] at hv
      linarith
  · obtain ⟨-, e', he', -, hval, k, hk, -, hy⟩ := hA
    obtain ⟨f, rfl⟩ := exists_mapE (U := U) he'
    rw [eval_mapE] at hval
    refine ⟨f, ?_, hval⟩
    by_contra hlt
    push_neg at hlt
    interval_cases hs : f.sum (fun _ n => n)
    · rw [(finsupp_sum_eq_zero_iff f).mp hs] at hk
      simp [mapE] at hk
    · obtain ⟨i, rfl⟩ := (finsupp_sum_eq_one_iff f).mp hs
      have hkp : placedAt M k := he' k hk
      rw [mapE_apply_inr, dif_pos hkp] at hk
      have hi : i = Sum.inr ⟨k, hkp⟩ := by
        by_contra hne
        exact hk (Finsupp.single_eq_of_ne (Ne.symm hne))
      subst hi
      rw [idxVal_single] at hval
      have hsq := absorbY_le_sqrt (Nat.cast_nonneg _) h.hX (x := s) hsX.le le_rfl
      have hv : primeValueOf M (capH X₀) U k = s := hval
      have hy' : primeValueOf M (capH X₀) U k < absorbY X₀ s := hy
      have hn1 : (1 : ℝ) < s := by linarith
      have : s ^ (1 / 2 : ℝ) < s := by
        calc s ^ (1 / 2 : ℝ) < s ^ (1 : ℝ) :=
              Real.rpow_lt_rpow_of_exponent_lt hn1 (by norm_num)
          _ = s := Real.rpow_one _
      linarith

/-- The facts about the constructed model used for the window count. -/
structure WinFacts (θ : ℝ) (M : SlotModel X₀) (U : ℕ → ℝ) : Prop where
  split : ∀ x, (X₀ : ℝ) ≤ x → M.T x = X₀ + jumpD X₀ (DM M U) x + contD θ X₀ (DM M U) x
  cmono : ∀ x x', (X₀ : ℝ) ≤ x → x ≤ x' → contD θ X₀ (DM M U) x ≤ contD θ X₀ (DM M U) x'
  cup : ∀ x x', (X₀ : ℝ) ≤ x → x ≤ x' →
    contD θ X₀ (DM M U) x' - contD θ X₀ (DM M U) x ≤ 1.01 * (x' - x)
  comp : ∀ s : ℝ, (X₀ : ℝ) < s →
    ((∃ n : ℕ, (n : ℝ) = s ∧ n ∈ Nat.smoothNumbers X₀) ∨ s ∈ absSet X₀ (DM M U)) →
    ∃ e : RealisedIdx M →₀ ℕ, 2 ≤ e.sum (fun _ n => n) ∧ idxVal M (capH X₀) U e = s
  linked : ArrivalsLinked M (capH X₀) U
  ok : RealisedOK M (capH X₀) U
  big : (2 : ℝ) ^ (16 : ℕ) ≤ X₀
  fin : LocFinD (DM M U)

lemma winFacts : WinFacts θ h.limModel U :=
  ⟨fun _ hx => limModel_split h hx, fun _ _ hx hxx => contD_mono' h hx hxx,
    fun _ _ hx hxx => contD_upper h.hθ h.hX _ (locFinD_DM h.hX h.hU _) hx hxx,
    fun _ hn hj => comp_at_jump h hn hj, limModel_linked h, limModel_realisedOK h,
    X₀_ge_two_pow h.hX, locFinD_DM h.hX h.hU _⟩

end Constructed

section Window

variable {θ : ℝ} {U : ℕ → ℝ} {M : SlotModel X₀} (W : WinFacts θ M U)
include W

/-- **A slot receiving a prime is a continuous slot**: `X₀ + J(s-) + C(s) = j + ϑ_s`. -/
theorem placed_level {m : ℕ} (hunit : UnitJumpAt X₀ (DM M U) (M.slot (m + 1)))
    (hm : placedAt M m) (hs : (X₀ : ℝ) < M.slot (m + 1)) :
    (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot (m + 1)) + contD θ X₀ (DM M U) (M.slot (m + 1)) =
      M.level (m + 1) := by
  classical
  have h16 := W.big
  have hs0 : 0 < M.slot (m + 1) := by linarith
  obtain ⟨ℓ, hℓ, hJ⟩ := jumpD_lconst (X₀ := X₀) (DM M U) W.fin hs0
  apply le_antisymm
  · by_contra hgt
    push_neg at hgt
    set δ := ((X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot (m + 1)) +
      contD θ X₀ (DM M U) (M.slot (m + 1)) - M.level (m + 1)) / 2.02 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
    set x := max (max ℓ X₀) (M.slot (m + 1) - δ) with hxdef
    have hxs : x < M.slot (m + 1) := max_lt (max_lt hℓ hs) (by linarith)
    have hxX : (X₀ : ℝ) ≤ x := (le_max_right _ _).trans (le_max_left _ _)
    have hxc : ℓ ≤ x := (le_max_left _ _).trans (le_max_left _ _)
    have hxd : M.slot (m + 1) - δ ≤ x := le_max_right _ _
    have hT := M.T_lt_level (by linarith) hxs
    rw [W.split _ hxX, hJ x hxc hxs] at hT
    have hC := W.cup _ _ hxX hxs.le
    have h2 : 2.02 * δ = (X₀ : ℝ) + jumpL X₀ (DM M U) (M.slot (m + 1)) +
        contD θ X₀ (DM M U) (M.slot (m + 1)) - M.level (m + 1) := by rw [hδ]; ring
    linarith
  · have hTs := M.level_le_T_slot (m + 1)
    rw [W.split _ hs.le] at hTs
    have hdiff := jumpD_sub_jumpL (X₀ := X₀) (DM M U) W.fin hs0
    by_cases hz : jumpD X₀ (DM M U) (M.slot (m + 1)) = jumpL X₀ (DM M U) (M.slot (m + 1))
    · rw [hz] at hTs; exact hTs
    have hj : (∃ n : ℕ, (n : ℝ) = M.slot (m + 1) ∧ n ∈ Nat.smoothNumbers X₀) ∨
        M.slot (m + 1) ∈ absSet X₀ (DM M U) := by
      by_contra hc
      push_neg at hc
      rw [if_neg (fun ⟨n, hn, hn'⟩ => hc.1 n hn hn'), if_neg hc.2] at hdiff
      exact hz (by linarith)
    have hle1 : jumpD X₀ (DM M U) (M.slot (m + 1)) - jumpL X₀ (DM M U) (M.slot (m + 1)) ≤ 1 := by
      rw [hdiff]
      by_cases h1 : ∃ n : ℕ, (n : ℝ) = M.slot (m + 1) ∧ n ∈ Nat.smoothNumbers X₀
      · obtain ⟨n, hn, hsm⟩ := h1
        have hnX : (X₀ : ℝ) < n := by rw [hn]; exact hs
        have hnA := hunit n hn hnX hsm
        rw [hn] at hnA
        rw [if_pos ⟨n, hn, hsm⟩, if_neg hnA]; norm_num
      · rw [if_neg h1]; split_ifs <;> norm_num
    obtain ⟨e, he2, hev⟩ := W.comp _ hs hj
    have hnext : M.slot (m + 2) ≤ M.slot (m + 1) := by
      by_contra hc
      push_neg at hc
      have hmem : e ∈ compositeSet M (capH X₀) U (M.slot (m + 1)) (M.slot (m + 1 + 1)) :=
        ⟨he2, by rw [hev], by rw [hev]; exact hc⟩
      have hfin : (compositeSet M (capH X₀) U (M.slot (m + 1)) (M.slot (m + 1 + 1))).Finite :=
        (finite_compLt W.ok (M.slot (m + 1 + 1))).subset fun e he => ⟨he.1, he.2.2⟩
      have hpos := (Set.ncard_pos hfin).mpr ⟨e, hmem⟩
      have harr := W.linked m
      unfold compositeArr at harr
      rw [placed_arr_zero hm] at harr
      omega
    have hT2 := M.level_le_T_slot (m + 2)
    have hTmono := M.T_mono hnext
    rw [W.split _ hs.le] at hTmono
    unfold SlotModel.level at hT2 ⊢
    push_cast at hT2 ⊢
    linarith

/-- **Between two placed slot starts the continuous part gains one unit.** -/
theorem placed_gap {m m' : ℕ} (hu : UnitJumpAt X₀ (DM M U) (M.slot (m + 1)))
    (hu' : UnitJumpAt X₀ (DM M U) (M.slot (m' + 1))) (hmm : m < m')
    (hm : placedAt M m) (hm' : placedAt M m') (hs : (X₀ : ℝ) < M.slot (m + 1)) :
    1 ≤ contD θ X₀ (DM M U) (M.slot (m' + 1)) - contD θ X₀ (DM M U) (M.slot (m + 1)) := by
  have h16 := W.big
  have hss : M.slot (m + 1) ≤ M.slot (m' + 1) := M.slot_mono (by omega)
  have hs' : (X₀ : ℝ) < M.slot (m' + 1) := lt_of_lt_of_le hs hss
  have hL := placed_level W hu hm hs
  have hL' := placed_level W hu' hm' hs'
  have hmm' : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hmm
  unfold SlotModel.level at hL hL'
  push_cast at hL hL'
  have hlt : M.slot (m + 1) < M.slot (m' + 1) := by
    rcases hss.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      rw [← h1] at hL'
      linarith
  have hs0 : 0 < M.slot (m' + 1) := by linarith
  obtain ⟨ℓ, hℓ, hJ⟩ := jumpD_lconst (X₀ := X₀) (DM M U) W.fin hs0
  have hxs : max ℓ (M.slot (m + 1)) < M.slot (m' + 1) := max_lt hℓ hlt
  have hxs1 : M.slot (m + 1) ≤ max ℓ (M.slot (m + 1)) := le_max_right _ _
  have hT := M.T_lt_level (by linarith) hxs
  rw [W.split _ (by linarith), hJ _ (le_max_left _ _) hxs] at hT
  have hCm := W.cmono _ _ hs.le hxs1
  unfold SlotModel.level at hT
  push_cast at hT
  obtain ⟨z, hz⟩ := jumpL_int (X₀ := X₀) (DM M U) (M.slot (m + 1))
  obtain ⟨z', hz'⟩ := jumpL_int (X₀ := X₀) (DM M U) (M.slot (m' + 1))
  rw [hz] at hL
  rw [hz'] at hL' hT
  have hmz : (z' : ℝ) - z < m' - m := by linarith
  have hmz' : z' - z < (m' : ℤ) - m := by exact_mod_cast hmz
  have hmz'' : ((z' - z : ℤ) : ℝ) ≤ (m' : ℝ) - m - 1 := by
    have : z' - z ≤ (m' : ℤ) - m - 1 := by omega
    exact_mod_cast this
  push_cast at hmz''
  linarith

/-- **Placed slot starts with unit jumps in a window**: a window `(a, b]` holds at most
`1.01 (b - a) + 1` starts of placed slots of `S₀` (each with a unit jump at its start). -/
theorem window_count_on (S₀ : Set ℕ)
    (hS₀ : ∀ m ∈ S₀, placedAt M m ∧ UnitJumpAt X₀ (DM M U) (M.slot (m + 1)))
    (hslot1 : (X₀ : ℝ) < M.slot 1) {a b : ℝ} (hab : a ≤ b) :
    ({m | m ∈ S₀ ∧ a < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}.ncard : ℝ) ≤
      1.01 * (b - a) + 1 := by
  classical
  set S := {m | m ∈ S₀ ∧ a < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}
  have hge : ∀ m, (X₀ : ℝ) < M.slot (m + 1) := fun m =>
    lt_of_lt_of_le hslot1 (M.slot_mono (by omega))
  rcases S.eq_empty_or_nonempty with hS | ⟨m₀, hm₀⟩
  · rw [hS, Set.ncard_empty]; push_cast; linarith
  have hL0 : 0 ≤ 1.01 * (b - a) := by nlinarith
  set C := contD θ X₀ (DM M U)
  set g : ℕ → ℕ := fun m => ⌊C (M.slot (m + 1)) - C (max a (X₀ : ℝ))⌋₊
  have hpos : ∀ m ∈ S, 0 ≤ C (M.slot (m + 1)) - C (max a (X₀ : ℝ)) := by
    intro m hm
    have := W.cmono _ _ (le_max_right a (X₀ : ℝ)) (max_le hm.2.1.le (hge m).le)
    linarith
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' hg
    by_contra hne
    have h3 : (g m : ℝ) = g m' := by rw [hg]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := placed_gap W (hS₀ m hm.1).2 (hS₀ m' hm'.1).2 hlt (hS₀ m hm.1).1
        (hS₀ m' hm'.1).1 (hge m)
      have h1 := Nat.floor_le (hpos m hm)
      have h2 := Nat.lt_floor_add_one (C (M.slot (m' + 1)) - C (max a (X₀ : ℝ)))
      simp only [g] at h3
      linarith
    · have := placed_gap W (hS₀ m' hm'.1).2 (hS₀ m hm.1).2 hlt (hS₀ m' hm'.1).1
        (hS₀ m hm.1).1 (hge m')
      have h1 := Nat.floor_le (hpos m' hm')
      have h2 := Nat.lt_floor_add_one (C (M.slot (m + 1)) - C (max a (X₀ : ℝ)))
      simp only [g] at h3
      linarith
  have hmaps : Set.MapsTo g S (Finset.range (⌊1.01 * (b - a)⌋₊ + 1) : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    have hup := W.cup _ _ (le_max_right a (X₀ : ℝ)) (max_le hm.2.1.le (hge m).le)
    have : M.slot (m + 1) - max a (X₀ : ℝ) ≤ b - a := by
      have := le_max_left a (X₀ : ℝ); linarith [hm.2.2]
    have h0 : 0 ≤ M.slot (m + 1) - max a (X₀ : ℝ) := by
      have := max_le hm.2.1.le (hge m).le; linarith
    nlinarith
  have hcard := Set.ncard_le_ncard_of_injOn g hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at hcard
  have h1 : ((⌊1.01 * (b - a)⌋₊ + 1 : ℕ) : ℝ) ≤ 1.01 * (b - a) + 1 := by
    push_cast; linarith [Nat.floor_le hL0]
  have hc : (S.ncard : ℝ) ≤ ((⌊1.01 * (b - a)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Placed slot starts in a window** (`PlacedWindowCount`, §3.4). -/
theorem window_count (hunit : UnitJumps X₀ (DM M U)) (hslot1 : (X₀ : ℝ) < M.slot 1) :
    PlacedWindowCount M := by
  intro a b hab
  have h := window_count_on W {m | placedAt M m} (fun m hm => ⟨hm, hunit.at _⟩) hslot1 hab
  simpa using h

end Window


end BModel

end
