module

public import RequestProject.Beurling.Construction.ElemCount

/-!
# Slot counts for the linked construction

The counting identities behind Corollary 3.8 for the construction whose arrivals are the
composites of the realised system:

* `realised_primes_eq`: for `x ≥ X₀`, the primes `≤ x` are the rational primes, plus the primes
  placed at relative slots `< k`, minus those landing above `x`, plus those placed later landing at
  or below `x`;
* `realised_comp_eq`: the composites `≤ x` are the composites `< y` minus those in `(x, y)`;
* `V_eq_count`: Lemma 3.6, from its base case at the first slot;
* `compIoo_le_slotArr`: the composites in `(x, s_{k+1})` are at most the arrivals `A_k`.
-/

@[expose] public section

open Set Real CaplLink SlotModel Target Oscillation Absorbed Filter QueueMono Greedy Bookkeeping
  DesignedZero GoodHeights Decomp

namespace Construction

section Slots

variable {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}

/-- Every slot start from relative slot `1` on is at least `X₀`. -/
lemma slot_ge_of_low (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {k : ℕ} (hk : 1 ≤ k) :
    (X₀ : ℝ) ≤ M.slot k := by
  obtain ⟨h1, hlev⟩ := M.slot_mem k
  by_contra hlt
  push_neg at hlt
  rw [hTlow _ hlt] at hlev
  have hfl : (⌊M.slot k⌋₊ : ℝ) ≤ M.slot k := Nat.floor_le (by linarith)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold level at hlev
  linarith [M.hϑ0]

/-- Only finitely many slot starts lie below any bound. -/
lemma finite_slot_succ_le (b : ℝ) : {m : ℕ | M.slot (m + 1) ≤ b}.Finite := by
  apply (Set.finite_Iic ⌈M.T b - X₀⌉₊).subset
  intro m hm
  simp only [mem_setOf_eq] at hm
  simp only [mem_Iic]
  have hT := (M.slot_mem (m + 1)).2.trans (M.T_mono hm)
  unfold level at hT
  have : (m : ℝ) ≤ M.T b - X₀ := by push_cast at hT; linarith [M.hϑ0]
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- The composites of value `< y` are finitely many. -/
lemma finite_compLt (h : RealisedOK M H U) (y : ℝ) : (compLt M H U y).Finite :=
  (finite_idxVal_le h y).subset fun _ he => he.2.le

/-- **The composites `≤ x` are those `< y` minus those in `(x, y)`.** -/
theorem realised_comp_eq (h : RealisedOK M H U) {x y : ℝ} (hxy : x < y) :
    ((compLe M H U x).ncard : ℝ) =
      ((compLt M H U y).ncard : ℝ) - ((compIoo M H U x y).ncard : ℝ) := by
  have hsub : compIoo M H U x y ⊆ compLt M H U y := fun e he => ⟨he.1, he.2.2⟩
  have hdiff : compLt M H U y \ compIoo M H U x y = compLe M H U x := by
    ext e
    simp only [compLt, compIoo, compLe, mem_diff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h2, hy⟩, hn⟩
      refine ⟨h2, ?_⟩
      by_contra hc
      push_neg at hc
      exact hn ⟨h2, hc, hy⟩
    · rintro ⟨h2, hx⟩
      exact ⟨⟨h2, by linarith⟩, fun ⟨_, hc, _⟩ => by linarith⟩
  have := Set.ncard_diff_add_ncard_of_subset hsub (finite_compLt h y)
  rw [hdiff] at this
  rw [← this]
  push_cast
  ring

/-- The placed primes landing at or below `x` are finitely many. -/
lemma finite_placed_le (h : RealisedOK M H U) (x : ℝ) :
    {m | placedAt M m ∧ primeValueOf M H U m ≤ x}.Finite := by
  have hpre : ((Sum.inr : {k : ℕ // placedAt M k} → RealisedIdx M) ⁻¹'
      {i | realisedVal M H U i ≤ x}).Finite :=
    (h.finite_le x).preimage Sum.inr_injective.injOn
  apply (hpre.image Subtype.val).subset
  rintro m ⟨hm, hv⟩
  exact ⟨⟨m, hm⟩, hv, rfl⟩

/-- **The primes `≤ x`**, for `x ≥ X₀`: the rational primes, plus the primes placed at relative
slots `< k`, minus those of them landing above `x`, plus the primes placed later landing at or
below `x`. -/
theorem realised_primes_eq (h : RealisedOK M H U) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) (k : ℕ) :
    ({i | realisedVal M H U i ≤ x}.ncard : ℝ) =
      ({p : ℕ | p.Prime ∧ p < X₀}.ncard : ℝ) + ((placedBefore M k).ncard : ℝ) -
        ((emSet M H U k x).ncard : ℝ) + ((epSet M H U k x).ncard : ℝ) := by
  classical
  set R : Set {p : ℕ // p.Prime ∧ p < X₀} := univ
  set P : Set {k : ℕ // placedAt M k} := {q | primeValueOf M H U q.1 ≤ x}
  have hsplit : {i | realisedVal M H U i ≤ x} = Sum.inl '' R ∪ Sum.inr '' P := by
    ext i
    cases i with
    | inl p =>
      refine ⟨fun _ => Or.inl ⟨p, mem_univ _, rfl⟩, fun _ => ?_⟩
      show (p.1 : ℝ) ≤ x
      have : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
      linarith
    | inr q =>
      simp [realisedVal, P]
  have hfin := h.finite_le x
  have hdisj : Disjoint (Sum.inl '' R) (Sum.inr '' P) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    cases hb
  have hRfin : (Sum.inl '' R : Set (RealisedIdx M)).Finite :=
    hfin.subset (by rw [hsplit]; exact subset_union_left)
  have hPfin : (Sum.inr '' P : Set (RealisedIdx M)).Finite :=
    hfin.subset (by rw [hsplit]; exact subset_union_right)
  have hR : (Sum.inl '' R : Set (RealisedIdx M)).ncard = {p : ℕ | p.Prime ∧ p < X₀}.ncard := by
    rw [Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ]
    exact Nat.card_coe_set_eq {p : ℕ | p.Prime ∧ p < X₀}
  set Q := {m | placedAt M m ∧ primeValueOf M H U m ≤ x}
  have hP : (Sum.inr '' P : Set (RealisedIdx M)).ncard = Q.ncard := by
    rw [Set.ncard_image_of_injective _ Sum.inr_injective]
    have : Q = Subtype.val '' P := by
      ext m
      simp only [Q, P, mem_setOf_eq, mem_image, Subtype.exists, exists_and_right,
        exists_eq_right]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
    rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hQ : Q = (placedBefore M k \ emSet M H U k x) ∪ epSet M H U k x := by
    ext m
    simp only [Q, placedBefore, emSet, epSet, mem_setOf_eq, mem_union, mem_diff, not_and,
      not_lt]
    constructor
    · rintro ⟨hm, hv⟩
      rcases Nat.lt_or_ge m k with hk | hk
      · exact Or.inl ⟨⟨hm, hk⟩, fun _ _ => hv⟩
      · exact Or.inr ⟨hm, hk, hv⟩
    · rintro (⟨⟨hm, hk⟩, hv⟩ | ⟨hm, -, hv⟩)
      · exact ⟨hm, hv hm hk⟩
      · exact ⟨hm, hv⟩
  have hQfin : Q.Finite := finite_placed_le h x
  have hd2 : Disjoint (placedBefore M k \ emSet M H U k x) (epSet M H U k x) := by
    rw [Set.disjoint_left]
    rintro m ⟨⟨-, hk⟩, -⟩ ⟨-, hk', -⟩
    omega
  have hpbfin : (placedBefore M k).Finite := (Set.finite_Iio k).subset fun m hm => hm.2
  have hemsub : emSet M H U k x ⊆ placedBefore M k := fun m hm => ⟨hm.1, hm.2.1⟩
  have hdiff := Set.ncard_diff_add_ncard_of_subset hemsub hpbfin
  rw [hsplit, Set.ncard_union_eq hdisj hRfin hPfin, hR, hP, hQ,
    Set.ncard_union_eq hd2 (hpbfin.diff) (hQfin.subset (by rw [hQ]; exact subset_union_right))]
  have hd' : ((placedBefore M k \ emSet M H U k x).ncard : ℝ) =
      ((placedBefore M k).ncard : ℝ) - ((emSet M H U k x).ncard : ℝ) := by
    rw [← hdiff]; push_cast; ring
  push_cast
  rw [hd']
  ring

/-- `compLt` grows by the composites of the next slot. -/
lemma compLt_succ_eq (k : ℕ) :
    compLt M H U (M.slot (k + 2)) =
      compLt M H U (M.slot (k + 1)) ∪ compositeSet M H U (M.slot (k + 1)) (M.slot (k + 2)) := by
  have hmono : M.slot (k + 1) ≤ M.slot (k + 2) := M.slot_mono (by omega)
  ext e
  simp only [compLt, compositeSet, mem_union, mem_setOf_eq]
  constructor
  · rintro ⟨h2, hy⟩
    rcases lt_or_ge (idxVal M H U e) (M.slot (k + 1)) with h | h
    · exact Or.inl ⟨h2, h⟩
    · exact Or.inr ⟨h2, h, hy⟩
  · rintro (⟨h2, hy⟩ | ⟨h2, -, hy⟩)
    · exact ⟨h2, lt_of_lt_of_le hy hmono⟩
    · exact ⟨h2, hy⟩

/-- `placedBefore` grows by the decision at the current slot. -/
lemma placedBefore_succ_ncard (k : ℕ) :
    ((placedBefore M (k + 1)).ncard : ℝ) =
      ((placedBefore M k).ncard : ℝ) + (greedyPrime M.arr k : ℝ) := by
  classical
  have hpbfin : (placedBefore M k).Finite := (Set.finite_Iio k).subset fun m hm => hm.2
  by_cases hk : placedAt M k
  · have heq : placedBefore M (k + 1) = insert k (placedBefore M k) := by
      ext m
      simp only [placedBefore, mem_insert_iff, mem_setOf_eq]
      constructor
      · rintro ⟨hm, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact Or.inr ⟨hm, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hm, hlt⟩)
        · exact ⟨hk, by omega⟩
        · exact ⟨hm, by omega⟩
    have hnot : k ∉ placedBefore M k := fun h => lt_irrefl _ h.2
    rw [heq, Set.ncard_insert_of_notMem hnot hpbfin]
    have : greedyPrime M.arr k = 1 := hk
    rw [this]
    push_cast
    ring
  · have heq : placedBefore M (k + 1) = placedBefore M k := by
      ext m
      simp only [placedBefore, mem_setOf_eq]
      constructor
      · rintro ⟨hm, hlt⟩
        refine ⟨hm, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact h
        · subst h; exact absurd hm hk
      · rintro ⟨hm, hlt⟩
        exact ⟨hm, by omega⟩
    rw [heq, greedyPrime_eq_zero_of_ne_one M.arr_nonneg hk]
    simp

/-- **Lemma 3.6 (count identity) for the construction**, from its base case at the first slot:
`V_k = #(composites < s_{k+1}) + #(rational primes) + #(primes placed at slots ≤ k) + 1`. -/
theorem V_eq_count (h : RealisedOK M H U) (hlink : ArrivalsLinked M H U)
    (hinit : (X₀ : ℝ) = ((compLt M H U (M.slot 1)).ncard : ℝ) +
      ({p : ℕ | p.Prime ∧ p < X₀}.ncard : ℝ) + 1) (k : ℕ) :
    (M.V k : ℝ) = ((compLt M H U (M.slot (k + 1))).ncard : ℝ) +
      ({p : ℕ | p.Prime ∧ p < X₀}.ncard : ℝ) + ((placedBefore M k).ncard : ℝ) + 1 := by
  induction k with
  | zero =>
    rw [M.V_zero]
    have : placedBefore M 0 = ∅ := by
      ext m; simp [placedBefore]
    rw [this, Set.ncard_empty]
    push_cast
    rw [hinit]
    ring
  | succ k ih =>
    have hstep := M.V_step k
    have harr := hlink k
    unfold compositeArr at harr
    have hd : Disjoint (compLt M H U (M.slot (k + 1)))
        (compositeSet M H U (M.slot (k + 1)) (M.slot (k + 2))) := by
      rw [Set.disjoint_left]
      rintro e ⟨-, h1⟩ ⟨-, h2, -⟩
      linarith
    have hfin2 : (compositeSet M H U (M.slot (k + 1)) (M.slot (k + 2))).Finite :=
      (finite_compLt h (M.slot (k + 2))).subset fun e he => ⟨he.1, he.2.2⟩
    have hc : ((compLt M H U (M.slot (k + 1 + 1))).ncard : ℝ) =
        ((compLt M H U (M.slot (k + 1))).ncard : ℝ) +
          ((compositeSet M H U (M.slot (k + 1)) (M.slot (k + 2))).ncard : ℝ) := by
      rw [compLt_succ_eq, Set.ncard_union_eq hd (finite_compLt h _) hfin2]
      push_cast; ring
    have hstepR : (M.V (k + 1) : ℝ) = (M.V k : ℝ) + (M.arr (k + 1) : ℝ) +
        (greedyPrime M.arr k : ℝ) := by
      rw [hstep]; push_cast; ring
    rw [hstepR, ih, harr, hc, placedBefore_succ_ncard]
    push_cast
    ring

/-- **`C ≤ A_k`**: the composites in `(x, s_{k+1})` are arrivals of slot `k` (for `k = 0`, there
are none, by the base case `(X₀, s_1) ∩ composites = ∅`). -/
theorem compIoo_le_slotArr (h : RealisedOK M H U) (hlink : ArrivalsLinked M H U)
    (hgap : compIoo M H U X₀ (M.slot 1) = ∅) (hX₀ : 1 ≤ X₀) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    ((compIoo M H U x (M.slot (M.slotIdx x + 1))).ncard : ℝ) ≤
      (M.slotArr (M.slotIdx x) : ℝ) := by
  obtain ⟨hs, -, -, -⟩ := M.mem_slot hX₀ hx
  rcases Nat.eq_zero_or_pos (M.slotIdx x) with hk | hk
  · have hsub : compIoo M H U x (M.slot (M.slotIdx x + 1)) ⊆ compIoo M H U X₀ (M.slot 1) := by
      rintro e ⟨h2, h3, h4⟩
      rw [hk] at h4
      exact ⟨h2, lt_of_le_of_lt hx h3, h4⟩
    rw [hgap, Set.subset_empty_iff] at hsub
    rw [hsub, Set.ncard_empty]
    simp [slotArr, hk]
  · obtain ⟨j, hj⟩ : ∃ j, M.slotIdx x = j + 1 := ⟨M.slotIdx x - 1, by omega⟩
    have harr := hlink j
    unfold compositeArr at harr
    rw [hj] at hs ⊢
    have hsub : compIoo M H U x (M.slot (j + 1 + 1)) ⊆
        compositeSet M H U (M.slot (j + 1)) (M.slot (j + 1 + 1)) := by
      rintro e ⟨h2, h3, h4⟩
      exact ⟨h2, by linarith, h4⟩
    have hfin : (compositeSet M H U (M.slot (j + 1)) (M.slot (j + 1 + 1))).Finite :=
      (finite_compLt h _).subset fun e he => ⟨he.1, he.2.2⟩
    have hle := Set.ncard_le_ncard hsub hfin
    simp only [slotArr, Nat.add_one_ne_zero, if_false, harr]
    push_cast
    exact_mod_cast hle

/-! ### The bounds on `E±` -/

/-- **Placed slot starts in a window** (§3.4 and Corollary 3.8): only continuous slots receive
primes, consecutive continuous-slot starts are one unit of continuous mass apart, and
`T'_cont ≤ 1.01`; so a window `(a, b]` holds at most `1.01 (b - a) + 1` starts of slots at which a
prime is placed. -/
def PlacedWindowCount {X₀ : ℕ} (M : SlotModel X₀) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    ({m | placedAt M m ∧ a < M.slot (m + 1) ∧ M.slot (m + 1) ≤ b}.ncard : ℝ) ≤ 1.01 * (b - a) + 1

/-- **The jitter width varies slowly** (Theorem 6.23(c)): if `x ≤ y` and `y - H(y)/2 ≤ x`, then
`H(y) ≤ H(x) + 1/4`. A deterministic property of `H`. -/
def JitterWidthRegular (X₀ : ℕ) : Prop :=
  ∀ x y : ℝ, (X₀ : ℝ) ≤ x → x ≤ y → y - capH X₀ y / 2 ≤ x → capH X₀ y ≤ capH X₀ x + 1 / 4

lemma primeValueOf_le_box (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hH : ∀ s, 0 ≤ H s) (m : ℕ) :
    primeValueOf M H U m ≤ M.slot (m + 1) + H (M.slot (m + 1)) / 2 := by
  unfold primeValueOf landing
  have := (hU (m + 1)).2
  nlinarith [hH (M.slot (m + 1))]

lemma primeValueOf_ge_box (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hH : ∀ s, 0 ≤ H s) (m : ℕ) :
    M.slot (m + 1) - H (M.slot (m + 1)) / 2 ≤ primeValueOf M H U m := by
  unfold primeValueOf landing
  have := (hU (m + 1)).1
  nlinarith [hH (M.slot (m + 1))]

/-- **`E₋ ≤ H(x) + 3/2`**: the primes placed at slots `≤ k` that land above `x` were placed at
slots starting in `(x - H(x)/2, x]`. -/
theorem Em_le (hX : 10 ^ 8 ≤ Real.log X₀) (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) (hW : PlacedWindowCount M) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) :
    ((emSet M (capH X₀) U (M.slotIdx x) x).ncard : ℝ) ≤ capH X₀ x + 3 / 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast (one_lt_of_logX hX0 hX).le
  have hH0 := capH_nonneg (X₀ : ℝ) x
  obtain ⟨hs, -, -, -⟩ := M.mem_slot hX₀ hx
  set W := {m | placedAt M m ∧ x - capH X₀ x / 2 < M.slot (m + 1) ∧ M.slot (m + 1) ≤ x}
  have hsub : emSet M (capH X₀) U (M.slotIdx x) x ⊆ W := by
    rintro m ⟨hm, hk, hv⟩
    have hsk : M.slot (m + 1) ≤ x := (M.slot_mono (by omega)).trans hs
    have hsX : (X₀ : ℝ) ≤ M.slot (m + 1) := slot_ge_of_low hTlow (by omega)
    have hHm : capH X₀ (M.slot (m + 1)) ≤ capH X₀ x :=
      capH_monotoneOn hX0 hX hsX hx hsk
    have hpv := primeValueOf_le_box (M := M) hU (capH_nonneg (X₀ : ℝ)) m
    refine ⟨hm, by linarith, hsk⟩
  have hWfin : W.Finite := (finite_slot_succ_le x).subset fun m hm => hm.2.2
  have hle : ((emSet M (capH X₀) U (M.slotIdx x) x).ncard : ℝ) ≤ (W.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hWfin
  have hw := hW (x - capH X₀ x / 2) x (by linarith)
  linarith

/-- **`E₊ ≤ H(x) + 3/2`**: the primes placed at slots `> k` that land at or below `x` were placed at
slots starting in `(x, y]`, with `y` the latest such start, `y - H(y)/2 ≤ x`. -/
theorem Ep_le (h : RealisedOK M (capH X₀) U) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hW : PlacedWindowCount M) (hreg : JitterWidthRegular X₀) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    ((epSet M (capH X₀) U (M.slotIdx x) x).ncard : ℝ) ≤ capH X₀ x + 3 / 2 := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast (one_lt_of_logX hX0 hX).le
  have hH0 := capH_nonneg (X₀ : ℝ) x
  obtain ⟨-, hs1, -, -⟩ := M.mem_slot hX₀ hx
  set E := epSet M (capH X₀) U (M.slotIdx x) x
  have hEfin : E.Finite := (finite_placed_le h x).subset fun m hm => ⟨hm.1, hm.2.2⟩
  rcases E.eq_empty_or_nonempty with he | hne
  · rw [he, Set.ncard_empty]; push_cast; linarith
  obtain ⟨m₀, hm₀, hmax⟩ := hEfin.toFinset.exists_max_image (fun m => M.slot (m + 1))
    (by simpa using hne)
  rw [Set.Finite.mem_toFinset] at hm₀
  set y := M.slot (m₀ + 1)
  have hgt : ∀ m ∈ E, x < M.slot (m + 1) := fun m hm =>
    lt_of_lt_of_le hs1 (M.slot_mono (by have := hm.2.1; omega))
  have hxy : x < y := hgt m₀ hm₀
  have hyX : (X₀ : ℝ) ≤ y := by linarith
  have hpv := primeValueOf_ge_box (M := M) hU (capH_nonneg (X₀ : ℝ)) m₀
  have hyx : y - capH X₀ y / 2 ≤ x := hpv.trans hm₀.2.2
  have hHy := hreg x y hx hxy.le hyx
  set W := {m | placedAt M m ∧ x < M.slot (m + 1) ∧ M.slot (m + 1) ≤ y}
  have hsub : E ⊆ W := fun m hm =>
    ⟨hm.1, hgt m hm, hmax m (by rw [Set.Finite.mem_toFinset]; exact hm)⟩
  have hWfin : W.Finite := (finite_slot_succ_le y).subset fun m hm => hm.2.2
  have hle : (E.ncard : ℝ) ≤ (W.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hWfin
  have hw := hW x y hxy.le
  linarith

/-- **On the initial range, `H(x) ≤ H(X₀) + 2`**: for `X₀ ≤ x < X₀ + 2H(x)`, `H = H_std` and its
slope is at most `2/√X₀`, while `x - X₀ < 2H(x) ≤ √X₀`. -/
theorem capH_initial_le {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ}
    (hx1 : X₀ ≤ x) (hearly : x < X₀ + 2 * capH X₀ x) : capH X₀ x ≤ capH X₀ X₀ + 2 := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hx2 : x < 2 * X₀ := InitialRange.lt_two_mul_of_initial hX0 hX hx1 hearly
  have hXbig : 10 ^ 8 ≤ X₀ := by
    have h1 := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log (by linarith)] at h1
    linarith
  have hsX : 0 < Real.sqrt X₀ := Real.sqrt_pos.mpr (by linarith)
  set ε := 2 / Real.sqrt X₀ with hε
  set f : ℝ → ℝ := fun y => Real.exp (8 * Real.log (Real.log y) ^ 2) with hf
  set g : ℝ → ℝ := fun y => ε * y - f y with hg
  have hderiv : ∀ y, 1 < y → HasDerivAt g
      (ε - f y * (8 * (2 * Real.log (Real.log y) * ((1 / y) / Real.log y)))) y := by
    intro y hy
    have hy0 : y ≠ 0 := by positivity
    have hLy : Real.log y ≠ 0 := (Real.log_pos hy).ne'
    have h1 : HasDerivAt Real.log (1 / y) y := by
      simpa [one_div] using Real.hasDerivAt_log hy0
    have h2 : HasDerivAt (fun y => Real.log (Real.log y)) ((1 / y) / Real.log y) y :=
      h1.log hLy
    have h3 := ((h2.pow 2).const_mul 8).exp
    have h4 := (hasDerivAt_id y).const_mul ε
    have h5 := h4.sub h3
    convert h5 using 1
    · simp only [Nat.cast_ofNat, mul_one, hf, Pi.pow_apply]
      ring
  have hcont : ContinuousOn g (Icc X₀ x) := fun y hy =>
    (hderiv y (by linarith [hy.1])).continuousAt.continuousWithinAt
  have hmono : MonotoneOn g (Icc X₀ x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · intro y hy
      rw [interior_Icc] at hy
      exact (hderiv y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy1 : X₀ ≤ y := hy.1.le
      have hy0 : 0 < y := by linarith
      rw [(hderiv y (by linarith)).deriv]
      obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hy1
      have hle := (hstd.trans (InitialRange.capH_le_rpow hX0 hX hy1))
      have hr : y ^ (1 / 8 : ℝ) ≤ Real.sqrt y := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      obtain ⟨hL8, -, hl0⟩ := logs_of_ge hX0 hX hy1
      set L := Real.log y
      set l := Real.log L
      have hlL : l ≤ L / 8 := by
        have h := Real.log_le_sub_one_of_pos (show 0 < L / 16 by linarith)
        rw [Real.log_div (by linarith) (by norm_num)] at h
        have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
        linarith
      have hfy : f y ≤ Real.sqrt y := hle.trans hr
      have hf0 : 0 ≤ f y := (Real.exp_pos _).le
      have e : f y * (8 * (2 * l * ((1 / y) / L))) = (f y / y) * (16 * l / L) := by
        field_simp
        ring
      rw [e]
      have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      have hsyy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
      have hsXy : Real.sqrt X₀ ≤ Real.sqrt y := Real.sqrt_le_sqrt hy1
      have h1 : f y / y ≤ 1 / Real.sqrt X₀ := by
        rw [div_le_div_iff₀ hy0 hsX]
        calc f y * Real.sqrt X₀ ≤ Real.sqrt y * Real.sqrt y :=
              mul_le_mul hfy hsXy hsX.le hsy.le
          _ = 1 * y := by rw [hsyy, one_mul]
      have h2 : 16 * l / L ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have h3 : 0 ≤ 16 * l / L := by positivity
      have h4 : 0 ≤ f y / y := by positivity
      have : f y / y * (16 * l / L) ≤ 1 / Real.sqrt X₀ * 2 :=
        mul_le_mul h1 h2 h3 (by positivity)
      rw [hε]
      linarith [show 1 / Real.sqrt X₀ * 2 = 2 / Real.sqrt X₀ by ring]
  have hm := hmono (left_mem_Icc.mpr hx1) (right_mem_Icc.mpr hx1) hx1
  simp only [hg] at hm
  have hHx := JitterFloor.capH_eq_std hX0 hX hx1 hx2.le
  have hHX := JitterFloor.capH_eq_std hX0 hX le_rfl (by linarith)
  -- `2 H(x) ≤ √X₀`
  have hHle : 2 * capH X₀ x ≤ Real.sqrt X₀ := by
    have hr := InitialRange.capH_le_rpow hX0 hX hx1
    have hH1 := InitialRange.one_le_capH hX0 hX hx1
    by_contra hc
    push_neg at hc
    have hpow : (x ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h8 : (Real.sqrt X₀ / 2) ^ (8 : ℕ) < capH X₀ x ^ (8 : ℕ) :=
      pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    have h8' : capH X₀ x ^ (8 : ℕ) ≤ x := by
      have := pow_le_pow_left₀ (by linarith) hr 8
      rwa [hpow] at this
    have hsq : Real.sqrt X₀ ^ 2 = X₀ := Real.sq_sqrt hX0
    have e8 : (Real.sqrt X₀ / 2) ^ (8 : ℕ) = X₀ ^ 4 / 256 := by
      rw [div_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hsq]; norm_num
    rw [e8] at h8
    have : 2 * X₀ ≤ X₀ ^ 4 / 256 := by
      have hX3 : (512 : ℝ) ≤ X₀ ^ 3 := by
        have : (10 ^ 8 : ℝ) ^ 3 ≤ X₀ ^ 3 := pow_le_pow_left₀ (by norm_num) hXbig 3
        norm_num at this ⊢; linarith
      nlinarith
    linarith
  have hεH : ε * (x - X₀) ≤ 2 := by
    have : x - X₀ ≤ Real.sqrt X₀ := by linarith
    calc ε * (x - X₀) ≤ ε * Real.sqrt X₀ := by
          apply mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 := by rw [hε]; field_simp
  rw [hHx, hHX]
  simp only [hf] at hm
  nlinarith

end Slots

end Construction

end
