module

public import RequestProject.Beurling.Queue6.Increment
public import RequestProject.Beurling.Model.Bookkeep

/-!
# Lemma 3.9 two-sided, for physical windows (the identity (edge) of §5.3)

For the constructed slot model `M` (off `𝒩₌`, `ExcFacts`) and a physical window `[α, β)` with
`X₀ ≤ α ≤ β` (arbitrary real endpoints):

* `fi M α` : the first decision `k` whose slot starts at or above `α` (`α ≤ s_{k+1}`);
* `sigP M α β` : `σ([α, β))`, the primes placed at slots starting in `[α, β)`;
* `card_placed_eq` : the queue identity `#{k ∈ [i, j) placed} = Q_j - Q_i - exc(i, j)`
  (`Q_{k+1} = Q_k + A_{k+1} + P_k - 1`);
* `val_ge_of_jit`, `cjit_low` : a composite with a jittered prime has value `≥ 7X₀/4`, so
  `C_jit` vanishes below `7X₀/4`;
* `partial_cell` : the cut cell `[α, s_{fi α + 1})` carries `C_jit ≤ Q + 1` (its composites are
  arrivals of one slot, `A_k ≤ Q_k + 1`) and continuous mass `≤ 2`;
* `phys_bounds` : **Lemma 3.9 / (edge), two-sided**:
  `-Q_i - 4 ≤ σ([α, β)) - (C(β) - C(α)) + C_jit([α, β)) ≤ Q_j + 4`, `i = fi α`, `j = fi β`;
* `slot_fi_le` : the slot cell containing `β` ends below `β + 25 log(2β) + 2` (one cell carries
  continuous mass `≤ 2`, and `C' ≥ 0.08/log`).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono BModel QueueDet

namespace Queue6

variable {X₀ : ℕ}

/-! ### The first slot at or above a height -/

section First

variable (M : SlotModel X₀)

lemma exists_slot_ge (α : ℝ) : ∃ k, α ≤ M.slot (k + 1) := by
  obtain ⟨k, hk⟩ := slots_unbounded M α
  exact ⟨k, hk.le⟩

/-- The first decision `k` whose slot starts at or above `α`. -/
noncomputable def fi (α : ℝ) : ℕ := Nat.find (exists_slot_ge M α)

/-- `σ([α, β))`: the primes placed at slots starting in `[α, β)`. -/
noncomputable def sigP (α β : ℝ) : ℕ :=
  {k | placedAt M k ∧ α ≤ M.slot (k + 1) ∧ M.slot (k + 1) < β}.ncard

variable {M}

lemma fi_spec (α : ℝ) : α ≤ M.slot (fi M α + 1) := Nat.find_spec (exists_slot_ge M α)

lemma fi_le_iff {α : ℝ} {k : ℕ} : fi M α ≤ k ↔ α ≤ M.slot (k + 1) := by
  constructor
  · intro h
    exact (fi_spec α).trans (M.slot_mono (by omega))
  · intro h
    exact Nat.find_min' _ h

lemma slot_lt_of_lt_fi {α : ℝ} {k : ℕ} (hk : k < fi M α) : M.slot (k + 1) < α := by
  by_contra h
  push_neg at h
  have := fi_le_iff.mpr h
  omega

lemma fi_mono {α β : ℝ} (h : α ≤ β) : fi M α ≤ fi M β := fi_le_iff.mpr (h.trans (fi_spec β))

open Classical in
lemma sigP_eq (α β : ℝ) :
    sigP M α β = ((Finset.Ico (fi M α) (fi M β)).filter (placedAt M)).card := by
  unfold sigP
  rw [← Set.ncard_coe_finset]
  congr 1
  ext k
  simp only [mem_setOf_eq, Finset.coe_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hp, h1, h2⟩
    refine ⟨⟨fi_le_iff.mpr h1, ?_⟩, hp⟩
    by_contra h
    push_neg at h
    have := fi_le_iff.mp h
    linarith
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, fi_le_iff.mp h1, slot_lt_of_lt_fi h2⟩

open Classical in
/-- **The queue identity**: `#{k ∈ [i, j) : P_k = 1} = Q_j - Q_i - exc(i, j)`. -/
lemma card_placed_eq {i j : ℕ} (hij : i ≤ j) :
    (((Finset.Ico i j).filter (placedAt M)).card : ℤ) =
      M.queue j - M.queue i - exc M.arr i j := by
  induction j, hij using Nat.le_induction with
  | base => simp [exc]
  | succ j hij ih =>
    have hq : M.queue (j + 1) = M.queue j + M.arr (j + 1) + greedyPrime M.arr j - 1 := by
      simp only [SlotModel.queue, greedyQueue, greedyPrime]
    have hexc : exc M.arr i (j + 1) = exc M.arr i j + M.arr (j + 1) - 1 := by
      unfold exc
      rw [Finset.sum_Ioc_succ_top (by omega)]
      push_cast; ring
    rw [Nat.Ico_succ_right_eq_insert_Ico hij, Finset.filter_insert]
    have hnot : j ∉ (Finset.Ico i j).filter (placedAt M) := by simp
    by_cases hp : placedAt M j
    · rw [if_pos hp, Finset.card_insert_of_notMem hnot]
      have : greedyPrime M.arr j = 1 := hp
      rw [hq, hexc, this]
      push_cast
      linarith
    · rw [if_neg hp]
      have h0 : greedyPrime M.arr j = 0 := by
        rcases greedyPrime_mem M.arr_nonneg j with h | h
        · exact h
        · exact absurd h hp
      rw [hq, hexc, h0]
      linarith

/-- `A_l ≤ Q_l + 1` for `l ≥ 1`. -/
lemma arr_le_queue {l : ℕ} (hl : 1 ≤ l) : (M.arr l : ℝ) ≤ M.queue l + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h := greedyQueue_succ M.arr k
  have h0 := greedyQueue_nonneg M.arr k
  have : M.arr (k + 1) ≤ M.queue (k + 1) + 1 := by
    show M.arr (k + 1) ≤ greedyQueue M.arr (k + 1) + 1
    rw [h]
    have := le_max_right 0 (greedyQueue M.arr k + M.arr (k + 1) - 1)
    omega
  exact_mod_cast this

end First

/-! ### The low composites -/

section Low

variable {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **A composite with a jittered prime has value `≥ 7X₀/4`** (if all jittered primes are
`≥ 7X₀/8 ≥ 2`): it is `q^a` with `a ≥ 2`, or `q` times a nontrivial cofactor (`≥ 2`). -/
lemma val_ge_of_jit
    (hjit : ∀ k : {k // placedAt M k}, 7 / 8 * (X₀ : ℝ) ≤ realisedVal M (capH X₀) U (Sum.inr k))
    (hX2 : 2 ≤ 7 / 8 * (X₀ : ℝ)) {e : RealisedIdx M →₀ ℕ} (h2 : 2 ≤ e.sum fun _ n => n)
    (hr : ¬ RatOnly e) : 7 / 4 * (X₀ : ℝ) ≤ idxVal M (capH X₀) U e := by
  classical
  have hv : ∀ j, 2 ≤ realisedVal M (capH X₀) U j := by
    intro j
    rcases j with p | k
    · show (2 : ℝ) ≤ (p.1 : ℝ)
      exact_mod_cast p.2.1.two_le
    · exact hX2.trans (hjit k)
  have hv1 : ∀ j, 1 ≤ realisedVal M (capH X₀) U j := fun j => by linarith [hv j]
  unfold RatOnly at hr
  push_neg at hr
  obtain ⟨k, hk⟩ := hr
  set i : RealisedIdx M := Sum.inr k
  set q := realisedVal M (capH X₀) U i
  have hq : 7 / 8 * (X₀ : ℝ) ≤ q := hjit k
  have hq2 : 2 ≤ q := hX2.trans hq
  have hval := idxVal_erase (U := U) e i
  have h1 : 1 ≤ idxVal M (capH X₀) U (e.erase i) := by
    unfold idxVal Finsupp.prod
    have := Finset.prod_le_prod (s := (e.erase i).support) (f := fun _ => (1 : ℝ))
      (g := fun j => realisedVal M (capH X₀) U j ^ (e.erase i) j)
      (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (hv1 j))
    simpa using this
  rcases Nat.lt_or_ge (e i) 2 with hlt | hge
  · -- `e i = 1`: the cofactor is nontrivial
    have hei : e i = 1 := by omega
    have hne : e.erase i ≠ 0 := by
      intro h0
      have he : e = Finsupp.single i 1 := by
        rw [← Finsupp.erase_add_single i e, h0, zero_add, hei]
      rw [he, Finsupp.sum_single_index rfl] at h2
      omega
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
    have hpow := pow_le_finsupp_prod (realisedVal M (capH X₀) U) hv1 (e.erase i) j
    have hjv : realisedVal M (capH X₀) U j ≤ realisedVal M (capH X₀) U j ^ (e.erase i) j :=
      le_self_pow₀ (hv1 j) hj
    have hc2 : 2 ≤ idxVal M (capH X₀) U (e.erase i) := by
      unfold idxVal; linarith [hv j]
    rw [hval, hei, pow_one]
    nlinarith
  · have hqq : q ^ 2 ≤ q ^ (e i) := pow_le_pow_right₀ (by linarith) hge
    rw [hval]
    have hq0 : 0 ≤ q ^ (e i) := by positivity
    nlinarith

variable {θ : ℝ} (F : ExcFacts θ M U)
include F

/-- `C_jit` is additive over adjacent windows. -/
lemma cjit_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Cjit M U a c = Cjit M U a b + Cjit M U b c := by
  unfold Cjit
  have e : cjitSet M U a c = cjitSet M U a b ∪ cjitSet M U b c := by
    ext e
    simp only [cjitSet, mem_union, mem_setOf_eq, compositeSet_union hab hbc]
    tauto
  have hd : Disjoint (cjitSet M U a b) (cjitSet M U b c) := by
    rw [Set.disjoint_left]
    intro e he1 he2
    have h1 := he1.1.2.2
    have h2 := he2.1.2.1
    linarith
  rw [e, Set.ncard_union_eq hd (cjit_finite F a b) (cjit_finite F b c)]
  push_cast; ring

/-- `C_jit([a, b)) ≤ #comp([a, b))`. -/
lemma cjit_le_comp (a b : ℝ) :
    Cjit M U a b ≤ ((compositeSet M (capH X₀) U a b).ncard : ℝ) := by
  unfold Cjit
  exact_mod_cast Set.ncard_le_ncard (s := cjitSet M U a b) (fun e he => he.1) (comp_finite F a b)

/-- **`C_jit` vanishes below `7X₀/4`.** -/
lemma cjit_low
    (hjit : ∀ k : {k // placedAt M k}, 7 / 8 * (X₀ : ℝ) ≤ realisedVal M (capH X₀) U (Sum.inr k))
    {a b : ℝ} (hb : b ≤ 7 / 4 * (X₀ : ℝ)) : Cjit M U a b = 0 := by
  have hX2 : 2 ≤ 7 / 8 * (X₀ : ℝ) := by have := F.win.big; linarith
  unfold Cjit
  have : cjitSet M U a b = ∅ := by
    ext e
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨h2, -, hlt⟩, hr, -⟩
    have := val_ge_of_jit hjit hX2 h2 hr
    linarith
  rw [this, Set.ncard_empty]; simp

/-- `J` is non-decreasing on `[1, ∞)`. -/
lemma jumpL_mono {s s' : ℝ} (hs : 1 ≤ s) (hss : s ≤ s') :
    jumpL X₀ (DM M U) s ≤ jumpL X₀ (DM M U) s' := by
  unfold jumpL
  have h1 : ((⌈s⌉₊ : ℝ) - 1) ≤ (⌈s'⌉₊ : ℝ) - 1 := by
    have : (⌈s⌉₊ : ℝ) ≤ ⌈s'⌉₊ := by exact_mod_cast Nat.ceil_mono hss
    linarith
  have h2 := BModel.smoothCount_mono X₀ h1
  have h3 := countAlt_sub (A := absSet X₀ (DM M U)) (absSet_locFin F.win.fin) hs hss
  have h4 : (0 : ℝ) ≤ ((absSet X₀ (DM M U) ∩ Set.Ico s s').ncard : ℝ) := Nat.cast_nonneg _
  linarith

/-- **One slot cell carries continuous mass `≤ 2`**: `C(s_{l+1}) - C(s_l) ≤ 2`. -/
lemma cell_mass {l : ℕ} (hl : 1 ≤ l) :
    contD θ X₀ (DM M U) (M.slot (l + 1)) - contD θ X₀ (DM M U) (M.slot l) ≤ 2 := by
  have hlo := level_lower F (Nat.le_add_left 1 l)
  have hup := level_upper F hl
  have hlev : M.level (l + 1) = M.level l + 1 := by
    unfold SlotModel.level; push_cast; ring
  have hs := slot_gt F hl
  have hJ := jumpL_mono F (s := M.slot l) (s' := M.slot (l + 1))
    (by have := F.win.big; linarith) (M.slot_mono (by omega))
  linarith

/-- The arrivals of slot `l ≥ 1` are the composites of its cell. -/
lemma arr_eq {l : ℕ} (hl : 1 ≤ l) :
    (M.arr l : ℝ) = ((compositeSet M (capH X₀) U (M.slot l) (M.slot (l + 1))).ncard : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [F.win.linked k]
  unfold compositeArr
  push_cast; ring_nf

/-- **The cut cell** `[α, s_{fi α + 1})`: `C_jit ≤ Q_{fi α} + 1` and continuous mass `≤ 2`. -/
lemma partial_cell (hs1 : M.slot 1 ≤ X₀ + 2)
    (hjit : ∀ k : {k // placedAt M k}, 7 / 8 * (X₀ : ℝ) ≤ realisedVal M (capH X₀) U (Sum.inr k))
    {α : ℝ} (hα : (X₀ : ℝ) ≤ α) :
    Cjit M U α (M.slot (fi M α + 1)) ≤ M.queue (fi M α) + 1 ∧
      contD θ X₀ (DM M U) (M.slot (fi M α + 1)) - contD θ X₀ (DM M U) α ≤ 2 := by
  have hbig := F.win.big
  have hQ0 : (0 : ℝ) ≤ M.queue (fi M α) := by
    exact_mod_cast greedyQueue_nonneg M.arr (fi M α)
  rcases Nat.eq_zero_or_pos (fi M α) with h0 | hpos
  · rw [h0]
    have hcl : Cjit M U α (M.slot (0 + 1)) = 0 :=
      cjit_low F hjit (by simp only [zero_add]; linarith)
    rw [hcl]
    have hq0 : (0 : ℝ) ≤ M.queue 0 := by exact_mod_cast greedyQueue_nonneg M.arr 0
    refine ⟨by linarith, ?_⟩
    have h1 := contD_slot_one_le F
    have h2 := F.win.cmono _ _ le_rfl hα
    rw [contD_at] at h2
    simp only [zero_add]
    linarith
  · set i := fi M α
    have hlt : M.slot i < α := by
      obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have := slot_lt_of_lt_fi (M := M) (α := α) (k := k) (by omega)
      rw [hk]; exact this
    have hsX := slot_gt F hpos
    have hspec := fi_spec (M := M) α
    refine ⟨?_, ?_⟩
    · have h1 := cjit_mono F hlt.le (le_refl (M.slot (i + 1)))
      have h2 := cjit_le_comp F (M.slot i) (M.slot (i + 1))
      rw [← arr_eq F hpos] at h2
      have h3 := arr_le_queue (M := M) hpos
      linarith
    · have h1 := cell_mass F hpos
      have h2 := F.win.cmono _ _ hsX.le hlt.le
      linarith

/-- **Lemma 3.9 / eq. (edge), two-sided, for a physical window** `[α, β)`, `X₀ ≤ α ≤ β`:
`-Q_{fi α} - 4 ≤ σ([α, β)) - (C(β) - C(α)) + C_jit([α, β)) ≤ Q_{fi β} + 4`. -/
theorem phys_bounds (hs1 : M.slot 1 ≤ X₀ + 2)
    (hjit : ∀ k : {k // placedAt M k}, 7 / 8 * (X₀ : ℝ) ≤ realisedVal M (capH X₀) U (Sum.inr k))
    {α β : ℝ} (hα : (X₀ : ℝ) ≤ α) (hαβ : α ≤ β) :
    (sigP M α β : ℝ) ≤ M.queue (fi M β) + 4 - Cjit M U α β +
        (contD θ X₀ (DM M U) β - contD θ X₀ (DM M U) α) ∧
      -(M.queue (fi M α) : ℝ) - 4 - Cjit M U α β +
        (contD θ X₀ (DM M U) β - contD θ X₀ (DM M U) α) ≤ sigP M α β := by
  classical
  set i := fi M α with hi
  set j := fi M β with hj
  have hij : i ≤ j := fi_mono hαβ
  have hsi := fi_spec (M := M) α
  have hsj := fi_spec (M := M) β
  rw [← hi] at hsi
  rw [← hj] at hsj
  have hs1i := slot_gt F (Nat.le_add_left 1 i)
  have hss : M.slot (i + 1) ≤ M.slot (j + 1) := M.slot_mono (by omega)
  -- the queue identity
  have hσ : (sigP M α β : ℝ) = M.queue j - M.queue i - exc M.arr i j := by
    rw [sigP_eq, ← hi, ← hj]
    have := card_placed_eq (M := M) hij
    exact_mod_cast this
  have hexc : (exc M.arr i j : ℝ) =
      ((compositeSet M (capH X₀) U (M.slot (i + 1)) (M.slot (j + 1))).ncard : ℝ) -
        ((j : ℝ) - i) := by
    unfold exc; push_cast; rw [← sum_arr F hij]; push_cast; ring
  have hcomp := comp_eq F hs1i hss
  have hlo1 := level_lower F (Nat.le_add_left 1 i)
  have hup1 := level_upper F (Nat.le_add_left 1 i)
  have hlo2 := level_lower F (Nat.le_add_left 1 j)
  have hup2 := level_upper F (Nat.le_add_left 1 j)
  have hlev : M.level (j + 1) - M.level (i + 1) = (j : ℝ) - i := by
    unfold SlotModel.level; push_cast; ring
  -- the two cut cells
  obtain ⟨hPa, hCa⟩ := partial_cell F hs1 hjit hα
  obtain ⟨hPb, hCb⟩ := partial_cell F hs1 hjit (hα.trans hαβ)
  rw [← hi] at hPa hCa
  rw [← hj] at hPb hCb
  have hma := F.win.cmono _ _ hα hsi
  have hmb := F.win.cmono _ _ (hα.trans hαβ) hsj
  -- `C_jit` of the hull against `C_jit([α, β))`
  set Ch := Cjit M U (M.slot (i + 1)) (M.slot (j + 1))
  have hCh0 : 0 ≤ Ch := Nat.cast_nonneg _
  have hU1 : Cjit M U α β ≤ Cjit M U α (M.slot (i + 1)) + Ch := by
    rcases le_or_gt (M.slot (i + 1)) β with h | h
    · rw [cjit_add F hsi h]
      have := cjit_mono F (le_refl (M.slot (i + 1))) hsj
      linarith
    · have := cjit_mono F (le_refl α) h.le
      linarith
  have hL1 : Ch ≤ Cjit M U α β + Cjit M U β (M.slot (j + 1)) := by
    rw [← cjit_add F hαβ hsj]
    exact cjit_mono F hsi (le_refl _)
  rw [hσ, hexc, hcomp]
  constructor <;> linarith

/-- **The slot cell containing `β`** ends below `β + 25 log(2β) + 2`. -/
lemma slot_fi_le (hs1 : M.slot 1 ≤ X₀ + 2) {β : ℝ} (hβ : (X₀ : ℝ) ≤ β) :
    M.slot (fi M β + 1) ≤ β + 25 * Real.log (2 * β) + 2 := by
  have hbig := F.win.big
  have hβ1 : 1 ≤ β := by linarith
  have hl2 : 0 ≤ Real.log (2 * β) := Real.log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos (fi M β) with h0 | hpos
  · rw [h0]; linarith
  · set j := fi M β
    set x := M.slot (j + 1)
    have hlt : M.slot j < β := by
      obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have := slot_lt_of_lt_fi (M := M) (α := β) (k := k) (by omega)
      rw [hk]; exact this
    have hsX := slot_gt F hpos
    have hjx : M.slot j ≤ x := M.slot_mono (by omega)
    have hx0 : (X₀ : ℝ) < x := lt_of_lt_of_le hsX hjx
    have hxpos : 0 < x := by linarith
    have hm := cell_mass F hpos
    have hlow := F.lower _ _ hsX.le hjx
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hcell : x - M.slot j ≤ 25 * Real.log x := by
      have : 0.08 * (x - M.slot j) / Real.log x ≤ 2 := by linarith
      rw [div_le_iff₀ hlx] at this
      linarith
    -- `log x ≤ 2 √x`
    have hsq : Real.log x ≤ 2 * Real.sqrt x := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hxpos)
      have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hxpos.le]; ring
      linarith
    have hsx : 100 ≤ Real.sqrt x := by
      rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
    have hx2 : x ≤ 2 * β := by
      by_contra h
      push_neg at h
      nlinarith
    have hlog : Real.log x ≤ Real.log (2 * β) := Real.log_le_log hxpos hx2
    linarith

end Low

end Queue6

end
