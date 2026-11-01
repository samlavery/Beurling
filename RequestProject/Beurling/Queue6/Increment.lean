module

public import RequestProject.Beurling.Queue6.Excess
public import RequestProject.Beurling.Queue6.Cover

/-!
# Corollary 6.12 (per-prime increment bound) for the constructed model

For a window `[α, β)` and a relative slot `k` (the prime `q` decided at relative slot `k + 1`),
`Queue6.Xcount α β k n` is the number of non-absorbed composites in `[α, β)` with jittered latest
prime `q` and `q^n ‖ n` (`X⁽ⁿ⁾_q(I)` of §6.3), and `Queue6.X2count α β k` the number with `n ≥ 2`.

* `Queue6.cjit_eq_sum` : `C_jit([α, β)) = ∑_{k<N} (X⁽¹⁾_k + X⁽²⁾_k)` for all large `N`;
* `Queue6.latest_ge_absorbY` : a composite `m ≥ X₀` with jittered latest prime `q`, not in `𝒜`,
  has `q ≥ y(m)` (definition (5) of `𝒜`);
* `Queue6.xcount_le` : **Corollary 6.12**: on the cluster event `ClusterUpTo P X₀ Z M`, if every
  value `≥ α` has threshold `y(·) ≥ y`, `(β - α)/y < 1`, `(β - α)/y ≤ 2 (log(β/y))^{-6}` and
  `β/y ≤ Z`, then `X⁽ⁿ⁾_q([α, β)) ≤ 2M` for every jittered `q` and every `n` (the cofactors lie in
  a window of length `≤ |I|/q^n` covered by two grid windows, or below `X₀⁻`, where they are
  integers);
* `Queue6.mult_le` : `q^n ≤ β`, so `n ≤ log β / log q` (`a_max` of Theorem 6.6(ii)).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono BModel QueueDet

namespace Queue6

variable {X₀ : ℕ}

section Defs

variable (M : SlotModel X₀) (U : ℕ → ℝ)

open Classical in
/-- The exponent of the prime decided at relative slot `k + 1`. -/
noncomputable def mult (e : RealisedIdx M →₀ ℕ) (k : ℕ) : ℕ :=
  if hk : placedAt M k then e (Sum.inr ⟨k, hk⟩) else 0

/-- `X⁽ⁿ⁾_q([α, β))`: the non-absorbed composites in `[α, β)` with latest prime decided at
relative slot `k + 1`, exactly to the power `n`. -/
def xset (α β : ℝ) (k n : ℕ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | e ∈ cjitSet M U α β ∧ latk M e = k ∧ mult M e k = n}

/-- The composites of `xset` with exponent `≥ 2` (`X⁽²⁾_q` of §6.3). -/
def x2set (α β : ℝ) (k : ℕ) : Set (RealisedIdx M →₀ ℕ) :=
  {e | e ∈ cjitSet M U α β ∧ latk M e = k ∧ 2 ≤ mult M e k}

/-- `X⁽ⁿ⁾_q([α, β))`. -/
noncomputable def Xcount (α β : ℝ) (k n : ℕ) : ℝ := ((xset M U α β k n).ncard : ℝ)

/-- `X⁽²⁾_q([α, β))`. -/
noncomputable def X2count (α β : ℝ) (k : ℕ) : ℝ := ((x2set M U α β k).ncard : ℝ)

end Defs

section Latest

variable {M : SlotModel X₀}

lemma mult_pos {e : RealisedIdx M →₀ ℕ} (he : ¬ RatOnly e) : 1 ≤ mult M e (latk M e) := by
  obtain ⟨hk, hne⟩ := latk_mem he
  unfold mult; rw [dif_pos hk]; omega

end Latest

section Decomp

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ} (F : ExcFacts θ M U)
include F

lemma cjit_finite (α β : ℝ) : (cjitSet M U α β).Finite :=
  (comp_finite F α β).subset fun _ he => he.1

/-- **`C_jit = ∑_q (X⁽¹⁾_q + X⁽²⁾_q)`** (§6.3), for all large `N`. -/
theorem cjit_eq_sum (α β : ℝ) : ∃ N₀, ∀ N ≥ N₀,
    Cjit M U α β = ∑ k ∈ Finset.range N, (Xcount M U α β k 1 + X2count M U α β k) := by
  classical
  set C := cjit_finite F α β |>.toFinset
  refine ⟨C.sup (latk M) + 1, fun N hN => ?_⟩
  have hmem : ∀ e ∈ C, latk M e ∈ Finset.range N := fun e he => by
    have := Finset.le_sup (f := latk M) he
    exact Finset.mem_range.mpr (by omega)
  unfold Cjit
  rw [Set.ncard_eq_toFinset_card _ (cjit_finite F α β),
    Finset.card_eq_sum_card_fiberwise (f := latk M) (t := Finset.range N)
    (fun e he => Finset.mem_coe.mpr (hmem e he))]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold Xcount X2count
  have hf1 : (xset M U α β k 1).Finite := (cjit_finite F α β).subset fun e he => he.1
  have hf2 : (x2set M U α β k).Finite := (cjit_finite F α β).subset fun e he => he.1
  rw [← Set.ncard_coe_finset, ← Nat.cast_add, ← Set.ncard_union_eq _ hf1 hf2]
  · congr 2
    ext e
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, mem_setOf_eq, xset, x2set, mem_union,
      C]
    constructor
    · rintro ⟨he, hk⟩
      have := mult_pos (M := M) he.2.1
      rw [hk] at this
      rcases Nat.lt_or_ge (mult M e k) 2 with h | h
      · left; exact ⟨he, hk, by omega⟩
      · right; exact ⟨he, hk, h⟩
    · rintro (⟨he, hk, -⟩ | ⟨he, hk, -⟩) <;> exact ⟨he, hk⟩
  · rw [Set.disjoint_left]
    rintro e ⟨-, -, h1⟩ ⟨-, -, h2⟩
    omega

end Decomp

/-! ### The threshold: non-absorbed composites have `q ≥ y` -/

section Threshold

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **The threshold** (definition (5)): a composite of value `m ≥ X₀` (so `log m ≥ L*`) whose
latest prime is jittered and which is not in `𝒜` has its latest prime `≥ y(m)`. -/
theorem latest_ge_absorbY (hX : 10 ^ 7 ≤ Real.log X₀)
    {e : RealisedIdx M →₀ ℕ} (hr : ¬ RatOnly e) (hX0 : (X₀ : ℝ) ≤ idxVal M (capH X₀) U e)
    (hA : ¬ OwnAbs M U e) :
    absorbY X₀ (idxVal M (capH X₀) U e) ≤ primeValueOf M (capH X₀) U (latk M e) := by
  by_contra hlt
  push_neg at hlt
  apply hA
  have hX1 : (0 : ℝ) < X₀ := by
    by_contra h; push_neg at h
    have : Real.log X₀ ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) (by linarith)
    linarith
  exact ⟨hX.trans (Real.log_le_log hX1 hX0), hr, hlt⟩

end Threshold

/-! ### Cofactors -/

section Cofactor

variable {M : SlotModel X₀} {U : ℕ → ℝ}

/-- The value of `e` is that of its cofactor times `q^n`. -/
lemma idxVal_erase (e : RealisedIdx M →₀ ℕ) (i : RealisedIdx M) :
    idxVal M (capH X₀) U e =
      idxVal M (capH X₀) U (e.erase i) * realisedVal M (capH X₀) U i ^ e i := by
  classical
  conv_lhs => rw [← Finsupp.erase_add_single i e]
  unfold idxVal
  rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)]
  congr 1
  simp [Finsupp.prod_single_index]

/-- Elements of value `< c` with `c ≤` every jittered prime have only rational primes. -/
lemma ratOnly_of_lt (hok : RealisedOK M (capH X₀) U) {c : ℝ}
    (hc : ∀ k : {k // placedAt M k}, c ≤ realisedVal M (capH X₀) U (Sum.inr k))
    {f : RealisedIdx M →₀ ℕ} (hf : idxVal M (capH X₀) U f < c) : RatOnly f := by
  intro k
  by_contra hk
  have h1 := pow_le_finsupp_prod (realisedVal M (capH X₀) U) (fun i => (hok.one_lt i).le) f
    (Sum.inr k)
  have h2 : realisedVal M (capH X₀) U (Sum.inr k) ≤
      realisedVal M (capH X₀) U (Sum.inr k) ^ f (Sum.inr k) :=
    le_self_pow₀ (hok.one_lt _).le hk
  have h3 := hc k
  unfold idxVal at hf
  linarith

/-- A window of length `< 1` below every jittered prime holds at most one element. -/
lemma low_le_one (hok : RealisedOK M (capH X₀) U) {c w δ : ℝ}
    (hc : ∀ k : {k // placedAt M k}, c ≤ realisedVal M (capH X₀) U (Sum.inr k))
    (hδ : δ < 1) (hwc : w + δ ≤ c) :
    {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < w + δ}.ncard
      ≤ 1 := by
  rw [Set.ncard_le_one (hs := (finite_idxVal_le hok (w + δ)).subset fun f hf => hf.2.le)]
  rintro f ⟨hf1, hf2⟩ g ⟨hg1, hg2⟩
  have hrf := ratOnly_of_lt hok hc (lt_of_lt_of_le hf2 hwc)
  have hrg := ratOnly_of_lt hok hc (lt_of_lt_of_le hg2 hwc)
  rw [idxVal_ratOnly _ _ hrf] at hf1 hf2
  rw [idxVal_ratOnly _ _ hrg] at hg1 hg2
  apply num_inj hrf hrg
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (num f : ℝ) + 1 ≤ num g := by exact_mod_cast h
    linarith
  · have : (num g : ℝ) + 1 ≤ num f := by exact_mod_cast h
    linarith

/-- The elements of the realised index set in a window are the elements of `P(ω)` there. -/
lemma ncard_win_eq (hok : RealisedOK M (capH X₀) U) (a b : ℝ) :
    {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < b}.ncard =
      {e : ℕ →₀ ℕ | a ≤ (realisedSystem M (capH X₀) U).val e ∧
        (realisedSystem M (capH X₀) U).val e < b}.ncard := by
  have e1 : {f : RealisedIdx M →₀ ℕ | a ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < b} =
      (Finsupp.equivMapDomain hok.equiv) '' {e : ℕ →₀ ℕ |
        a ≤ (realisedSystem M (capH X₀) U).val e ∧ (realisedSystem M (capH X₀) U).val e < b} := by
    ext f
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hf
      refine ⟨Finsupp.equivMapDomain hok.equiv.symm f, ?_,
        by simp [← Finsupp.equivMapDomain_trans]⟩
      rw [val_eq_idxVal hok]; simpa [← Finsupp.equivMapDomain_trans] using hf
    · rintro ⟨e, he, rfl⟩
      rwa [← val_eq_idxVal hok]
  rw [e1, Set.ncard_image_of_injective _ (equivMapDomain_inj _)]

end Cofactor

/-! ### Corollary 6.12 -/

section Increment

variable {θ : ℝ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- Every jittered prime is at least `7X₀/8` (box-centred placement at slot starts `≥ X₀`). -/
lemma jit_ge (hX : 10 ^ 8 ≤ Real.log X₀) (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1)
    (hslot : ∀ l, 1 ≤ l → (X₀ : ℝ) ≤ M.slot l) (k : {k // placedAt M k}) :
    7 / 8 * (X₀ : ℝ) ≤ realisedVal M (capH X₀) U (Sum.inr k) := by
  show 7 / 8 * (X₀ : ℝ) ≤ primeValueOf M (capH X₀) U k.1
  have hs := hslot (k.1 + 1) (by omega)
  have hH : 0 ≤ capH X₀ (M.slot (k.1 + 1)) := le_trans (Real.exp_pos _).le (le_max_left _ _)
  have h1 := (landing_mem_box (s := M.slot (k.1 + 1)) hH (hU (k.1 + 1))).1
  have h2 := boxFloor_ge hX hs
  unfold boxFloor at h2
  unfold primeValueOf
  nlinarith

/-- **Corollary 6.12 (per-prime increment bound)** for the constructed model. -/
theorem xcount_le (hok : RealisedOK M (capH X₀) U) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hU : ∀ j, U j ∈ Icc (0 : ℝ) 1) (hslot : ∀ l, 1 ≤ l → (X₀ : ℝ) ≤ M.slot l)
    {α β y Z Mc : ℝ} (hy1 : 1 ≤ y)
    (hy : ∀ e ∈ cjitSet M U α β, y ≤ primeValueOf M (capH X₀) U (latk M e))
    (hlen1 : (β - α) / y < 1) (hlen : (β - α) / y ≤ 2 / Real.log (β / y) ^ 6)
    (hZ : β / y ≤ Z) (hcl : ClusterUpTo (realisedSystem M (capH X₀) U) X₀ Z Mc)
    (hMc : 1 / 2 ≤ Mc) (k n : ℕ) : Xcount M U α β k n ≤ 2 * Mc := by
  classical
  have hX1 : (2 : ℝ) ^ (16 : ℕ) ≤ X₀ := two_pow_le_of_logX (Nat.cast_nonneg _) hX
  unfold Xcount
  rcases (xset M U α β k n).eq_empty_or_nonempty with h0 | ⟨e0, he0⟩
  · rw [h0, Set.ncard_empty]; push_cast; linarith
  -- the prime `q`
  have hr0 := he0.1.2.1
  obtain ⟨hk, -⟩ := latk_mem (M := M) hr0
  rw [he0.2.1] at hk
  set i : RealisedIdx M := Sum.inr ⟨k, hk⟩
  set q := realisedVal M (capH X₀) U i
  have hq : y ≤ q := by
    have := hy e0 he0.1; rw [he0.2.1] at this; exact this
  have hq1 : 1 < q := hok.one_lt i
  have hqn : 1 ≤ q ^ n := one_le_pow₀ hq1.le
  have hqn' : y ≤ q ^ n ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · right; exact h
    · left; exact hq.trans (le_self_pow₀ hq1.le (by omega))
  -- the cofactor window
  set w := α / q ^ n
  set δ := (β - α) / q ^ n
  have hqn0 : 0 < q ^ n := by positivity
  have hsub : ∀ e ∈ xset M U α β k n, e.erase i ∈
      {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < w + δ} := by
    intro e he
    have hm : e i = n := by
      have := he.2.2; unfold mult at this; rw [dif_pos hk] at this; exact this
    have hv := idxVal_erase (U := U) e i
    rw [hm] at hv
    have h1 := he.1.1.2.1
    have h2 := he.1.1.2.2
    rw [hv] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hqn0]; exact h1
    · have : w + δ = β / q ^ n := by simp only [w, δ]; field_simp; ring
      rw [this, lt_div_iff₀ hqn0]; exact h2
  have hinj : Set.InjOn (fun e => e.erase i) (xset M U α β k n) := by
    intro e he e' he' heq
    have hm : e i = n := by
      have := he.2.2; unfold mult at this; rw [dif_pos hk] at this; exact this
    have hm' : e' i = n := by
      have := he'.2.2; unfold mult at this; rw [dif_pos hk] at this; exact this
    simp only at heq
    rw [← Finsupp.erase_add_single i e, ← Finsupp.erase_add_single i e', heq, hm, hm']
  have hfinW := (finite_idxVal_le hok (w + δ)).subset
    (fun f (hf : f ∈ {f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧
      idxVal M (capH X₀) U f < w + δ}) => hf.2.le)
  have hle := Set.ncard_le_ncard_of_injOn _ hsub hinj hfinW
  -- the cofactor window is short
  have hδ1 : δ < 1 := by
    have hβα : 0 ≤ β - α := by
      rcases le_or_gt α β with h | h
      · linarith
      · exfalso
        have := he0.1.1.2
        linarith [this.1, this.2]
    rcases hqn' with h | h
    · calc δ ≤ (β - α) / y := div_le_div_of_nonneg_left hβα (by linarith) h
        _ < 1 := hlen1
    · exfalso
      -- `n ≥ 1` since `e0` has the prime `q`
      have := mult_pos (M := M) hr0
      rw [he0.2.1, he0.2.2, h] at this; omega
  have hjit := jit_ge hX hU hslot
  have hle' : ((xset M U α β k n).ncard : ℝ) ≤ (({f : RealisedIdx M →₀ ℕ | w ≤
      idxVal M (capH X₀) U f ∧ idxVal M (capH X₀) U f < w + δ}.ncard : ℕ) : ℝ) := by
    exact_mod_cast hle
  refine le_trans hle' ?_
  by_cases hlow : w + δ ≤ 7 / 8 * (X₀ : ℝ)
  · have := low_le_one hok hjit hδ1 hlow
    have : (({f : RealisedIdx M →₀ ℕ | w ≤ idxVal M (capH X₀) U f ∧
        idxVal M (capH X₀) U f < w + δ}.ncard : ℕ) : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  · push_neg at hlow
    rw [ncard_win_eq hok]
    have hn1 : 1 ≤ n := by
      have := mult_pos (M := M) hr0
      rw [he0.2.1, he0.2.2] at this; exact this
    have hyq : y ≤ q ^ n := hq.trans (le_self_pow₀ hq1.le (by omega))
    have hβ0 : 0 ≤ β := by
      have hv0 : (0 : ℝ) < idxVal M (capH X₀) U e0 := by
        unfold idxVal Finsupp.prod
        exact Finset.prod_pos fun j _ => pow_pos (by linarith [hok.one_lt j]) _
      linarith [he0.1.1.2.2]
    have hwβ : w + δ ≤ β / y := by
      have : w + δ = β / q ^ n := by simp only [w, δ]; field_simp; ring
      rw [this]; exact div_le_div_of_nonneg_left hβ0 (by linarith) hyq
    have hw : 3 * (X₀ : ℝ) / 4 ≤ w := by linarith
    have hw1 : 1 < w := by linarith
    have hβα : 0 ≤ β - α := by
      have := he0.1.1.2; linarith [this.1, this.2]
    have hδy : δ ≤ (β - α) / y := div_le_div_of_nonneg_left hβα (by linarith) hyq
    have hδ0 : 0 ≤ δ := div_nonneg hβα hqn0.le
    have hlog : Real.log w ≤ Real.log (β / y) := Real.log_le_log (by linarith) (by linarith)
    have hlw : 0 < Real.log w := Real.log_pos hw1
    have h6 : 2 / Real.log (β / y) ^ 6 ≤ 2 / Real.log w ^ 6 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlw.le hlog 6)
    exact two_window_cover _ (by linarith) (by linarith) hcl hw
      (by linarith) (hδy.trans (hlen.trans h6))

end Increment

/-! ### The `q^a` part, `a ≥ 2` -/

section Square

variable {M : SlotModel X₀} {U : ℕ → ℝ}

/-- `q^n ≤ val(e) < β` for `e ∈ X⁽ⁿ⁾_q([α, β))`. -/
lemma pow_lt_of_xset (hok : RealisedOK M (capH X₀) U) {α β : ℝ} {k n : ℕ}
    {e : RealisedIdx M →₀ ℕ} (he : e ∈ xset M U α β k n) (hk : placedAt M k) :
    primeValueOf M (capH X₀) U k ^ n < β := by
  set i : RealisedIdx M := Sum.inr ⟨k, hk⟩
  have hm : e i = n := by
    have := he.2.2; unfold mult at this; rw [dif_pos hk] at this; exact this
  have hv := idxVal_erase (U := U) e i
  rw [hm] at hv
  have h1 : 1 ≤ idxVal M (capH X₀) U (e.erase i) := by
    unfold idxVal Finsupp.prod
    have := Finset.prod_le_prod₀ (s := (e.erase i).support) (f := fun _ => (1 : ℝ))
      (g := fun j => realisedVal M (capH X₀) U j ^ (e.erase i) j)
      (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (hok.one_lt j).le)
    simpa using this
  have h2 := he.1.1.2.2
  have hq : 0 < realisedVal M (capH X₀) U i ^ n := pow_pos (by linarith [hok.one_lt i]) _
  have : realisedVal M (capH X₀) U i ^ n ≤ idxVal M (capH X₀) U e := by
    rw [hv]; nlinarith
  exact lt_of_le_of_lt this h2

/-- **The `a ≥ 2` part of one prime** (proof of Theorem 6.6(ii)): if every exponent of `q` in
`[α, β)` is at most `A` (`a_max`) and each `X⁽ⁿ⁾_q ≤ 2M`, then `X⁽²⁾_q ≤ 2 A M`. -/
lemma x2count_le (hok : RealisedOK M (capH X₀) U) {α β Mc : ℝ} (hMc : 0 ≤ Mc) {k A : ℕ}
    (hA : ∀ e ∈ x2set M U α β k, mult M e k ≤ A) (hX : ∀ n, Xcount M U α β k n ≤ 2 * Mc) :
    X2count M U α β k ≤ 2 * A * Mc := by
  have hfin : ∀ n, (xset M U α β k n).Finite := fun n =>
    (finite_idxVal_le hok β).subset fun e he => he.1.1.2.2.le
  have h := count_le_of_cover (S := x2set M U α β k) (A - 1) (fun i => xset M U α β k (i + 2))
    (fun i => hfin (i + 2)) (fun i _ => hX (i + 2)) (fun e he =>
      ⟨mult M e k - 2, by have := hA e he; have := he.2.2; omega,
        ⟨he.1, he.2.1, by have := he.2.2; omega⟩⟩)
  unfold X2count
  refine h.trans ?_
  rcases Nat.eq_zero_or_pos A with h0 | hpos
  · rw [h0]; simp
  · rw [Nat.cast_sub hpos]; push_cast; nlinarith

end Square

end Queue6

end
