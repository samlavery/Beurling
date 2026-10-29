module

public import RequestProject.Beurling.Queue6.Thresh6
public import RequestProject.Beurling.Queue6.WinCount

/-!
# Lemma 5.23, case (i): the field `countI` of `BeurlingSystem.ThreshHyp` for `P(ω)`

For `m ∈ Mset_j` (decision times `t = tJ`) write `m = p m'`, `p = p_j`; then
`val m' ∈ J_p = [x(1-δ), x)/(t(p) p)` (`Mset_val`), and `m ↦ m'` is injective. Here:

* `ratCount_le`, `primeCount_gen` : the primes of `P(ω)` in `[c, d]` number at most
  `1.0001 (d - c + H(2 max(d, X₀)) + 1) + 1 + (d - c + 1)` (jittered ones by slots, rational ones
  as integers);
* `prime_lower` : every prime `q` of `m'` has `q ≥ 0.99 p` (the paper's "every prime `q` of `m'`
  has `q ≥ 0.99p`");
* `countI_large` : **case `p > 1.01 x^{1/4}`**: `m'` is a single prime of `J_p`, counted by
  `primeCount_gen`: `#Mset_j ≤ 4 δx/p²`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- `0.99 p ≤ t(p) ≤ 1.01 p` and `|t(p) - p| ≤ H(t(p))/2 ≤ t(p)/(2·10⁷)` or `t(p) = p`. -/
lemma tJ_near (ω : JitterΩ) (j : ℕ) :
    0.99 * (PR θ X₀ ω).p j ≤ tJ θ X₀ ω j ∧ tJ θ X₀ ω j ≤ 1.01 * (PR θ X₀ ω).p j := by
  have hp2 := two_le_p hc ω j
  rcases tJ_cases hc ω j with ⟨h1, -⟩ | ⟨k, h1, h2⟩
  · rw [h1]; constructor <;> linarith
  · rw [h1, h2]
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    have hs := slotF_ge hc k ω
    have hH : HF θ X₀ k ω ≤ slotF θ X₀ k ω / 10 ^ 7 := capH_le_div hc.hX hs
    have h0 : 0 ≤ slotF θ X₀ k ω := by linarith [X₀_ge_two_pow hc.hX]
    constructor <;> nlinarith

/-- **Every prime `q` of an element of `Mset_j` other than `p_j` has `q ≥ 0.99 p_j`.** -/
lemma prime_lower (ω : JitterΩ) {x δ : ℝ} {j : ℕ} {m : ℕ →₀ ℕ}
    (hm : m ∈ (PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j) {i : ℕ} (hi : i ∈ m.support) :
    0.99 * (PR θ X₀ ω).p j ≤ (PR θ X₀ ω).p i := by
  classical
  have hti : tJ θ X₀ ω j ≤ tJ θ X₀ ω i := (Finset.mem_filter.mp hm).2.2.2.1 i hi
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hbig := X₀_ge_two_pow hc.hX
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    unfold Xm; linarith
  rcases tJ_cases hc ω j with ⟨hj1, p, hp⟩ | ⟨k, hj1, hj2⟩
  · -- `p_j` rational, `t = p_j < X₀`
    have hpX : (PR θ X₀ ω).p j < X₀ := by rw [hp]; exact_mod_cast p.2.2
    rcases tJ_cases hc ω i with ⟨hi1, -⟩ | ⟨k', hi1, hi2⟩
    · rw [hj1, hi1] at hti; linarith [two_le_p hc ω j]
    · rw [hi2]
      have := valF_ge_Xm hc k' ω
      linarith
  · -- `p_j` jittered at the slot `s ≥ X₀`
    have hs := slotF_ge hc k ω
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    have hH : HF θ X₀ k ω ≤ slotF θ X₀ k ω / 10 ^ 7 := capH_le_div hc.hX hs
    rw [hj2]
    rw [hj1] at hti
    rcases tJ_cases hc ω i with ⟨hi1, -⟩ | ⟨k', hi1, hi2⟩
    · rw [hi1] at hti; nlinarith
    · rw [hi1] at hti
      rw [hi2]
      obtain ⟨c1, -⟩ := valF_box hc ω k'
      have hmono := phiMinus_mono hc hti
      rw [Hc_slot hc ω k, Hc_slot hc ω k'] at hmono
      nlinarith

omit hc in
/-- **The value of `m'`**: `val m = p_j · val(m.erase j)` for `m ∈ Mset_j`. -/
lemma Mset_val (ω : JitterΩ) {x δ : ℝ} {j : ℕ} {m : ℕ →₀ ℕ}
    (hm : m ∈ (PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j) :
    (PR θ X₀ ω).val m = (PR θ X₀ ω).p j * (PR θ X₀ ω).val (m.erase j) ∧
      m = m.erase j + Finsupp.single j 1 := by
  classical
  obtain ⟨-, hs, hj, -⟩ := Finset.mem_filter.mp hm
  have hmj : m j = 1 := le_antisymm (hs j) (Nat.one_le_iff_ne_zero.mpr
    (Finsupp.mem_support_iff.mp hj))
  have hs' : BeurlingSystem.Sqf (m.erase j) := fun i => by
    rw [Finsupp.erase_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hs i
  refine ⟨?_, ?_⟩
  · rw [(PR θ X₀ ω).val_eq_prod_support hs, (PR θ X₀ ω).val_eq_prod_support hs',
      Finsupp.support_erase, ← Finset.mul_prod_erase _ _ hj]
  · conv_lhs => rw [← Finsupp.erase_add_single j m, hmj]

omit hc in
/-- `#(ℕ ∩ [c, d]) ≤ d - c + 1`. -/
lemma nat_count_le {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c ≤ d) :
    ((Finset.Icc ⌈c⌉₊ ⌊d⌋₊).card : ℝ) ≤ d - c + 1 := by
  rw [Nat.card_Icc]
  have h1 : (⌊d⌋₊ : ℝ) ≤ d := Nat.floor_le (hc0.trans hcd)
  have h2 : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  rcases Nat.lt_or_ge (⌊d⌋₊ + 1) ⌈c⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
  · rw [Nat.cast_sub h]; push_cast; linarith

variable (hev : Even X₀)
include hev

set_option maxHeartbeats 1600000 in
/-- **The primes of `P(ω)` in `[c, d]`** (`0 ≤ c ≤ d`), on `NiceEv`:
at most `1.0001 (d - c + H(2 max(d, X₀)) + 1) + 1 + (d - c + 1)`. -/
theorem primeCount_gen {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {S : Set ℝ} {c d : ℝ}
    (hc0 : 0 ≤ c) (hcd : c ≤ d) (hS : S ⊆ Icc c d) :
    ({i | (PR θ X₀ ω).p i ∈ S}.ncard : ℝ) ≤
      1.0001 * (d - c + capH X₀ (2 * max d X₀) + 1) + 1 + (d - c + 1) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hok := realisedOK_Mcl hc ω
  have hpj : ∀ j, (PR θ X₀ ω).p j = realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (hok.equiv j) :=
    fun j => realisedSystem_p hok j
  set D := max d (X₀ : ℝ)
  have hDX : (X₀ : ℝ) ≤ D := le_max_right _ _
  have hdD : d ≤ D := le_max_left _ _
  set Hb := capH X₀ (2 * D)
  have hHb0 : 0 ≤ Hb := capH_nonneg _ _
  have hsg : ∀ k, ω ∈ stageGood θ X₀ k := fun k => by
    have := hN.2.1; simp only [SG, mem_iInter] at this; exact this k
  set K := {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}
  have hKv : ∀ k ∈ K, slotF θ X₀ k ω ≤ 1.0000001 * D ∧ HF θ X₀ k ω ≤ Hb := fun k hk =>
    slot_of_val hc ω hDX ((hS hk.2).2.trans hdD)
  have hfinK : K.Finite := (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * D)).subset fun k hk => by
    have := (hKv k hk).1
    show slotF θ X₀ k ω ≤ 2 * D
    linarith
  have hK : (K.ncard : ℝ) ≤ 1.0001 * (d - c + Hb + 1) + 1 := by
    rw [Set.ncard_eq_toFinset_card _ hfinK]
    refine slot_window_card hc hev (ω := ω) hfinK.toFinset (a₀ := c - Hb / 2 - 1)
      (b := d + Hb / 2) (ℓ := d - c + Hb + 1) (fun k hk => ?_) (by linarith) (by linarith)
    have hk' := hfinK.mem_toFinset.mp hk
    obtain ⟨-, hHk⟩ := hKv k hk'
    obtain ⟨hp, hv⟩ := hk'
    obtain ⟨hv1, hv2⟩ := hS hv
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    exact ⟨⟨hp, hsg k⟩, by linarith, by linarith⟩
  set A := {j | (PR θ X₀ ω).p j ∈ S ∧ ∃ k, hok.equiv j = Sum.inr k}
  set R := {j | (PR θ X₀ ω).p j ∈ S ∧ ∃ p, hok.equiv j = Sum.inl p}
  have hsub : {j | (PR θ X₀ ω).p j ∈ S} ⊆ A ∪ R := by
    intro j hj
    rcases he : hok.equiv j with p | k
    · exact Or.inr ⟨hj, p, he⟩
    · exact Or.inl ⟨hj, k, he⟩
  have hfinS : {j | (PR θ X₀ ω).p j ∈ S}.Finite :=
    ((PR θ X₀ ω).finite_p_le d).subset fun j hj => (hS hj).2
  have hfinA : A.Finite := hfinS.subset fun j hj => hj.1
  have hfinR : R.Finite := hfinS.subset fun j hj => hj.1
  let f : ℕ → ℕ := fun j => match hok.equiv j with
    | Sum.inl _ => 0
    | Sum.inr k => k.1
  have hA : A.ncard ≤ K.ncard := by
    refine Set.ncard_le_ncard_of_injOn f (fun j hj => ?_) (fun j hj j' hj' hff => ?_) hfinK
    · obtain ⟨hjS, k, hk⟩ := hj
      simp only [f, hk]
      rw [hpj, hk] at hjS
      exact ⟨k.2, hjS⟩
    · obtain ⟨-, k, hk⟩ := hj
      obtain ⟨-, k', hk'⟩ := hj'
      simp only [f, hk, hk'] at hff
      apply hok.equiv.injective
      rw [hk, hk']
      congr 1; exact Subtype.ext hff
  have hR : (R.ncard : ℝ) ≤ d - c + 1 := by
    let g : ℕ → ℕ := fun j => match hok.equiv j with
      | Sum.inl p => p.1
      | Sum.inr _ => 0
    have h := Set.ncard_le_ncard_of_injOn g (s := R)
      (t := (Finset.Icc ⌈c⌉₊ ⌊d⌋₊ : Set ℕ))
      (fun j hj => by
        obtain ⟨hjS, p, hp⟩ := hj
        rw [hpj, hp] at hjS
        obtain ⟨h1, h2⟩ := hS hjS
        simp only [g, hp, Finset.coe_Icc, Set.mem_Icc]
        have h1' : c ≤ (p.1 : ℝ) := h1
        have h2' : (p.1 : ℝ) ≤ d := h2
        exact ⟨Nat.ceil_le.mpr h1', Nat.le_floor h2'⟩)
      (fun j hj j' hj' hgg => by
        obtain ⟨-, p, hp⟩ := hj
        obtain ⟨-, p', hp'⟩ := hj'
        simp only [g, hp, hp'] at hgg
        apply hok.equiv.injective
        rw [hp, hp']
        congr 1; exact Subtype.ext hgg)
      (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have := nat_count_le hc0 hcd
    have h' : (R.ncard : ℝ) ≤ ((Finset.Icc ⌈c⌉₊ ⌊d⌋₊).card : ℝ) := by exact_mod_cast h
    linarith
  have h1 := Set.ncard_le_ncard hsub (hfinA.union hfinR)
  have h2 := Set.ncard_union_le A R
  have h3 : (({j | (PR θ X₀ ω).p j ∈ S}.ncard : ℕ) : ℝ) ≤ (A.ncard : ℝ) + R.ncard := by
    exact_mod_cast h1.trans h2
  have h4 : (A.ncard : ℝ) ≤ K.ncard := by exact_mod_cast hA
  linarith

set_option maxHeartbeats 3200000 in
/-- **The field `countI`, case `p > 1.01 x^{1/4}`** (04e-lp.tex, Lemma 5.23 (i), second
bullet): `m'` is a single prime of `J_p`, so `#Mset_j ≤ 4 δx/p_j²`. The hypotheses are those of
`ThreshHyp` used here: `δ ≤ 1/4`, `2X₀ ≤ x`, `p_j ≤ √(δx/(2H(x)))`. -/
theorem countI_large {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {x δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (hxX : 2 * (X₀ : ℝ) ≤ x) {j : ℕ}
    (hpj : (PR θ X₀ ω).p j ≤ √(δ * x / (2 * Hc X₀ x)))
    (hpl : 1.01 * x ^ (1 / 4 : ℝ) < (PR θ X₀ ω).p j) :
    (((PR θ X₀ ω).Mset (tJ θ X₀ ω) x δ j).card : ℝ) ≤ 4 * δ * x / (PR θ X₀ ω).p j ^ 2 := by
  classical
  set P := PR θ X₀ ω
  set p := P.p j with hpe
  set τ := tJ θ X₀ ω j with hτe
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hbig := X₀_ge_two_pow hc.hX
  have hx0 : 0 < x := by linarith
  have hx2 := hxX
  have hxX : (X₀ : ℝ) ≤ x := by linarith
  have hp2 : 2 ≤ p := two_le_p hc ω j
  obtain ⟨hτ1, hτ2⟩ := tJ_near hc ω j
  have hτ0 : 0 < τ := by linarith
  have hHx : 200 ≤ Hc X₀ x := by
    have := Hc_ge hc x; rw [max_eq_left hxX] at this
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith); linarith
  -- `p² ≤ δx/(2H)`, so `δx/p² ≥ 2H(x)`
  have hpp : p ^ 2 ≤ δ * x / (2 * Hc X₀ x) := by
    have h0 : 0 ≤ δ * x / (2 * Hc X₀ x) := by positivity
    have := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (δ * x / (2 * Hc X₀ x))]
  have hp20 : 0 < p ^ 2 := by positivity
  have hJ2H : 2 * Hc X₀ x ≤ δ * x / p ^ 2 := by
    rw [le_div_iff₀ hp20]
    rw [le_div_iff₀ (by positivity)] at hpp
    nlinarith
  -- `p⁴ > 1.04 x`
  set r := x ^ (1 / 4 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hx0.le _
  have hr4 : r ^ 4 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hp4 : 1.04 * x < p ^ 4 := by
    have : (1.01 * r) ^ 4 < p ^ 4 := pow_lt_pow_left₀ hpl (by positivity) (by norm_num)
    nlinarith [pow_nonneg hr0 4]
  -- the window `J_p = [c, d)`
  set c := x * (1 - δ) / (τ * p) with hce
  set d := x / (τ * p) with hde
  have hτp : 0 < τ * p := by positivity
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hτp.le
  have hcd : c ≤ d := div_le_div_of_nonneg_right (by nlinarith) hτp.le
  -- each `m` is `p_j q` for one prime `q ∈ J_p`
  have hsingle : ∀ m ∈ P.Mset (tJ θ X₀ ω) x δ j, ∃ i, m.erase j = Finsupp.single i 1 ∧
      P.p i ∈ Icc c d := by
    intro m hm
    obtain ⟨hval, -⟩ := Mset_val ω hm
    obtain ⟨hmx, hs, hjm, hge, h1, h2⟩ := Finset.mem_filter.mp hm
    have h1' : x * (1 - δ) ≤ τ * (p * P.val (m.erase j)) := by rw [← hval]; exact h1
    have h2' : τ * (p * P.val (m.erase j)) < x := by rw [← hval]; exact h2
    have hs' : BeurlingSystem.Sqf (m.erase j) := fun i => by
      rw [Finsupp.erase_apply]; split_ifs
      · exact Nat.zero_le _
      · exact hs i
    have hv'pos := P.one_le_val (m.erase j)
    have hv1 : c ≤ P.val (m.erase j) := by
      rw [hce, div_le_iff₀ hτp]; nlinarith
    have hv2 : P.val (m.erase j) < d := by
      rw [hde, lt_div_iff₀ hτp]; nlinarith
    have hmem : ∀ i ∈ (m.erase j).support, i ∈ m.support ∧ i ≠ j := fun i hi => by
      rw [Finsupp.support_erase] at hi
      exact ⟨Finset.mem_of_mem_erase hi, Finset.ne_of_mem_erase hi⟩
    -- `m' ≠ 0`
    have hne : (m.erase j).support.Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at h0
      have : P.val (m.erase j) = 1 := by rw [h0]; exact P.val_zero
      rw [this, mul_one] at h1'
      have hpx : p ^ 2 ≤ x / 400 := by
        refine hpp.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      nlinarith
    obtain ⟨i, hi⟩ := hne
    obtain ⟨hi', hij⟩ := hmem i hi
    -- at most one prime
    have hsupp : (m.erase j).support = {i} := by
      ext i'
      rw [Finset.mem_singleton]
      refine ⟨fun hi2 => ?_, fun h => h ▸ hi⟩
      by_contra hne'
      obtain ⟨hi2', -⟩ := hmem i' hi2
      have hq1 := prime_lower hc ω hm hi'
      have hq2 := prime_lower hc ω hm hi2'
      have hpi := P.p_pos i
      have hpi' := P.p_pos i'
      have hprod : P.p i * P.p i' ≤ P.val (m.erase j) := by
        rw [P.val_eq_prod_support hs', ← Finset.mul_prod_erase _ _ hi,
          ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne', hi2⟩)]
        have h1'' := P.one_le_prod_p (((m.erase j).support.erase i).erase i')
        have := mul_pos hpi hpi'
        nlinarith
      have hq : 0.99 * p * (0.99 * p) ≤ P.p i * P.p i' :=
        mul_le_mul hq1 hq2 (by positivity) (by linarith)
      have hA : 0.99 * p * (p * (0.99 * p * (0.99 * p))) ≤ τ * (p * P.val (m.erase j)) := by
        apply mul_le_mul hτ1 _ (by positivity) hτ0.le
        exact mul_le_mul_of_nonneg_left (hq.trans hprod) (by linarith)
      have e : 0.99 * p * (p * (0.99 * p * (0.99 * p))) = 0.970299 * p ^ 4 := by ring
      nlinarith
    have hm'i : (m.erase j) i = 1 := le_antisymm (hs' i) (Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hi))
    have hm'eq : m.erase j = Finsupp.single i 1 := by
      ext i'
      by_cases h : i' = i
      · rw [h, hm'i, Finsupp.single_eq_same]
      · rw [Finsupp.single_apply, if_neg (Ne.symm h)]
        exact Finsupp.notMem_support_iff.mp (by rw [hsupp]; simpa using h)
    have hvi : P.val (m.erase j) = P.p i := by
      rw [hm'eq]; simp [BeurlingSystem.val, Finsupp.prod_single_index]
    exact ⟨i, hm'eq, by rw [← hvi]; exact hv1, by rw [← hvi]; exact hv2.le⟩
  -- the injection `m ↦ q`
  let φ : (ℕ →₀ ℕ) → ℕ := fun m => ∑ i ∈ (m.erase j).support, i
  have hφ : ∀ m ∈ P.Mset (tJ θ X₀ ω) x δ j, ∀ i, m.erase j = Finsupp.single i 1 → φ m = i := by
    intro m hm i hi
    simp only [φ, hi, Finsupp.support_single_ne_zero i one_ne_zero, Finset.sum_singleton]
  have hfin : {i | P.p i ∈ Icc c d}.Finite := (P.finite_p_le d).subset fun i hi => hi.2
  have hcard : (P.Mset (tJ θ X₀ ω) x δ j).card ≤ {i | P.p i ∈ Icc c d}.ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    refine Finset.card_le_card_of_injOn φ (fun m hm => ?_) (fun m hm m' hm' h => ?_)
    · obtain ⟨i, hi, hiJ⟩ := hsingle m hm
      rw [hφ m hm i hi]
      exact hfin.mem_toFinset.mpr hiJ
    · obtain ⟨i, hi, -⟩ := hsingle m hm
      obtain ⟨i', hi', -⟩ := hsingle m' hm'
      rw [hφ m hm i hi, hφ m' hm' i' hi'] at h
      rw [(Mset_val ω hm).2, (Mset_val ω hm').2, hi, hi', h]
  have hcount := primeCount_gen hc hev hN (S := Icc c d) hc0 hcd le_rfl
  -- sizes: `|J_p| = δx/(τp) ≤ 1.0102 δx/p²`, `H(2 max(d, X₀)) ≤ H(x)`
  have hJ : d - c = δ * x / (τ * p) := by
    rw [hce, hde]; field_simp; ring
  have hJle : δ * x / (τ * p) ≤ 1.0102 * (δ * x / p ^ 2) := by
    rw [div_le_iff₀ hτp]
    have : δ * x / p ^ 2 * (τ * p) ≥ δ * x / p ^ 2 * (0.99 * p * p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have e : δ * x / p ^ 2 * (0.99 * p * p) = 0.99 * (δ * x) := by field_simp
    nlinarith [mul_pos hδ0 hx0]
  have hd2 : 2 * max d (X₀ : ℝ) ≤ x := by
    have hτp4 : 3.96 ≤ τ * p := by
      have : 0.99 * p ≤ τ := by rw [hpe, hτe]; exact hτ1
      nlinarith
    have hdx : 3.96 * d ≤ x := by
      rw [hde, mul_div_assoc', div_le_iff₀ hτp]; nlinarith
    have : 2 * (X₀ : ℝ) ≤ x := hx2
    rcases le_total d (X₀ : ℝ) with h | h
    · rw [max_eq_right h]; exact this
    · rw [max_eq_left h]; linarith
  have hHd : capH X₀ (2 * max d (X₀ : ℝ)) ≤ Hc X₀ x := by
    rw [Hc_eq hxX]
    exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr (by
      have := le_max_right d (X₀ : ℝ); linarith)) (mem_Ici.mpr hxX) hd2
  have hc' : ((P.Mset (tJ θ X₀ ω) x δ j).card : ℝ) ≤ ({i | P.p i ∈ Icc c d}.ncard : ℝ) := by
    exact_mod_cast hcard
  rw [hJ] at hcount
  have hδxp : 0 ≤ δ * x / p ^ 2 := by positivity
  have e4 : 4 * δ * x / p ^ 2 = 4 * (δ * x / p ^ 2) := by ring
  rw [e4]
  nlinarith

end Queue6

end
