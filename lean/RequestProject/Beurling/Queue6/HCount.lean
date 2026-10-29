module

public import RequestProject.Beurling.Queue6.PrimeCount
public import RequestProject.Beurling.LocalPNT.Defs

/-!
# Proposition 5.35(B), Step 1, first bullet: `∫_J ρ̃ ≥ Π(J) - E_loc` (the field `hcount`)

For `ω ∈ NiceEv` and a window `J = (a, b]` with `X₀ ≤ a ≤ b`, `X₀³ ≤ b`:

`Π(b) - Π(a) - E_loc(b) ≤ ∫_a^b ρ̃`, `E_loc(b) = 2 (1.0001 (H(2b) + 1) + 1) + 2.03 √b + 3 +
(log b / log 2) (2.03 b^{1/3} + 3)` (`hcount_R`).

* the primes of `J` are jittered primes `q_k ∈ (a, b]`; those whose box `[s_k ± H(s_k)/2)` lies in
  `[a, b]` contribute mass `1` each to `∫_a^b ρ̃` (`rho_mass_ge`); the others have their slot
  within `H(2b)/2 + 1` of `a` or `b` (two slot windows, `slot_window_card`);
* the prime powers `p^k`, `k ≥ 2`, of `J` have `p ≤ √b` (`k = 2`) or `p ≤ b^{1/3}`,
  `k ≤ log b/log 2`
  (`primeCount_le_low`).

`Eloc_le` : `E_loc(b) ≤ 40 √b` once `log b ≥ 10⁴` (in particular in range (B),
`log b ≥ X₀^{1/100}`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable (X₀ : ℕ)

/-- `E_loc(b)`. -/
noncomputable def Eloc (b : ℝ) : ℝ :=
  2 * (1.0001 * (capH X₀ (2 * b) + 1) + 1) + (2.03 * √b + 3) +
    Real.log b / Real.log 2 * (2.03 * b ^ (1 / 3 : ℝ) + 3)

variable {X₀} {θ : ℝ} (hc : Cond θ X₀)
include hc

/-- **The primes of a window above `X₀` are jittered**: `#{j : p_j ∈ S} ≤ #{k placed : q_k ∈ S}`
for `S ⊂ [c, d]`, `X₀ ≤ c`. -/
lemma ncard_p_le_jit (ω : JitterΩ) {S : Set ℝ} {c d : ℝ} (hcX : (X₀ : ℝ) ≤ c)
    (hS : S ⊆ Icc c d) :
    {j | (PR θ X₀ ω).p j ∈ S}.ncard ≤
      {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}.ncard := by
  classical
  have hok := realisedOK_Mcl hc ω
  have hpj : ∀ j, (PR θ X₀ ω).p j = realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (hok.equiv j) :=
    fun j => realisedSystem_p hok j
  have hdX : (X₀ : ℝ) ≤ d ∨ S = ∅ := by
    by_cases h : S = ∅
    · exact Or.inr h
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact Or.inl (hcX.trans ((hS hx).1.trans (hS hx).2))
  rcases hdX with hdX | h0
  swap
  · have : {j | (PR θ X₀ ω).p j ∈ S} = ∅ := by rw [h0]; ext; simp
    rw [this, Set.ncard_empty]; exact Nat.zero_le _
  have hfinK : {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}.Finite :=
    (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * d)).subset fun k hk => by
      have := (slot_of_val hc ω hdX (hS hk.2).2).1
      show slotF θ X₀ k ω ≤ 2 * d
      linarith
  let f : ℕ → ℕ := fun j => match hok.equiv j with
    | Sum.inl _ => 0
    | Sum.inr k => k.1
  refine Set.ncard_le_ncard_of_injOn f (fun j hj => ?_) (fun j hj j' hj' hff => ?_) hfinK
  · simp only [mem_setOf_eq] at hj
    rw [hpj] at hj
    simp only [f]
    rcases he : hok.equiv j with p | k
    · rw [he] at hj
      have : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
      have : c ≤ (p.1 : ℝ) := (hS hj).1
      exfalso; linarith
    · rw [he] at hj
      exact ⟨k.2, hj⟩
  · simp only [mem_setOf_eq] at hj hj'
    rw [hpj] at hj hj'
    apply hok.equiv.injective
    simp only [f] at hff
    rcases he : hok.equiv j with p | k <;> rcases he' : hok.equiv j' with p' | k' <;>
      rw [he] at hj hff <;> rw [he'] at hj' hff
    · have : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
      have : c ≤ (p.1 : ℝ) := (hS hj).1; exfalso; linarith
    · have : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
      have : c ≤ (p.1 : ℝ) := (hS hj).1; exfalso; linarith
    · have : (p'.1 : ℝ) < X₀ := by exact_mod_cast p'.2.2
      have : c ≤ (p'.1 : ℝ) := (hS hj').1; exfalso; linarith
    · simp only at hff
      congr 1; exact Subtype.ext hff

omit hc in
/-- One box: `∫_a^b H⁻¹ 1[s - H/2 ≤ y < s + H/2] dy ≥ 1` when the box lies in `[a, b]`, and the
integrand is `≥ 0`. -/
lemma box_integral {a b s H : ℝ} (hH : 0 < H) (h1 : a ≤ s - H / 2) (h2 : s + H / 2 ≤ b) :
    1 ≤ ∫ y in a..b, (if s - H / 2 ≤ y ∧ y < s + H / 2 then H⁻¹ else 0) := by
  classical
  set g : ℝ → ℝ := fun y => if s - H / 2 ≤ y ∧ y < s + H / 2 then H⁻¹ else 0
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    simp only [g]; split_ifs <;> positivity
  have hgm : Measurable g := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  have hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun p q =>
    (intervalIntegrable_const (c := H⁻¹)).mono_fun' hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
        simp only [g]; split_ifs
        · exact le_rfl
        · positivity)
  have hmono := intervalIntegral.integral_mono_interval (f := g) (μ := volume) h1
    (by linarith : s - H / 2 ≤ s + H / 2) h2 (Filter.Eventually.of_forall fun y => hg0 y)
    (hgi a b)
  refine le_trans ?_ hmono
  have hc : (∫ y in (s - H / 2)..(s + H / 2), g y) =
      ∫ y in (s - H / 2)..(s + H / 2), (H⁻¹ : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hX : ∀ᵐ r ∂volume, r ≠ s + H / 2 := by
      have : volume ({s + H / 2} : Set ℝ) = 0 := Real.volume_singleton
      rw [ae_iff]; simp [this]
    filter_upwards [hX] with y hy hyI
    rw [uIoc_of_le (by linarith)] at hyI
    simp only [g]
    rw [if_pos ⟨hyI.1.le, lt_of_le_of_ne hyI.2 hy⟩]
  rw [hc, intervalIntegral.integral_const, smul_eq_mul]
  have : (s + H / 2 - (s - H / 2)) * H⁻¹ = 1 := by field_simp; ring
  rw [this]

variable (hev : Even X₀)
include hev

omit hev in
set_option maxHeartbeats 1600000 in
/-- **The mass of the boxes inside a window**: the decisions of good stages whose boxes lie in
`[a, b]` number at most `∫_a^b ρ̃`. -/
theorem rho_mass_ge (ω : JitterΩ) {a b : ℝ} (hab : a ≤ b) (K : Finset ℕ)
    (hK : ∀ k ∈ K, ω ∈ lawA θ X₀ k ∧ a ≤ slotF θ X₀ k ω - HF θ X₀ k ω / 2 ∧
      slotF θ X₀ k ω + HF θ X₀ k ω / 2 ≤ b) :
    (K.card : ℝ) ≤ ∫ y in a..b, rhoT θ X₀ ω y := by
  classical
  set Q := s2Q θ X₀ ω b 0
  set sl := s2sl θ X₀ ω b 0
  have hrep : ∀ y ∈ uIcc a b, rhoT θ X₀ ω y = Margin.Exact.rhoTilde Q sl (Hc X₀) y :=
    fun y hy => by
      rw [uIcc_of_le hab] at hy
      exact hS2rep_R hc ω b 0 y (by linarith [hy.2])
  rw [intervalIntegral.integral_congr hrep]
  set g : ℕ → ℝ → ℝ := fun q y => if sl q - Hc X₀ (sl q) / 2 ≤ y ∧ y < sl q + Hc X₀ (sl q) / 2
    then (Hc X₀ (sl q))⁻¹ else 0
  have hHq : ∀ q, 0 < Hc X₀ (sl q) := fun q => by
    show 0 < Hc X₀ (slotF θ X₀ q ω)
    rw [Hc_slot hc ω q]; exact HF_pos hc q ω
  have hg0 : ∀ q y, 0 ≤ g q y := fun q y => by
    simp only [g]; split_ifs
    · exact (inv_pos.mpr (hHq q)).le
    · exact le_rfl
  have hgm : ∀ q, Measurable (g q) := fun q => by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  have hgi : ∀ q, IntervalIntegrable (g q) volume a b := fun q =>
    (intervalIntegrable_const (c := (Hc X₀ (sl q))⁻¹)).mono_fun' (hgm q).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 q y)]
        simp only [g]; split_ifs
        · exact le_rfl
        · exact (inv_pos.mpr (hHq q)).le)
  have hsum : (fun y => Margin.Exact.rhoTilde Q sl (Hc X₀) y) = fun y => ∑ q ∈ Q, g q y := by
    funext y; unfold Margin.Exact.rhoTilde; rfl
  rw [hsum, intervalIntegral.integral_finset_sum fun q _ => hgi q]
  -- `K ⊂ Q` and each box of `K` has mass `1`
  have hKQ : K ⊆ Q := fun k hk => by
    obtain ⟨hA, -, h2⟩ := hK k hk
    have := HF_pos hc k ω
    refine mem_s2Q.mpr ⟨?_, hA⟩
    have hs := slotF_ge hc k ω
    have hb : (X₀ : ℝ) ≤ b := by linarith
    nlinarith
  have h1 : ∀ k ∈ K, (1 : ℝ) ≤ ∫ y in a..b, g k y := fun k hk => by
    obtain ⟨-, h1, h2⟩ := hK k hk
    have hH := Hc_slot hc ω k
    simp only [g, sl, s2sl, hH]
    exact box_integral (HF_pos hc k ω) h1 h2
  have h0 : ∀ q ∈ Q, 0 ≤ ∫ y in a..b, g q y := fun q _ =>
    intervalIntegral.integral_nonneg hab fun y _ => hg0 q y
  calc (K.card : ℝ) = ∑ k ∈ K, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ K, ∫ y in a..b, g k y := Finset.sum_le_sum h1
    _ ≤ ∑ q ∈ Q, ∫ y in a..b, g q y := Finset.sum_le_sum_of_subset_of_nonneg hKQ
        fun q hq _ => h0 q hq

set_option maxHeartbeats 1600000 in
/-- **The primes of a window** `(a, b]`, `X₀ ≤ a ≤ b`: at most
`∫_a^b ρ̃ + 2 (1.0001 (H(2b) + 1) + 1)`, on `NiceEv`. -/
theorem primes_window_le {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {a b : ℝ} (haX : (X₀ : ℝ) ≤ a)
    (hab : a ≤ b) :
    ({j | (PR θ X₀ ω).p j ∈ Ioc a b}.ncard : ℝ) ≤
      (∫ y in a..b, rhoT θ X₀ ω y) + 2 * (1.0001 * (capH X₀ (2 * b) + 1) + 1) := by
  classical
  have hbX : (X₀ : ℝ) ≤ b := haX.trans hab
  set Hb := capH X₀ (2 * b)
  have hHb0 : 0 ≤ Hb := capH_nonneg _ _
  have hsg : ∀ k, ω ∈ stageGood θ X₀ k := fun k => by
    have := hN.2.1; simp only [SG, mem_iInter] at this; exact this k
  have h1 := ncard_p_le_jit hc ω (S := Ioc a b) haX Ioc_subset_Icc_self
  set K := {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ Ioc a b}
  have hfinK : K.Finite := (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * b)).subset fun k hk => by
    have := (slot_of_val hc ω hbX hk.2.2).1
    show slotF θ X₀ k ω ≤ 2 * b
    linarith
  set KF := hfinK.toFinset
  set Kin := KF.filter fun k => a ≤ slotF θ X₀ k ω - HF θ X₀ k ω / 2 ∧
    slotF θ X₀ k ω + HF θ X₀ k ω / 2 ≤ b
  set Ka := KF.filter fun k => slotF θ X₀ k ω - HF θ X₀ k ω / 2 < a
  set Kb := KF.filter fun k => b < slotF θ X₀ k ω + HF θ X₀ k ω / 2
  have hcov : KF ⊆ Kin ∪ Ka ∪ Kb := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_filter, Kin, Ka, Kb]
    by_cases h1 : a ≤ slotF θ X₀ k ω - HF θ X₀ k ω / 2
    · by_cases h2 : slotF θ X₀ k ω + HF θ X₀ k ω / 2 ≤ b
      · exact Or.inl (Or.inl ⟨hk, h1, h2⟩)
      · exact Or.inr ⟨hk, lt_of_not_ge h2⟩
    · exact Or.inl (Or.inr ⟨hk, lt_of_not_ge h1⟩)
  have hmem : ∀ k ∈ KF, placedAt (Mcl θ X₀ ω) k ∧ a < valF θ X₀ k ω ∧ valF θ X₀ k ω ≤ b ∧
      HF θ X₀ k ω ≤ Hb := fun k hk => by
    obtain ⟨hp, hv1, hv2⟩ := hfinK.mem_toFinset.mp hk
    exact ⟨hp, hv1, hv2, (slot_of_val hc ω hbX hv2).2⟩
  have hin := rho_mass_ge hc ω hab Kin fun k hk => by
    obtain ⟨hk, h1, h2⟩ := Finset.mem_filter.mp hk
    exact ⟨⟨(hmem k hk).1, hsg k⟩, h1, h2⟩
  have hKa : (Ka.card : ℝ) ≤ 1.0001 * (Hb + 1) + 1 := by
    refine slot_window_card hc hev (ω := ω) Ka (a₀ := a - Hb / 2 - 1) (b := a + Hb / 2)
      (ℓ := Hb + 1) (fun k hk => ?_) (by linarith) (by linarith)
    obtain ⟨hk, h⟩ := Finset.mem_filter.mp hk
    obtain ⟨hp, hv1, hv2, hH⟩ := hmem k hk
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    exact ⟨⟨hp, hsg k⟩, by linarith, by linarith⟩
  have hKb : (Kb.card : ℝ) ≤ 1.0001 * (Hb + 1) + 1 := by
    refine slot_window_card hc hev (ω := ω) Kb (a₀ := b - Hb / 2 - 1) (b := b + Hb / 2)
      (ℓ := Hb + 1) (fun k hk => ?_) (by linarith) (by linarith)
    obtain ⟨hk, h⟩ := Finset.mem_filter.mp hk
    obtain ⟨hp, hv1, hv2, hH⟩ := hmem k hk
    obtain ⟨b1, b2⟩ := valF_box hc ω k
    exact ⟨⟨hp, hsg k⟩, by linarith, by linarith⟩
  have hcard : (KF.card : ℝ) ≤ Kin.card + Ka.card + Kb.card := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le (Kin ∪ Ka) Kb
    have h3 := Finset.card_union_le Kin Ka
    have : KF.card ≤ Kin.card + Ka.card + Kb.card := by omega
    exact_mod_cast this
  have hK : (K.ncard : ℝ) = KF.card := by rw [Set.ncard_eq_toFinset_card _ hfinK]
  have h1' : ({j | (PR θ X₀ ω).p j ∈ Ioc a b}.ncard : ℝ) ≤ K.ncard := by exact_mod_cast h1
  linarith

set_option maxHeartbeats 1600000 in
/-- **The field `hcount`** (Proposition 5.35(B), Step 1, first bullet): on `NiceEv`, for
`X₀ ≤ a ≤ b`, `X₀³ ≤ b`, `Π(b) - Π(a) - E_loc(b) ≤ ∫_a^b ρ̃`. -/
theorem hcount_R {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {a b : ℝ} (haX : (X₀ : ℝ) ≤ a)
    (hab : a ≤ b) (hb3 : (X₀ : ℝ) ^ 3 ≤ b) :
    LocalPNT.piCount (PR θ X₀ ω) b - LocalPNT.piCount (PR θ X₀ ω) a - Eloc X₀ b ≤
      ∫ y in a..b, rhoT θ X₀ ω y := by
  classical
  set P := PR θ X₀ ω
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hbig := X₀_ge_two_pow hc.hX
  have hb0 : 0 < b := by linarith
  have hp2 := two_le_p hc ω
  -- `Π(b) - Π(a)` is the sum over the prime powers of `(a, b]`
  have hsub : P.pps a ⊆ P.pps b := fun jk hjk => by
    rw [BeurlingSystem.mem_pps] at hjk ⊢; linarith
  have hdiff : LocalPNT.piCount P b - LocalPNT.piCount P a =
      ∑ jk ∈ P.pps b \ P.pps a, 1 / ((jk.2 : ℝ) + 1) := by
    unfold LocalPNT.piCount
    rw [← Finset.sum_sdiff hsub]; ring
  set D := P.pps b \ P.pps a
  set D0 := D.filter fun jk => jk.2 = 0
  set D1 := D.filter fun jk => jk.2 = 1
  set D2 := D.filter fun jk => 2 ≤ jk.2
  have hD : ∑ jk ∈ D, 1 / ((jk.2 : ℝ) + 1) ≤ D0.card + D1.card + D2.card := by
    have h1 : ∑ jk ∈ D, 1 / ((jk.2 : ℝ) + 1) ≤ ∑ jk ∈ D, (1 : ℝ) :=
      Finset.sum_le_sum fun jk _ => by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ jk.2 := Nat.cast_nonneg _; linarith
    have h2 : D ⊆ D0 ∪ D1 ∪ D2 := fun jk hjk => by
      simp only [Finset.mem_union, Finset.mem_filter, D0, D1, D2]
      rcases Nat.lt_or_ge jk.2 2 with h | h
      · rcases Nat.lt_or_ge jk.2 1 with h' | h'
        · exact Or.inl (Or.inl ⟨hjk, by omega⟩)
        · exact Or.inl (Or.inr ⟨hjk, by omega⟩)
      · exact Or.inr ⟨hjk, h⟩
    have h3a := Finset.card_le_card h2
    have h3b := Finset.card_union_le (D0 ∪ D1) D2
    have h3c := Finset.card_union_le D0 D1
    have h3 : D.card ≤ D0.card + D1.card + D2.card := by omega
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    have : (D.card : ℝ) ≤ D0.card + D1.card + D2.card := by exact_mod_cast h3
    linarith
  -- `D₀`: the primes of `(a, b]`
  have hD0 : (D0.card : ℝ) ≤ ({j | P.p j ∈ Ioc a b}.ncard : ℝ) := by
    have hfin : {j | P.p j ∈ Ioc a b}.Finite := (P.finite_p_le b).subset fun j hj => hj.2
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have := Finset.card_le_card_of_injOn (fun jk : ℕ × ℕ => jk.1) (s := D0) (t := hfin.toFinset)
      (fun jk hjk => by
        obtain ⟨hD, h0⟩ := Finset.mem_filter.mp hjk
        obtain ⟨hb, ha⟩ := Finset.mem_sdiff.mp hD
        rw [BeurlingSystem.mem_pps, h0] at hb
        rw [BeurlingSystem.mem_pps, h0] at ha
        simp only [zero_add, pow_one, not_le] at hb ha
        simp only [Set.Finite.coe_toFinset, mem_setOf_eq, mem_Ioc]
        exact ⟨ha, hb⟩)
      (fun jk hjk jk' hjk' h => by
        have h0 := (Finset.mem_filter.mp hjk).2
        have h0' := (Finset.mem_filter.mp hjk').2
        exact Prod.ext h (by rw [h0, h0']))
    exact_mod_cast this
  -- `D₁`: the squares, `p ≤ √b`
  have hsb : (X₀ : ℝ) ≤ √b := by
    rw [show (X₀ : ℝ) = √((X₀ : ℝ) ^ 2) by rw [Real.sqrt_sq hX0]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hD1 : (D1.card : ℝ) ≤ 2.03 * √b + 3 := by
    refine le_trans ?_ (primeCount_le_low hc hev hN hsb)
    have hfin : {j | P.p j ≤ √b}.Finite := P.finite_p_le _
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have := Finset.card_le_card_of_injOn (fun jk : ℕ × ℕ => jk.1) (s := D1) (t := hfin.toFinset)
      (fun jk hjk => by
        obtain ⟨hD, h1⟩ := Finset.mem_filter.mp hjk
        obtain ⟨hb, -⟩ := Finset.mem_sdiff.mp hD
        rw [BeurlingSystem.mem_pps, h1] at hb
        simp only [Set.Finite.coe_toFinset, mem_setOf_eq]
        have hp0 : 0 ≤ P.p jk.1 := by linarith [hp2 jk.1]
        rw [show P.p jk.1 = √(P.p jk.1 ^ 2) by rw [Real.sqrt_sq hp0]]
        exact Real.sqrt_le_sqrt (by simpa using hb))
      (fun jk hjk jk' hjk' h => by
        have h1 := (Finset.mem_filter.mp hjk).2
        have h1' := (Finset.mem_filter.mp hjk').2
        exact Prod.ext h (by rw [h1, h1']))
    exact_mod_cast this
  -- `D₂`: the higher powers, `p ≤ b^{1/3}`, `k + 1 ≤ log b / log 2`
  set B3 := b ^ (1 / 3 : ℝ)
  have hB3 : B3 ^ 3 = b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; norm_num
  have hB30 : 0 ≤ B3 := Real.rpow_nonneg hb0.le _
  have hB3X : (X₀ : ℝ) ≤ B3 := by
    by_contra h; push_neg at h
    have : B3 ^ 3 < (X₀ : ℝ) ^ 3 := pow_lt_pow_left₀ h hB30 (by norm_num)
    linarith
  set Kmax := ⌊Real.log b / Real.log 2⌋₊
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD2 : (D2.card : ℝ) ≤ Real.log b / Real.log 2 * (2.03 * B3 + 3) := by
    have hfin : {j | P.p j ≤ B3}.Finite := P.finite_p_le _
    have hmaps : ∀ jk ∈ D2, jk ∈ hfin.toFinset ×ˢ Finset.range (Kmax + 1) := fun jk hjk => by
      obtain ⟨hD, h2⟩ := Finset.mem_filter.mp hjk
      obtain ⟨hb, -⟩ := Finset.mem_sdiff.mp hD
      rw [BeurlingSystem.mem_pps] at hb
      have hp := hp2 jk.1
      have hp1 : 1 ≤ P.p jk.1 := by linarith
      rw [Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_range]
      constructor
      · show P.p jk.1 ≤ B3
        have h3 : P.p jk.1 ^ 3 ≤ b :=
          (pow_le_pow_right₀ hp1 (by omega : 3 ≤ jk.2 + 1)).trans hb
        by_contra h; push_neg at h
        have : B3 ^ 3 < P.p jk.1 ^ 3 := pow_lt_pow_left₀ h hB30 (by norm_num)
        linarith
      · have h4 : (2 : ℝ) ^ (jk.2 + 1) ≤ b :=
          (pow_le_pow_left₀ (by norm_num) hp _).trans hb
        have h5 : ((jk.2 + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log b := by
          rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h4
        have h6 : ((jk.2 + 1 : ℕ) : ℝ) ≤ Real.log b / Real.log 2 := by
          rw [le_div_iff₀ hl2]; exact h5
        have := Nat.le_floor h6
        omega
    have h1 := Finset.card_le_card hmaps
    rw [Finset.card_product, Finset.card_range] at h1
    have h2 : (hfin.toFinset.card : ℝ) ≤ 2.03 * B3 + 3 := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]; exact primeCount_le_low hc hev hN hB3X
    -- `D₂ ⊂ (j, k)` with `k ≥ 2`: refine the count (`k ∈ [2, Kmax]`)
    have hmaps' : ∀ jk ∈ D2, jk ∈ hfin.toFinset ×ˢ (Finset.range (Kmax + 1)).filter (2 ≤ ·) :=
      fun jk hjk => by
        have := hmaps jk hjk
        rw [Finset.mem_product] at this ⊢
        exact ⟨this.1, Finset.mem_filter.mpr ⟨this.2, (Finset.mem_filter.mp hjk).2⟩⟩
    have h1' := Finset.card_le_card hmaps'
    rw [Finset.card_product] at h1'
    have hK : (((Finset.range (Kmax + 1)).filter (2 ≤ ·)).card : ℝ) ≤
        Real.log b / Real.log 2 := by
      have : ((Finset.range (Kmax + 1)).filter (2 ≤ ·)) ⊆ Finset.Icc 2 Kmax := fun k hk => by
        obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
        rw [Finset.mem_range] at hk1
        exact Finset.mem_Icc.mpr ⟨hk2, by omega⟩
      have h := Finset.card_le_card this
      rw [Nat.card_Icc] at h
      have : (((Finset.range (Kmax + 1)).filter (2 ≤ ·)).card : ℝ) ≤ (Kmax : ℝ) := by
        have : Kmax + 1 - 2 ≤ Kmax := by omega
        exact_mod_cast h.trans this
      exact this.trans (Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) hl2.le))
    have h0 : (0 : ℝ) ≤ 2.03 * B3 + 3 := by positivity
    calc (D2.card : ℝ) ≤ (hfin.toFinset.card : ℝ) *
          (((Finset.range (Kmax + 1)).filter (2 ≤ ·)).card : ℝ) := by exact_mod_cast h1'
      _ ≤ (2.03 * B3 + 3) * (Real.log b / Real.log 2) :=
          mul_le_mul h2 hK (Nat.cast_nonneg _) h0
      _ = Real.log b / Real.log 2 * (2.03 * B3 + 3) := by ring
  have hpw := primes_window_le hc hev hN haX hab
  unfold Eloc
  rw [hdiff]
  linarith

omit hc hev in
/-- **`E_loc(b) ≤ 40 √b`** for `log b ≥ 10⁴`, `X₀ ≤ b` (and `log X₀ ≥ 10⁸`). -/
theorem Eloc_le (hX : 10 ^ 8 ≤ Real.log X₀) {b : ℝ} (hbX : (X₀ : ℝ) ≤ b)
    (hb : 10 ^ 4 ≤ Real.log b) : Eloc X₀ b ≤ 40 * √b := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hb0 : 0 < b := by linarith
  set L := Real.log b
  -- `H(2b) ≤ (2b)^{1/8} ≤ √b`
  have hH : capH X₀ (2 * b) ≤ (2 * b) ^ (1 / 8 : ℝ) :=
    InitialRange.capH_le_rpow hX0 hX (by linarith)
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb0
  have hsq : √b * √b = b := Real.mul_self_sqrt hb0.le
  -- the powers of `b` in terms of `e^{L/24}`
  set E := Real.exp (L / 24)
  have hE : 0 < E := Real.exp_pos _
  have hbE : b = E ^ 24 := by
    rw [← Real.exp_nat_mul, show ((24 : ℕ) : ℝ) * (L / 24) = L by ring, Real.exp_log hb0]
  have hsE : √b = E ^ 12 := by
    rw [hbE, show E ^ 24 = (E ^ 12) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h3E : b ^ (1 / 3 : ℝ) = E ^ 8 := by
    rw [hbE, ← Real.rpow_natCast, ← Real.rpow_mul hE.le, ← Real.rpow_natCast]; norm_num
  have h8E : (2 * b) ^ (1 / 8 : ℝ) ≤ 2 * E ^ 3 := by
    rw [Real.mul_rpow (by norm_num) hb0.le, hbE, ← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    have : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have e : (24 : ℕ) * (1 / 8 : ℝ) = (3 : ℕ) := by norm_num
    rw [show ((24 : ℕ) : ℝ) * (1 / 8 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [pow_pos hE 3]
  -- `E ≥ e^{416}`, so `L = 24 log E ≤ E` and `E ≥ 10^{100}`
  have hLE : L ≤ E := by
    have := Real.add_one_le_exp (L / 24)
    have h2 := Real.add_one_le_exp (L / 48)
    have e : Real.exp (L / 24) = Real.exp (L / 48) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [show E = Real.exp (L / 24) from rfl, e]
    nlinarith
  have hE1 : 1000 ≤ E := by
    have := Real.add_one_le_exp (L / 24)
    show 1000 ≤ Real.exp (L / 24)
    linarith
  have hl2 : 0.69 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hdiv : L / Real.log 2 ≤ 1.45 * L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold Eloc
  rw [h3E, hsE]
  rw [hsE] at hsb
  have hLE' : L / Real.log 2 ≤ 1.45 * E := by linarith
  have hL0 : 0 ≤ L / Real.log 2 := div_nonneg (by linarith) (by linarith)
  have h1 : L / Real.log 2 * (2.03 * E ^ 8 + 3) ≤ 1.45 * E * (2.03 * E ^ 8 + 3) :=
    mul_le_mul_of_nonneg_right hLE' (by positivity)
  have hE9 : E ^ 9 ≤ E ^ 12 / 1000 := by
    rw [le_div_iff₀ (by norm_num)]
    have : E ^ 12 = E ^ 9 * E ^ 3 := by ring
    have h3 : (1000 : ℝ) ≤ E ^ 3 := le_trans hE1 (le_self_pow₀ (by linarith) (by norm_num))
    nlinarith [pow_pos hE 9]
  have hE3 : E ^ 3 ≤ E ^ 12 / 1000 := by
    rw [le_div_iff₀ (by norm_num)]
    have : E ^ 12 = E ^ 3 * E ^ 9 := by ring
    have h9 : (1000 : ℝ) ≤ E ^ 9 := le_trans hE1 (le_self_pow₀ (by linarith) (by norm_num))
    nlinarith [pow_pos hE 3]
  have hE1' : E ≤ E ^ 12 / 1000 := by
    have : E ≤ E ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have h1e : (1 : ℝ) ≤ E ^ 12 / 1000 := by linarith
  nlinarith

omit hc hev in
lemma Eloc_nonneg (b : ℝ) (hb : 1 ≤ b) : 0 ≤ Eloc X₀ b := by
  have := capH_nonneg (X₀ : ℝ) (2 * b)
  have : 0 ≤ Real.log b := Real.log_nonneg hb
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Eloc; positivity

/-- **The field `hcount` of `KR.RML6.G1BInputs`** at a start `y` with `0 < δ ≤ 1/4`,
`X₀ ≤ y(1 - 2δ)`, `X₀³ ≤ y(1 - δ)` and `log(y(1 - δ)) ≥ 10⁴`, for `ρt = ρ̃`, on `NiceEv`:
`E_loc = E_loc(y(1 - δ))` satisfies `0 ≤ E_loc ≤ 40√y` and
`Π(y(1-δ)) - Π(y(1-2δ)) - E_loc ≤ ∫_{y(1-2δ)}^{y(1-δ)} ρ̃`. -/
theorem hcount_field {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {y δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (ha : (X₀ : ℝ) ≤ y * (1 - 2 * δ)) (hb3 : (X₀ : ℝ) ^ 3 ≤ y * (1 - δ))
    (hlb : 10 ^ 4 ≤ Real.log (y * (1 - δ))) :
    0 ≤ Eloc X₀ (y * (1 - δ)) ∧ Eloc X₀ (y * (1 - δ)) ≤ 40 * √y ∧
      LocalPNT.piCount (PR θ X₀ ω) (y * (1 - δ)) -
          LocalPNT.piCount (PR θ X₀ ω) (y * (1 - 2 * δ)) - Eloc X₀ (y * (1 - δ)) ≤
        ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), rhoT θ X₀ ω z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hy0 : 0 < y := by
    by_contra h; push_neg at h
    have : y * (1 - 2 * δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
    linarith
  have hab : y * (1 - 2 * δ) ≤ y * (1 - δ) := by nlinarith
  have hbX : (X₀ : ℝ) ≤ y * (1 - δ) := ha.trans hab
  refine ⟨Eloc_nonneg _ (by linarith), ?_, hcount_R hc hev hN ha hab hb3⟩
  refine (Eloc_le hc.hX hbX hlb).trans ?_
  have : √(y * (1 - δ)) ≤ √y := Real.sqrt_le_sqrt (by nlinarith)
  linarith

end Queue6

end
