module

public import RequestProject.Beurling.Queue6.S2Ep
public import RequestProject.Beurling.Noise.ThreshMass

/-!
# Local prime counts of the realised system (Corollary 6.3, local form)

For `ω ∈ NiceEv` (all stages good), the primes of `P(ω)` with value in a window `S ⊂ [c, d]`,
`X₀ ≤ c`, are jittered primes decided at slots `s` with `|s - p| ≤ H(s)/2` (box-centred
placement), so their slots lie in `(c - H̄/2 - 1, d + H̄/2]`, `H̄ = H(2d)`, and the sharp slot
count of a window (`slot_window_card`) gives

* `primeCount_le` : `#{j : p_j ∈ S} ≤ 1.0001 (d - c + H(2d) + 1) + 1`;
* `primeCount_le_low` : `#{j : p_j ≤ B} ≤ 2.03 B + 3` for `B ≥ X₀` (rational primes and
  jittered ones);
* `localCount_R` : **the field `localCount` of `BeurlingSystem.ThreshHyp`** for `P(ω)`, with
  `K_loc = H(2 b_*)`.

Also `two_le_p` : every prime of `P(ω)` is `≥ 2`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

lemma realisedOK_Mcl (ω : JitterΩ) : RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω) := by
  rw [Mcl_eq hc]; exact limModel_realisedOK (hc.std ω)

/-- The value of the prime decided at relative slot `k + 1` lies in its box (closed). -/
lemma valF_box (ω : JitterΩ) (k : ℕ) :
    slotF θ X₀ k ω - HF θ X₀ k ω / 2 ≤ valF θ X₀ k ω ∧
      valF θ X₀ k ω ≤ slotF θ X₀ k ω + HF θ X₀ k ω / 2 := by
  rw [valF_eq]
  exact landing_mem_box (HF_pos hc k ω).le (clamp01_mem _)

/-- **Every prime of `P(ω)` is `≥ 2`.** -/
lemma two_le_p (ω : JitterΩ) (j : ℕ) : 2 ≤ (PR θ X₀ ω).p j := by
  have hok := realisedOK_Mcl hc ω
  show 2 ≤ (realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω)).p j
  rw [realisedSystem_p hok]
  rcases hok.equiv j with p | k
  · show (2 : ℝ) ≤ (p.1 : ℝ)
    exact_mod_cast p.2.1.two_le
  · show (2 : ℝ) ≤ valF θ X₀ k.1 ω
    have h1 := (valF_box hc ω k.1).1
    have h2 := four_capH_le (Nat.cast_nonneg _) hc.hX (slotF_ge hc k.1 ω)
    have h3 := slotF_ge hc k.1 ω
    have := X₀_ge_two_pow hc.hX
    unfold HF at h1
    linarith

/-- The slot of a decision whose value is `≤ d` (`d ≥ X₀`) is `≤ 1.0000001 d`, and its width is
`≤ H(2d)`. -/
lemma slot_of_val (ω : JitterΩ) {k : ℕ} {d : ℝ} (hd : (X₀ : ℝ) ≤ d) (hv : valF θ X₀ k ω ≤ d) :
    slotF θ X₀ k ω ≤ 1.0000001 * d ∧ HF θ X₀ k ω ≤ capH X₀ (2 * d) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hs := slotF_ge hc k ω
  have h1 := (valF_box hc ω k).1
  have hH : HF θ X₀ k ω ≤ slotF θ X₀ k ω / 10 ^ 7 := capH_le_div hc.hX hs
  have hsd : slotF θ X₀ k ω ≤ 1.0000001 * d := by
    have : slotF θ X₀ k ω ≤ d + slotF θ X₀ k ω / (2 * 10 ^ 7) := by linarith
    nlinarith
  refine ⟨hsd, ?_⟩
  exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hs) (mem_Ici.mpr (by linarith)) (by linarith)

variable (hev : Even X₀)
include hev

set_option maxHeartbeats 800000 in
/-- **The jittered primes in a window**: for `S ⊂ [c, d]`, `X₀ ≤ d`, on `NiceEv`,
`#{k placed : q_k ∈ S} ≤ 1.0001 (d - c + H(2d) + 1) + 1`. -/
theorem jitCount_le {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {S : Set ℝ} {c d : ℝ}
    (hdX : (X₀ : ℝ) ≤ d) (hcd : c ≤ d) (hS : S ⊆ Icc c d) :
    ({k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}.ncard : ℝ) ≤
      1.0001 * (d - c + capH X₀ (2 * d) + 1) + 1 := by
  classical
  set K := {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}
  have hfin : K.Finite := (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * d)).subset
    fun k hk => by
      have := (slot_of_val hc ω hdX (hS hk.2).2).1
      show slotF θ X₀ k ω ≤ 2 * d
      linarith
  have hH0 : 0 ≤ capH X₀ (2 * d) := capH_nonneg _ _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine slot_window_card hc hev (ω := ω) hfin.toFinset (a₀ := c - capH X₀ (2 * d) / 2 - 1)
    (b := d + capH X₀ (2 * d) / 2) (ℓ := d - c + capH X₀ (2 * d) + 1) (fun k hk => ?_)
    (by linarith) (by linarith)
  obtain ⟨hp, hv⟩ := hfin.mem_toFinset.mp hk
  obtain ⟨hv1, hv2⟩ := hS hv
  obtain ⟨-, hHk⟩ := slot_of_val hc ω hdX hv2
  obtain ⟨b1, b2⟩ := valF_box hc ω k
  have hsg : ω ∈ stageGood θ X₀ k := by
    have := hN.2.1; simp only [SG, mem_iInter] at this; exact this k
  exact ⟨⟨hp, hsg⟩, by linarith, by linarith⟩

set_option maxHeartbeats 800000 in
/-- **The primes of `P(ω)` in a window** `S ⊂ [c, d]`, `X₀ ≤ d`: the jittered ones and at most
`X₀` rational ones, and no rational one when `X₀ ≤ c`. -/
theorem primeCount_split {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {S : Set ℝ} {c d : ℝ}
    (hdX : (X₀ : ℝ) ≤ d) (hcd : c ≤ d) (hS : S ⊆ Icc c d) :
    ({j | (PR θ X₀ ω).p j ∈ S}.ncard : ℝ) ≤ 1.0001 * (d - c + capH X₀ (2 * d) + 1) + 1 +
      (if (X₀ : ℝ) ≤ c then 0 else (X₀ : ℝ)) := by
  classical
  have hok := realisedOK_Mcl hc ω
  have hpj : ∀ j, (PR θ X₀ ω).p j = realisedVal (Mcl θ X₀ ω) (capH X₀) (Ucl ω) (hok.equiv j) :=
    fun j => realisedSystem_p hok j
  set K := {k | placedAt (Mcl θ X₀ ω) k ∧ valF θ X₀ k ω ∈ S}
  have hfinK : K.Finite := (finite_slot_succ_le (M := Mcl θ X₀ ω) (2 * d)).subset
    fun k hk => by
      have := (slot_of_val hc ω hdX (hS hk.2).2).1
      show slotF θ X₀ k ω ≤ 2 * d
      linarith
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
  -- the jittered part
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
  -- the rational part
  have hR : (R.ncard : ℝ) ≤ if (X₀ : ℝ) ≤ c then 0 else (X₀ : ℝ) := by
    split_ifs with h
    · have : R = ∅ := by
        ext j; simp only [R, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hjS, p, hp⟩
        rw [hpj, hp] at hjS
        have h1 : (p.1 : ℝ) < X₀ := by exact_mod_cast p.2.2
        have := (hS hjS).1
        exact absurd (show (p.1 : ℝ) ≥ c from this) (by
          show ¬ ((p.1 : ℝ) ≥ c); push_neg; linarith)
      rw [this, Set.ncard_empty]; simp
    · let g : ℕ → ℕ := fun j => match hok.equiv j with
        | Sum.inl p => p.1
        | Sum.inr _ => 0
      have := Set.ncard_le_ncard_of_injOn g (s := R) (t := (Finset.range X₀ : Set ℕ))
        (fun j hj => by
          obtain ⟨-, p, hp⟩ := hj
          simp only [g, hp, Finset.coe_range, mem_Iio]
          exact p.2.2)
        (fun j hj j' hj' hgg => by
          obtain ⟨-, p, hp⟩ := hj
          obtain ⟨-, p', hp'⟩ := hj'
          simp only [g, hp, hp'] at hgg
          apply hok.equiv.injective
          rw [hp, hp']
          congr 1; exact Subtype.ext hgg)
        (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Finset.card_range] at this
      exact_mod_cast this
  have hK := jitCount_le hc hev hN hdX hcd hS
  have h1 := Set.ncard_le_ncard hsub (hfinA.union hfinR)
  have h2 := Set.ncard_union_le A R
  have h3 : ((({j | (PR θ X₀ ω).p j ∈ S}).ncard : ℕ) : ℝ) ≤ (A.ncard : ℝ) + R.ncard := by
    exact_mod_cast h1.trans h2
  have h4 : (A.ncard : ℝ) ≤ K.ncard := by exact_mod_cast hA
  linarith

/-- **The primes of `P(ω)` in a window above `X₀`**: `#{j : p_j ∈ S} ≤ 1.0001 (d - c + H(2d) + 1)
+ 1` for `S ⊂ [c, d]`, `X₀ ≤ c ≤ d`. -/
theorem primeCount_le {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {S : Set ℝ} {c d : ℝ}
    (hcX : (X₀ : ℝ) ≤ c) (hcd : c ≤ d) (hS : S ⊆ Icc c d) :
    ({j | (PR θ X₀ ω).p j ∈ S}.ncard : ℝ) ≤ 1.0001 * (d - c + capH X₀ (2 * d) + 1) + 1 := by
  have h := primeCount_split hc hev hN (hcX.trans hcd) hcd hS
  rw [if_pos hcX, add_zero] at h
  exact h

/-- **All the primes of `P(ω)` up to `B ≥ X₀`**: `#{j : p_j ≤ B} ≤ 2.03 B + 3` on `NiceEv`. -/
theorem primeCount_le_low {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) {B : ℝ} (hB : (X₀ : ℝ) ≤ B) :
    ({j | (PR θ X₀ ω).p j ≤ B}.ncard : ℝ) ≤ 2.03 * B + 3 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX2 := X₀_ge_two_pow hc.hX
  have he : {j | (PR θ X₀ ω).p j ≤ B} = {j | (PR θ X₀ ω).p j ∈ Icc 2 B} := by
    ext j; simp only [mem_setOf_eq, mem_Icc]
    exact ⟨fun h => ⟨two_le_p hc ω j, h⟩, fun h => h.2⟩
  rw [he]
  have h := primeCount_split hc hev hN (S := Icc 2 B) hB (by linarith) le_rfl
  have hX2' : ¬ ((X₀ : ℝ) ≤ 2) := by push_neg; linarith
  rw [if_neg hX2'] at h
  have hH : capH X₀ (2 * B) ≤ 2 * B / 10 ^ 7 := capH_le_div hc.hX (by linarith)
  linarith

open Classical in
/-- **The field `localCount` of `BeurlingSystem.ThreshHyp`** for `P(ω)` (Lemma 5.23, case (ii)):
for `X₀ ≤ a_* ≤ b_*`, `#{p_j ≤ x : a_* ≤ p_j < b_*} ≤ 13.5 (b_* - a_*) + K_loc + 2` with
`K_loc = 1.0001 (H(2 b_*) + 1)`. -/
theorem localCount_R {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) (x δ : ℝ)
    (ha : (X₀ : ℝ) ≤ BeurlingSystem.aStar x δ)
    (hab : BeurlingSystem.aStar x δ ≤ BeurlingSystem.bStar x δ) :
    ((((PR θ X₀ ω).primesLe x).filter (fun j => BeurlingSystem.aStar x δ ≤ (PR θ X₀ ω).p j ∧
        (PR θ X₀ ω).p j < BeurlingSystem.bStar x δ)).card : ℝ) ≤
      13.5 * (BeurlingSystem.bStar x δ - BeurlingSystem.aStar x δ) +
        1.0001 * (capH X₀ (2 * BeurlingSystem.bStar x δ) + 1) + 2 := by
  set a := BeurlingSystem.aStar x δ
  set b := BeurlingSystem.bStar x δ
  have h := primeCount_le hc hev hN (S := Ico a b) ha hab Ico_subset_Icc_self
  have hsub : ((((PR θ X₀ ω).primesLe x).filter (fun j => a ≤ (PR θ X₀ ω).p j ∧
      (PR θ X₀ ω).p j < b)) : Set ℕ) ⊆ {j | (PR θ X₀ ω).p j ∈ Ico a b} := by
    intro j hj
    simp only [Finset.coe_filter, mem_setOf_eq] at hj
    exact hj.2
  have hfin : {j | (PR θ X₀ ω).p j ∈ Ico a b}.Finite :=
    ((PR θ X₀ ω).finite_p_le b).subset fun j hj => hj.2.le
  have h2 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at h2
  have h3 : ((((PR θ X₀ ω).primesLe x).filter (fun j => a ≤ (PR θ X₀ ω).p j ∧
      (PR θ X₀ ω).p j < b)).card : ℝ) ≤ ({j | (PR θ X₀ ω).p j ∈ Ico a b}.ncard : ℝ) := by
    exact_mod_cast h2
  have hl : 0 ≤ b - a := by linarith
  linarith

end Queue6

end
