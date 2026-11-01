module

public import RequestProject.Beurling.BaseRange.Step3Split
public import RequestProject.Beurling.GenNatPart

/-!
# Step 3 of the proof of Lemma 7.3(b): the decomposition of an element sum

For a Beurling system `S`, a cut index `J₁` (small primes `j < J₁`, large primes `j ≥ J₁`, with
values `< X₀⁻` and `≥ X₀⁻`), a height `x` and a summand `G(value, largest prime)`, the sum over
the elements `e ≠ 0` of value `≤ x` splits (`decomp`) as

  `∑_{d rigid, d ≠ 0} G(d, P⁺(d)) + ∑_{T ⊆ L, T ≠ ∅} Ψ(∏_T p, max_T p)`
  `+ ∑_{e: ℓ(e) not squarefree} G`,

where `L` are the large primes `≤ x`, `D` the rigid elements of value `≤ x`, and
`Ψ(P, M) = ∑_{d ∈ D} 1[val(d) P ≤ x] G(val(d) P, M)`.
-/

@[expose] public section

open Finset BeurlingSystem

namespace BaseRange.S3

variable (S : BeurlingSystem) (J1 : ℕ) (x : ℝ) (G : ℝ → ℝ → ℝ)

/-- The rigid elements of value `≤ x`. -/
noncomputable def Drig : Finset (ℕ →₀ ℕ) := (S.elems x).filter (fun d => ∀ j ∈ d.support, j < J1)

/-- The large primes of value `≤ x`. -/
noncomputable def Lg : Finset ℕ := (S.primesLe x).filter (fun j => J1 ≤ j)

/-- `Ψ(P, M) = ∑_{d ∈ D} 1[val(d) P ≤ x] G(val(d) P, M)`. -/
noncomputable def PsiD (P M : ℝ) : ℝ :=
  ∑ d ∈ Drig S J1 x, if S.val d * P ≤ x then G (S.val d * P) M else 0

/-- The squarefree large parts. -/
def SqfL (J1 : ℕ) (e : ℕ →₀ ℕ) : Prop := ∀ j, J1 ≤ j → e j ≤ 1

lemma p_le_val {e : ℕ →₀ ℕ} {j : ℕ} (hj : j ∈ e.support) : S.p j ≤ S.val e := by
  have h1 := S.pow_le_val e j
  have hk : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have h2 : S.p j ≤ S.p j ^ e j := by
    calc S.p j = S.p j ^ 1 := (pow_one _).symm
      _ ≤ S.p j ^ e j := pow_le_pow_right₀ (S.one_lt j).le hk
  linarith

lemma one_le_val' (e : ℕ →₀ ℕ) : 1 ≤ S.val e := S.one_le_val e

open Classical in
/-- **The decomposition** of the element sum. -/
theorem decomp {X0m : ℝ} (hsmall : ∀ j < J1, S.p j < X0m) (hlarge : ∀ j, J1 ≤ j → X0m ≤ S.p j) :
    ∑ e ∈ (S.elems x).filter (· ≠ 0), G (S.val e) (maxV S e) =
      ∑ d ∈ (Drig S J1 x).filter (· ≠ 0), G (S.val d) (maxV S d) +
      ∑ T ∈ (Lg S J1 x).powerset.filter (·.Nonempty),
        PsiD S J1 x G (∏ j ∈ T, S.p j) (T.fold max 0 S.p) +
      ∑ e ∈ (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e), G (S.val e) (maxV S e) := by
  set E := (S.elems x).filter (· ≠ 0)
  -- split off the rigid elements
  rw [← Finset.sum_filter_add_sum_filter_not E (fun e => largePart J1 e = 0)]
  have hrig : E.filter (fun e => largePart J1 e = 0) = (Drig S J1 x).filter (· ≠ 0) := by
    ext e
    simp only [E, Drig, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, fun j hj => ?_⟩, h2⟩
      by_contra hc
      have : largePart J1 e j = e j := by
        unfold largePart; rw [Finsupp.filter_apply, if_pos hc]
      rw [h3, Finsupp.zero_apply] at this
      exact Finsupp.mem_support_iff.mp hj this.symm
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, h3⟩, ?_⟩
      ext j
      unfold largePart
      rw [Finsupp.filter_apply, Finsupp.zero_apply]
      by_cases h : j < J1
      · rw [if_neg (not_not.mpr h)]
      · rw [if_pos h]; exact Finsupp.notMem_support_iff.mp (fun hj => h (h2 j hj))
  rw [hrig, add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (E.filter (fun e => ¬ largePart J1 e = 0))
    (fun e => SqfL J1 e)]
  have hns : (E.filter (fun e => ¬ largePart J1 e = 0)).filter (fun e => ¬ SqfL J1 e) =
      (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e) := by
    ext e
    simp only [E, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, -⟩, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩
      refine ⟨⟨⟨h1, h2⟩, fun h => h4 ?_⟩, h4⟩
      intro j hj
      have : largePart J1 e j = e j := by
        unfold largePart; rw [Finsupp.filter_apply, if_pos (by omega)]
      rw [h, Finsupp.zero_apply] at this
      omega
  rw [hns]
  congr 1
  -- the squarefree large parts: a bijection with `(T, d)`
  set Pset := ((Lg S J1 x).powerset.filter (·.Nonempty) ×ˢ Drig S J1 x).filter
    (fun q => S.val q.2 * ∏ j ∈ q.1, S.p j ≤ x) with hPset
  have hbij : ∑ e ∈ (E.filter (fun e => ¬ largePart J1 e = 0)).filter (fun e => SqfL J1 e),
      G (S.val e) (maxV S e) =
      ∑ q ∈ Pset, G (S.val q.2 * ∏ j ∈ q.1, S.p j) (q.1.fold max 0 S.p) := by
    apply Finset.sum_nbij' (fun e => ((largePart J1 e).support, smallPart J1 e))
      (fun q => q.2 + ind q.1)
    · intro e he
      simp only [E, Finset.mem_filter] at he
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := he
      have hval := val_split S J1 e
      have hle : S.val (largePart J1 e) = ∏ j ∈ (largePart J1 e).support, S.p j := by
        conv_lhs => rw [largePart_eq_ind h4]
        rw [val_ind]
      simp only [hPset, Finset.mem_product,
        Finset.mem_filter, Finset.mem_powerset, Lg, Drig]
      have hev : S.val e ≤ x := S.mem_elems.mp h1
      refine ⟨⟨⟨fun j hj => ?_, ?_⟩, ?_, fun j hj => ?_⟩, ?_⟩
      · have hj' := hj
        unfold largePart at hj'
        rw [Finsupp.mem_support_iff, Finsupp.filter_apply] at hj'
        by_cases hc : j < J1
        · rw [if_neg (not_not.mpr hc)] at hj'; exact absurd rfl hj'
        · refine Finset.mem_filter.mpr ⟨S.mem_primesLe.mpr ?_, by omega⟩
          have : S.p j ≤ S.val (largePart J1 e) := p_le_val S hj
          have h1' : 1 ≤ S.val (smallPart J1 e) := S.one_le_val _
          nlinarith [S.one_le_val (largePart J1 e)]
      · rw [Finsupp.support_nonempty_iff]; exact h3
      · rw [S.mem_elems]
        have := S.one_le_val (largePart J1 e)
        have h0 := S.one_le_val (smallPart J1 e)
        nlinarith
      · unfold smallPart at hj
        rw [Finsupp.support_filter, Finset.mem_filter] at hj
        exact hj.2
      · rw [← hle, ← hval]; exact hev
    · intro q hq
      simp only [hPset, Finset.mem_product,
        Finset.mem_filter, Finset.mem_powerset, Lg, Drig] at hq
      obtain ⟨⟨⟨hTL, hTn⟩, hd1, hd2⟩, hval⟩ := hq
      have hT : ∀ j ∈ q.1, J1 ≤ j := fun j hj => (Finset.mem_filter.mp (hTL hj)).2
      simp only [E, Finset.mem_filter]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [S.mem_elems, S.val_add, val_ind]; exact hval
      · intro h
        have : (q.2 + ind q.1) (hTn.choose) = 0 := by rw [h]; rfl
        rw [Finsupp.add_apply, ind_apply, if_pos hTn.choose_spec] at this
        omega
      · rw [largePart_add_ind hd2 hT]
        intro h
        have : ind q.1 hTn.choose = 0 := by rw [h]; rfl
        rw [ind_apply, if_pos hTn.choose_spec] at this
        omega
      · intro j hj
        rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp (fun h => by
          have := hd2 j h; omega), zero_add, ind_apply]
        split_ifs <;> omega
    · intro e he
      simp only [E, Finset.mem_filter] at he
      simp only
      rw [← largePart_eq_ind he.2, smallPart_add_largePart]
    · intro q hq
      simp only [hPset, Finset.mem_product,
        Finset.mem_filter, Finset.mem_powerset, Lg, Drig] at hq
      obtain ⟨⟨⟨hTL, -⟩, -, hd2⟩, -⟩ := hq
      have hT : ∀ j ∈ q.1, J1 ≤ j := fun j hj => (Finset.mem_filter.mp (hTL hj)).2
      rw [largePart_add_ind hd2 hT, smallPart_add_ind hd2 hT, support_ind]
    · intro e he
      simp only [E, Finset.mem_filter] at he
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := he
      have hsd : ∀ j ∈ (smallPart J1 e).support, j < J1 := by
        intro j hj
        unfold smallPart at hj
        rw [Finsupp.support_filter, Finset.mem_filter] at hj
        exact hj.2
      have hTl : ∀ j ∈ (largePart J1 e).support, J1 ≤ j := by
        intro j hj
        unfold largePart at hj
        rw [Finsupp.support_filter, Finset.mem_filter] at hj
        omega
      have hTn : (largePart J1 e).support.Nonempty := Finsupp.support_nonempty_iff.mpr h3
      have he' : e = smallPart J1 e + ind (largePart J1 e).support := by
        rw [← largePart_eq_ind h4, smallPart_add_largePart]
      simp only
      conv_lhs => rw [he']
      rw [S.val_add, val_ind, maxV_add_ind S hsmall hlarge hsd hTl hTn]
  rw [hbij, hPset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold PsiD
  rfl

end BaseRange.S3
