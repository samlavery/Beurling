module

public import RequestProject.Beurling.BaseRange.StepTele
public import RequestProject.Beurling.BaseRange.StepAbel

/-!
# Step 3 of the proof of Lemma 7.3(b): elements as rigid part × large primes

For a Beurling system `S` and a cut index `J₁` (the primes `p_j`, `j < J₁`, are the small ones),
an element `e` splits as `e = d + ℓ` with `d = e|_{j < J₁}` (the rigid part, in the paper
`d ∈ 𝒟`) and `ℓ = e|_{j ≥ J₁}` (the large primes). This file proves the structural facts used to
rewrite the value-order sharp operator as a sum over the rigid parts and the sets of large
primes:

* `smallPart`, `largePart`, `smallPart_add_largePart`, `val_split`;
* `ind T = ∑_{j ∈ T} single j 1` (a squarefree large part), `ind_apply`, `support_ind`,
  `val_ind` (`= ∏_{j ∈ T} p_j`);
* `maxV` (the largest prime value), `maxV_add_ind` (it is the largest large prime when `T ≠ ∅`).
-/

@[expose] public section

open Finset BeurlingSystem

namespace BaseRange.S3

variable (S : BeurlingSystem)

/-- The rigid part `e|_{j < J₁}`. -/
noncomputable def smallPart (J1 : ℕ) (e : ℕ →₀ ℕ) : ℕ →₀ ℕ := e.filter (· < J1)

/-- The large part `e|_{j ≥ J₁}`. -/
noncomputable def largePart (J1 : ℕ) (e : ℕ →₀ ℕ) : ℕ →₀ ℕ := e.filter (fun j => ¬ j < J1)

lemma smallPart_add_largePart (J1 : ℕ) (e : ℕ →₀ ℕ) :
    smallPart J1 e + largePart J1 e = e :=
  Finsupp.filter_pos_add_filter_neg e (· < J1)

lemma val_split (J1 : ℕ) (e : ℕ →₀ ℕ) :
    S.val e = S.val (smallPart J1 e) * S.val (largePart J1 e) := by
  conv_lhs => rw [← smallPart_add_largePart J1 e]
  rw [S.val_add]

/-- `ind T = ∑_{j ∈ T} single j 1`. -/
noncomputable def ind (T : Finset ℕ) : ℕ →₀ ℕ := ∑ j ∈ T, Finsupp.single j 1

lemma ind_apply (T : Finset ℕ) (j : ℕ) : ind T j = if j ∈ T then 1 else 0 := by
  classical
  unfold ind
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

lemma support_ind (T : Finset ℕ) : (ind T).support = T := by
  classical
  ext j
  rw [Finsupp.mem_support_iff, ind_apply]
  split_ifs with h <;> simp [h]

lemma val_ind (T : Finset ℕ) : S.val (ind T) = ∏ j ∈ T, S.p j := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [ind, BeurlingSystem.val]
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, ← ih]
    unfold ind
    rw [Finset.sum_insert ha, S.val_add, S.val_single, pow_one]

/-- The largest prime value of `e` (`0` for `e = 0`). -/
noncomputable def maxV (e : ℕ →₀ ℕ) : ℝ := e.support.fold max 0 S.p

lemma fold_max_le_iff (T : Finset ℕ) (f : ℕ → ℝ) (b c : ℝ) :
    T.fold max b f ≤ c ↔ b ≤ c ∧ ∀ j ∈ T, f j ≤ c := Finset.fold_max_le (c := c)

/-- With rigid `d` and a nonempty set `T` of large primes, the largest prime of `d + ind T` is
the largest of `T`. -/
lemma maxV_add_ind {J1 : ℕ} {X0m : ℝ} (hsmall : ∀ j < J1, S.p j < X0m)
    (hlarge : ∀ j, J1 ≤ j → X0m ≤ S.p j) {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < J1)
    {T : Finset ℕ} (hT : ∀ j ∈ T, J1 ≤ j) (hTn : T.Nonempty) :
    maxV S (d + ind T) = T.fold max 0 S.p := by
  classical
  have hdisj : Disjoint d.support (ind T).support := by
    rw [support_ind, Finset.disjoint_left]
    intro j hj hjT
    have := hd j hj; have := hT j hjT; omega
  unfold maxV
  rw [Finsupp.support_add_eq hdisj, support_ind]
  apply le_antisymm
  · rw [fold_max_le_iff]
    obtain ⟨j0, hj0⟩ := hTn
    have hp0 : 0 ≤ S.p j0 := (S.one_lt j0).le.trans' (by norm_num)
    have hT0 : S.p j0 ≤ T.fold max 0 S.p := (Finset.le_fold_max _).mpr (Or.inr ⟨j0, hj0, le_rfl⟩)
    refine ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun j hj => ?_⟩
    rcases Finset.mem_union.mp hj with h | h
    · have h1 := hsmall j (hd j h)
      have h2 := hlarge j0 (hT j0 hj0)
      linarith
    · exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, h, le_rfl⟩)
  · rw [fold_max_le_iff]
    refine ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun j hj => ?_⟩
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_union_right _ hj, le_rfl⟩)

lemma smallPart_add_ind {J1 : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < J1) {T : Finset ℕ}
    (hT : ∀ j ∈ T, J1 ≤ j) : smallPart J1 (d + ind T) = d := by
  classical
  ext j
  unfold smallPart
  rw [Finsupp.filter_apply]
  split_ifs with h
  · rw [Finsupp.add_apply, ind_apply, if_neg (fun hj => by have := hT j hj; omega), add_zero]
  · rw [Finsupp.notMem_support_iff.mp (fun hj => h (hd j hj))]

lemma largePart_add_ind {J1 : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < J1) {T : Finset ℕ}
    (hT : ∀ j ∈ T, J1 ≤ j) : largePart J1 (d + ind T) = ind T := by
  classical
  ext j
  unfold largePart
  rw [Finsupp.filter_apply]
  by_cases h : j < J1
  · rw [if_neg (not_not.mpr h), ind_apply, if_neg (fun hj => by have := hT j hj; omega)]
  · rw [if_pos h, Finsupp.add_apply, Finsupp.notMem_support_iff.mp (fun hj => h (hd j hj)),
      zero_add]

/-- A squarefree large part is `ind` of its support. -/
lemma largePart_eq_ind {J1 : ℕ} {e : ℕ →₀ ℕ} (hsq : ∀ j, J1 ≤ j → e j ≤ 1) :
    largePart J1 e = ind (largePart J1 e).support := by
  classical
  ext j
  rw [ind_apply]
  by_cases hj : j ∈ (largePart J1 e).support
  · rw [if_pos hj]
    have h1 := Finsupp.mem_support_iff.mp hj
    unfold largePart at h1 ⊢
    rw [Finsupp.filter_apply] at h1 ⊢
    split_ifs at h1 ⊢ with h
    all_goals first | exact absurd rfl h1 | (have := hsq j (by omega); omega)
  · rw [if_neg hj]
    exact Finsupp.notMem_support_iff.mp hj

end BaseRange.S3
