module

public import RequestProject.Beurling.RankFull.StageC

/-!
# Lemma A.6 (S3)(a) for a cover: the block bound with the chain rows of the cover

As `BlockModel.lean`, but with the weight `∏_g q_g^{-a^C_g}` of the rows of the cover only
(`a^C_g = ∑_{y ∈ C} w_{yg}`), the admissible columns depending on the slot and on the set of slots
of the block (the entries of the rows outside the cover are fixed by (s4)), and the chain rows
`R ⊆ C`: every admissible column is determined by, and non-zero on, its entries in `R`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace RankFull

variable {N : ℕ}

theorem fiber_leC {K : ℕ} (D : ℕ) (R Cd : Finset (Fin K)) (hRC : R ⊆ Cd)
    (Col : Fin N → Set (Fin K → ℕ))
    (hinj : ∀ g, ∀ w ∈ Col g, ∀ w' ∈ Col g, (∀ y ∈ R, w y = w' y) → w = w')
    (hnz : ∀ g, ∀ w ∈ Col g, ∃ y ∈ R, w y ≠ 0)
    (S : Finset (Fin N)) (q : Fin N → ℝ) (hq : ∀ g ∈ S, 1 < q g) :
    ∑ W ∈ (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col g),
        ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) ≤ ∏ g ∈ S, (((1 - (q g)⁻¹)⁻¹) ^ R.card - 1) := by
  set φ : (Fin K → Fin N → ℕ) → (Fin N → Fin K → ℕ) := fun W g =>
    if g ∈ S then (fun y => if y ∈ R then W y g else 0) else 0 with hφ
  set hfun : Fin N → (Fin K → ℕ) → ℝ := fun g v =>
    if g ∈ S then (q g)⁻¹ ^ (∑ y, v y) else 1 with hh
  set TS : Finset (Fin N → Fin K → ℕ) := Fintype.piFinset fun g =>
    if g ∈ S then (VR R D).filter (· ≠ 0) else {0} with hTS
  set fib := (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col g) with hfib
  have hqinv : ∀ g ∈ S, 0 < (q g)⁻¹ ∧ (q g)⁻¹ ≤ 1 := fun g hg =>
    ⟨inv_pos.mpr (by linarith [hq g hg]), inv_le_one_of_one_le₀ (hq g hg).le⟩
  -- (i) the weight is at most the stage-row weight
  have hw : ∀ W ∈ fib, ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) ≤ ∏ g, hfun g (φ W g) := by
    intro W hW
    obtain ⟨-, hsupp, -⟩ := Finset.mem_filter.mp hW
    refine Finset.prod_le_prod₀ (fun g _ => ?_) (fun g _ => ?_)
    · by_cases hg : g ∈ S
      · exact pow_nonneg (hqinv g hg).1.le _
      · have : ∀ y, W y g = 0 := by
          intro y; by_contra h
          exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        simp [this]
    · by_cases hg : g ∈ S
      · simp only [hh, hφ, if_pos hg]
        refine pow_le_pow_of_le_one (hqinv g hg).1.le (hqinv g hg).2 ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter]
        exact Finset.sum_le_sum_of_subset hRC
      · have : ∀ y, W y g = 0 := by
          intro y; by_contra h
          exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        simp [hh, hg, this]
  -- (ii) the map to the stage-row entries is injective, into `TS`
  have hmaps : ∀ W ∈ fib, φ W ∈ TS := by
    intro W hW
    obtain ⟨hWs, hsupp, hcol⟩ := Finset.mem_filter.mp hW
    rw [hTS, Fintype.mem_piFinset]
    intro g
    by_cases hg : g ∈ S
    · simp only [hφ, if_pos hg]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [VR, Fintype.mem_piFinset]
        intro y
        split_ifs with hy
        · have := Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hWs y) g
          exact this
        · simp
      · intro h0'
        obtain ⟨y, hyR, hy⟩ := hnz g (colW W g) (hcol g hg)
        have := congrFun h0' y
        simp only [hyR, if_true, Pi.zero_apply] at this
        exact hy this
    · simp [hφ, hg]
  have hinjφ : Set.InjOn φ fib := by
    intro W hW W' hW' h
    obtain ⟨-, hsupp, hcol⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hW)
    obtain ⟨-, hsupp', hcol'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hW')
    funext y g
    by_cases hg : g ∈ S
    · have := hinj g (colW W g) (hcol g hg) (colW W' g) (hcol' g hg) (fun y' hy' => by
        have := congrFun (congrFun h g) y'
        simpa [colW, hφ, hg, hy'] using this)
      exact congrFun this y
    · have h1 : W y g = 0 := by
        by_contra h1; exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h1⟩)
      have h2 : W' y g = 0 := by
        by_contra h2; exact hg (hsupp' ▸ mem_suppW.mpr ⟨y, h2⟩)
      rw [h1, h2]
  calc ∑ W ∈ fib, ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g)
      ≤ ∑ W ∈ fib, ∏ g, hfun g (φ W g) := Finset.sum_le_sum hw
    _ ≤ ∑ V ∈ TS, ∏ g, hfun g (V g) := by
        refine sum_comp_le_of_injOn fib TS φ hmaps hinjφ (fun V => ∏ g, hfun g (V g))
          fun V _ => Finset.prod_nonneg fun g _ => ?_
        simp only [hh]; split_ifs with hg
        · exact pow_nonneg (hqinv g hg).1.le _
        · exact zero_le_one
    _ = ∏ g, ∑ v ∈ (if g ∈ S then (VR R D).filter (· ≠ 0) else {0}), hfun g v := by
        rw [hTS, Finset.prod_univ_sum]
    _ = ∏ g ∈ S, ∑ v ∈ (VR R D).filter (· ≠ 0), (q g)⁻¹ ^ (∑ y, v y) := by
        rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ S)]
        have h2 : ∏ g ∈ univ.filter (fun g => ¬ g ∈ S),
            ∑ v ∈ (if g ∈ S then (VR R D).filter (· ≠ 0) else {0}), hfun g v = 1 :=
          Finset.prod_eq_one fun g hg => by
            rw [if_neg (Finset.mem_filter.mp hg).2]; simp [hh, (Finset.mem_filter.mp hg).2]
        rw [h2, mul_one]
        have hfilt : univ.filter (· ∈ S) = S := by ext; simp
        rw [hfilt]
        refine Finset.prod_congr rfl fun g hg => ?_
        rw [if_pos hg]
        exact Finset.sum_congr rfl fun v _ => by simp [hh, hg]
    _ ≤ ∏ g ∈ S, (((1 - (q g)⁻¹)⁻¹) ^ R.card - 1) := by
        refine Finset.prod_le_prod₀ (fun g hg => Finset.sum_nonneg fun v _ =>
          pow_nonneg (hqinv g hg).1.le _) fun g hg => ?_
        exact geomR_le R D (hqinv g hg).1.le (inv_lt_one_of_one_lt₀ (hq g hg))


/-- An admissible non-empty block content for a cover: decided slots `≥ b`, the column of each slot
admissible for the set of slots of the content. -/
def BlockOKC {K : ℕ} (ok : Fin N → Prop) (b : ℕ) (Col : Finset (Fin N) → Fin N → Set (Fin K → ℕ))
    (W : Fin K → Fin N → ℕ) : Prop :=
  (suppW W).Nonempty ∧ ∀ g ∈ suppW W, ok g ∧ b ≤ (g : ℕ) ∧ colW W g ∈ Col (suppW W) g

/-- **Lemma A.6 (S3)(a) for a cover** (chain rows `R ⊆ C`). -/
theorem blockSum_leC [NeZero N] {K : ℕ} (D : ℕ) (R Cd : Finset (Fin K)) (hRC : R ⊆ Cd)
    (Col : Finset (Fin N) → Fin N → Set (Fin K → ℕ))
    (hinj : ∀ S g, ∀ w ∈ Col S g, ∀ w' ∈ Col S g, (∀ y ∈ R, w y = w' y) → w = w')
    (hnz : ∀ S g, ∀ w ∈ Col S g, ∃ y ∈ R, w y ≠ 0)
    (ok : Fin N → Prop) (q : Fin N → ℝ) (hq : ∀ g, ok g → 1 < q g) {Eu : ℝ} (hEu : 0 < Eu)
    (b smax : ℕ) (Gp : ℕ → Prop) {A : ℝ} (hS3 : ∀ u ≤ smax, Gp u → EuS ok q Eu u ≤ A)
    {m j : ℕ} (hK : R.card = m + j) {Gf : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ Gf y)
    (hGanti : AntitoneOn Gf (Set.Ioi 0)) :
    ∑ W ∈ Wset K N D, (if BlockOKC ok b Col W then
        chiB smax Gp (uW W) * (Gf (EuS ok q Eu (uW W)) / EuS ok q Eu (uW W) ^ m) *
          ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) else 0) ≤
      Gnext A R.card j Gf (EuS ok q Eu b) / EuS ok q Eu b ^ R.card := by
  set Dset := univ.filter fun g : Fin N => ok g ∧ b ≤ (g : ℕ) with hD
  set T := Dset.powerset.filter (·.Nonempty) with hT
  set F : (Fin K → Fin N → ℕ) → ℝ := fun W =>
    chiB smax Gp (uW W) * (Gf (EuS ok q Eu (uW W)) / EuS ok q Eu (uW W) ^ m) *
      ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) with hF
  have hΦ0 : ∀ u, 0 ≤ chiB smax Gp u * (Gf (EuS ok q Eu u) / EuS ok q Eu u ^ m) := by
    intro u
    have hE := EuS_pos hq hEu u
    refine mul_nonneg (by unfold chiB; split_ifs <;> norm_num)
      (div_nonneg (hG0 _ hE) (pow_nonneg hE.le _))
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (g := suppW) (t := T) (fun W hW => by
    obtain ⟨-, hne, hall⟩ := Finset.mem_filter.mp hW
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun g hg => ?_, hne⟩
    obtain ⟨h1, h2, -⟩ := hall g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)]
  have hfib : ∀ S ∈ T, ∑ W ∈ ((Wset K N D).filter (BlockOKC ok b Col)).filter
      (fun W => suppW W = S), F W ≤
      chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
        (∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1)) *
        (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
          EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m) := by
    intro S hS
    obtain ⟨hSD, hne⟩ := Finset.mem_filter.mp hS
    have hSq : ∀ g ∈ S, 1 < q g := fun g hg =>
      hq g (Finset.mem_filter.mp (Finset.mem_powerset.mp hSD hg)).2.1
    have hsub : ((Wset K N D).filter (BlockOKC ok b Col)).filter (fun W => suppW W = S) ⊆
        (Wset K N D).filter (fun W => suppW W = S ∧ ∀ g ∈ S, colW W g ∈ Col S g) := by
      intro W hW
      simp only [Finset.mem_filter] at hW ⊢
      obtain ⟨⟨hWs, -, hall⟩, hsupp⟩ := hW
      exact ⟨hWs, hsupp, fun g hg => hsupp ▸ (hall g (hsupp ▸ hg)).2.2⟩
    have hval : ∀ W ∈ ((Wset K N D).filter (BlockOKC ok b Col)).filter (fun W => suppW W = S),
        F W = (chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
          (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
            EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m)) * ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) := by
      intro W hW
      have hsupp := (Finset.mem_filter.mp hW).2
      simp only [hF, uW, hsupp]
    rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
    have hfl := fiber_leC D R Cd hRC (Col S) (hinj S) (hnz S) S q hSq
    have hle : ∑ W ∈ ((Wset K N D).filter (BlockOKC ok b Col)).filter (fun W => suppW W = S),
        ∏ g, (q g)⁻¹ ^ (∑ y ∈ Cd, W y g) ≤ ∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun W hW _ =>
        Finset.prod_nonneg fun g _ => ?_) hfl
      by_cases hg : g ∈ S
      · exact pow_nonneg (inv_nonneg.mpr (by linarith [hSq g hg])) _
      · have hsupp := (Finset.mem_filter.mp hW).2.1
        have : ∑ y ∈ Cd, W y g = 0 := Finset.sum_eq_zero fun y _ => by
          by_contra h; exact hg (hsupp ▸ mem_suppW.mpr ⟨y, h⟩)
        rw [this, pow_zero]; exact zero_le_one
    calc _ ≤ (chiB smax Gp (S.sup fun g => (g : ℕ) + 1) *
          (Gf (EuS ok q Eu (S.sup fun g => (g : ℕ) + 1)) /
            EuS ok q Eu (S.sup fun g => (g : ℕ) + 1) ^ m)) *
          ∏ g ∈ S, ((1 - (q g)⁻¹)⁻¹ ^ R.card - 1) :=
          mul_le_mul_of_nonneg_left hle (hΦ0 _)
      _ = _ := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  exact blockSets_le ok q hq hEu b smax Gp hS3 hK hG0 hGanti

end RankFull
