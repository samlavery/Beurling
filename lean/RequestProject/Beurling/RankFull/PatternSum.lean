module

public import Mathlib

/-!
# Lemma A.3 (pattern sum), first inequality

Lemma A.3 of Appendix A: summing over the invertible non-negative integer `k × k` matrices `E_P`
(columns in decision order), with `s_j = ∑_i E_{ij}` the `j`-th column sum and `τ_j > 1`,
`(1/k!) ∑_{E_P} ∏_j τ_j^{-(s_j - 1)} ≤ ∏_j (1 - 1/τ_j)^{-k}`.

The proof is the paper's: a non-zero Leibniz term `∏_j E_{σ(j), j} ≠ 0` gives a permutation `σ`
whose permutation matrix lies in the support of `E_P`; `E_P ↦ (σ, E_P - P_σ)` is injective, the
column sums of `X = E_P - P_σ` are `s_j - 1`, and the sum over all `X ∈ ℕ^{k×k}` factorises.

Sums are in `ℝ≥0∞` (all terms are non-negative; invertibility is over `ℚ`).

* `RankFull.tsum_fin_pi_prod` : `∑_{v : Fin n → β} ∏_i g_i(v_i) = ∏_i ∑_b g_i(b)`;
* `RankFull.pattern_sum` : **Lemma A.3**, first inequality.
-/

@[expose] public section

open Finset

namespace RankFull

/-- `∑_{v : Fin n → β} ∏_i g_i(v_i) = ∏_i ∑_b g_i(b)` in `ℝ≥0∞`. -/
lemma tsum_fin_pi_prod {β : Type*} : ∀ (n : ℕ) (g : Fin n → β → ENNReal),
    ∑' v : Fin n → β, ∏ i, g i (v i) = ∏ i, ∑' b, g i b
  | 0, g => by simp
  | n + 1, g => by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => β)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, tsum_fin_pi_prod n (fun i => g i.succ)]
    rw [ENNReal.tsum_mul_right]

/-- Every invertible matrix has a non-zero Leibniz term. -/
lemma exists_perm_support {k : ℕ} (E : Matrix (Fin k) (Fin k) ℕ)
    (hE : (E.map (Nat.cast : ℕ → ℚ)).det ≠ 0) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, E (σ j) j ≠ 0 := by
  rw [Matrix.det_apply] at hE
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
  refine ⟨σ, fun j hj => hσ ?_⟩
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), smul_zero]

/-- **Lemma A.3 (pattern sum)**, first inequality: for `τ_j > 1`,
`∑_{E_P invertible} ∏_j τ_j^{-(s_j - 1)} ≤ k! ∏_j (1 - 1/τ_j)^{-k}`. -/
theorem pattern_sum {k : ℕ} (τ : Fin k → ℝ) (hτ : ∀ j, 1 < τ j) :
    ∑' E : Matrix (Fin k) (Fin k) ℕ,
        {E : Matrix (Fin k) (Fin k) ℕ | (E.map (Nat.cast : ℕ → ℚ)).det ≠ 0}.indicator
          (fun E => ∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E i j) - 1))) E ≤
      k.factorial * ∏ j, ENNReal.ofReal ((1 - (τ j)⁻¹)⁻¹ ^ k) := by
  classical
  set S := {E : Matrix (Fin k) (Fin k) ℕ | (E.map (Nat.cast : ℕ → ℚ)).det ≠ 0}
  set x : Fin k → ENNReal := fun j => ENNReal.ofReal (τ j)⁻¹ with hx
  have hτ0 : ∀ j, 0 < (τ j)⁻¹ := fun j => inv_pos.mpr (by linarith [hτ j])
  have hτ1 : ∀ j, (τ j)⁻¹ < 1 := fun j => inv_lt_one_of_one_lt₀ (hτ j)
  -- the weight of a pair `(σ, X)`
  let F : Equiv.Perm (Fin k) × Matrix (Fin k) (Fin k) ℕ → ENNReal :=
    fun p => ∏ j, x j ^ (∑ i, p.2 i j)
  -- the injection
  let σE : S → Equiv.Perm (Fin k) := fun E => Classical.choose (exists_perm_support E.1 E.2)
  have hσE : ∀ E : S, ∀ j, E.1 (σE E j) j ≠ 0 :=
    fun E => Classical.choose_spec (exists_perm_support E.1 E.2)
  let φ : S → Equiv.Perm (Fin k) × Matrix (Fin k) (Fin k) ℕ :=
    fun E => (σE E, fun r c => E.1 r c - if r = σE E c then 1 else 0)
  have hdecomp : ∀ E : S, ∀ r c, E.1 r c = (φ E).2 r c + if r = (φ E).1 c then 1 else 0 := by
    intro E r c
    simp only [φ]
    split_ifs with h
    · have := hσE E c; rw [← h] at this; omega
    · simp
  have hφ : Function.Injective φ := by
    intro E E' h
    apply Subtype.ext
    funext r c
    rw [hdecomp E r c, hdecomp E' r c, h]
  have hcol : ∀ E : S, ∀ j, (∑ i, E.1 i j) - 1 = ∑ i, (φ E).2 i j := by
    intro E j
    have : ∑ i, E.1 i j = ∑ i, (φ E).2 i j + 1 := by
      simp_rw [hdecomp E _ j]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
      simp
    omega
  have hfE : ∀ E : S, ∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E.1 i j) - 1)) = F (φ E) := by
    intro E
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hcol E j, ENNReal.ofReal_pow (hτ0 j).le]
  -- the sum over all `X`
  have hX : ∑' X : Matrix (Fin k) (Fin k) ℕ, ∏ j, x j ^ (∑ i, X i j) =
      ∏ j, ENNReal.ofReal ((1 - (τ j)⁻¹)⁻¹ ^ k) := by
    have h1 : ∀ X : Matrix (Fin k) (Fin k) ℕ, ∏ j, x j ^ (∑ i, X i j) =
        ∏ i, ∏ j, x j ^ X i j := by
      intro X
      rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun j _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
    simp_rw [h1]
    have h2 : ∑' X : Matrix (Fin k) (Fin k) ℕ, ∏ i, ∏ j, x j ^ X i j =
        ∏ _i : Fin k, ∑' w : Fin k → ℕ, ∏ j, x j ^ w j :=
      tsum_fin_pi_prod (β := Fin k → ℕ) k (fun _ w => ∏ j, x j ^ w j)
    have h3 : ∑' w : Fin k → ℕ, ∏ j, x j ^ w j = ∏ j, ∑' n : ℕ, x j ^ n :=
      tsum_fin_pi_prod k (fun j (n : ℕ) => x j ^ n)
    rw [h2, h3]
    have hgeom : ∀ j, ∑' n : ℕ, x j ^ n = ENNReal.ofReal ((1 - (τ j)⁻¹)⁻¹) := by
      intro j
      rw [hx, ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (hτ0 j).le,
        ENNReal.ofReal_inv_of_pos (by linarith [hτ1 j])]
    simp_rw [hgeom]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (by linarith [hτ1 j]))]
  calc ∑' E, S.indicator (fun E => ∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E i j) - 1))) E
      = ∑' E : S, ∏ j, ENNReal.ofReal ((τ j)⁻¹ ^ ((∑ i, E.1 i j) - 1)) :=
        (_root_.tsum_subtype S _).symm
    _ = ∑' E : S, F (φ E) := tsum_congr hfE
    _ ≤ ∑' p, F p := ENNReal.tsum_comp_le_tsum_of_injective hφ F
    _ = ∑' σ : Equiv.Perm (Fin k), ∑' X : Matrix (Fin k) (Fin k) ℕ, ∏ j, x j ^ (∑ i, X i j) :=
        ENNReal.tsum_prod'
    _ = k.factorial * ∏ j, ENNReal.ofReal ((1 - (τ j)⁻¹)⁻¹ ^ k) := by
        simp_rw [hX]
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]

end RankFull
