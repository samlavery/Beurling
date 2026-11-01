module

public import Mathlib

/-!
# Theorem A.10 (Staged Volume Lemma): the stage identity and the inequality (B1)

The structural (linear-algebra) facts of Theorem A.10 are in `BSCert/SVLFacts.lean` and
`BSCert/StageRows.lean` (Lemma A.8). This file proves the remaining algebraic statements:

* `RankFull.svl_identity` : **Theorem A.10(i), identity (A.svl-identity)**: if
  `n_y = c_y^{(≤t)} ∏_{j ∈ P≤t} q_j^{E_yj}` for every `y ∈ R≤t`, then
  `∏_{P≤t} q_j / ∏_{R≤t} n_y = W_t^cov ∏_{y ∈ R≤t \ C} 1/n_y ∏_{P≤t} q_j^{1 - s_j^cov}`,
  `W_t^cov = ∏_{y ∈ C ∩ R≤t} 1/c_y^{(≤t)}`, `s_j^cov = ∑_{y ∈ C ∩ R≤t} E_yj`;
* `RankFull.svl_det_ge_one` : a non-zero integer determinant has `|det| ≥ 1`, so the Jacobian
  integrand is at most the right side of the identity;
* `RankFull.cap_replace` : the replacement `q_j^{1-s} ≤ τ_j^{1-s}` for `s ≥ 1`, `q_j ≥ τ_j > 0`
  (proof of A.10(ii), by the caps of Lemma A.5);
* `RankFull.svl_B1` : **inequality (B1)** of A.10(iii): on `Proj_t`, removing the summed primes
  (each `≥ X₀⁻ > 1`) and replacing the earlier pivots by `τ_j` only lowers `n_y`.
-/

@[expose] public section

open Finset

namespace RankFull

/-- **Theorem A.10(i), the identity (A.svl-identity).** Rows `Rt = R≤t`, pivot columns `Pt = P≤t`,
cover rows `C`; `n_y = c_y ∏_{j ∈ Pt} q_j^{E_yj}` for `y ∈ Rt`, all `q_j, c_y > 0`. -/
theorem svl_identity {ρ κ : Type*} [DecidableEq ρ] (Rt C : Finset ρ) (Pt : Finset κ)
    (E : ρ → κ → ℕ) (q : κ → ℝ) (c n : ρ → ℝ) (hq : ∀ j ∈ Pt, 0 < q j) (hc : ∀ y ∈ Rt, 0 < c y)
    (hn : ∀ y ∈ Rt, n y = c y * ∏ j ∈ Pt, q j ^ E y j) :
    (∏ j ∈ Pt, q j) / ∏ y ∈ Rt, n y =
      (∏ y ∈ Rt ∩ C, (c y)⁻¹) * (∏ y ∈ Rt \ C, (n y)⁻¹) *
        ∏ j ∈ Pt, q j ^ (1 - ((∑ y ∈ Rt ∩ C, E y j : ℕ) : ℤ)) := by
  have hsplit : ∏ y ∈ Rt, n y = (∏ y ∈ Rt ∩ C, n y) * ∏ y ∈ Rt \ C, n y := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter Rt C).symm, Finset.union_comm,
      Finset.sdiff_union_inter]
  have hcov : ∏ y ∈ Rt ∩ C, n y =
      (∏ y ∈ Rt ∩ C, c y) * ∏ j ∈ Pt, q j ^ (∑ y ∈ Rt ∩ C, E y j) := by
    rw [Finset.prod_congr rfl fun y hy => hn y (Finset.mem_inter.mp hy).1,
      Finset.prod_mul_distrib, Finset.prod_comm]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Finset.prod_pow_eq_pow_sum _ _ _
  have hq0 : ∀ j ∈ Pt, q j ≠ 0 := fun j hj => (hq j hj).ne'
  have hzp : ∀ j ∈ Pt, q j ^ (1 - ((∑ y ∈ Rt ∩ C, E y j : ℕ) : ℤ)) *
      q j ^ (∑ y ∈ Rt ∩ C, E y j) = q j := by
    intro j hj
    rw [← zpow_natCast, ← zpow_add₀ (hq0 j hj)]
    simp
  have hnR : ∀ y ∈ Rt, n y ≠ 0 := fun y hy => by
    rw [hn y hy]
    exact mul_ne_zero (hc y hy).ne' (Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ (hq0 j hj))
  have hc0 : ∀ y ∈ Rt ∩ C, c y ≠ 0 := fun y hy => (hc y (Finset.mem_inter.mp hy).1).ne'
  have hQ : ∏ j ∈ Pt, q j = (∏ j ∈ Pt, q j ^ (1 - ((∑ y ∈ Rt ∩ C, E y j : ℕ) : ℤ))) *
      ∏ j ∈ Pt, q j ^ (∑ y ∈ Rt ∩ C, E y j) := by
    rw [← Finset.prod_mul_distrib]; exact (Finset.prod_congr rfl hzp).symm
  have hRC : ∏ y ∈ Rt \ C, n y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y hy =>
    hnR y (Finset.mem_sdiff.mp hy).1
  have hCc : ∏ y ∈ Rt ∩ C, c y ≠ 0 := Finset.prod_ne_zero_iff.mpr hc0
  have hpow : ∏ j ∈ Pt, q j ^ (∑ y ∈ Rt ∩ C, E y j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hq0 j hj)
  rw [hsplit, hcov, hQ, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  field_simp

/-- A non-zero integer has absolute value `≥ 1` (Theorem A.10(i): `|det E_{R≤t,P≤t}| ≥ 1`). -/
theorem svl_det_ge_one {d : ℤ} (hd : d ≠ 0) : (1 : ℝ) ≤ |(d : ℝ)| := by
  have : 1 ≤ |d| := Int.one_le_abs hd
  exact_mod_cast this

/-- The cap replacement `q^{1-s} ≤ τ^{1-s}` for `s ≥ 1` and `q ≥ τ > 0`
(proof of Theorem A.10(ii)). -/
theorem cap_replace {q τ : ℝ} (hτ : 0 < τ) (hqτ : τ ≤ q) {s : ℕ} (hs : 1 ≤ s) :
    q ^ (1 - (s : ℤ)) ≤ τ ^ (1 - (s : ℤ)) := by
  have h : (1 - (s : ℤ)) = -((s - 1 : ℕ) : ℤ) := by omega
  rw [h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hqτ _)

/-- **Inequality (B1)** of Theorem A.10(iii). If `n_y = c^{noF} · f · ∏_{P_{t'}} q_j^{E_yj}
∏_{P_{<t'}} q_j^{E_yj}` with the product `f ≥ 1` of the summed primes of `F≤t` in `y` and
`q_j ≥ τ_j > 0` for the earlier pivots, then
`n_y ≥ c^{noF} ∏_{P_{t'}} q_j^{E_yj} ∏_{P_{<t'}} τ_j^{E_yj}`. -/
theorem svl_B1 {κ : Type*} (Pcur Pearly : Finset κ) (E : κ → ℕ) (q τ : κ → ℝ) {cnoF f ny : ℝ}
    (hc : 0 ≤ cnoF) (hf : 1 ≤ f) (hq0 : ∀ j ∈ Pcur, 0 ≤ q j) (hτ : ∀ j ∈ Pearly, 0 ≤ τ j)
    (hqτ : ∀ j ∈ Pearly, τ j ≤ q j)
    (hny : ny = cnoF * f * (∏ j ∈ Pcur, q j ^ E j) * ∏ j ∈ Pearly, q j ^ E j) :
    cnoF * (∏ j ∈ Pcur, q j ^ E j) * ∏ j ∈ Pearly, τ j ^ E j ≤ ny := by
  rw [hny]
  have h1 : ∏ j ∈ Pearly, τ j ^ E j ≤ ∏ j ∈ Pearly, q j ^ E j :=
    Finset.prod_le_prod₀ (fun j hj => pow_nonneg (hτ j hj) _)
      fun j hj => pow_le_pow_left₀ (hτ j hj) (hqτ j hj) _
  have h2 : 0 ≤ ∏ j ∈ Pcur, q j ^ E j := Finset.prod_nonneg fun j hj => pow_nonneg (hq0 j hj) _
  have h3 : 0 ≤ ∏ j ∈ Pearly, τ j ^ E j := Finset.prod_nonneg fun j hj => pow_nonneg (hτ j hj) _
  calc cnoF * (∏ j ∈ Pcur, q j ^ E j) * ∏ j ∈ Pearly, τ j ^ E j
      ≤ cnoF * f * (∏ j ∈ Pcur, q j ^ E j) * ∏ j ∈ Pearly, τ j ^ E j := by
        gcongr; nlinarith
    _ ≤ cnoF * f * (∏ j ∈ Pcur, q j ^ E j) * ∏ j ∈ Pearly, q j ^ E j := by
        gcongr

end RankFull
