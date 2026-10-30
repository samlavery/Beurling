module

public import RequestProject.Beurling.GenChebyshev

/-!
# Rankin's inequality for a Beurling system (used in Lemma 5.21(ii))

* `BeurlingSystem.sum_rpow_le_euler` : for `θ > 0` and a finite set `S` of elements whose primes
  all have index in `J`, `∑_{e ∈ S} e^{-θ} ≤ ∏_{j ∈ J} (1 - p_j^{-θ})⁻¹`;
* `LemS.neg_log_one_sub_le` : `-log(1 - x) ≤ x + x²/(2(1-x))` for `0 ≤ x < 1`;
* `LemS.prod_inv_le_exp` : `∏ (1 - x_j)⁻¹ ≤ exp ∑ (x_j + x_j²/(2(1 - x_j)))`.
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable (P : BeurlingSystem)

lemma val_eq_single_mul_erase (e : ℕ →₀ ℕ) (j : ℕ) :
    P.val e = P.p j ^ e j * P.val (e.erase j) := by
  conv_lhs => rw [← Finsupp.single_add_erase j e]
  rw [P.val_add, P.val_single]

lemma val_rpow_neg (e : ℕ →₀ ℕ) (j : ℕ) (θ : ℝ) :
    P.val e ^ (-θ) = (P.p j ^ (-θ)) ^ e j * P.val (e.erase j) ^ (-θ) := by
  rw [P.val_eq_single_mul_erase e j,
    Real.mul_rpow (pow_pos (P.p_pos j) _).le (P.val_pos _).le,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (P.p_pos j).le,
    ← Real.rpow_mul (P.p_pos j).le, mul_comm (-θ)]

/-- **Rankin / Euler product inequality**: `∑_{e ∈ S} e^{-θ} ≤ ∏_{j ∈ J} (1 - p_j^{-θ})⁻¹` for
`θ > 0` and `S` a finite set of elements with all prime indices in `J`. -/
theorem sum_rpow_le_euler {θ : ℝ} (hθ : 0 < θ) (J : Finset ℕ) :
    ∀ S : Finset (ℕ →₀ ℕ), (∀ e ∈ S, e.support ⊆ J) →
      ∑ e ∈ S, P.val e ^ (-θ) ≤ ∏ j ∈ J, (1 - P.p j ^ (-θ))⁻¹ := by
  classical
  have hx : ∀ j, 0 ≤ P.p j ^ (-θ) ∧ P.p j ^ (-θ) < 1 := fun j =>
    ⟨by have := P.p_pos j; positivity,
      Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)⟩
  induction J using Finset.induction_on with
  | empty =>
    intro S hS
    have : S ⊆ {0} := by
      intro e he
      have := hS e he
      rw [Finset.subset_empty, Finsupp.support_eq_empty] at this
      simp [this]
    calc ∑ e ∈ S, P.val e ^ (-θ) ≤ ∑ e ∈ ({0} : Finset (ℕ →₀ ℕ)), P.val e ^ (-θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg this fun e _ _ => by
            have := P.val_pos e; positivity
      _ = 1 := by simp [BeurlingSystem.val]
      _ = ∏ j ∈ (∅ : Finset ℕ), (1 - P.p j ^ (-θ))⁻¹ := by simp
  | insert j J hj ih =>
    intro S hS
    set x := P.p j ^ (-θ)
    obtain ⟨hx0, hx1⟩ := hx j
    -- bound the exponents of `j`
    obtain ⟨M, hM⟩ : ∃ M, ∀ e ∈ S, e j < M :=
      ⟨(S.sup fun e => e j) + 1, fun e he =>
        Nat.lt_succ_of_le (Finset.le_sup (f := fun e => e j) he)⟩
    have hsplit : ∑ e ∈ S, P.val e ^ (-θ) =
        ∑ k ∈ Finset.range M, ∑ e ∈ S.filter (fun e => e j = k), P.val e ^ (-θ) := by
      exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.range M)
        (g := fun e : ℕ →₀ ℕ => e j) (fun e he => Finset.mem_range.mpr (hM e he))
        (fun e => P.val e ^ (-θ))).symm
    rw [hsplit]
    have hfib : ∀ k ∈ Finset.range M, ∑ e ∈ S.filter (fun e => e j = k), P.val e ^ (-θ) ≤
        x ^ k * ∏ i ∈ J, (1 - P.p i ^ (-θ))⁻¹ := by
      intro k _
      have e1 : ∑ e ∈ S.filter (fun e => e j = k), P.val e ^ (-θ) =
          x ^ k * ∑ e ∈ S.filter (fun e => e j = k), P.val (e.erase j) ^ (-θ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [P.val_rpow_neg e j θ, (Finset.mem_filter.mp he).2]
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx0 k)
      have hinj : Set.InjOn (fun e : ℕ →₀ ℕ => e.erase j)
          (S.filter (fun e => e j = k) : Set (ℕ →₀ ℕ)) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        have h1 := Finsupp.single_add_erase j a
        have h2 := Finsupp.single_add_erase j b
        simp only at hab
        rw [← h1, ← h2, hab, ha.2, hb.2]
      rw [← Finset.sum_image (f := fun e => P.val e ^ (-θ)) hinj]
      apply ih
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      intro i hi
      rw [Finsupp.support_erase, Finset.mem_erase] at hi
      have := hS a (Finset.mem_filter.mp ha).1 hi.2
      rw [Finset.mem_insert] at this
      rcases this with h | h
      · exact absurd h hi.1
      · exact h
    have hP0 : 0 ≤ ∏ i ∈ J, (1 - P.p i ^ (-θ))⁻¹ :=
      Finset.prod_nonneg fun i _ => by
        have := (hx i).2; exact inv_nonneg.mpr (by linarith)
    calc ∑ k ∈ Finset.range M, ∑ e ∈ S.filter (fun e => e j = k), P.val e ^ (-θ)
        ≤ ∑ k ∈ Finset.range M, x ^ k * ∏ i ∈ J, (1 - P.p i ^ (-θ))⁻¹ :=
          Finset.sum_le_sum hfib
      _ = (∑ k ∈ Finset.range M, x ^ k) * ∏ i ∈ J, (1 - P.p i ^ (-θ))⁻¹ := by
          rw [Finset.sum_mul]
      _ ≤ (1 - x)⁻¹ * ∏ i ∈ J, (1 - P.p i ^ (-θ))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hP0
          rw [geom_sum_eq hx1.ne]
          rw [show x ^ M - 1 = -(1 - x ^ M) by ring, show x - 1 = -(1 - x) by ring,
            neg_div_neg_eq, div_eq_mul_inv]
          have := pow_nonneg hx0 M
          have : 0 < (1 - x)⁻¹ := inv_pos.mpr (by linarith)
          nlinarith
      _ = ∏ i ∈ insert j J, (1 - P.p i ^ (-θ))⁻¹ := by rw [Finset.prod_insert hj]

end BeurlingSystem

namespace LemS

/-- `-log(1 - x) ≤ x + x²/(2(1-x))` for `0 ≤ x < 1`. -/
lemma neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  -- `φ(s) = s + s²/(2(1-s)) + log(1-s)` is non-decreasing on `[0, x]`, `φ(0) = 0`
  set φ : ℝ → ℝ := fun s => s + s ^ 2 / (2 * (1 - s)) + Real.log (1 - s)
  have hd : ∀ s ∈ Set.Icc 0 x, HasDerivAt φ (s ^ 2 / (2 * (1 - s) ^ 2)) s := by
    intro s hs
    have hs1 : 1 - s ≠ 0 := by linarith [hs.2]
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa [Pi.sub_def] using (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id' s)
    have h2 := ((hasDerivAt_id s).pow 2).div (h1.const_mul 2) (mul_ne_zero two_ne_zero hs1)
    have h3 := h1.log hs1
    have := ((hasDerivAt_id s).add h2).add h3
    convert! this using 1
    · simp only [id, Pi.pow_apply]
      field_simp
      ring
  have hmono : MonotoneOn φ (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]; positivity
  have := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  simp only [φ] at this
  norm_num at this
  linarith

/-- `∏ (1 - x_j)⁻¹ ≤ exp ∑ (x_j + x_j²/(2(1-x_j)))` for `0 ≤ x_j < 1`. -/
lemma prod_inv_le_exp (J : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ j ∈ J, 0 ≤ x j ∧ x j < 1) :
    ∏ j ∈ J, (1 - x j)⁻¹ ≤ Real.exp (∑ j ∈ J, (x j + x j ^ 2 / (2 * (1 - x j)))) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro j hj; have := (hx j hj).2; exact inv_nonneg.mpr (by linarith)
  · intro j hj
    obtain ⟨h0, h1⟩ := hx j hj
    have hl := neg_log_one_sub_le h0 h1
    calc (1 - x j)⁻¹ = Real.exp (-Real.log (1 - x j)) := by
          rw [Real.exp_neg, Real.exp_log (by linarith)]
      _ ≤ Real.exp (x j + x j ^ 2 / (2 * (1 - x j))) := Real.exp_le_exp.mpr hl

end LemS

end
