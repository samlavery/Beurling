module

public import RequestProject.Beurling.RankFull.DickmanRows

/-!
# Lemma 6.22(e): the joint Rankin bound at exponent `3/4`

`admGen π k₁ K X₀ τl Y` is the set of (s4) data of a row of `R` of degree in `[k₁, K]`: its
monomial `v` in the `π` labels (label values `τl`) and its `X₀`-smooth tail `d`, with
`M_v(τ) d ≤ Y`. (`admGen π 1 K = admDick π K`, and `admGen ⊆ admHigh`.)

* `RankFull.card_admGen_le_rankin` : **Lemma 6.22(e)**, the Rankin step:
  `#admGen ≤ Y^{3/4} ∏_{j<π} (1 - τ_j^{-3/4})^{-1} ∏_{p<X₀} (1 - p^{-3/4})^{-1}`.
* `RankFull.log_rankinConst_34_le` : `log ∏_{p<X₀} (1 - p^{-3/4})^{-1} ≤
  1.42 (2/log 2 + 0.38 + log Λ + (4X₀^{1/4}/Λ)(1 + 8/Λ)) + 0.77`. (The paper has
  `log Λ + 2 + 5.2 X₀^{1/4}/Λ`, from Rosser–Schoenfeld; we use the certified `ψ(x) ≤ 1.42x`, as in
  `SmoothTailsCert.lean`. This changes the constants of (e), not its use.)
* `RankFull.sum_rpow_34_le` : `∑_{n=1}^{N} n^{-3/4} ≤ 4 N^{1/4}`.
* `RankFull.T2_weight` : the bound used in Step 4 (T2) of Theorem 6.23: for `ℓ ≥ 0.3Λ`
  (`L ≥ X₀^{0.3}`), `π ≤ L²` and label values `τ_j ≥ max(3, (j+1)/2)`,
  `#admGen ≤ z e^{-0.24 L}`, i.e. `log(1/w_y) ≥ 0.24 L`.
-/

@[expose] public section

open Finset

namespace RankFull

/-- The (s4) data of a row of degree in `[k₁, K]` with `X₀`-smooth tail. -/
noncomputable def admGen (π k₁ K X₀ : ℕ) (τl : Fin π → ℝ) (Y : ℝ) :
    Finset ((Fin π → ℕ) × ℕ) := by
  classical exact (((Icc k₁ K).biUnion (Finset.Nat.antidiagonalTuple π)) ×ˢ
    Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter fun p => monoVal τl p.1 * p.2 ≤ Y

lemma admGen_one (π K X₀ : ℕ) (τl : Fin π → ℝ) (Y : ℝ) :
    admGen π 1 K X₀ τl Y = admDick π K X₀ τl Y := rfl

lemma admGen_subset_admHigh (π k₁ K X₀ : ℕ) (τl : Fin π → ℝ) (Y : ℝ) :
    admGen π k₁ K X₀ τl Y ⊆ admHigh π k₁ K τl Y := by
  classical
  intro p hp
  unfold admGen at hp
  unfold admHigh
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨hv, hd⟩ := Finset.mem_product.mp hp1
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, ?_⟩, hp2⟩
  rw [Nat.mem_smoothNumbersUpTo] at hd
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd.2.1, hd.1⟩

/-! ## `∑ n^{-3/4} ≤ 4 N^{1/4}` -/

lemma rpow_34_step {n : ℝ} (hn : 1 ≤ n) :
    n ^ (-(3 / 4 : ℝ)) ≤ 4 * (n ^ (1 / 4 : ℝ) - (n - 1) ^ (1 / 4 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  set a := n ^ (1 / 4 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn0 _
  have ha4 : a ^ 4 = n := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have ha1 : 1 ≤ a := by
    by_contra h; push_neg at h
    have : a ^ 4 < 1 := pow_lt_one₀ ha0.le h (by norm_num)
    linarith
  have hn34 : n ^ (-(3 / 4 : ℝ)) = (a ^ 3)⁻¹ := by
    rw [← ha4, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le,
      show ((4 : ℕ) : ℝ) * -(3 / 4) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha0.le,
      Real.rpow_natCast]
  set y := (a ^ 4)⁻¹ / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 4 := by
    rw [hy]; have : (a ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1); linarith
  set b := a * (1 - y) with hb
  have hb0 : 0 ≤ b := mul_nonneg ha0.le (by linarith)
  have hb4 : n - 1 ≤ b ^ 4 := by
    have hber := one_add_mul_le_pow (show (-2 : ℝ) ≤ -y by linarith) 4
    have e : b ^ 4 = a ^ 4 * (1 - y) ^ 4 := by rw [hb, mul_pow]
    rw [e, ← ha4]
    have : a ^ 4 * (1 + (4 : ℕ) * -y) = a ^ 4 - 1 := by
      rw [hy]; push_cast; field_simp; ring
    have h4 : a ^ 4 * (1 + (4 : ℕ) * -y) ≤ a ^ 4 * (1 - y) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [sub_eq_add_neg] using hber
    linarith
  have hroot : (n - 1) ^ (1 / 4 : ℝ) ≤ b := by
    have h1 : (n - 1) ^ (1 / 4 : ℝ) ≤ (b ^ 4) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hb4 (by norm_num)
    have h2 : (b ^ 4) ^ (1 / 4 : ℝ) = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num
    linarith
  have hab : 4 * (a - b) = (a ^ 3)⁻¹ := by
    rw [hb, hy]; field_simp; ring
  rw [hn34]; linarith

/-- `∑_{n=1}^{N} n^{-3/4} ≤ 4 N^{1/4}`. -/
theorem sum_rpow_34_le (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  have h : ∀ n ∈ range N, ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) ≤
      4 * ((((n + 1 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) - ((n : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
    intro n _
    have := rpow_34_step (n := (n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    push_cast; simpa using this
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun n => ((n : ℕ) : ℝ) ^ (1 / 4 : ℝ))]
  simp

/-! ## The Rankin step -/

lemma geom_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i ≤ (1 - x)⁻¹ := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h2 : 0 < 1 - x := by linarith
  rw [geom_sum_eq (by linarith : x ≠ 1)]
  have e : (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [e, inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ h2.le
  have : 0 ≤ x ^ n := pow_nonneg hx0 n
  linarith

lemma sum_smooth_rpow_le (X₀ N : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∑ d ∈ Nat.smoothNumbersUpTo N X₀, (d : ℝ) ^ (-θ) ≤ Rankin.rankinConst X₀ θ := by
  classical
  obtain ⟨-, hh⟩ := Rankin.hasSum_smooth_rpow X₀ hθ
  have hsub : ∀ d ∈ Nat.smoothNumbersUpTo N X₀, d ∈ X₀.smoothNumbers := fun d hd =>
    (Nat.mem_smoothNumbersUpTo.mp hd).2
  have e : ∑ d ∈ Nat.smoothNumbersUpTo N X₀, (d : ℝ) ^ (-θ) =
      ∑ d ∈ (Nat.smoothNumbersUpTo N X₀).subtype (· ∈ X₀.smoothNumbers), ((d : ℕ) : ℝ) ^ (-θ) := by
    exact (Finset.sum_subtype_of_mem (fun d : ℕ => (d : ℝ) ^ (-θ)) hsub).symm
  rw [e]
  exact sum_le_hasSum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hh

/-- **Lemma 6.22(e)**, the Rankin step at exponent `3/4`: for label values `τ_j > 1` and
`Y ≥ 0`, `#admGen ≤ Y^{3/4} ∏_j (1 - τ_j^{-3/4})^{-1} ∏_{p<X₀} (1 - p^{-3/4})^{-1}`. -/
theorem card_admGen_le_rankin {π k₁ K X₀ : ℕ} {Y : ℝ} (hY : 0 ≤ Y) {τl : Fin π → ℝ}
    (hτl : ∀ i, 1 < τl i) :
    ((admGen π k₁ K X₀ τl Y).card : ℝ) ≤
      Y ^ (3 / 4 : ℝ) * (∏ i, (1 - τl i ^ (-(3 / 4 : ℝ)))⁻¹) * Rankin.rankinConst X₀ (3 / 4) := by
  classical
  set V := (Icc k₁ K).biUnion (Finset.Nat.antidiagonalTuple π)
  set Sm := Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀
  set x : Fin π → ℝ := fun i => τl i ^ (-(3 / 4 : ℝ)) with hx
  have hτ0 : ∀ i, 0 < τl i := fun i => by linarith [hτl i]
  have hx0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos (hτ0 i) _).le
  have hx1 : ∀ i, x i < 1 := fun i =>
    Real.rpow_lt_one_of_one_lt_of_neg (hτl i) (by norm_num)
  have hM : ∀ v, 0 < monoVal τl v := fun v =>
    Finset.prod_pos fun i _ => pow_pos (hτ0 i) _
  have hMr : ∀ v : Fin π → ℕ, (monoVal τl v) ^ (-(3 / 4 : ℝ)) = ∏ i, x i ^ v i := by
    intro v
    unfold monoVal
    rw [← Real.finset_prod_rpow _ _ (fun i _ => pow_nonneg (hτ0 i).le _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (hτ0 i).le, ← Real.rpow_natCast,
      ← Real.rpow_mul (hτ0 i).le, mul_comm]
  -- each element counts at most `(Y/(M d))^{3/4}`
  have hpt : ∀ p ∈ admGen π k₁ K X₀ τl Y,
      (1 : ℝ) ≤ Y ^ (3 / 4 : ℝ) * ((monoVal τl p.1) ^ (-(3 / 4 : ℝ)) *
        ((p.2 : ℝ) ^ (-(3 / 4 : ℝ)))) := by
    intro p hp
    unfold admGen at hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have hd := (Nat.mem_smoothNumbersUpTo.mp (Finset.mem_product.mp hp1).2).2.1
    have hd0 : (0 : ℝ) < p.2 := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hMd : 0 < monoVal τl p.1 * p.2 := mul_pos (hM _) hd0
    rw [← Real.mul_rpow (hM _).le hd0.le, Real.rpow_neg hMd.le, ← div_eq_mul_inv,
      ← Real.div_rpow hY hMd.le]
    exact Real.one_le_rpow ((one_le_div hMd).mpr hp2) (by norm_num)
  have hsum1 : ((admGen π k₁ K X₀ τl Y).card : ℝ) ≤ ∑ p ∈ V ×ˢ Sm,
      Y ^ (3 / 4 : ℝ) * ((monoVal τl p.1) ^ (-(3 / 4 : ℝ)) * ((p.2 : ℝ) ^ (-(3 / 4 : ℝ)))) := by
    calc ((admGen π k₁ K X₀ τl Y).card : ℝ) = ∑ p ∈ admGen π k₁ K X₀ τl Y, (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ admGen π k₁ K X₀ τl Y,
            Y ^ (3 / 4 : ℝ) * ((monoVal τl p.1) ^ (-(3 / 4 : ℝ)) *
              ((p.2 : ℝ) ^ (-(3 / 4 : ℝ)))) := Finset.sum_le_sum hpt
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p _ _
          have := (hM p.1).le
          exact mul_nonneg (Real.rpow_nonneg hY _) (mul_nonneg (Real.rpow_nonneg this _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  -- the monomial sum
  have hVsum : ∑ v ∈ V, (monoVal τl v) ^ (-(3 / 4 : ℝ)) ≤ ∏ i, (1 - x i)⁻¹ := by
    simp_rw [hMr]
    have hsub : V ⊆ Fintype.piFinset fun _ : Fin π => range (K + 1) := by
      intro v hv
      obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
      rw [Fintype.mem_piFinset]
      intro i
      have hs := Finset.Nat.mem_antidiagonalTuple.mp hvk
      have : v i ≤ k := hs ▸ Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
    calc ∑ v ∈ V, ∏ i, x i ^ v i
        ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin π => range (K + 1)), ∏ i, x i ^ v i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
            Finset.prod_nonneg fun i _ => pow_nonneg (hx0 i) _
      _ = ∏ i, ∑ n ∈ range (K + 1), x i ^ n := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ i, (1 - x i)⁻¹ := Finset.prod_le_prod
          (fun i _ => Finset.sum_nonneg fun n _ => pow_nonneg (hx0 i) _)
          fun i _ => geom_partial_le (hx0 i) (hx1 i) _
  have hSmsum := sum_smooth_rpow_le X₀ ⌊Y⌋₊ (θ := 3 / 4) (by norm_num)
  calc ((admGen π k₁ K X₀ τl Y).card : ℝ)
      ≤ ∑ p ∈ V ×ˢ Sm, Y ^ (3 / 4 : ℝ) * ((monoVal τl p.1) ^ (-(3 / 4 : ℝ)) *
          ((p.2 : ℝ) ^ (-(3 / 4 : ℝ)))) := hsum1
    _ = Y ^ (3 / 4 : ℝ) * ((∑ v ∈ V, (monoVal τl v) ^ (-(3 / 4 : ℝ))) *
          ∑ d ∈ Sm, (d : ℝ) ^ (-(3 / 4 : ℝ))) := by
        rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
    _ ≤ Y ^ (3 / 4 : ℝ) * ((∏ i, (1 - x i)⁻¹) * Rankin.rankinConst X₀ (3 / 4)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hY _)
        apply mul_le_mul hVsum hSmsum (Finset.sum_nonneg fun d _ =>
          Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hx1 i])).le
    _ = _ := by rw [hx]; ring

/-! ## The numerics of Lemma 6.22(e) and Step 4 (T2) -/

/-- `log ∏_{p<X₀} (1 - p^{-3/4})^{-1} ≤ 1.42 (2/log 2 + 0.38 + log Λ + (e^{Λ/4}/(Λ/4))(1 + 8/Λ))
+ 0.77` for `Λ = log X₀ ≥ 44`. -/
theorem log_rankinConst_34_le {X₀ : ℕ} (hX₀ : 3 ≤ X₀) (hΛ : 44 ≤ Real.log X₀) :
    Real.log (Rankin.rankinConst X₀ (3 / 4)) ≤
      1.42 * (2 / Real.log 2 + 0.38 + Real.log (Real.log X₀) +
        Real.exp (Real.log X₀ / 4) / (Real.log X₀ / 4) * (1 + 8 / Real.log X₀)) + 0.77 := by
  have h1 := SmoothTails.log_rankinConst_le X₀ (σ := 3 / 4) (by norm_num)
  have h2 := SmoothTails.sum_rpow_primes_le hX₀ (η := 1 / 4) (by norm_num) (by norm_num)
  rw [show (-(1 - 1 / 4) : ℝ) = -(3 / 4) by norm_num] at h2
  have hx : (11 : ℝ) ≤ 1 / 4 * Real.log X₀ := by linarith
  have hEi := BSCert.EiFn.Ei_le_of_ge_11 hx
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog : 0 ≤ Real.log (1 / 4 * Real.log X₀) := Real.log_nonneg (by linarith)
  have hEin : BSCert.EiFn.Ein (1 / 4 * Real.log X₀) ≤ BSCert.EiFn.Ei (1 / 4 * Real.log X₀) := by
    unfold BSCert.EiFn.Ei; linarith
  have e : Real.exp (1 / 4 * Real.log X₀) / (1 / 4 * Real.log X₀) *
      (1 + 2 / (1 / 4 * Real.log X₀)) =
      Real.exp (Real.log X₀ / 4) / (Real.log X₀ / 4) * (1 + 8 / Real.log X₀) := by
    have : Real.log X₀ ≠ 0 := by linarith
    rw [show 1 / 4 * Real.log X₀ = Real.log X₀ / 4 by ring]; field_simp; ring
  rw [e] at hEi
  linarith

lemma two_rpow_34_le : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 :=
  calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

lemma three_rpow_neg34_le : (3 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 := by
  rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
  have h : ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra hlt
  push_neg at hlt
  have : ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) < (1 / 2)⁻¹ ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  rw [h] at this; norm_num at this

set_option maxHeartbeats 1000000 in
/-- **The weight bound of Step 4 (T2)** of Theorem 6.23 (from Lemma 6.22(e)): with
`Λ = log X₀ ≥ 10⁸`, `L ≥ e^{0.3Λ}`, `z = e^L`, `π ≤ L²` and label values
`τ_j ≥ max(3, (j+1)/2)`, `#admGen ≤ z e^{-0.24L}`. -/
theorem T2_weight {X₀ : ℕ} (hX₀ : 3 ≤ X₀) (hΛ : 10 ^ 8 ≤ Real.log X₀) {L : ℝ}
    (hL : Real.exp (0.3 * Real.log X₀) ≤ L) {π k₁ K : ℕ} (hπ : (π : ℝ) ≤ L ^ 2)
    {τl : Fin π → ℝ} (hτ3 : ∀ i, 3 ≤ τl i) (hτi : ∀ i : Fin π, (((i : ℕ) : ℝ) + 1) / 2 ≤ τl i) :
    ((admGen π k₁ K X₀ τl (2 * Real.exp L + 1)).card : ℝ) ≤
      Real.exp L * Real.exp (-0.24 * L) := by
  set Λ := Real.log X₀ with hΛdef
  set z := Real.exp L with hz
  have hΛ0 : 0 < Λ := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hτ1 : ∀ i, 1 < τl i := fun i => by linarith [hτ3 i]
  have hcard := card_admGen_le_rankin (k₁ := k₁) (K := K) (X₀ := X₀)
    (show (0 : ℝ) ≤ 2 * z + 1 by positivity) hτ1
  set x : Fin π → ℝ := fun i => τl i ^ (-(3 / 4 : ℝ)) with hx
  have hτ0 : ∀ i, 0 < τl i := fun i => by linarith [hτ3 i]
  have hx0 : ∀ i, 0 < x i := fun i => Real.rpow_pos_of_pos (hτ0 i) _
  have hxh : ∀ i, x i ≤ 1 / 2 := fun i => le_trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) (hτ3 i) (by norm_num)) three_rpow_neg34_le
  -- the label product
  have hxi : ∀ i : Fin π, x i ≤ 2 * (((i : ℕ) : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
    intro i
    have h1 : x i ≤ ((((i : ℕ) : ℝ) + 1) / 2) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hτi i) (by norm_num)
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_inv_eq_mul] at h1
    have := two_rpow_34_le
    have h0 : 0 ≤ (((i : ℕ) : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by positivity
    nlinarith
  have hP : Real.log (∏ i, (1 - x i)⁻¹) ≤ 16 * L ^ (1 / 2 : ℝ) := by
    rw [Real.log_prod (fun i _ => (inv_pos.mpr (by linarith [hxh i])).ne')]
    have hterm : ∀ i : Fin π, Real.log (1 - x i)⁻¹ ≤ 2 * x i := by
      intro i
      rw [Real.log_inv]
      have hpos : 0 < 1 - x i := by linarith [hxh i]
      have h := Real.one_sub_inv_le_log_of_pos hpos
      have h1 : (1 - x i)⁻¹ - 1 ≤ 2 * x i := by
        rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
        nlinarith [hxh i, hx0 i]
      linarith
    calc ∑ i, Real.log (1 - x i)⁻¹ ≤ ∑ i : Fin π, 2 * x i := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i : Fin π, 2 * (2 * (((i : ℕ) : ℝ) + 1) ^ (-(3 / 4 : ℝ))) :=
          Finset.sum_le_sum fun i _ => by linarith [hxi i]
      _ = 4 * ∑ n ∈ range π, ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
          rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun n => 2 * (2 * ((n : ℝ) + 1) ^
            (-(3 / 4 : ℝ))))]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ 4 * (4 * (π : ℝ) ^ (1 / 4 : ℝ)) := by
          gcongr; exact sum_rpow_34_le π
      _ ≤ 16 * L ^ (1 / 2 : ℝ) := by
          have : (π : ℝ) ^ (1 / 4 : ℝ) ≤ (L ^ 2) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hπ (by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le] at this
          norm_num at this ⊢
          linarith
  -- the rigid product
  have hR := log_rankinConst_34_le hX₀ (by linarith)
  rw [← hΛdef] at hR
  have hl2 : 2 / Real.log 2 ≤ 2.886 := by
    have := Real.log_two_gt_d9
    rw [div_le_iff₀ (by linarith)]; linarith
  have hlogΛ : Real.log Λ ≤ Λ := by
    have := Real.log_le_sub_one_of_pos hΛ0; linarith
  -- sizes
  have he15 : 10000 ≤ Real.exp (0.15 * Λ) := by
    have := Real.add_one_le_exp (0.15 * Λ); linarith
  have he05 : 10000 ≤ Real.exp (0.05 * Λ) := by
    have := Real.add_one_le_exp (0.05 * Λ); linarith
  have hsqrt : 16 * L ^ (1 / 2 : ℝ) ≤ 0.002 * L := by
    have hsq : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    have hh : Real.exp (0.15 * Λ) ≤ L ^ (1 / 2 : ℝ) := by
      have : Real.exp (0.15 * Λ) = Real.exp (0.3 * Λ) ^ (1 / 2 : ℝ) := by
        rw [← Real.exp_mul]; ring_nf
      rw [this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hL (by norm_num)
    have hp : 0 < L ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hL0 _
    nlinarith
  have hEi : Real.exp (Λ / 4) / (Λ / 4) * (1 + 8 / Λ) ≤ 0.0001 * L := by
    have h8 : 8 / Λ ≤ 1 := by rw [div_le_one hΛ0]; linarith
    have h1 : Real.exp (Λ / 4) / (Λ / 4) * (1 + 8 / Λ) ≤ Real.exp (Λ / 4) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := Real.exp_pos (Λ / 4)
      nlinarith
    have h2 : Real.exp (Λ / 4) * Real.exp (0.05 * Λ) = Real.exp (0.3 * Λ) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (Λ / 4)]
  have hsmall : 1.42 * (2.886 + 0.38 + Λ) + 0.77 + 1.2 ≤ 0.004 * L := by
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 0.3 * Λ by positivity)
    nlinarith
  -- assemble
  have hY : (2 * z + 1) ^ (3 / 4 : ℝ) ≤ 3 * Real.exp (0.75 * L) := by
    have hz1 : 1 ≤ z := Real.one_le_exp hL0.le
    have h1 : (2 * z + 1) ^ (3 / 4 : ℝ) ≤ (3 * z) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity), hz, ← Real.exp_mul] at h1
    have h3 : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    calc (2 * z + 1) ^ (3 / 4 : ℝ) ≤ 3 ^ (3 / 4 : ℝ) * Real.exp (L * (3 / 4)) := h1
      _ ≤ 3 * Real.exp (0.75 * L) := by
          rw [show L * (3 / 4) = 0.75 * L by ring]
          exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have hPpos : 0 < ∏ i, (1 - x i)⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.mpr (by linarith [hxh i])
  have hRpos : 0 < Rankin.rankinConst X₀ (3 / 4) := by
    unfold Rankin.rankinConst
    refine Finset.prod_pos fun p hp => inv_pos.mpr ?_
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by norm_num)
    linarith
  have hPle : ∏ i, (1 - x i)⁻¹ ≤ Real.exp (16 * L ^ (1 / 2 : ℝ)) := by
    rw [← Real.exp_log hPpos]; exact Real.exp_le_exp.mpr hP
  have hRle : Rankin.rankinConst X₀ (3 / 4) ≤
      Real.exp (1.42 * (2.886 + 0.38 + Λ) + 0.77 + 1.42 * (0.0001 * L)) := by
    rw [← Real.exp_log hRpos]; apply Real.exp_le_exp.mpr; nlinarith
  calc ((admGen π k₁ K X₀ τl (2 * z + 1)).card : ℝ)
      ≤ (2 * z + 1) ^ (3 / 4 : ℝ) * (∏ i, (1 - x i)⁻¹) * Rankin.rankinConst X₀ (3 / 4) := hcard
    _ ≤ 3 * Real.exp (0.75 * L) * Real.exp (16 * L ^ (1 / 2 : ℝ)) *
          Real.exp (1.42 * (2.886 + 0.38 + Λ) + 0.77 + 1.42 * (0.0001 * L)) := by
        apply mul_le_mul (mul_le_mul hY hPle hPpos.le (by positivity)) hRle hRpos.le
          (by positivity)
    _ = Real.exp (Real.log 3 + 0.75 * L + 16 * L ^ (1 / 2 : ℝ) +
          (1.42 * (2.886 + 0.38 + Λ) + 0.77 + 1.42 * (0.0001 * L))) := by
        rw [Real.exp_add (Real.log 3 + 0.75 * L + 16 * L ^ (1 / 2 : ℝ)),
          Real.exp_add (Real.log 3 + 0.75 * L), Real.exp_add (Real.log 3),
          Real.exp_log (by norm_num)]
    _ ≤ Real.exp (L + -0.24 * L) := by
        apply Real.exp_le_exp.mpr
        have : Real.log 3 ≤ 1.2 := by
          have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
          rw [Real.log_div (by norm_num) (by norm_num)] at this
          have := Real.log_two_lt_d9; linarith
        nlinarith
    _ = z * Real.exp (-0.24 * L) := by rw [Real.exp_add]

end RankFull
