module

public import RequestProject.Beurling.BaseFactor

/-!
# The divisor function squared over smooth numbers

For the fourth moment of `Z_∞(1+it)` (proof of Lemma 4.8(i)) we need
`∑_{n∈D} τ(n)²/n^σ = ∏_{p<X₀} (1 + p^{-σ})/(1 - p^{-σ})³` (`hasSum_tau_sq_smooth`), with the bounds
`∑_{n∈D} τ(n)²/n² ≤ 13` (`tsum_tau_sq_two_le`) and `∑_{n∈D} τ(n)²/n ≤ 16^{X₀}`
(`tsum_tau_sq_one_le`). Here `D` is the set of `X₀`-smooth numbers.
-/

@[expose] public section

open Finset

namespace TauSum

/-- `∑_k (k+1)² x^k = (1+x)/(1-x)³`. -/
lemma hasSum_sq_succ_geometric {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * x ^ k) ((1 + x) / (1 - x) ^ 3) := by
  have hx : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hA := hasSum_choose_mul_geometric_of_norm_lt_one 2 hx
  have hB := hasSum_choose_mul_geometric_of_norm_lt_one 1 hx
  have h := (hA.mul_left 2).sub hB
  have hne : (1 - x) ≠ 0 := by linarith
  convert h using 1
  · funext k
    rw [Nat.cast_choose_two]
    simp only [Nat.choose_one_right]
    push_cast; ring
  · field_simp; ring

lemma card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- `∑_{n∈D} τ(n)² n^{-σ} = ∏_{p<X₀} (1 + p^{-σ})/(1 - p^{-σ})³`. -/
lemma hasSum_tau_sq_smooth (X₀ : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun n : ℕ => if n ∈ X₀.smoothNumbers then
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-σ)) else 0)
      (∏ p ∈ X₀.primesBelow, (1 + (p : ℝ) ^ (-σ)) / (1 - (p : ℝ) ^ (-σ)) ^ 3) := by
  classical
  set f : ℕ → ℝ := fun n => (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-σ) with hf
  have h1 : f 1 = 1 := by simp [hf]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hf, Nat.Coprime.card_divisors_mul hmn, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, f (p ^ k) = ((k : ℝ) + 1) ^ 2 * ((p : ℝ) ^ (-σ)) ^ k := by
    intro p hp k
    simp only [hf, card_divisors_prime_pow hp k, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    congr 1
    rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul (Nat.cast_nonneg p),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]
  have hx0 : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ (-σ) := fun p => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hx1 : ∀ {p : ℕ}, p.Prime → (p : ℝ) ^ (-σ) < 1 := fun hp => BaseFactor.rpow_neg_lt_one hp hσ
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    have := (hasSum_sq_succ_geometric (hx0 p) (hx1 hp)).summable
    refine this.congr fun k => ?_
    rw [hpow hp, Real.norm_eq_abs, abs_of_nonneg (by have := hx0 p; positivity)]
  obtain ⟨-, hh⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 hmul hsum X₀
  have hprod : (∏ p ∈ X₀.primesBelow, ∑' n : ℕ, f (p ^ n)) =
      ∏ p ∈ X₀.primesBelow, (1 + (p : ℝ) ^ (-σ)) / (1 - (p : ℝ) ^ (-σ)) ^ 3 := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    simp only [hpow hp']
    exact (hasSum_sq_succ_geometric (hx0 p) (hx1 hp')).tsum_eq
  rw [hprod] at hh
  have := (hasSum_subtype_iff_indicator (s := (X₀.smoothNumbers : Set ℕ)) (f := f)).mp hh
  convert this using 1
  funext d
  simp only [Set.indicator_apply, hf]

lemma one_add_div_one_sub_cube_le_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    (1 + x) / (1 - x) ^ 3 ≤ Real.exp (5 * x) := by
  have hpos : 0 < 1 - x := by linarith
  -- `1 + x ≤ e^x` and `(1 - x)⁻¹ ≤ e^{4x/3}`
  have ha : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hb : (1 - x)⁻¹ ≤ Real.exp (4 * x / 3) := by
    rw [inv_le_comm₀ hpos (Real.exp_pos _), ← Real.exp_neg]
    have h2 := Real.add_one_le_exp (4 * x / 3)
    have h3 : Real.exp (-(4 * x / 3)) = (Real.exp (4 * x / 3))⁻¹ := Real.exp_neg _
    rw [h3, inv_le_comm₀ (Real.exp_pos _) hpos]
    calc (1 - x)⁻¹ ≤ 4 * x / 3 + 1 := by
          rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
      _ ≤ _ := h2
  calc (1 + x) / (1 - x) ^ 3 = (1 + x) * ((1 - x)⁻¹) ^ 3 := by field_simp
    _ ≤ Real.exp x * (Real.exp (4 * x / 3)) ^ 3 := by
        apply mul_le_mul ha (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
          (Real.exp_pos _).le
    _ = Real.exp (5 * x) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- `∑_{k=1}^{K} 1/(4k(k+1)) ≤ 1/4`. -/
lemma sum_telescope_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, (1 : ℝ) / (4 * k * (k + 1)) ≤ 1 / 4 := by
  have key : ∀ K : ℕ, ∑ k ∈ Finset.Ico 1 (K + 1), (1 : ℝ) / (4 * k * (k + 1)) =
      1 / 4 - 1 / (4 * (K + 1)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      push_cast
      field_simp
      ring
  rcases K with _ | K
  · simp
  · rw [key]
    have : (0 : ℝ) ≤ 1 / (4 * ((K : ℝ) + 1)) := by positivity
    linarith

/-- `∑_{p<X₀} 1/p² ≤ 1/2`. -/
lemma sum_primes_inv_sq_le (X₀ : ℕ) :
    ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
  classical
  set P := X₀.primesBelow
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p = 2)]
  have h2 : ∑ p ∈ P.filter (fun p => p = 2), ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    calc ∑ p ∈ P.filter (fun p => p = 2), ((p : ℝ) ^ 2)⁻¹ ≤ ∑ p ∈ ({2} : Finset ℕ),
          ((p : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; simp only [Finset.mem_filter] at hp; simp [hp.2]
          · intro _ _ _; positivity
      _ = 1 / 4 := by norm_num
  have hodd : ∑ p ∈ P.filter (fun p => ¬ p = 2), ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    set Q := P.filter (fun p => ¬ p = 2)
    have hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ p < X₀ := by
      intro p hp
      simp only [Q, P, Finset.mem_filter, Nat.mem_primesBelow] at hp
      exact ⟨hp.1.2, hp.2, hp.1.1⟩
    have hle : ∀ p ∈ Q, ((p : ℝ) ^ 2)⁻¹ ≤ 1 / (4 * ((p / 2 : ℕ) : ℝ) * (((p / 2 : ℕ) : ℝ) + 1)) := by
      intro p hp
      obtain ⟨hpp, hp2, -⟩ := hQ p hp
      obtain ⟨m, hm⟩ := hpp.odd_of_ne_two hp2
      have hm2 : p / 2 = m := by omega
      have hm1 : 1 ≤ m := by have := hpp.two_le; omega
      rw [hm2, hm]
      have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      push_cast
      rw [one_div]
      apply inv_anti₀ (by positivity)
      nlinarith
    have hinj : Set.InjOn (fun p : ℕ => p / 2) Q := by
      intro p hp q hq hpq
      obtain ⟨m, hm⟩ := (hQ p hp).1.odd_of_ne_two (hQ p hp).2.1
      obtain ⟨n, hn⟩ := (hQ q hq).1.odd_of_ne_two (hQ q hq).2.1
      simp only at hpq
      omega
    calc ∑ p ∈ Q, ((p : ℝ) ^ 2)⁻¹
        ≤ ∑ p ∈ Q, 1 / (4 * ((p / 2 : ℕ) : ℝ) * (((p / 2 : ℕ) : ℝ) + 1)) :=
          Finset.sum_le_sum hle
      _ = ∑ k ∈ Q.image (fun p : ℕ => p / 2), (1 : ℝ) / (4 * (k : ℝ) * ((k : ℝ) + 1)) :=
          (Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (4 * (k : ℝ) * ((k : ℝ) + 1)))
            hinj).symm
      _ ≤ ∑ k ∈ Finset.Ico 1 X₀, (1 : ℝ) / (4 * k * (k + 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨hpp, hp2, hpX⟩ := hQ p hp
            have := hpp.two_le
            simp only [Finset.mem_Ico]; omega
          · intro _ _ _; positivity
      _ ≤ 1 / 4 := sum_telescope_le X₀
  linarith

lemma exp_five_halves_le : Real.exp (5 / 2) ≤ 13 := by
  have he := Real.exp_one_lt_d9
  have hh : Real.exp (1 / 2) ≤ 1.65 := by
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have e : Real.exp (5 / 2) = Real.exp 1 ^ 2 * Real.exp (1 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h1 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
  nlinarith [Real.exp_pos (1 / 2), Real.exp_pos 1]

/-- `∑_{n∈D} τ(n)²/n² ≤ 13`. -/
theorem tsum_tau_sq_two_le (X₀ : ℕ) :
    ∑' n : ℕ, (if n ∈ X₀.smoothNumbers then
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(2 : ℝ))) else 0) ≤ 13 := by
  rw [(hasSum_tau_sq_smooth X₀ (by norm_num : (0 : ℝ) < 2)).tsum_eq]
  have hx : ∀ p ∈ X₀.primesBelow, (p : ℝ) ^ (-(2 : ℝ)) = ((p : ℝ) ^ 2)⁻¹ := by
    intro p _
    rw [Real.rpow_neg (Nat.cast_nonneg p), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  calc ∏ p ∈ X₀.primesBelow, (1 + (p : ℝ) ^ (-(2 : ℝ))) / (1 - (p : ℝ) ^ (-(2 : ℝ))) ^ 3
      ≤ ∏ p ∈ X₀.primesBelow, Real.exp (5 * ((p : ℝ) ^ 2)⁻¹) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpp := (Nat.mem_primesBelow.mp hp).2
          have h1 := BaseFactor.rpow_neg_lt_one hpp (by norm_num : (0 : ℝ) < 2)
          have h0 : 0 ≤ (p : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
          have : 0 < 1 - (p : ℝ) ^ (-(2 : ℝ)) := by linarith
          positivity
        · intro p hp
          have hpp := (Nat.mem_primesBelow.mp hp).2
          have hp2 := BaseFactor.two_le_cast hpp
          rw [hx p hp]
          apply one_add_div_one_sub_cube_le_exp (by positivity)
          rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    _ = Real.exp (5 * ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ 2)⁻¹) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (5 / 2) := by
        apply Real.exp_le_exp.mpr
        have := sum_primes_inv_sq_le X₀
        linarith
    _ ≤ 13 := exp_five_halves_le

/-- `∑_{n∈D} τ(n)²/n ≤ 16^{X₀}`. -/
theorem tsum_tau_sq_one_le (X₀ : ℕ) :
    ∑' n : ℕ, (if n ∈ X₀.smoothNumbers then
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 : ℝ))) else 0) ≤ 16 ^ X₀ := by
  rw [(hasSum_tau_sq_smooth X₀ (by norm_num : (0 : ℝ) < 1)).tsum_eq]
  calc ∏ p ∈ X₀.primesBelow, (1 + (p : ℝ) ^ (-(1 : ℝ))) / (1 - (p : ℝ) ^ (-(1 : ℝ))) ^ 3
      ≤ ∏ _p ∈ X₀.primesBelow, (16 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpp := (Nat.mem_primesBelow.mp hp).2
          have h1 := BaseFactor.rpow_neg_lt_one hpp (by norm_num : (0 : ℝ) < 1)
          have h0 : 0 ≤ (p : ℝ) ^ (-(1 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
          have : 0 < 1 - (p : ℝ) ^ (-(1 : ℝ)) := by linarith
          positivity
        · intro p hp
          have hpp := (Nat.mem_primesBelow.mp hp).2
          have hp2 := BaseFactor.two_le_cast hpp
          rw [Real.rpow_neg_one]
          have hx : (p : ℝ)⁻¹ ≤ 1 / 2 := by
            rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
          have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
          rw [div_le_iff₀ (by have : 0 < 1 - (p : ℝ)⁻¹ := by linarith
                              positivity)]
          have h3 : (1 / 2 : ℝ) ^ 3 ≤ (1 - (p : ℝ)⁻¹) ^ 3 :=
            pow_le_pow_left₀ (by norm_num) (by linarith) 3
          norm_num at h3 ⊢; linarith
    _ = 16 ^ X₀.primesBelow.card := by rw [Finset.prod_const]
    _ ≤ 16 ^ X₀ := by
        apply pow_le_pow_right₀ (by norm_num)
        calc X₀.primesBelow.card ≤ (Finset.range X₀).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = X₀ := Finset.card_range _

end TauSum

end
