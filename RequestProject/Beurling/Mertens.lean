module

public import RequestProject.Beurling.BaseFactor

/-!
# Mertens' estimates for `Z_∞`

We prove the two Mertens-type estimates used in Lemma 4.2 (`BaseFactor.lemma_4_2_Zinf`),
for `log X₀ ≥ 10⁴` (in Theorem 2.1, `X₀ ≥ e^{10⁸}`):

* `logSum_one_le` : `∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀`;
* `ZinfR_one_le` : `Z_∞(1) = ∏_{p<X₀} (1 - 1/p)^{-1} ≤ 1.8 log X₀`.

Both are elementary. The first uses only Mertens' first theorem in the form
`∑_{p≤n} log p/p ≤ log n + log 4` (`sum_log_div_le`), proved from `log n! ≤ n log n`,
Legendre's formula and Chebyshev's bound `θ(n) ≤ n log 4`.

For the second we compare with `σ = 1 + ε`, `ε = 5/log X₀`:
`Z_∞(1) ≤ Z_∞(σ) · exp(∑_{p<X₀} (1 - p^{-ε})/(p-1))`, and `Z_∞(σ) ≤ ζ(σ) ≤ 1 + 1/ε`. The sum is
estimated by Abel summation against Mertens' first theorem, which bounds its main part by
`∫_0^5 (1 - e^{-u})/u du ≤ Q(5) ≤ 2.1884`, where `Q` is an explicit polynomial (the integral of
a Taylor upper bound for `(1 - e^{-u})/u`). Since `e^{2.192}/5 < 1.8`, this gives the claim. (The
true constant is `e^γ = 1.781…`; Mathlib's bounds on `γ` are not needed.)
-/

@[expose] public section

open Finset

namespace Mertens

open scoped Nat

/-! ### Elementary sums over primes -/

lemma sum_primesBelow_eq (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (N + 1).primesBelow, f p = ∑ k ∈ Icc 2 N, if k.Prime then f k else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Nat.mem_primesBelow, mem_filter, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨by omega, h2⟩

/-- `∑_{p ≤ n} ⌊n/p⌋ log p ≤ log n!`. -/
lemma sum_div_mul_log_le_log_factorial (n : ℕ) :
    ∑ p ∈ (n + 1).primesBelow, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n ! : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (s := (n+1).primesBelow) _ _)
  · apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    have := Nat.factorization_factorial hpp (b := Nat.log p n + 1) (n := n) (Nat.lt_succ_self _)
    rw [this]
    by_cases hpn : p ≤ n
    · have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) := by
        have := Nat.log_pos hpp.one_lt hpn
        simp; exact ⟨hpn, hpp.one_lt⟩
      have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
      simp at this
      exact_mod_cast this
    · have : n / p = 0 := Nat.div_eq_of_lt (by omega)
      simp only [this, Nat.cast_zero]
      positivity
  · intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp)
    rw [Finsupp.mem_support_iff]
    exact (hpp.2.factorization_pos_of_dvd (Nat.factorial_ne_zero n)
      (Nat.dvd_factorial hpp.2.pos (by omega))).ne'
  · intro p _ _
    exact mul_nonneg (by positivity) (Real.log_natCast_nonneg p)

/-- Chebyshev: `θ(n) = ∑_{p ≤ n} log p ≤ n log 4`. -/
lemma sum_log_le (n : ℕ) : ∑ p ∈ (n + 1).primesBelow, Real.log p ≤ n * Real.log 4 := by
  have h : ∑ p ∈ (n + 1).primesBelow, Real.log p = Real.log ((primorial n : ℕ) : ℝ) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    · rfl
    · intro p hp; simp at hp; exact_mod_cast hp.2.ne_zero
  rw [h]
  have := primorial_le_four_pow n
  calc Real.log ((primorial n : ℕ) : ℝ) ≤ Real.log ((4 ^ n : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast primorial_pos n) (by exact_mod_cast this)
    _ = n * Real.log 4 := by push_cast; rw [Real.log_pow]

/-- **Mertens' first theorem (upper bound).** `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem sum_log_div_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ (n + 1).primesBelow, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) * ∑ p ∈ (n + 1).primesBelow, Real.log p / p ≤
      ∑ p ∈ (n + 1).primesBelow, ((n / p : ℕ) : ℝ) * Real.log p +
        ∑ p ∈ (n + 1).primesBelow, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      have h1 := Nat.div_add_mod n p
      have h2 := Nat.mod_lt n hpp.pos
      rw [div_le_iff₀ hp0]
      have h3 : (n : ℝ) = p * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by exact_mod_cast h1.symm
      have h4 : ((n % p : ℕ) : ℝ) ≤ p := by exact_mod_cast h2.le
      nlinarith
    calc (n : ℝ) * (Real.log p / p) = (n / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hdiv hlog
      _ = _ := by ring
  have h1 := sum_div_mul_log_le_log_factorial n
  have h2 := sum_log_le n
  have h3 : Real.log (n ! : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
      (by exact_mod_cast Nat.factorial_le_pow n)
  have : (n : ℝ) * ∑ p ∈ (n + 1).primesBelow, Real.log p / p ≤
      (n : ℝ) * (Real.log n + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left this hn0

/-- The weights `a_n = log n / n` on primes, `0` elsewhere. -/
noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

lemma primeLogWeight_partial_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, primeLogWeight k ≤ Real.log N + Real.log 4 := by
  have e : ∑ k ∈ Icc 2 N, primeLogWeight k = ∑ p ∈ (N + 1).primesBelow, Real.log p / p := by
    rw [sum_primesBelow_eq]; rfl
  rw [e]
  exact sum_log_div_le (by omega)

/-! ### Abel summation (upper bound form) -/

/-- If the partial sums of `a` are bounded by `B` and `w ≥ 0` is non-increasing, then
`∑_{k=2}^N a_k w_k ≤ B(2) w(2) + ∑_{n=3}^N (B(n) - B(n-1)) w(n)`. -/
lemma abel_upper (a w B : ℕ → ℝ) (hA : ∀ N ≥ 2, ∑ k ∈ Icc 2 N, a k ≤ B N)
    (hw : ∀ n ≥ 2, w (n + 1) ≤ w n) (hw0 : ∀ n ≥ 2, 0 ≤ w n) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, a k * w k ≤ B 2 * w 2 + ∑ n ∈ Icc 3 N, (B n - B (n - 1)) * w n := by
  have key : ∀ N ≥ 2, ∑ k ∈ Icc 2 N, a k * w k ≤ B 2 * w 2 +
      ∑ n ∈ Icc 3 N, (B n - B (n - 1)) * w n + (∑ k ∈ Icc 2 N, a k - B N) * w N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp; ring_nf; rfl
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 : (∑ k ∈ Icc 2 M, a k - B M) * (w M - w (M + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith [hA M hM]) (by linarith [hw M hM])
      simp only [Nat.add_sub_cancel]
      nlinarith
  have := key N hN
  have h2 : (∑ k ∈ Icc 2 N, a k - B N) * w N ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hA N hN]) (hw0 N hN)
  linarith

lemma sum_inv_sq_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 - 1 / ((N : ℝ) - 1) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    have h1 : 1 / ((M : ℝ) + 1 - 1) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / ((M : ℝ) + 1 - 1) := by
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith)
        (by nlinarith)]
      nlinarith
    linarith

lemma log_sub_log_pred_le {n : ℕ} (hn : 3 ≤ n) :
    Real.log n - Real.log ((n - 1 : ℕ) : ℝ) ≤ 1 / ((n : ℝ) - 1) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega), Nat.cast_one, ← Real.log_div (by linarith) (by linarith)]
  have := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / (n - 1) by
    apply div_pos <;> linarith)
  have e : (n : ℝ) / (n - 1) - 1 = 1 / (n - 1) := by
    rw [div_sub_one (by linarith)]; congr 1; ring
  linarith

lemma log_two_add_log_four_le : Real.log 2 + Real.log 4 ≤ 2.08 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  norm_num at *
  linarith

/-- `∑_{p ≤ N} log p / (p (p-1)) ≤ 5`. -/
lemma sum_log_div_mul_pred_le (N : ℕ) :
    ∑ p ∈ (N + 1).primesBelow, Real.log p / (p * (p - 1)) ≤ 5 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [sum_primesBelow_eq, Finset.Icc_eq_empty (by omega)]; simp
  rw [sum_primesBelow_eq]
  have e : ∀ k ∈ Icc 2 N, (if k.Prime then Real.log k / (k * (k - 1)) else 0) =
      primeLogWeight k * (1 / ((k : ℝ) - 1)) := by
    intro k _
    unfold primeLogWeight
    split_ifs
    · rw [div_mul_div_comm, mul_one]
    · simp
  rw [Finset.sum_congr rfl e]
  have hab := abel_upper primeLogWeight (fun k => 1 / ((k : ℝ) - 1))
    (fun n => Real.log n + Real.log 4) (fun N hN => primeLogWeight_partial_le hN)
    (by
      intro n hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      apply one_div_le_one_div_of_le (by linarith) (by linarith))
    (by
      intro n hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      apply div_nonneg zero_le_one (by linarith)) hN
  refine hab.trans ?_
  try dsimp only
  have h2 : ∑ n ∈ Icc 3 N, (Real.log n + Real.log 4 - (Real.log ((n - 1 : ℕ) : ℝ) +
      Real.log 4)) * (1 / ((n : ℝ) - 1)) ≤ ∑ n ∈ Icc 3 N, 1 / ((n : ℝ) - 1) ^ 2 := by
    apply Finset.sum_le_sum
    intro n hn
    have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have := log_sub_log_pred_le hn3
    have h0 : 0 ≤ 1 / ((n : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    calc _ = (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * (1 / ((n : ℝ) - 1)) := by ring
      _ ≤ (1 / ((n : ℝ) - 1)) * (1 / ((n : ℝ) - 1)) := mul_le_mul_of_nonneg_right this h0
      _ = _ := by rw [one_div_mul_one_div, sq]
  have h3 := sum_inv_sq_le hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : 0 ≤ 1 / ((N : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  have h5 := log_two_add_log_four_le
  have h6 : (1 : ℝ) / (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
  rw [h6]
  linarith

/-! ### Mertens' estimate for `∑ log p/(p-1)` -/

lemma three_le_of_log {X₀ : ℕ} (hX : 1 ≤ Real.log X₀) : 3 ≤ X₀ := by
  by_contra h
  push_neg at h
  have : Real.log X₀ ≤ Real.log 2 := by
    rcases Nat.eq_zero_or_pos X₀ with h0 | h0
    · subst h0; simp; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : X₀ ≤ 2))
  have := Real.log_two_lt_d9
  norm_num at *; linarith

/-- **Mertens' estimate** `∑_{p<X₀} log p/(p-1) ≤ 1.01 log X₀` for `log X₀ ≥ 10⁴`. -/
theorem logSum_one_le {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀) :
    BaseFactor.logSum X₀ 1 ≤ 1.01 * Real.log X₀ := by
  have h3 := three_le_of_log (X₀ := X₀) (by linarith)
  obtain ⟨N, rfl⟩ : ∃ N, X₀ = N + 1 := ⟨X₀ - 1, by omega⟩
  unfold BaseFactor.logSum
  have e : ∀ p ∈ (N + 1).primesBelow, Real.log p / ((p : ℝ) ^ (1 : ℝ) - 1) =
      Real.log p / p + Real.log p / (p * (p - 1)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have h1 : (p:ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p:ℝ) ≠ 0 := by linarith
    rw [Real.rpow_one]
    field_simp
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  have h1 := sum_log_div_le (n := N) (by omega)
  have h2 := sum_log_div_mul_pred_le N
  have h4 := log_two_add_log_four_le
  have h5 : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by push_cast; linarith)
  have h6 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-! ### The comparison with `ζ(1 + ε)` -/

/-- `n ↦ n^{-σ}` as a completely multiplicative function. -/
noncomputable def rpowHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by push_cast; exact Real.mul_rpow (by positivity) (by positivity)

/-- `Z_∞(σ) ≤ ζ(σ) ≤ 1 + 1/(σ - 1)` for `σ > 1`. -/
lemma ZinfR_le_of_one_lt (N : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    BaseFactor.ZinfR N σ ≤ 1 + 1 / (σ - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hprod := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers
    (f := rpowHom σ) hsum N
  have e1 : BaseFactor.ZinfR N σ = ∑' m : N.smoothNumbers, (m : ℝ) ^ (-σ) := hprod
  rw [e1]
  have h1 : ∑' m : N.smoothNumbers, (m : ℝ) ^ (-σ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
    Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ)) _ (fun n => by positivity) hsum
  have h2 : ∑' n : ℕ, (n : ℝ) ^ (-σ) = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ σ := by
    rw [hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    rw [Real.zero_rpow (by linarith), zero_add]
    congr 1; ext n
    rw [Real.rpow_neg (by positivity), one_div]
  have h3 := ZetaAsymptotics.zeta_limit_aux1 hσ
  have h4 : 0 ≤ ZetaAsymptotics.termTSum σ :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg _ _)
  have h5 : 0 ≤ σ * ZetaAsymptotics.termTSum σ := mul_nonneg (by linarith) h4
  linarith

/-- `(1 - 1/p)^{-1} ≤ (1 - p^{-1-ε})^{-1} e^{(1 - p^{-ε})/(p-1)}`. -/
lemma factor_one_le {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ ≤ (1 - (p : ℝ) ^ (-(1 + ε)))⁻¹ *
      Real.exp ((1 - (p : ℝ) ^ (-ε)) / (p - 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set q := (p : ℝ) ^ (-ε) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have e1 : (p : ℝ) ^ (-(1 : ℝ)) = 1 / p := by rw [Real.rpow_neg_one, one_div]
  have e2 : (p : ℝ) ^ (-(1 + ε)) = q / p := by
    rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one, hq]; ring
  rw [e1, e2]
  have h1 := Real.add_one_le_exp ((1 - q) / (p - 1))
  have hpq : 0 < 1 - q / p := by
    rw [sub_pos, div_lt_one hp0]; linarith
  have e3 : (1 - 1 / (p : ℝ))⁻¹ = (1 - q / p)⁻¹ * ((1 - q) / (p - 1) + 1) := by
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) - q ≠ 0 := by linarith
    field_simp
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hpq).le

/-- `Z_∞(1) ≤ Z_∞(1+ε) · exp(∑_{p<X₀} (1 - p^{-ε})/(p-1))`. -/
lemma ZinfR_one_le_mul_exp (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    BaseFactor.ZinfR N 1 ≤ BaseFactor.ZinfR N (1 + ε) *
      Real.exp (∑ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-ε)) / (p - 1)) := by
  unfold BaseFactor.ZinfR
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [Real.rpow_neg_one]
    apply inv_nonneg.mpr
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  · intro p hp
    exact factor_one_le (Nat.mem_primesBelow.mp hp).2 hε

/-! ### Taylor bounds and the polynomial `Q` -/

/-- Taylor polynomial of `e^{-u}` of degree `< n`. -/
noncomputable def expNegTaylor (n : ℕ) (u : ℝ) : ℝ := ∑ k ∈ range n, (-u) ^ k / (k ! : ℝ)

lemma hasDerivAt_expNegTaylor (n : ℕ) (u : ℝ) :
    HasDerivAt (expNegTaylor (n + 1)) (-expNegTaylor n u) u := by
  induction n generalizing u with
  | zero =>
    have : expNegTaylor 1 = fun _ => 1 := by funext v; simp [expNegTaylor]
    rw [this]; simpa [expNegTaylor] using hasDerivAt_const u (1 : ℝ)
  | succ n ih =>
    have e : expNegTaylor (n + 1 + 1) =
        fun v => expNegTaylor (n + 1) v + (-v) ^ (n + 1) / ((n + 1)! : ℝ) := by
      funext v; simp only [expNegTaylor]; rw [Finset.sum_range_succ]
    rw [e]
    have h2 : HasDerivAt (fun v : ℝ => (-v) ^ (n + 1) / ((n + 1)! : ℝ))
        (((n + 1 : ℕ) : ℝ) * (-u) ^ n * (-1) / ((n + 1)! : ℝ)) u := by
      have := ((hasDerivAt_neg u).pow (n + 1)).div_const ((n + 1)! : ℝ)
      simpa using this
    convert! (ih u).add h2 using 1
    simp only [expNegTaylor]
    rw [Finset.sum_range_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The alternating Taylor bounds: `(-1)^n (e^{-u} - T_n(u)) ≥ 0` for `u ≥ 0`. -/
lemma expNegTaylor_alt (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (-1) ^ n * (Real.exp (-u) - expNegTaylor n u) := by
  induction n generalizing u with
  | zero => simp [expNegTaylor]; positivity
  | succ n ih =>
    set f : ℝ → ℝ := fun v => (-1) ^ (n + 1) * (Real.exp (-v) - expNegTaylor (n + 1) v)
    have hd : ∀ v, HasDerivAt f ((-1) ^ n * (Real.exp (-v) - expNegTaylor n v)) v := by
      intro v
      have h1 : HasDerivAt (fun v => Real.exp (-v)) (-Real.exp (-v)) v := by
        simpa [Function.comp_def] using (Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)
      convert! (h1.sub (hasDerivAt_expNegTaylor n v)).const_mul ((-1 : ℝ) ^ (n + 1)) using 1
      ring
    have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun v _ => (hd v).continuousAt.continuousWithinAt
      · exact fun v _ => (hd v).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        rw [(hd v).deriv]
        exact ih (le_of_lt hv)
    have h0 : f 0 = 0 := by
      simp only [f, expNegTaylor, neg_zero, Real.exp_zero]
      rw [Finset.sum_range_succ']
      simp
    have := hmono Set.self_mem_Ici hu hu
    rw [h0] at this
    exact this

/-- `P(u) = ∑_{k<15} (-1)^k u^k/(k+1)!`, an upper bound for `(1 - e^{-u})/u`. -/
noncomputable def einP (u : ℝ) : ℝ := ∑ k ∈ range 15, (-1) ^ k * u ^ k / ((k + 1)! : ℝ)

/-- `Q(u) = ∑_{k<15} (-1)^k u^{k+1}/((k+1)(k+1)!)`, an antiderivative of `P`. -/
noncomputable def einQ (u : ℝ) : ℝ :=
  ∑ k ∈ range 15, (-1) ^ k * u ^ (k + 1) / ((k + 1 : ℝ) * ((k + 1)! : ℝ))

lemma one_sub_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : 1 - Real.exp (-u) ≤ u * einP u := by
  have h := expNegTaylor_alt 16 hu
  norm_num at h
  have e : expNegTaylor 16 u = 1 - u * einP u := by
    unfold expNegTaylor einP
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [add_comm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_pow, pow_succ (-1 : ℝ), pow_succ u]
    ring
  linarith

lemma hasDerivAt_einQ (u : ℝ) : HasDerivAt einQ (einP u) u := by
  unfold einQ einP
  have : ∀ k ∈ range 15, HasDerivAt (fun v : ℝ => (-1) ^ k * v ^ (k + 1) /
      ((k + 1 : ℝ) * ((k + 1)! : ℝ))) ((-1) ^ k * u ^ k / ((k + 1)! : ℝ)) u := by
    intro k _
    have h := ((hasDerivAt_pow (k + 1) u).const_mul ((-1 : ℝ) ^ k)).div_const
      ((k + 1 : ℝ) * ((k + 1)! : ℝ))
    convert! h using 1
    push_cast
    field_simp
  convert! HasDerivAt.sum this using 1

lemma einQ_five_le : einQ 5 ≤ 2.1884 := by
  norm_num [einQ, Finset.sum_range_succ, Nat.factorial]

/-- `φ(u) = (1 - e^{-u})/u`. -/
noncomputable def phi (u : ℝ) : ℝ := (1 - Real.exp (-u)) / u

lemma phi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ phi u := by
  unfold phi
  apply div_nonneg _ hu
  have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma phi_le_one {u : ℝ} (hu : 0 ≤ u) : phi u ≤ 1 := by
  unfold phi
  rcases hu.eq_or_lt with h | h
  · subst h; simp
  · rw [div_le_one h]
    have := Real.add_one_le_exp (-u)
    linarith

lemma phi_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : phi t ≤ phi s := by
  have h := convexOn_exp.secant_mono (a := 0) (x := -t) (y := -s) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) (by linarith)
  unfold phi
  simp only [Real.exp_zero, sub_zero] at h
  rw [← neg_div_neg_eq (1 - Real.exp (-t)), ← neg_div_neg_eq (1 - Real.exp (-s))]
  simpa using h

lemma phi_le_einP {u : ℝ} (hu : 0 < u) : phi u ≤ einP u := by
  unfold phi
  rw [div_le_iff₀ hu, mul_comm]
  exact one_sub_exp_neg_le hu.le

/-- The per-step comparison: `(b - a) ε φ(εb) ≤ Q(εb) - Q(εa)` for `0 ≤ a ≤ b`. -/
lemma step_le {ε a b : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * (ε * phi (ε * b)) ≤ einQ (ε * b) - einQ (ε * a) := by
  set c := ε * phi (ε * b)
  set F : ℝ → ℝ := fun t => einQ (ε * t) - t * c
  have hd : ∀ t, HasDerivAt F (ε * einP (ε * t) - c) t := by
    intro t
    have h1 : HasDerivAt (fun t => einQ (ε * t)) (einP (ε * t) * ε) t := by
      have := (hasDerivAt_einQ (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)
      simpa [Function.comp_def] using this
    convert! h1.sub ((hasDerivAt_id t).mul_const c) using 1
    simp; ring
  have hmono : MonotoneOn F (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun v _ => (hd v).continuousAt.continuousWithinAt
    · exact fun v _ => (hd v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v).deriv]
      have hv0 : 0 < ε * v := mul_pos hε (by linarith [hv.1])
      have h1 := phi_le_einP hv0
      have h2 := phi_anti hv0 (mul_le_mul_of_nonneg_left hv.2.le hε.le)
      have : c ≤ ε * einP (ε * v) := mul_le_mul_of_nonneg_left (h2.trans h1) hε.le
      linarith
  have := hmono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  simp only [F] at this
  linarith

/-! ### The main sum -/

lemma telescope_le {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * (ε * phi (ε * Real.log n)) ≤
      einQ (ε * Real.log N) - einQ (ε * Real.log 2) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have h := step_le hε (Real.log_nonneg (by linarith : (1:ℝ) ≤ M))
      (Real.log_le_log (by linarith) (by linarith : (M : ℝ) ≤ M + 1))
    simp only [Nat.add_sub_cancel]
    push_cast at h ⊢
    linarith

/-- `∑_{p ≤ N} (1 - p^{-ε})/p ≤ 2.08 ε + Q(ε log M)` for `2 ≤ N ≤ M`. -/
lemma sum_one_sub_rpow_div_le {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 2 ≤ N) {M : ℝ}
    (hNM : (N : ℝ) ≤ M) :
    ∑ p ∈ (N + 1).primesBelow, (1 - (p : ℝ) ^ (-ε)) / p ≤
      2.08 * ε + einQ (ε * Real.log M) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set w : ℕ → ℝ := fun n => ε * phi (ε * Real.log n) with hw
  rw [sum_primesBelow_eq]
  have e : ∀ k ∈ Icc 2 N, (if k.Prime then (1 - (k : ℝ) ^ (-ε)) / k else 0) =
      primeLogWeight k * w k := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hlog : 0 < Real.log k := Real.log_pos (by linarith)
    unfold primeLogWeight
    split_ifs
    · simp only [hw, phi]
      rw [Real.rpow_def_of_pos (by linarith)]
      field_simp
    · simp
  rw [Finset.sum_congr rfl e]
  have hw0 : ∀ n ≥ 2, 0 ≤ w n := by
    intro n hn
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg hε.le (phi_nonneg (mul_nonneg hε.le (Real.log_nonneg (by linarith))))
  have hab := abel_upper primeLogWeight w (fun n => Real.log n + Real.log 4)
    (fun N hN => primeLogWeight_partial_le hN)
    (by
      intro n hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      simp only [hw]
      apply mul_le_mul_of_nonneg_left _ hε.le
      apply phi_anti (mul_pos hε (Real.log_pos (by linarith)))
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact Real.log_le_log (by linarith) (by push_cast; linarith)) hw0 hN
  refine hab.trans ?_
  try dsimp only
  have h1 : ∑ n ∈ Icc 3 N, (Real.log n + Real.log 4 - (Real.log ((n - 1 : ℕ) : ℝ) +
      Real.log 4)) * w n = ∑ n ∈ Icc 3 N, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * w n := by
    apply Finset.sum_congr rfl; intro n _; ring
  rw [h1]
  have h2 := telescope_le hε hN
  have h3 := step_le hε (Real.log_nonneg (by linarith : (1:ℝ) ≤ N)) (Real.log_le_log
    (by linarith) hNM)
  have h4 := step_le hε (le_refl 0) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have h5 : 0 ≤ (Real.log M - Real.log N) * (ε * phi (ε * Real.log M)) :=
    mul_nonneg (by linarith [Real.log_le_log (by linarith) hNM])
      (mul_nonneg hε.le (phi_nonneg (mul_nonneg hε.le (Real.log_nonneg (by linarith)))))
  have h6 : 0 ≤ (Real.log 2 - 0) * (ε * phi (ε * Real.log 2)) :=
    mul_nonneg (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)])
      (mul_nonneg hε.le (phi_nonneg (mul_nonneg hε.le (Real.log_nonneg (by norm_num)))))
  have h7 : einQ (ε * 0) = 0 := by simp [einQ]
  have h8 : w 2 ≤ ε := by
    simp only [hw]
    have := phi_le_one (mul_nonneg hε.le (Real.log_nonneg (by norm_num : (1:ℝ) ≤ ((2:ℕ):ℝ))))
    nlinarith
  have h9 := log_two_add_log_four_le
  have h10 : (Real.log ((2:ℕ):ℝ) + Real.log 4) * w 2 ≤ 2.08 * ε := by
    have : 0 ≤ w 2 := hw0 2 le_rfl
    push_cast
    nlinarith
  linarith

lemma exp_le_aux : Real.exp 2.192 ≤ 8.96 := by
  have h1 : Real.exp 2.192 = Real.exp 1 * Real.exp 1 * Real.exp 0.192 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_bound (x := 0.192) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h3
  have h4 : Real.exp 0.192 ≤ 1.2117 := by
    have := (abs_le.mp h3).2
    linarith
  rw [h1]
  have h5 : 0 < Real.exp 1 := Real.exp_pos 1
  have h6 : 0 < Real.exp 0.192 := Real.exp_pos _
  calc Real.exp 1 * Real.exp 1 * Real.exp 0.192 ≤ 2.7182818286 * 2.7182818286 * 1.2117 := by
        gcongr
    _ ≤ 8.96 := by norm_num

/-- **Mertens' product estimate** `Z_∞(1) = ∏_{p<X₀} (1 - 1/p)^{-1} ≤ 1.8 log X₀` for
`log X₀ ≥ 10⁴`. -/
theorem ZinfR_one_le {X₀ : ℕ} (hX : 10 ^ 4 ≤ Real.log X₀) :
    BaseFactor.ZinfR X₀ 1 ≤ 1.8 * Real.log X₀ := by
  have h3 := three_le_of_log (X₀ := X₀) (by linarith)
  set L := Real.log X₀ with hL
  have hL0 : 0 < L := by linarith
  set ε := 5 / L with hε
  have hε0 : 0 < ε := by positivity
  have hεL : ε * L = 5 := by rw [hε]; field_simp
  have hεs : ε ≤ 5 / 10 ^ 4 := by
    rw [hε]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
  obtain ⟨N, hN⟩ : ∃ N, X₀ = N + 1 := ⟨X₀ - 1, by omega⟩
  have hN2 : 2 ≤ N := by omega
  -- the sum `S = ∑_{p<X₀} (1 - p^{-ε})/(p-1)`
  have hS : ∑ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-ε)) / (p - 1) ≤ 2.192 := by
    have e : ∀ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-ε)) / (p - 1) =
        (1 - (p : ℝ) ^ (-ε)) / p + (1 - (p : ℝ) ^ (-ε)) / (p * (p - 1)) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
      have h1 : (p:ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p:ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
    have h1 := sum_one_sub_rpow_div_le hε0 hN2 (M := (X₀ : ℝ)) (by rw [hN]; push_cast; linarith)
    rw [← hN, ← hL, hεL] at h1
    have h2 : ∑ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-ε)) / (p * (p - 1)) ≤
        ε * ∑ p ∈ X₀.primesBelow, Real.log p / (p * (p - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
      have hq : 1 - (p : ℝ) ^ (-ε) ≤ ε * Real.log p := by
        rw [Real.rpow_def_of_pos (by linarith)]
        have := Real.add_one_le_exp (Real.log p * -ε)
        linarith
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hq (by nlinarith)
    have h4 := sum_log_div_mul_pred_le N
    rw [← hN] at h4
    have h5 := einQ_five_le
    nlinarith
  have hZ := ZinfR_one_le_mul_exp X₀ hε0
  have hZσ := ZinfR_le_of_one_lt X₀ (show 1 < 1 + ε by linarith)
  have hexp : Real.exp (∑ p ∈ X₀.primesBelow, (1 - (p : ℝ) ^ (-ε)) / (p - 1)) ≤ 8.96 :=
    (Real.exp_le_exp.mpr hS).trans exp_le_aux
  have e2 : 1 + 1 / (1 + ε - 1) = 1 + L / 5 := by rw [hε]; field_simp; ring
  rw [e2] at hZσ
  calc BaseFactor.ZinfR X₀ 1 ≤ (1 + L / 5) * 8.96 :=
        hZ.trans (mul_le_mul hZσ hexp (Real.exp_pos _).le (by positivity))
    _ ≤ 1.8 * L := by nlinarith

end Mertens

end
