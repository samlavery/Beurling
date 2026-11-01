module

public import RequestProject.Beurling.BaseRange.Window

/-!
# Lemma 7.3(d) and the "Use" paragraph of §7.2: the self-contained steps

Throughout `Λ = log X₀ ≥ 10⁸` and `κ = X₀^{-5/12 + 2ε_κ} = X₀^{-0.39666…}`.

* `MAP_le_edge` : for `q ∈ (X₀/(1+κ), X₀)`, `MA[ℙ](q) ≤ 1.0001/Λ` (proof of (d)(ii): the window
  `[X₀, (1+κ)q]` is either admissible in (84) at `X₀`, or holds at most `(2X₀)^{7/12} + 1`
  integers);
* `edge_N_unique` : for `X₀ ≤ x ≤ X₀^{1.01}` at most one integer `N` has
  `x/N ∈ (X₀/(1+κ), X₀)` ((d)(ii));
* `six_le_of_moebius_eq_one` : a negative term needs `μ(N) = 1`, so `N ≥ 6`;
* `edge_ii_term` : **(d)(ii)**, the single term: if `N ≥ 6`, `m ≤ 1.0001/Λ` and
  `log x ≤ log N + Λ` (as `x < N X₀`), then `-(m/N) log x ≥ -0.167`;
* `edge_iii_g` : the bound `1.0001 (log x/Λ)(κ + X₀/x) ≤ 3X₀^{-0.01}` of (d)(iii);
* `kappa_log5_le` : `4.1 κ (log x)⁵ ≤ X₀^{-0.34}` for `log x ≤ X₀^{1/100}` (end of (d)(iii),
  and, with `2.1`, the response to `μ₀` in "Use");
* `use_A_low`, `use_A_high`, `use_saias` : the arithmetic of "Use" (range (A) of
  Proposition 5.35: `≥ 0.822` on `[X₀ + H, X₀^{1.01}]`, `≥ 0.989` on `[X₀^{1.01}/2, X_sw]`,
  and `C_S · 7·10⁻⁶ ≤ 6·10⁻⁴`).
-/

@[expose] public section

open Real Set Filter
open scoped ArithmeticFunction.Moebius

namespace BaseRange

/-- `X₀^a = exp(a Λ)`. -/
lemma rpow_eq_exp {X0 : ℝ} (hX0 : 0 < X0) (a : ℝ) : X0 ^ a = Real.exp (a * Real.log X0) := by
  rw [Real.rpow_def_of_pos hX0, mul_comm]

/-- `c Λ ≤ e^{a Λ}` once `Λ ≥ 10⁸`, for `a ≥ 10⁻⁴` and `c ≤ 10⁶`. -/
lemma lin_le_exp {Λ a c : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (ha : 1 / 10 ^ 4 ≤ a) (hc : c ≤ 10 ^ 6) :
    c * Λ ≤ Real.exp (a * Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  set y := 1 / 10 ^ 4 * Λ with hy
  have hy0 : 10 ^ 4 ≤ y := by rw [hy]; nlinarith
  have hya : y ≤ a * Λ := by rw [hy]; nlinarith
  have h4 := Real.pow_div_factorial_le_exp y (by linarith) 4
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h4
  have hE : Real.exp y ≤ Real.exp (a * Λ) := Real.exp_le_exp.mpr hya
  -- `y⁴/24 ≥ 10⁶ Λ = 10¹⁰ y`, as `y³ ≥ 10¹² ≥ 24·10¹⁰`
  have hy3 : (10 : ℝ) ^ 12 ≤ y ^ 3 := by
    calc (10 : ℝ) ^ 12 = (10 ^ 4) ^ 3 := by norm_num
      _ ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy0 3
  have hΛy : Λ = 10 ^ 4 * y := by rw [hy]; ring
  have : c * Λ ≤ y ^ 4 / 24 := by
    rw [hΛy]
    have hy0' : 0 < y := by linarith
    have h1 : c * (10 ^ 4 * y) ≤ 10 ^ 10 * y := by nlinarith
    have h2 : 10 ^ 10 * y ≤ y ^ 4 / 24 := by
      have : y ^ 4 = y ^ 3 * y := by ring
      rw [this]; nlinarith
    linarith
  linarith

/-! ### `MA[ℙ]` on the partial windows below `X₀` -/

/-- **Proof of Lemma 7.3(d)(ii)**: for `q ∈ (X₀/(1+κ), X₀)`, `MA[ℙ](q) ≤ 1.0001/Λ`. -/
theorem MAP_le_edge {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq1 : (X0 : ℝ) / (1 + Construction.kappaParam X0) < q) (hq2 : q < X0) :
    MAP X0 (Construction.kappaParam X0) q ≤ 1.0001 / Real.log X0 := by
  set κ := Construction.kappaParam X0 with hκdef
  set Λ := Real.log X0 with hΛdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := lt_of_le_of_lt (by positivity) hq1
  have hκq : 0 < κ * q := mul_pos hκ0 hq0
  set b := (1 + κ) * q with hb
  have hbX : (X0 : ℝ) < b := by
    rw [div_lt_iff₀ (by linarith)] at hq1; simp only [hb]; linarith
  -- the new primes of the window are the primes of `[X₀, b]`
  have hcount : newPrimeCount X0 q b = primeCount X0 b := by
    unfold newPrimeCount primeCount
    congr 1; ext p
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, by exact_mod_cast h2, h4⟩
    · rintro ⟨h1, h2, h4⟩
      exact ⟨h1, by exact_mod_cast h2, hq2.le.trans h2, h4⟩
  have hlen : b - X0 ≤ κ * q := by simp only [hb]; linarith
  unfold MAP
  rw [← hb, hcount, div_le_div_iff₀ hκq hΛ0]
  have hε1 : Real.log X0 ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hX
  have hε0 : 0 ≤ Real.log X0 ^ (-3 : ℤ) := zpow_neg3_nonneg hΛ0.le
  by_cases hlong : (2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) ≤ b - X0
  · -- admissible at `X₀`
    have hadm : Admissible X0 X0 b := ⟨le_rfl, by simp only [hb]; nlinarith, hlong⟩
    have hX2 : (2 : ℝ) ≤ X0 := by
      have h2 : Real.exp (10 ^ 8) ≤ X0 := by
        rw [← Real.exp_log hX0]; exact Real.exp_le_exp.mpr hX
      linarith [Real.add_one_le_exp (10 ^ 8 : ℝ)]
    have hc := count_le hH hX2 le_rfl hadm
    have hli := liI_le hX1 hbX.le
    have : (primeCount X0 b : ℝ) ≤ (1 + 1 / 10 ^ 24) * (κ * q / Λ) := by
      refine hc.trans ?_
      apply mul_le_mul (by linarith) (hli.trans ?_) (liI_pos hX1 hbX).le (by norm_num)
      exact div_le_div_of_nonneg_right hlen hΛ0.le
    rw [show (1 + 1 / 10 ^ 24) * (κ * q / Λ) = (1 + 1 / 10 ^ 24) * (κ * q) / Λ by ring,
      le_div_iff₀ hΛ0] at this
    nlinarith
  · -- a short window: at most `(2X₀)^{7/12} + 1` integers
    push_neg at hlong
    have hc : (primeCount X0 b : ℝ) ≤ b - X0 + 1 := by
      have hsub : {p : ℕ | p.Prime ∧ (X0 : ℝ) ≤ p ∧ (p : ℝ) ≤ b} ⊆ ↑(Finset.Icc X0 ⌊b⌋₊) := by
        intro p hp
        simp only [Finset.coe_Icc, mem_Icc]
        exact ⟨by exact_mod_cast hp.2.1, Nat.le_floor hp.2.2⟩
      have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Nat.card_Icc] at h1
      have hfl : X0 ≤ ⌊b⌋₊ := Nat.le_floor hbX.le
      have h2 : ((⌊b⌋₊ + 1 - X0 : ℕ) : ℝ) ≤ b - X0 + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast
        linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ b)]
      exact (Nat.cast_le.mpr h1).trans h2
    -- `((2X₀)^{7/12} + 1) Λ ≤ κ q`
    have hsmall : ((2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) + 1) * Λ ≤ κ * q := by
      have hq' : (X0 : ℝ) / 2 ≤ q := by
        refine le_trans ?_ hq1.le
        exact div_le_div_of_nonneg_left hX0.le (by linarith) (by linarith)
      have hκX : κ * X0 = Real.exp ((7 / 12 + (1 / 50 - 1 / 30 + 1 / 30)) * Λ) := by
        rw [hκdef, Construction.kappaParam, ← Real.rpow_add_one hX0.ne', rpow_eq_exp hX0]
        congr 1; ring
      have h7 : (2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) ≤ 2 * Real.exp (7 / 12 * Λ) := by
        rw [Real.mul_rpow (by norm_num) hX0.le, rpow_eq_exp hX0]
        have : (2 : ℝ) ^ (7 / 12 : ℝ) ≤ 2 := by
          calc (2 : ℝ) ^ (7 / 12 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      have he1 : (1 : ℝ) ≤ Real.exp (7 / 12 * Λ) := Real.one_le_exp (by positivity)
      have hbig : 6 * Λ ≤ Real.exp (1 / 50 * Λ) := lin_le_exp hX (by norm_num) (by norm_num)
      have hsplit : Real.exp ((7 / 12 + (1 / 50 - 1 / 30 + 1 / 30)) * Λ) =
          Real.exp (7 / 12 * Λ) * Real.exp (1 / 50 * Λ) := by
        rw [← Real.exp_add]; congr 1; ring
      have : ((2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) + 1) * Λ ≤ κ * X0 / 2 := by
        rw [hκX, hsplit]
        have hE := Real.exp_pos (7 / 12 * Λ)
        nlinarith
      nlinarith
    have : (primeCount X0 b : ℝ) * Λ ≤ κ * q := by
      have h1 : (primeCount X0 b : ℝ) * Λ ≤ ((2 * (X0 : ℝ)) ^ (7 / 12 : ℝ) + 1) * Λ :=
        mul_le_mul_of_nonneg_right (by linarith) hΛ0.le
      linarith
    nlinarith

/-! ### (d)(ii): one `N`, and its sign -/

/-- For `X₀ ≤ x ≤ X₀^{1.01}` the interval `(x/X₀, (1+κ)x/X₀)` has length `κx/X₀ < 1`. -/
lemma edge_len_lt_one {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ}
    (hx : x ≤ (X0 : ℝ) ^ (1.01 : ℝ)) : Construction.kappaParam X0 * x / X0 < 1 := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hκ0 := (BModel.kappa_facts hX).1
  rw [div_lt_one hX0]
  calc Construction.kappaParam X0 * x ≤ Construction.kappaParam X0 * (X0 : ℝ) ^ (1.01 : ℝ) :=
        mul_le_mul_of_nonneg_left hx hκ0.le
    _ = Real.exp ((-5 / 12 + 2 * 0.01 + 1.01) * Real.log X0) := by
        rw [Construction.kappaParam, rpow_eq_exp hX0, rpow_eq_exp hX0, ← Real.exp_add]
        congr 1; ring
    _ < Real.exp (Real.log X0) := Real.exp_lt_exp.mpr (by nlinarith)
    _ = X0 := Real.exp_log hX0

/-- **(d)(ii)**: for `X₀ ≤ x ≤ X₀^{1.01}`, at most one `N` has `x/N ∈ (X₀/(1+κ), X₀)`. -/
theorem edge_N_unique {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx1 : (X0 : ℝ) ≤ x)
    (hx : x ≤ (X0 : ℝ) ^ (1.01 : ℝ)) {N1 N2 : ℕ} (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (h1 : x / N1 ∈ Ioo ((X0 : ℝ) / (1 + Construction.kappaParam X0)) X0)
    (h2 : x / N2 ∈ Ioo ((X0 : ℝ) / (1 + Construction.kappaParam X0)) X0) : N1 = N2 := by
  set κ := Construction.kappaParam X0
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hκ0 := (BModel.kappa_facts hX).1
  have hx0 : 0 < x := by linarith
  have hlen := edge_len_lt_one hX hx
  -- `x/X₀ < N < (1+κ)x/X₀`
  have hb : ∀ N : ℕ, 1 ≤ N →
      x / N ∈ Ioo ((X0 : ℝ) / (1 + κ)) X0 → x / X0 < N ∧ (N : ℝ) < (1 + κ) * x / X0 := by
    intro N hN hmem
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨ha, hb⟩ := hmem
    constructor
    · rw [div_lt_iff₀ hN0] at hb; rw [div_lt_iff₀ hX0]; linarith
    · rw [div_lt_div_iff₀ (by linarith) hN0] at ha; rw [lt_div_iff₀ hX0]; linarith
  obtain ⟨a1, b1⟩ := hb N1 hN1 h1
  obtain ⟨a2, b2⟩ := hb N2 hN2 h2
  have e : (1 + κ) * x / X0 = x / X0 + κ * x / X0 := by ring
  have hd : |(N1 : ℝ) - N2| < 1 := by rw [abs_lt]; constructor <;> linarith
  have : ((N1 : ℤ) - N2 : ℤ) = 0 := by
    have : |((N1 : ℤ) - N2 : ℤ)| < 1 := by exact_mod_cast hd
    rw [abs_lt] at this; omega
  omega

/-- A negative term of (d)(i) needs `μ(N) = 1`; with `N ≥ 2` this forces `N ≥ 6`. -/
theorem six_le_of_moebius_eq_one {N : ℕ} (hN : 2 ≤ N) (hμ : μ N = 1) : 6 ≤ N := by
  by_contra h
  push_neg at h
  interval_cases N
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hμ; norm_num at hμ
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three] at hμ; norm_num at hμ
  · have : μ 4 = 0 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
        ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by norm_num)]
      norm_num
    rw [this] at hμ; norm_num at hμ
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)] at hμ
    norm_num at hμ

lemma log_six_le_two : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

/-- `(1 + log N/Λ)/N ≤ (1 + 2/Λ)/6` for `N ≥ 6`, `Λ ≥ 10⁸`. -/
lemma edge_decr {N : ℕ} (hN : 6 ≤ N) {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    (1 + Real.log N / Λ) / N ≤ (1 + 2 / Λ) / 6 := by
  have hΛ0 : 0 < Λ := by linarith
  have hN0 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  rcases eq_or_lt_of_le hN with h6 | h7
  · subst h6
    have := log_six_le_two
    have : Real.log ((6 : ℕ) : ℝ) / Λ ≤ 2 / Λ := by
      push_cast; exact div_le_div_of_nonneg_right this hΛ0.le
    push_cast at this ⊢
    nlinarith
  · have hN7 : (7 : ℝ) ≤ N := by exact_mod_cast h7
    have hl : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h1 : 6 * (Real.log N / Λ) ≤ 6 * ((N - 1) / Λ) := by
      have := div_le_div_of_nonneg_right hl hΛ0.le; linarith
    have h2 : 6 * ((N - 1) / Λ) ≤ (N - 6) := by
      rw [← mul_div_assoc, div_le_iff₀ hΛ0]; nlinarith
    have h3 : 0 ≤ (N : ℝ) * (2 / Λ) := by positivity
    nlinarith

/-- **Lemma 7.3(d)(ii)**, the single term: if `N ≥ 6`, the window density is
`m ≤ 1.0001/Λ` and `0 ≤ log x ≤ log N + Λ` (as `x < N X₀`), then
`-(m/N) log x ≥ -0.167`. -/
theorem edge_ii_term {N : ℕ} (hN : 6 ≤ N) {Λ m L : ℝ} (hΛ : 10 ^ 8 ≤ Λ)
    (hm : m ≤ 1.0001 / Λ) (hL0 : 0 ≤ L) (hL : L ≤ Real.log N + Λ) : -0.167 ≤ -(m / N * L) := by
  have hΛ0 : 0 < Λ := by linarith
  have hN6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hd := edge_decr hN hΛ
  have h1 : m / N * L ≤ 1.0001 / Λ / N * (Real.log N + Λ) := by
    apply mul_le_mul (div_le_div_of_nonneg_right hm hN0.le) hL hL0 (by positivity)
  have e : 1.0001 / Λ / N * (Real.log N + Λ) = 1.0001 * ((1 + Real.log N / Λ) / N) := by
    field_simp; ring
  have h2 : 1.0001 * ((1 + Real.log N / Λ) / N) ≤ 1.0001 * ((1 + 2 / Λ) / 6) :=
    mul_le_mul_of_nonneg_left hd (by norm_num)
  have h3 : 2 / Λ ≤ 2 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
  have h4 : 1.0001 * ((1 + 2 / Λ) / 6) ≤ 0.167 := by nlinarith
  linarith

/-! ### (d)(iii) -/

/-- `κ (log x)^k ≤ X₀^{-0.3966 + k/100}` for `1 ≤ log x ≤ X₀^{1/100}`. -/
lemma kappa_log_pow_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx1 : 0 ≤ Real.log x)
    (hx : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ)) (k : ℕ) :
    Construction.kappaParam X0 * Real.log x ^ k ≤
      Real.exp ((-5 / 12 + 2 * 0.01 + k / 100) * Real.log X0) := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hpow : Real.log x ^ k ≤ Real.exp (k / 100 * Real.log X0) := by
    calc Real.log x ^ k ≤ ((X0 : ℝ) ^ (1 / 100 : ℝ)) ^ k := pow_le_pow_left₀ hx1 hx k
      _ = Real.exp (k / 100 * Real.log X0) := by
          rw [rpow_eq_exp hX0, ← Real.exp_nat_mul]; congr 1; ring
  calc Construction.kappaParam X0 * Real.log x ^ k
      ≤ Construction.kappaParam X0 * Real.exp (k / 100 * Real.log X0) :=
        mul_le_mul_of_nonneg_left hpow (BModel.kappa_facts hX).1.le
    _ = _ := by
        rw [Construction.kappaParam, rpow_eq_exp hX0, ← Real.exp_add]; congr 1; ring

/-- `c κ (log x)⁵ ≤ X₀^{-0.34}` for `0 ≤ log x ≤ X₀^{1/100}` and `c ≤ 4.1`: the end of the proof of
(d)(iii) (`c = 4.1`) and the response to `μ₀` in "Use" (`c = 2.1`). -/
theorem kappa_log5_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x c : ℝ}
    (hc : c ≤ 4.1) (hx1 : 0 ≤ Real.log x) (hx : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ)) :
    c * (Construction.kappaParam X0 * Real.log x ^ 5) ≤ (X0 : ℝ) ^ (-0.34 : ℝ) := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have h := kappa_log_pow_le hX hx1 hx 5
  rw [rpow_eq_exp hX0]
  have hsplit : Real.exp (-0.34 * Real.log X0) =
      Real.exp ((-5 / 12 + 2 * 0.01 + (5 : ℕ) / 100) * Real.log X0) *
        Real.exp ((1 / 150) * Real.log X0) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hsplit]
  have hbig : (4.1 : ℝ) ≤ Real.exp (1 / 150 * Real.log X0) := by
    have := Real.add_one_le_exp (1 / 150 * Real.log X0)
    nlinarith
  have hE := Real.exp_pos ((-5 / 12 + 2 * 0.01 + (5 : ℕ) / 100) * Real.log X0)
  have h0 : 0 ≤ Construction.kappaParam X0 * Real.log x ^ 5 :=
    mul_nonneg (BModel.kappa_facts hX).1.le (pow_nonneg hx1 5)
  calc c * (Construction.kappaParam X0 * Real.log x ^ 5)
      ≤ 4.1 * (Construction.kappaParam X0 * Real.log x ^ 5) := mul_le_mul_of_nonneg_right hc h0
    _ ≤ 4.1 * Real.exp ((-5 / 12 + 2 * 0.01 + (5 : ℕ) / 100) * Real.log X0) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ _ := by nlinarith

/-- **(d)(iii)**, the bound on `g`: for `x ≥ X₀^{1.01}/2` and `log x ≤ X₀^{1/100}`,
`1.0001 (log x/Λ)(κ + X₀/x) ≤ 3X₀^{-0.01}`. -/
theorem edge_iii_g {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ}
    (hx : (X0 : ℝ) ^ (1.01 : ℝ) / 2 ≤ x) (hxl : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ)) :
    1.0001 * (Real.log x / Real.log X0) * (Construction.kappaParam X0 + X0 / x) ≤
      3 * (X0 : ℝ) ^ (-0.01 : ℝ) := by
  set Λ := Real.log X0 with hΛdef
  set κ := Construction.kappaParam X0
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set x0 := (X0 : ℝ) ^ (1.01 : ℝ) / 2 with hx0def
  have hx0e : x0 = Real.exp (1.01 * Λ) / 2 := by rw [hx0def, rpow_eq_exp hX0]
  have hx0big : Real.exp 1 ≤ x0 := by
    rw [hx0e, le_div_iff₀ (by norm_num)]
    have h1 : Real.exp 1 * 2 ≤ Real.exp 1 * Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); nlinarith [Real.exp_pos 1]
    have h2 : Real.exp 1 * Real.exp 1 ≤ Real.exp (1.01 * Λ) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hx0pos : 0 < x0 := lt_of_lt_of_le (Real.exp_pos 1) hx0big
  have hxpos : 0 < x := lt_of_lt_of_le hx0pos hx
  -- `log x / x ≤ log x0 / x0`
  have hmono := Real.log_div_self_antitoneOn (a := x0) (b := x) hx0big
    (hx0big.trans hx) hx
  simp only at hmono
  have hlogx0 : Real.log x0 ≤ 1.01 * Λ := by
    rw [hx0e, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
    have := Real.log_pos one_lt_two; linarith
  -- the `X₀/x` part: `(log x/Λ)(X₀/x) ≤ 2.02 X₀^{-0.01}`
  have hpart1 : Real.log x / Λ * (X0 / x) ≤ 2.02 * Real.exp (-0.01 * Λ) := by
    have e : Real.log x / Λ * (X0 / x) = (Real.log x / x) * (X0 / Λ) := by
      field_simp
    rw [e]
    have h1 : Real.log x / x * (X0 / Λ) ≤ Real.log x0 / x0 * (X0 / Λ) :=
      mul_le_mul_of_nonneg_right hmono (by positivity)
    have h2 : Real.log x0 / x0 * (X0 / Λ) ≤ 1.01 * Λ / x0 * (X0 / Λ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right hlogx0 hx0pos.le
    have h3 : 1.01 * Λ / x0 * (X0 / Λ) = 2.02 * Real.exp (-0.01 * Λ) := by
      rw [hx0e]
      have hX0e : (X0 : ℝ) = Real.exp Λ := (Real.exp_log hX0).symm
      rw [hX0e]
      have : Real.exp (-0.01 * Λ) = Real.exp Λ / Real.exp (1.01 * Λ) := by
        rw [← Real.exp_sub]; congr 1; ring
      rw [this]
      field_simp
      ring
    linarith
  -- the `κ` part: `(log x/Λ) κ ≤ X₀^{-0.38}`
  have hpart2 : Real.log x / Λ * κ ≤ 0.01 * Real.exp (-0.01 * Λ) := by
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have h := kappa_log_pow_le hX hlx0 hxl 1
    have e : Real.log x / Λ * κ = (κ * Real.log x ^ 1) / Λ := by ring
    rw [e, div_le_iff₀ hΛ0]
    refine h.trans ?_
    have hsplit : Real.exp ((-5 / 12 + 2 * 0.01 + ((1 : ℕ) : ℝ) / 100) * Λ) =
        Real.exp (-0.01 * Λ) * Real.exp ((-5 / 12 + 2 * 0.01 + 1 / 100 + 0.01) * Λ) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hsplit]
    have hsm : Real.exp ((-5 / 12 + 2 * 0.01 + 1 / 100 + 0.01) * Λ) ≤ 0.01 * Λ := by
      have h1 : Real.exp ((-5 / 12 + 2 * 0.01 + 1 / 100 + 0.01) * Λ) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith
    have hE := Real.exp_pos (-0.01 * Λ)
    nlinarith
  rw [rpow_eq_exp hX0]
  have hE := Real.exp_pos (-0.01 * Λ)
  have e : 1.0001 * (Real.log x / Λ) * (κ + X0 / x) =
      1.0001 * (Real.log x / Λ * κ + Real.log x / Λ * (X0 / x)) := by ring
  rw [e]
  nlinarith

/-! ### "Use": the arithmetic of range (A) of Proposition 5.35 -/

lemma rpow_neg_small {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {a : ℝ} (ha : 1 / 1000 ≤ a) :
    (X0 : ℝ) ^ (-a) ≤ 1 / 10 ^ 21 := by
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  rw [rpow_eq_exp hX0]
  exact le_trans (Real.exp_le_exp.mpr (by nlinarith : -a * Real.log X0 ≤ -100)) exp_neg_100_le

lemma exp_neg_80_le : Real.exp (-80) ≤ 1 / 10 ^ 4 := by
  have h3 : Real.exp (-80) ≤ Real.exp (-20) := Real.exp_le_exp.mpr (by norm_num)
  have h4 : Real.exp (-20) ≤ 1 / 10 ^ 4 := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have h5 : (2 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
    rw [Real.exp_one_pow] at h5; norm_num at h5 ⊢; linarith
  linarith

/-- "Use", range (A) on `[X₀ + H, X₀^{1.01}]`:
`0.99 - 0.167 - 6·10⁻⁴ - X₀^{-0.34} - e^{-80} ≥ 0.822`. -/
theorem use_A_low {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) :
    0.822 ≤ 0.99 - 0.167 - 6e-4 - (X0 : ℝ) ^ (-0.34 : ℝ) - Real.exp (-80) := by
  have h1 := rpow_neg_small hX (a := 0.34) (by norm_num)
  have h2 := exp_neg_80_le
  norm_num at h1 h2 ⊢
  linarith

/-- "Use", range (A) on `[X₀^{1.01}/2, X_sw]`:
`0.99 - 6·10⁻⁴ - 2X₀^{-0.34} - 3X₀^{-0.01} - e^{-80} ≥ 0.989`. -/
theorem use_A_high {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) :
    0.989 ≤ 0.99 - 6e-4 - 2 * (X0 : ℝ) ^ (-0.34 : ℝ) - 3 * (X0 : ℝ) ^ (-0.01 : ℝ) -
      Real.exp (-80) := by
  have h1 := rpow_neg_small hX (a := 0.34) (by norm_num)
  have h2 := rpow_neg_small hX (a := 0.01) (by norm_num)
  have h3 := exp_neg_80_le
  norm_num at h1 h2 h3 ⊢
  linarith

/-- "Use", (c): with `C_S ≤ 77`, `C_S · 7·10⁻⁶ ≤ 6·10⁻⁴`, inside the budget
`c'/(8 C_S)`, `c' = 0.15`, with a factor `≥ 30` to spare when `C_S ≤ 77`. -/
theorem use_saias {CS : ℝ} (hCS : CS ≤ 77) :
    CS * 7e-6 ≤ 6e-4 ∧ (30 : ℝ) * 7e-6 ≤ 0.15 / (8 * 77) := by
  constructor
  · nlinarith
  · rw [le_div_iff₀ (by norm_num)]; norm_num

end BaseRange
