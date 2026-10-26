module

public import RequestProject.Beurling.Lemma51NatFull
public import RequestProject.Beurling.SmoothTails

/-!
# Chebyshev's upper bound `ψ(x) ≤ 1.12 x + O(log² x)` and `π(X) ≤ 1.26 X / log X`

Lemma 6.22(c) (second part) uses the Rosser–Schoenfeld bound `π(X₀) ≤ 1.26 X₀ / log X₀`.
In the paper's range `log X₀ ≥ 10⁸` this follows from Chebyshev's classical argument with the
weights `1, -1/2, -1/3, -1/5, 1/30`:

* `F(q) = q - ⌊q/2⌋ - ⌊q/3⌋ - ⌊q/5⌋ + ⌊q/30⌋ ∈ {0, 1}`, with `F(q) = 1` for `1 ≤ q ≤ 5`;
* `L(m) - L(m/2) - L(m/3) - L(m/5) + L(m/30) = ∑_d Λ(d) F(⌊m/d⌋) ≥ ψ(m) - ψ(m/6)`, where
  `L(m) = log m!`;
* by Stirling, the left side is at most `A m + 4 log m + 2`, `A = (7/15) log 2 + (3/10) log 3 +
  (1/6) log 5 ≤ 0.926`;
* summing over the blocks `(x/6^{k+1}, x/6^k]`: `ψ(x) ≤ 1.2 · 0.926 x + (4 log x + 50)(log x + 1)`;
* `π(X) ≤ X^{0.95} + θ(X)/(0.95 log X) ≤ 1.26 X / log X` for `log X ≥ 10⁸`.

Main results: `ChebyshevUpper.psi_le`, `ChebyshevUpper.primesBelow_card_le`, and
`SmoothTails.smooth_tail_count_large` (Lemma 6.22(c), second part, with no hypothesis on `π`).
-/

@[expose] public section

open Real Finset ArithmeticFunction Chebyshev

namespace ChebyshevUpper

/-- `F(q) = q - ⌊q/2⌋ - ⌊q/3⌋ - ⌊q/5⌋ + ⌊q/30⌋`. -/
def Fz (q : ℕ) : ℤ := (q : ℤ) - (q / 2 : ℕ) - (q / 3 : ℕ) - (q / 5 : ℕ) + (q / 30 : ℕ)

lemma Fz_mod (q : ℕ) : Fz q = Fz (q % 30) := by
  have hq := Nat.div_add_mod q 30
  set a := q / 30
  set r := q % 30
  have hr : r < 30 := Nat.mod_lt _ (by norm_num)
  have e2 : q / 2 = 15 * a + r / 2 := by omega
  have e3 : q / 3 = 10 * a + r / 3 := by omega
  have e5 : q / 5 = 6 * a + r / 5 := by omega
  have e30 : q / 30 = a + r / 30 := by omega
  unfold Fz
  rw [e2, e3, e5, e30]
  push_cast
  rw [← hq]
  push_cast
  ring

lemma Fz_small : ∀ r < 30, 0 ≤ Fz r ∧ Fz r ≤ 1 := by decide

lemma Fz_one_five : ∀ r, 1 ≤ r → r ≤ 5 → Fz r = 1 := by
  intro r h1 h5; interval_cases r <;> decide

lemma Fz_nonneg (q : ℕ) : 0 ≤ Fz q := by
  rw [Fz_mod]; exact (Fz_small _ (Nat.mod_lt _ (by norm_num))).1

/-- `L(m) = log m!` as `∑_{d ≤ M} Λ(d) ⌊m/d⌋` for any `M ≥ m`. -/
lemma chebL_div_eq (m k : ℕ) :
    BSCert.FiniteN.chebL (m / k) = ∑ d ∈ range (m + 1), Λ d * ((m / d / k : ℕ) : ℝ) := by
  unfold BSCert.FiniteN.chebL
  have hsub : range (m / k + 1) ⊆ range (m + 1) :=
    Finset.range_subset_range.mpr (by have := Nat.div_le_self m k; omega)
  rw [← Finset.sum_subset hsub]
  · apply sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  · intro d hd hnd
    simp only [mem_range, not_lt] at hd hnd
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have h1 : m < d * k := (Nat.div_lt_iff_lt_mul hk).mp (by omega)
    rw [Nat.div_div_eq_div_mul, Nat.div_eq_of_lt h1]
    simp

/-- The weighted combination of `L` as a sum of `Λ(d) F(⌊m/d⌋)`. -/
lemma comb_eq (m : ℕ) :
    BSCert.FiniteN.chebL m - BSCert.FiniteN.chebL (m / 2) - BSCert.FiniteN.chebL (m / 3) -
      BSCert.FiniteN.chebL (m / 5) + BSCert.FiniteN.chebL (m / 30) =
      ∑ d ∈ range (m + 1), Λ d * ((Fz (m / d) : ℤ) : ℝ) := by
  rw [chebL_div_eq, chebL_div_eq, chebL_div_eq, chebL_div_eq]
  unfold BSCert.FiniteN.chebL
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  unfold Fz
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

/-- `ψ(m) - ψ(⌊m/6⌋) ≤ L(m) - L(m/2) - L(m/3) - L(m/5) + L(m/30)`. -/
lemma psi_sub_le_comb (m : ℕ) :
    ψ (m : ℝ) - ψ ((m / 6 : ℕ) : ℝ) ≤
      BSCert.FiniteN.chebL m - BSCert.FiniteN.chebL (m / 2) - BSCert.FiniteN.chebL (m / 3) -
        BSCert.FiniteN.chebL (m / 5) + BSCert.FiniteN.chebL (m / 30) := by
  rw [comb_eq, BSCert.FiniteN.psi_natCast, BSCert.FiniteN.psi_natCast,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (m / 6)) (Nat.div_le_self m 6),
    add_sub_cancel_left]
  have hIoc : ∑ d ∈ Ioc (m / 6) m, Λ d =
      ∑ d ∈ range (m + 1), if m / 6 < d then Λ d else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d; simp only [mem_Ioc, mem_filter, mem_range]; omega
  rw [hIoc]
  apply Finset.sum_le_sum
  intro d hd
  simp only [mem_range] at hd
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have hF : (0 : ℝ) ≤ ((Fz (m / d) : ℤ) : ℝ) := by exact_mod_cast Fz_nonneg _
  split_ifs with h
  · have h1 : 1 ≤ m / d := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    have h5 : m / d ≤ 5 := by
      have : m / d < 6 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    rw [Fz_one_five _ h1 h5]
    simp
  · positivity

/-- `g(t) = t log t - t`. -/
noncomputable def g (t : ℝ) : ℝ := t * Real.log t - t

lemma g_sub_le {q t : ℝ} (hq : 0 < q) (hqt : q ≤ t) : g t - g q ≤ (t - q) * Real.log t := by
  have ht : 0 < t := lt_of_lt_of_le hq hqt
  have h := Real.log_le_sub_one_of_pos (show 0 < t / q by positivity)
  rw [Real.log_div ht.ne' hq.ne'] at h
  have h2 : q * (Real.log t - Real.log q) ≤ q * (t / q - 1) := mul_le_mul_of_nonneg_left h hq.le
  have e : q * (t / q - 1) = t - q := by field_simp
  unfold g; nlinarith

lemma g_mono {q t : ℝ} (hq1 : 1 ≤ q) (hqt : q ≤ t) : g q ≤ g t := by
  have hq : 0 < q := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht : 0 < t := lt_of_lt_of_le hq hqt
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < t / q by positivity)
  rw [Real.log_div ht.ne' hq.ne', inv_div] at h
  have h2 : t * (1 - q / t) ≤ t * (Real.log t - Real.log q) := mul_le_mul_of_nonneg_left h ht.le
  have e : t * (1 - q / t) = t - q := by field_simp
  have hl : Real.log q ≤ Real.log t := Real.log_le_log hq hqt
  unfold g; nlinarith

/-- For `1 ≤ k ≤ m`: `g(m/k) - log(m/k) ≤ log ⌊m/k⌋!`. -/
lemma log_factorial_div_ge (m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    g ((m : ℝ) / k) - Real.log ((m : ℝ) / k) ≤ Real.log (((m / k : ℕ)).factorial : ℝ) := by
  set q := m / k
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff hk).mpr hkm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hqt : (q : ℝ) ≤ (m : ℝ) / k := by
    rw [le_div_iff₀ hk']; exact_mod_cast Nat.div_mul_le_self m k
  have htq : (m : ℝ) / k < q + 1 := by
    rw [div_lt_iff₀ hk']
    have := Nat.lt_div_mul_add (a := m) hk
    have h' : m < (q + 1) * k := by
      show m < (m / k + 1) * k
      rw [add_mul, one_mul]; exact this
    exact_mod_cast h'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlt : 0 ≤ Real.log ((m : ℝ) / k) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith)
  have h1 := g_sub_le hq0 hqt
  have h2 := (Lemma51Nat.log_factorial_bounds q hq1).1
  have h3 : ((m : ℝ) / k - q) * Real.log ((m : ℝ) / k) ≤ Real.log ((m : ℝ) / k) := by
    have : (m : ℝ) / k - q ≤ 1 := by linarith
    nlinarith
  unfold g at h1 ⊢
  linarith

/-- `A = (7/15) log 2 + (3/10) log 3 + (1/6) log 5`. -/
noncomputable def Aconst : ℝ := 7 / 15 * Real.log 2 + 3 / 10 * Real.log 3 + 1 / 6 * Real.log 5

/-- **Stirling for the combination**: for `m ≥ 30`,
`log m! - log ⌊m/2⌋! - log ⌊m/3⌋! - log ⌊m/5⌋! + log ⌊m/30⌋! ≤ A m + 4 log m + 2`. -/
lemma comb_le (m : ℕ) (hm : 30 ≤ m) :
    Real.log (m.factorial : ℝ) - Real.log ((m / 2).factorial : ℝ) -
      Real.log ((m / 3).factorial : ℝ) - Real.log ((m / 5).factorial : ℝ) +
      Real.log ((m / 30).factorial : ℝ) ≤ Aconst * m + 4 * Real.log m + 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h2 := log_factorial_div_ge m 2 (by norm_num) (by omega)
  have h3 := log_factorial_div_ge m 3 (by norm_num) (by omega)
  have h5 := log_factorial_div_ge m 5 (by norm_num) (by omega)
  have hm1 := (Lemma51Nat.log_factorial_bounds m (by omega)).2
  set q := m / 30
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by norm_num)).mpr hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h30 := (Lemma51Nat.log_factorial_bounds q hq1).2
  have hqt : (q : ℝ) ≤ (m : ℝ) / 30 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self m 30
  have hg30 := g_mono (by exact_mod_cast hq1) hqt
  have hlq : Real.log q ≤ Real.log m :=
    Real.log_le_log hq0 (by exact_mod_cast Nat.div_le_self m 30)
  have hl : ∀ k : ℝ, 0 < k → Real.log ((m : ℝ) / k) = Real.log m - Real.log k :=
    fun k hk => Real.log_div hm0.ne' hk.ne'
  have hl2 := hl 2 (by norm_num)
  have hl3 := hl 3 (by norm_num)
  have hl5 := hl 5 (by norm_num)
  have hl30 := hl 30 (by norm_num)
  have h30' : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hl2p : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3p : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl5p : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hq30 : (q : ℝ) * Real.log q - q ≤ (m : ℝ) / 30 * Real.log ((m : ℝ) / 30) - m / 30 :=
    hg30
  unfold g at h2 h3 h5
  push_cast at h2 h3 h5
  rw [hl2] at h2; rw [hl3] at h3; rw [hl5] at h5; rw [hl30, h30'] at hq30
  unfold Aconst
  nlinarith

lemma neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) 3
  rw [abs_of_nonneg hx0] at h
  have h2 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2
  linarith

lemma log_three_le : Real.log 3 ≤ 1.113 := by
  have h := neg_log_one_sub_le (x := 1 / 3) (by norm_num) (by norm_num)
  have e : Real.log 3 = Real.log 2 - Real.log (1 - 1 / 3) := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    ring
  have := Real.log_two_lt_d9
  norm_num at h
  rw [e]; norm_num; linarith

lemma log_five_le : Real.log 5 ≤ 1.611 := by
  have h := neg_log_one_sub_le (x := 1 / 5) (by norm_num) (by norm_num)
  have e : Real.log 5 = 2 * Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have := Real.log_two_lt_d9
  norm_num at h
  rw [e]; norm_num; linarith

lemma Aconst_le : Aconst ≤ 0.926 := by
  unfold Aconst
  have := Real.log_two_lt_d9
  have := log_three_le
  have := log_five_le
  norm_num at *
  linarith

lemma Aconst_nonneg : 0 ≤ Aconst := by
  unfold Aconst
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
  positivity

/-- **Chebyshev's step**: `ψ(x) - ψ(x/6) ≤ 0.926 x + 4 log x + 43` for every `x ≥ 1`. -/
theorem psi_sub_psi_sixth_le {x : ℝ} (hx : 1 ≤ x) :
    ψ x - ψ (x / 6) ≤ 0.926 * x + 4 * Real.log x + 43 := by
  set m := ⌊x⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hx)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hψx : ψ x = ψ (m : ℝ) := psi_eq_psi_coe_floor x
  have hψ6 : ψ (x / 6) = ψ ((m / 6 : ℕ) : ℝ) := by
    rw [psi_eq_psi_coe_floor (x / 6)]
    have := Nat.floor_div_natCast x 6
    push_cast at this
    rw [this]
  rw [hψx, hψ6]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases lt_or_ge m 30 with hm | hm
  · -- small `m`: `ψ(m) ≤ 1.42 m < 43`
    have h1 := BSCert.FiniteN.psi_le_one_point_four_two (x := (m : ℝ)) (Nat.cast_nonneg m)
    have h2 := Chebyshev.psi_nonneg ((m / 6 : ℕ) : ℝ)
    have : (m : ℝ) ≤ 29 := by exact_mod_cast (by omega : m ≤ 29)
    linarith
  · have h1 := psi_sub_le_comb m
    simp only [BSCert.FiniteN.chebL_eq_log_factorial] at h1
    have h2 := comb_le m hm
    have h3 := Aconst_le
    have h4 : Real.log m ≤ Real.log x := Real.log_le_log (by positivity) hmx
    have h5 : Aconst * m ≤ 0.926 * x := by
      have := Aconst_nonneg
      calc Aconst * m ≤ 0.926 * m := by gcongr
        _ ≤ 0.926 * x := by gcongr
    linarith

/-- Summing Chebyshev's step over the blocks `(x/6^{k+1}, x/6^k]`. -/
lemma psi_le_geom {z : ℝ} (hz : 1 ≤ z) :
    ∀ n : ℕ, ∀ x, 0 ≤ x → x < 6 ^ n → x ≤ z →
      ψ x ≤ 1.1112 * x + n * (4 * Real.log z + 43) := by
  have hlz : 0 ≤ Real.log z := Real.log_nonneg hz
  intro n
  induction n with
  | zero =>
    intro x hx0 hx _
    simp only [pow_zero] at hx
    rw [psi_eq_zero_of_lt_two (by linarith)]; simp; linarith
  | succ n ih =>
    intro x hx0 hx hxz
    by_cases h1 : 1 ≤ x
    · have hx6 : x / 6 < 6 ^ n := by rw [pow_succ] at hx; linarith
      have h := ih (x / 6) (by linarith) hx6 (by linarith)
      have hs := psi_sub_psi_sixth_le h1
      have hl : Real.log x ≤ Real.log z := Real.log_le_log (by linarith) hxz
      push_cast
      nlinarith
    · push_neg at h1
      rw [psi_eq_zero_of_lt_two (by linarith)]
      positivity

/-- **Chebyshev's upper bound**: `ψ(x) ≤ 1.1112 x + (log x + 1)(4 log x + 43)` for `x ≥ 1`. -/
theorem psi_le {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ 1.1112 * x + (Real.log x + 1) * (4 * Real.log x + 43) := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl6 : 1 < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  set n := ⌊Real.log x / Real.log 6⌋₊ + 1
  have hn : x < 6 ^ n := by
    have h1 : Real.log x / Real.log 6 < n := by
      have := Nat.lt_floor_add_one (Real.log x / Real.log 6)
      push_cast [n]; exact this
    have h2 : Real.log x < n * Real.log 6 := by
      rwa [div_lt_iff₀ (by linarith)] at h1
    rw [← Real.log_lt_log_iff (by linarith) (by positivity), Real.log_pow]
    exact h2
  have hn' : (n : ℝ) ≤ Real.log x + 1 := by
    have h1 : (⌊Real.log x / Real.log 6⌋₊ : ℝ) ≤ Real.log x / Real.log 6 :=
      Nat.floor_le (by positivity)
    have h2 : Real.log x / Real.log 6 ≤ Real.log x := div_le_self hlx hl6.le
    push_cast [n]; linarith
  have h := psi_le_geom hx n x (by linarith) hn le_rfl
  have : (n : ℝ) * (4 * Real.log x + 43) ≤ (Real.log x + 1) * (4 * Real.log x + 43) :=
    mul_le_mul_of_nonneg_right hn' (by positivity)
  linarith

/-- **`π(X) ≤ 1.26 X / log X`** for `log X ≥ 10⁸` (the Rosser–Schoenfeld bound used in
Lemma 6.22(c), in the paper's range). -/
theorem primesBelow_card_le {X : ℕ} (hX : 10 ^ 8 ≤ Real.log X) :
    (X.primesBelow.card : ℝ) ≤ 1.26 * X / Real.log X := by
  have hX0 : (0 : ℝ) < X := by
    rcases (Nat.cast_nonneg X : (0 : ℝ) ≤ X).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  set L := Real.log X with hL
  have hL0 : 0 < L := by linarith
  have hXe : (X : ℝ) = Real.exp L := (Real.exp_log hX0).symm
  set Y := (X : ℝ) ^ (0.95 : ℝ) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hlogY : Real.log Y = 0.95 * L := by rw [hY, Real.log_rpow hX0]
  -- split the primes below `X` at `Y`
  set S1 := X.primesBelow.filter (fun p : ℕ => (p : ℝ) ≤ Y)
  set S2 := X.primesBelow.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y)
  have hsplit : X.primesBelow.card = S1.card + S2.card :=
    (Finset.card_filter_add_card_filter_not (fun p : ℕ => (p : ℝ) ≤ Y)).symm
  have hS1 : (S1.card : ℝ) ≤ Y := by
    have hsub : S1 ⊆ Ioc 0 ⌊Y⌋₊ := by
      intro p hp
      simp only [S1, mem_filter, Nat.mem_primesBelow] at hp
      simp only [mem_Ioc]
      exact ⟨hp.1.2.pos, Nat.le_floor hp.2⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Ioc, tsub_zero] at this
    calc (S1.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ Y := Nat.floor_le hY0.le
  have hS2 : (S2.card : ℝ) * (0.95 * L) ≤ ψ X := by
    have h1 : (S2.card : ℝ) * (0.95 * L) ≤ ∑ p ∈ S2, Real.log p := by
      rw [← nsmul_eq_mul]
      apply Finset.card_nsmul_le_sum
      intro p hp
      simp only [S2, mem_filter, not_le] at hp
      rw [← hlogY]
      exact Real.log_le_log hY0 hp.2.le
    have h2 : ∑ p ∈ S2, Real.log p ≤ θ X := by
      unfold Chebyshev.theta
      rw [Nat.floor_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [S2, mem_filter, Nat.mem_primesBelow] at hp
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨hp.1.2.pos, hp.1.1.le⟩, hp.1.2⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    linarith [Chebyshev.theta_le_psi (X : ℝ)]
  have hψ := psi_le (x := (X : ℝ)) (by
    rw [hXe]; exact Real.one_le_exp (by linarith))
  -- the error terms
  have hY_le : Y ≤ 0.045 * X / L := by
    have e : Y = X * Real.exp (-(0.05 * L)) := by
      rw [hY, Real.rpow_def_of_pos hX0, hXe, ← Real.exp_add, Real.log_exp]; ring_nf
    have hexp : 23 * L ≤ Real.exp (0.05 * L) := by
      have := Real.pow_div_factorial_le_exp (0.05 * L) (by positivity) 2
      norm_num [Nat.factorial] at this
      nlinarith
    rw [e, le_div_iff₀ hL0, Real.exp_neg]
    have hE := Real.exp_pos (0.05 * L)
    rw [mul_assoc, mul_comm (Real.exp (0.05 * L))⁻¹, ← mul_assoc, ← div_eq_mul_inv,
      div_le_iff₀ hE]
    nlinarith
  have hpoly : (L + 1) * (4 * L + 43) ≤ 0.04 * X / L := by
    have hexp : L ^ 4 / 24 ≤ Real.exp L := by
      have := Real.pow_div_factorial_le_exp L hL0.le 4
      norm_num [Nat.factorial] at this; linarith
    have h1 : (L + 1) * (4 * L + 43) ≤ 5 * L ^ 2 := by nlinarith
    have h2 : (L + 1) * (4 * L + 43) * L ≤ 5 * L ^ 3 := by
      have := mul_le_mul_of_nonneg_right h1 hL0.le
      nlinarith
    have h3 : 5 * L ^ 3 ≤ 0.04 * (L ^ 4 / 24) := by
      have : 0 ≤ L ^ 3 := by positivity
      nlinarith
    rw [le_div_iff₀ hL0, hXe]
    nlinarith
  rw [hsplit]
  push_cast
  have hS2' : (S2.card : ℝ) ≤ ψ X / (0.95 * L) := by
    rw [le_div_iff₀ (by positivity)]; exact hS2
  have h3 : ψ X / (0.95 * L) ≤ (1.1112 * X + 0.04 * X / L) / (0.95 * L) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h4 : (1.1112 * X + 0.04 * X / L) / (0.95 * L) ≤ 1.215 * X / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    have : 0.04 * X / L ≤ 0.04 * X / 1 := by
      apply div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
    nlinarith
  have h5 : 1.215 * (X : ℝ) / L + 0.045 * X / L = 1.26 * X / L := by ring
  linarith

end ChebyshevUpper

namespace SmoothTails

/-- **Lemma 6.22(c), second part**, in the paper's range `log X₀ ≥ 10⁸`, with no hypothesis on
`π(X₀)`: for `Y > 0` with `log Y ≥ 2`, `Ψ(Y, X₀) ≤ exp(1.26 X₀ log(2 log Y) / log X₀)`. -/
theorem smooth_tail_count_large {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {Y : ℝ} (hY0 : 0 < Y)
    (hY : 2 ≤ Real.log Y) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤
      Real.exp (1.26 * X₀ * Real.log (2 * Real.log Y) / Real.log X₀) := by
  have hX2 : 2 ≤ X₀ := by
    by_contra h
    push_neg at h
    have : (X₀ : ℝ) ≤ 1 := by exact_mod_cast (by omega : X₀ ≤ 1)
    rcases (Nat.cast_nonneg X₀ : (0 : ℝ) ≤ X₀).lt_or_eq with h0 | h0
    · have := Real.log_le_sub_one_of_pos h0; linarith
    · rw [← h0, Real.log_zero] at hX; norm_num at hX
  exact smooth_tail_count hX2 hY0 hY (ChebyshevUpper.primesBelow_card_le hX)

end SmoothTails
