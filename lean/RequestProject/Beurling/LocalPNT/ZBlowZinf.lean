module

public import RequestProject.Beurling.LocalPNT.ZBlowEin
public import RequestProject.Beurling.Mertens
public import RequestProject.Beurling.Lemma51NatFull

/-!
# Lemma 4.3: `Z_∞(σ)` slightly left of `σ = 1`

For `σ ≥ 1 - a/Λ` (`Λ = log X₀ ≥ 10⁸`, `0 < a ≤ 8`) we prove
`Z_∞(σ) ≤ Z_∞(1) e^{Ein(a) + 1/2}` (`ZinfR_le_exp_Ein`), the estimate behind the factor
`e^{Ein(a)}` of Lemma 4.3.

With `δ = a/Λ`, each Euler factor satisfies `(1 - p^{-σ})^{-1} ≤ (1 - p^{-1})^{-1} e^{F_p}`,
`F_p = (p^δ - 1)/(p - p^δ) = (p^δ - 1)/p + (p^δ - 1)p^δ/(p(p - p^δ))`.

* The main part: `p^δ - 1 = (log p/p)·w(p)` with the non-decreasing weight
  `w(n) = δ·(e^{δ log n} - 1)/(δ log n)`. Abel summation against Mertens' first theorem in the
  elementary form `log n - 6 ≤ ∑_{p≤n} log p/p ≤ log n + log 4` (`sum_log_div_ge`,
  `Mertens.sum_log_div_le`) bounds `∑_{p<X₀} (p^δ - 1)/p` by
  `∑_{n<X₀} (log(n+1) - log n) w(n) + 8.1 w(X₀)`, and the first sum is a lower Riemann sum of
  `∫_0^a (e^t - 1)/t dt = Ein(a)`.
* The second-order part is at most `5 w_max e^a/(1 - w_max)`, `w_max = (e^a - 1)/Λ ≤ 3·10⁻⁵`,
  by `∑_p log p/(p(p-1)) ≤ 5` (`Mertens.sum_log_div_mul_pred_le`).
-/

@[expose] public section

open Real Finset

namespace LocalPNT

/-! ### Abel summation with partial sums bounded below -/

/-- If `w` is non-decreasing and the partial sums `B(n) = ∑_{k=1}^n b_k` are `≥ -L`, then
`∑_{k=1}^N b_k w_k ≤ B(N) w_N + L (w_N - w_1)`. -/
lemma abel_le (b w : ℕ → ℝ) {L : ℝ} (hw : ∀ k ≥ 1, w k ≤ w (k + 1))
    (hB : ∀ n ≥ 1, -L ≤ ∑ k ∈ Icc 1 n, b k) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Icc 1 N, b k * w k ≤ (∑ k ∈ Icc 1 N, b k) * w N + L * (w N - w 1) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 := hB M hM
    have h2 := hw M hM
    nlinarith

lemma sum_log_succ_sub (n : ℕ) :
    ∑ k ∈ Icc 1 n, (Real.log ((k : ℝ) + 1) - Real.log k) = Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

lemma sum_primesBelow_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (N + 1).primesBelow, f p = ∑ k ∈ Icc 1 N, if k.Prime then f k else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Nat.mem_primesBelow, mem_filter, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
  · rintro ⟨⟨_, h3⟩, h2⟩; exact ⟨by omega, h2⟩

lemma sum_primeLogWeight_eq (n : ℕ) :
    ∑ k ∈ Icc 1 n, Mertens.primeLogWeight k = ∑ p ∈ (n + 1).primesBelow, Real.log p / p := by
  rw [sum_primesBelow_eq_Icc]; rfl

/-- Mertens' first theorem, lower bound: `∑_{p ≤ n} log p/p ≥ log n - 6`, from
`n log n - n ≤ log n! = ∑_{p ≤ n} v_p(n!) log p`, `v_p(n!) ≤ n/(p-1)` and
`∑_p log p/(p(p-1)) ≤ 5`. -/
lemma sum_log_div_ge {n : ℕ} (hn : 1 ≤ n) :
    Real.log n - 6 ≤ ∑ p ∈ (n + 1).primesBelow, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac := (Lemma51Nat.log_factorial_bounds n hn).1
  have hlog : Real.log (n.factorial : ℝ) ≤
      ∑ p ∈ (n + 1).primesBelow, (n : ℝ) * (Real.log p / (p - 1)) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := (n + 1).primesBelow) ?_ ?_).trans ?_
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).mp hp.2.1), hp.1⟩
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    · refine Finset.sum_le_sum fun p hp => ?_
      have hpp := (Nat.mem_primesBelow.mp hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have h1 : ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / (p - 1) := by
        calc ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
              exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
          _ ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
          _ = (n : ℝ) / (p - 1) := by rw [Nat.cast_sub hpp.one_lt.le, Nat.cast_one]
      calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤
            (n : ℝ) / (p - 1) * Real.log p :=
            mul_le_mul_of_nonneg_right h1 (Real.log_natCast_nonneg p)
        _ = _ := by ring
  have hsplit : ∀ p ∈ (n + 1).primesBelow,
      Real.log p / ((p : ℝ) - 1) = Real.log p / p + Real.log p / (p * (p - 1)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [← Finset.mul_sum, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib] at hlog
  have h5 := Mertens.sum_log_div_mul_pred_le n
  have : (n : ℝ) * (Real.log n - 1) ≤
      (n : ℝ) * (∑ p ∈ (n + 1).primesBelow, Real.log p / p + 5) := by
    nlinarith
  have := le_of_mul_le_mul_left this hn0
  linarith

/-- The sum of the integrals over `[δ log k, δ log (k+1)]`, `1 ≤ k ≤ n`. -/
lemma sum_integral_log (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ∫ t in δ * Real.log k..δ * Real.log ((k : ℝ) + 1), einDens t =
      ∫ t in (0 : ℝ)..δ * Real.log ((n : ℝ) + 1), einDens t := by
  have hl : ∀ x : ℝ, 0 ≤ x → 0 ≤ δ * Real.log (x + 1) := fun x hx =>
    mul_nonneg hδ (Real.log_nonneg (by linarith))
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_einDens le_rfl (hl _ (Nat.cast_nonneg n)))
      (intervalIntegrable_einDens (hl _ (Nat.cast_nonneg n)) (hl _ (by positivity)))

/-! ### The Euler factors -/

/-- `(1 - p^{-σ})^{-1} ≤ (1 - p^{-1})^{-1} e^{(p^δ - 1)/(p - p^δ)}` for `σ ≥ 1 - δ`. -/
lemma factor_le_exp {p : ℕ} (hp : p.Prime) {δ σ : ℝ} (hδ1 : δ < 1)
    (hσ : 1 - δ ≤ σ) :
    (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ * Real.exp (((p : ℝ) ^ δ - 1) / (p - (p : ℝ) ^ δ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hu : (p : ℝ) ^ δ < p := by
    calc (p : ℝ) ^ δ < (p : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hδ1
      _ = p := Real.rpow_one _
  have hq : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ δ / p := by
    rw [← Real.rpow_sub_one hp0.ne']
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hQ : 0 < 1 - (p : ℝ) ^ δ / p := by
    rw [sub_pos, div_lt_one hp0]; exact hu
  have hpu : 0 < (p : ℝ) - (p : ℝ) ^ δ := by linarith
  rw [Real.rpow_neg_one]
  calc (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ (1 - (p : ℝ) ^ δ / p)⁻¹ := inv_anti₀ hQ (by linarith)
    _ = (1 - (p : ℝ)⁻¹)⁻¹ * (((p : ℝ) ^ δ - 1) / (p - (p : ℝ) ^ δ) + 1) := by
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
    _ ≤ _ := by
        have h3 : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
          apply inv_pos.mpr
          rw [sub_pos, inv_lt_one₀ hp0]; linarith
        exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) h3.le

/-! ### The main estimate -/

lemma exp_eight_le : Real.exp 8 ≤ 2981 := by
  have h : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
    _ ≤ 2981 := by norm_num

/-- `∑_{p<X₀} (p^δ - 1)/(p - p^δ) ≤ Ein(a) + 1/2` for `δ = a/Λ`. -/
theorem sum_F_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 8) :
    ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ (a / Real.log X₀) - 1) /
      (p - (p : ℝ) ^ (a / Real.log X₀)) ≤ Ein a + 1 / 2 := by
  have h3 := Mertens.three_le_of_log (X₀ := X₀) (by linarith)
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  set δ := a / Λ with hδ
  have hδ0 : 0 < δ := div_pos ha hΛ0
  have hδΛ : δ * Λ = a := by rw [hδ]; field_simp
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one hΛ0]; linarith
  set E := Real.exp a with hE
  have hE8 : E ≤ 2981 := (Real.exp_le_exp.mpr ha8).trans exp_eight_le
  have hE1 : 1 ≤ E := Real.one_le_exp ha.le
  set wm := (E - 1) / Λ with hwm
  have hwm0 : 0 ≤ wm := div_nonneg (by linarith) hΛ0.le
  have hwm1 : wm ≤ 3 / 10 ^ 5 := by
    rw [hwm, div_le_iff₀ hΛ0]; nlinarith
  have hδE : δ * einDens a = wm := by
    rw [hδ, hwm, einDens]; field_simp; rfl
  obtain ⟨N, hN⟩ : ∃ N, X₀ = N + 1 := ⟨X₀ - 1, by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hXN : (X₀ : ℝ) = N + 1 := by rw [hN]; push_cast; ring
  -- facts on the primes below `X₀`
  have hfact : ∀ p ∈ X₀.primesBelow, 2 ≤ (p : ℝ) ∧ 0 < δ * Real.log p ∧ δ * Real.log p ≤ a ∧
      (p : ℝ) ^ δ = Real.exp (δ * Real.log p) := by
    intro p hp
    obtain ⟨hpX, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    refine ⟨hp2, mul_pos hδ0 hlp, ?_, by rw [Real.rpow_def_of_pos (by linarith), mul_comm]⟩
    rw [← hδΛ]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith)
      (by exact_mod_cast hpX.le)) hδ0.le
  -- `p^δ - 1 ≤ w_max log p` and `p^δ ≤ e^a`
  have hu1 : ∀ p ∈ X₀.primesBelow, (p : ℝ) ^ δ - 1 ≤ wm * Real.log p := by
    intro p hp
    obtain ⟨_, hx0, hxa, hu⟩ := hfact p hp
    rw [hu]
    have e : Real.exp (δ * Real.log p) - 1 = (δ * Real.log p) * einDens (δ * Real.log p) := by
      rw [einDens, mul_div_cancel₀ _ hx0.ne']
    rw [e, ← hδE]
    calc δ * Real.log p * einDens (δ * Real.log p) ≤ δ * Real.log p * einDens a :=
          mul_le_mul_of_nonneg_left (einDens_monotoneOn (Set.mem_Ici.mpr hx0.le)
            (Set.mem_Ici.mpr ha.le) hxa) hx0.le
      _ = _ := by ring
  have hu2 : ∀ p ∈ X₀.primesBelow, 1 ≤ (p : ℝ) ^ δ ∧ (p : ℝ) ^ δ ≤ E := by
    intro p hp
    obtain ⟨hp2, _, hxa, hu⟩ := hfact p hp
    exact ⟨Real.one_le_rpow (by linarith) hδ0.le, by rw [hu]; exact Real.exp_le_exp.mpr hxa⟩
  -- the decomposition `F_p = (p^δ - 1)/p + excess`
  have hsplit : ∀ p ∈ X₀.primesBelow, ((p : ℝ) ^ δ - 1) / (p - (p : ℝ) ^ δ) =
      ((p : ℝ) ^ δ - 1) / p + ((p : ℝ) ^ δ - 1) * (p : ℝ) ^ δ / (p * (p - (p : ℝ) ^ δ)) := by
    intro p hp
    obtain ⟨hp2, _, _, _⟩ := hfact p hp
    have hlt : (p : ℝ) ^ δ < p := by
      calc (p : ℝ) ^ δ < (p : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hδ1
        _ = p := Real.rpow_one _
    have h1 : (p : ℝ) - (p : ℝ) ^ δ ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the second-order part
  have hexc : ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ δ - 1) * (p : ℝ) ^ δ / (p * (p - (p : ℝ) ^ δ)) ≤
      wm * E / (1 - wm) * 5 := by
    have hb : ∀ p ∈ X₀.primesBelow, ((p : ℝ) ^ δ - 1) * (p : ℝ) ^ δ / (p * (p - (p : ℝ) ^ δ)) ≤
        wm * E / (1 - wm) * (Real.log p / (p * (p - 1))) := by
      intro p hp
      obtain ⟨hp2, _, _, _⟩ := hfact p hp
      have h1 := hu1 p hp
      obtain ⟨h2, h3⟩ := hu2 p hp
      have hlog : Real.log p ≤ p - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hden : ((p : ℝ) - 1) * (1 - wm) ≤ p - (p : ℝ) ^ δ := by nlinarith
      have hden0 : 0 < ((p : ℝ) - 1) * (1 - wm) := mul_pos (by linarith) (by linarith)
      calc ((p : ℝ) ^ δ - 1) * (p : ℝ) ^ δ / (p * (p - (p : ℝ) ^ δ)) ≤
            (wm * Real.log p * E) / (p * (((p : ℝ) - 1) * (1 - wm))) := by
            apply div_le_div₀ (by positivity)
              (mul_le_mul h1 h3 (by linarith) (by positivity)) (by positivity)
            exact mul_le_mul_of_nonneg_left hden (by linarith)
        _ = _ := by
            have : (1 : ℝ) - wm ≠ 0 := by linarith
            have : (p : ℝ) - 1 ≠ 0 := by linarith
            have : (p : ℝ) ≠ 0 := by linarith
            field_simp
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have h5 := Mertens.sum_log_div_mul_pred_le N
    rw [← hN] at h5
    exact mul_le_mul_of_nonneg_left h5 (div_nonneg (by positivity) (by linarith))
  -- the main part, by Abel summation
  set w : ℕ → ℝ := fun n => δ * einDens (δ * Real.log n) with hw
  have hlogn : ∀ n : ℕ, 0 ≤ δ * Real.log n := fun n =>
    mul_nonneg hδ0.le (Real.log_natCast_nonneg n)
  have hwmono : ∀ k ≥ 1, w k ≤ w (k + 1) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [hw]
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    apply einDens_monotoneOn (Set.mem_Ici.mpr (hlogn k)) (Set.mem_Ici.mpr (hlogn (k + 1)))
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    exact Real.log_le_log (by linarith) (by push_cast; linarith)
  have hw1 : w 1 = 0 := by simp [hw, einDens]
  have hwN : w N ≤ wm := by
    rw [← hδE]
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    apply einDens_monotoneOn (Set.mem_Ici.mpr (hlogn N)) (Set.mem_Ici.mpr ha.le)
    rw [← hδΛ]
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    exact Real.log_le_log (by exact_mod_cast hN1) (by rw [hXN]; linarith)
  have hwN0 : 0 ≤ w N := mul_nonneg hδ0.le (einDens_nonneg (hlogn N))
  have hmain_eq : ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ δ - 1) / p =
      ∑ k ∈ Icc 1 N, Mertens.primeLogWeight k * w k := by
    rw [hN, sum_primesBelow_eq_Icc]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold Mertens.primeLogWeight
    split_ifs with hk'
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk'.two_le
      have hlk : 0 < Real.log k := Real.log_pos (by linarith)
      simp only [hw, einDens]
      rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log k) δ]
      field_simp
    · simp
  -- `B(n) = ∑_{k≤n} (a_k - (log(k+1) - log k)) ∈ [-6.7, log 4]`
  set b : ℕ → ℝ := fun k => Mertens.primeLogWeight k - (Real.log ((k : ℝ) + 1) - Real.log k)
    with hb
  have hBeq : ∀ n, ∑ k ∈ Icc 1 n, b k =
      ∑ p ∈ (n + 1).primesBelow, Real.log p / p - Real.log ((n : ℝ) + 1) := by
    intro n
    rw [Finset.sum_sub_distrib, sum_primeLogWeight_eq, sum_log_succ_sub]
  have hBlow : ∀ n ≥ 1, -6.7 ≤ ∑ k ∈ Icc 1 n, b k := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hBeq]
    have h1 := sum_log_div_ge hn
    have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have h3 := Real.log_two_lt_d9
    linarith
  have hBN : ∑ k ∈ Icc 1 N, b k ≤ 1.3863 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [hBeq]
    have h1 := Mertens.sum_log_div_le hN1
    have h3 : Real.log 4 ≤ 1.3863 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have h2 : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have habel := abel_le b w hwmono hBlow hN1
  rw [hw1] at habel
  have hint : ∑ k ∈ Icc 1 N, (Real.log ((k : ℝ) + 1) - Real.log k) * w k ≤ Ein a := by
    have hle : ∀ k ∈ Icc 1 N, (Real.log ((k : ℝ) + 1) - Real.log k) * w k ≤
        ∫ t in δ * Real.log k..δ * Real.log ((k : ℝ) + 1), einDens t := by
      intro k hk
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hl1 : δ * Real.log k ≤ δ * Real.log ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hδ0.le
      have hl0 : 0 ≤ δ * Real.log ((k : ℝ) + 1) :=
        mul_nonneg hδ0.le (Real.log_nonneg (by linarith))
      have h := intervalIntegral.integral_mono_on hl1 intervalIntegrable_const
        (intervalIntegrable_einDens (hlogn k) hl0)
        (fun x hx => einDens_monotoneOn (Set.mem_Ici.mpr (hlogn k))
          (Set.mem_Ici.mpr ((hlogn k).trans hx.1)) hx.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      calc (Real.log ((k : ℝ) + 1) - Real.log k) * w k =
            (δ * Real.log ((k : ℝ) + 1) - δ * Real.log k) * einDens (δ * Real.log k) := by
            simp only [hw]; ring
        _ ≤ _ := h
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [sum_integral_log δ hδ0.le N, ← hXN, ← hΛ, hδΛ, Ein_eq]
  have hsum : ∑ k ∈ Icc 1 N, Mertens.primeLogWeight k * w k =
      ∑ k ∈ Icc 1 N, b k * w k +
        ∑ k ∈ Icc 1 N, (Real.log ((k : ℝ) + 1) - Real.log k) * w k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [hb]; ring
  have hmain : ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ δ - 1) / p ≤ Ein a + 8.1 * wm := by
    rw [hmain_eq, hsum]
    have : (∑ k ∈ Icc 1 N, b k) * w N ≤ 1.3863 * w N := mul_le_mul_of_nonneg_right hBN hwN0
    linarith
  -- numerics: `8.1 w_max + 5 w_max e^a/(1 - w_max) ≤ 1/2`
  have hnum : 8.1 * wm + wm * E / (1 - wm) * 5 ≤ 1 / 2 := by
    have hwE : wm * E ≤ 2981 ^ 2 / 10 ^ 8 := by
      rw [hwm, div_mul_eq_mul_div, div_le_div_iff₀ hΛ0 (by norm_num)]
      have : (E - 1) * E ≤ 2981 ^ 2 := by nlinarith
      nlinarith
    have h1 : wm * E / (1 - wm) ≤ (2981 ^ 2 / 10 ^ 8) / (1 - 3 / 10 ^ 5) :=
      div_le_div₀ (by norm_num) hwE (by norm_num) (by linarith)
    have h2 : (2981 ^ 2 / 10 ^ 8 : ℝ) / (1 - 3 / 10 ^ 5) * 5 + 8.1 * (3 / 10 ^ 5) ≤ 1 / 2 := by
      norm_num
    linarith
  linarith

/-- **`Z_∞` left of `σ = 1`** (Lemma 4.3): for `σ ≥ 1 - a/Λ`, `0 < a ≤ 8`, `Λ = log X₀ ≥ 10⁸`,
`Z_∞(σ) ≤ Z_∞(1) e^{Ein(a) + 1/2}`. -/
theorem ZinfR_le_exp_Ein {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {a σ : ℝ} (ha : 0 < a)
    (ha8 : a ≤ 8) (hσ : 1 - a / Real.log X₀ ≤ σ) :
    BaseFactor.ZinfR X₀ σ ≤ BaseFactor.ZinfR X₀ 1 * Real.exp (Ein a + 1 / 2) := by
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hδ1 : a / Real.log X₀ < 1 := by rw [div_lt_one hΛ0]; linarith
  have hσ0 : 0 < σ := by linarith
  calc BaseFactor.ZinfR X₀ σ ≤ ∏ p ∈ X₀.primesBelow, ((1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ *
        Real.exp (((p : ℝ) ^ (a / Real.log X₀) - 1) / (p - (p : ℝ) ^ (a / Real.log X₀)))) := by
        unfold BaseFactor.ZinfR
        apply Finset.prod_le_prod
        · intro p hp
          exact (BaseFactor.factor_pos (Nat.mem_primesBelow.mp hp).2 hσ0).le
        · intro p hp
          exact factor_le_exp (Nat.mem_primesBelow.mp hp).2 hδ1 hσ
    _ = BaseFactor.ZinfR X₀ 1 * Real.exp (∑ p ∈ X₀.primesBelow,
          ((p : ℝ) ^ (a / Real.log X₀) - 1) / (p - (p : ℝ) ^ (a / Real.log X₀))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]; rfl
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sum_F_le hX ha ha8))
        exact (BaseFactor.ZinfR_pos X₀ one_pos).le

end LocalPNT

end
