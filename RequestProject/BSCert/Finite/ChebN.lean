module

public import RequestProject.BSCert.Finite.CMCert

/-!
# Lemma 5.1(i) for `ℕ` in full: `ψ(x) - ψ(x/2) ≤ 0.71 x` and `ψ(x) ≤ 1.42 x`

The paper (proof of Lemma 5.1(i), last paragraph) says that for the integers
`ψ(x) - ψ(x/2) ≤ x log 2 + 3 log x + 3 ≤ 0.71 x` for `x ≥ 1500`, and that a direct computation
(line 1 of `finite_checks.py`) covers `x < 1500`. Here the analytic part is proved with the
classical Chebyshev argument (`log m! = ∑_{d ≤ m} Λ(d) ⌊m/d⌋` and central binomial
coefficients), which gives the slightly stronger `ψ(x) - ψ(x/2) ≤ x log 2 + log x`; combined
with `psi_sub_psi_half_le_small` and `cm1_tail` this gives Lemma 5.1(i) for `ℕ`.
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction Chebyshev

/-- `L(m) = ∑_{d ≤ m} Λ(d) ⌊m/d⌋`. -/
noncomputable def chebL (m : ℕ) : ℝ := ∑ d ∈ range (m + 1), Λ d * ((m / d : ℕ) : ℝ)

lemma chebL_eq_log_factorial (m : ℕ) : chebL m = Real.log (m.factorial : ℝ) := by
  induction m with
  | zero => simp [chebL]
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ← ih]
    unfold chebL
    have hsplit : ∀ d, Λ d * (((m + 1) / d : ℕ) : ℝ) =
        Λ d * ((m / d : ℕ) : ℝ) + (if d ∣ m + 1 then Λ d else 0) := by
      intro d
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_add_distrib,
      Finset.sum_range_succ (fun d => Λ d * ((m / d : ℕ) : ℝ)) (m + 1),
      Nat.div_eq_of_lt (Nat.lt_succ_self m)]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hdiv : ∑ d ∈ range (m + 2), (if d ∣ m + 1 then Λ d else 0) =
        ∑ d ∈ (m + 1).divisors, Λ d := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [mem_filter, mem_range, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, _⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) h), h⟩
    rw [hdiv, vonMangoldt_sum]
    push_cast
    ring

/-- `log m! - 2 log (m/2)! ≤ m log 2 + log m` for `m ≥ 1`. -/
lemma log_factorial_sub_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ) - 2 * Real.log ((m / 2).factorial : ℝ) ≤
      m * Real.log 2 + Real.log m := by
  set k := m / 2
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hC : ((2 * k + 1).choose k : ℝ) ≤ 4 ^ k := by exact_mod_cast Nat.choose_middle_le_pow k
  have hk0 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h4 : Real.log ((4 : ℝ) ^ k) = 2 * k * Real.log 2 := by
    rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hkj : k = j := by omega
    have hm2 : m = 2 * k := by omega
    have hfac : (m.factorial : ℝ) = ((2 * k).choose k : ℝ) * k.factorial * k.factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      rw [show 2 * k - k = k by omega] at this
      rw [hm2]; exact_mod_cast this.symm
    have hC' : ((2 * k).choose k : ℝ) ≤ 4 ^ k := by
      have := Nat.choose_le_succ (2 * k) k
      exact le_trans (by exact_mod_cast this) hC
    have hCpos : (0 : ℝ) < ((2 * k).choose k : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [hfac, Real.log_mul (by positivity) hk0.ne', Real.log_mul hCpos.ne' hk0.ne']
    have := Real.log_le_log hCpos hC'
    rw [h4] at this
    have hmk : (m : ℝ) * Real.log 2 = 2 * k * Real.log 2 := by
      rw [show (m : ℝ) = 2 * k by exact_mod_cast hm2]
    linarith
  · have hkj : k = j := by omega
    have hm2 : m = 2 * k + 1 := by omega
    have hfac : (m.factorial : ℝ) =
        ((2 * k + 1).choose k : ℝ) * k.factorial * k.factorial * (k + 1) := by
      have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k + 1 by omega)
      rw [show 2 * k + 1 - k = k + 1 by omega, Nat.factorial_succ] at this
      rw [hm2]
      have h' : ((2 * k + 1).factorial : ℝ) =
          ((2 * k + 1).choose k : ℝ) * k.factorial * ((k + 1) * k.factorial) := by
        exact_mod_cast this.symm
      rw [h']; ring
    have hCpos : (0 : ℝ) < ((2 * k + 1).choose k : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hk0.ne',
      Real.log_mul hCpos.ne' hk0.ne']
    have := Real.log_le_log hCpos hC
    rw [h4] at this
    have hk1 : Real.log ((k : ℝ) + 1) ≤ Real.log m :=
      Real.log_le_log (by positivity) (by rw [hm2]; push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    have hmk : (m : ℝ) = 2 * k + 1 := by exact_mod_cast hm2
    rw [hmk] at hk1 ⊢
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- `ψ(m) - ψ(m/2) ≤ L(m) - 2 L(m/2)`. -/
lemma psi_diff_le_chebL (m : ℕ) :
    ψ (m : ℝ) - ψ ((m / 2 : ℕ) : ℝ) ≤ chebL m - 2 * chebL (m / 2) := by
  set k := m / 2
  have hkm : k ≤ m := Nat.div_le_self m 2
  rw [psi_natCast, psi_natCast, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le k) hkm,
    add_sub_cancel_left]
  -- extend `L(k)` to a sum over `d ≤ m`
  have hLk : chebL k = ∑ d ∈ range (m + 1), Λ d * ((k / d : ℕ) : ℝ) := by
    unfold chebL
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro d hd hnd
    simp only [mem_range, not_lt] at hd hnd
    rw [Nat.div_eq_of_lt (by omega)]; simp
  rw [hLk, chebL, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hIoc : ∑ d ∈ Ioc k m, Λ d = ∑ d ∈ range (m + 1), if k < d then Λ d else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d; simp only [mem_Ioc, mem_filter, mem_range]; omega
  rw [hIoc]
  apply Finset.sum_le_sum
  intro d hd
  simp only [mem_range] at hd
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have hcoef : 2 * ((k / d : ℕ) : ℝ) ≤ ((m / d : ℕ) : ℝ) := by
    have h1 : 2 * (k / d) ≤ 2 * k / d := Nat.mul_div_le_mul_div_assoc 2 k d
    have h2 : 2 * k / d ≤ m / d := Nat.div_le_div_right (by omega)
    exact_mod_cast h1.trans h2
  split_ifs with hkd
  · have h0 : k / d = 0 := Nat.div_eq_of_lt hkd
    have h1 : 1 ≤ m / d := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    rw [h0]
    have : (1 : ℝ) ≤ ((m / d : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast
    nlinarith
  · nlinarith

/-- `ψ(x) - ψ(x/2) ≤ x log 2 + log x` for `x ≥ 1` (Chebyshev). -/
theorem psi_sub_psi_half_le_log {x : ℝ} (hx : 1 ≤ x) :
    ψ x - ψ (x / 2) ≤ x * Real.log 2 + Real.log x := by
  set m := ⌊x⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hx)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hψx : ψ x = ψ (m : ℝ) := psi_eq_psi_coe_floor x
  have hψ2 : ψ (x / 2) = ψ ((m / 2 : ℕ) : ℝ) := by
    rw [psi_eq_psi_coe_floor (x / 2)]
    have := Nat.floor_div_natCast x 2
    push_cast at this
    rw [this]
  rw [hψx, hψ2]
  have h1 := psi_diff_le_chebL m
  rw [chebL_eq_log_factorial, chebL_eq_log_factorial] at h1
  have h2 := log_factorial_sub_le m hm1
  have h3 : Real.log m ≤ Real.log x := Real.log_le_log (by positivity) hmx
  have h4 : (m : ℝ) * Real.log 2 ≤ x * Real.log 2 :=
    mul_le_mul_of_nonneg_right hmx (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  linarith

/-- **Lemma 5.1(i) for `ℕ`, first part.** `ψ(x) - ψ(x/2) ≤ 0.71 x` for every `x ≥ 1`. -/
theorem psi_sub_psi_half_le {x : ℝ} (hx : 1 ≤ x) : ψ x - ψ (x / 2) ≤ 0.71 * x := by
  rcases lt_or_ge x 1500 with h | h
  · have := psi_sub_psi_half_le_small hx h
    linarith
  · have h1 := psi_sub_psi_half_le_log hx
    have h2 := cm1_tail h
    have h3 : 0 ≤ Real.log x := Real.log_nonneg hx
    linarith

/-- **Lemma 5.1(i) for `ℕ`, second part.** `ψ(x) ≤ 1.42 x` for every `x ≥ 0`. -/
theorem psi_le_one_point_four_two {x : ℝ} (hx : 0 ≤ x) : ψ x ≤ 1.42 * x := by
  induction h : ⌊x⌋₊ using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases lt_or_ge x 2 with hx2 | hx2
    · rw [psi_eq_zero_of_lt_two hx2]; linarith
    · have h1 := psi_sub_psi_half_le (show 1 ≤ x by linarith)
      have hlt : ⌊x / 2⌋₊ < n := by
        have := Nat.floor_div_natCast x 2
        push_cast at this
        rw [this, h]
        have : 2 ≤ n := by rw [← h]; exact Nat.le_floor (by exact_mod_cast hx2)
        omega
      have h2 := ih _ hlt (show 0 ≤ x / 2 by linarith) rfl
      linarith

end BSCert.FiniteN
