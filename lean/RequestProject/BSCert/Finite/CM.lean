module

public import RequestProject.BSCert.Finite.Loop

/-!
# Lemma 5.1 (Chebyshev–Mertens) for `ℕ`: the finite computations (`finite_checks.py`, lines 1, 2, 6)

* Line 1, Lemma 5.1(i): `ψ(x) - ψ(x/2) ≤ 0.6803 x` for `1 ≤ x < 1500`, and
  `x log 2 + 3 log x + 3 < 0.71 x` for `x ≥ 1500`.
* Line 2, Lemma 5.1(ii): `-0.753 ≤ S(x) - log x ≤ 0` for `1 ≤ x ≤ 10⁷`, where
  `S(x) = ∑_{p^k ≤ x} log p / p^k = ∑_{n ≤ x} Λ(n)/n`.
* Line 6, Lemma 5.1(iii): `∑_p log p / (p(p-1)) ≤ 0.75537`.

This file contains the checks (as boolean functions) and the proofs that they imply the real
statements; the checks themselves are run in `CMCert.lean`.
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction Chebyshev

/-! ## Fixed-point bounds for `Λ` -/

/-- Fixed-point upper bound for `Λ n`. -/
def vmHi (n : ℕ) : ℤ := if ppBase n = 0 then 0 else logHiN (ppBase n)

lemma vmHi_spec (n : ℕ) : 2 ^ KS * Λ n ≤ (vmHi n : ℝ) := by
  rw [vonMangoldt_eq_ppBase, vmHi]
  split_ifs with h
  · simp
  · exact logHiN_spec (by have := ppBase_ge_two h; omega)

/-! ## Line 1: Lemma 5.1(i) -/

/-- The check of line 1 for one integer `N`: `ψ(N) - ψ(N/2) ≤ 0.6803 N`. -/
def cm1Check (N : ℕ) : Bool :=
  decide (10000 * ∑ k ∈ Ioc (N / 2) N, vmHi k ≤ 6803 * (N : ℤ) * 2 ^ KS)

lemma psi_natCast (n : ℕ) : ψ (n : ℝ) = ∑ k ∈ Ioc 0 n, Λ k := by
  rw [psi, Nat.floor_natCast]

theorem cm1_of_check (h : ∀ N ∈ Icc 1 1499, cm1Check N = true) {x : ℝ} (hx1 : 1 ≤ x)
    (hx2 : x < 1500) : ψ x - ψ (x / 2) ≤ 0.6803 * x := by
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN2 : N ≤ 1499 := by
    have : N < 1500 := Nat.floor_lt (by linarith) |>.mpr (by exact_mod_cast hx2)
    omega
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hc := h N (mem_Icc.mpr ⟨hN1, hN2⟩)
  simp only [cm1Check, decide_eq_true_eq] at hc
  have hψx : ψ x = ψ (N : ℝ) := by rw [psi_eq_psi_coe_floor]
  have hψ2 : ψ ((N / 2 : ℕ) : ℝ) ≤ ψ (x / 2) := by
    apply psi_mono
    have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self N 2
    linarith
  have hsplit : ψ (N : ℝ) - ψ ((N / 2 : ℕ) : ℝ) = ∑ k ∈ Ioc (N / 2) N, Λ k := by
    rw [psi_natCast, psi_natCast, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (N / 2))
      (Nat.div_le_self N 2)]
    ring
  have hsum : 2 ^ KS * ∑ k ∈ Ioc (N / 2) N, Λ k ≤ ((∑ k ∈ Ioc (N / 2) N, vmHi k : ℤ) : ℝ) := by
    rw [mul_sum]; push_cast
    exact sum_le_sum (fun k _ => vmHi_spec k)
  have hc' : (10000 : ℝ) * ((∑ k ∈ Ioc (N / 2) N, vmHi k : ℤ) : ℝ) ≤ 6803 * N * 2 ^ KS := by
    exact_mod_cast hc
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have : ∑ k ∈ Ioc (N / 2) N, Λ k ≤ 0.6803 * N := by
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_left hcon hK
    nlinarith
  linarith

/-- Line 1, second part: `x log 2 + 3 log x + 3 < 0.71 x` for every `x ≥ 1500`. -/
theorem cm1_tail {x : ℝ} (hx : 1500 ≤ x) : x * Real.log 2 + 3 * Real.log x + 3 < 0.71 * x := by
  have h2 := Real.log_two_lt_d9
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ Real.log 1500 + (x / 1500 - 1) := by
    have := Real.log_le_sub_one_of_pos (show 0 < x / 1500 by positivity)
    rw [Real.log_div hx0.ne' (by norm_num)] at this
    linarith
  have h1500 : Real.log 1500 < 7.4 := by
    have he := Real.exp_one_gt_d9
    have h04 := Real.add_one_le_exp (0.4 : ℝ)
    have h7 : Real.exp 7.4 = Real.exp 1 ^ 7 * Real.exp 0.4 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have : (1500 : ℝ) < Real.exp 7.4 := by
      rw [h7]
      have h1 : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr
      calc (1500 : ℝ) < (2.7182818283 : ℝ) ^ 7 * (0.4 + 1) := by norm_num
        _ ≤ Real.exp 1 ^ 7 * Real.exp 0.4 := by gcongr
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    exact this
  nlinarith

/-! ## Line 2: Lemma 5.1(ii) -/

/-- `S(x) = ∑_{n ≤ x} Λ(n)/n = ∑_{p^k ≤ x} log p / p^k`. -/
noncomputable def mertensS (x : ℝ) : ℝ := ∑ n ∈ range (⌊x⌋₊ + 1), Λ n / n

/-- Lower bound for `Λ(i)/i`. -/
def cm2Lo (i : ℕ) : ℤ := if ppBase i = 0 then 0 else fdiv (logLoN (ppBase i)) i
/-- Upper bound for `Λ(i)/i`. -/
def cm2Hi (i : ℕ) : ℤ := if ppBase i = 0 then 0 else cdiv (logHiN (ppBase i)) i
/-- The test of line 2 at `n`: `S(n) ≤ log n` and `S(n) - log(n+1) ≥ -0.753`. -/
def cm2Ok (n : ℕ) (A B : ℤ) : Bool :=
  decide (B ≤ logLoN n) && decide (-753 * 2 ^ KS ≤ 1000 * (A - logHiN (n + 1)))

lemma ppBase_pos_arg {i : ℕ} (h : ppBase i ≠ 0) : 0 < i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [ppBase] at h
  · exact hi

lemma cm2_hg (i : ℕ) : ((cm2Lo i : ℤ) : ℝ) ≤ 2 ^ KS * (Λ i / i) ∧
    2 ^ KS * (Λ i / i) ≤ ((cm2Hi i : ℤ) : ℝ) := by
  rw [vonMangoldt_eq_ppBase, cm2Lo, cm2Hi]
  split_ifs with h
  · simp
  · have hp := ppBase_ge_two h
    have hi := ppBase_pos_arg h
    have hl := logLoN_spec (n := ppBase i) (by omega)
    have hu := logHiN_spec (n := ppBase i) (by omega)
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    constructor
    · refine le_trans (fdiv_le hi) ?_
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hl hi'.le
    · refine le_trans ?_ (le_cdiv hi)
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hu hi'.le

theorem cm2_of_check (h : sumLoop cm2Lo cm2Hi cm2Ok (10 ^ 7) 1 0 0 = true) {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 7) :
    -0.753 ≤ mertensS x - Real.log x ∧ mertensS x - Real.log x ≤ 0 := by
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx1)
  have hN2 : N ≤ 10 ^ 7 := Nat.floor_le_of_le (by exact_mod_cast hx2)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have h0 : ∑ i ∈ range 1, Λ i / (i : ℝ) = 0 := by simp
  obtain ⟨A, B, hA, hB, hok⟩ := sumLoop_spec cm2Lo cm2Hi cm2Ok (fun i => Λ i / i) cm2_hg
    (10 ^ 7) 1 0 0 h (by rw [h0]; simp) (by rw [h0]; simp) N hN1 (by omega)
  simp only [cm2Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok1, hok2⟩ := hok
  have hS : mertensS x = ∑ i ∈ range (N + 1), Λ i / (i : ℝ) := rfl
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have hlo := logLoN_spec (n := N) hN1
  have hhi := logHiN_spec (n := N + 1) (by omega)
  have hlogx1 : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlogx2 : Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by linarith); push_cast; linarith
  have hok1' : (B : ℝ) ≤ (logLoN N : ℝ) := by exact_mod_cast hok1
  have hok2' : -753 * (2 : ℝ) ^ KS ≤ 1000 * ((A : ℝ) - (logHiN (N + 1) : ℝ)) := by
    exact_mod_cast hok2
  rw [hS]
  constructor
  · have : -0.753 * 2 ^ KS ≤ 2 ^ KS * (∑ i ∈ range (N + 1), Λ i / (i : ℝ) -
        Real.log ((N + 1 : ℕ) : ℝ)) := by
      rw [mul_sub]; linarith
    have h3 : -0.753 ≤ ∑ i ∈ range (N + 1), Λ i / (i : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) := by
      by_contra hcon; push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hK
      linarith
    linarith
  · have : 2 ^ KS * ∑ i ∈ range (N + 1), Λ i / (i : ℝ) ≤ 2 ^ KS * Real.log N := by linarith
    have h3 := le_of_mul_le_mul_left this hK
    linarith

/-! ## Line 6: Lemma 5.1(iii) -/

/-- The summand `log n / (n (n-1))` on primes, `0` elsewhere. -/
noncomputable def cm3g (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) else 0

/-- Upper bound for the summand. -/
def cm3Hi (i : ℕ) : ℤ := if i.Prime then cdiv (logHiN i) (i * (i - 1)) else 0

/-- The cut-off `N = 10⁷`. -/
def cm3N : ℕ := 10 ^ 7

/-- The final test of line 6: partial sum up to `N` plus the tail bound `(log N + 2)/N`. -/
def cm3Ok (k : ℕ) (_A B : ℤ) : Bool :=
  k != cm3N || decide (100000 * (B * cm3N + logHiN cm3N + 2 * 2 ^ KS) ≤ 75537 * cm3N * 2 ^ KS)

lemma cm3g_nonneg (n : ℕ) : 0 ≤ cm3g n := by
  unfold cm3g
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h.two_le
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  · exact le_rfl

lemma cm3_hg (i : ℕ) : ((0 : ℤ) : ℝ) ≤ 2 ^ KS * cm3g i ∧ 2 ^ KS * cm3g i ≤ ((cm3Hi i : ℤ) : ℝ) := by
  refine ⟨by simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ KS) (cm3g_nonneg i), ?_⟩
  unfold cm3g cm3Hi
  split_ifs with h
  · have h2 := h.two_le
    have hu := logHiN_spec (n := i) (by omega)
    have hd : 0 < i * (i - 1) := Nat.mul_pos (by omega) (by omega)
    refine le_trans ?_ (le_cdiv hd)
    have e : ((i * (i - 1) : ℕ) : ℝ) = (i : ℝ) * ((i : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
    rw [e, mul_div_assoc']
    apply div_le_div_of_nonneg_right hu
    have : (2 : ℝ) ≤ i := by exact_mod_cast h2
    nlinarith
  · simp

/-- `F(n) = (log n + 2)/n`, the telescoping majorant of the tail. -/
noncomputable def cm3F (n : ℕ) : ℝ := (Real.log n + 2) / n

/-- `log n / (n(n-1)) ≤ F(n-1) - F(n)` for `n ≥ 2`. -/
lemma cm3_step {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ cm3F (n - 1) - cm3F n := by
  unfold cm3F
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have e : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [e]
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h0 : (0 : ℝ) < n := by linarith
  -- `log (n-1) ≥ log n - 1/(n-1)`
  have hl : Real.log n - 1 / ((n : ℝ) - 1) ≤ Real.log ((n : ℝ) - 1) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < ((n : ℝ) - 1) / n by positivity)
    rw [Real.log_div h1.ne' h0.ne'] at this
    have e2 : 1 - (((n : ℝ) - 1) / n)⁻¹ = -(1 / ((n : ℝ) - 1)) := by
      field_simp; ring
    linarith
  rw [div_sub_div _ _ h1.ne' h0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have key : Real.log n ≤ (Real.log ((n : ℝ) - 1) + 2) * n - (Real.log n + 2) * ((n : ℝ) - 1) := by
    have : n * (Real.log n - 1 / ((n : ℝ) - 1)) ≤ n * Real.log ((n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hl h0.le
    have e3 : (n : ℝ) * (1 / ((n : ℝ) - 1)) = 1 + 1 / ((n : ℝ) - 1) := by field_simp; ring
    have h4 : 1 / ((n : ℝ) - 1) ≤ 1 := by rw [div_le_one h1]; linarith
    nlinarith
  have hpos : (0 : ℝ) < n * ((n : ℝ) - 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hpos.le]

lemma cm3_tail (N : ℕ) (hN : 1 ≤ N) :
    ∀ M, N ≤ M → ∑ n ∈ Ioc N M, cm3g n ≤ cm3F N - cm3F M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hstep : cm3g (M + 1) ≤ cm3F M - cm3F (M + 1) := by
      unfold cm3g
      split_ifs with h
      · have := cm3_step (n := M + 1) (by omega)
        simpa using this
      · -- non-prime: the bound `F(M) - F(M+1) ≥ 0` still holds
        have := cm3_step (n := M + 1) (by omega)
        have hnn : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) / (((M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) - 1)) := by
          apply div_nonneg (Real.log_nonneg (by norm_cast; omega))
          have : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by norm_cast; omega
          nlinarith
        simp only [Nat.add_sub_cancel] at this
        linarith
    linarith

lemma cm3F_nonneg (n : ℕ) : 0 ≤ cm3F n := by
  unfold cm3F
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply div_nonneg _ (by positivity)
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith

theorem cm3_partial_of_check
    (h : sumLoop (fun _ => 0) cm3Hi cm3Ok (cm3N + 1) 0 0 0 = true) (M : ℕ) :
    ∑ n ∈ range (M + 1), cm3g n ≤ 0.75537 := by
  obtain ⟨A, B, -, hB, hok⟩ := sumLoop_spec (fun _ => 0) cm3Hi cm3Ok cm3g cm3_hg
    (cm3N + 1) 0 0 0 h (by simp) (by simp) cm3N (Nat.zero_le _) (by omega)
  simp only [cm3Ok, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hok
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have hNpos : (0 : ℝ) < (cm3N : ℝ) := by norm_num [cm3N]
  have hL := logHiN_spec (n := cm3N) (by norm_num [cm3N])
  have hok' : (100000 : ℝ) * ((B : ℝ) * cm3N + (logHiN cm3N : ℝ) + 2 * 2 ^ KS) ≤
      75537 * cm3N * 2 ^ KS := by exact_mod_cast hok
  -- the partial sum up to `N` plus the tail bound
  have hP : ∑ n ∈ range (cm3N + 1), cm3g n + cm3F cm3N ≤ 0.75537 := by
    unfold cm3F
    have e : (2 : ℝ) ^ KS * (∑ n ∈ range (cm3N + 1), cm3g n + (Real.log cm3N + 2) / cm3N) * cm3N
        = (2 ^ KS * ∑ n ∈ range (cm3N + 1), cm3g n) * cm3N + 2 ^ KS * Real.log cm3N +
          2 * 2 ^ KS := by
      field_simp
      ring
    have h1 : (2 : ℝ) ^ KS * (∑ n ∈ range (cm3N + 1), cm3g n + (Real.log cm3N + 2) / cm3N) *
        cm3N ≤ 0.75537 * cm3N * 2 ^ KS := by
      rw [e]
      have := mul_le_mul_of_nonneg_right hB hNpos.le
      linarith
    have h2 : (2 : ℝ) ^ KS * cm3N * (∑ n ∈ range (cm3N + 1), cm3g n +
        (Real.log cm3N + 2) / cm3N) ≤ (2 ^ KS * cm3N) * 0.75537 := by linarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  rcases le_or_gt M cm3N with hM | hM
  · have : ∑ n ∈ range (M + 1), cm3g n ≤ ∑ n ∈ range (cm3N + 1), cm3g n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun i _ _ => cm3g_nonneg i)
    linarith [cm3F_nonneg cm3N]
  · have hsplit : ∑ n ∈ range (M + 1), cm3g n =
        ∑ n ∈ range (cm3N + 1), cm3g n + ∑ n ∈ Ioc cm3N M, cm3g n := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (cm3N + 1)) (by omega : cm3N + 1 ≤ M + 1),
        Finset.Ico_add_one_add_one_eq_Ioc]
    have ht := cm3_tail cm3N (by norm_num [cm3N]) M hM.le
    rw [hsplit]
    linarith [cm3F_nonneg M]

theorem cm3_of_check (h : sumLoop (fun _ => 0) cm3Hi cm3Ok (cm3N + 1) 0 0 0 = true) :
    Summable (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) ∧
    ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75537 := by
  have hnn : 0 ≤ (fun p : Nat.Primes => Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p
    have := cm3g_nonneg p
    simpa [cm3g, p.2] using this
  have hfin : ∀ u : Finset Nat.Primes,
      ∑ p ∈ u, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.75537 := by
    intro u
    obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ u, (p : ℕ) ≤ M :=
      ⟨u.sup (fun p => (p : ℕ)), fun p hp => Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp⟩
    have e : ∑ p ∈ u, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) =
        ∑ n ∈ u.map ⟨fun p : Nat.Primes => (p : ℕ), Subtype.val_injective⟩, cm3g n := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p _
      simp [cm3g, p.2]
    rw [e]
    refine le_trans ?_ (cm3_partial_of_check h M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hM p hp))
    · intro i _ _; exact cm3g_nonneg i
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

end BSCert.FiniteN
