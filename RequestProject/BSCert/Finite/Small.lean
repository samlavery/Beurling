module

public import RequestProject.BSCert.Finite.Loop

/-!
# `finite_checks.py`, lines 3a, 3b, 4 and 5: the checks and their soundness

* Lines 3a/3b (Lemma 5.3, small heights): `∑_{Y < n ≤ 2Y} 1/n`.
* Line 4 (Section 5.8): `F_{1/2} = max_{1 ≤ y ≤ 10⁶} y^{-1/2} ∑_{n ≤ y} μ²(n) n^{-1/2}`.
* Line 5 (Lemma 5.23, threshold mass): `∏_{q < p} (1 - 1/q)⁻¹ - 1.8 log p` for primes `p < 400`.

The checks are run in `SmallCert.lean`.
-/

@[expose] public section

namespace BSCert.FiniteN

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## Lines 3a and 3b: `∑_{Y < n ≤ 2Y} 1/n` -/

/-- `∑_{n ∈ ℕ, Y < n ≤ 2Y} 1/n`. -/
noncomputable def harmWin (Y : ℝ) : ℝ :=
  ∑ n ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun n : ℕ => Y < n), (1 : ℝ) / n

/-- For `Y ≥ 0`, the window is `{⌊2Y⌋/2 < n ≤ ⌊2Y⌋}`. -/
lemma harmWin_eq {Y : ℝ} (hY : 0 ≤ Y) :
    harmWin Y = ∑ n ∈ Ioc (⌊2 * Y⌋₊ / 2) ⌊2 * Y⌋₊, (1 : ℝ) / n := by
  unfold harmWin
  have hfl : ⌊Y⌋₊ = ⌊2 * Y⌋₊ / 2 := by
    have := Nat.floor_div_natCast (2 * Y) 2
    push_cast at this
    rw [← this]; congr 1; ring
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_filter, mem_range, mem_Ioc]
  rw [← hfl, Nat.floor_lt hY]
  exact ⟨fun ⟨a, b⟩ => ⟨b, by omega⟩, fun ⟨a, b⟩ => ⟨by omega, a⟩⟩

/-- The window sum as a function of `k = ⌊2Y⌋`. -/
noncomputable def winR (k : ℕ) : ℝ := ∑ n ∈ Ioc (k / 2) k, (1 : ℝ) / n

/-- Exact rational window sum (line 3b). -/
def winQ (k : ℕ) : ℚ := ∑ n ∈ Ioc (k / 2) k, (1 : ℚ) / n

lemma winR_eq_winQ (k : ℕ) : winR k = (winQ k : ℝ) := by
  unfold winR winQ; push_cast; rfl

/-- Fixed-point upper bound `⌈2^KS / n⌉` for `1/n`. -/
def recipHi (n : ℕ) : ℤ := cdiv (2 ^ KS) n

lemma recipHi_spec {n : ℕ} (hn : 0 < n) : 2 ^ KS * ((1 : ℝ) / n) ≤ (recipHi n : ℝ) := by
  have := le_cdiv (a := 2 ^ KS) hn
  push_cast at this
  unfold recipHi
  rw [mul_one_div]; exact this

/-- The integer window sum of the fixed-point bounds. -/
def winU (k : ℕ) : ℤ := ∑ n ∈ Ioc (k / 2) k, recipHi n

lemma winU_succ (k : ℕ) :
    winU (k + 1) = winU k + recipHi (k + 1) - (if (k + 1) % 2 = 0 then recipHi ((k + 1) / 2) else 0) := by
  unfold winU
  split_ifs with h
  · have e : (k + 1) / 2 = k / 2 + 1 := by omega
    rw [e, Finset.sum_Ioc_succ_top (by omega)]
    have := Finset.sum_Ioc_consecutive (fun n => recipHi n) (Nat.le_succ (k / 2))
      (show k / 2 + 1 ≤ k by omega)
    rw [← this, Nat.Ioc_succ_singleton, Finset.sum_singleton]
    ring
  · have e : (k + 1) / 2 = k / 2 := by omega
    rw [e, Finset.sum_Ioc_succ_top (by omega)]
    ring

/-- The incremental check of line 3a. -/
def winLoop : ℕ → ℕ → ℤ → Bool
  | 0, _, _ => true
  | f + 1, k, D =>
    let D' := D + recipHi (k + 1) - (if (k + 1) % 2 = 0 then recipHi ((k + 1) / 2) else 0)
    decide (100000 * D' ≤ 69659 * 2 ^ KS) && winLoop f (k + 1) D'

theorem winLoop_spec : ∀ f k, winLoop f k (winU k) = true →
    ∀ k', k < k' → k' ≤ k + f → 100000 * winU k' ≤ 69659 * 2 ^ KS := by
  intro f
  induction f with
  | zero => intro k _ k' h1 h2; omega
  | succ f ih =>
    intro k h k' hk1 hk2
    simp only [winLoop, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [← winU_succ] at h
    rcases Nat.eq_or_lt_of_le (show k + 1 ≤ k' by omega) with rfl | hlt
    · exact h.1
    · exact ih (k + 1) h.2 k' hlt (by omega)

lemma winR_le_of_winU {k : ℕ} (h : 100000 * winU k ≤ 69659 * 2 ^ KS) : winR k ≤ 0.69659 := by
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have h1 : 2 ^ KS * winR k ≤ (winU k : ℝ) := by
    unfold winR winU; rw [mul_sum]; push_cast
    exact sum_le_sum (fun n hn => recipHi_spec (by simp at hn; omega))
  have h2 : (100000 : ℝ) * (winU k : ℝ) ≤ 69659 * 2 ^ KS := by exact_mod_cast h
  by_contra hc; push_neg at hc
  nlinarith

/-- `∑_{m < n ≤ M} 1/n ≤ log M - log m` for `1 ≤ m ≤ M`. -/
lemma sum_Ioc_recip_le_log {m : ℕ} (hm : 1 ≤ m) :
    ∀ M, m ≤ M → ∑ n ∈ Ioc m M, (1 : ℝ) / n ≤ Real.log M - Real.log m := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hmM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hstep : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) - Real.log M := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M / ((M + 1 : ℕ) : ℝ) by positivity)
      rw [Real.log_div hM0.ne' (by positivity)] at h
      have e : (M : ℝ) / ((M + 1 : ℕ) : ℝ) - 1 = -(1 / ((M + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    linarith

/-- Line 3a, large heights: for `Y ≥ 10⁴`, `∑_{Y < n ≤ 2Y} 1/n ≤ log 2 + 10⁻⁴`. -/
theorem harmWin_le_large {Y : ℝ} (hY : 10 ^ 4 ≤ Y) : harmWin Y ≤ Real.log 2 + 1 / 10 ^ 4 := by
  rw [harmWin_eq (by linarith)]
  set k := ⌊2 * Y⌋₊
  have hk : 20000 ≤ k := Nat.le_floor (by push_cast; linarith)
  set m := k / 2
  have hm : 10000 ≤ m := by omega
  have hkm : k ≤ 2 * m + 1 := by omega
  have h1 := sum_Ioc_recip_le_log (m := m) (by omega) k (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (10000 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : Real.log k ≤ Real.log (2 * m + 1) :=
    Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hkm)
  have h3 : Real.log (2 * m + 1) - Real.log m = Real.log 2 + Real.log (1 + 1 / (2 * m)) := by
    rw [← Real.log_div (by positivity) hm0.ne', ← Real.log_mul (by norm_num) (by positivity)]
    congr 1; field_simp
  have h4 : Real.log (1 + 1 / (2 * m)) ≤ 1 / (2 * m) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (2 * m) by positivity)
    linarith
  have h5 : 1 / (2 * (m : ℝ)) ≤ 1 / 10 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

/-- Rational check of line 3b for one `k`. -/
def win3bCheck (k : ℕ) : Bool := decide (winQ k ≤ 5 / 6)

/-! ## Line 4: `F_{1/2}` -/

/-- Fixed-point upper bound for `1/√n`: the least `u` with `u² n ≥ 4^KS`. -/
def invSqrtHi (n : ℕ) : ℕ :=
  let t := (4 ^ KS + n - 1) / n
  let s := Nat.sqrt t
  if s * s < t then s + 1 else s

lemma invSqrtHi_spec {n : ℕ} (hn : 0 < n) :
    2 ^ KS * (1 / Real.sqrt n) ≤ (invSqrtHi n : ℝ) := by
  set u := invSqrtHi n
  have hu : 4 ^ KS ≤ u * u * n := by
    have ht : 4 ^ KS ≤ (4 ^ KS + n - 1) / n * n := by
      have := Nat.div_mul_le_self (4 ^ KS + n - 1) n
      have h2 := Nat.lt_div_mul_add (a := 4 ^ KS + n - 1) hn
      have : 4 ^ KS + n - 1 < (4 ^ KS + n - 1) / n * n + n := by
        rw [Nat.mul_comm]; linarith [Nat.div_add_mod (4 ^ KS + n - 1) n,
          Nat.mod_lt (4 ^ KS + n - 1) hn]
      omega
    have hs : (4 ^ KS + n - 1) / n ≤ u * u := by
      simp only [u, invSqrtHi]
      split_ifs with h
      · have := Nat.lt_succ_sqrt' ((4 ^ KS + n - 1) / n)
        rw [pow_two] at this
        exact this.le
      · push_neg at h; exact h
    exact le_trans ht (Nat.mul_le_mul_right n hs)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hu' : (2 : ℝ) ^ KS * 2 ^ KS ≤ (u : ℝ) * u * n := by
    have : ((4 ^ KS : ℕ) : ℝ) ≤ ((u * u * n : ℕ) : ℝ) := by exact_mod_cast hu
    push_cast at this
    rw [← mul_pow]; norm_num; exact this
  rw [mul_one_div, div_le_iff₀ hsq]
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  by_contra hc; push_neg at hc
  have h0 : (0 : ℝ) ≤ u * Real.sqrt n := by positivity
  have := mul_self_lt_mul_self h0 hc
  nlinarith

/-- `F(y) = y^{-1/2} ∑_{n ≤ y} μ²(n) n^{-1/2}`. -/
noncomputable def F12 (y : ℝ) : ℝ :=
  (Real.sqrt y)⁻¹ * ∑ n ∈ range (⌊y⌋₊ + 1), ((μ n : ℤ) : ℝ) ^ 2 / Real.sqrt n

/-- Upper bound for `μ²(n)/√n`. -/
def f12Hi (n : ℕ) : ℤ := if Squarefree n then (invSqrtHi n : ℤ) else 0

/-- The test of line 4 at `k`: `B ≤ 1.32964 √k · 2^KS`. -/
def f12Ok (k : ℕ) (_A B : ℤ) : Bool :=
  decide (10000000000 * (B * B) ≤ 17679425296 * (k : ℤ) * 4 ^ KS)

lemma f12_hg (n : ℕ) : ((0 : ℤ) : ℝ) ≤ 2 ^ KS * (((μ n : ℤ) : ℝ) ^ 2 / Real.sqrt n) ∧
    2 ^ KS * (((μ n : ℤ) : ℝ) ^ 2 / Real.sqrt n) ≤ ((f12Hi n : ℤ) : ℝ) := by
  have hmu : ((μ n : ℤ) : ℝ) ^ 2 = if Squarefree n then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (moebius_sq (n := n))
    push_cast at this
    rw [this]
  rw [hmu]
  unfold f12Hi
  split_ifs with h
  · have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact not_squarefree_zero h)
    refine ⟨by push_cast; positivity, ?_⟩
    have := invSqrtHi_spec hn
    push_cast
    exact this
  · simp

theorem f12_of_check (h : sumLoop (fun _ => 0) f12Hi f12Ok (10 ^ 6) 1 0 0 = true) {y : ℝ}
    (hy1 : 1 ≤ y) (hy2 : y ≤ 10 ^ 6) : F12 y ≤ 1.32964 := by
  set N := ⌊y⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy1)
  have hN2 : N ≤ 10 ^ 6 := Nat.floor_le_of_le (by exact_mod_cast hy2)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have h0 : ∑ i ∈ range 1, ((μ i : ℤ) : ℝ) ^ 2 / Real.sqrt i = 0 := by simp
  obtain ⟨A, B, -, hB, hok⟩ := sumLoop_spec (fun _ => 0) f12Hi f12Ok
    (fun i => ((μ i : ℤ) : ℝ) ^ 2 / Real.sqrt i) f12_hg (10 ^ 6) 1 0 0 h
    (by rw [h0]; simp) (by rw [h0]; simp) N hN1 (by omega)
  simp only [f12Ok, decide_eq_true_eq] at hok
  set S := ∑ i ∈ range (N + 1), ((μ i : ℤ) : ℝ) ^ 2 / Real.sqrt i
  have hS0 : 0 ≤ S := sum_nonneg (fun i _ => by positivity)
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hok' : (10000000000 : ℝ) * ((B : ℝ) * B) ≤ 17679425296 * N * 4 ^ KS := by
    exact_mod_cast hok
  -- `S ≤ 1.32964 √N`
  have hKS0 : 0 ≤ 2 ^ KS * S := mul_nonneg hK.le hS0
  have hB0 : 0 ≤ (B : ℝ) := le_trans hKS0 hB
  have hSN : S ≤ 1.32964 * Real.sqrt N := by
    have h1 : (2 ^ KS * S) ^ 2 ≤ (B : ℝ) ^ 2 := pow_le_pow_left₀ hKS0 hB 2
    have h4 : (4 : ℝ) ^ KS = (2 ^ KS) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2 : (2 ^ KS * S) ^ 2 ≤ (1.32964 * 2 ^ KS) ^ 2 * N := by
      rw [h4] at hok'; nlinarith
    have h3 : 2 ^ KS * S ≤ 1.32964 * 2 ^ KS * Real.sqrt N := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hKS0, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)] at this
    nlinarith
  have hsy : Real.sqrt N ≤ Real.sqrt y := Real.sqrt_le_sqrt hNy
  have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  unfold F12
  rw [inv_mul_le_iff₀ hsy0]
  nlinarith

/-! ## Line 5: the threshold-mass products -/

/-- `∏_{q < p, q prime} q/(q-1)` as an exact rational. -/
def thrProd (p : ℕ) : ℚ := ∏ q ∈ (range p).filter Nat.Prime, (q : ℚ) / ((q : ℚ) - 1)

/-- The check of line 5 for one prime `p`: `∏ - 1/4 ≤ 1.8 log p`. -/
def thrCheck (p : ℕ) : Bool := decide ((thrProd p - 1 / 4) * 2 ^ KS ≤ 9 / 5 * (logLoN p : ℚ))

theorem thr_of_check (h : ∀ p ∈ (range 400).filter Nat.Prime, thrCheck p = true) {p : ℕ}
    (hp : p.Prime) (hp4 : p < 400) :
    ∏ q ∈ (range p).filter Nat.Prime, (1 - 1 / (q : ℝ))⁻¹ - 1.8 * Real.log p ≤ 0.25 := by
  have hc := h p (mem_filter.mpr ⟨mem_range.mpr hp4, hp⟩)
  simp only [thrCheck, decide_eq_true_eq] at hc
  have hprod : ∏ q ∈ (range p).filter Nat.Prime, (1 - 1 / (q : ℝ))⁻¹ = (thrProd p : ℝ) := by
    unfold thrProd
    push_cast
    apply prod_congr rfl
    intro q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (mem_filter.mp hq).2.two_le
    field_simp
  rw [hprod]
  have hc' : ((thrProd p : ℝ) - 1 / 4) * 2 ^ KS ≤ 9 / 5 * (logLoN p : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at this
    exact this
  have hl := logLoN_spec (n := p) hp.one_lt.le
  have hK : (0 : ℝ) < 2 ^ KS := by positivity
  nlinarith

end BSCert.FiniteN
