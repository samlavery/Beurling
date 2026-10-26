module

public import RequestProject.BSCert.Transc

/-!
# The Rankin constants `R(0.69) ≤ 0.77` and `R(0.75) ≤ 0.63`

Lemma 6.22(c),(e) of the paper uses
`R(σ) := ∑_p (-log(1 - p^{-σ}) - p^{-σ})` (sum over all primes), with the
computer-assisted bounds `R(0.69) ≤ 0.77` and `R(0.75) ≤ 0.63` (script `rankin_R.py`).

The Lean proof follows the script:
* the primes `p ≤ N = 10⁵` are summed explicitly, each term bounded above by an exact rational
  computation (`p^{-σ}` is bounded by a rational `x` checked through `x^b p^a ≥ 1` for
  `σ = a/b`, and `-log(1-x) - x` by a truncated Taylor series with remainder);
* the primes `p > N` are bounded by `(1/2 + δ/(1-δ)) p^{-2σ}` with `δ ≥ N^{-σ}`, and
  `∑_{n > N, n odd} n^{-2σ}` is bounded by a telescoping sum.
  (The script uses `N = 10⁷` and the tail over all integers; we use a smaller `N` and the
  tail over odd integers only.)
-/

@[expose] public section

namespace BSCert.Rankin

open Finset

/-- The summand of `R(σ)`: `-log(1 - p^{-σ}) - p^{-σ}`. -/
noncomputable def rTerm (σ : ℝ) (p : ℕ) : ℝ :=
  -Real.log (1 - (p : ℝ) ^ (-σ)) - (p : ℝ) ^ (-σ)

/-- `R(σ) = ∑_p (-log(1 - p^{-σ}) - p^{-σ})`, the sum over all primes (Lemma 6.22(c)). -/
noncomputable def R (σ : ℝ) : ℝ := ∑' p : Nat.Primes, rTerm σ p

/-! ## Elementary bounds -/

/-- Truncated Taylor majorant of `-log(1-x) - x`. -/
noncomputable def P (K : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ range K, x ^ (i + 2) / ((i : ℝ) + 2)) + x ^ (K + 2) / (1 - x)

lemma log_term_le_P {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (K : ℕ) :
    -Real.log (1 - x) - x ≤ P K x := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg h0]; exact h1) (K + 1)
  rw [abs_of_nonneg h0] at h
  have h2 := (abs_le.mp h).1
  rw [Finset.sum_range_succ'] at h2
  unfold P
  have : ∑ i ∈ range K, x ^ (i + 1 + 1) / (((i + 1 : ℕ) : ℝ) + 1)
      = ∑ i ∈ range K, x ^ (i + 2) / ((i : ℝ) + 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [this] at h2
  simp only [zero_add, pow_one, Nat.cast_zero] at h2
  have e : K + 1 + 1 = K + 2 := by ring
  rw [e] at h2
  linarith

lemma log_term_nonneg {x : ℝ} (h1 : x < 1) : 0 ≤ -Real.log (1 - x) - x := by
  have := Real.log_le_sub_one_of_pos (x := 1 - x) (by linarith)
  linarith

lemma P_mono {x y : ℝ} (h0 : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) (K : ℕ) : P K x ≤ P K y := by
  unfold P
  have hy0 : 0 ≤ y := le_trans h0 hxy
  have h1y : 0 < 1 - y := by linarith
  gcongr with i hi

/-- The tail bound `-log(1-x) - x ≤ x²(1/2 + δ/(1-δ))` for `0 ≤ x ≤ δ < 1`. -/
lemma log_term_le_sq {x δ : ℝ} (h0 : 0 ≤ x) (hx : x ≤ δ) (hδ : δ < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 * (1 / 2 + δ / (1 - δ)) := by
  refine le_trans (log_term_le_P h0 (by linarith) 1) ?_
  unfold P
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add]
  have h1x : 0 < 1 - x := by linarith
  have h1d : 0 < 1 - δ := by linarith
  have : x / (1 - x) ≤ δ / (1 - δ) := by
    rw [div_le_div_iff₀ h1x h1d]; nlinarith
  have e : x ^ (1 + 2) / (1 - x) = x ^ 2 * (x / (1 - x)) := by ring
  rw [e]
  have hx2 : 0 ≤ x ^ 2 := by positivity
  nlinarith

/-- Checking `p^{-a/b} ≤ q` exactly: it suffices that `q^b n^a ≥ 1`. -/
lemma rpow_neg_le_of_check {n : ℝ} (hn : 0 < n) {a b : ℕ} (hb : 0 < b) {q : ℝ} (hq : 0 ≤ q)
    (h : 1 ≤ q ^ b * n ^ a) : n ^ (-((a : ℝ) / b)) ≤ q := by
  have ht : 0 ≤ n ^ (-((a : ℝ) / b)) := Real.rpow_nonneg hn.le _
  rw [← pow_le_pow_iff_left₀ ht hq hb.ne']
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have : -((a : ℝ) / b) * b = -(a : ℝ) := by field_simp
  rw [this, Real.rpow_neg hn.le, Real.rpow_natCast]
  have hna : 0 < n ^ a := pow_pos hn a
  rw [inv_le_iff_one_le_mul₀' hna]
  linarith [mul_comm (q ^ b) (n ^ a)]

/-- One telescoping step: `m^{-(1+α)} ≤ ((m-2)^{-α} - m^{-α})/(2α)` for `m > 2`, `0 < α ≤ 1`. -/
lemma rpow_step {m α : ℝ} (hm : 2 < m) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    m ^ (-(1 + α)) ≤ ((m - 2) ^ (-α) - m ^ (-α)) / (2 * α) := by
  have hm0 : 0 < m := by linarith
  have hs : (-1 : ℝ) ≤ -2 / m := by
    rw [le_div_iff₀ hm0]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hα0.le hα1
  have hq : 1 + -2 / m = (m - 2) / m := by field_simp; ring
  rw [hq] at hb
  have hpos : 0 < ((m - 2) / m) ^ α := Real.rpow_pos_of_pos (div_pos (by linarith) hm0) _
  have hlin : 0 < 1 + α * (-2 / m) := lt_of_lt_of_le hpos hb
  have e1 : (m - 2) ^ (-α) = m ^ (-α) / ((m - 2) / m) ^ α := by
    rw [Real.div_rpow (by linarith) hm0.le, Real.rpow_neg (by linarith), Real.rpow_neg hm0.le]
    field_simp
  have e2 : m ^ (-(1 + α)) = m ^ (-α) / m := by
    rw [neg_add, Real.rpow_add hm0, Real.rpow_neg_one]; ring
  have hma : 0 < m ^ (-α) := Real.rpow_pos_of_pos hm0 _
  rw [e1, e2, le_div_iff₀ (by linarith)]
  have key : m ^ (-α) / ((m - 2) / m) ^ α ≥ m ^ (-α) / (1 + α * (-2 / m)) :=
    div_le_div_of_nonneg_left hma.le hpos hb
  have key2 : m ^ (-α) / (1 + α * (-2 / m)) ≥ m ^ (-α) * (1 + 2 * α / m) := by
    rw [ge_iff_le, le_div_iff₀ hlin]
    have : (1 + 2 * α / m) * (1 + α * (-2 / m)) = 1 - (2 * α / m) ^ 2 := by ring
    rw [mul_assoc, this]
    have : 0 ≤ (2 * α / m) ^ 2 := sq_nonneg _
    nlinarith
  have e3 : m ^ (-α) / m * (2 * α) = m ^ (-α) * (2 * α / m) := by ring
  rw [e3]
  nlinarith

/-- The telescoped odd tail. -/
lemma odd_tail_le {N α : ℝ} (hN : 3 ≤ N) (hα0 : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∑ j ∈ range k, (N + 1 + 2 * j) ^ (-(1 + α)) ≤ (N - 1) ^ (-α) / (2 * α) := by
  have : ∀ k : ℕ, ∑ j ∈ range k, (N + 1 + 2 * j) ^ (-(1 + α))
      ≤ ((N - 1) ^ (-α) - (N - 1 + 2 * k) ^ (-α)) / (2 * α) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hst := rpow_step (m := N + 1 + 2 * k) (by linarith) hα0 hα1
      have e : N + 1 + 2 * (k : ℝ) - 2 = N - 1 + 2 * k := by ring
      rw [e] at hst
      have e2 : N - 1 + 2 * ((k + 1 : ℕ) : ℝ) = N + 1 + 2 * k := by push_cast; ring
      rw [e2]
      have : ((N - 1) ^ (-α) - (N - 1 + 2 * k) ^ (-α)) / (2 * α)
          + ((N - 1 + 2 * k) ^ (-α) - (N + 1 + 2 * k) ^ (-α)) / (2 * α)
          = ((N - 1) ^ (-α) - (N + 1 + 2 * k) ^ (-α)) / (2 * α) := by ring
      linarith
  refine le_trans (this k) ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 0 ≤ (N - 1 + 2 * k) ^ (-α) := Real.rpow_nonneg (by linarith) _
  gcongr
  linarith


lemma rTerm_nonneg {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : 2 ≤ p) : 0 ≤ rTerm σ p := by
  unfold rTerm
  apply log_term_nonneg
  have hp' : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg hp' (by linarith)

/-- Tail estimate for one prime `p ≥ N`. -/
lemma rTerm_le_tail {σ δ : ℝ} (hσ : 0 < σ) {N p : ℕ} (hN : 1 ≤ N) (hNp : N ≤ p)
    (hδ : (N : ℝ) ^ (-σ) ≤ δ) (hδ1 : δ < 1) :
    rTerm σ p ≤ (1 / 2 + δ / (1 - δ)) * (p : ℝ) ^ (-(1 + (2 * σ - 1))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNp' : (N : ℝ) ≤ p := by exact_mod_cast hNp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hN' hNp'
  have hx0 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
  have hxN : (p : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hN' hNp' (by linarith)
  have h := log_term_le_sq hx0 (le_trans hxN hδ) hδ1
  unfold rTerm
  have e : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(1 + (2 * σ - 1))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
  rw [e] at h
  linarith

/-- The generic bound: explicit head plus telescoped odd tail. -/
theorem R_le_of {σ : ℝ} (hσ1 : 1 / 2 < σ) (hσ2 : σ ≤ 1) {N : ℕ} (hN : 4 ≤ N) (hNe : Even N)
    {δ Y H : ℝ} (hδ : (N : ℝ) ^ (-σ) ≤ δ) (hδ1 : δ < 1)
    (hY : ((N : ℝ) - 1) ^ (-(2 * σ - 1)) ≤ Y)
    (hH : ∑ p ∈ (range (N + 1)).filter Nat.Prime, rTerm σ p ≤ H) :
    R σ ≤ H + (1 / 2 + δ / (1 - δ)) * (Y / (2 * (2 * σ - 1))) := by
  have hσ0 : 0 < σ := by linarith
  set α := 2 * σ - 1 with hα
  have hα0 : 0 < α := by linarith
  have hα1 : α ≤ 1 := by linarith
  set c := 1 / 2 + δ / (1 - δ) with hc
  have hN1 : 1 ≤ N := by omega
  have hδ0 : 0 ≤ δ := le_trans (Real.rpow_nonneg (by positivity) _) hδ
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - δ := by linarith
    positivity
  unfold R
  refine Real.tsum_le_of_sum_le (fun p => rTerm_nonneg hσ0 p.2.two_le) (fun s => ?_)
  set M := s.sup (fun p : Nat.Primes => (p : ℕ)) with hM
  set A := (range (M + 1)).filter Nat.Prime with hA
  have h1 : ∑ p ∈ s, rTerm σ (p : ℕ) ≤ ∑ n ∈ A, rTerm σ n := by
    have e := Finset.sum_map s (Function.Embedding.subtype _) (fun n => rTerm σ n)
    refine le_trans (le_of_eq e.symm) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_map] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      simp only [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp), p.2⟩
    · intro n hn _
      simp only [hA, Finset.mem_filter] at hn
      exact rTerm_nonneg hσ0 hn.2.two_le
  refine le_trans h1 ?_
  rw [← Finset.sum_filter_add_sum_filter_not A (fun n => n ≤ N)]
  have h2 : ∑ n ∈ A.filter (fun n => n ≤ N), rTerm σ n ≤ H := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hH
    · intro n hn
      simp only [hA, Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨by omega, hn.1.2⟩
    · intro n hn _
      simp only [Finset.mem_filter] at hn
      exact rTerm_nonneg hσ0 hn.2.two_le
  have h3 : ∑ n ∈ A.filter (fun n => ¬ n ≤ N), rTerm σ n ≤ c * (Y / (2 * α)) := by
    calc ∑ n ∈ A.filter (fun n => ¬ n ≤ N), rTerm σ n
        ≤ ∑ n ∈ A.filter (fun n => ¬ n ≤ N), c * (n : ℝ) ^ (-(1 + α)) := by
          apply Finset.sum_le_sum
          intro n hn
          simp only [Finset.mem_filter] at hn
          exact rTerm_le_tail hσ0 hN1 (by omega) hδ hδ1
      _ ≤ ∑ n ∈ (range (M + 1)).image (fun j => N + 1 + 2 * j), c * (n : ℝ) ^ (-(1 + α)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [hA, Finset.mem_filter, Finset.mem_range] at hn
            obtain ⟨⟨hnM, hpr⟩, hnN⟩ := hn
            have hodd : n % 2 = 1 := by
              rcases hpr.eq_two_or_odd with h | h
              · omega
              · exact h
            obtain ⟨k, hk⟩ := hNe
            simp only [Finset.mem_image, Finset.mem_range]
            exact ⟨(n - N - 1) / 2, by omega, by omega⟩
          · intro n _ _
            have : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + α)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
            positivity
      _ = ∑ j ∈ range (M + 1), c * ((N : ℝ) + 1 + 2 * j) ^ (-(1 + α)) := by
          rw [Finset.sum_image]
          · push_cast; rfl
          · intro i _ j _ h; simp only at h; omega
      _ = c * ∑ j ∈ range (M + 1), ((N : ℝ) + 1 + 2 * j) ^ (-(1 + α)) := by
          rw [Finset.mul_sum]
      _ ≤ c * (((N : ℝ) - 1) ^ (-α) / (2 * α)) := by
          gcongr
          exact odd_tail_le (by exact_mod_cast (by omega : 3 ≤ N)) hα0 hα1 _
      _ ≤ c * (Y / (2 * α)) := by gcongr
  linarith

/-! ## Exact rational computation of the head -/

/-- Rational version of `P`. -/
def Pq (K : ℕ) (x : ℚ) : ℚ :=
  (∑ i ∈ range K, x ^ (i + 2) / ((i : ℚ) + 2)) + x ^ (K + 2) / (1 - x)

lemma Pq_cast (K : ℕ) (x : ℚ) : ((Pq K x : ℚ) : ℝ) = P K (x : ℝ) := by
  unfold Pq P; push_cast; rfl

/-- Number of Taylor terms used for the prime `p`. -/
def Kp (p : ℕ) : ℕ := if p ≤ 30 then 60 else if p ≤ 1000 then 20 else 8

/-- A candidate rational upper bound for `p^{-σ}`, proposed by floating point (`sf ≈ σ`);
it is accepted only after the exact check in `primeOK`. -/
def xc (sf : Float) (p : ℕ) : ℚ :=
  match ratOfFloat ((Float.ofNat p) ^ (-sf)) with
  | some g => ((⌈g * 2 ^ 40⌉.toNat + 2 : ℕ) : ℚ) / 2 ^ 40
  | none => 1

/-- Exact check that `xc sf p` is an upper bound for `p^{-a/b}` lying in `[0,1)`. -/
def primeOK (a b : ℕ) (sf : Float) (p : ℕ) : Bool :=
  decide (0 ≤ xc sf p) && decide (xc sf p < 1) && decide (1 ≤ xc sf p ^ b * (p : ℚ) ^ a)

/-- The certified upper bound for the term of the prime `p`. -/
def termUB (sf : Float) (p : ℕ) : ℚ := rup (Pq (Kp p) (xc sf p))

lemma rTerm_le_termUB {a b : ℕ} (hb : 0 < b) {sf : Float} {p : ℕ} (hp : 2 ≤ p)
    (h : primeOK a b sf p = true) : rTerm ((a : ℝ) / b) p ≤ ((termUB sf p : ℚ) : ℝ) := by
  simp only [primeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h0' : (0 : ℝ) ≤ (xc sf p : ℝ) := by exact_mod_cast h0
  have h1' : ((xc sf p : ℚ) : ℝ) < 1 := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ ((xc sf p : ℚ) : ℝ) ^ b * (p : ℝ) ^ a := by exact_mod_cast h2
  have hx := rpow_neg_le_of_check hp0 hb h0' h2'
  have hx0 : 0 ≤ (p : ℝ) ^ (-((a : ℝ) / b)) := Real.rpow_nonneg hp0.le _
  unfold rTerm termUB
  refine le_trans (log_term_le_P hx0 (lt_of_le_of_lt hx h1') (Kp p)) ?_
  refine le_trans (P_mono hx0 hx h1' _) ?_
  rw [← Pq_cast]
  exact_mod_cast le_rup _

/-- The head sum of certified upper bounds. -/
def headUB (sf : Float) (N : ℕ) : ℚ := ∑ p ∈ (range (N + 1)).filter Nat.Prime, termUB sf p

lemma head_le {a b : ℕ} (hb : 0 < b) {sf : Float} {N : ℕ}
    (h : ∀ p ∈ (range (N + 1)).filter Nat.Prime, primeOK a b sf p = true) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, rTerm ((a : ℝ) / b) p ≤ ((headUB sf N : ℚ) : ℝ) := by
  unfold headUB
  push_cast
  apply Finset.sum_le_sum
  intro p hp
  exact rTerm_le_termUB hb (Finset.mem_filter.mp hp).2.two_le (h p hp)

end BSCert.Rankin
