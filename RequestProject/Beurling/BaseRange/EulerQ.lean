module

public import RequestProject.Beurling.Lemma51NatFull
public import RequestProject.Beurling.SmoothTailsCert
public import RequestProject.Beurling.Rankin

/-!
# The Rankin–Euler product in the proof of Lemma 7.3(c), for the rational primes

Bullet 2 of the proof of Lemma 7.3(c) uses Rankin's method with exponent `1 - σ`,
`σ = 2/log y`, and the bound

  `∏_{p ≤ y} (1 - p^{σ-1})^{-1} ≤ 2 e^γ e^{Ein(2)} log y`.

Here it is proved for the rational primes (`rankinConst_le`, in the stronger form
`≤ 1.8 log(N+1) · e^{Ein(2) + 840σ}` with `N = ⌊y⌋`), by comparison with Mertens' product
`∏_{p ≤ N} (1 - 1/p)^{-1} ≤ 1.8 log(N+1)` (`Mertens.ZinfR_one_le`):

* `(1 - p^{σ-1})^{-1} = (1 - 1/p)^{-1} (p - 1)/(p - p^σ) ≤ (1 - 1/p)^{-1} exp((p^σ - 1)/(p - p^σ))`;
* `∑_{p ≤ N} (p^σ - 1)/p ≤ Ein(2) + 12σ` (`sum_rpow_sub_one_div_le`), by Abel summation against
  `∑_{p ≤ t} log p/p = log t + O(1)` (Lemma 5.1(iii) for `ℕ`, `lemma_5_1_iii_nat_all`) with the
  increasing weight `w(t) = (t^σ - 1)/log t = σ φ(σ log t)`, `φ(u) = (e^u - 1)/u`, and the
  lower Riemann bound `(B - A) φ(A) ≤ Ein(B) - Ein(A)`;
* the rest, `∑_p (p^σ - 1)(1/(p - p^σ) - 1/p)`, is at most `15 e⁴ σ`.
-/

@[expose] public section

open Real Finset BSCert.EiFn

namespace BaseRange

/-- `φ(u) = (e^u - 1)/u`, the integrand of `Ein`. -/
noncomputable def ph (u : ℝ) : ℝ := (Real.exp u - 1) / u

lemma ph_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : ph s ≤ ph t := by
  have h := convexOn_exp.secant_mono (a := 0) (x := s) (y := t) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) hs.ne' (by linarith) hst
  simpa [ph, Real.exp_zero] using h

lemma ph_pos {u : ℝ} (hu : 0 < u) : 0 < ph u := by
  unfold ph
  have := Real.add_one_lt_exp hu.ne'
  apply div_pos (by linarith) hu

lemma ph_two_le : ph 2 ≤ 3.2 := by
  unfold ph
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e, div_le_iff₀ (by norm_num)]
  nlinarith [Real.exp_pos 1]

lemma ph_le {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) : ph u ≤ 3.2 := (ph_mono hu hu2).trans ph_two_le

/-- The lower Riemann bound for the increasing integrand of `Ein`:
`(B - A) φ(A) ≤ Ein(B) - Ein(A)` for `0 < A ≤ B`. -/
lemma ein_lower {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) : (B - A) * ph A ≤ Ein B - Ein A := by
  set c := ph A
  set G : ℝ → ℝ := fun t => Ein t - t * c
  have hd : ∀ t, 0 < t → HasDerivAt G ((Real.exp t - 1) / t - c) t := by
    intro t ht
    exact (hasDerivAt_Ein ht).sub ((hasDerivAt_id t).mul_const c |>.congr_deriv (by simp))
  have hmono : MonotoneOn G (Set.Icc A B) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc A B)
    · exact fun v hv => (hd v (by linarith [hv.1])).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      exact (hd v (by linarith [hv.1])).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v (by linarith [hv.1])).deriv]
      have := ph_mono hA hv.1.le
      have hc : c = (Real.exp A - 1) / A := rfl
      simp only [ph] at this
      linarith
  have := hmono (Set.left_mem_Icc.mpr hAB) (Set.right_mem_Icc.mpr hAB) hAB
  simp only [G] at this
  linarith

/-! ### Abel summation with an increasing weight -/

/-- If `-c₂ ≤ ∑_{k=2}^N a_k - log N ≤ c₁` for every `N ≥ 2` and `w ≥ 0` is non-decreasing, then
`∑_{k=2}^N a_k w_k ≤ (c₁ + c₂) w(N) + log 2 · w(2) + ∑_{n=3}^N (log n - log(n-1)) w(n)`. -/
lemma abel_incr (a w : ℕ → ℝ) {c1 c2 : ℝ}
    (hA : ∀ N ≥ 2, -c2 ≤ ∑ k ∈ Icc 2 N, a k - Real.log N ∧ ∑ k ∈ Icc 2 N, a k - Real.log N ≤ c1)
    (hw : ∀ n ≥ 2, w n ≤ w (n + 1)) (hw0 : ∀ n ≥ 2, 0 ≤ w n) (hc2 : 0 ≤ c2) {N : ℕ}
    (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, a k * w k ≤ (c1 + c2) * w N + Real.log 2 * w 2 +
      ∑ n ∈ Icc 3 N, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * w n := by
  have key : ∀ N ≥ 2, ∑ k ∈ Icc 2 N, a k * w k ≤
      (∑ k ∈ Icc 2 N, a k - Real.log N + c2) * w N + (Real.log 2 - c2) * w 2 +
      ∑ n ∈ Icc 3 N, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * w n := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp; ring_nf; rfl
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 : 0 ≤ (∑ k ∈ Icc 2 M, a k - Real.log M + c2) * (w (M + 1) - w M) :=
        mul_nonneg (by linarith [(hA M hM).1]) (by linarith [hw M hM])
      simp only [Nat.add_sub_cancel]
      push_cast at ih ⊢
      nlinarith
  have := key N hN
  have h2 : (∑ k ∈ Icc 2 N, a k - Real.log N + c2) * w N ≤ (c1 + c2) * w N :=
    mul_le_mul_of_nonneg_right (by linarith [(hA N hN).2]) (hw0 N hN)
  have h3 : 0 ≤ c2 * w 2 := mul_nonneg hc2 (hw0 2 le_rfl)
  linarith

/-- The telescoping against `Ein`: for `σ > 0`, `N ≥ 2`,
`∑_{n=3}^N (log n - log(n-1)) σ φ(σ log n) ≤ Ein(σ log N) - Ein(σ log 2)
  + (σ/2)(φ(σ log N) - φ(σ log 2))`. -/
lemma telescope_ein {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) * (σ * ph (σ * Real.log n)) ≤
      Ein (σ * Real.log N) - Ein (σ * Real.log 2) +
        σ / 2 * (ph (σ * Real.log N) - ph (σ * Real.log 2)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    set a := Real.log M
    set b := Real.log ((M + 1 : ℕ) : ℝ)
    have ha : 0 < a := Real.log_pos (by linarith)
    have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
    have hba : b - a ≤ 1 / 2 := by
      have : b - a = Real.log (((M + 1 : ℕ) : ℝ) / M) := by
        rw [Real.log_div (by positivity) (by positivity)]
      rw [this]
      have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) / M)
      have e : ((M + 1 : ℕ) : ℝ) / M - 1 = 1 / M := by push_cast; field_simp; ring
      have : (1 : ℝ) / M ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hM'
      linarith
    have hσa : 0 < σ * a := mul_pos hσ ha
    have h1 := ein_lower hσa (mul_le_mul_of_nonneg_left hab hσ.le)
    have h2 := ph_mono hσa (mul_le_mul_of_nonneg_left hab hσ.le)
    have h3 : (b - a) * (σ * ph (σ * b)) ≤ Ein (σ * b) - Ein (σ * a) +
        σ / 2 * (ph (σ * b) - ph (σ * a)) := by
      have e : (b - a) * (σ * ph (σ * b)) = (σ * b - σ * a) * ph (σ * a) +
          σ * (b - a) * (ph (σ * b) - ph (σ * a)) := by ring
      rw [e]
      have : σ * (b - a) * (ph (σ * b) - ph (σ * a)) ≤ σ / 2 * (ph (σ * b) - ph (σ * a)) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        nlinarith
      linarith
    push_cast at h3 ih ⊢
    linarith

/-! ### `∑_{p ≤ N} (p^σ - 1)/p ≤ Ein(2) + 12σ` -/

lemma primesBelow_eq_filter (N : ℕ) : (N + 1).primesBelow = (Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨by omega, h3⟩

lemma rpow_eq_exp_mul_log {p σ : ℝ} (hp : 0 < p) : p ^ σ = Real.exp (σ * Real.log p) := by
  rw [Real.rpow_def_of_pos hp, mul_comm]

/-- **`∑_{p ≤ N} (p^σ - 1)/p ≤ Ein(2) + 12σ`** for `0 < σ`, `N ≥ 2`, `σ log N ≤ 2`. -/
theorem sum_rpow_sub_one_div_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N)
    (hσN : σ * Real.log N ≤ 2) :
    ∑ p ∈ (N + 1).primesBelow, ((p : ℝ) ^ σ - 1) / p ≤ Ein 2 + 12 * σ := by
  set w : ℕ → ℝ := fun n => σ * ph (σ * Real.log n) with hw
  rw [Mertens.sum_primesBelow_eq]
  have e : ∀ k ∈ Icc 2 N, (if k.Prime then ((k : ℝ) ^ σ - 1) / k else 0) =
      Mertens.primeLogWeight k * w k := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hlog : 0 < Real.log k := Real.log_pos (by linarith)
    unfold Mertens.primeLogWeight
    split_ifs
    · simp only [hw, ph]
      rw [rpow_eq_exp_mul_log (by linarith)]
      field_simp
    · simp
  rw [Finset.sum_congr rfl e]
  have hw0 : ∀ n ≥ 2, 0 ≤ w n := by
    intro n hn
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg hσ.le (ph_pos (mul_pos hσ (Real.log_pos (by linarith)))).le
  have hwm : ∀ n ≥ 2, w n ≤ w (n + 1) := by
    intro n hn
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hw]
    apply mul_le_mul_of_nonneg_left _ hσ.le
    apply ph_mono (mul_pos hσ (Real.log_pos (by linarith)))
    apply mul_le_mul_of_nonneg_left _ hσ.le
    exact Real.log_le_log (by linarith) (by push_cast; linarith)
  have hA : ∀ M ≥ 2, -1.77 ≤ ∑ k ∈ Icc 2 M, Mertens.primeLogWeight k - Real.log M ∧
      ∑ k ∈ Icc 2 M, Mertens.primeLogWeight k - Real.log M ≤ 0.43 := by
    intro M hM
    have e2 : ∑ k ∈ Icc 2 M, Mertens.primeLogWeight k = Lemma51Nat.primeLogSum M := by
      unfold Mertens.primeLogWeight Lemma51Nat.primeLogSum
      rw [← Mertens.sum_primesBelow_eq (fun n : ℕ => Real.log n / n), primesBelow_eq_filter,
        Nat.floor_natCast]
    rw [e2]
    exact Lemma51Nat.lemma_5_1_iii_nat_all (by exact_mod_cast (by omega : 1 ≤ M))
  have hab := abel_incr Mertens.primeLogWeight w hA hwm hw0 (by norm_num) hN
  refine hab.trans ?_
  have ht := telescope_ein hσ hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hσ2 : 0 < σ * Real.log 2 := mul_pos hσ hl2
  have hφN : ph (σ * Real.log N) ≤ 3.2 := ph_le (mul_pos hσ hlN) hσN
  have hφ2 : ph (σ * Real.log 2) ≤ 3.2 :=
    ph_le hσ2 (le_trans (mul_le_mul_of_nonneg_left hl2N hσ.le) hσN)
  have hφ2p := ph_pos hσ2
  have hφNp := ph_pos (mul_pos hσ hlN)
  have hE1 : Ein (σ * Real.log N) ≤ Ein 2 := SmoothTails.Ein_mono (by positivity) hσN
  have hE2 : 0 ≤ Ein (σ * Real.log 2) := SmoothTails.Ein_nonneg hσ2.le
  have hl2' : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  simp only [hw] at ht ⊢
  push_cast at ht ⊢
  nlinarith

/-! ### The product -/

/-- `p - p^σ ≥ p/3` for a prime `p ≤ N` when `0 < σ ≤ 1/100` and `σ log N ≤ 2`. -/
lemma sub_rpow_ge {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100) {p N : ℕ} (hp : 2 ≤ p)
    (hpN : p ≤ N) (hσN : σ * Real.log N ≤ 2) : (p : ℝ) / 3 ≤ p - (p : ℝ) ^ σ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hlp : σ * Real.log p ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hpN') hσ.le) hσN
  rw [rpow_eq_exp_mul_log (by linarith)]
  rcases le_or_gt 12 p with h12 | h12
  · have : (12 : ℝ) ≤ p := by exact_mod_cast h12
    have he : Real.exp (σ * Real.log p) ≤ Real.exp 2 := Real.exp_le_exp.mpr hlp
    have he2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    linarith
  · have h12' : (p : ℝ) < 12 := by exact_mod_cast h12
    have hl : Real.log p ≤ 11 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < p); linarith
    have hu : σ * Real.log p ≤ 0.11 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ p); nlinarith
    have hu0 : 0 ≤ σ * Real.log p := mul_nonneg hσ.le (Real.log_nonneg (by linarith))
    have he : Real.exp (σ * Real.log p) ≤ 4 / 3 := by
      rcases eq_or_lt_of_le hu0 with h0 | h0
      · rw [← h0, Real.exp_zero]; norm_num
      · have := Real.exp_bound_div_one_sub_of_interval' h0 (by linarith)
        have : 1 / (1 - σ * Real.log p) ≤ 4 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
    linarith

/-- The per-prime comparison:
`(1 - p^{-(1-σ)})^{-1} ≤ (1 - p^{-1})^{-1} · exp((p^σ - 1)/(p - p^σ))`. -/
lemma factor_le {σ : ℝ} {p : ℝ} (hp : 2 ≤ p) (hpp : p / 3 ≤ p - p ^ σ) :
    (1 - p ^ (-(1 - σ)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ * Real.exp ((p ^ σ - 1) / (p - p ^ σ)) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - p ^ σ := by linarith
  have e1 : p ^ (-(1 - σ)) = p ^ σ / p := by
    rw [show -(1 - σ) = σ - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
  have e2 : p ^ (-(1 : ℝ)) = 1 / p := by rw [Real.rpow_neg_one, one_div]
  rw [e1, e2]
  have e3 : (1 - p ^ σ / p)⁻¹ = p / (p - p ^ σ) := by
    rw [show 1 - p ^ σ / p = (p - p ^ σ) / p by field_simp, inv_div]
  have e4 : (1 - 1 / p)⁻¹ = p / (p - 1) := by
    rw [show 1 - 1 / p = (p - 1) / p by field_simp, inv_div]
  rw [e3, e4]
  have h1 : 1 + (p ^ σ - 1) / (p - p ^ σ) ≤ Real.exp ((p ^ σ - 1) / (p - p ^ σ)) :=
    by linarith [Real.add_one_le_exp ((p ^ σ - 1) / (p - p ^ σ))]
  have hp1 : p - 1 ≠ 0 := by linarith
  have e5 : p / (p - p ^ σ) = p / (p - 1) * (1 + (p ^ σ - 1) / (p - p ^ σ)) := by
    field_simp
    ring
  rw [e5]
  exact mul_le_mul_of_nonneg_left h1 (div_nonneg hp0.le (by linarith))

/-- **The Rankin–Euler product for `ℕ`**: for `0 < σ ≤ 1/100`, `N ≥ 2` with `σ log N ≤ 2` and
`log(N+1) ≥ 10⁴`, `∏_{p ≤ N} (1 - p^{σ-1})^{-1} ≤ 1.8 log(N+1) e^{Ein(2) + 840σ}`. -/
theorem rankinConst_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100) {N : ℕ} (hN : 2 ≤ N)
    (hσN : σ * Real.log N ≤ 2) (hlog : 10 ^ 4 ≤ Real.log ((N + 1 : ℕ) : ℝ)) :
    Rankin.rankinConst (N + 1) (1 - σ) ≤
      1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (Ein 2 + 840 * σ) := by
  have hmem : ∀ p ∈ (N + 1).primesBelow, 2 ≤ p ∧ p ≤ N := by
    intro p hp
    have := Nat.mem_primesBelow.mp hp
    exact ⟨this.2.two_le, by omega⟩
  -- the factorwise comparison
  have hprod : Rankin.rankinConst (N + 1) (1 - σ) ≤ BaseFactor.ZinfR (N + 1) 1 *
      Real.exp (∑ p ∈ (N + 1).primesBelow, (((p : ℝ) ^ σ - 1) / (p - (p : ℝ) ^ σ))) := by
    unfold Rankin.rankinConst BaseFactor.ZinfR
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1
      apply inv_nonneg.mpr
      have : (p : ℝ) ^ (-(1 - σ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      linarith
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1
      exact factor_le hp2 (sub_rpow_ge hσ hσ1 (hmem p hp).1 (hmem p hp).2 hσN)
  -- the sum
  have hsum : ∑ p ∈ (N + 1).primesBelow, (((p : ℝ) ^ σ - 1) / (p - (p : ℝ) ^ σ)) ≤
      Ein 2 + 840 * σ := by
    have hsplit : ∀ p ∈ (N + 1).primesBelow, ((p : ℝ) ^ σ - 1) / (p - (p : ℝ) ^ σ) ≤
        ((p : ℝ) ^ σ - 1) / p + 3 * Real.exp 4 * σ * (Real.log p / (p * (p - 1))) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1
      have hpN : (p : ℝ) ≤ N := by exact_mod_cast (hmem p hp).2
      have hpp := sub_rpow_ge hσ hσ1 (hmem p hp).1 (hmem p hp).2 hσN
      have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hlp : σ * Real.log p ≤ 2 :=
        le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hpN) hσ.le) hσN
      set r := (p : ℝ) ^ σ with hr
      have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith) hσ.le
      have hre : r = Real.exp (σ * Real.log p) := rpow_eq_exp_mul_log (by linarith)
      have hr2 : r ≤ Real.exp 2 := by rw [hre]; exact Real.exp_le_exp.mpr hlp
      -- `r - 1 ≤ σ log p · r`
      have hr3 : r - 1 ≤ σ * Real.log p * r := by
        rw [hre]
        have := Real.add_one_le_exp (-(σ * Real.log p))
        have h2 : Real.exp (-(σ * Real.log p)) * Real.exp (σ * Real.log p) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (σ * Real.log p)]
      have hd : 0 < (p : ℝ) - r := by linarith
      have e : (r - 1) / (p - r) = (r - 1) / p + (r - 1) * r / (p * (p - r)) := by
        field_simp; ring
      rw [e]
      have h4 : (r - 1) * r / (p * (p - r)) ≤ 3 * Real.exp 4 * σ * (Real.log p / (p * (p - 1)))
          := by
        have he4 : Real.exp 2 * Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
        have hnum : (r - 1) * r ≤ σ * Real.log p * Real.exp 4 := by
          have h5 : (r - 1) * r ≤ σ * Real.log p * r * r :=
            mul_le_mul_of_nonneg_right hr3 (by linarith)
          have h6 : r * r ≤ Real.exp 4 := by rw [← he4]; nlinarith
          have h7 : 0 ≤ σ * Real.log p := mul_nonneg hσ.le hlp0
          nlinarith
        have hden : p * (p - 1) / 3 ≤ p * (p - r) := by nlinarith
        have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
        rw [div_le_iff₀ (by positivity)]
        calc (r - 1) * r ≤ σ * Real.log p * Real.exp 4 := hnum
          _ = 3 * Real.exp 4 * σ * (Real.log p / (p * (p - 1))) * (p * (p - 1) / 3) := by
              field_simp
          _ ≤ 3 * Real.exp 4 * σ * (Real.log p / (p * (p - 1))) * (p * (p - r)) := by
              apply mul_le_mul_of_nonneg_left hden
              have : 0 ≤ Real.log p / (p * (p - 1)) := by
                apply div_nonneg hlp0; nlinarith
              positivity
      linarith
    refine (Finset.sum_le_sum hsplit).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := sum_rpow_sub_one_div_le hσ hN hσN
    have h2 := Mertens.sum_log_div_mul_pred_le N
    have he4 : Real.exp 4 ≤ 55 := by
      have h := Real.exp_one_lt_d9
      have e : Real.exp 4 = (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
        rw [show (4:ℝ) = 1 + 1 + (1 + 1) by norm_num, Real.exp_add, Real.exp_add]
      rw [e]
      have h1 : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
      nlinarith [Real.exp_pos 1]
    have : 3 * Real.exp 4 * σ * ∑ p ∈ (N + 1).primesBelow, Real.log p / (p * (p - 1)) ≤
        3 * 55 * σ * 5 := by
      have h0 : 0 ≤ ∑ p ∈ (N + 1).primesBelow, Real.log p / (p * (p - 1)) := by
        apply Finset.sum_nonneg
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1
        apply div_nonneg (Real.log_nonneg (by linarith)); nlinarith
      have : 3 * Real.exp 4 * σ ≤ 3 * 55 * σ := by nlinarith
      nlinarith [Real.exp_pos 4]
    nlinarith
  have hZ := Mertens.ZinfR_one_le hlog
  have hZ0 : 0 ≤ BaseFactor.ZinfR (N + 1) 1 := by
    unfold BaseFactor.ZinfR
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hmem p hp).1
    apply inv_nonneg.mpr
    have : (p : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    linarith
  calc Rankin.rankinConst (N + 1) (1 - σ)
      ≤ BaseFactor.ZinfR (N + 1) 1 *
        Real.exp (∑ p ∈ (N + 1).primesBelow, (((p : ℝ) ^ σ - 1) / (p - (p : ℝ) ^ σ))) := hprod
    _ ≤ 1.8 * Real.log ((N + 1 : ℕ) : ℝ) * Real.exp (Ein 2 + 840 * σ) :=
        mul_le_mul hZ (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le (by positivity)

end BaseRange
