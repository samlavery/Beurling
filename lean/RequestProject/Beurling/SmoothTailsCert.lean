module

public import RequestProject.Beurling.SmoothTails
public import RequestProject.Beurling.Mertens
public import RequestProject.BSCert.RankinCert
public import RequestProject.BSCert.EiCert
public import RequestProject.BSCert.Finite.ChebN

/-!
# Lemma 6.22(c), first part, with the Euler-product estimate proved

`SmoothTails.smooth_tail_rankin` derives the smooth-tail bound `Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)`
from Rankin's bound and an estimate for `log ∏_{p<X₀} (1 - p^{-σ})^{-1}`, which was a hypothesis
there. Here that estimate is **proved**, from three certificates of Appendix B:

* `R(0.69) ≤ 0.77` (`rankin_R.py`, `BSCert.Rankin.R_069_le`): for `σ ≥ 0.69`,
  `log ∏_{p<X₀} (1 - p^{-σ})^{-1} ≤ ∑_{p<X₀} p^{-σ} + R(σ) ≤ ∑_{p<X₀} p^{-σ} + 0.77`
  (`log_rankinConst_le`);
* `ψ(x) ≤ 1.42 x` (`finite_checks.py`, Lemma 5.1(i), `BSCert.FiniteN.psi_le_one_point_four_two`):
  by partial summation against `θ(x) ≤ ψ(x)` and comparison with
  `F(t) = log log t + Ein(η log t)`, whose derivative is `t^{-σ}/log t` (`η = 1 - σ`),
  `∑_{p<X₀} p^{-σ} ≤ 1.42 (2/log 2 + 0.38 + log Λ + Ein(η Λ))` (`sum_rpow_primes_le`);
* `Ei(x) ≤ (eˣ/x)(1 + 2/x)` for `x ≥ 11` (`rankin_R.py`, `BSCert.EiFn.Ei_le_of_ge_11`): at
  `x = ηΛ = log(u log u)` this gives `Ein(ηΛ) ≤ u` (`Ein_le_u`).

Here `ψ ≤ 1.42 x` is weaker than the Rosser–Schoenfeld bound used in the paper, so the
intermediate estimate is `log ∏ ≤ 1.42 log Λ + 1.42 u + 5.5` instead of `log Λ + 1.3 u + 2`; the
final bound `Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)` is the same (`smooth_tail_rankin_cert`). The only
extra condition is `σ ≥ 0.69`, the range of the certificate `R(0.69) ≤ 0.77`.
-/

@[expose] public section

open Real Finset

namespace SmoothTails

/-! ### The prime-power part: `R(0.69) ≤ 0.77` -/

lemma rTerm_anti {p : ℕ} (hp : 2 ≤ p) {σ τ : ℝ} (hτ : 0 < τ) (hστ : τ ≤ σ) :
    BSCert.Rankin.rTerm σ p ≤ BSCert.Rankin.rTerm τ p := by
  unfold BSCert.Rankin.rTerm
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set a := (p : ℝ) ^ (-σ)
  set b := (p : ℝ) ^ (-τ)
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by linarith) _
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have h1 : Real.log ((1 - b) / (1 - a)) ≤ (1 - b) / (1 - a) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  rw [Real.log_div (by linarith) (by linarith)] at h1
  have h2 : (1 - b) / (1 - a) - 1 ≤ a - b := by
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

lemma log_rankinConst_le (X₀ : ℕ) {σ : ℝ} (hσ : 0.69 ≤ σ) :
    Real.log (Rankin.rankinConst X₀ σ) ≤ ∑ p ∈ X₀.primesBelow, (p : ℝ) ^ (-σ) + 0.77 := by
  have hfac : ∀ p ∈ X₀.primesBelow, 0 < 1 - (p : ℝ) ^ (-σ) := by
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    linarith
  have hlog : Real.log (Rankin.rankinConst X₀ σ) =
      ∑ p ∈ X₀.primesBelow, ((p : ℝ) ^ (-σ) + BSCert.Rankin.rTerm σ p) := by
    unfold Rankin.rankinConst
    rw [Real.log_prod (fun p hp => (inv_pos.mpr (hfac p hp)).ne')]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_inv]; unfold BSCert.Rankin.rTerm; ring
  rw [hlog, Finset.sum_add_distrib]
  gcongr
  have hs1 := BSCert.Rankin.summable_rTerm (σ := σ) (by linarith)
  have hs2 := BSCert.Rankin.summable_rTerm (σ := 69/100) (by norm_num)
  have hnn : ∀ q : Nat.Primes, 0 ≤ BSCert.Rankin.rTerm σ q := fun q =>
    BSCert.Rankin.rTerm_nonneg (by linarith) q.2.two_le
  have e : ∑ p ∈ X₀.primesBelow, BSCert.Rankin.rTerm σ p =
      ∑ q ∈ X₀.primesBelow.subtype Nat.Prime, BSCert.Rankin.rTerm σ q := by
    rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
    intro p hp; exact (Nat.mem_primesBelow.mp hp).2
  rw [e]
  calc _ ≤ BSCert.Rankin.R σ := hs1.sum_le_tsum _ (fun q _ => hnn q)
    _ ≤ BSCert.Rankin.R (69/100) :=
        hs1.tsum_le_tsum (fun q => rTerm_anti q.2.two_le (by norm_num) (by linarith)) hs2
    _ ≤ 0.77 := by have := BSCert.Rankin.R_069_le; norm_num at this ⊢; linarith

/-! ### Partial summation against `θ(x) ≤ 1.42 x` -/

lemma theta_partial_le (N : ℕ) :
    ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) ≤ 1.42 * N := by
  have h1 := BSCert.FiniteN.psi_le_one_point_four_two (x := (N : ℝ)) (Nat.cast_nonneg _)
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  have e : Chebyshev.theta (N : ℝ) =
      ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro k hk; simp at hk ⊢; omega
    · intro k hk hk'
      simp at hk hk'
      have : ¬ k.Prime := by intro hp; have := hp.two_le; omega
      simp [this]
  linarith

/-- The weight `h(t) = t^{-σ}/log t`. -/
noncomputable def hw (σ t : ℝ) : ℝ := t ^ (-σ) / Real.log t

lemma hw_anti {σ : ℝ} (hσ : 0 < σ) {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : hw σ t ≤ hw σ s := by
  unfold hw
  have hls : 0 < Real.log s := Real.log_pos hs
  have hlst : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  have h1 : t ^ (-σ) ≤ s ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by linarith) hst (by linarith)
  have h0 : 0 ≤ t ^ (-σ) := Real.rpow_nonneg (by linarith) _
  calc t ^ (-σ) / Real.log t ≤ s ^ (-σ) / Real.log t := by gcongr; linarith
    _ ≤ s ^ (-σ) / Real.log s := by
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hls hlst

lemma sum_rpow_primes_le_abel {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ (N + 1).primesBelow, (p : ℝ) ^ (-σ) ≤
      1.42 * (2 * hw σ 2 + ∑ n ∈ Icc 3 N, hw σ n) := by
  have e : ∑ p ∈ (N + 1).primesBelow, (p : ℝ) ^ (-σ) =
      ∑ k ∈ Icc 2 N, (if k.Prime then Real.log k else 0) * hw σ k := by
    rw [Mertens.sum_primesBelow_eq]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs with hp
    · unfold hw
      have : Real.log k ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp
    · simp
  rw [e]
  have hw2 : ∀ n : ℕ, 2 ≤ n → 0 ≤ hw σ n := fun n hn => by
    unfold hw
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg this.le)
  have := Mertens.abel_upper (fun k => if k.Prime then Real.log k else 0) (fun n => hw σ n)
    (fun n => 1.42 * n) (fun N _ => theta_partial_le N)
    (fun n hn => by
      have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      exact hw_anti hσ this (by push_cast; linarith))
    hw2 hN
  refine this.trans (le_of_eq ?_)
  simp only
  rw [mul_add, Finset.mul_sum]
  congr 1
  · push_cast; ring
  · apply Finset.sum_congr rfl
    intro n hn
    simp at hn
    rw [Nat.cast_sub (by omega)]; push_cast; ring

/-! ### Comparison with `F(t) = log log t + Ein(η log t)` -/

/-- `F(t) = log log t + Ein(η log t)`. -/
noncomputable def Fcmp (η t : ℝ) : ℝ := Real.log (Real.log t) + BSCert.EiFn.Ein (η * Real.log t)

lemma hasDerivAt_Fcmp {η t : ℝ} (hη : 0 < η) (ht : 1 < t) :
    HasDerivAt (Fcmp η) (hw (1 - η) t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 : HasDerivAt (fun t => Real.log t) t⁻¹ t := Real.hasDerivAt_log ht0.ne'
  have h2 := h1.log hl.ne'
  have h3 := (h1.const_mul η)
  have h4 := (BSCert.EiFn.hasDerivAt_Ein (mul_pos hη hl)).comp t h3
  have h5 := h2.add h4
  unfold Fcmp
  convert h5 using 1
  unfold hw
  rw [Real.rpow_def_of_pos ht0]
  have : Real.log t * -(1 - η) = η * Real.log t - Real.log t := by ring
  rw [this, Real.exp_sub, Real.exp_log ht0]
  field_simp
  ring

lemma sum_hw_le_Fcmp {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, hw (1 - η) n ≤ Fcmp η N - Fcmp η 2 := by
  have step : ∀ n : ℕ, 3 ≤ n → hw (1 - η) n ≤ Fcmp η n - Fcmp η (n - 1 : ℕ) := by
    intro n hn
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hc]
    obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope (Fcmp η) (fun t => hw (1 - η) t)
      (show (n : ℝ) - 1 < n by linarith)
      (fun x hx => (hasDerivAt_Fcmp hη (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_Fcmp hη (by linarith [hx.1]))
    simp only [sub_sub_cancel, div_one] at hc2
    rw [← hc2]
    exact hw_anti (by linarith) (by linarith [hc1.1]) hc1.2.le
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := step (M + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    push_cast at this ⊢
    linarith

lemma Ein_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ BSCert.EiFn.Ein x := by
  unfold BSCert.EiFn.Ein
  apply intervalIntegral.integral_nonneg hx
  intro w hw
  exact div_nonneg (by linarith [Real.add_one_le_exp w, hw.1]) hw.1

lemma Ein_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : BSCert.EiFn.Ein x ≤ BSCert.EiFn.Ein y := by
  unfold BSCert.EiFn.Ein
  have hi1 := BSCert.EiFn.integrand_intervalIntegrable hx
  have hi2 := BSCert.EiFn.integrand_intervalIntegrable (hx.trans hxy)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 (hi1.symm.trans hi2)]
  have : 0 ≤ ∫ w in x..y, (Real.exp w - 1) / w := by
    apply intervalIntegral.integral_nonneg hxy
    intro w hw
    have : 0 ≤ w := hx.trans hw.1
    exact div_nonneg (by linarith [Real.add_one_le_exp w]) this
  linarith

/-- `∑_{p<X₀} p^{-σ} ≤ 1.42 (2/log 2 + 0.38 + log Λ + Ein(ηΛ))`, `η = 1 - σ`, `Λ = log X₀`. -/
lemma sum_rpow_primes_le {X₀ : ℕ} (hX₀ : 3 ≤ X₀) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∑ p ∈ X₀.primesBelow, (p : ℝ) ^ (-(1 - η)) ≤
      1.42 * (2 / Real.log 2 + 0.38 + Real.log (Real.log X₀) +
        BSCert.EiFn.Ein (η * Real.log X₀)) := by
  obtain ⟨N, rfl⟩ : ∃ N, X₀ = N + 1 := ⟨X₀ - 1, by omega⟩
  have hN : 2 ≤ N := by omega
  have h1 := sum_rpow_primes_le_abel (σ := 1 - η) (by linarith) hN
  have h2 := sum_hw_le_Fcmp hη hη1 hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhw2 : 2 * hw (1 - η) 2 ≤ 2 / Real.log 2 := by
    unfold hw
    have : (2 : ℝ) ^ (-(1 - η)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rw [mul_div_assoc']
    gcongr; linarith
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlN : 0 < Real.log N := Real.log_pos hN1
  have hlNX : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have hF : Fcmp η N - Fcmp η 2 ≤ 0.38 + Real.log (Real.log ((N + 1 : ℕ) : ℝ)) +
      BSCert.EiFn.Ein (η * Real.log ((N + 1 : ℕ) : ℝ)) := by
    unfold Fcmp
    have e1 : Real.log (Real.log N) ≤ Real.log (Real.log ((N + 1 : ℕ) : ℝ)) :=
      Real.log_le_log hlN hlNX
    have e2 := Ein_mono (x := η * Real.log N) (y := η * Real.log ((N + 1 : ℕ) : ℝ))
      (by positivity) (by gcongr)
    have e3 := Ein_nonneg (x := η * Real.log 2) (by positivity)
    have e4 : -0.38 ≤ Real.log (Real.log 2) := by
      rw [Real.le_log_iff_exp_le hl2]
      have h := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.38 by norm_num)
      have h2 := Real.log_two_gt_d9
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) hl2]
      calc (Real.log 2)⁻¹ ≤ (0.6931471803 : ℝ)⁻¹ := by
            apply inv_anti₀ (by norm_num); linarith
        _ ≤ 1 + 0.38 + 0.38 ^ 2 / 2 := by norm_num
        _ ≤ _ := h
    have e5 : (((2 : ℕ) : ℝ)) = 2 := by norm_num
    linarith
  calc _ ≤ 1.42 * (2 * hw (1 - η) 2 + ∑ n ∈ Icc 3 N, hw (1 - η) n) := by
        simpa using h1
    _ ≤ 1.42 * (2 / Real.log 2 + (0.38 + Real.log (Real.log ((N + 1 : ℕ) : ℝ)) +
        BSCert.EiFn.Ein (η * Real.log ((N + 1 : ℕ) : ℝ)))) := by
        gcongr; linarith
    _ = _ := by ring

/-! ### The exponential integral at `x = log(u log u)` -/

lemma Ein_le_u {u : ℝ} (hu : 10 ^ 4 ≤ u) :
    BSCert.EiFn.Ein (Real.log (u * Real.log u)) ≤ u := by
  have hu0 : 0 < u := by linarith
  have h9 : 9 ≤ Real.log u := by
    have he : Real.exp 9 ≤ 10 ^ 4 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 := pow_le_pow_left₀ (by positivity) this.le 9
        _ ≤ 10 ^ 4 := by norm_num
    rw [Real.le_log_iff_exp_le hu0]; linarith
  have h2 : 2 ≤ Real.log (Real.log u) := by
    have he : Real.exp 2 ≤ 9 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (by positivity) this.le 2
        _ ≤ 9 := by norm_num
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  set L1 := Real.log u
  set L2 := Real.log L1
  have hx : Real.log (u * L1) = L1 + L2 := Real.log_mul hu0.ne' (by linarith)
  have hx11 : 11 ≤ Real.log (u * L1) := by
    have he : Real.exp 11 ≤ 10 ^ 4 * 9 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 := pow_le_pow_left₀ (by positivity) this.le 11
        _ ≤ 10 ^ 4 * 9 := by norm_num
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith
  set x := Real.log (u * L1)
  have hEi := BSCert.EiFn.Ei_le_of_ge_11 hx11
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hEin : BSCert.EiFn.Ein x ≤ BSCert.EiFn.Ei x := by
    unfold BSCert.EiFn.Ei; linarith
  have hexp : Real.exp x = u * L1 := Real.exp_log (by positivity)
  rw [hexp] at hEi
  have hx0 : 0 < x := by linarith
  have key : u * L1 / x * (1 + 2 / x) ≤ u := by
    rw [show u * L1 / x * (1 + 2 / x) = u * (L1 * (x + 2)) / x ^ 2 by field_simp]
    rw [div_le_iff₀ (by positivity)]
    have : L1 * (x + 2) ≤ x ^ 2 := by rw [hx]; nlinarith
    nlinarith
  linarith

/-! ### Lemma 6.22(c), first part -/

/-- **The Euler-product estimate of Lemma 6.22(c)**, proved from the certificates:
for `X₀ ≥ 3`, `Λ = log X₀`, `u ≥ 10⁴`, `σ = 1 - log(u log u)/Λ ∈ [0.69, 1)`,
`log ∏_{p<X₀} (1 - p^{-σ})^{-1} ≤ 1.42 log Λ + 1.42 u + 5.5`. -/
theorem euler_estimate {X₀ : ℕ} (hX₀ : 3 ≤ X₀) {u : ℝ} (hu : 10 ^ 4 ≤ u)
    (hσ : 0.69 ≤ 1 - Real.log (u * Real.log u) / Real.log X₀) :
    Real.log (Rankin.rankinConst X₀ (1 - Real.log (u * Real.log u) / Real.log X₀)) ≤
      1.42 * Real.log (Real.log X₀) + 1.42 * u + 5.5 := by
  have hΛ : 0 < Real.log X₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < X₀))
  have hu0 : 0 < u := by linarith
  have hlu : 1 < Real.log u := by
    rw [Real.lt_log_iff_exp_lt hu0]
    have := Real.exp_one_lt_d9; linarith
  have hul : 0 < Real.log (u * Real.log u) := Real.log_pos (by nlinarith)
  set η := Real.log (u * Real.log u) / Real.log X₀ with hηdef
  have hη : 0 < η := div_pos hul hΛ
  have hη1 : η < 1 := by linarith
  have hηΛ : η * Real.log X₀ = Real.log (u * Real.log u) := by
    rw [hηdef]; field_simp
  have h1 := log_rankinConst_le X₀ hσ
  have h2 := sum_rpow_primes_le hX₀ hη hη1
  have h3 := Ein_le_u hu
  rw [hηΛ] at h2
  have hl2 : 2 / Real.log 2 ≤ 2.886 := by
    have := Real.log_two_gt_d9
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma tail_arith_cert {u Λ : ℝ} (hu : 10 ^ 4 ≤ u) (huΛ : Real.log Λ ≤ u) :
    -u * Real.log u - u * Real.log (Real.log u) + (1.42 * Real.log Λ + 1.42 * u + 5.5) ≤
      -0.9 * (u * Real.log u) := by
  have hu0 : 0 < u := by linarith
  have h9 : 9 ≤ Real.log u := by
    have he : Real.exp 9 ≤ 10 ^ 4 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 := pow_le_pow_left₀ (by positivity) this.le 9
        _ ≤ 10 ^ 4 := by norm_num
    rw [Real.le_log_iff_exp_le hu0]; linarith
  have h2 : 2 ≤ Real.log (Real.log u) := by
    have he : Real.exp 2 ≤ 9 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (by positivity) this.le 2
        _ ≤ 9 := by norm_num
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have k1 : 9 * u ≤ u * Real.log u := by nlinarith
  have k2 : 2 * u ≤ u * Real.log (Real.log u) := by nlinarith
  nlinarith

/-- **Lemma 6.22(c)**, first part, with the Euler-product estimate proved from the certificates
`R(0.69) ≤ 0.77`, `ψ(x) ≤ 1.42 x` and `Ei(x) ≤ (eˣ/x)(1 + 2/x)`. Let `X₀ ≥ 3`, `Λ = log X₀`,
`Y > 0`, `u = log Y / Λ` with `u ≥ max(10⁴, log Λ)`, and `σ = 1 - log(u log u)/Λ ≥ 0.69`. Then
`Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)`. -/
theorem smooth_tail_rankin_cert {X₀ : ℕ} (hX₀ : 3 ≤ X₀) {Y : ℝ} (hY : 0 < Y)
    (hu : 10 ^ 4 ≤ Real.log Y / Real.log X₀)
    (huΛ : Real.log (Real.log X₀) ≤ Real.log Y / Real.log X₀)
    (hσ : 0.69 ≤ 1 - Real.log (Real.log Y / Real.log X₀ *
      Real.log (Real.log Y / Real.log X₀)) / Real.log X₀) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤
      Y * Real.exp (-0.9 * (Real.log Y / Real.log X₀ *
        Real.log (Real.log Y / Real.log X₀))) := by
  set Λ := Real.log X₀ with hΛ
  set u := Real.log Y / Λ with hudef
  set σ := 1 - Real.log (u * Real.log u) / Λ with hσdef
  have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (by omega : 1 < X₀))
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hR := Rankin.smoothCount_le_rankin X₀ (show 0 < σ by linarith) hY.le
  have hRpos : 0 < Rankin.rankinConst X₀ σ := by
    unfold Rankin.rankinConst
    apply Finset.prod_pos
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
    positivity
  have hEuler := euler_estimate hX₀ hu hσ
  have hRle : Rankin.rankinConst X₀ σ ≤
      Real.exp (1.42 * Real.log Λ + 1.42 * u + 5.5) := by
    rw [← Real.exp_log hRpos]; exact Real.exp_le_exp.mpr hEuler
  have hYσ : Y ^ σ = Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u)) := by
    rw [Real.rpow_def_of_pos hY, ← Real.exp_log hY]
    rw [Real.log_exp, ← Real.exp_add]
    congr 1
    have hlY : Real.log Y = u * Λ := by rw [hudef]; field_simp
    rw [hσdef, Real.log_mul hu0.ne' hlu.ne', hlY]
    field_simp
    ring
  calc (Rankin.smoothCount X₀ Y : ℝ) ≤ Y ^ σ * Rankin.rankinConst X₀ σ := hR
    _ ≤ Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u)) *
          Real.exp (1.42 * Real.log Λ + 1.42 * u + 5.5) := by
        rw [hYσ]; exact mul_le_mul_of_nonneg_left hRle (by positivity)
    _ = Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u) +
          (1.42 * Real.log Λ + 1.42 * u + 5.5)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ Y * Real.exp (-0.9 * (u * Real.log u)) := by
        apply mul_le_mul_of_nonneg_left _ hY.le
        exact Real.exp_le_exp.mpr (tail_arith_cert hu huΛ)

end SmoothTails
