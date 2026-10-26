module

public import RequestProject.BSCert.CaplChecks
meta import RequestProject.BSCert.CaplChecks

/-!
# The raise of `H` over `H_std` (`raise_max.py`, Theorem 6.23(c))

`raise_max.py` evaluates, on a grid of `(Λ, s)`, the raise
`max(0, 2 log M̄₁ - 8ℓ²)/L` of `log H` over `log H_std`, where
* `ℓ = 2 log Λ + s`, `L = e^ℓ`;
* `log c = max(4ℓ² - log 4, γ(s) Λ)`;
* `r̄₀ = L/(3ℓ) + 4` and `M̄₁ = r̄₀ + φ(r̄₀) + 1` with `φ(u) = c + u√c + u(u+1)/2`;

and compares its maximum with the bound `10⁻⁶` used in the proof. We prove the bound
`≤ 10⁻⁶` for **all** `Λ ≥ 10⁸` and `s ≥ -log Λ` (the script samples
`Λ ∈ [10⁸, 10³⁰]`, `s ∈ [-log Λ, 30]`), following the analytic argument of the paper
(`M̄₁ ≤ 2c`, then `(2γΛ + 2)/L ≤ 10⁻⁶`).
-/

@[expose] public section

namespace BSCert.Capl

open Real Set

/-- `log c = max(4ℓ² - log 4, γ(s)Λ)` with `ℓ = 2 log Λ + s`. -/
noncomputable def logc (sH Λ s : ℝ) : ℝ :=
  max (4 * (2 * Real.log Λ + s) ^ 2 - Real.log 4) (gam sH s * Λ)

/-- `r̄₀ = L/(3ℓ) + 4`. -/
noncomputable def rbar0 (Λ s : ℝ) : ℝ :=
  Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4

/-- `M̄₁ = r̄₀ + φ(r̄₀) + 1`, `φ(u) = c + u√c + u(u+1)/2`. -/
noncomputable def Mbar1 (sH Λ s : ℝ) : ℝ :=
  let c := Real.exp (logc sH Λ s)
  let r := rbar0 Λ s
  r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1

/-- The raise `max(0, 2 log M̄₁ - 8ℓ²)/L`. -/
noncomputable def raise (sH Λ s : ℝ) : ℝ :=
  max 0 (2 * Real.log (Mbar1 sH Λ s) - 8 * (2 * Real.log Λ + s) ^ 2)
    / Real.exp (2 * Real.log Λ + s)

/-! ## `M̄₁ ≤ 2c` -/

lemma Mbar1_le {sH Λ s : ℝ} (hl : 18 ≤ 2 * Real.log Λ + s) :
    Mbar1 sH Λ s ≤ 2 * Real.exp (logc sH Λ s) := by
  set ℓ := 2 * Real.log Λ + s with hℓ
  set X := logc sH Λ s
  have hX : 4 * ℓ ^ 2 - Real.log 4 ≤ X := le_max_left _ _
  set c := Real.exp X
  set q := Real.sqrt c
  have hc0 : 0 < c := Real.exp_pos X
  have hq2 : q ^ 2 = c := Real.sq_sqrt hc0.le
  have hq0 : 0 < q := Real.sqrt_pos.mpr hc0
  -- `q ≥ e^{2ℓ²}/2`
  have hq : Real.exp (2 * ℓ ^ 2) / 2 ≤ q := by
    have h4 : Real.exp (4 * ℓ ^ 2) / 4 ≤ c := by
      have : Real.exp (4 * ℓ ^ 2 - Real.log 4) = Real.exp (4 * ℓ ^ 2) / 4 := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]
      rw [← this]; exact Real.exp_le_exp.mpr hX
    have e : (Real.exp (2 * ℓ ^ 2) / 2) ^ 2 = Real.exp (4 * ℓ ^ 2) / 4 := by
      rw [div_pow, ← Real.exp_nat_mul]; ring_nf
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.exp (2 * ℓ ^ 2) / 2), e]
    exact Real.sqrt_le_sqrt h4
  -- `r̄₀ ≤ e^ℓ ≤ q/8`
  set r := rbar0 Λ s
  have hr0 : 0 ≤ r := by unfold r rbar0; rw [← hℓ]; positivity
  have heℓ : 1 ≤ Real.exp ℓ := Real.one_le_exp (by linarith)
  have hr : r ≤ Real.exp ℓ := by
    unfold r rbar0; rw [← hℓ]
    have h18 : (18 : ℝ) ≤ Real.exp ℓ := by
      have := Real.add_one_le_exp ℓ; linarith
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hrq : 8 * Real.exp ℓ ≤ q := by
    refine le_trans ?_ hq
    have h3 : (16 : ℝ) ≤ Real.exp 3 := by
      have := Real.sum_le_exp_of_nonneg (x := 3) (by norm_num) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
    have : Real.exp ℓ * Real.exp 3 ≤ Real.exp (2 * ℓ ^ 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos ℓ]
  have hq1 : 8 ≤ q := by nlinarith
  show r + (c + r * q + r * (r + 1) / 2) + 1 ≤ 2 * c
  rw [← hq2]
  nlinarith

/-! ## `(2γΛ + 2)/L ≤ 10⁻⁶` -/

lemma exp_two_log_add {Λ s : ℝ} (hΛ : 0 < Λ) :
    Real.exp (2 * Real.log Λ + s) = Λ ^ 2 * Real.exp s := by
  rw [Real.exp_add, show 2 * Real.log Λ = Real.log (Λ ^ 2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity)]

lemma log_18_42_ge : (2.9 : ℝ) ≤ Real.log 18.42 := by
  have h := logLoPt_le (a := 1842 / 100) (by norm_num)
  have hc : (29 / 10 : ℚ) ≤ logLoPt (1842 / 100) := by native_decide
  have hc' : ((29 / 10 : ℚ) : ℝ) ≤ ((logLoPt (1842 / 100) : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at h hc'
  norm_num at h hc' ⊢
  linarith

lemma exp_half_log1e8 : Real.exp (Real.log 100000000 / 2) = 10000 := by
  have h : Real.exp (Real.log 100000000 / 2) ^ 2 = 10000 ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast
    rw [show (2 : ℝ) * (Real.log 100000000 / 2) = Real.log 100000000 by ring,
      Real.exp_log (by norm_num)]; norm_num
  exact (pow_left_inj₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).mp h

lemma sqrt_mul_succ_le {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (a * (a + 1)) ≤ a + 1 :=
  calc Real.sqrt (a * (a + 1)) ≤ Real.sqrt ((a + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = a + 1 := Real.sqrt_sq (by linarith)

/-- Region `s > s_H`: `γ ≤ 7.5`. -/
lemma gam_le_of_gt {sH s : ℝ} (hg : gstar sH ≤ 7.5) (h : sH < s) : gam sH s ≤ 7.5 := by
  unfold gam
  rw [if_neg (by linarith)]
  split_ifs with h2
  · have h0 : 0 ≤ s - sH := by linarith
    have h1 : s - sH ≤ 1 := by linarith
    nlinarith
  · exact le_rfl

/-- Region `-log 10⁸ ≤ s ≤ 10`: `G(10⁸, s) ≤ 34.5 eˢ`. -/
lemma G8_le {s : ℝ} (hs0 : -Real.log 100000000 ≤ s) (hs1 : s ≤ 10) :
    G 100000000 s ≤ 34.5 * Real.exp s := by
  obtain ⟨hL1, hL2⟩ := log1e8_bounds
  set L8 := Real.log 100000000 with hL8
  set s0 := -L8
  have hl : 0 < 2 * L8 + s := by linarith
  have hA : A 100000000 s = Real.log 2 + 3 * L8 + 2 * s - Real.log (2 * L8 + s) :=
    A_eq (by norm_num) hl
  have hlog2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- bounds on `A`
  have hA14 : 14 ≤ A 100000000 s := by
    rw [hA]
    have htan : Real.log (2 * L8 + s) ≤ (2 * L8 + s) / 40 + Real.log 40 - 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2 * L8 + s) / 40) (by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      linarith
    have := log40_le
    linarith
  have hA77 : A 100000000 s ≤ 77 := by
    rw [hA]
    have : 0 ≤ Real.log (2 * L8 + s) := Real.log_nonneg (by linarith)
    linarith
  -- `(A + 1) e^{-s/2} ≤ (A₀ + 1) · 10⁴` with `A₀ + 1 ≤ 17.23`
  have hA0 : A 100000000 s ≤ Real.log 2 + L8 - Real.log L8 + 2 * (s - s0) := by
    rw [hA]
    have : Real.log L8 ≤ Real.log (2 * L8 + s) := Real.log_le_log (by linarith) (by linarith)
    simp only [s0]
    linarith
  have hlogL8 : 2.9 ≤ Real.log L8 :=
    le_trans log_18_42_ge (Real.log_le_log (by norm_num) hL1)
  have ht0 : 0 ≤ s - s0 := by simp only [s0]; linarith
  have hexp_t : 1 + (s - s0) / 2 ≤ Real.exp ((s - s0) / 2) := by
    have := Real.add_one_le_exp ((s - s0) / 2); linarith
  have hkey : (A 100000000 s + 1) * Real.exp (-s / 2) ≤ 17.23 * 10000 := by
    have e1 : Real.exp (-s / 2) = 10000 / Real.exp ((s - s0) / 2) := by
      rw [← exp_half_log1e8, ← Real.exp_sub]; congr 1; simp only [s0]; ring
    rw [e1, mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
    have hc : A 100000000 s + 1 ≤ 17.23 * Real.exp ((s - s0) / 2) := by
      have : A 100000000 s + 1 ≤ 17.23 + 2 * (s - s0) := by linarith
      nlinarith
    nlinarith
  -- the denominator
  have hden : 9999 ≤ Real.sqrt (100000000 - A 100000000 s - 1) := by
    rw [show (9999 : ℝ) = Real.sqrt (9999 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnum := sqrt_mul_succ_le (a := A 100000000 s) (by linarith)
  unfold G
  rw [div_le_iff₀ (by linarith)]
  have es : Real.exp (s / 2) = Real.exp (-s / 2) * Real.exp s := by
    rw [← Real.exp_add]; congr 1; ring
  rw [es]
  have hE := Real.exp_pos s
  have hE2 := Real.exp_pos (-s / 2)
  have h1 : 2 * Real.sqrt (A 100000000 s * (A 100000000 s + 1)) * (Real.exp (-s / 2) * Real.exp s)
      ≤ 2 * (17.23 * 10000) * Real.exp s := by
    have := mul_le_mul_of_nonneg_right hnum hE2.le
    nlinarith
  nlinarith

/-- Region `s < -log 10⁸`: here `Λ_s = e^{-s}`. -/
lemma gam_bound_low {sH Λ s : ℝ} (hsH : 5.9745 ≤ sH) (hΛ : 100000000 ≤ Λ)
    (hs : -Real.log Λ ≤ s) (hs8 : s < -Real.log 100000000) :
    2 * (gam sH s * Λ) + 2 ≤ Real.exp (2 * Real.log Λ + s) / 1000000 := by
  obtain ⟨hL1, hL2⟩ := log1e8_bounds
  set u := -s with hu
  have hu8 : Real.log 100000000 < u := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hΛu : Real.exp u ≤ Λ := by
    rw [← Real.exp_log hΛ0]; exact Real.exp_le_exp.mpr (by linarith)
  have heu8 : 100000000 ≤ Real.exp u := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 100000000)]
    exact Real.exp_le_exp.mpr hu8.le
  have hLam : LamS s = Real.exp u := by
    unfold LamS; rw [← hu]; exact max_eq_right heu8
  have hgam : gam sH s = 1.3 * G (Real.exp u) s := by
    unfold gam gstar; rw [if_pos (by linarith), hLam]
  -- `A(e^u, s) = log 2 + u - log u`
  have hA : A (Real.exp u) s = Real.log 2 + u - Real.log u := by
    rw [A_eq (Real.exp_pos u) (by rw [Real.log_exp]; linarith), Real.log_exp]
    rw [show 2 * u + s = u by rw [hu]; ring]; rw [hu]; ring
  have hlog2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogu : 2.9 ≤ Real.log u :=
    le_trans log_18_42_ge (Real.log_le_log (by norm_num) (by linarith))
  have hlogu' : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  set a := A (Real.exp u) s
  have ha0 : 0 ≤ a := by rw [hA]; linarith
  have ha1 : a + 1 ≤ u - 1.2 := by rw [hA]; linarith
  -- `u ≤ e^u / 5000`
  have hu5000 : u ≤ Real.exp u / 5000 := by
    have h1 : 10000 ≤ Real.exp (u / 2) := by
      rw [← exp_half_log1e8]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 : u / 2 ≤ Real.exp (u / 2) := by
      have := Real.add_one_le_exp (u / 2); linarith
    have e : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]; nlinarith
  have heu2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hden : 0.99 * Real.exp (u / 2) ≤ Real.sqrt (Real.exp u - a - 1) := by
    rw [show 0.99 * Real.exp (u / 2) = Real.sqrt ((0.99 * Real.exp (u / 2)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, heu2]
    nlinarith
  have hnum := sqrt_mul_succ_le ha0
  -- `G ≤ 2(a+1)e^{-u}/0.99`
  have hG : G (Real.exp u) s * 0.99 * Real.exp u ≤ 2 * (a + 1) := by
    unfold G
    have hd0 : 0 < Real.sqrt (Real.exp u - a - 1) :=
      lt_of_lt_of_le (by positivity) hden
    have es : Real.exp (s / 2) * Real.exp (u / 2) = 1 := by
      rw [← Real.exp_add, hu, show s / 2 + -s / 2 = 0 by ring, Real.exp_zero]
    have : 2 * Real.sqrt (a * (a + 1)) * Real.exp (s / 2) / Real.sqrt (Real.exp u - a - 1)
        * 0.99 * Real.exp u
        = 2 * Real.sqrt (a * (a + 1)) * (Real.exp (s / 2) * Real.exp (u / 2))
          * (0.99 * Real.exp (u / 2) / Real.sqrt (Real.exp u - a - 1)) := by
      rw [← heu2]; field_simp
    rw [this, es]
    have hq : 0.99 * Real.exp (u / 2) / Real.sqrt (Real.exp u - a - 1) ≤ 1 :=
      (div_le_one hd0).mpr hden
    have hq0 : 0 ≤ 0.99 * Real.exp (u / 2) / Real.sqrt (Real.exp u - a - 1) := by positivity
    have : 0 ≤ Real.sqrt (a * (a + 1)) := Real.sqrt_nonneg _
    nlinarith
  -- conclusion
  rw [exp_two_log_add hΛ0, hgam]
  have heu : 0 < Real.exp u := Real.exp_pos u
  have hes : Real.exp s * Real.exp u = 1 := by
    rw [← Real.exp_add, hu, show s + -s = 0 by ring, Real.exp_zero]
  set w := Λ * Real.exp s with hw
  have hw1 : 1 ≤ w := by
    have : Real.exp u * Real.exp s ≤ Λ * Real.exp s :=
      mul_le_mul_of_nonneg_right hΛu (Real.exp_pos s).le
    rw [mul_comm (Real.exp u), hes] at this; exact this
  have hGw : G (Real.exp u) s * Λ ≤ 2 * (a + 1) / 0.99 * w := by
    have : G (Real.exp u) s ≤ 2 * (a + 1) / 0.99 * Real.exp s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_right hG (Real.exp_pos s).le
      calc G (Real.exp u) s * 0.99 = G (Real.exp u) s * 0.99 * Real.exp u * Real.exp s := by
            rw [mul_assoc _ (Real.exp u), mul_comm (Real.exp u), hes, mul_one]
        _ ≤ 2 * (a + 1) * Real.exp s := this
    rw [hw]
    have hΛ0' : 0 ≤ Λ := hΛ0.le
    nlinarith
  -- `5.26(a+1) + 2 ≤ Λ/10⁶`
  have hbig : 2 * 1.3 * (2 * (a + 1) / 0.99) + 2 ≤ Λ / 1000000 := by
    have hex : 100000000 * (1 + (u - Real.log 100000000)) ≤ Real.exp u := by
      have h1 := Real.add_one_le_exp (u - Real.log 100000000)
      have h2 : Real.exp u = 100000000 * Real.exp (u - Real.log 100000000) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]; field_simp
      rw [h2]; linarith
    have : 2 * 1.3 * (2 * (a + 1) / 0.99) ≤ 5.2526 * (u - 1.2) := by
      have e : 2 * 1.3 * (2 * (a + 1) / 0.99) = (520 / 99) * (a + 1) := by ring
      rw [e]; nlinarith
    linarith
  calc 2 * (1.3 * G (Real.exp u) s * Λ) + 2
      = 2 * 1.3 * (G (Real.exp u) s * Λ) + 2 := by ring
    _ ≤ 2 * 1.3 * (2 * (a + 1) / 0.99 * w) + 2 * w := by linarith
    _ = (2 * 1.3 * (2 * (a + 1) / 0.99) + 2) * w := by ring
    _ ≤ Λ / 1000000 * w := mul_le_mul_of_nonneg_right hbig (by linarith)
    _ = Λ ^ 2 * Real.exp s / 1000000 := by rw [hw]; ring

/-- The bound on `γ(s)Λ` in all three regimes of `s`. -/
lemma gam_bound {sH Λ s : ℝ} (hsH : 5.9745 ≤ sH) (hsH2 : sH ≤ 10) (hg : gstar sH ≤ 7.5)
    (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) :
    2 * (gam sH s * Λ) + 2 ≤ Real.exp (2 * Real.log Λ + s) / 1000000 := by
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : Real.log 100000000 ≤ Real.log Λ := Real.log_le_log (by norm_num) hΛ
  have hw1 : 1 ≤ Λ * Real.exp s := by
    have : Real.exp (-Real.log Λ) ≤ Real.exp s := Real.exp_le_exp.mpr hs
    rw [Real.exp_neg, Real.exp_log hΛ0] at this
    rw [inv_le_iff_one_le_mul₀' hΛ0] at this; linarith
  rcases lt_or_ge sH s with h | h
  · -- `s > s_H`
    have hγ := gam_le_of_gt hg h
    rw [exp_two_log_add hΛ0]
    have hE : 393 ≤ Real.exp s := le_trans exp_sH_ge (Real.exp_le_exp.mpr (by linarith))
    have : gam sH s * Λ ≤ 7.5 * Λ := mul_le_mul_of_nonneg_right hγ hΛ0.le
    nlinarith
  · rcases lt_or_ge s (-Real.log 100000000) with h8 | h8
    · exact gam_bound_low hsH hΛ hs h8
    · -- `-log 10⁸ ≤ s ≤ s_H`
      have hLam : LamS s = 100000000 := by
        unfold LamS; apply max_eq_left
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 100000000)]
        exact Real.exp_le_exp.mpr (by linarith)
      have hgam : gam sH s = 1.3 * G 100000000 s := by
        unfold gam gstar; rw [if_pos h, hLam]
      have hG := G8_le h8 (by linarith)
      rw [exp_two_log_add hΛ0, hgam]
      have hE := Real.exp_pos s
      have : 1.3 * G 100000000 s * Λ ≤ 1.3 * (34.5 * Real.exp s) * Λ := by
        apply mul_le_mul_of_nonneg_right _ hΛ0.le; linarith
      nlinarith

/-- **`raise_max.py`.** For every `Λ ≥ 10⁸` and `s ≥ -log Λ`, the raise of `log H` over
`log H_std`, divided by `L = log z`, is at most `10⁻⁶`. Here `s_H` is the break point of `γ`
(any `s_H ∈ [5.9745, 10]` with `γ*(s_H) ≤ 7.5`; in particular the root of `sH_spec`). -/
theorem raise_le {sH Λ s : ℝ} (hsH : 5.9745 ≤ sH) (hsH2 : sH ≤ 10) (hg : gstar sH ≤ 7.5)
    (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) : raise sH Λ s ≤ 1 / 1000000 := by
  have hlogΛ : 18.42 ≤ Real.log Λ :=
    le_trans log1e8_bounds.1 (Real.log_le_log (by norm_num) hΛ)
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hl : 18 ≤ ℓ := by linarith
  have hM := Mbar1_le (sH := sH) hl
  have hL : 0 < Real.exp ℓ := Real.exp_pos ℓ
  have hγ := gam_bound hsH hsH2 hg hΛ hs
  rw [← hℓ] at hγ
  unfold raise
  rw [← hℓ, div_le_iff₀ hL]
  have hMpos : 0 < Mbar1 sH Λ s := by
    unfold Mbar1 rbar0
    rw [← hℓ]
    have : 0 < 2 * Real.log Λ + s := by linarith
    positivity
  have hlogM : Real.log (Mbar1 sH Λ s) ≤ Real.log 2 + logc sH Λ s := by
    have := Real.log_le_log hMpos hM
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply max_le
  · positivity
  · unfold logc at hlogM
    rw [← hℓ] at hlogM
    rcases le_total (gam sH s * Λ) (4 * ℓ ^ 2 - Real.log 4) with h | h
    · rw [max_eq_left h] at hlogM
      have : 2 * Real.log (Mbar1 sH Λ s) - 8 * ℓ ^ 2 ≤ 0 := by linarith
      have : 0 ≤ 1 / 1000000 * Real.exp ℓ := by positivity
      linarith
    · rw [max_eq_right h] at hlogM
      have : 0 ≤ 8 * ℓ ^ 2 := by positivity
      linarith

/-- **`raise_max.py`, with the true break point.** With `s_H` the root of
`γ*(s_H) = 1/3 - 10⁻⁵` (`sH_spec`), the raise is at most `10⁻⁶` at every `Λ ≥ 10⁸` and
`s ≥ -log Λ`. -/
theorem raise_le_at_sH : ∃ sH ∈ Ioo (5.9745 : ℝ) 5.9746, gstar sH = gTarget ∧
    ∀ Λ s : ℝ, 100000000 ≤ Λ → -Real.log Λ ≤ s → raise sH Λ s ≤ 1 / 1000000 := by
  obtain ⟨sH, hsH, hval, -⟩ := sH_spec
  refine ⟨sH, hsH, hval, fun Λ s hΛ hs => raise_le hsH.1.le (by linarith [hsH.2]) ?_ hΛ hs⟩
  rw [hval]; unfold gTarget; norm_num

end BSCert.Capl
