module

public import RequestProject.Beurling.InitialRange

/-!
# The jitter width near `X₀` and the floor `X₀⁻ = X₀ - H(X₀)/2` of the jittered primes

The placement of the jittered primes (§3.4, §6.1: "every jittered prime is at least
`X₀⁻ = X₀ - H(X₀)/2`") uses only that `s - H(s)/2 ≥ X₀ - H(X₀)/2` for every slot start `s ≥ X₀`.
This was a hypothesis (the monotonicity of `v - H(v)/2`). Here it is **proved** for the paper's
`H = max(H_std, M̄₁²)`:

* `gstar_mul_le` : `γ*(s) Λ ≤ 7.5 (log Λ + 1)` for `-log Λ ≤ s ≤ 1 - log Λ`, `Λ ≥ 10⁸`;
* `capH_eq_std` : on `[X₀, 2X₀]` the capacity threshold is the standard one,
  `log c = 4ℓ² - log 4`, so `M̄₁² ≤ H_std` and `H = H_std = e^{8 (log log x)²}`;
* `capH_sub_le` : `H(s) - H(X₀) ≤ 2 (s - X₀)` on `[X₀, 2X₀]` (mean value theorem, as
  `H_std' = H_std · 16 ℓ/(x L) ≤ x^{1/8 - 1} ≤ 2`);
* `capH_floor` : `X₀ - H(X₀)/2 ≤ s - H(s)/2` for every `s ≥ X₀`. If `s ≥ X₀ + H(s)/2` this is
  immediate; otherwise `s < X₀ + 2H(s)`, so `s < 2X₀` (`InitialRange.lt_two_mul_of_initial`).
-/

@[expose] public section

open Real Set CaplLink BSCert.Capl

namespace JitterFloor

set_option maxHeartbeats 2000000 in
/-- **`γ*` near `s = -log Λ`**: `γ*(s) Λ ≤ 7.5 (log Λ + 1)` for `-log Λ ≤ s ≤ 1 - log Λ`. -/
theorem gstar_mul_le {Λ s : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hs1 : -Real.log Λ ≤ s)
    (hs2 : s ≤ 1 - Real.log Λ) : gstar s * Λ ≤ 7.5 * (Real.log Λ + 1) := by
  have hΛpos : 0 < Λ := by linarith
  have hl18 : 18 ≤ Real.log Λ := log_ge_18 (by norm_num at hΛ ⊢; linarith)
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  -- `Λ_s ∈ [Λ/e, Λ]`, `Λ_s ≥ 10⁸`
  set Ls := LamS s with hLsdef
  have he1 : Real.exp (-s) ≤ Λ := by
    rw [← Real.exp_log hΛpos]; exact Real.exp_le_exp.mpr (by linarith)
  have he2 : Λ ≤ Real.exp 1 * Real.exp (-s) := by
    rw [← Real.exp_add, ← Real.exp_log hΛpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hLs1 : (10 ^ 8 : ℝ) ≤ Ls := by
    rw [hLsdef]; unfold LamS; norm_num
  have hLs2 : Ls ≤ Λ := by
    rw [hLsdef]; unfold LamS; exact max_le (by norm_num at hΛ ⊢; linarith) he1
  have hLs3 : Λ ≤ Real.exp 1 * Ls := by
    refine he2.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le)
    rw [hLsdef]; unfold LamS; exact le_max_right _ _
  have hLs0 : 0 < Ls := by linarith
  have hlLs2 : Real.log Ls ≤ Real.log Λ := Real.log_le_log hLs0 hLs2
  have hlLs3 : Real.log Λ ≤ 1 + Real.log Ls := by
    have := Real.log_le_log hΛpos hLs3
    rwa [Real.log_mul (Real.exp_pos 1).ne' hLs0.ne', Real.log_exp] at this
  set ℓs := 2 * Real.log Ls + s with hℓs
  have hℓ1 : Real.log Λ - 2 ≤ ℓs := by rw [hℓs]; linarith
  have hℓ2 : ℓs ≤ Real.log Λ + 1 := by rw [hℓs]; linarith
  have hA := A_eq (Λ := Ls) (s := s) hLs0 (by linarith)
  rw [← hℓs] at hA
  set a := A Ls s with hadef
  -- `0 ≤ A ≤ log Λ`
  have h16 : Real.log 16 ≤ Real.log ℓs := Real.log_le_log (by norm_num) (by linarith)
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have ha1 : a ≤ Real.log Λ := by rw [hA]; linarith
  have hlℓ : Real.log ℓs ≤ Real.log 2 + (Real.log Λ + 1) / 2 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ℓs / 2 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    linarith
  have ha0 : 0 ≤ a := by rw [hA]; linarith
  -- the denominator: `Λ_s - A - 1 ≥ Λ/3`
  have hlogΛ : Real.log Λ ≤ 7 + Λ / 1000 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Λ / 1000 by positivity)
    rw [Real.log_div hΛpos.ne' (by norm_num)] at h
    have h7 : Real.log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 7]
    linarith
  set D := Ls - a - 1 with hD
  have hD3 : Λ / 3 ≤ D := by
    have : Λ ≤ 2.7182818286 * Ls := hLs3.trans (mul_le_mul_of_nonneg_right he'.le hLs0.le)
    rw [hD]; nlinarith
  have hD0 : 0 < D := by linarith
  -- `E = e^{s/2}`, `E² ≤ e/Λ`
  set E := Real.exp (s / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : E ^ 2 * Λ ≤ Real.exp 1 := by
    have h1 : E ^ 2 = Real.exp s := by rw [hE, ← Real.exp_nat_mul]; ring_nf
    have h2 : Real.exp s * Λ = Real.exp (s + Real.log Λ) := by
      rw [Real.exp_add, Real.exp_log hΛpos]
    rw [h1, h2]; exact Real.exp_le_exp.mpr (by linarith)
  set Q := E * Λ / Real.sqrt D with hQ
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hQ0 : 0 ≤ Q := by positivity
  have hQ2 : Q ^ 2 ≤ 3 * Real.exp 1 := by
    rw [hQ, div_pow, Real.sq_sqrt hD0.le, div_le_iff₀ hD0]
    have : E ^ 2 * Λ * Λ ≤ Real.exp 1 * Λ := mul_le_mul_of_nonneg_right hE2 hΛpos.le
    nlinarith
  have hQb : Q ≤ 2.86 := by
    by_contra h
    push_neg at h
    have h' : (2.86 : ℝ) ^ 2 < Q ^ 2 := pow_lt_pow_left₀ h (by norm_num) two_ne_zero
    linarith
  have hS : Real.sqrt (a * (a + 1)) ≤ a + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have eG : gstar s * Λ = 1.3 * (2 * Real.sqrt (a * (a + 1)) * Q) := by
    unfold gstar G; rw [← hLsdef, ← hadef, ← hE, ← hD, hQ]; ring
  rw [eG]
  have hS0 : 0 ≤ Real.sqrt (a * (a + 1)) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul hS hQb hQ0 (by linarith)]

/-- On `[X₀, 2X₀]` the capacity parameter `s = log log x - 2 log Λ` lies in `[-log Λ, 1 - log Λ]`. -/
lemma capS_mem {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx1 : X₀ ≤ x)
    (hx2 : x ≤ 2 * X₀) :
    -Real.log (Real.log X₀) ≤ capS X₀ x ∧ capS X₀ x ≤ 1 - Real.log (Real.log X₀) := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hΛ : 0 < Real.log X₀ := by linarith
  have hL1 : Real.log X₀ ≤ Real.log x := Real.log_le_log (by linarith) hx1
  have hL2 : Real.log x ≤ Real.log 2 + Real.log X₀ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hx2
  have hl2 := Real.log_two_lt_d9
  have he := Real.exp_one_gt_d9
  have h1 : Real.log (Real.log X₀) ≤ Real.log (Real.log x) := Real.log_le_log hΛ hL1
  have h2 : Real.log (Real.log x) ≤ 1 + Real.log (Real.log X₀) := by
    have : Real.log x ≤ Real.exp 1 * Real.log X₀ := by nlinarith
    have h := Real.log_le_log (by linarith) this
    rwa [Real.log_mul (Real.exp_pos 1).ne' hΛ.ne', Real.log_exp] at h
  unfold capS
  constructor <;> linarith

/-- **`H = H_std` on `[X₀, 2X₀]`.** -/
theorem capH_eq_std {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx1 : X₀ ≤ x)
    (hx2 : x ≤ 2 * X₀) : capH X₀ x = Real.exp (8 * Real.log (Real.log x) ^ 2) := by
  obtain ⟨hs1, hs2⟩ := capS_mem hX0 hX hx1 hx2
  obtain ⟨-, hℓΛ, -⟩ := logs_of_ge hX0 hX hx1
  set Λ := Real.log X₀ with hΛdef
  set ℓ := Real.log (Real.log x) with hℓdef
  set s := capS X₀ x with hsdef
  have hl18 : 18 ≤ Real.log Λ := log_ge_18 (by norm_num at hX ⊢; linarith)
  have hℓ : 2 * Real.log Λ + s = ℓ := ell_eq X₀ x
  have hsH := sHroot_mem
  have hgam : gam sHroot s = gstar s := by
    unfold gam; rw [if_pos (by linarith [hsH.1])]
  have hg := gstar_mul_le (by linarith) hs1 hs2
  have hl4 := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogc : logc sHroot Λ s = 4 * ℓ ^ 2 - Real.log 4 := by
    unfold logc
    rw [hℓ, hgam]
    apply max_eq_left
    nlinarith
  have hM := Mbar1_le (sH := sHroot) (Λ := Λ) (s := s) (by linarith)
  rw [hlogc, Real.exp_sub, Real.exp_log (by norm_num)] at hM
  have hMpos := capM1_pos hX0 hX hx1
  have hM' : capM1 X₀ x ≤ Real.exp (4 * ℓ ^ 2) / 2 := by
    unfold capM1; rw [← hΛdef, ← hsdef]; linarith
  have hsq : capM1 X₀ x ^ 2 ≤ Real.exp (8 * ℓ ^ 2) := by
    have e : Real.exp (8 * ℓ ^ 2) = Real.exp (4 * ℓ ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [e]
    have h0 : 0 < Real.exp (4 * ℓ ^ 2) := Real.exp_pos _
    nlinarith
  unfold capH
  exact max_eq_left hsq

/-- **`H(s) - H(X₀) ≤ 2 (s - X₀)` on `[X₀, 2X₀]`.** -/
theorem capH_sub_le {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx1 : X₀ ≤ x)
    (hx2 : x ≤ 2 * X₀) : capH X₀ x - capH X₀ X₀ ≤ 2 * (x - X₀) := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  set f : ℝ → ℝ := fun y => Real.exp (8 * Real.log (Real.log y) ^ 2) with hf
  set g : ℝ → ℝ := fun y => 2 * y - f y with hg
  have hderiv : ∀ y, 1 < y → HasDerivAt g
      (2 - f y * (8 * (2 * Real.log (Real.log y) * ((1 / y) / Real.log y)))) y := by
    intro y hy
    have hy0 : y ≠ 0 := by positivity
    have hLy : Real.log y ≠ 0 := (Real.log_pos hy).ne'
    have h1 : HasDerivAt Real.log (1 / y) y := by
      simpa [one_div] using Real.hasDerivAt_log hy0
    have h2 : HasDerivAt (fun y => Real.log (Real.log y)) ((1 / y) / Real.log y) y :=
      h1.log hLy
    have h3 := ((h2.pow 2).const_mul 8).exp
    have h4 := (hasDerivAt_id y).const_mul 2
    have h5 := h4.sub h3
    convert h5 using 1
    · simp only [Nat.cast_ofNat, mul_one, hf, Pi.pow_apply]
      ring
  have hcont : ContinuousOn g (Icc X₀ x) := fun y hy =>
    (hderiv y (by linarith [hy.1])).continuousAt.continuousWithinAt
  have hmono : MonotoneOn g (Icc X₀ x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · intro y hy
      rw [interior_Icc] at hy
      exact (hderiv y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy1 : X₀ ≤ y := hy.1.le
      have hy0 : 0 < y := by linarith
      rw [(hderiv y (by linarith)).deriv]
      obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hy1
      have hle := (hstd.trans (InitialRange.capH_le_rpow hX0 hX hy1))
      have hr : y ^ (1 / 8 : ℝ) ≤ y := by
        conv_rhs => rw [← Real.rpow_one y]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      obtain ⟨hL8, -, hl0⟩ := logs_of_ge hX0 hX hy1
      set L := Real.log y
      set l := Real.log L
      have hlL : l ≤ L / 8 := by
        have h := Real.log_le_sub_one_of_pos (show 0 < L / 16 by linarith)
        rw [Real.log_div (by linarith) (by norm_num)] at h
        have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
        linarith
      have hfy : f y ≤ y := hle.trans hr
      have hf0 : 0 ≤ f y := (Real.exp_pos _).le
      have e : f y * (8 * (2 * l * ((1 / y) / L))) = (f y / y) * (16 * l / L) := by
        field_simp
        ring
      rw [e]
      have h1 : f y / y ≤ 1 := by rw [div_le_one hy0]; exact hfy
      have h2 : 16 * l / L ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have h3 : 0 ≤ 16 * l / L := by positivity
      have h4 : 0 ≤ f y / y := by positivity
      nlinarith
  have hm := hmono (left_mem_Icc.mpr hx1) (right_mem_Icc.mpr hx1) hx1
  simp only [hg] at hm
  rw [capH_eq_std hX0 hX hx1 hx2, capH_eq_std hX0 hX le_rfl (by linarith)]
  simp only [hf] at hm
  linarith

/-- **The floor of the jittered primes**: `X₀ - H(X₀)/2 ≤ s - H(s)/2` for every `s ≥ X₀`. -/
theorem capH_floor {X₀ s : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hs : X₀ ≤ s) :
    X₀ - capH X₀ X₀ / 2 ≤ s - capH X₀ s / 2 := by
  have hH0 : 0 ≤ capH X₀ s := le_trans (Real.exp_pos _).le (le_max_left _ _)
  by_cases hfar : X₀ + capH X₀ s / 2 ≤ s
  · have : 0 ≤ capH X₀ X₀ := le_trans (Real.exp_pos _).le (le_max_left _ _)
    linarith
  · push_neg at hfar
    have h2 : s < 2 * X₀ :=
      InitialRange.lt_two_mul_of_initial hX0 hX hs (by linarith)
    have := capH_sub_le hX0 hX hs h2.le
    linarith

end JitterFloor

end
