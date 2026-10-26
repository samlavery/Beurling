module

public import RequestProject.BSCert.CaplRaise
meta import RequestProject.BSCert.CaplRaise

/-!
# Step 2 of the proof of Theorem 6.23 (high-degree rows)

`caplw_check_independent.py` evaluates, for `s ≤ s_H + 1`, the high-degree-row criterion
with `m ≤ L²/(ℓΛ)`, so that `a = log 2m = A(Λ, s)`:
* `j = ⌊(log c - 1)/(2A) - 1/2⌋`,
* `D* = ⌊(log c / 2)/(1 + A)⌋`, `k = D* + 1`,
* `gain = k(Λ - 1 - A) - log 3`,

and checks `(1 + j) · gain ≥ L + 10ℓ + 10`. We prove this for all `Λ ≥ 10⁸` and
`-log Λ ≤ s ≤ s_H + 1`, following the paper: `log c ≥ 1.3 G(Λ, s) Λ` (Step 1 and, on the
ramp, `γ ≥ γ*`), and then the product is at least `1.63 L`.
-/

@[expose] public section

namespace BSCert.Capl

open Real Set

/-- The left side `(1 + j) · gain` of the high-degree-row criterion, for `log c = X`. -/
noncomputable def step2LHS (X Λ s : ℝ) : ℝ :=
  (1 + (⌊(X - 1) / (2 * A Λ s) - 1 / 2⌋ : ℝ)) *
    (((⌊X / 2 / (1 + A Λ s)⌋ : ℝ) + 1) * (Λ - 1 - A Λ s) - Real.log 3)

set_option maxHeartbeats 1000000 in
/-- On the ramp `[s_H, s_H + 1]`, `γ* ≤ γ`. -/
lemma gstar_le_gam_ramp {sH s : ℝ} (hsH : sH ∈ Ioo (5.9745 : ℝ) 5.9746)
    (hval : gstar sH = gTarget) (h1 : sH ≤ s) (h2 : s ≤ sH + 1) : gstar s ≤ gam sH s := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; unfold gam; rw [if_pos le_rfl]
  have hgam : gam sH s = gTarget + (7.5 - gTarget) * (s - sH) := by
    unfold gam; rw [if_neg (not_le.mpr h), if_pos h2, hval]
  rw [hgam]
  obtain ⟨hs1, hs2⟩ := hsH
  have hsI : sH ∈ Icc (0 : ℝ) 10 := ⟨by linarith, by linarith⟩
  have hsI' : s ∈ Icc (0 : ℝ) 10 := ⟨by linarith, by linarith⟩
  set t := s - sH with ht
  have ht0 : 0 < t := by linarith
  have ht1 : t ≤ 1 := by linarith
  -- the two values of `A`
  obtain ⟨hL1, hL2⟩ := log1e8_bounds
  set a0 := A 100000000 sH
  set a1 := A 100000000 s
  have ha01 : a0 + t < a1 := A8_strictMono hsI.1 h
  have ha01' : a1 ≤ a0 + 2 * t := by
    simp only [a0, a1]
    rw [A8_eq hsI.1, A8_eq hsI'.1]
    have : Real.log (2 * Real.log 100000000 + sH) ≤ Real.log (2 * Real.log 100000000 + s) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have ha60 : 60 ≤ a0 := by
    simp only [a0]; rw [A8_eq hsI.1]
    have htan : Real.log (2 * Real.log 100000000 + sH)
        ≤ (2 * Real.log 100000000 + sH) / 40 + Real.log 40 - 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2 * Real.log 100000000 + sH) / 40) (by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      linarith
    have := log40_le
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have ha1b := A8_bounds hsI'.1 hsI'.2
  have ha1u : a1 ≤ 80 := by
    simp only [a1]; rw [A8_eq hsI'.1]
    have : 0 ≤ Real.log (2 * Real.log 100000000 + s) := Real.log_nonneg (by linarith)
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
    linarith
  -- numerator
  set N0 := Real.sqrt (a0 * (a0 + 1))
  set N1 := Real.sqrt (a1 * (a1 + 1))
  have hN : N1 ≤ N0 * (1 + t / 30) := by
    have hq : a1 * (a1 + 1) ≤ (N0 * (1 + 2 * t / a0)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have e1 : a0 * (1 + 2 * t / a0) = a0 + 2 * t := by field_simp
      have e2 : (a0 + 1) * (1 + 2 * t / a0) = a0 + 1 + 2 * t + 2 * t / a0 := by field_simp; ring
      have hpos : 0 ≤ 2 * t / a0 := by positivity
      calc a1 * (a1 + 1) ≤ (a0 + 2 * t) * (a0 + 1 + 2 * t + 2 * t / a0) := by
            apply mul_le_mul ha01' (by linarith) (by linarith) (by linarith)
        _ = a0 * (a0 + 1) * (1 + 2 * t / a0) ^ 2 := by rw [← e1, ← e2]; ring
    have h1 : N1 ≤ N0 * (1 + 2 * t / a0) := by
      calc N1 ≤ Real.sqrt ((N0 * (1 + 2 * t / a0)) ^ 2) := Real.sqrt_le_sqrt hq
        _ = N0 * (1 + 2 * t / a0) := Real.sqrt_sq (by positivity)
    have h2 : 2 * t / a0 ≤ t / 30 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have : 0 ≤ N0 := Real.sqrt_nonneg _
    nlinarith
  -- exponential
  have hE : Real.exp (s / 2) ≤ Real.exp (sH / 2) * (1 + t) := by
    have e : Real.exp (s / 2) = Real.exp (sH / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; rw [ht]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hb := Real.exp_bound_div_one_sub_of_interval (x := t / 2) (by linarith) (by linarith)
    refine le_trans hb ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- denominator
  set D0 := Real.sqrt (100000000 - a0 - 1)
  set D1 := Real.sqrt (100000000 - a1 - 1)
  have hD1 : 0 < D1 := Real.sqrt_pos.mpr (by linarith)
  have hD : D0 ≤ D1 * (1 + t / 10000000) := by
    have hq : 100000000 - a0 - 1 ≤ (D1 * (1 + t / 10000000)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      have hu : 0 ≤ t / 10000000 := by positivity
      have hP : 0 ≤ 100000000 - a1 - 1 := by linarith
      have hu2 : 1 + t / 10000000 ≤ (1 + t / 10000000) ^ 2 := by nlinarith
      have h1 := mul_le_mul_of_nonneg_left hu2 hP
      have h3 : 9 * t ≤ (100000000 - a1 - 1) * (t / 10000000) := by
        have : 0 ≤ (100000000 - a1 - 1 - 90000000) * (t / 10000000) :=
          mul_nonneg (by linarith) hu
        nlinarith
      nlinarith
    calc D0 ≤ Real.sqrt ((D1 * (1 + t / 10000000)) ^ 2) := Real.sqrt_le_sqrt hq
      _ = D1 * (1 + t / 10000000) := Real.sqrt_sq (by positivity)
  -- combine
  have hG0 : gstar sH = 1.3 * (2 * N0 * Real.exp (sH / 2) / D0) := by
    rw [gstar_eq_on hsI]; rfl
  have hG1 : gstar s = 1.3 * (2 * N1 * Real.exp (s / 2) / D1) := by
    rw [gstar_eq_on hsI']; rfl
  have hD0 : 0 < D0 := Real.sqrt_pos.mpr (by linarith)
  have hratio : gstar s ≤ gstar sH * (1 + 3 * t) := by
    rw [hG0, hG1]
    have hN0 : 0 ≤ N0 := Real.sqrt_nonneg _
    have hE0 := Real.exp_pos (sH / 2)
    have key : N1 * Real.exp (s / 2) * D0
        ≤ N0 * Real.exp (sH / 2) * D1 * ((1 + t / 30) * (1 + t) * (1 + t / 10000000)) := by
      have h1 : N1 * Real.exp (s / 2) ≤ N0 * (1 + t / 30) * (Real.exp (sH / 2) * (1 + t)) :=
        mul_le_mul hN hE (Real.exp_pos _).le (by positivity)
      calc N1 * Real.exp (s / 2) * D0
          ≤ N0 * (1 + t / 30) * (Real.exp (sH / 2) * (1 + t)) * (D1 * (1 + t / 10000000)) :=
            mul_le_mul h1 hD hD0.le (by positivity)
        _ = _ := by ring
    have hpoly : (1 + t / 30) * (1 + t) * (1 + t / 10000000) ≤ 1 + 3 * t := by
      have : t ^ 2 ≤ t := by nlinarith
      have : t ^ 3 ≤ t := by nlinarith
      nlinarith
    have h3 : N0 * Real.exp (sH / 2) * D1 * ((1 + t / 30) * (1 + t) * (1 + t / 10000000))
        ≤ N0 * Real.exp (sH / 2) * D1 * (1 + 3 * t) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    have : 2 * N1 * Real.exp (s / 2) / D1 ≤ 2 * N0 * Real.exp (sH / 2) * (1 + 3 * t) / D0 := by
      rw [div_le_div_iff₀ hD1 hD0]
      have e1 : 2 * N1 * Real.exp (s / 2) * D0 = 2 * (N1 * Real.exp (s / 2) * D0) := by ring
      have e2 : 2 * N0 * Real.exp (sH / 2) * (1 + 3 * t) * D1
          = 2 * (N0 * Real.exp (sH / 2) * D1 * (1 + 3 * t)) := by ring
      rw [e1, e2]
      linarith
    have e3 : 2 * N0 * Real.exp (sH / 2) * (1 + 3 * t) / D0
        = 2 * N0 * Real.exp (sH / 2) / D0 * (1 + 3 * t) := by ring
    rw [e3] at this
    linarith
  have hg0 : gstar sH = gTarget := hval
  rw [hg0] at hratio
  unfold gTarget at hratio ⊢
  nlinarith

/-- `log c ≥ 1.3 G(Λ, s) Λ` for `s ≤ s_H + 1`. -/
lemma logc_ge_G {sH Λ s : ℝ} (hsH : sH ∈ Ioo (5.9745 : ℝ) 5.9746) (hval : gstar sH = gTarget)
    (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs2 : s ≤ sH + 1) :
    1.3 * G Λ s * Λ ≤ logc sH Λ s := by
  have hΛ0 : 0 < Λ := by linarith
  -- `γ*(s) ≥ 1.3 G(Λ, s)` by Step 1
  have hLs : 100000000 ≤ LamS s := le_max_left _ _
  have hLs' : -Real.log (LamS s) ≤ s := by
    have : Real.exp (-s) ≤ LamS s := le_max_right _ _
    have := Real.log_le_log (Real.exp_pos _) this
    rw [Real.log_exp] at this; linarith
  have hLsΛ : LamS s ≤ Λ := by
    unfold LamS
    refine max_le hΛ ?_
    rw [← Real.exp_log hΛ0]; exact Real.exp_le_exp.mpr (by linarith)
  have hG := G_antitone hLs hLs' (by linarith [hsH.2]) hLsΛ
  have hgs : 1.3 * G Λ s ≤ gstar s := by unfold gstar; linarith
  have hgam : gstar s ≤ gam sH s := by
    rcases le_or_gt s sH with h | h
    · unfold gam; rw [if_pos h]
    · exact gstar_le_gam_ramp hsH hval h.le hs2
  unfold logc
  refine le_trans ?_ (le_max_right _ _)
  exact mul_le_mul_of_nonneg_right (hgs.trans hgam) hΛ0.le

set_option maxHeartbeats 1000000 in
/-- The core estimate of Step 2. -/
lemma step2_core {X Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs7 : s ≤ 7)
    (hXG : 1.3 * G Λ s * Λ ≤ X) (hXstd : 4 * (2 * Real.log Λ + s) ^ 2 - Real.log 4 ≤ X) :
    Real.exp (2 * Real.log Λ + s) + 10 * (2 * Real.log Λ + s) + 10 ≤ step2LHS X Λ s := by
  obtain ⟨hΛ0, hlogΛ, hl1, hA12, hAΛ, -⟩ := step1_dom hΛ hs (by linarith) le_rfl
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hl : 18.42 ≤ ℓ := by linarith
  have hAeq : A Λ s = Af s Λ := A_eq hΛ0 (by linarith)
  set a := A Λ s with ha
  rw [← hAeq] at hA12 hAΛ
  have ha2 : a ≤ 2 * ℓ := by
    rw [hAeq]; unfold Af
    have h2 : Real.log 2 ≤ Real.log Λ := Real.log_le_log (by norm_num) (by linarith)
    have h3 : 0 ≤ Real.log ℓ := Real.log_nonneg hl1
    rw [← hℓ]; linarith
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hX39 : 3.9 * ℓ ^ 2 ≤ X := by nlinarith
  have hX1a : 1 + a ≤ 0.03 * X := by nlinarith
  have hX0 : 0 < X := by nlinarith
  have ha0 : 0 < a := by linarith
  -- the factor `1 + j`
  set p : ℝ := 1 + (⌊(X - 1) / (2 * a) - 1 / 2⌋ : ℝ) with hp_def
  have hp : 0.97 * X / (2 * a) ≤ p := by
    have h := Int.lt_floor_add_one ((X - 1) / (2 * a) - 1 / 2)
    have e : (X - 1) / (2 * a) - 1 / 2 = (X - 1 - a) / (2 * a) := by field_simp
    rw [e] at h
    have : 0.97 * X / (2 * a) ≤ (X - 1 - a) / (2 * a) := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    rw [hp_def, e]; linarith
  -- the gain
  set kk : ℝ := (⌊X / 2 / (1 + a)⌋ : ℝ) + 1 with hkk_def
  have hkk : X / 2 / (1 + a) ≤ kk := (Int.lt_floor_add_one _).le
  have hΛa : Λ / 2 ≤ Λ - 1 - a := by
    have hlogΛ' : Real.log Λ ≤ Λ / 1000 + 999 := by
      have := Real.log_le_sub_one_of_pos (x := Λ / 1000) (by positivity)
      rw [Real.log_div hΛ0.ne' (by norm_num)] at this
      have h1000 := Real.log_le_sub_one_of_pos (x := 1000) (by norm_num)
      linarith
    linarith
  have hlog3 : Real.log 3 ≤ 1.2 := by
    have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hy16 : 16 ≤ X / 2 / (1 + a) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  set gain := kk * (Λ - 1 - a) - Real.log 3 with hgain
  have hg : 0.999 * (X / 2 / (1 + a) * (Λ - 1 - a)) ≤ gain := by
    have h1 : X / 2 / (1 + a) * (Λ - 1 - a) ≤ kk * (Λ - 1 - a) :=
      mul_le_mul_of_nonneg_right hkk (by linarith)
    have h2 : 16 * (Λ / 2) ≤ X / 2 / (1 + a) * (Λ - 1 - a) :=
      mul_le_mul hy16 hΛa (by positivity) (by linarith)
    rw [hgain]; linarith
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have hprod : 0.97 * X / (2 * a) * (0.999 * (X / 2 / (1 + a) * (Λ - 1 - a))) ≤ p * gain :=
    mul_le_mul hp hg (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))) hp0
  -- `G²`
  have hden0 : 0 < Λ - a - 1 := by linarith
  have hG2 : G Λ s ^ 2 * (Λ - a - 1) = 4 * a * (a + 1) * Real.exp s := by
    unfold G
    rw [← ha, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hden0.le, ← Real.exp_nat_mul]
    field_simp
    ring_nf
  have hG0 : 0 ≤ G Λ s := by
    unfold G; rw [← ha]; positivity
  have hX2 : (1.3 * G Λ s * Λ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hXG 2
  -- assemble
  have hmain : 1.6376 * (Λ ^ 2 * Real.exp s) ≤ p * gain := by
    refine le_trans ?_ hprod
    have e : 0.97 * X / (2 * a) * (0.999 * (X / 2 / (1 + a) * (Λ - 1 - a)))
        = 0.97 * 0.999 / 4 * (X ^ 2 * (Λ - a - 1) / (a * (1 + a))) := by
      field_simp; ring
    rw [e]
    have h1 : (1.3 * G Λ s * Λ) ^ 2 * (Λ - a - 1) / (a * (1 + a))
        = 1.69 * 4 * (Λ ^ 2 * Real.exp s) := by
      have : (1.3 * G Λ s * Λ) ^ 2 * (Λ - a - 1) = 1.69 * Λ ^ 2 * (G Λ s ^ 2 * (Λ - a - 1)) := by
        ring
      rw [this, hG2]; field_simp; ring
    have h2 : (1.3 * G Λ s * Λ) ^ 2 * (Λ - a - 1) / (a * (1 + a))
        ≤ X ^ 2 * (Λ - a - 1) / (a * (1 + a)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hX2 hden0.le
    rw [h1] at h2
    have : 0 ≤ Λ ^ 2 * Real.exp s := by positivity
    linarith
  -- `L + 10ℓ + 10 ≤ 1.6376 L`
  have hL : Real.exp ℓ = Λ ^ 2 * Real.exp s := exp_two_log_add hΛ0
  have hcube : ℓ ^ 3 / 6 ≤ Real.exp ℓ := by
    have h := Real.sum_le_exp_of_nonneg (x := ℓ) (by linarith) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : 0 ≤ ℓ ^ 2 / 2 := by positivity
    linarith
  have h339 : 339 * ℓ ≤ ℓ ^ 3 := by
    have h1 : 339 ≤ ℓ ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ ℓ)
    have e : ℓ * ℓ ^ 2 = ℓ ^ 3 := by ring
    linarith
  have hsmall : 10 * ℓ + 10 ≤ 0.6376 * Real.exp ℓ := by linarith
  unfold step2LHS
  rw [← ha]
  show Real.exp ℓ + 10 * ℓ + 10 ≤ p * gain
  rw [hL] at hsmall ⊢
  linarith

/-- **Step 2 of the proof of Theorem 6.23** (checked at random points by
`caplw_check_independent.py`): with `s_H` the break point of `sH_spec`, for every `Λ ≥ 10⁸`
and `-log Λ ≤ s ≤ s_H + 1`, the high-degree-row criterion `(1 + j) · gain ≥ L + 10ℓ + 10` holds
with `log c = max(4ℓ² - log 4, γ(s)Λ)`. -/
theorem step2 {sH Λ s : ℝ} (hsH : sH ∈ Ioo (5.9745 : ℝ) 5.9746) (hval : gstar sH = gTarget)
    (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs2 : s ≤ sH + 1) :
    Real.exp (2 * Real.log Λ + s) + 10 * (2 * Real.log Λ + s) + 10
      ≤ step2LHS (logc sH Λ s) Λ s :=
  step2_core hΛ hs (by linarith [hsH.2]) (logc_ge_G hsH hval hΛ hs hs2) (le_max_left _ _)

end BSCert.Capl
