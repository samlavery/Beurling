module

public import RequestProject.Beurling.Construction.JitterRegular

/-!
# The final numerical inequality of Lemma 4.8(ii)

With `X = X₀ + 1`, `η = min(θ, 1/2 - θ)/2`, `2^J X ≤ 2a`, `|w| ≤ c ≤ 4X₀` on `[log X₀, log a]` and
`M = (X^η + 2)(X₀/2)^{-3/4}`, the inequality of `Lemma48PiecesCount` holds for `Γ = Γ_k`
(`a ≤ x_k ≤ 1.001 a`, `log x_k ≥ X₀²`, `log X₀ ≥ 10⁸`). The margin comes from
`(1-θ)/2 - 1/4 - η/2 ≥ (1/2 - θ)/4 ≥ 2.5·10⁻⁵` and `log a ≥ X₀² - 1`.
-/

@[expose] public section

open Set Real Construction

namespace Zeros48

/-- `4000 L^8 ≤ e^{L/20000}` for `L ≥ 10^60`. -/
lemma key_exp {L : ℝ} (hL : 10 ^ 60 ≤ L) : 4000 * L ^ 8 ≤ Real.exp (L / 20000) := by
  have h := Real.pow_div_factorial_le_exp (L / 20000) (by positivity) 9
  have hf : ((Nat.factorial 9 : ℕ) : ℝ) = 362880 := by norm_num [Nat.factorial]
  rw [hf, div_pow] at h
  have hL0 : 0 ≤ L ^ 8 := by positivity
  have h1 : (4000 * 362880 * 20000 ^ 9 : ℝ) * L ^ 8 ≤ L * L ^ 8 :=
    mul_le_mul_of_nonneg_right (by linarith) hL0
  have h2 : L ^ 9 / 20000 ^ 9 / 362880 = L * L ^ 8 / (20000 ^ 9 * 362880) := by ring
  rw [h2, div_le_iff₀ (by positivity)] at h
  nlinarith

/-- `10^61 ≤ e^{2ℓ}` for `ℓ ≥ 10^8`. -/
lemma exp_two_mul_ge {ℓ : ℝ} (hℓ : 10 ^ 8 ≤ ℓ) : 10 ^ 61 ≤ Real.exp (2 * ℓ) := by
  have h := Real.pow_div_factorial_le_exp (2 * ℓ) (by positivity) 8
  have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h1 : (2 * 10 ^ 8 : ℝ) ^ 8 ≤ (2 * ℓ) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
  have h2 : (10 ^ 61 : ℝ) ≤ (2 * 10 ^ 8 : ℝ) ^ 8 / 40320 := by norm_num
  have h3 : (2 * 10 ^ 8 : ℝ) ^ 8 / 40320 ≤ (2 * ℓ) ^ 8 / 40320 := by gcongr
  linarith

lemma sq_le_imp {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ^ 2 ≤ B ^ 2) : A ≤ B :=
  (pow_le_pow_iff_left₀ hA hB (by norm_num)).mp h

set_option maxHeartbeats 1000000 in
theorem lemma48_numerics {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ a xk : ℝ}
    (hX0 : 0 < X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (ha : X₀ ≤ a) (haxk : a ≤ xk)
    (hxk : xk ≤ (1 + 1 / 1000) * a) (hxk0 : X₀ ^ 2 ≤ Real.log xk) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 4 * X₀) {J : ℕ} (hJ : 2 ^ J * (X₀ + 1) ≤ 2 * a) :
    1 ≤ DesignedZero.heightScale θ (kappa0Param X₀) xk ∧
    1 ≤ (Real.log a - Real.log X₀) * (DesignedZero.heightScale θ (kappa0Param X₀) xk + 1 / 2) ∧
    25 * Real.sqrt (DesignedZero.heightScale θ (kappa0Param X₀) xk + 1 / 2) *
        (X₀ + 1) ^ (lagExponent θ / 2 - 1 / 4) +
      40 * (2 ^ J * (X₀ + 1)) ^ (lagExponent θ / 2 + 1 / 4) +
      (Real.sqrt ((DesignedZero.heightScale θ (kappa0Param X₀) xk + 1 / 2) / 2) *
          (((X₀ + 1) ^ lagExponent θ + 2) * (X₀ / 2) ^ (-(3 / 4 : ℝ))) +
        2 * Real.sqrt (1 + Real.log ((Real.log a - Real.log X₀) *
          (DesignedZero.heightScale θ (kappa0Param X₀) xk + 1 / 2))) * c *
          Real.exp (Real.log a / 4)) ≤
      100 * X₀ ^ (-(3 / 16 : ℝ)) * Real.sqrt (DesignedZero.heightScale θ (kappa0Param X₀) xk) := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  set ℓ := Real.log X₀ with hℓ
  set L := Real.log a with hLdef
  set Λ := Real.log xk with hΛdef
  set G := DesignedZero.heightScale θ (kappa0Param X₀) xk with hGdef
  set η := lagExponent θ with hηdef
  set Y : ℝ := 2 ^ J * (X₀ + 1) with hYdef
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  clear_value ℓ L Λ G η Y
  have hXexp : X₀ = Real.exp ℓ := by rw [hℓ]; exact (Real.exp_log hX0).symm
  have hX1 : 1 + ℓ ≤ X₀ := by rw [hXexp]; linarith [Real.add_one_le_exp ℓ]
  have ha0 : 0 < a := by linarith
  have hxk0' : 0 < xk := by linarith
  have hsq : X₀ ^ 2 = Real.exp (2 * ℓ) := by
    rw [hXexp, sq, ← Real.exp_add]; ring_nf
  have hbig : (10 : ℝ) ^ 61 ≤ X₀ ^ 2 := hsq ▸ exp_two_mul_ge hX
  have hl1001 : Real.log (1 + 1 / 1000) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 1000 by norm_num); linarith
  have hΛL : Λ ≤ L + 1 := by
    have h1 := Real.log_le_log hxk0' hxk
    rw [Real.log_mul (by norm_num) ha0.ne', ← hΛdef, ← hLdef] at h1
    linarith
  have hLΛ : L ≤ Λ := by rw [hLdef, hΛdef]; exact Real.log_le_log ha0 haxk
  have hL60 : (10 : ℝ) ^ 60 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hXX : X₀ ≤ X₀ ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have h3X : 3 * X₀ ≤ X₀ ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hX0.le
  have hX2L : X₀ ≤ 2 * L := by linarith
  -- the exponent
  have hη0 : 0 ≤ η := by
    simp only [hηdef, lagExponent]
    exact div_nonneg (le_min (by linarith) (by linarith)) (by norm_num)
  have hη8 : η ≤ (1 / 2 - θ) / 2 := by
    simp only [hηdef, lagExponent]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hηle : η ≤ 1 / 8 := by linarith
  -- the height
  have hΛpos : 0 < Λ := by linarith
  have hGeq : G = xk ^ (1 - θ) / (2 * X₀ * Λ) := by
    rw [hGdef, hΛdef]; simp only [DesignedZero.heightScale, kappa0Param]
    field_simp
  have hxkθ : Real.exp ((1 - θ) * L) ≤ xk ^ (1 - θ) := by
    have := Real.rpow_le_rpow ha0.le haxk (by linarith : (0 : ℝ) ≤ 1 - θ)
    rw [Real.rpow_def_of_pos ha0, ← hLdef] at this
    rw [mul_comm]; exact this
  have hΛ3 : 2 * X₀ * Λ ≤ 64 * L ^ 3 := by
    have h1 : 2 * X₀ * Λ ≤ 2 * (2 * L) * (L + 1) :=
      mul_le_mul (by linarith) hΛL hΛpos.le (by linarith)
    nlinarith [mul_le_mul hL1 hL1 zero_le_one hL0]
  have hy0 : 0 ≤ xk ^ (1 - θ) := Real.rpow_nonneg hxk0'.le _
  have hGlow : Real.exp ((1 - θ) * L) ≤ 64 * L ^ 3 * G := by
    refine hxkθ.trans ?_
    rw [hGeq, mul_div_assoc', le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hΛ3 hy0
    linarith
  have hxk1 : 1 ≤ xk := by linarith
  have hGup : G ≤ xk := by
    rw [hGeq]
    have h1 : xk ^ (1 - θ) ≤ xk := by
      have := Real.rpow_le_rpow_of_exponent_le hxk1 (show 1 - θ ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
    have h2 : 1 ≤ 2 * X₀ * Λ := by nlinarith
    exact (div_le_self hy0 h2).trans h1
  have hkey := key_exp hL60
  -- the master bound `31.25 L⁴ e^y ≤ ρ² G` for `y + L/20000 ≤ (1-θ)L`
  set ρ := X₀ ^ (-(3 / 16 : ℝ)) with hρdef
  have hρ : ρ = Real.exp (ℓ * (-(3 / 16 : ℝ))) := by
    rw [hρdef, hℓ]; exact Real.rpow_def_of_pos hX0 _
  clear_value ρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact Real.exp_pos _
  have hρ2 : 1 ≤ ρ ^ 2 * X₀ := by
    rw [hρ, hXexp, sq, ← Real.exp_add, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hG0 : 0 ≤ G := by rw [hGeq]; positivity
  have master : ∀ y : ℝ, y + L / 20000 ≤ (1 - θ) * L →
      31.25 * L ^ 4 * Real.exp y ≤ ρ ^ 2 * G := by
    intro y hy
    have h1 : Real.exp y * (4000 * L ^ 8) ≤ Real.exp ((1 - θ) * L) := by
      calc Real.exp y * (4000 * L ^ 8) ≤ Real.exp y * Real.exp (L / 20000) :=
            mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
        _ = Real.exp (y + L / 20000) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hy
    have hL3 : 0 < L ^ 3 := by positivity
    have h2 : 62.5 * L ^ 5 * Real.exp y ≤ G := by
      have e : L ^ 3 * (62.5 * L ^ 5 * Real.exp y) = Real.exp y * (4000 * L ^ 8) / 64 := by ring
      have : L ^ 3 * (62.5 * L ^ 5 * Real.exp y) ≤ L ^ 3 * G := by
        rw [e]; linarith
      exact le_of_mul_le_mul_left this hL3
    have h3 : G ≤ ρ ^ 2 * G * (2 * L) := by
      have h5 : 1 ≤ ρ ^ 2 * (2 * L) :=
        hρ2.trans (mul_le_mul_of_nonneg_left hX2L (by positivity))
      calc G = 1 * G := by ring
        _ ≤ ρ ^ 2 * (2 * L) * G := mul_le_mul_of_nonneg_right h5 hG0
        _ = ρ ^ 2 * G * (2 * L) := by ring
    have h4 : (2 * L) * (31.25 * L ^ 4 * Real.exp y) ≤ (2 * L) * (ρ ^ 2 * G) := by
      have e1 : (2 * L) * (31.25 * L ^ 4 * Real.exp y) = 62.5 * L ^ 5 * Real.exp y := by ring
      have e2 : (2 * L) * (ρ ^ 2 * G) = ρ ^ 2 * G * (2 * L) := by ring
      linarith
    exact le_of_mul_le_mul_left h4 (by linarith)
  have hsG := Real.sqrt_nonneg G
  have hsGsq : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG0
  have hgapL : L / 2 + L / 20000 ≤ (1 - θ) * L := by
    have := mul_le_mul_of_nonneg_right (show 1 / 2 + 1 / 20000 ≤ 1 - θ by linarith) hL0
    linarith
  have hG1 : 1 ≤ G := by
    have h1 := master (L / 2) hgapL
    have h2 : 1 ≤ 31.25 * L ^ 4 * Real.exp (L / 2) := by
      have h4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
      have h5 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by linarith)
      have := one_le_mul_of_one_le_of_one_le h4 h5
      linarith
    -- ρ² ≤ 1
    have hρ1 : ρ ^ 2 ≤ 1 := by
      rw [hρ, sq, ← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
    have := mul_le_of_le_one_left hG0 hρ1
    linarith
  refine ⟨hG1, ?_, ?_⟩
  · have hℓX : ℓ < X₀ := by linarith
    have : 1 ≤ L - ℓ := by linarith
    exact one_le_mul_of_one_le_of_one_le this (by linarith)
  -- T1
  have hT1 : 25 * Real.sqrt (G + 1 / 2) * (X₀ + 1) ^ (η / 2 - 1 / 4) ≤ 31.25 * ρ * Real.sqrt G := by
    have hs : Real.sqrt (G + 1 / 2) ≤ 1.25 * Real.sqrt G := by
      refine sq_le_imp (Real.sqrt_nonneg _) (by positivity) ?_
      rw [Real.sq_sqrt (by linarith), mul_pow, hsGsq]; norm_num; linarith
    have hp : (X₀ + 1) ^ (η / 2 - 1 / 4) ≤ ρ := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < X₀ + 1 by linarith), hρ]
      apply Real.exp_le_exp.mpr
      have hl : ℓ ≤ Real.log (X₀ + 1) := by rw [hℓ]; exact Real.log_le_log hX0 (by linarith)
      have h1 := mul_le_mul_of_nonpos_right hl (show η / 2 - 1 / 4 ≤ 0 by linarith)
      have h2 := mul_le_mul_of_nonneg_left (show η / 2 - 1 / 4 ≤ -(3 / 16) by linarith) hℓ0
      linarith
    have hp0 : 0 ≤ (X₀ + 1) ^ (η / 2 - 1 / 4) := Real.rpow_nonneg (by linarith) _
    calc 25 * Real.sqrt (G + 1 / 2) * (X₀ + 1) ^ (η / 2 - 1 / 4)
        ≤ 25 * (1.25 * Real.sqrt G) * ρ := by gcongr
      _ = 31.25 * ρ * Real.sqrt G := by ring
  -- T2
  have hT2 : 40 * Y ^ (η / 2 + 1 / 4) ≤ 30 * ρ * Real.sqrt G := by
    set q := η / 2 + 1 / 4
    have hq0 : 0 ≤ q := by positivity
    have hqdef : q = η / 2 + 1 / 4 := rfl
    clear_value q
    have h1 : Y ^ q ≤ (2 * a) ^ q := Real.rpow_le_rpow hY0.le hJ hq0
    have h2 : (2 * a) ^ q ≤ 3 * Real.exp (q * L) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 * a by linarith),
        Real.log_mul (by norm_num) ha0.ne', ← hLdef]
      have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      have : (Real.log 2 + L) * q ≤ 1 + q * L := by
        have := mul_le_mul_of_nonneg_right hl2.le hq0
        have hq1 : q ≤ 1 := by rw [hqdef]; linarith
        linarith
      calc Real.exp ((Real.log 2 + L) * q) ≤ Real.exp (1 + q * L) := Real.exp_le_exp.mpr this
        _ = Real.exp 1 * Real.exp (q * L) := Real.exp_add _ _
        _ ≤ 3 * Real.exp (q * L) := by
          gcongr; have := Real.exp_one_lt_d9; linarith
    have h3 : 120 * Real.exp (q * L) ≤ 30 * ρ * Real.sqrt G := by
      refine sq_le_imp (by positivity) (by positivity) ?_
      have hm := master (2 * (q * L)) (by
        have e : 2 * (q * L) = (η + 1 / 2) * L := by rw [hqdef]; ring
        have := mul_le_mul_of_nonneg_right (show η + 1 / 2 + 1 / 20000 ≤ 1 - θ by linarith) hL0
        linarith)
      have he : Real.exp (q * L) ^ 2 = Real.exp (2 * (q * L)) := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [mul_pow, mul_pow, mul_pow, hsGsq, he]
      have h4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
      have := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (2 * (q * L))).le
      have := Real.exp_pos (2 * (q * L))
      linarith
    linarith
  -- T3
  have hT3 : Real.sqrt ((G + 1 / 2) / 2) * (((X₀ + 1) ^ η + 2) * (X₀ / 2) ^ (-(3 / 4 : ℝ))) ≤
      ρ * Real.sqrt G := by
    have hs : Real.sqrt ((G + 1 / 2) / 2) ≤ Real.sqrt G :=
      Real.sqrt_le_sqrt (show (G + 1 / 2) / 2 ≤ G by linarith)
    have he1 : (X₀ + 1) ^ η ≤ Real.exp ((ℓ + 1) / 8) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < X₀ + 1 by linarith)]
      apply Real.exp_le_exp.mpr
      have hl : Real.log (X₀ + 1) ≤ ℓ + 1 := by
        have := Real.log_le_log (by linarith) (show X₀ + 1 ≤ 2 * X₀ by linarith)
        rw [Real.log_mul (by norm_num) hX0.ne', ← hℓ] at this
        have := Real.log_two_lt_d9; linarith
      have := mul_le_mul hl hηle hη0 (by linarith)
      linarith
    have he2 : (X₀ / 2) ^ (-(3 / 4 : ℝ)) ≤ Real.exp (-(3 / 4) * (ℓ - 1)) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < X₀ / 2 by linarith),
        Real.log_div hX0.ne' (by norm_num), ← hℓ]
      apply Real.exp_le_exp.mpr
      have := Real.log_two_lt_d9; linarith
    have he3 : 2 ≤ Real.exp ((ℓ + 1) / 8) := by
      have := Real.add_one_le_exp ((ℓ + 1) / 8); linarith
    have hM : ((X₀ + 1) ^ η + 2) * (X₀ / 2) ^ (-(3 / 4 : ℝ)) ≤ ρ := by
      have hp0 : 0 ≤ (X₀ / 2) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
      calc ((X₀ + 1) ^ η + 2) * (X₀ / 2) ^ (-(3 / 4 : ℝ))
          ≤ (2 * Real.exp ((ℓ + 1) / 8)) * Real.exp (-(3 / 4) * (ℓ - 1)) := by
            gcongr; linarith
        _ = 2 * Real.exp ((ℓ + 1) / 8 + -(3 / 4) * (ℓ - 1)) := by rw [Real.exp_add]; ring
        _ ≤ Real.exp 1 * Real.exp ((ℓ + 1) / 8 + -(3 / 4) * (ℓ - 1)) := by
            gcongr; have := Real.add_one_le_exp 1; linarith
        _ = Real.exp (1 + ((ℓ + 1) / 8 + -(3 / 4) * (ℓ - 1))) := (Real.exp_add _ _).symm
        _ ≤ ρ := by rw [hρ]; exact Real.exp_le_exp.mpr (by linarith)
    have hM0 : 0 ≤ ((X₀ + 1) ^ η + 2) * (X₀ / 2) ^ (-(3 / 4 : ℝ)) := by positivity
    calc _ ≤ Real.sqrt G * ρ := mul_le_mul hs hM hM0 hsG
      _ = ρ * Real.sqrt G := by ring
  -- T4
  have hT4 : 2 * Real.sqrt (1 + Real.log ((L - ℓ) * (G + 1 / 2))) * c * Real.exp (L / 4) ≤
      30 * ρ * Real.sqrt G := by
    have hLℓ : 0 < L - ℓ := by linarith
    have hlogP : 1 + Real.log ((L - ℓ) * (G + 1 / 2)) ≤ 4 * L := by
      rw [Real.log_mul hLℓ.ne' (by linarith)]
      have h1 := Real.log_le_sub_one_of_pos hLℓ
      have h2 : Real.log (G + 1 / 2) ≤ Real.log (2 * xk) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hxk0'.ne'] at h2
      have := Real.log_two_lt_d9
      linarith
    have hs : Real.sqrt (1 + Real.log ((L - ℓ) * (G + 1 / 2))) ≤ Real.sqrt (4 * L) :=
      Real.sqrt_le_sqrt hlogP
    have h3 : 2 * Real.sqrt (4 * L) * c * Real.exp (L / 4) ≤ 30 * ρ * Real.sqrt G := by
      refine sq_le_imp (by positivity) (by positivity) ?_
      have hm := master (L / 2) hgapL
      have he : Real.exp (L / 4) ^ 2 = Real.exp (L / 2) := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith), hsGsq, he]
      have hc8 : c ^ 2 ≤ 64 * L ^ 2 := by
        have := pow_le_pow_left₀ hc0.le (show c ≤ 8 * L by linarith) 2
        have e : (8 * L) ^ 2 = 64 * L ^ 2 := by ring
        linarith
      have hE := Real.exp_pos (L / 2)
      have h34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
      have h5 : 2 ^ 2 * (4 * L) * c ^ 2 * Real.exp (L / 2) ≤ 1024 * L ^ 3 * Real.exp (L / 2) := by
        have : 2 ^ 2 * (4 * L) * c ^ 2 ≤ 1024 * L ^ 3 := by
          have := mul_le_mul_of_nonneg_left hc8 (show (0 : ℝ) ≤ 16 * L by linarith)
          have e : (2 : ℝ) ^ 2 * (4 * L) * c ^ 2 = 16 * L * c ^ 2 := by ring
          have e2 : 16 * L * (64 * L ^ 2) = 1024 * L ^ 3 := by ring
          linarith
        exact mul_le_mul_of_nonneg_right this hE.le
      have := mul_le_mul_of_nonneg_right h34 hE.le
      have : 0 ≤ L ^ 4 * Real.exp (L / 2) := by positivity
      linarith
    calc _ ≤ 2 * Real.sqrt (4 * L) * c * Real.exp (L / 4) := by gcongr
      _ ≤ _ := h3
  have hρG : 0 ≤ ρ * Real.sqrt G := by positivity
  linarith

end Zeros48

end
