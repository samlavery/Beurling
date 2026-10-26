module

public import RequestProject.Beurling.InitialRange

/-!
# The absorbed set is empty at low heights
-/

@[expose] public section

open Real BSCert.Capl CaplLink QueueMono InitialRange

namespace AbsorbEmpty

/-- `g := γ*(s_H) = 1/3 - 10⁻⁵`. -/
lemma gstar_le_target {s : ℝ} (hs : s ≤ 0) : gam sHroot s ≤ gTarget := by
  have hsH := sHroot_mem
  unfold gam
  rw [if_pos (by linarith [hsH.1])]
  rw [← gstar_sHroot]
  exact gstar_mono (by linarith [hsH.1]) (by linarith [hsH.2])

/-- Logarithmic estimates at `Λ ≥ 10⁸`: `16 (log Λ)² ≤ Λ/4`, `32 (log Λ)² ≤ Λ/400` and
`30 log Λ + 20 ≤ 2.5·10⁻⁵ Λ`. -/
lemma log_estimates {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    32 * Real.log Λ ^ 2 ≤ Λ / 400 ∧ 30 * Real.log Λ + 20 ≤ 25 / 1000000 * Λ := by
  have hΛ0 : 0 < Λ := by linarith
  set q := Λ ^ (1 / 8 : ℝ) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hΛ0.le _
  have hq8 : q ^ 8 = Λ := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hq10 : 10 ≤ q := by
    by_contra h; push_neg at h
    have : q ^ 8 < 10 ^ 8 := pow_lt_pow_left₀ h hq0 (by norm_num)
    linarith
  have hlog : Real.log Λ ≤ 8 * q := by
    have := Real.log_le_rpow_div hΛ0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    rw [← hq] at this; linarith
  have hlog0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hq6 : 10 ^ 6 * q ^ 2 ≤ q ^ 8 := by
    have : (10 : ℝ) ^ 6 ≤ q ^ 6 := pow_le_pow_left₀ (by norm_num) hq10 6
    nlinarith [pow_nonneg hq0 2]
  have hq7 : 10 ^ 7 * q ≤ q ^ 8 := by
    have : (10 : ℝ) ^ 7 ≤ q ^ 7 := pow_le_pow_left₀ (by norm_num) hq10 7
    nlinarith
  constructor
  · have : Real.log Λ ^ 2 ≤ 64 * q ^ 2 := by nlinarith
    rw [hq8] at hq6; linarith
  · rw [hq8] at hq7; linarith

lemma exp_ten_ge : (17073 : ℝ) ≤ Real.exp 10 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (17073 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h.le 10

lemma exp_fourteen_ge : (1092672 : ℝ) ≤ Real.exp 14 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (1092672 : ℝ) ≤ 2.7182818283 ^ 14 := by norm_num
    _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) h.le 14

/-- **The arithmetic core**: with `Λ ≥ 10⁸`, `1 ≤ L ≤ Λ²`, `1 ≤ c ≤ e^{gΛ}` (`g = 1/3 - 10⁻⁵`),
`4 ≤ r ≤ 2Λ²`, `0 ≤ H_std ≤ e^{32 (log Λ)²}` and `M = r + φ(r) + 1`, `φ(r) = c + r√c + r(r+1)/2`:
`max(H_std, M²) · max(L⁵, 48 M L³/c'²) · L⁶ < e^Λ/2`. -/
lemma y_core {Λ L c r Hs : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL1 : 1 ≤ L) (hL : L ≤ Λ ^ 2) (hc1 : 1 ≤ c)
    (hc : c ≤ Real.exp (gTarget * Λ)) (hr4 : 4 ≤ r) (hr : r ≤ 2 * Λ ^ 2) (hHs0 : 0 ≤ Hs)
    (hHs : Hs ≤ Real.exp (32 * Real.log Λ ^ 2)) :
    max Hs ((r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1) ^ 2) *
      max (L ^ 5) (48 * (r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1) * L ^ 3 / 0.15 ^ 2) *
      L ^ 6 < Real.exp Λ / 2 := by
  set M := r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1 with hM
  have hΛ0 : 0 < Λ := by linarith
  have hsq : Real.sqrt c ≤ c := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsq0 := Real.sqrt_nonneg c
  have hM0 : 0 ≤ M := by positivity
  have hMle : M ≤ 8 * Λ ^ 4 * c := by
    have h1 : M ≤ 2 * r ^ 2 * c := by
      have : r * Real.sqrt c ≤ r * c := mul_le_mul_of_nonneg_left hsq (by linarith)
      have hk : r ^ 2 / 2 + 5 / 2 * r + 2 ≤ 2 * r ^ 2 := by nlinarith
      have hc' : 0 ≤ c - 1 := by linarith
      have h3 : M ≤ c * (r ^ 2 / 2 + 5 / 2 * r + 2) := by
        rw [hM]
        nlinarith [mul_nonneg (show 0 ≤ r by linarith) hc', mul_nonneg (sq_nonneg r) hc']
      calc M ≤ c * (r ^ 2 / 2 + 5 / 2 * r + 2) := h3
        _ ≤ c * (2 * r ^ 2) := mul_le_mul_of_nonneg_left hk (by linarith)
        _ = 2 * r ^ 2 * c := by ring
    have h2 : r ^ 2 ≤ 4 * Λ ^ 4 := by nlinarith
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hL5 : L ^ 5 ≤ Λ ^ 10 := by
    calc L ^ 5 ≤ (Λ ^ 2) ^ 5 := pow_le_pow_left₀ hL0 hL 5
      _ = Λ ^ 10 := by ring
  have hL3 : L ^ 3 ≤ Λ ^ 6 := by
    calc L ^ 3 ≤ (Λ ^ 2) ^ 3 := pow_le_pow_left₀ hL0 hL 3
      _ = Λ ^ 6 := by ring
  have hL6 : L ^ 6 ≤ Λ ^ 12 := by
    calc L ^ 6 ≤ (Λ ^ 2) ^ 6 := pow_le_pow_left₀ hL0 hL 6
      _ = Λ ^ 12 := by ring
  have hP10 : 0 ≤ Λ ^ 10 := by positivity
  have hP4 : 0 ≤ Λ ^ 4 := by positivity
  -- the three factors
  have hF1 : max Hs (M ^ 2) ≤ Real.exp (32 * Real.log Λ ^ 2) + 64 * Λ ^ 8 * c ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg (Λ ^ 4 * c)]
    · have : M ^ 2 ≤ (8 * Λ ^ 4 * c) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
      nlinarith [Real.exp_pos (32 * Real.log Λ ^ 2)]
  have hF2 : max (L ^ 5) (48 * M * L ^ 3 / 0.15 ^ 2) ≤ 17073 * Λ ^ 10 * c := by
    apply max_le
    · nlinarith
    · have : 48 * M * L ^ 3 / 0.15 ^ 2 ≤ 48 * (8 * Λ ^ 4 * c) * Λ ^ 6 / 0.15 ^ 2 := by
        gcongr
      have e : 48 * (8 * Λ ^ 4 * c) * Λ ^ 6 / 0.15 ^ 2 = 384 / 0.0225 * (Λ ^ 10 * c) := by ring
      rw [e] at this
      nlinarith
  have hF1' : 0 ≤ max Hs (M ^ 2) := le_max_of_le_left hHs0
  have hF2' : 0 ≤ max (L ^ 5) (48 * M * L ^ 3 / 0.15 ^ 2) :=
    le_max_of_le_left (by positivity)
  have hprod : max Hs (M ^ 2) * max (L ^ 5) (48 * M * L ^ 3 / 0.15 ^ 2) * L ^ 6 ≤
      (Real.exp (32 * Real.log Λ ^ 2) + 64 * Λ ^ 8 * c ^ 2) * (17073 * Λ ^ 10 * c) * Λ ^ 12 := by
    apply mul_le_mul (mul_le_mul hF1 hF2 hF2' (by positivity)) hL6 (by positivity)
      (by positivity)
  -- exponential form
  set lam := Real.log Λ with hlam
  have hexpl : Real.exp lam = Λ := Real.exp_log hΛ0
  have hpow : ∀ k : ℕ, Λ ^ k = Real.exp (k * lam) := by
    intro k; rw [Real.exp_nat_mul, hexpl]
  obtain ⟨hl1, hl2⟩ := log_estimates hΛ
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
  have hc3 : c ^ 3 ≤ Real.exp (3 * (gTarget * Λ)) := by
    rw [show 3 * (gTarget * Λ) = (3 : ℕ) * (gTarget * Λ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) hc 3
  have hlog4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hquarter : Real.exp (Λ - 1.39) < Real.exp Λ / 4 := by
    rw [Real.exp_sub, div_lt_div_iff_of_pos_left (Real.exp_pos _) (Real.exp_pos _) (by norm_num)]
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp 1.39 := Real.exp_lt_exp.mpr hlog4
  -- term 1
  have hT1 : Real.exp (32 * lam ^ 2) * (17073 * Λ ^ 10 * c) * Λ ^ 12 ≤
      Real.exp (Λ - 1.39) := by
    have e : Real.exp (32 * lam ^ 2) * (17073 * Λ ^ 10 * c) * Λ ^ 12 =
        17073 * Λ ^ 22 * c * Real.exp (32 * lam ^ 2) := by ring
    rw [e, hpow 22]
    calc 17073 * Real.exp ((22 : ℕ) * lam) * c * Real.exp (32 * lam ^ 2)
        ≤ Real.exp 10 * Real.exp ((22 : ℕ) * lam) * Real.exp (gTarget * Λ) *
            Real.exp (32 * lam ^ 2) := by
          gcongr
          · exact exp_ten_ge
      _ = Real.exp (10 + 22 * lam + gTarget * Λ + 32 * lam ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (Λ - 1.39) := by
          apply Real.exp_le_exp.mpr; rw [hg]; linarith
  -- term 2
  have hT2 : 64 * Λ ^ 8 * c ^ 2 * (17073 * Λ ^ 10 * c) * Λ ^ 12 < Real.exp (Λ - 1.39) := by
    have e : 64 * Λ ^ 8 * c ^ 2 * (17073 * Λ ^ 10 * c) * Λ ^ 12 =
        1092672 * Λ ^ 30 * c ^ 3 := by ring
    rw [e, hpow 30]
    calc 1092672 * Real.exp ((30 : ℕ) * lam) * c ^ 3
        ≤ Real.exp 14 * Real.exp ((30 : ℕ) * lam) * Real.exp (3 * (gTarget * Λ)) := by
          gcongr
          · exact exp_fourteen_ge
      _ = Real.exp (14 + 30 * lam + 3 * (gTarget * Λ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
      _ < Real.exp (Λ - 1.39) := by
          apply Real.exp_lt_exp.mpr; rw [hg]; linarith
  have e2 : (Real.exp (32 * lam ^ 2) + 64 * Λ ^ 8 * c ^ 2) * (17073 * Λ ^ 10 * c) * Λ ^ 12
      = Real.exp (32 * lam ^ 2) * (17073 * Λ ^ 10 * c) * Λ ^ 12 +
        64 * Λ ^ 8 * c ^ 2 * (17073 * Λ ^ 10 * c) * Λ ^ 12 := by ring
  rw [e2] at hprod
  calc _ ≤ _ := hprod
    _ < Real.exp (Λ - 1.39) + Real.exp (Λ - 1.39) := add_lt_add_of_le_of_lt hT1 hT2
    _ < Real.exp Λ / 4 + Real.exp Λ / 4 := add_lt_add hquarter hquarter
    _ = Real.exp Λ / 2 := by ring

/-- The block-length bound `L₀(x) = max(L⁵, 48 M₁ L³/c'²)` (Section 2.2, `c' = 0.15`), with the
smooth majorant `M̄₁ ≥ M₁`. -/
noncomputable def absorbL0 (X₀ x : ℝ) : ℝ :=
  max (Real.log x ^ 5) (48 * capM1 X₀ x * Real.log x ^ 3 / 0.15 ^ 2)

/-- The absorption threshold `y(x) = H(x) L₀(x) (log x)⁶` at a height `x` (Section 3.2, (5)). -/
noncomputable def absorbYAt (X₀ x : ℝ) : ℝ := capH X₀ x * absorbL0 X₀ x * Real.log x ^ 6

/-- The threshold `y(n) := y(x)` frozen at the dyadic scale `x` of `n` (scales `X₀ 2^k`; heights
below `X₀` use the scale `X₀`). -/
noncomputable def absorbY (X₀ : ℝ) (n : ℕ) : ℝ := absorbYAt X₀ (dyadicScale X₀ (max X₀ n))

/-- **`y < X₀⁻` at low heights** (the step of §6.8 using Theorem 6.23(b)): for `log X₀ ≥ 10⁸`
and `X₀ ≤ x` with `log x ≤ (log X₀)²` (so `s = log log x - 2 log Λ ≤ 0 < s_H`),
`y(x) < X₀ - H(X₀)/2`. -/
theorem absorbYAt_lt {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hlow : Real.log x ≤ Real.log X₀ ^ 2) : absorbYAt X₀ x < X₀ - capH X₀ X₀ / 2 := by
  have hX1 := one_lt_of_logX hX0 hX
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log x with hLdef
  have hΛ0 : 0 < Λ := by linarith
  have hLΛ : Λ ≤ L := Real.log_le_log (by linarith) hx
  have hL0 : 0 < L := by linarith
  set l := Real.log L with hldef
  have hl18 : 18 ≤ Real.log Λ := log_ge_18 (by linarith)
  have hl1 : Real.log Λ ≤ l := Real.log_le_log hΛ0 hLΛ
  have hl2 : l ≤ 2 * Real.log Λ := by
    have := Real.log_le_log hL0 hlow
    rwa [Real.log_pow] at this
  have hell : 2 * Real.log Λ + capS X₀ x = l := ell_eq X₀ x
  have hs0 : capS X₀ x ≤ 0 := by linarith
  obtain ⟨hest1, -⟩ := log_estimates hX
  -- the pieces of `M̄₁`
  set c := Real.exp (logc sHroot Λ (capS X₀ x)) with hc
  set r := rbar0 Λ (capS X₀ x) with hr
  have hlog4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hc1 : 1 ≤ c := by
    rw [hc]; apply Real.one_le_exp
    unfold logc; rw [hell]
    apply le_max_of_le_left; nlinarith
  have hcle : c ≤ Real.exp (gTarget * Λ) := by
    rw [hc]; apply Real.exp_le_exp.mpr
    unfold logc; rw [hell]
    have hg : gTarget = 1 / 3 - 1 / 100000 := rfl
    apply max_le
    · have : l ^ 2 ≤ 4 * Real.log Λ ^ 2 := by nlinarith
      rw [hg]; nlinarith
    · exact mul_le_mul_of_nonneg_right (gstar_le_target hs0) hΛ0.le
  have hr4 : 4 ≤ r := by
    rw [hr]; unfold rbar0; rw [hell]
    have : 0 ≤ Real.exp l / (3 * l) := div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  have hrle : r ≤ 2 * Λ ^ 2 := by
    rw [hr]; unfold rbar0; rw [hell, hldef, Real.exp_log hL0, ← hldef]
    have h3 : L / (3 * l) ≤ L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hHs : Real.exp (8 * l ^ 2) ≤ Real.exp (32 * Real.log Λ ^ 2) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hcore := y_core hX (by linarith) hlow hc1 hcle hr4 hrle (Real.exp_pos _).le hHs
  have hy : absorbYAt X₀ x = max (Real.exp (8 * l ^ 2))
      ((r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1) ^ 2) *
      max (L ^ 5) (48 * (r + (c + r * Real.sqrt c + r * (r + 1) / 2) + 1) * L ^ 3 / 0.15 ^ 2) *
      L ^ 6 := by
    rfl
  rw [hy]
  refine lt_of_lt_of_le hcore ?_
  rw [hΛdef, Real.exp_log (by linarith)]
  have hH := capH_le_rpow hX0 hX le_rfl
  have h8 : X₀ ^ (1 / 8 : ℝ) ≤ X₀ := by
    calc X₀ ^ (1 / 8 : ℝ) ≤ X₀ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
      _ = X₀ := Real.rpow_one X₀
  linarith

/-- **The absorbed set is empty at low heights.** Suppose every `a ∈ A` has a (jittered, latest)
prime `r` with `X₀⁻ = X₀ - H(X₀)/2 ≤ r < y(a)` (the definition (5) of `A`, together with the
centred placement of jittered primes, §6.8). Then `#(A ∩ [1, x]) = 0` for `log x ≤ (log X₀)²`. -/
theorem countA_eq_zero_of_low {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    {A : Set ℕ} (hA : ∀ a ∈ A, ∃ r : ℝ, X₀ - capH X₀ X₀ / 2 ≤ r ∧ r < absorbY X₀ a) :
    ∀ x ≥ (1 : ℝ), Real.log x ≤ Real.log X₀ ^ 2 → Absorbed.countA A x = 0 := by
  intro x hx1 hlow
  have hX1 := one_lt_of_logX hX0 hX
  have hX0p : 0 < X₀ := by linarith
  unfold Absorbed.countA
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro hkA
  obtain ⟨r, hr1, hr2⟩ := hA k hkA
  set m := max X₀ (k : ℝ) with hm
  have hXm : X₀ ≤ m := le_max_left _ _
  set z := dyadicScale X₀ m with hz
  have hz1 : X₀ ≤ z := le_dyadicScale hX0p hXm
  have hz2 : z ≤ m := dyadicScale_le hX0p (by linarith)
  have hlogm : Real.log m ≤ Real.log X₀ ^ 2 := by
    rcases le_total (k : ℝ) X₀ with h | h
    · rw [hm, max_eq_left h]; nlinarith
    · rw [hm, max_eq_right h]
      have hkx : (k : ℝ) ≤ x := by
        have := (Finset.mem_Icc.mp hk).2
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
      exact (Real.log_le_log (by linarith) hkx).trans hlow
  have hlogz : Real.log z ≤ Real.log X₀ ^ 2 :=
    (Real.log_le_log (by linarith) hz2).trans hlogm
  have := absorbYAt_lt hX0 hX hz1 hlogz
  have e : absorbY X₀ k = absorbYAt X₀ z := rfl
  linarith

end AbsorbEmpty

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  DesignedZero Target RankinMinorant GoodHeights AbsorbEmpty

/-- **The inputs of Theorem 4.10 without the emptiness of `A` at low heights.** As
`Theorem410InputsSize`, except that `#(A ∩ [1, x]) = 0` for `log x ≤ (log X₀)²` is no longer
assumed. In its place: every `a ∈ A` has a prime `r` (its latest prime, which is jittered) with
`X₀ - H(X₀)/2 ≤ r < y(a)`. This is the definition (5) of `A` together with the centred placement
of jittered primes (§6.8). -/
def Theorem410InputsAbs (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ κ₀ η : ℝ) (xp a : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℕ) (u : ℕ → ℝ),
    10 ^ 8 ≤ Real.log X₀ ∧ 1 / 4 ≤ θ ∧ θ ≤ 1 / 2 ∧
    Real.exp (-Real.log X₀) ≤ κ ∧ κ ≤ 1 ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (X₀ : ℝ) ^ 2 ≤ Real.log (xp 0) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (Dlt k)) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (θ / 2) A u ∧
    (∀ n ∈ A, ∃ r : ℝ, (X₀ : ℝ) - CaplLink.capH X₀ X₀ / 2 ≤ r ∧ r < absorbY X₀ n) ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x))) ∧
    (∀ k, ∀ s ∈ closedBall (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s +
        (∑' j, oscHat θ (designAlpha X₀ κ θ κ₀ Dlt xp j) (designGamma X₀ κ θ κ₀ Dlt xp j)
          (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (θ / 2) A u s)

/-- **The emptiness of `A` at low heights is derived**: `Theorem410InputsAbs` gives
`Theorem410InputsSize`. -/
theorem Theorem410InputsAbs.toSize {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsAbs θ F) :
    Theorem410InputsSize θ F := by
  obtain ⟨X₀, κ, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκ, hκ1, hκ₀1, hκ₀2, hxp0, hDd,
    hpieces, hsp, hη0, hη, ha, hD, hA, hAy, hbound, hdec⟩ := h
  exact ⟨X₀, κ, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκ, hκ1, hκ₀1, hκ₀2, hxp0, hDd,
    hpieces, hsp, hη0, hη, ha, hD, hA, countA_eq_zero_of_low (Nat.cast_nonneg _) hX hAy, hbound,
    hdec⟩

/-- Refined inputs for one system: `PartIInputsSlotModelInit` and `Theorem410InputsAbs`. -/
def TheoremAInputsAbs (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotModelInit θ X₀ P ∧ Theorem410InputsAbs θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsInitSize`, without the emptiness of
the absorbed set at low heights (derived from the definition of `A`). -/
def Theorem21InputsAbs : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsAbs θ X₀ (P ω)

theorem theorem21InputsInitSize_of_abs (h : Theorem21InputsAbs) : Theorem21InputsInitSize := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toSize⟩⟩

/-- The refined hypothesis `Theorem21InputsAbs` implies Theorem 2.1. -/
theorem theorem21_of_abs (h : Theorem21InputsAbs) : Theorem21 :=
  theorem21_of_initSize (theorem21InputsInitSize_of_abs h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsAbs`. -/
theorem corollary_2_2_of_abs (h : Theorem21InputsAbs) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_abs h)


end
