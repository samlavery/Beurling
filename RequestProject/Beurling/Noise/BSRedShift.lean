module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Theorem 5.6: elementary facts about `U(ℓ)`, `m(w)` and `u*`

* `Uf_monotoneOn`: `U` is non-decreasing in `ℓ`;
* `mOf_ge_tau`: for `w ≥ w₁`, `m(w) ≥ (ℓ - τ - log 2)/2 ≥ τ` (Step 2, `ℓ ≥ 3τ + log 2`);
* `U_shift`: for `ℓ ≥ 30τ`, `ℓ ≥ 3·10⁹` and `w₁ ≤ w ≤ U(ℓ) - 1/2`, `w ≤ U(m(w))`: the induction
  hypothesis applies to every prime with `w ≤ U(ℓ) - 1/2` (this replaces "`U(m) ≥ U(ℓ) - 1/2`
  for `m ≥ ℓ(1 - 1/U)`" of Step 6);
* `ustar_lemma53`: the hypotheses of Lemma 5.3 at `u* = U(ℓ) + 1/2`, `z = e^{ℓ/u*}` (Step 6);
* `base_lemma53`: the hypotheses of Lemma 5.3 at `1 ≤ u ≤ U(ℓ)`, `τ ≤ ℓ ≤ 30τ` (Step 4).
-/

@[expose] public section

open Real

namespace BSaias

lemma u0_nonneg (ℓ : ℝ) : 0 ≤ u0 ℓ := by unfold u0 BSCert.Z2.u0; positivity

lemma red_u0_sq {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : u0 ℓ ^ 2 = √ℓ := by
  unfold u0 BSCert.Z2.u0; rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma u0_pow4 {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : u0 ℓ ^ 4 = ℓ := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, red_u0_sq hℓ, Real.sq_sqrt hℓ]

lemma red_u0_mono {a b : ℝ} (h : a ≤ b) : u0 a ≤ u0 b := by
  unfold u0 BSCert.Z2.u0; exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

/-- `c q ≤ u0 ℓ` as soon as `(c q)^4 ≤ ℓ`. -/
lemma le_u0_of_pow4 {ℓ x : ℝ} (hx : 0 ≤ x) (h : x ^ 4 ≤ ℓ) : x ≤ u0 ℓ := by
  have hℓ : 0 ≤ ℓ := le_trans (by positivity) h
  by_contra hc
  push_neg at hc
  have := pow_lt_pow_left₀ hc (u0_nonneg ℓ) (by norm_num : (4 : ℕ) ≠ 0)
  rw [u0_pow4 hℓ] at this
  linarith

lemma Uf_monotoneOn {τ : ℝ} (hτ : 0 < τ) : MonotoneOn (Uf τ) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold Uf
  have h1 := red_u0_mono hab
  have h2 : √(2 * Real.log (a / τ) + 4) ≤ √(2 * Real.log (b / τ) + 4) := by
    apply Real.sqrt_le_sqrt
    have := Real.log_le_log (div_pos ha hτ) (div_le_div_of_nonneg_right hab hτ.le)
    linarith
  have := u0_nonneg a
  have := Real.sqrt_nonneg (2 * Real.log (a / τ) + 4)
  nlinarith

lemma u0_le_Uf (τ ℓ : ℝ) : u0 ℓ ≤ Uf τ ℓ := by
  unfold Uf
  have := u0_nonneg ℓ
  have := Real.sqrt_nonneg (2 * Real.log (ℓ / τ) + 4)
  nlinarith

lemma one_add_w1 {τ ℓ : ℝ} (h : 0 < ℓ + τ + Real.log 2) :
    1 + w1 τ ℓ = 2 * ℓ / (ℓ + τ + Real.log 2) := by
  unfold w1; field_simp; ring

lemma red_w1_pos {τ ℓ : ℝ} (hτ : 0 ≤ τ) (hℓ : τ + Real.log 2 < ℓ) : 0 < w1 τ ℓ := by
  unfold w1
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_pos (by linarith) (by linarith)

lemma w1_lt_one {τ ℓ : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) : w1 τ ℓ < 1 := by
  unfold w1
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_one (by linarith)]; linarith

lemma mOf_mono {ℓ a b : ℝ} (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a ≤ b) : mOf ℓ a ≤ mOf ℓ b := by
  unfold mOf
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma mOf_w1 {τ ℓ : ℝ} (hτ : 0 ≤ τ) (hℓ : τ + Real.log 2 < ℓ) :
    mOf ℓ (w1 τ ℓ) = (ℓ - τ - Real.log 2) / 2 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hD : 0 < ℓ + τ + Real.log 2 := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  unfold mOf
  rw [one_add_w1 hD]
  unfold w1
  field_simp

/-- For `w ≥ w₁`: `m(w) ≥ τ` (when `ℓ ≥ 3τ + log 2`). -/
lemma mOf_ge_tau {τ ℓ w : ℝ} (hτ : 0 < τ) (hℓ : 3 * τ + Real.log 2 ≤ ℓ) (hw : w1 τ ℓ ≤ w) :
    τ ≤ mOf ℓ w := by
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hℓ' : τ + Real.log 2 < ℓ := by linarith
  have := mOf_mono (ℓ := ℓ) (by linarith) (red_w1_pos hτ.le hℓ').le hw
  rw [mOf_w1 hτ.le hℓ'] at this
  linarith

lemma mOf_lt {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 ≤ w) : mOf ℓ w < ℓ := by
  unfold mOf; rw [div_lt_iff₀ (by linarith)]; linarith

lemma log_thirty_gt : 3 < Real.log 30 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have := pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : (3 : ℕ) ≠ 0)
  linarith [show (2.7182818286 : ℝ) ^ 3 < 30 by norm_num]

/-- The arithmetic core of case C of `U_shift`. -/
lemma shift_core {q s U w x Um : ℝ} (hq : 0 ≤ q) (hs : 3 ≤ s) (hU : U = q * (1 + s))
    (hw : 0 ≤ w) (hx : x = 1 / (1 + w)) (hwU : w ≤ U - 1 / 2) (hw735 : 0.735 * U ≤ w)
    (hUm : q * (1 - 0.26 * x) * (1 + (s - 0.52 * x)) ≤ Um) : w ≤ Um := by
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have e1 : U - 0.39 * U * x ≤ q * (1 - 0.26 * x) * (1 + (s - 0.52 * x)) := by
    have : q * (1 - 0.26 * x) * (1 + (s - 0.52 * x)) - (U - 0.39 * U * x) =
        q * x * (0.13 * s - 0.39 + 0.1352 * x) := by rw [hU]; ring
    have : 0 ≤ q * x * (0.13 * s - 0.39 + 0.1352 * x) :=
      mul_nonneg (mul_nonneg hq hx0) (by linarith)
    linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have e2 : 0.39 * U ≤ (U - w) * (1 + w) := by
    rcases le_or_gt (U - w) 0.54 with hd | hd
    · nlinarith
    · nlinarith
  have e3 : 0.39 * U * x ≤ U - w := by
    rw [hx, mul_one_div, div_le_iff₀ (by linarith)]; linarith
  linarith

/-- Case C of `U_shift` (`w > U(ℓ/2)`). -/
lemma shift_caseC {τ ℓ w q s : ℝ} (hτ0 : 0 < τ) (hℓ0 : 0 < ℓ) (hq0 : 0 ≤ q)
    (hq4 : q ^ 4 = ℓ) (hq234 : 234 ≤ q) (hs3 : 3 ≤ s)
    (hss : s ^ 2 = 2 * Real.log (ℓ / τ) + 4) (hU : Uf τ ℓ = q * (1 + s))
    (hm0 : 0 < mOf ℓ w) (hw0 : 0 < w) (hw2 : w ≤ Uf τ ℓ - 1 / 2)
    (hC : Uf τ (ℓ / 2) < w) (hUhalf : 0.735 * Uf τ ℓ ≤ Uf τ (ℓ / 2)) :
    w ≤ Uf τ (mOf ℓ w) := by
  set m := mOf ℓ w with hm
  set x := 1 / (1 + w) with hx
  have hUq : 3 * q ≤ Uf τ ℓ := by rw [hU]; nlinarith
  have hw100 : 100 ≤ w := by linarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx01 : x ≤ 0.01 := by rw [hx, div_le_iff₀ (by linarith)]; linarith
  have hmx : m = ℓ * (1 - x) := by
    rw [hm, hx]; unfold mOf; field_simp; ring
  have hx3 : x ^ 3 ≤ 1 := by
    calc x ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hx0.le (by linarith) 3
      _ = 1 := by norm_num
  have hx2 := pow_two_nonneg x
  have hu0m : q * (1 - 0.26 * x) ≤ u0 m := by
    apply le_u0_of_pow4 (mul_nonneg hq0 (by linarith))
    rw [mul_pow, hq4, hmx]
    apply mul_le_mul_of_nonneg_left _ hℓ0.le
    have e : (1 - x) - (1 - 0.26 * x) ^ 4 =
        x * (0.04 - 0.4056 * x + 0.070304 * x ^ 2 - 0.00456976 * x ^ 3) := by ring
    have : 0 ≤ x * (0.04 - 0.4056 * x + 0.070304 * x ^ 2 - 0.00456976 * x ^ 3) :=
      mul_nonneg hx0.le (by linarith)
    linarith
  have h1x : 0 < 1 - x := by linarith
  have hlog1x : -(1.02 * x) ≤ Real.log (1 - x) := by
    have h := Real.one_sub_inv_le_log_of_pos h1x
    have e : 1 - (1 - x)⁻¹ - -(1.02 * x) = x * (0.02 - 1.02 * x) / (1 - x) := by
      field_simp; ring
    have : 0 ≤ 1 - (1 - x)⁻¹ - -(1.02 * x) := by
      rw [e]; exact div_nonneg (mul_nonneg hx0.le (by linarith)) h1x.le
    linarith
  have hsm : s - 0.52 * x ≤ √(2 * Real.log (m / τ) + 4) := by
    apply Real.le_sqrt_of_sq_le
    rw [hmx, show ℓ * (1 - x) / τ = (ℓ / τ) * (1 - x) by ring,
      Real.log_mul (by positivity) h1x.ne']
    have : (s - 0.52 * x) ^ 2 = s ^ 2 - 1.04 * s * x + 0.2704 * x ^ 2 := by ring
    have : 3.12 * x ≤ 1.04 * s * x := by nlinarith
    nlinarith
  have hUm : q * (1 - 0.26 * x) * (1 + (s - 0.52 * x)) ≤ Uf τ m := by
    unfold Uf
    have h2 : 0 ≤ 1 + (s - 0.52 * x) := by linarith
    have := mul_le_mul hu0m (show 1 + (s - 0.52 * x) ≤ 1 + √(2 * Real.log (m / τ) + 4) by
      linarith) h2 (u0_nonneg m)
    linarith
  exact shift_core hq0 hs3 hU hw0.le hx hw2 (by linarith) hUm

/-- **The shift lemma**: for `w₁ ≤ w ≤ U(ℓ) - 1/2`, `w ≤ U(m(w))`. -/
theorem U_shift {τ ℓ w : ℝ} (hτ : 1 ≤ τ) (hℓτ : 30 * τ ≤ ℓ) (hℓ : 3000000000 ≤ ℓ)
    (hw1 : w1 τ ℓ ≤ w) (hw2 : w ≤ Uf τ ℓ - 1 / 2) : w ≤ Uf τ (mOf ℓ w) := by
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl2' : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hw0 : 0 < w := lt_of_lt_of_le (red_w1_pos hτ0.le (by linarith)) hw1
  set q := u0 ℓ with hq
  have hq0 : 0 ≤ q := u0_nonneg ℓ
  have hq4 : q ^ 4 = ℓ := u0_pow4 hℓ0.le
  have hq234 : 234 ≤ q := le_u0_of_pow4 (by norm_num) (by norm_num; linarith)
  set s := √(2 * Real.log (ℓ / τ) + 4) with hs
  have hlogℓτ : Real.log 30 ≤ Real.log (ℓ / τ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hτ0]; linarith)
  have hs3 : 3 ≤ s := by
    rw [hs, show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; linarith [log_thirty_gt]
  have hss : s ^ 2 = 2 * Real.log (ℓ / τ) + 4 := by
    rw [hs, Real.sq_sqrt (by linarith [log_thirty_gt])]
  have hU : Uf τ ℓ = q * (1 + s) := by unfold Uf; rw [← hq, ← hs]; ring
  set m := mOf ℓ w with hm
  have hmτ : τ ≤ m := mOf_ge_tau hτ0 (by linarith) hw1
  have hm0 : 0 < m := by linarith
  -- Case A: w ≤ 1
  rcases le_or_gt w 1 with hA | hA
  · refine hA.trans ((?_ : (1 : ℝ) ≤ u0 m).trans (u0_le_Uf τ m))
    exact le_u0_of_pow4 (by norm_num) (by norm_num; linarith)
  -- m ≥ ℓ/2
  have hmhalf : ℓ / 2 ≤ m := by
    rw [hm]; unfold mOf; rw [le_div_iff₀ (by linarith)]; nlinarith
  have hmono := Uf_monotoneOn hτ0 (show (0 : ℝ) < ℓ / 2 by linarith) (show (0 : ℝ) < m from hm0)
    hmhalf
  -- lower bound U(ℓ/2) ≥ 0.735 U(ℓ)
  have hUhalf : 0.735 * Uf τ ℓ ≤ Uf τ (ℓ / 2) := by
    have h1 : 0.84 * q ≤ u0 (ℓ / 2) :=
      le_u0_of_pow4 (by positivity) (by rw [mul_pow, hq4]; nlinarith)
    have h2 : s - 0.5 ≤ √(2 * Real.log (ℓ / 2 / τ) + 4) := by
      rw [show ℓ / 2 / τ = (ℓ / τ) / 2 by ring, Real.log_div (by positivity) (by norm_num)]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    rw [hU]
    unfold Uf
    have h2' : 1 + (s - 0.5) ≤ 1 + √(2 * Real.log (ℓ / 2 / τ) + 4) := by linarith
    have := mul_le_mul h1 h2' (by linarith) (u0_nonneg _)
    nlinarith
  rcases le_or_gt w (Uf τ (ℓ / 2)) with hB | hC
  · exact hB.trans hmono
  exact shift_caseC hτ0 hℓ0 hq0 hq4 hq234 hs3 hss hU hm0 hw0 hw2 hC hUhalf

/-- The hypotheses of Lemma 5.3 at `u* = U(ℓ) + 1/2` (Step 6). -/
theorem ustar_lemma53 {τ ℓ : ℝ} (hτ : 1 ≤ τ) (hℓτ : 30 * τ ≤ ℓ) (hℓ : 3000000000 ≤ ℓ) :
    1 ≤ ustar τ ℓ ∧ 100 ≤ ℓ / ustar τ ℓ ∧ ustar τ ℓ ≤ ℓ / ustar τ ℓ := by
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set r := √(u0 ℓ) with hr
  have hq0 := u0_nonneg ℓ
  have hr2 : r ^ 2 = u0 ℓ := by rw [hr, Real.sq_sqrt hq0]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq4 : u0 ℓ ^ 4 = ℓ := u0_pow4 hℓ0.le
  have hq234 : 234 ≤ u0 ℓ := le_u0_of_pow4 (by norm_num) (by norm_num; linarith)
  have hr15 : 15 ≤ r := by nlinarith
  set s := √(2 * Real.log (ℓ / τ) + 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlog : Real.log (ℓ / τ) ≤ u0 ℓ * 4 := by
    have h1 : Real.log (ℓ / τ) ≤ Real.log ℓ :=
      Real.log_le_log (by positivity) (div_le_self hℓ0.le hτ)
    have h2 : Real.log ℓ = 4 * Real.log (u0 ℓ) := by
      have : Real.log (u0 ℓ ^ 4) = 4 * Real.log (u0 ℓ) := by rw [Real.log_pow]; norm_num
      rwa [hq4] at this
    have h3 := Real.log_le_sub_one_of_pos (show 0 < u0 ℓ by linarith)
    linarith
  have hs3 : s ≤ 3 * r := by
    rw [hs]; apply Real.sqrt_le_iff.mpr; refine ⟨by positivity, ?_⟩
    nlinarith
  have hU : ustar τ ℓ = u0 ℓ * (1 + s) + 1 / 2 := by unfold ustar Uf; rw [← hs]; ring
  have hU1 : 1 ≤ ustar τ ℓ := by rw [hU]; nlinarith
  have hUle : ustar τ ℓ ≤ 4 * r ^ 3 := by rw [hU, ← hr2]; nlinarith
  have hU0 : 0 < ustar τ ℓ := by linarith
  have hℓr : ℓ = r ^ 8 := by rw [← hq4, ← hr2]; ring
  refine ⟨hU1, ?_, ?_⟩
  · rw [le_div_iff₀ hU0]
    have : 100 * (4 * r ^ 3) ≤ r ^ 8 := by
      have : (400 : ℝ) ≤ r ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num) hr15 5]
      nlinarith [pow_nonneg hr0 3]
    nlinarith
  · rw [le_div_iff₀ hU0]
    have h16 : (4 * r ^ 3) ^ 2 ≤ r ^ 8 := by
      have : (16 : ℝ) ≤ r ^ 2 := by nlinarith
      nlinarith [pow_nonneg hr0 6]
    have := mul_le_mul hUle hUle hU0.le (by positivity)
    nlinarith

/-- The hypotheses of Lemma 5.3 in the base region `τ ≤ ℓ ≤ 30τ`, `1 ≤ u ≤ U(ℓ)` (Step 4). -/
theorem base_lemma53 {τ ℓ u : ℝ} (hτ : 100000000 ≤ τ) (h1 : τ ≤ ℓ) (h2 : ℓ ≤ 30 * τ)
    (hu1 : 1 ≤ u) (hu2 : u ≤ Uf τ ℓ) : 100 ≤ ℓ / u ∧ u ≤ ℓ / u := by
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hq0 := u0_nonneg ℓ
  have hq4 : u0 ℓ ^ 4 = ℓ := u0_pow4 hℓ0.le
  have hq100 : 100 ≤ u0 ℓ := le_u0_of_pow4 (by norm_num) (by norm_num; linarith)
  set s := √(2 * Real.log (ℓ / τ) + 4) with hs
  have hlog : Real.log (ℓ / τ) ≤ Real.log 30 :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ hτ0]; linarith)
  have hl30 : Real.log 30 < 3.5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h' : Real.exp 3.5 = Real.exp 1 ^ 3 * Real.exp 0.5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h05 := Real.add_one_le_exp (0.5 : ℝ)
    have he := Real.exp_one_gt_d9
    have h3 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
      pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have : (2.7182818283 : ℝ) ^ 3 * 1.5 > 30 := by norm_num
    rw [h']
    nlinarith [Real.exp_pos 0.5, pow_pos (Real.exp_pos 1) 3]
  have hs4 : s ≤ 4 := by
    rw [hs]; apply Real.sqrt_le_iff.mpr; refine ⟨by norm_num, ?_⟩; nlinarith
  have hU : Uf τ ℓ ≤ 5 * u0 ℓ := by
    unfold Uf; rw [← hs]; nlinarith [Real.sqrt_nonneg (2 * Real.log (ℓ / τ) + 4)]
  have hu0 : 0 < u := by linarith
  have hu5 : u ≤ 5 * u0 ℓ := hu2.trans hU
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hu0]
    have : 500 * u0 ℓ ≤ u0 ℓ ^ 4 := by
      have : (500 : ℝ) ≤ u0 ℓ ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hq100 3]
      nlinarith
    nlinarith
  · rw [le_div_iff₀ hu0]
    have := mul_le_mul hu5 hu5 hu0.le (by positivity)
    have : 25 * u0 ℓ ^ 2 ≤ u0 ℓ ^ 4 := by nlinarith
    nlinarith

end BSaias

end
