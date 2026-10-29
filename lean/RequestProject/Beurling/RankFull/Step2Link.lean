module

public import RequestProject.Beurling.RankFull.CapLw
public import RequestProject.BSCert.CaplStep2
public import RequestProject.Beurling.RowWeights

/-!
# Theorem 6.23(a), Step 2 (high-degree rows, `s ≤ s_H + 1`): the inputs of `theorem_6_23a`

Step 2 of the proof of Theorem 6.23: with `ℓ = 2 log Λ + s`, `L = e^ℓ`, `X = log c`
(`BSCert.Capl.logc`), `A = A(Λ, s)` and
`j = ⌊(X - 1)/(2A) - 1/2⌋`, `D* = ⌊(X/2)/(1 + A)⌋` (`j2`, `k2`), the rows outside the cover have
degree `≥ D* + 1`, and Lemma 6.22(b) bounds their weights by
`w = 3 (e(π + D* + 1)/(D* + 1))^{D*+1} (X₀⁻)^{-(D*+1)}` (`w2`).

* `RankFull.step2_core_var` : the variant of `BSCert.Capl.step2_core` with the gain
  `k(Λ - 1 - A) - 1.1` (instead of `- log 3`): this absorbs the loss `k(Λ - log X₀⁻) ≤ 10⁻³` of
  Lemma 6.22(b) with `X₀⁻` (as in the paper);
* `RankFull.hc_step2`, `RankFull.hlow_step2`, `RankFull.h80_step2` : the inputs `hc`, `hlow`
  (as the binomial bound `C(r₀ + D*, D*) ≤ Q`) and (80) of `theorem_6_23a`;
* `RankFull.theorem_6_23a_step2` : **Theorem 6.23(a) for `-log Λ ≤ s ≤ s_H + 1`**, from
  `TypeUnionBound` (Lemma 6.21(ii)) at `w = w2`.
-/

@[expose] public section

open Finset MeasureTheory BSCert.Capl
open scoped ENNReal

namespace RankFull

set_option maxHeartbeats 1000000 in
/-- **The core estimate of Step 2, with the `X₀⁻` gain**: as `BSCert.Capl.step2_core`, but with
gain `kk(Λ - 1 - A) - 1.1`; also returns the facts on the floors and `A`. -/
lemma step2_core_var {X Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs7 : s ≤ 7)
    (hXG : 1.3 * G Λ s * Λ ≤ X) (hXstd : 4 * (2 * Real.log Λ + s) ^ 2 - Real.log 4 ≤ X) :
    0 ≤ ⌊(X - 1) / (2 * A Λ s) - 1 / 2⌋ ∧ 0 ≤ ⌊X / 2 / (1 + A Λ s)⌋ ∧ 12 ≤ A Λ s ∧
      A Λ s ≤ 2 * (2 * Real.log Λ + s) ∧ A Λ s + 1 < Λ ∧
      Real.exp (2 * Real.log Λ + s) + 10 * (2 * Real.log Λ + s) + 10 ≤
        (1 + (⌊(X - 1) / (2 * A Λ s) - 1 / 2⌋ : ℝ)) *
          (((⌊X / 2 / (1 + A Λ s)⌋ : ℝ) + 1) * (Λ - 1 - A Λ s) - 1.1) := by
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
  set p : ℝ := 1 + (⌊(X - 1) / (2 * a) - 1 / 2⌋ : ℝ) with hp_def
  have hp : 0.97 * X / (2 * a) ≤ p := by
    have h := Int.lt_floor_add_one ((X - 1) / (2 * a) - 1 / 2)
    have e : (X - 1) / (2 * a) - 1 / 2 = (X - 1 - a) / (2 * a) := by field_simp
    rw [e] at h
    have : 0.97 * X / (2 * a) ≤ (X - 1 - a) / (2 * a) := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    rw [hp_def, e]; linarith
  have hfl1 : 0 ≤ ⌊(X - 1) / (2 * a) - 1 / 2⌋ := by
    apply Int.floor_nonneg.mpr
    have : 1 / 2 ≤ (X - 1) / (2 * a) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  set kk : ℝ := (⌊X / 2 / (1 + a)⌋ : ℝ) + 1 with hkk_def
  have hkk : X / 2 / (1 + a) ≤ kk := (Int.lt_floor_add_one _).le
  have hΛa : Λ / 2 ≤ Λ - 1 - a := by
    have hlogΛ' : Real.log Λ ≤ Λ / 1000 + 999 := by
      have := Real.log_le_sub_one_of_pos (x := Λ / 1000) (by positivity)
      rw [Real.log_div hΛ0.ne' (by norm_num)] at this
      have h1000 := Real.log_le_sub_one_of_pos (x := 1000) (by norm_num)
      linarith
    linarith
  have hy16 : 16 ≤ X / 2 / (1 + a) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hfl2 : 0 ≤ ⌊X / 2 / (1 + a)⌋ := Int.floor_nonneg.mpr (by linarith)
  set gain := kk * (Λ - 1 - a) - 1.1 with hgain
  have hg : 0.999 * (X / 2 / (1 + a) * (Λ - 1 - a)) ≤ gain := by
    have h1 : X / 2 / (1 + a) * (Λ - 1 - a) ≤ kk * (Λ - 1 - a) :=
      mul_le_mul_of_nonneg_right hkk (by linarith)
    have h2 : 16 * (Λ / 2) ≤ X / 2 / (1 + a) * (Λ - 1 - a) :=
      mul_le_mul hy16 hΛa (by positivity) (by linarith)
    rw [hgain]; linarith
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have hprod : 0.97 * X / (2 * a) * (0.999 * (X / 2 / (1 + a) * (Λ - 1 - a))) ≤ p * gain :=
    mul_le_mul hp hg (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))) hp0
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
  refine ⟨hfl1, hfl2, hA12, ha2, hAΛ, ?_⟩
  show Real.exp ℓ + 10 * ℓ + 10 ≤ p * gain
  rw [hL] at hsmall ⊢
  linarith

/-- `j = ⌊(X - 1)/(2A) - 1/2⌋` (Step 2). -/
noncomputable def j2 (X a : ℝ) : ℕ := (⌊(X - 1) / (2 * a) - 1 / 2⌋).toNat

/-- `D* = ⌊(X/2)/(1 + A)⌋` (Step 2). -/
noncomputable def k2 (X a : ℝ) : ℕ := (⌊X / 2 / (1 + a)⌋).toNat

/-- The row-weight bound of Lemma 6.22(b) at degree `k'`: `3 (e(π + k')/k')^{k'} Xm^{-k'}`. -/
noncomputable def wHigh (π k' : ℕ) (Xm : ℝ) : ℝ :=
  3 * (Real.exp 1 * (π + k') / k') ^ k' * Xm⁻¹ ^ k'

lemma wHigh_pos {π k' : ℕ} (hk : 1 ≤ k') {Xm : ℝ} (hXm : 0 < Xm) : 0 < wHigh π k' Xm := by
  unfold wHigh
  have : (0 : ℝ) < k' := by exact_mod_cast hk
  positivity

/-- **Input `hc`**: `e (r₀(D+1))^{2j+1} < e^X` when `r₀(D+1) < e^A` and `(2j+1)A ≤ X - 1`. -/
theorem hc_step2 {X a : ℝ} {r₀ D j : ℕ} (hr : (r₀ : ℝ) * (D + 1) < Real.exp a)
    (hr0 : 1 ≤ r₀) (hj : (2 * j + 1 : ℝ) * a ≤ X - 1) :
    Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) < Real.exp X := by
  have hpos : 0 < (r₀ : ℝ) * (D + 1) := by
    have : (1 : ℝ) ≤ r₀ := by exact_mod_cast hr0
    positivity
  have h1 : ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) < Real.exp a ^ (2 * j + 1) :=
    pow_lt_pow_left₀ hr hpos.le (by omega)
  have h2 : Real.exp a ^ (2 * j + 1) ≤ Real.exp (X - 1) := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; linarith
  calc Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) < Real.exp 1 * Real.exp (X - 1) :=
        mul_lt_mul_of_pos_left (h1.trans_le h2) (Real.exp_pos 1)
    _ = Real.exp X := by rw [← Real.exp_add]; ring_nf

/-- **Input `hlow`, the count**: `C(r₀ + k, k) ≤ e^{X/2} = Q` when `r₀ + 1 ≤ e^A` and
`k(1 + A) ≤ X/2`. -/
theorem hlow_step2 {X a : ℝ} {r₀ k : ℕ} (hr : (r₀ : ℝ) + 1 ≤ Real.exp a)
    (hk : (k : ℝ) * (1 + a) ≤ X / 2) : ((r₀ + k).choose k : ℝ) ≤ Real.exp (X / 2) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk1
  · subst h0; simp; simpa using hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h1 := RowWeights.choose_le_exp_mul_div_pow (r₀ + k) k hk1
  have h2 : Real.exp 1 * ((r₀ + k : ℕ) : ℝ) / k ≤ Real.exp 1 * Real.exp a := by
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have h3 : (r₀ : ℝ) + k ≤ ((r₀ : ℝ) + 1) * k := by
      have : (0 : ℝ) ≤ r₀ := Nat.cast_nonneg _
      nlinarith
    have h4 : ((r₀ : ℝ) + 1) * k ≤ Real.exp a * k :=
      mul_le_mul_of_nonneg_right hr (by linarith)
    have he := Real.exp_pos 1
    calc Real.exp 1 * ((r₀ : ℝ) + k) ≤ Real.exp 1 * (Real.exp a * k) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) he.le
      _ = Real.exp 1 * Real.exp a * k := by ring
  calc ((r₀ + k).choose k : ℝ) ≤ (Real.exp 1 * ((r₀ + k : ℕ) : ℝ) / k) ^ k := h1
    _ ≤ (Real.exp 1 * Real.exp a) ^ k := pow_le_pow_left₀ (by positivity) h2 k
    _ = Real.exp (k * (1 + a)) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]
    _ ≤ Real.exp (X / 2) := Real.exp_le_exp.mpr hk

/-- **Input (80), the gain**: `log(1/w) ≥ k'(Λ - 1 - A) - 1.1` for `w = wHigh π k' Xm`, when
`π + 1 ≤ e^A`, `log Xm ≥ Λ - η` and `k' η ≤ 10⁻³`. -/
theorem gain_step2 {Λ a Xm η : ℝ} (hXm : 0 < Xm) {π k' : ℕ} (hk : 1 ≤ k')
    (hπ : (π : ℝ) + 1 ≤ Real.exp a) (hlog : Λ - η ≤ Real.log Xm) (hη : (k' : ℝ) * η ≤ 0.0001) :
    (k' : ℝ) * (Λ - 1 - a) - 1.1 ≤ Real.log (1 / wHigh π k' Xm) := by
  have hk' : (1 : ℝ) ≤ k' := by exact_mod_cast hk
  have hr : 0 < Real.exp 1 * (π + k') / k' := by positivity
  have hw : Real.log (wHigh π k' Xm) =
      Real.log 3 + k' * (1 + Real.log ((π + k') / k')) - k' * Real.log Xm := by
    unfold wHigh
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_inv, mul_div_assoc,
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  have hq : Real.log ((π + k') / k') ≤ a := by
    have : ((π : ℝ) + k') / k' ≤ π + 1 := by
      rw [div_le_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ π := Nat.cast_nonneg _
      nlinarith
    calc Real.log ((π + k') / k') ≤ Real.log (Real.exp a) :=
          Real.log_le_log (by positivity) (this.trans hπ)
      _ = a := Real.log_exp a
  have hl3 : Real.log 3 ≤ 1.09915 := by
    have h15 : Real.log 1.5 ≤ 0.406 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have hb := Real.exp_bound (x := (0.406 : ℝ)) (by norm_num [abs_of_pos]) (n := 5)
        (by norm_num)
      have := (abs_le.mp hb).1
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have e : Real.log 3 = Real.log 2 + Real.log 1.5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [one_div, Real.log_inv, hw]
  have : (k' : ℝ) * Real.log Xm ≥ k' * Λ - k' * η := by nlinarith
  nlinarith

/-- `L ≥ 60`, `r₀ ≤ L`, and the sizes `r₀(D+1) < e^A`, `r₀ + 1 ≤ e^A`, `r₀D + 1 ≤ e^A` in
Step 2, from `r₀ ≤ L/(3ℓ) + 4`, `D ≤ 2L/Λ`, `L = e^ℓ = Λ²eˢ` and `e^A = 2Λ³e^{2s}/ℓ`. -/
lemma step2_sizes {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs7 : s ≤ 7) {r₀ D : ℕ}
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4)
    (hD : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log Λ + s) / Λ) :
    (r₀ : ℝ) * (D + 1) < Real.exp (A Λ s) ∧ (r₀ : ℝ) + 1 ≤ Real.exp (A Λ s) ∧
      (r₀ : ℝ) * D + 1 ≤ Real.exp (A Λ s) ∧ 60 ≤ Real.exp (2 * Real.log Λ + s) ∧
      (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) := by
  obtain ⟨hΛ0, hlogΛ, hl1, -, -, -⟩ := step1_dom hΛ hs (by linarith) le_rfl
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hl : 18.42 ≤ ℓ := by linarith
  set L := Real.exp ℓ with hLdef
  have hL : L = Λ ^ 2 * Real.exp s := exp_two_log_add hΛ0
  have hes : Real.exp (-Real.log Λ) ≤ Real.exp s := Real.exp_le_exp.mpr hs
  rw [Real.exp_neg, Real.exp_log hΛ0] at hes
  have hLΛ : Λ ≤ L := by
    rw [hL]
    have : Λ ^ 2 * Λ⁻¹ = Λ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hes (sq_nonneg Λ)]
  have heA : Real.exp (A Λ s) = 2 * L ^ 2 / (ℓ * Λ) := by
    unfold A
    rw [show 2 * Real.log Λ + s = ℓ from rfl, Real.exp_log (by positivity), hL]
    have : Real.exp (2 * s) = Real.exp s ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [this]; field_simp
  -- `L ≥ ℓ³/6 ≥ 1000 ℓ`
  have hcube : ℓ ^ 3 / 6 ≤ L := by
    have h := Real.sum_le_exp_of_nonneg (x := ℓ) (by linarith) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : 0 ≤ ℓ ^ 2 / 2 := by positivity
    rw [hLdef]; linarith
  have hLl : 56 * ℓ ≤ L := by
    have h1 : 339 ≤ ℓ ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ ℓ)
    have e : ℓ * ℓ ^ 2 = ℓ ^ 3 := by ring
    linarith
  have hL60 : 60 ≤ L := by nlinarith
  have hr₀' : (r₀ : ℝ) ≤ L / (2 * ℓ) := by
    have : L / (3 * ℓ) + 4 ≤ L / (2 * ℓ) := by
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hD' : (D : ℝ) + 1 ≤ 3 * L / Λ := by
    have : 1 ≤ L / Λ := by rw [le_div_iff₀ hΛ0]; linarith
    have : (D : ℝ) ≤ 2 * L / Λ := hD
    have : 2 * L / Λ + 1 ≤ 3 * L / Λ := by
      rw [show 3 * L / Λ = 2 * L / Λ + L / Λ by ring]; linarith
    linarith
  have hr0n : (0 : ℝ) ≤ r₀ := Nat.cast_nonneg _
  have hDn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hkey : L / (2 * ℓ) * (3 * L / Λ) = 1.5 * L ^ 2 / (ℓ * Λ) := by field_simp; ring
  have hbig : 1.5 * L ^ 2 / (ℓ * Λ) + 1 < 2 * L ^ 2 / (ℓ * Λ) := by
    have : 0.5 * L ^ 2 / (ℓ * Λ) > 1 := by
      rw [gt_iff_lt, lt_div_iff₀ (by positivity)]; nlinarith
    have e : 2 * L ^ 2 / (ℓ * Λ) = 1.5 * L ^ 2 / (ℓ * Λ) + 0.5 * L ^ 2 / (ℓ * Λ) := by ring
    linarith
  have h1 : (r₀ : ℝ) * (D + 1) ≤ 1.5 * L ^ 2 / (ℓ * Λ) := by
    rw [← hkey]; exact mul_le_mul hr₀' hD' (by positivity) (by positivity)
  have hLℓ : L / (2 * ℓ) + 1 ≤ 1.5 * L ^ 2 / (ℓ * Λ) := by
    have : L / (2 * ℓ) * 3 ≤ L / (2 * ℓ) * (3 * L / Λ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ hΛ0]; linarith
    have h1' : 1 ≤ L / (2 * ℓ) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [← hkey]; linarith
  refine ⟨?_, ?_, ?_, hL60, ?_⟩
  · rw [heA]; linarith
  · rw [heA]; linarith
  · rw [heA]
    have : (r₀ : ℝ) * D ≤ (r₀ : ℝ) * (D + 1) := by nlinarith
    linarith
  · have : L / (2 * ℓ) ≤ L := div_le_self (by positivity) (by linarith)
    linarith

/-- `2Λ e^7 e^{-0.98Λ} ≤ 10⁻³` for `Λ ≥ 10⁸`. -/
lemma tiny_le {Λ : ℝ} (hΛ : 100000000 ≤ Λ) :
    2 * Λ * Real.exp 7 * Real.exp (-0.98 * Λ) ≤ 0.0001 := by
  have he7 : Real.exp 7 ≤ 1200 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 7 ≤ 2.7182818286 ^ 7 := pow_le_pow_left₀ (by positivity) h.le 7
      _ ≤ 1200 := by norm_num
  have hb : (0.98 * Λ) ^ 2 / 2 ≤ Real.exp (0.98 * Λ) := by
    have h := Real.sum_le_exp_of_nonneg (x := 0.98 * Λ) (by positivity) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith
  rw [show -0.98 * Λ = -(0.98 * Λ) by ring, Real.exp_neg]
  have hpos := Real.exp_pos (0.98 * Λ)
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The parameters of Step 2.** With `X = logc s_H Λ s`, `A = A(Λ, s)`, `j = j2 X A`,
`D* = k2 X A`, `L = e^ℓ`: `L ≥ 60`, `r₀ ≤ L`, the input `hc`, the size facts for `hlow`, and,
when `D* + 1 ≤ D`, the criterion (80) for `w = wHigh π (D* + 1) X₀⁻`, `w ≤ 1`, and the condition
`e(π + D* + 1)/((D* + 1) X₀⁻) ≤ 1/3` of Lemma 6.22(b). -/
theorem step2_params {sH Λ s Xm : ℝ} (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746)
    (hval : gstar sH = gTarget) (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs2 : s ≤ sH + 1)
    {r₀ D π : ℕ} (hr0 : 1 ≤ r₀)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log Λ + s) / Λ) (hπ : π ≤ r₀ * D)
    (hXm0 : 0 < Xm) (hXm : Λ - Real.exp (-0.98 * Λ) ≤ Real.log Xm) :
    60 ≤ Real.exp (2 * Real.log Λ + s) ∧ (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) ∧
      Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j2 (logc sH Λ s) (A Λ s) + 1) <
        Real.exp (logc sH Λ s) ∧
      (r₀ : ℝ) + 1 ≤ Real.exp (A Λ s) ∧
      ((k2 (logc sH Λ s) (A Λ s) : ℕ) : ℝ) * (1 + A Λ s) ≤ logc sH Λ s / 2 ∧
      (k2 (logc sH Λ s) (A Λ s) + 1 ≤ D →
        Real.exp (2 * Real.log Λ + s) + 10 * Real.log (Real.exp (2 * Real.log Λ + s)) + 10 ≤
          (1 + (j2 (logc sH Λ s) (A Λ s) : ℕ)) *
            Real.log (1 / wHigh π (k2 (logc sH Λ s) (A Λ s) + 1) Xm) ∧
        wHigh π (k2 (logc sH Λ s) (A Λ s) + 1) Xm ≤ 1 ∧
        Real.exp 1 * (π + (k2 (logc sH Λ s) (A Λ s) + 1 : ℕ)) /
          ((k2 (logc sH Λ s) (A Λ s) + 1 : ℕ) * Xm) ≤ 1 / 3) := by
  set X := logc sH Λ s with hX
  set a := A Λ s with ha
  set ℓ := 2 * Real.log Λ + s with hℓ
  set L := Real.exp ℓ with hL
  have hs7 : s ≤ 7 := by linarith [hsH.2]
  have hXG := logc_ge_G hsH hval hΛ hs hs2
  have hXstd : 4 * ℓ ^ 2 - Real.log 4 ≤ X := le_max_left _ _
  obtain ⟨hf1, hf2, ha12, ha2l, haΛ, hcore⟩ := step2_core_var hΛ hs hs7 hXG hXstd
  obtain ⟨hsz1, hsz2, hsz3, hL60, hr0L⟩ := step2_sizes hΛ hs hs7 hr₀ hDle
  have ha0 : 0 < a := by linarith
  have hj : ((j2 X a : ℕ) : ℝ) = (⌊(X - 1) / (2 * a) - 1 / 2⌋ : ℝ) := by
    unfold j2; exact_mod_cast Int.toNat_of_nonneg hf1
  have hk : ((k2 X a : ℕ) : ℝ) = (⌊X / 2 / (1 + a)⌋ : ℝ) := by
    unfold k2; exact_mod_cast Int.toNat_of_nonneg hf2
  have hjA : (2 * (j2 X a : ℕ) + 1 : ℝ) * a ≤ X - 1 := by
    rw [hj]
    have := Int.floor_le ((X - 1) / (2 * a) - 1 / 2)
    have e : (2 * ((X - 1) / (2 * a) - 1 / 2) + 1) * a = X - 1 := by field_simp; ring
    nlinarith
  have hkA : ((k2 X a : ℕ) : ℝ) * (1 + a) ≤ X / 2 := by
    rw [hk]
    have := Int.floor_le (X / 2 / (1 + a))
    have e : X / 2 / (1 + a) * (1 + a) = X / 2 := by field_simp
    nlinarith
  refine ⟨hL60, hr0L, hc_step2 hsz1 hr0 hjA, hsz2, hkA, fun hDk => ?_⟩
  have hΛ0 : 0 < Λ := by linarith
  have hk1 : 1 ≤ k2 X a + 1 := by omega
  have hπ' : (π : ℝ) + 1 ≤ Real.exp a := by
    have : (π : ℝ) ≤ r₀ * D := by exact_mod_cast hπ
    linarith
  have hη : ((k2 X a + 1 : ℕ) : ℝ) * Real.exp (-0.98 * Λ) ≤ 0.0001 := by
    have h1 : ((k2 X a + 1 : ℕ) : ℝ) ≤ 2 * L / Λ :=
      le_trans (by exact_mod_cast hDk) hDle
    have hLe : L ≤ Λ ^ 2 * Real.exp 7 := by
      rw [hL, hℓ, exp_two_log_add hΛ0]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs7) (by positivity)
    have h2 : 2 * L / Λ ≤ 2 * Λ * Real.exp 7 := by
      rw [div_le_iff₀ hΛ0]
      have : 2 * Λ * Real.exp 7 * Λ = 2 * (Λ ^ 2 * Real.exp 7) := by ring
      rw [this]; linarith
    have := tiny_le hΛ
    have hep := (Real.exp_pos (-0.98 * Λ)).le
    calc ((k2 X a + 1 : ℕ) : ℝ) * Real.exp (-0.98 * Λ)
        ≤ 2 * Λ * Real.exp 7 * Real.exp (-0.98 * Λ) :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hep
      _ ≤ 0.0001 := this
  have hgain := gain_step2 hXm0 hk1 hπ' hXm hη
  have h80 : L + 10 * Real.log L + 10 ≤
      (1 + (j2 X a : ℕ)) * Real.log (1 / wHigh π (k2 X a + 1) Xm) := by
    rw [hL, Real.log_exp]
    have hj0 : (0 : ℝ) ≤ 1 + (j2 X a : ℕ) := by positivity
    calc Real.exp ℓ + 10 * ℓ + 10 ≤ (1 + (⌊(X - 1) / (2 * a) - 1 / 2⌋ : ℝ)) *
          (((⌊X / 2 / (1 + a)⌋ : ℝ) + 1) * (Λ - 1 - a) - 1.1) := hcore
      _ = (1 + (j2 X a : ℕ)) * (((k2 X a + 1 : ℕ) : ℝ) * (Λ - 1 - a) - 1.1) := by
          rw [hj]; push_cast; rw [hk]
      _ ≤ (1 + (j2 X a : ℕ)) * Real.log (1 / wHigh π (k2 X a + 1) Xm) :=
          mul_le_mul_of_nonneg_left hgain hj0
  have hw0 := wHigh_pos (π := π) hk1 hXm0
  -- `w ≤ 1`: the right side of (80) is positive
  have hw1 : wHigh π (k2 X a + 1) Xm ≤ 1 := by
    have hLpos : 0 < L + 10 * Real.log L + 10 := by
      have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      linarith
    have hlogpos : 0 < Real.log (1 / wHigh π (k2 X a + 1) Xm) := by
      have hj0 : (0 : ℝ) ≤ 1 + (j2 X a : ℕ) := by positivity
      by_contra hneg
      push_neg at hneg
      have : (1 + (j2 X a : ℕ) : ℝ) * Real.log (1 / wHigh π (k2 X a + 1) Xm) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hj0 hneg
      linarith
    rw [one_div, Real.log_inv] at hlogpos
    have hlt : Real.log (wHigh π (k2 X a + 1) Xm) < 0 := by linarith
    exact ((Real.log_neg_iff hw0).mp hlt).le
  -- the condition of Lemma 6.22(b)
  have hcond : Real.exp 1 * (π + (k2 X a + 1 : ℕ)) / ((k2 X a + 1 : ℕ) * Xm) ≤ 1 / 3 := by
    have hk' : (1 : ℝ) ≤ ((k2 X a + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    have hq : ((π : ℝ) + (k2 X a + 1 : ℕ)) / (k2 X a + 1 : ℕ) ≤ Real.exp a := by
      rw [div_le_iff₀ (by linarith)]
      have h0 : (0 : ℝ) ≤ π := Nat.cast_nonneg _
      have h1 : (π : ℝ) + (k2 X a + 1 : ℕ) ≤ ((π : ℝ) + 1) * (k2 X a + 1 : ℕ) := by
        have := mul_le_mul_of_nonneg_left hk' h0
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right hπ' (by linarith))
    have hXmlow : Real.exp (Λ - 1) ≤ Xm := by
      rw [← Real.exp_log hXm0]
      apply Real.exp_le_exp.mpr
      have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have haΛ' : a + 1 + Real.log 3 ≤ Λ - 1 := by
      have hlogΛ : Real.log Λ ≤ Λ / 1000 + 999 := by
        have := Real.log_le_sub_one_of_pos (x := Λ / 1000) (by positivity)
        rw [Real.log_div hΛ0.ne' (by norm_num)] at this
        have h1000 := Real.log_le_sub_one_of_pos (x := 1000) (by norm_num)
        linarith
      have hl3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num); linarith
      linarith
    have key : Real.exp 1 * Real.exp a ≤ Xm / 3 := by
      rw [← Real.exp_add]
      have : Real.exp (1 + a) ≤ Real.exp (Λ - 1) / 3 := by
        rw [le_div_iff₀ (by norm_num), ← Real.exp_log (by norm_num : (0 : ℝ) < 3),
          ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith [hXmlow]
    rw [div_le_iff₀ (by positivity)]
    have e : Real.exp 1 * (π + (k2 X a + 1 : ℕ)) =
        Real.exp 1 * (((π : ℝ) + (k2 X a + 1 : ℕ)) / (k2 X a + 1 : ℕ)) * (k2 X a + 1 : ℕ) := by
      field_simp
    rw [e]
    have h1 : Real.exp 1 * (((π : ℝ) + (k2 X a + 1 : ℕ)) / (k2 X a + 1 : ℕ)) ≤ Xm / 3 :=
      le_trans (mul_le_mul_of_nonneg_left hq (Real.exp_pos 1).le) key
    have hk0 : (0 : ℝ) ≤ ((k2 X a + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hk0]
  exact ⟨h80, hw1, hcond⟩

/-- **Theorem 6.23(a) in the range of Step 2** (`-log Λ ≤ s ≤ s_H + 1`, high-degree rows).
`L = e^ℓ`, `ℓ = 2 log Λ + s`, `c = e^X`, `X = log c = logc s_H Λ s`, `Q = e^{X/2}`,
`j = j2 X A`, `D* = k2 X A`; the integer degree cap `D ≤ 2L/Λ`, `r₀ ≤ L/(3ℓ) + 4`,
`log X₀⁻ ≥ Λ - e^{-0.98Λ}`, `π ≤ r₀ D`, and, when `D* + 1 ≤ D`, `TypeUnionBound`
(Lemma 6.21(ii)) at `w = wHigh π (D* + 1) X₀⁻`. (If `D* + 1 > D` the event is empty.) -/
theorem theorem_6_23a_step2 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ))
    (h0 : ∀ J ω, 0 ∉ S J ω) {sH Λ s Xm : ℝ} (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746)
    (hval : gstar sH = gTarget) (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) (hs2 : s ≤ sH + 1)
    {r₀ D π : ℕ} (hr0 : 1 ≤ r₀)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log Λ + s) / Λ)
    (hD : ∀ J ω, ∀ v ∈ S J ω, Covers.deg v ≤ D) (hπ : π ≤ r₀ * D) (hXm0 : 0 < Xm)
    (hXm : Λ - Real.exp (-0.98 * Λ) ≤ Real.log Xm)
    (hmeas : ∀ J ∈ W, Measurable fun ω =>
      (configCount r₀ (j2 (logc sH Λ s) (A Λ s)) (k2 (logc sH Λ s) (A Λ s)) (S J ω) : ℝ≥0∞))
    (htu : k2 (logc sH Λ s) (A Λ s) + 1 ≤ D →
      TypeUnionBound P Good W S r₀ (j2 (logc sH Λ s) (A Λ s)) (k2 (logc sH Λ s) (A Λ s))
        (Real.exp (2 * Real.log Λ + s)) (Real.exp (Real.exp (2 * Real.log Λ + s)))
        (wHigh π (k2 (logc sH Λ s) (A Λ s) + 1) Xm)) :
    P ({ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
      (r₀ : ℝ) + Covers.phi (Real.exp (logc sH Λ s)) (Real.exp (logc sH Λ s / 2)) r₀ ≤
        (S J ω).card} ∩ Good) ≤
      ENNReal.ofReal (Real.exp (2 * Real.log Λ + s) ^ (-3 : ℝ)) := by
  classical
  set X := logc sH Λ s with hX
  set a := A Λ s with ha
  obtain ⟨hL60, hr0L, hc, hsz2, hkA, hmain⟩ :=
    step2_params hsH hval hΛ hs hs2 hr0 hr₀ hDle hπ hXm0 hXm
  have hlow : ∀ J ω, ∀ V : Submodule ℚ (Fin m → ℚ), Covers.ElemSpanned (S J ω) V →
      Module.finrank ℚ V < r₀ → ((((Covers.inter (S J ω) V).filter
        (fun y => Covers.deg y ≤ k2 X a)).card : ℕ) : ℝ) ≤ Real.exp (X / 2) := by
    intro J ω V _ hV
    have h1 := Covers.card_le_of_mem_subspace V ((Covers.inter (S J ω) V).filter
      (fun y => Covers.deg y ≤ k2 X a)) (k2 X a)
      (fun v hv => by
        have := (Finset.mem_filter.mp hv).1
        unfold Covers.inter at this
        exact (Finset.mem_filter.mp this).2)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    have h2 : (Module.finrank ℚ V + k2 X a).choose (k2 X a) ≤ (r₀ + k2 X a).choose (k2 X a) :=
      Nat.choose_le_choose _ (by omega)
    have h3 := hlow_step2 hsz2 hkA
    calc ((((Covers.inter (S J ω) V).filter (fun y => Covers.deg y ≤ k2 X a)).card : ℕ) : ℝ)
        ≤ ((r₀ + k2 X a).choose (k2 X a) : ℝ) := by exact_mod_cast h1.trans h2
      _ ≤ _ := h3
  by_cases hDk : k2 X a + 1 ≤ D
  · obtain ⟨h80, -, -⟩ := hmain hDk
    have hk1 : 1 ≤ k2 X a + 1 := by omega
    exact theorem_6_23a P hGood W S h0 hD (Q := Real.exp (X / 2)) (Real.exp_pos _).le hL60 hr0L
      (wHigh_pos hk1 hXm0) hc.le hlow hmeas (htu hDk) h80
  · have hempty : {ω | ∃ J ∈ W, Covers.rank (S J ω) < r₀ ∧
        (r₀ : ℝ) + Covers.phi (Real.exp X) (Real.exp (X / 2)) r₀ ≤ (S J ω).card} ∩ Good = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨J, _, hr, hcard⟩, _⟩
      have h1 := exists_config (h0 J ω) (hD J ω) (Real.exp_pos _).le hr hcard hc.le (hlow J ω)
      unfold configCount at h1
      obtain ⟨⟨C, B⟩, hCB⟩ := Finset.card_pos.mp h1
      obtain ⟨_, hBS, -, -, -, -, hRc, hdeg⟩ := Finset.mem_filter.mp hCB
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) hRc)
      have := hdeg y hy
      have := hD J ω y (hBS (Finset.mem_sdiff.mp hy).1)
      omega
    rw [hempty, measure_empty]; exact zero_le _

end RankFull
