module

public import RequestProject.Beurling.Queue6.S2Ep

/-!
# The size of `ε_z` (consistency of `hS2Ep`/`hS2Em` with `hS2err`, Lemma 5.22 "(SW) sums")

`H = max(e^{8 (log L)²}, M₁²)` gives `H ≥ L^{32}` and `M₁ L^{16} ≤ H` (`L = log u`), hence

* `eB_le` : `e(u) ≤ H(u) (1.04 s₂(u) + 51 L^{-6})` (the Freedman terms are `≤ 30 H L^{-7}`,
  `18 H L^{-6}`, …);
* `queueB_le_H` : `B(4w) ≤ H(w) L_w^{-6}` (`B ≤ 34 M₁ L_q²`, `H(4w) ≤ 1.00002 H(w)`);
* `s2ε_le` : `ε_z ≤ H(z) (1.1 s₂(u₁) + 1.1 s₂(2u₁) + 105 L₁^{-6})`, `L₁ = log u₁`;
* `hS2err_R` : hence `2 ε_z/H(z) + (3.3 + 2.1 m*) δ_z ≤ 2.2 s₂(u₁) + 2.2 s₂(2u₁) +
  210 L₁^{-6} + (6.6 + 4.2 m*)/H(z)` (`δ_z = 2/H(z)`), the form `2 ν̂ + O(δ)` of the paper
  (`ν̂(u) ≤ 62 L_u^{-6} + 1.1 s₂(u)`), so any `err` dominating the right side satisfies
  the field `hS2err`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed SlotModel QueueBound

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- `H(x) ≥ (log x)^{32}` and `M₁(x) (log x)^{16} ≤ H(x)`. -/
lemma capH_big {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    Real.log x ^ 32 ≤ capH X₀ x ∧ capM1 X₀ x * Real.log x ^ 16 ≤ capH X₀ x := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, -⟩ := logs_of_ge hX0 hc.hX hx
  set L := Real.log x
  have hM1 := QueueBound.one_le_capM1 hX0 hc.hX hx
  have hstd : Real.exp (8 * Real.log L ^ 2) ≤ capH X₀ x := le_max_left _ _
  have hMH : capM1 X₀ x ^ 2 ≤ capH X₀ x := le_max_right _ _
  have hlL : 4 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
    rw [e]; linarith
  have h32 : L ^ 32 ≤ capH X₀ x := by
    have e : L ^ 32 = Real.exp (32 * Real.log L) := by
      rw [show 32 * Real.log L = Real.log (L ^ 32) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [e]
    refine le_trans (Real.exp_le_exp.mpr ?_) hstd
    nlinarith
  refine ⟨h32, ?_⟩
  have hH0 : 0 ≤ capH X₀ x := by linarith [pow_nonneg (show (0 : ℝ) ≤ L by linarith) 32]
  have hsq : (capM1 X₀ x * L ^ 16) ^ 2 ≤ capH X₀ x ^ 2 := by
    have : (capM1 X₀ x * L ^ 16) ^ 2 = capM1 X₀ x ^ 2 * L ^ 32 := by ring
    rw [this]
    calc capM1 X₀ x ^ 2 * L ^ 32 ≤ capH X₀ x * capH X₀ x := mul_le_mul hMH h32 (by positivity) hH0
      _ = capH X₀ x ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) hH0 (by norm_num)).mp hsq

set_option maxHeartbeats 1600000 in
/-- **The block error is small**: `e(u) ≤ H(u) (1.04 s₂(u) + 51 L^{-6})`. -/
theorem eB_le (m : ℕ) :
    eB X₀ m ≤ capH X₀ (uS X₀ m) *
      (1.04 * s2E3 X₀ (uS X₀ m) + 51 / Real.log (uS X₀ m) ^ 6) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hu, hl, hH1, hM1⟩ := uS_facts hc m
  set u := uS X₀ m
  set L := Real.log u
  set H := capH X₀ u
  set M := capM1 X₀ u
  set lam := lamE3 X₀ u
  obtain ⟨h32', hML'⟩ := capH_big hc hu
  have h32 : L ^ 32 ≤ H := h32'
  have hML : M * L ^ 16 ≤ H := hML'
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith [X₀_ge_two_pow hc.hX]
  have hHu : H ≤ u / 10 ^ 7 := capH_le_div hc.hX hu
  have hlogH : Real.log H ≤ L := by
    have := Real.log_le_log (by linarith) (show H ≤ u by linarith); exact this
  have hlogL : Real.log L ≤ L / 1000 + 7 := by
    have := Real.log_le_sub_one_of_pos (show 0 < L / 1000 by positivity)
    rw [Real.log_div hL0.ne' (by norm_num)] at this
    have : Real.log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      rw [e]; nlinarith
    linarith
  have hlam : lam ≤ 4.1 * L := by
    have : lam = 3 * L + 2 * Real.log L + 2 + Real.log H := rfl
    rw [this]; nlinarith
  have hlam0 : 0 < lam := lamE3_pos hc m
  have hlog2 : Real.log (2 * u) ≤ 1.01 * L := by
    rw [Real.log_mul (by norm_num) hu0.ne']
    have := Real.log_two_lt_d9; nlinarith
  have hlog20 : 0 < Real.log (2 * u) := Real.log_pos (by linarith)
  have hH100 : 100 ≤ H := by
    have : (100 : ℝ) ≤ L ^ 32 := le_trans (by norm_num) (hl.trans (le_self_pow₀ (by linarith)
      (by norm_num)))
    linarith
  have hLen : LenB X₀ m ≤ 1.04 * H := by
    have : LenB X₀ m = 1.03 * H + 1 := rfl
    rw [this]; nlinarith
  have hLen0 : 0 ≤ LenB X₀ m := (LenB_pos hc m).le
  -- `A_u ≤ L`, `b₂ ≤ 2 L M`, `s₂ ≤ 9 L`
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
    unfold Xm; linarith
  have hlXm : 2 ≤ Real.log (Xm X₀) := by
    rw [Real.le_log_iff_exp_le (by linarith [X₀_ge_two_pow hc.hX])]
    have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le this 2
    linarith [X₀_ge_two_pow hc.hX]
  have hA : (AuE3 X₀ u : ℝ) ≤ L := by
    unfold AuE3
    have h1 : ((⌊Real.log (2 * u) / Real.log (Xm X₀)⌋₊ - 1 : ℕ) : ℝ) ≤
        (⌊Real.log (2 * u) / Real.log (Xm X₀)⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have h2 := Nat.floor_le (div_nonneg hlog20.le (by linarith : (0 : ℝ) ≤ Real.log (Xm X₀)))
    have h3 : Real.log (2 * u) / Real.log (Xm X₀) ≤ Real.log (2 * u) / 2 :=
      div_le_div_of_nonneg_left hlog20.le (by norm_num) hlXm
    linarith
  have hb2 : b2E3 X₀ u ≤ 2 * L * M := by
    unfold b2E3; nlinarith
  have hb20 := b2E3_nonneg hc m
  have hs2 := s2E3_pos hc u hl
  have hs2L : s2E3 X₀ u ≤ 9 * L := by
    unfold s2E3
    have hmax : 0 ≤ max (Real.log (Xm X₀)) (Real.sqrt (L * Real.log L) / 2) :=
      le_trans (by linarith) (le_max_left _ _)
    have : Real.exp (-max (Real.log (Xm X₀)) (Real.sqrt (L * Real.log L) / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  -- `M ≤ H / L^{16}`
  have hL16 : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ (by linarith)
  have hL6 : 0 < L ^ 6 := by positivity
  have hHL : 0 ≤ H := by linarith
  -- the five terms
  have hT1 : Real.sqrt (2 * (2 * M * (50 * Real.log (2 * u)) * LenB X₀ m) * lam) ≤
      30 * H / L ^ 6 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : 2 * (2 * M * (50 * Real.log (2 * u)) * LenB X₀ m) * lam ≤
        2 * (2 * M * (50 * (1.01 * L)) * (1.04 * H)) * (4.1 * L) := by gcongr
    have h2 : 2 * (2 * M * (50 * (1.01 * L)) * (1.04 * H)) * (4.1 * L) =
        861.328 * (M * L ^ 16) * H / L ^ 14 := by field_simp; ring
    have h3 : 861.328 * (M * L ^ 16) * H / L ^ 14 ≤ 861.328 * H * H / L ^ 14 := by
      gcongr
    have h4 : 861.328 * H * H / L ^ 14 ≤ (30 * H / L ^ 6) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
      have hH2 : 0 ≤ H * H := by positivity
      have e : (30 * H) ^ 2 * L ^ 14 = 900 * (H * H) * L ^ 14 := by ring
      have e2 : 861.328 * H * H * (L ^ 6) ^ 2 = 861.328 * (H * H) * L ^ 12 := by ring
      rw [e, e2]
      have : L ^ 12 ≤ L ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    linarith
  have hT2 : 2 * (2 * M) * lam / 3 ≤ H / L ^ 6 := by
    have h1 : 2 * (2 * M) * lam / 3 ≤ 5.5 * M * L := by nlinarith
    have h2 : 5.5 * M * L ≤ H / L ^ 6 := by
      rw [le_div_iff₀ hL6]
      have : 5.5 * L * L ^ 6 ≤ L ^ 16 := by
        have : L ^ 16 = L ^ 7 * L ^ 9 := by ring
        have h9 : (10 : ℝ) ≤ L ^ 9 := le_trans (by norm_num) (hl.trans (le_self_pow₀
          (by linarith) (by norm_num)))
        have : 0 ≤ L ^ 7 := by positivity
        nlinarith
      nlinarith
    linarith
  have hT3 : Real.sqrt (2 * (b2E3 X₀ u * s2E3 X₀ u * LenB X₀ m) * lam) ≤ 18 * H / L ^ 6 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : 2 * (b2E3 X₀ u * s2E3 X₀ u * LenB X₀ m) * lam ≤
        2 * (2 * L * M * (9 * L) * (1.04 * H)) * (4.1 * L) := by gcongr
    have h2 : 2 * (2 * L * M * (9 * L) * (1.04 * H)) * (4.1 * L) =
        153.504 * (M * L ^ 16) * H / L ^ 13 := by field_simp; ring
    have h3 : 153.504 * (M * L ^ 16) * H / L ^ 13 ≤ 153.504 * H * H / L ^ 13 := by gcongr
    have h4 : 153.504 * H * H / L ^ 13 ≤ (18 * H / L ^ 6) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have hH2 : 0 ≤ H * H := by positivity
      have e : (18 * H) ^ 2 * L ^ 13 = 324 * (H * H) * L ^ 13 := by ring
      have e2 : 153.504 * H * H * (L ^ 6) ^ 2 = 153.504 * (H * H) * L ^ 12 := by ring
      rw [e, e2]
      have : L ^ 12 ≤ L ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    linarith
  have hT4 : 2 * b2E3 X₀ u * lam / 3 ≤ H / L ^ 6 := by
    have h1 : 2 * b2E3 X₀ u * lam / 3 ≤ 5.5 * M * L ^ 2 := by nlinarith
    have h2 : 5.5 * M * L ^ 2 ≤ H / L ^ 6 := by
      rw [le_div_iff₀ hL6]
      have : 5.5 * L ^ 2 * L ^ 6 ≤ L ^ 16 := by
        have : L ^ 16 = L ^ 8 * L ^ 8 := by ring
        have h8 : (10 : ℝ) ≤ L ^ 8 := le_trans (by norm_num) (hl.trans (le_self_pow₀
          (by linarith) (by norm_num)))
        have : 0 ≤ L ^ 8 := by positivity
        nlinarith
      nlinarith
    linarith
  have hT5 : 100 * Real.log (2 * u) ≤ H / L ^ 6 := by
    rw [le_div_iff₀ hL6]
    have : 101 * L * L ^ 6 ≤ L ^ 32 := by
      have : L ^ 32 = L ^ 7 * L ^ 25 := by ring
      have h25 : (101 : ℝ) ≤ L ^ 25 := le_trans (by norm_num) (hl.trans (le_self_pow₀
        (by linarith) (by norm_num)))
      have : 0 ≤ L ^ 7 := by positivity
      nlinarith
    nlinarith
  have hT6 : s2E3 X₀ u * LenB X₀ m ≤ 1.04 * s2E3 X₀ u * H := by nlinarith
  show Real.sqrt (2 * (2 * M * (50 * Real.log (2 * u)) * LenB X₀ m) * lam) +
      2 * (2 * M) * lam / 3 +
      (Real.sqrt (2 * (b2E3 X₀ u * s2E3 X₀ u * LenB X₀ m) * lam) + 2 * b2E3 X₀ u * lam / 3) +
      s2E3 X₀ u * LenB X₀ m + 100 * Real.log (2 * u) ≤ _
  have e : H * (1.04 * s2E3 X₀ u + 51 / L ^ 6) = 1.04 * s2E3 X₀ u * H + 51 * H / L ^ 6 := by
    field_simp
  rw [e]
  have := add_le_add (add_le_add (add_le_add (add_le_add hT1 hT2) (add_le_add hT3 hT4)) hT6) hT5
  exact this.trans (le_of_eq (by ring))

set_option maxHeartbeats 800000 in
/-- **The queue term is small**: `B(4w) ≤ H(w) (log w)^{-6}`, `w ≥ X₀`. -/
theorem queueB_le_H {w : ℝ} (hw : (X₀ : ℝ) ≤ w) :
    queueB X₀ (4 * w) ≤ capH X₀ w / Real.log w ^ 6 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hw0 : 0 < w := by linarith
  have h4w : (X₀ : ℝ) ≤ 4 * w := by linarith
  obtain ⟨hl4, -, -⟩ := logs_of_ge hX0 hc.hX h4w
  obtain ⟨hlw, -, -⟩ := logs_of_ge hX0 hc.hX hw
  set L := Real.log (4 * w)
  have hM1 := QueueBound.one_le_capM1 hX0 hc.hX h4w
  obtain ⟨hq1, hq2, hq3⟩ := Lq_bounds hX0 hc.hX h4w
  have hLq : 10 ^ 8 ≤ Real.log (2 * (4 * w) + 12 * Real.log (4 * w) + 2) := by
    unfold Lq at hq1; linarith
  have hB := QueueBound.queueBound75_le hM1 hLq hc.hX
  have hLqK : Real.log (2 * (4 * w) + 12 * Real.log (4 * w) + 2) ≤ L + 1.4 := by
    unfold Lq at hq2; linarith
  obtain ⟨-, hML⟩ := capH_big hc h4w
  -- `H(4w) ≤ 1.00002 H(w)`
  have hS := CapHSlopeProof.capHSlope hc.hX w (4 * w) hw (by linarith)
  have hr : ((4 * w) / w) ^ (4 / 1000000 : ℝ) ≤ 1 + 4 / 1000000 * ((4 * w) / w - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := (4 * w) / w - 1)
      (by have : 0 ≤ (4 * w) / w := div_nonneg (by linarith) hw0.le
          linarith)
      (by norm_num : (0 : ℝ) ≤ 4 / 1000000) (by norm_num : (4 / 1000000 : ℝ) ≤ 1)
    simpa using this
  have e4 : (4 * w) / w = 4 := by field_simp
  rw [e4] at hr
  have hHw0 : 0 ≤ capH X₀ w := capH_nonneg _ _
  have hH4 : capH X₀ (4 * w) ≤ 1.00002 * capH X₀ w := by
    rw [e4] at hS
    calc capH X₀ (4 * w) ≤ (4 : ℝ) ^ (4 / 1000000 : ℝ) * capH X₀ w := hS
      _ ≤ 1.00002 * capH X₀ w := mul_le_mul_of_nonneg_right (by linarith) hHw0
  -- `log(4w) ≤ 1.0001 log w`
  have hLL : L ≤ 1.0001 * Real.log w := by
    show Real.log (4 * w) ≤ _
    rw [Real.log_mul (by norm_num) hw0.ne']
    have : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith
    nlinarith
  have hlwL : Real.log w ≤ L := Real.log_le_log hw0 (by linarith)
  have hL0 : 0 < Real.log w := by linarith
  set ℓ := Real.log w
  have hq0 : 0 ≤ Real.log (2 * (4 * w) + 12 * Real.log (4 * w) + 2) := by linarith
  have hsq : Real.log (2 * (4 * w) + 12 * Real.log (4 * w) + 2) ^ 2 ≤ (L + 1.4) ^ 2 :=
    pow_le_pow_left₀ hq0 hLqK 2
  have hM0 : 0 ≤ capM1 X₀ (4 * w) := by linarith
  unfold queueB
  refine (hB.1.trans hB.2).trans ?_
  -- `34 M (L + 1.4)² ≤ H(w)/ℓ⁶`
  have h1 : 34 * capM1 X₀ (4 * w) * Real.log (2 * (4 * w) + 12 * Real.log (4 * w) + 2) ^ 2 ≤
      34 * capM1 X₀ (4 * w) * (1.0002 * ℓ) ^ 2 := by
    have : L + 1.4 ≤ 1.0002 * ℓ := by nlinarith
    have : (L + 1.4) ^ 2 ≤ (1.0002 * ℓ) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
    gcongr
    linarith
  refine h1.trans ?_
  have hLl : ℓ ^ 16 ≤ L ^ 16 := pow_le_pow_left₀ hL0.le hlwL 16
  have hMl : capM1 X₀ (4 * w) * ℓ ^ 16 ≤ 1.00002 * capH X₀ w :=
    (mul_le_mul_of_nonneg_left hLl hM0).trans (hML.trans hH4)
  rw [le_div_iff₀ (by positivity)]
  have e : 34 * capM1 X₀ (4 * w) * (1.0002 * ℓ) ^ 2 * ℓ ^ 6 =
      34 * 1.0002 ^ 2 * (capM1 X₀ (4 * w) * ℓ ^ 16) / ℓ ^ 8 := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h8 : (100 : ℝ) ≤ ℓ ^ 8 := le_trans (by norm_num) (hlw.trans (le_self_pow₀
    (by linarith) (by norm_num)))
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **The size of `ε_z`**: `ε_z ≤ H(z) (1.1 s₂(u₁) + 1.1 s₂(2u₁) + 105 L₁^{-6})`. -/
theorem s2ε_le (z : ℝ) :
    s2ε X₀ z ≤ Hc X₀ z * (1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z)) +
      1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) + 105 / Real.log (uS X₀ (m1z X₀ z)) ^ 6) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set m1 := m1z X₀ z
  set u1 := uS X₀ m1
  set u2 := uS X₀ (m1 + 1)
  set w := max z (X₀ : ℝ)
  obtain ⟨hu1X, hl1, hH1, -⟩ := uS_facts hc m1
  obtain ⟨hu2X, hl2, hH2, -⟩ := uS_facts hc (m1 + 1)
  have hu21 : u2 = 2 * u1 := uS_succ m1
  have hwX : (X₀ : ℝ) ≤ w := le_max_right _ _
  -- `u₁ ≤ w`
  obtain ⟨hm1a, -⟩ := mB_spec hX0p (le_max_right (z - Hc X₀ z) (X₀ : ℝ))
  have hH0 := Hc_nonneg (X₀ := X₀) z
  have hu1w : u1 ≤ w := hm1a.trans (max_le_max (by linarith) le_rfl)
  have hHcz : Hc X₀ z = capH X₀ w := rfl
  have hHu1 : capH X₀ u1 ≤ Hc X₀ z := by
    rw [hHcz]; exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hu1X) (mem_Ici.mpr hwX) hu1w
  -- `H(2u₁) ≤ 1.00001 H(u₁)`
  have hS := CapHSlopeProof.capHSlope hc.hX u1 u2 hu1X (by rw [hu21]; linarith)
  have hu10 : 0 < u1 := by linarith
  have hr : (u2 / u1) ^ (4 / 1000000 : ℝ) ≤ 1 + 4 / 1000000 * (u2 / u1 - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := u2 / u1 - 1)
      (by have : 0 ≤ u2 / u1 := div_nonneg (by linarith) hu10.le
          linarith)
      (by norm_num : (0 : ℝ) ≤ 4 / 1000000) (by norm_num : (4 / 1000000 : ℝ) ≤ 1)
    simpa using this
  have e2 : u2 / u1 = 2 := by rw [hu21]; field_simp
  rw [e2] at hr hS
  have hHu10 : 0 ≤ capH X₀ u1 := by linarith
  have hHu2 : capH X₀ u2 ≤ 1.00001 * Hc X₀ z :=
    hS.trans ((mul_le_mul_of_nonneg_right (by linarith) hHu10).trans
      (mul_le_mul_of_nonneg_left hHu1 (by norm_num)))
  -- the pieces
  have hE1 := eB_le hc m1
  have hE2 := eB_le hc (m1 + 1)
  have hQ := queueB_le_H hc hwX
  set L1 := Real.log u1
  have hL20 : L1 ≤ Real.log u2 := Real.log_le_log hu10 (by rw [hu21]; linarith)
  have hLw : L1 ≤ Real.log w := Real.log_le_log hu10 hu1w
  have hL1p : 0 < L1 := by linarith
  have hL16 : 0 < L1 ^ 6 := by positivity
  have hs1 := s2E3_pos hc u1 hl1
  have hs2 := s2E3_pos hc u2 hl2
  have hd2 : 51 / Real.log u2 ^ 6 ≤ 51 / L1 ^ 6 :=
    div_le_div_of_nonneg_left (by norm_num) hL16 (pow_le_pow_left₀ hL1p.le hL20 6)
  have hdw : capH X₀ w / Real.log w ^ 6 ≤ Hc X₀ z / L1 ^ 6 := by
    rw [← hHcz]
    exact div_le_div_of_nonneg_left hH0 hL16 (pow_le_pow_left₀ hL1p.le hLw 6)
  -- `6 ≤ H(z) / L₁⁶`
  have h6 : 6 ≤ Hc X₀ z / L1 ^ 6 := by
    obtain ⟨h32, -⟩ := capH_big hc hu1X
    rw [le_div_iff₀ hL16]
    have : 6 * L1 ^ 6 ≤ L1 ^ 32 := by
      have : L1 ^ 32 = L1 ^ 6 * L1 ^ 26 := by ring
      have h26 : (6 : ℝ) ≤ L1 ^ 26 := le_trans (by norm_num) (hl1.trans (le_self_pow₀
        (by linarith) (by norm_num)))
      nlinarith
    linarith
  have hE1' : eB X₀ m1 ≤ Hc X₀ z * (1.04 * s2E3 X₀ u1 + 51 / L1 ^ 6) :=
    hE1.trans (mul_le_mul_of_nonneg_right hHu1 (by positivity))
  have hE2' : eB X₀ (m1 + 1) ≤ 1.00001 * Hc X₀ z * (1.04 * s2E3 X₀ u2 + 51 / L1 ^ 6) := by
    refine hE2.trans ?_
    have : 1.04 * s2E3 X₀ u2 + 51 / Real.log u2 ^ 6 ≤ 1.04 * s2E3 X₀ u2 + 51 / L1 ^ 6 := by
      linarith
    calc capH X₀ u2 * (1.04 * s2E3 X₀ u2 + 51 / Real.log u2 ^ 6)
        ≤ capH X₀ u2 * (1.04 * s2E3 X₀ u2 + 51 / L1 ^ 6) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ ≤ 1.00001 * Hc X₀ z * (1.04 * s2E3 X₀ u2 + 51 / L1 ^ 6) :=
          mul_le_mul_of_nonneg_right hHu2 (by positivity)
  unfold s2ε
  have hHL : Hc X₀ z / L1 ^ 6 * L1 ^ 6 = Hc X₀ z := by field_simp
  have e : Hc X₀ z * (1.1 * s2E3 X₀ u1 + 1.1 * s2E3 X₀ u2 + 105 / L1 ^ 6) =
      1.1 * Hc X₀ z * s2E3 X₀ u1 + 1.1 * Hc X₀ z * s2E3 X₀ u2 + 105 * (Hc X₀ z / L1 ^ 6) := by
    ring
  have e1 : Hc X₀ z * (1.04 * s2E3 X₀ u1 + 51 / L1 ^ 6) =
      1.04 * Hc X₀ z * s2E3 X₀ u1 + 51 * (Hc X₀ z / L1 ^ 6) := by ring
  have e2' : 1.00001 * Hc X₀ z * (1.04 * s2E3 X₀ u2 + 51 / L1 ^ 6) =
      1.0400104 * Hc X₀ z * s2E3 X₀ u2 + 51.00051 * (Hc X₀ z / L1 ^ 6) := by ring
  rw [e]
  rw [e1] at hE1'
  rw [e2'] at hE2'
  have : 0 ≤ Hc X₀ z * s2E3 X₀ u1 := by positivity
  have : 0 ≤ Hc X₀ z * s2E3 X₀ u2 := by positivity
  have : 0 ≤ Hc X₀ z / L1 ^ 6 := by positivity
  nlinarith

/-- **Consistency with the field `hS2err`**: with `δ_z = 2/H(z)` (`s2δ`),
`2 ε_z/H(z) + (3.3 + 2.1 m*) δ_z ≤ 2.2 s₂(u₁) + 2.2 s₂(2u₁) + 210 L₁^{-6} +
(6.6 + 4.2 m*)/H(z)`; any `err(z)` dominating the right side satisfies `hS2err`. -/
theorem hS2err_R (z mst : ℝ) :
    2 * s2ε X₀ z / Hc X₀ z + (3.3 + 2.1 * mst) * s2δ X₀ z ≤
      2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) +
        210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 + (6.6 + 4.2 * mst) / Hc X₀ z := by
  have hH : 0 < Hc X₀ z := by
    have := Hc_ge hc z
    have : 0 ≤ Real.log (max z X₀) := (logs_of_ge (Nat.cast_nonneg _) hc.hX
      (le_max_right z (X₀ : ℝ))).1 |> fun h => by linarith
    linarith
  have h := s2ε_le hc z
  have h2 : 2 * s2ε X₀ z / Hc X₀ z ≤ 2 * (1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z)) +
      1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) + 105 / Real.log (uS X₀ (m1z X₀ z)) ^ 6) := by
    rw [div_le_iff₀ hH]; nlinarith
  have h3 : (3.3 + 2.1 * mst) * s2δ X₀ z = (6.6 + 4.2 * mst) / Hc X₀ z := by
    unfold s2δ; field_simp; ring
  rw [h3]
  have e : 2 * (1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 1.1 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) +
      105 / Real.log (uS X₀ (m1z X₀ z)) ^ 6) = 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) +
      2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 := by ring
  rw [e] at h2
  exact add_le_add h2 le_rfl

end Queue6

end
