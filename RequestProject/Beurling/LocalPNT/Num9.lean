module

public import RequestProject.Beurling.LocalPNT.Num10

/-!
# Step 9 of the proof of Theorem 5.24(i): the numerics

Throughout `Λ ≥ 10⁸` and `L = log v ≥ log X_LP = 10⁵ Λ² log² Λ`; write `s = √L`, so
`s ≥ 316 Λ log Λ`.

* (Range) `L ≥ 10⁴ Λ² log L` (`yrange9`) and `L_{e^{2s}+1} ≤ log T_v + 1` (`hTy9`): the heights of
  Step 9 (`T₁ = e^{2√L}`) lie below `T_v`;
* (Constant of (i)) the shifted line, the horizontal segments, the tails and the smoothing error
  add up to at most `e^{97} Λ² e^{-c_LP √L}` (`num9_main`).
-/

@[expose] public section

open Real

namespace LocalPNT

namespace Num9

/-- `x² e^{-βx} ≤ 4/(β² e²)`. -/
lemma sq_mul_exp_neg_le {x β : ℝ} (hx : 0 ≤ x) (hβ : 0 < β) :
    x ^ 2 * Real.exp (-(β * x)) ≤ 4 / (β ^ 2 * Real.exp 2) := by
  have h1 := Real.add_one_le_exp (β * x / 2 - 1)
  have h2 : Real.exp (β * x / 2 - 1) * Real.exp 1 = Real.exp (β * x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he1 := Real.exp_pos 1
  have h3 : Real.exp 1 * (β * x / 2) ≤ Real.exp (β * x / 2) := by nlinarith
  have h4 : (Real.exp 1 * (β * x / 2)) ^ 2 ≤ Real.exp (β * x / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : Real.exp (β * x / 2) ^ 2 = Real.exp (β * x) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h6 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; ring_nf
  rw [h5] at h4
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  rw [← h6]
  nlinarith [sq_nonneg x]

/-- The basic facts on `s = √L`. -/
lemma s_facts {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ L) :
    18 ≤ Real.log Λ ∧ Real.log Λ ≤ Λ ∧ 0 ≤ L ∧ Real.sqrt L ^ 2 = L ∧
      316 * Λ * Real.log Λ ≤ Real.sqrt L ∧ 10 ^ 11 ≤ Real.sqrt L := by
  have hl := Num10.eighteen_le_log hΛ
  have hlΛ : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hsN : 316 * Λ * Real.log Λ ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by positivity) hL0]
    nlinarith [sq_nonneg (Λ * Real.log Λ)]
  refine ⟨hl, hlΛ, hL0, Real.sq_sqrt hL0, hsN, ?_⟩
  have : (10 ^ 11 : ℝ) ≤ 316 * Λ * Real.log Λ := by nlinarith
  linarith

/-- `log(316 Λ log Λ) ≤ 8 + 1.05 log Λ`. -/
lemma log_N_le {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    Real.log (316 * Λ * Real.log Λ) ≤ 8 + 1.05 * Real.log Λ := by
  have hl := Num10.eighteen_le_log hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hl0 : 0 < Real.log Λ := by linarith
  rw [Real.log_mul (by positivity) hl0.ne', Real.log_mul (by norm_num) hΛ0.ne']
  have h316 : Real.log 316 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have := Real.exp_one_gt_d9
    calc (316 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this.le 6
  have hll : Real.log (Real.log Λ) ≤ Real.log Λ / 20 + 2 := by
    have h := Num10.log_le_div_add (x := Real.log Λ) (N := Real.exp 3) hl0 (Real.exp_pos 3)
    rw [Real.log_exp] at h
    have he3 : 20 ≤ Real.exp 3 := by
      have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have := Real.exp_one_gt_d9
      calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) this.le 3
    have : Real.log Λ / Real.exp 3 ≤ Real.log Λ / 20 :=
      div_le_div_of_nonneg_left hl0.le (by norm_num) he3
    linarith
  linarith

/-- `log s ≤ log N + s/N - 1` with `N = 316 Λ log Λ`, in the form used below. -/
lemma log_s_le {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ L) :
    Real.log (Real.sqrt L) ≤
      7 + 1.05 * Real.log Λ + Real.sqrt L / (316 * Λ * Real.log Λ) := by
  obtain ⟨hl, -, -, -, hsN, hs⟩ := s_facts hΛ hL
  have hN : 0 < 316 * Λ * Real.log Λ := by positivity
  have h := Num10.log_le_div_add (x := Real.sqrt L) (by linarith) hN
  have := log_N_le hΛ
  linarith

/-- **(Range) for Step 9**: `L ≥ 10⁴ Λ² log L`. -/
theorem yrange9 {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ L) :
    10 ^ 4 * Λ ^ 2 * Real.log L ≤ L := by
  obtain ⟨hl, hlΛ, hL0, hs2, hsN, hs⟩ := s_facts hΛ hL
  set s := Real.sqrt L
  set l := Real.log Λ
  have hΛ0 : 0 < Λ := by linarith
  have hlogL : Real.log L = 2 * Real.log s := by rw [← hs2, Real.log_pow]; norm_num
  have hls := log_s_le hΛ hL
  set N := 316 * Λ * l
  have hN : 0 < N := by positivity
  set X := s / N
  have hsX : s = N * X := by simp only [X]; field_simp
  have hX1 : 1 ≤ X := by rw [le_div_iff₀ hN]; linarith
  rw [hlogL, ← hs2]
  -- `2·10⁴ Λ² (7 + 1.05 l + X) ≤ s² = N² X²`
  have key : 10 ^ 4 * Λ ^ 2 * (2 * (7 + 1.05 * l + X)) ≤ s ^ 2 := by
    rw [hsX]
    have hNX : N ^ 2 * X ^ 2 ≥ N ^ 2 * X := by nlinarith
    have hN2 : N ^ 2 = 316 ^ 2 * Λ ^ 2 * l ^ 2 := by simp only [N]; ring
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have h1 : 10 ^ 4 * (2 * (7 + 1.05 * l + X)) ≤ 316 ^ 2 * l ^ 2 * X := by
      have hlX : 18 * l ≤ l * l := by nlinarith
      have h2 : 18 * l * X ≤ l * l * X := mul_le_mul_of_nonneg_right hlX (by linarith)
      have h3 : 18 * l ≤ 18 * l * X := by nlinarith
      have h4 : 324 * X ≤ 18 * l * X := by nlinarith
      nlinarith
    nlinarith
  nlinarith

/-- **The heights of Step 9 lie below `T_v`**: `L_{e^{2√L}+1} ≤ log T_v + 1`. -/
theorem hTy9 {Λ L : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ L) :
    Lt (Real.exp (2 * Real.sqrt L) + 1) ≤ logTy Λ L + 1 := by
  obtain ⟨hl, hlΛ, hL0, hs2, hsN, hs⟩ := s_facts hΛ hL
  set s := Real.sqrt L
  set l := Real.log Λ
  have hΛ0 : 0 < Λ := by linarith
  have hlogL : Real.log L = 2 * Real.log s := by rw [← hs2, Real.log_pow]; norm_num
  have hls := log_s_le hΛ hL
  set N := 316 * Λ * l
  have hN : 0 < N := by positivity
  set X := s / N
  have hsX : s = N * X := by simp only [X]; field_simp
  have hX1 : 1 ≤ X := by rw [le_div_iff₀ hN]; linarith
  -- `Lt(e^{2s} + 1) ≤ 2s + 1`
  have hA : Lt (Real.exp (2 * s) + 1) ≤ 2 * s + 1 := by
    unfold Lt
    have he := Real.exp_pos (2 * s)
    have he1 : 4 ≤ Real.exp (2 * s) := by
      have := Real.add_one_le_exp (2 * s); linarith
    rw [abs_of_pos (by linarith), Real.log_le_iff_le_exp (by linarith), Real.exp_add]
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have hlogs0 : 0 < Real.log s := Real.log_pos (by linarith)
  have hlogL0 : 0 < Real.log L := by rw [hlogL]; positivity
  -- `102 Λ (2s + 500) log s ≤ s²`
  have hB : 2 * s + 500 ≤ L / (51 * Λ * Real.log L) := by
    rw [le_div_iff₀ (by positivity), hlogL, ← hs2]
    have h1 : (2 * s + 500) * (51 * Λ * (2 * Real.log s)) ≤
        2.000001 * s * (102 * Λ * (7 + 1.05 * l + X)) := by
      have : 2 * s + 500 ≤ 2.000001 * s := by linarith
      have h102 : 0 ≤ 102 * Λ * Real.log s := by positivity
      calc (2 * s + 500) * (51 * Λ * (2 * Real.log s)) = (2 * s + 500) * (102 * Λ * Real.log s) :=
            by ring
        _ ≤ 2.000001 * s * (102 * Λ * Real.log s) := mul_le_mul_of_nonneg_right this h102
        _ ≤ 2.000001 * s * (102 * Λ * (7 + 1.05 * l + X)) := by gcongr
    have h2 : 2.000001 * (102 * Λ * (7 + 1.05 * l + X)) ≤ s := by
      rw [hsX]; simp only [N]
      have : 2.000001 * 102 * (7 + 1.05 * l + X) ≤ 316 * l * X := by nlinarith
      nlinarith
    have hs0 : 0 ≤ s := by linarith
    nlinarith
  unfold logTy
  linarith

/-- `log(1/(17 log L/L)) ≤ log L` for `L ≥ 10⁸`. -/
theorem log_inv_c9 {L : ℝ} (hL : 10 ^ 8 ≤ L) :
    Real.log (1 / (17 * Real.log L / L)) ≤ Real.log L := by
  have hl := Num10.eighteen_le_log hL
  have hL0 : 0 < L := by linarith
  apply Real.log_le_log (by positivity)
  rw [one_div_div, div_le_iff₀ (by positivity)]
  nlinarith


/-- `e^{100} ≥ 2.7^{100}`. -/
lemma exp_100_ge : (2.7 : ℝ) ^ 100 ≤ Real.exp 100 := by
  have e : Real.exp 100 = Real.exp 1 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 100

/-- `e^{97} ≥ 2.71828^{97}`. -/
lemma exp_97_ge : (2.71828 : ℝ) ^ 97 ≤ Real.exp 97 := by
  have e : Real.exp 97 = Real.exp 1 ^ 97 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 97

/-- `s^{35} ≤ e^s` for `s ≥ 10⁸`. -/
lemma pow35_le_exp {s : ℝ} (hs : 10 ^ 8 ≤ s) : s ^ 35 ≤ Real.exp s := by
  have h := Num10.log_le_div_1e5 hs
  have hs0 : 0 < s := by linarith
  calc s ^ 35 = Real.exp (35 * Real.log s) := by
        rw [show (35 : ℝ) * Real.log s = Real.log (s ^ 35) by rw [Real.log_pow]; norm_num,
          Real.exp_log (pow_pos hs0 35)]
    _ ≤ Real.exp s := Real.exp_le_exp.mpr (by nlinarith)

/-- A junk term: `C s^{35} e^{-19 s} ≤ e^{-s}` for `C ≤ 2.7^{100}`. -/
lemma junk_le {s C : ℝ} (hs : 10 ^ 8 ≤ s) (hC : C ≤ 2.7 ^ 100) :
    C * s ^ 35 * Real.exp (-(19 * s)) ≤ Real.exp (-s) := by
  have h1 := pow35_le_exp hs
  have h2 : C ≤ Real.exp s :=
    hC.trans (exp_100_ge.trans (Real.exp_le_exp.mpr (by linarith)))
  have h3 : Real.exp s * Real.exp s * Real.exp (-(19 * s)) ≤ Real.exp (-s) := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  calc C * s ^ 35 * Real.exp (-(19 * s)) ≤ Real.exp s * Real.exp s * Real.exp (-(19 * s)) := by
        gcongr
    _ ≤ _ := h3

set_option maxHeartbeats 1000000 in
/-- **The constant of (i)** (Step 9): the shifted line (A), the horizontal segments (B), the
tails (C) and the smoothing error add up to at most `e^{97} Λ² e^{-c_LP √L}`. Here
`a ≥ 0.9 c_zf/(L_T + 442 + 2 log Λ + log L_T)` with `L_T = 2√L` is the shift of the contour. -/
theorem num9_main {Λ L a θ' : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hL : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ L)
    (ha : 0.9 * (cZF Λ / (2 * Real.sqrt L + 442 + 2 * Real.log Λ + Real.log (2 * Real.sqrt L)))
      ≤ a) (hθ' : θ' ≤ 0.51) :
    (1 / (2 * π)) * (GLam Λ (2 * Real.sqrt L) * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 *
          (4 * Real.log (1 + Real.exp (2 * Real.sqrt L) / a)))
        + 2 * GLam Λ (2 * Real.sqrt L) * (L ^ 17 * 76 ^ 19 * 3 * Real.exp (-(19 * Real.sqrt L)) /
          Real.exp (2 * Real.sqrt L))
        + (1.5 * Real.log L + 8) * (2 * (L ^ 17 * 76 ^ 19 * 3 / 19 *
          Real.exp (-(19 * Real.sqrt L)))))
      + 10 / Real.exp (Real.sqrt L) + 2000 * Real.exp ((θ' - 1) * L)
      ≤ Real.exp 97 * Λ ^ 2 * Real.exp (-(cLP Λ * Real.sqrt L)) := by
  obtain ⟨hl, hlΛ, hL0, hs2, hsN, hs⟩ := s_facts hΛ hL
  set s := Real.sqrt L
  set l := Real.log Λ
  have hΛ0 : 0 < Λ := by linarith
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < l := by linarith
  have hlsmall : l ≤ s / 10 ^ 10 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hΛs : Λ ≤ s := by nlinarith
  have hlog2s : Real.log (2 * s) ≤ 2 * s / 10 ^ 5 := Num10.log_le_div_1e5 (by linarith)
  have hlogs : Real.log s ≤ s / 10 ^ 5 := Num10.log_le_div_1e5 (by linarith)
  -- the denominator
  set Dn := 2 * s + 442 + 2 * l + Real.log (2 * s)
  have hlog2s0 : 0 ≤ Real.log (2 * s) := Real.log_nonneg (by linarith)
  have hDn0 : 0 < Dn := by positivity
  have hDn : Dn ≤ 2.0001 * s := by simp only [Dn]; linarith
  -- the shift `a`
  have ha1 : 0.0792 / (Λ * (2.0001 * s)) ≤ a := by
    refine le_trans ?_ ha
    rw [show 0.9 * (cZF Λ / Dn) = 0.0792 / (Λ * Dn) by unfold cZF; field_simp; norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hDn hΛ0.le)
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha1
  set c := cLP Λ with hcdef
  have hc : c = 0.0176 / Λ := by simp only [c]; unfold cLP cZF; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hΛ0]; linarith
  have haL : 2.2 * c * s ≤ a * L := by
    rw [← hs2]
    have : 0.0792 / (Λ * (2.0001 * s)) * s ^ 2 = 0.0792 / 2.0001 * s / Λ := by
      field_simp
    have h2 : 2.2 * c * s ≤ 0.0792 / (Λ * (2.0001 * s)) * s ^ 2 := by
      rw [this, hc]
      rw [show 2.2 * (0.0176 / Λ) * s = 0.03872 * s / Λ by ring]
      apply div_le_div_of_nonneg_right _ hΛ0.le
      nlinarith
    nlinarith [sq_nonneg s]
  set E := Real.exp (-(c * s))
  have hE0 : 0 < E := Real.exp_pos _
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  -- (A): `s² e^{-2.2 c s} ≤ 1214 Λ² E`
  have hsq : s ^ 2 * Real.exp (-(a * L)) ≤ 1214 * Λ ^ 2 * E := by
    have h1 : Real.exp (-(a * L)) ≤ Real.exp (-((1.2 * c) * s)) * E := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 := sq_mul_exp_neg_le hs0.le (show 0 < 1.2 * c by positivity)
    have h3 : 4 / ((1.2 * c) ^ 2 * Real.exp 2) ≤ 1214 * Λ ^ 2 := by
      have he2 : 7.389 ≤ Real.exp 2 := by
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith [Real.exp_one_gt_d9]
      rw [hc, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    calc s ^ 2 * Real.exp (-(a * L)) ≤ s ^ 2 * (Real.exp (-((1.2 * c) * s)) * E) := by gcongr
      _ = (s ^ 2 * Real.exp (-((1.2 * c) * s))) * E := by ring
      _ ≤ (1214 * Λ ^ 2) * E := mul_le_mul_of_nonneg_right (h2.trans h3) hE0.le
  have hG : GLam Λ (2 * s) ≤ 800.04 * s := by unfold GLam; linarith
  have hG0 : 0 ≤ GLam Λ (2 * s) := by unfold GLam; positivity
  have hlogA : Real.log (1 + Real.exp (2 * s) / a) ≤ 2.001 * s := by
    have hinv : 1 / a ≤ 26 * s ^ 2 := by
      rw [div_le_iff₀ ha0]
      have : 1 ≤ 0.0792 / (Λ * (2.0001 * s)) * (26 * s ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
      nlinarith [sq_nonneg s]
    have he1 : 1 ≤ Real.exp (2 * s) := Real.one_le_exp (by linarith)
    have hle : 1 + Real.exp (2 * s) / a ≤ Real.exp (2 * s) * (27 * s ^ 2) := by
      rw [div_eq_mul_one_div]
      nlinarith [sq_nonneg s]
    have h27 : Real.log 27 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc (27 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
    calc Real.log (1 + Real.exp (2 * s) / a) ≤ Real.log (Real.exp (2 * s) * (27 * s ^ 2)) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * s + Real.log 27 + 2 * Real.log s := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
            Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 2.001 * s := by linarith
  have hpi : 1 / (2 * π) ≤ 1 / 6.283184 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith [Real.pi_gt_d6]
  have hpi0 : 0 < 1 / (2 * π) := by positivity
  have hpi1 : 1 / (2 * π) ≤ 1 := hpi.trans (by norm_num)
  have hlog4 : 0 ≤ Real.log (1 + Real.exp (2 * s) / a) := Real.log_nonneg (by
    have : 0 ≤ Real.exp (2 * s) / a := by positivity
    linarith)
  have hA : GLam Λ (2 * s) * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 *
      (4 * Real.log (1 + Real.exp (2 * s) / a))) ≤
      (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) * Λ ^ 2 * E := by
    calc GLam Λ (2 * s) * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 *
          (4 * Real.log (1 + Real.exp (2 * s) / a))) ≤
        (800.04 * s) * (Real.exp (-(a * L)) * 76 ^ 19 * 1.0001 * (4 * (2.001 * s))) := by
          gcongr
      _ = (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001) * (s ^ 2 * Real.exp (-(a * L))) := by ring
      _ ≤ (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001) * (1214 * Λ ^ 2 * E) := by gcongr
      _ = _ := by ring
  -- the junk terms
  have hL17 : L ^ 17 = s ^ 34 := by rw [← hs2]; ring
  have hes : Real.exp (-s) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
  have hB : 2 * GLam Λ (2 * s) * (L ^ 17 * 76 ^ 19 * 3 * Real.exp (-(19 * s)) /
      Real.exp (2 * s)) ≤ Real.exp (-s) := by
    have e2 : Real.exp (-(19 * s)) / Real.exp (2 * s) ≤ Real.exp (-(19 * s)) :=
      div_le_self (Real.exp_pos _).le (Real.one_le_exp (by linarith))
    calc 2 * GLam Λ (2 * s) * (L ^ 17 * 76 ^ 19 * 3 * Real.exp (-(19 * s)) / Real.exp (2 * s))
        = 2 * GLam Λ (2 * s) * (L ^ 17 * 76 ^ 19 * 3) * (Real.exp (-(19 * s)) /
            Real.exp (2 * s)) := by ring
      _ ≤ 2 * (800.04 * s) * (s ^ 34 * 76 ^ 19 * 3) * Real.exp (-(19 * s)) := by
          rw [hL17]; gcongr
      _ = (2 * 800.04 * 76 ^ 19 * 3) * s ^ 35 * Real.exp (-(19 * s)) := by ring
      _ ≤ _ := junk_le (by linarith) (by norm_num)
  have hC : (1.5 * Real.log L + 8) * (2 * (L ^ 17 * 76 ^ 19 * 3 / 19 *
      Real.exp (-(19 * s)))) ≤ Real.exp (-s) := by
    have hlogL : Real.log L = 2 * Real.log s := by rw [← hs2, Real.log_pow]; norm_num
    have hlog0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    calc (1.5 * Real.log L + 8) * (2 * (L ^ 17 * 76 ^ 19 * 3 / 19 * Real.exp (-(19 * s))))
        ≤ (4 * s) * (2 * (s ^ 34 * 76 ^ 19 * 3 / 19 * Real.exp (-(19 * s)))) := by
          rw [hL17]; gcongr; rw [hlogL]; linarith
      _ = (4 * 2 * 76 ^ 19 * 3 / 19) * s ^ 35 * Real.exp (-(19 * s)) := by ring
      _ ≤ _ := junk_le (by linarith) (by norm_num)
  have hS1 : 10 / Real.exp s = 10 * Real.exp (-s) := by rw [Real.exp_neg]; ring
  have hS2 : Real.exp ((θ' - 1) * L) ≤ Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    rw [← hs2]
    have h1 : (θ' - 1) * s ^ 2 ≤ -0.49 * s ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
    have h2 : s ≤ 0.49 * s ^ 2 := by
      have : s * 1 ≤ s * (0.49 * s) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
      linarith [show s * (0.49 * s) = 0.49 * s ^ 2 by ring]
    linarith
  have hfin : (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) / 6.283184 + 2012 ≤
      (2.71828 : ℝ) ^ 97 := by norm_num
  have h97 := exp_97_ge
  have hAA := mul_le_mul_of_nonneg_left hA hpi0.le
  have hAA' : 1 / (2 * π) * ((800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) * Λ ^ 2 * E) ≤
      (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) / 6.283184 * Λ ^ 2 * E := by
    have h0 : 0 ≤ (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) * Λ ^ 2 * E := by positivity
    calc _ ≤ 1 / 6.283184 * ((800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) * Λ ^ 2 * E) :=
          mul_le_mul_of_nonneg_right hpi h0
      _ = _ := by ring
  have hBC := mul_le_mul_of_nonneg_left (add_le_add hB hC) hpi0.le
  have hBC' : 1 / (2 * π) * (Real.exp (-s) + Real.exp (-s)) ≤ 2 * Real.exp (-s) := by
    have h0 : 0 ≤ Real.exp (-s) + Real.exp (-s) := by positivity
    calc _ ≤ 1 * (Real.exp (-s) + Real.exp (-s)) := mul_le_mul_of_nonneg_right hpi1 h0
      _ = _ := by ring
  have hEΛ : Real.exp (-s) ≤ Λ ^ 2 * E := hes.trans (le_mul_of_one_le_left hE0.le hΛ2)
  have hfinal : (800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) / 6.283184 * Λ ^ 2 * E +
      2012 * (Λ ^ 2 * E) ≤ Real.exp 97 * Λ ^ 2 * E := by
    have h0 : 0 ≤ Λ ^ 2 * E := by positivity
    have := mul_le_mul_of_nonneg_right (hfin.trans h97) h0
    calc _ = ((800.04 * 76 ^ 19 * 1.0001 * 4 * 2.001 * 1214) / 6.283184 + 2012) * (Λ ^ 2 * E) :=
          by ring
      _ ≤ _ := this
      _ = _ := by ring
  rw [hS1, mul_add (1 / (2 * π)) (_ + _) _, mul_add (1 / (2 * π))]
  linarith
end Num9

end LocalPNT

end
