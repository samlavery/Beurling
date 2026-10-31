module

public import Mathlib

/-!
# The θ-free absorption window `h` (Section 2.2, parameter row "window h")

With `Λ = log X₀`, `L = log u` and `ℓ = log L`, the window of the absorbed set is

  `h(u) = u^{1/8}`                                   for `L ≤ 400Λ²`,
  `log h(u) = max(50Λ², 27Λℓ², 120ℓ⁴/log ℓ)`          for `L ≥ 400Λ²`.

Here `log h = winLog Λ L := min(L/8, G(max(L, 400Λ²)))` with `G = winG Λ`
(`winLog_eq_left`, `winLog_eq_right` give the two pieces), and `winH X₀ u = exp(winLog Λ (log u))`.

* `winH_le_rpow`, `winH_one_le`, `winH_pos`: `1 ≤ h(u) ≤ u^{1/8}` (for `u ≥ 1`);
* `winH_monotoneOn`, `winH_continuousOn`: `h` is non-decreasing and continuous on `(0, ∞)`;
* `winH_ratio`: `h(v) ≤ h(u) (v/u)^{1/8}` for `0 < u ≤ v` (the slope `d log h/d log u ≤ 1/8`);
* `winH_isWin`: these properties, bundled as `IsWin`;
* `winH_le_rpow_eps`: `h(x) ≤ C x^ε` for every `ε > 0` (so `h = x^{o(1)}`).
-/

@[expose] public section

open Real Set Filter

namespace Absorbed

/-- `G(L) = max(50Λ², 27Λℓ², 120ℓ⁴/log ℓ)`, `ℓ = log L`. -/
noncomputable def winG (Λ L : ℝ) : ℝ :=
  max (50 * Λ ^ 2) (max (27 * Λ * Real.log L ^ 2) (120 * Real.log L ^ 4 / Real.log (Real.log L)))

/-- `log h` as a function of `L = log u`: `min(L/8, G(max(L, 400Λ²)))`. -/
noncomputable def winLog (Λ L : ℝ) : ℝ := min (L / 8) (winG Λ (max L (400 * Λ ^ 2)))

/-- **The absorption window** `h(u) = exp(winLog (log X₀) (log u))`. -/
noncomputable def winH (X₀ : ℝ) (u : ℝ) : ℝ := Real.exp (winLog (Real.log X₀) (Real.log u))

/-- The properties of a window function used by the absorbed part of the target: on `(0, ∞)`,
`h > 0`, `h` is continuous and non-decreasing, `h(u) ≤ u^{1/8}`, `h ≥ 1` on `[1, ∞)` and
`h(v) ≤ h(u) (v/u)^{1/8}` for `u ≤ v`. -/
structure IsWin (h : ℝ → ℝ) : Prop where
  pos : ∀ v, 0 < v → 0 < h v
  one_le : ∀ v, 1 ≤ v → 1 ≤ h v
  le_rpow : ∀ v, 0 < v → h v ≤ v ^ (1 / 8 : ℝ)
  mono : MonotoneOn h (Ioi 0)
  ratio : ∀ u v, 0 < u → u ≤ v → h v ≤ h u * (v / u) ^ (1 / 8 : ℝ)
  cont : ContinuousOn h (Ioi 0)

namespace IsWin

variable {h : ℝ → ℝ} (hw : IsWin h)
include hw

lemma le_self {v : ℝ} (hv : 1 ≤ v) : h v ≤ v := by
  refine (hw.le_rpow v (by linarith)).trans ?_
  simpa using Real.rpow_le_rpow_of_exponent_le hv (show (1 / 8 : ℝ) ≤ 1 by norm_num)

lemma nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ h v := (hw.pos v hv).le

lemma mono' {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : h u ≤ h v :=
  hw.mono hu (lt_of_lt_of_le hu huv) huv

/-- `h(u)/h(v) ≥ (u/v)^{1/8}` for `0 < u ≤ v`. -/
lemma ratio' {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (u / v) ^ (1 / 8 : ℝ) * h v ≤ h u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1 := hw.ratio u v hu huv
  have e : (u / v) ^ (1 / 8 : ℝ) * (v / u) ^ (1 / 8 : ℝ) = 1 := by
    rw [← Real.mul_rpow (div_pos hu hv).le (div_pos hv hu).le,
      show u / v * (v / u) = 1 by field_simp, Real.one_rpow]
  have hp : 0 ≤ (u / v) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (div_pos hu hv).le _
  calc (u / v) ^ (1 / 8 : ℝ) * h v ≤ (u / v) ^ (1 / 8 : ℝ) * (h u * (v / u) ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hp
    _ = h u * ((u / v) ^ (1 / 8 : ℝ) * (v / u) ^ (1 / 8 : ℝ)) := by ring
    _ = h u := by rw [e, mul_one]

end IsWin

/-! ### The pieces of `G` -/

section pieces

variable {Λ : ℝ}

/-- `ℓ ↦ ℓ⁴/log ℓ` has derivative `ℓ³(4 log ℓ - 1)/(log ℓ)²` for `ℓ > 1`. -/
lemma hasDerivAt_pow4_div_log {ℓ : ℝ} (hℓ : 1 < ℓ) :
    HasDerivAt (fun t : ℝ => t ^ 4 / Real.log t)
      ((4 * ℓ ^ 3 * Real.log ℓ - ℓ ^ 4 * ℓ⁻¹) / Real.log ℓ ^ 2) ℓ := by
  have hl : Real.log ℓ ≠ 0 := (Real.log_pos hℓ).ne'
  have h1 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * ℓ ^ 3) ℓ := by
    simpa using hasDerivAt_pow 4 ℓ
  have h2 : HasDerivAt Real.log ℓ⁻¹ ℓ := Real.hasDerivAt_log (by linarith)
  convert h1.div h2 hl using 1

/-- `ℓ ↦ ℓ⁴/log ℓ` is non-decreasing on `[2, ∞)`. -/
lemma monotoneOn_pow4_div_log : MonotoneOn (fun t : ℝ => t ^ 4 / Real.log t) (Ici 2) := by
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine monotoneOn_of_deriv_nonneg (convex_Ici 2) ?_ ?_ ?_
  · intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    exact ((continuousAt_id.pow 4).div (Real.continuousAt_log (by linarith)) hl).continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hasDerivAt_pow4_div_log (by linarith [ht.out])).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht2 : (2 : ℝ) < t := ht
    rw [(hasDerivAt_pow4_div_log (by linarith)).deriv]
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2.le
    have ht0 : 0 < t := by linarith
    apply div_nonneg _ (sq_nonneg _)
    have e : t ^ 4 * t⁻¹ = t ^ 3 := by field_simp
    rw [e]
    have : 0 < t ^ 3 := by positivity
    nlinarith

/-- `L ↦ ℓ⁴/log ℓ` (`ℓ = log L`) has derivative `ℓ³(4 log ℓ - 1)/((log ℓ)² L)` for `L > e`. -/
lemma hasDerivAt_G2 {L : ℝ} (hL : Real.exp 1 < L) :
    HasDerivAt (fun t : ℝ => Real.log t ^ 4 / Real.log (Real.log t))
      ((4 * Real.log L ^ 3 * Real.log (Real.log L) - Real.log L ^ 4 * (Real.log L)⁻¹) /
        Real.log (Real.log L) ^ 2 * L⁻¹) L := by
  have hL0 : 0 < L := lt_trans (Real.exp_pos 1) hL
  have hl1 : 1 < Real.log L := by
    rw [Real.lt_log_iff_exp_lt hL0]; exact hL
  have h1 := hasDerivAt_pow4_div_log hl1
  have h2 : HasDerivAt Real.log L⁻¹ L := Real.hasDerivAt_log hL0.ne'
  exact h1.comp L h2

lemma exp_one_lt_of {L : ℝ} (hL : 100 ≤ L) : Real.exp 1 < L := by
  have := Real.exp_one_lt_d9; linarith

/-- `ℓ = log L ≤ 8 L^{1/8}`, as `log L ≤ q` with `q⁸ = L`... in the form `ℓ ≤ 8q`. -/
lemma log_le_eight_mul {L : ℝ} (hL : 0 < L) : Real.log L ≤ 8 * L ^ (1 / 8 : ℝ) := by
  have := Real.log_le_rpow_div hL.le (show (0 : ℝ) < 1 / 8 by norm_num)
  linarith

lemma log_le_four_mul {L : ℝ} (hL : 0 < L) : Real.log L ≤ 4 * L ^ (1 / 4 : ℝ) := by
  have := Real.log_le_rpow_div hL.le (show (0 : ℝ) < 1 / 4 by norm_num)
  linarith

/-- `27Λ(log L)² ≤ ...`: the slope of `27Λℓ²` is `54Λℓ/L ≤ 1/8` on `[400Λ², ∞)`. -/
lemma slope_G1 (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : 400 * Λ ^ 2 ≤ L) :
    54 * Λ * Real.log L / L ≤ 1 / 8 := by
  have hΛ0 : 0 < Λ := by linarith
  have hL0 : 0 < L := by nlinarith
  set q := L ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hL0 _
  have hq4 : q ^ 4 = L := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlog := log_le_four_mul hL0
  rw [← hq] at hlog
  -- `q² ≥ 20Λ` and `q ≥ 100`
  have hq2 : 20 * Λ ≤ q ^ 2 := by nlinarith [sq_nonneg (q ^ 2 - 20 * Λ), sq_nonneg (q ^ 2 + 20 * Λ)]
  have hq100 : 100 ≤ q := by nlinarith
  rw [div_le_iff₀ hL0]
  have : 54 * Λ * (4 * q) ≤ 1 / 8 * q ^ 4 := by nlinarith
  nlinarith

lemma slope_G2 {L : ℝ} (hL : 10 ^ 18 ≤ L) :
    480 * Real.log L ^ 3 / L ≤ 1 / 8 := by
  have hL0 : 0 < L := by linarith
  set q := L ^ (1 / 8 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hL0 _
  have hq8 : q ^ 8 = L := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlog := log_le_eight_mul hL0
  rw [← hq] at hlog
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hq100 : 100 ≤ q := by
    by_contra hc; push_neg at hc
    have : q ^ 8 < 100 ^ 8 := pow_lt_pow_left₀ hc hq0.le (by norm_num)
    nlinarith
  rw [div_le_iff₀ hL0]
  have h3 : Real.log L ^ 3 ≤ (8 * q) ^ 3 := pow_le_pow_left₀ hl0 hlog 3
  have : 480 * (8 * q) ^ 3 ≤ 1 / 8 * q ^ 8 := by
    have h5 : (100 : ℝ) ^ 5 ≤ q ^ 5 := pow_le_pow_left₀ (by norm_num) hq100 5
    have e : q ^ 8 = q ^ 5 * q ^ 3 := by ring
    have : 0 < q ^ 3 := by positivity
    rw [e]; nlinarith
  nlinarith

/-- `L/8 - 27Λ(log L)²` is non-decreasing on `[400Λ², ∞)`. -/
lemma monotoneOn_sub_G1 (hΛ : 10 ^ 8 ≤ Λ) :
    MonotoneOn (fun L : ℝ => L / 8 - 27 * Λ * Real.log L ^ 2) (Ici (400 * Λ ^ 2)) := by
  have hL0 : ∀ L ∈ Ici (400 * Λ ^ 2), 0 < L := fun L hL => by
    have : (0 : ℝ) < 400 * Λ ^ 2 := by positivity
    exact lt_of_lt_of_le this hL
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · intro L hL
    exact ((continuousAt_id.div_const 8).sub (continuousAt_const.mul
      ((Real.continuousAt_log (hL0 L hL).ne').pow 2))).continuousWithinAt
  · intro L hL
    rw [interior_Ici] at hL
    have hL' : 0 < L := hL0 L (mem_Ici.mpr hL.out.le)
    exact (((differentiableAt_id.div_const 8).sub (differentiableAt_const _ |>.mul
      ((Real.differentiableAt_log hL'.ne').pow 2)))).differentiableWithinAt
  · intro L hL
    rw [interior_Ici] at hL
    have hL' : 0 < L := hL0 L (mem_Ici.mpr hL.out.le)
    have hd : HasDerivAt (fun L : ℝ => L / 8 - 27 * Λ * Real.log L ^ 2)
        (1 / 8 - 27 * Λ * (2 * Real.log L * L⁻¹)) L := by
      have h1 : HasDerivAt (fun L : ℝ => L / 8) (1 / 8) L := by
        simpa using (hasDerivAt_id L).div_const 8
      have h2 : HasDerivAt (fun L : ℝ => Real.log L ^ 2) (2 * Real.log L * L⁻¹) L := by
        have := (Real.hasDerivAt_log hL'.ne').pow 2
        convert this using 1; push_cast; ring
      exact h1.sub (h2.const_mul _)
    rw [hd.deriv]
    have := slope_G1 hΛ hL.out.le
    have e : 27 * Λ * (2 * Real.log L * L⁻¹) = 54 * Λ * Real.log L / L := by
      field_simp; ring
    linarith

/-- `L/8 - 120ℓ⁴/log ℓ` is non-decreasing on `[400Λ², ∞)`. -/
lemma monotoneOn_sub_G2 (hΛ : 10 ^ 8 ≤ Λ) :
    MonotoneOn (fun L : ℝ => L / 8 - 120 * (Real.log L ^ 4 / Real.log (Real.log L)))
      (Ici (400 * Λ ^ 2)) := by
  have hL18 : ∀ L ∈ Ici (400 * Λ ^ 2), 10 ^ 18 ≤ L := fun L hL => by
    have : (10 : ℝ) ^ 18 ≤ 400 * Λ ^ 2 := by nlinarith
    exact this.trans hL
  have hfull : ∀ L : ℝ, 10 ^ 18 ≤ L →
      HasDerivAt (fun L : ℝ => L / 8 - 120 * (Real.log L ^ 4 / Real.log (Real.log L)))
        (1 / 8 - 120 * ((4 * Real.log L ^ 3 * Real.log (Real.log L) -
          Real.log L ^ 4 * (Real.log L)⁻¹) / Real.log (Real.log L) ^ 2 * L⁻¹)) L := by
    intro L hL
    have hd := hasDerivAt_G2 (exp_one_lt_of (by linarith))
    have h1 : HasDerivAt (fun L : ℝ => L / 8) (1 / 8) L := by
      simpa using (hasDerivAt_id L).div_const 8
    exact h1.sub (hd.const_mul 120)
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · intro L hL
    exact (hfull L (hL18 L hL)).continuousAt.continuousWithinAt
  · intro L hL
    rw [interior_Ici] at hL
    exact (hfull L (hL18 L (mem_Ici.mpr hL.out.le))).differentiableAt.differentiableWithinAt
  · intro L hL
    rw [interior_Ici] at hL
    have hL1 := hL18 L (mem_Ici.mpr hL.out.le)
    rw [(hfull L hL1).deriv]
    have hL0 : 0 < L := by linarith
    set ℓ := Real.log L with hℓ
    have hℓ40 : 40 ≤ ℓ := by
      rw [hℓ, Real.le_log_iff_exp_le hL0]
      have : Real.exp 40 ≤ 10 ^ 18 := by
        have h := Real.exp_one_lt_d9
        have e : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc Real.exp 1 ^ 40 ≤ (2.7182818286 : ℝ) ^ 40 :=
              pow_le_pow_left₀ (Real.exp_pos 1).le h.le 40
          _ ≤ 10 ^ 18 := by norm_num
      linarith
    have hlℓ : 1 ≤ Real.log ℓ := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hs := slope_G2 hL1
    rw [← hℓ] at hs
    -- the derivative of `ℓ⁴/log ℓ` in `L` is at most `4ℓ³/L`
    have hℓ0 : 0 < ℓ := by linarith
    have hnum : 4 * ℓ ^ 3 * Real.log ℓ - ℓ ^ 4 * ℓ⁻¹ ≤ 4 * ℓ ^ 3 * Real.log ℓ := by
      have : 0 ≤ ℓ ^ 4 * ℓ⁻¹ := by positivity
      linarith
    have hden : Real.log ℓ ≤ Real.log ℓ ^ 2 := by nlinarith
    have hd2 : (4 * ℓ ^ 3 * Real.log ℓ - ℓ ^ 4 * ℓ⁻¹) / Real.log ℓ ^ 2 * L⁻¹ ≤ 4 * ℓ ^ 3 / L := by
      have hlp : 0 < Real.log ℓ := by linarith
      have hA : (4 * ℓ ^ 3 * Real.log ℓ - ℓ ^ 4 * ℓ⁻¹) / Real.log ℓ ^ 2 ≤ 4 * ℓ ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        have : 4 * ℓ ^ 3 * Real.log ℓ ≤ 4 * ℓ ^ 3 * Real.log ℓ ^ 2 :=
          mul_le_mul_of_nonneg_left hden (by positivity)
        linarith
      rw [div_eq_mul_inv (4 * ℓ ^ 3)]
      exact mul_le_mul_of_nonneg_right hA (inv_nonneg.mpr hL0.le)
    have : 120 * (4 * ℓ ^ 3 / L) = 480 * ℓ ^ 3 / L := by ring
    nlinarith

/-- `27Λℓ²` is non-decreasing on `[1, ∞)`. -/
lemma monotoneOn_G1 (hΛ : 0 ≤ Λ) :
    MonotoneOn (fun L : ℝ => 27 * Λ * Real.log L ^ 2) (Ici 1) := by
  intro a ha b hb hab
  have ha1 : (1 : ℝ) ≤ a := ha
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have h0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have := pow_le_pow_left₀ h0 h1 2
  simp only
  nlinarith

/-- `120ℓ⁴/log ℓ` is non-decreasing on `[e², ∞)`. -/
lemma monotoneOn_G2 :
    MonotoneOn (fun L : ℝ => 120 * (Real.log L ^ 4 / Real.log (Real.log L)))
      (Ici (Real.exp 2)) := by
  intro a ha b hb hab
  have ha2 : Real.exp 2 ≤ a := ha
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 2) ha2
  have hla : 2 ≤ Real.log a := by rw [Real.le_log_iff_exp_le ha0]; exact ha2
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have := monotoneOn_pow4_div_log (mem_Ici.mpr hla) (mem_Ici.mpr (hla.trans hlab)) hlab
  simp only at this ⊢
  linarith

end pieces

/-! ### `G` and `winLog` -/

section G

variable {Λ : ℝ}

lemma L0_pos (hΛ : 10 ^ 8 ≤ Λ) : 0 < 400 * Λ ^ 2 := by positivity

lemma L0_ge (hΛ : 10 ^ 8 ≤ Λ) : 10 ^ 8 ≤ 400 * Λ ^ 2 := by nlinarith

/-- At `L₀ = 400Λ²` the maximum in `G` is `50Λ²`. -/
lemma winG_L0 (hΛ : 10 ^ 8 ≤ Λ) : winG Λ (400 * Λ ^ 2) = 50 * Λ ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  set L₀ := 400 * Λ ^ 2 with hL₀
  have hL₀0 : 0 < L₀ := L0_pos hΛ
  set ℓ := Real.log L₀ with hℓ
  -- `ℓ ≤ 8 q` with `q⁸ = L₀`, so `q⁴ = 20Λ` and `q² ≤ Λ/1000`
  have hl := log_le_eight_mul hL₀0
  rw [← hℓ] at hl
  set q := L₀ ^ (1 / 8 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hL₀0 _
  have hq8 : q ^ 8 = L₀ := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hL₀0.le]; norm_num
  have hΛ2 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
  have hq4 : q ^ 4 = 20 * Λ := by
    have e : (q ^ 4) ^ 2 = (20 * Λ) ^ 2 := by rw [← pow_mul, hq8, hL₀]; ring
    have h0 : 0 ≤ q ^ 4 := by positivity
    have h1 : 0 ≤ 20 * Λ := by positivity
    nlinarith [sq_nonneg (q ^ 4 - 20 * Λ), sq_nonneg (q ^ 4 + 20 * Λ)]
  have hq2 : q ^ 2 ≤ Λ / 1000 := by
    have e : (q ^ 2) ^ 2 = 20 * Λ := by rw [← pow_mul]; exact hq4
    nlinarith [sq_nonneg (q ^ 2 - Λ / 1000), sq_nonneg q]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hL₀0]
    have := Real.exp_one_lt_d9; rw [hL₀]; nlinarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h40 : (40 : ℝ) ≤ ℓ := by
      rw [hℓ, Real.le_log_iff_exp_le hL₀0]
      have : Real.exp 40 ≤ 10 ^ 18 := by
        have h := Real.exp_one_lt_d9
        have e : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        calc Real.exp 1 ^ 40 ≤ (2.7182818286 : ℝ) ^ 40 :=
              pow_le_pow_left₀ (Real.exp_pos 1).le h.le 40
          _ ≤ 10 ^ 18 := by norm_num
      have : (10 : ℝ) ^ 18 ≤ L₀ := by rw [hL₀]; nlinarith
      linarith
    have := Real.exp_one_lt_d9; linarith
  have hsq : ℓ ^ 2 ≤ 64 * q ^ 2 := by nlinarith
  have h1 : 27 * Λ * ℓ ^ 2 ≤ 50 * Λ ^ 2 := by
    have : ℓ ^ 2 ≤ 64 * (Λ / 1000) := by linarith
    nlinarith
  have h2 : 120 * ℓ ^ 4 / Real.log ℓ ≤ 50 * Λ ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : ℓ ^ 4 ≤ 4096 * (20 * Λ) := by
      have e : ℓ ^ 4 = (ℓ ^ 2) ^ 2 := by ring
      have : (ℓ ^ 2) ^ 2 ≤ (64 * q ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hsq 2
      have e2 : (64 * q ^ 2) ^ 2 = 4096 * q ^ 4 := by ring
      rw [e, ← hq4]; linarith
    nlinarith
  unfold winG
  rw [← hℓ, max_eq_left (max_le h1 h2)]

/-- `G(L) ≤ L/8` for `L ≥ 400Λ²` (from `G(L₀) = L₀/8` and the slopes `≤ 1/8`). -/
lemma winG_le (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : 400 * Λ ^ 2 ≤ L) : winG Λ L ≤ L / 8 := by
  have hL₀ := mem_Ici.mpr (le_refl (400 * Λ ^ 2))
  have hLm := mem_Ici.mpr hL
  have h0 := winG_L0 hΛ
  unfold winG at h0 ⊢
  have hA := max_le_iff.mp (le_of_eq h0)
  have hB := max_le_iff.mp hA.2
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · have := monotoneOn_sub_G1 hΛ hL₀ hLm hL
    simp only at this
    nlinarith
  · have := monotoneOn_sub_G2 hΛ hL₀ hLm hL
    simp only at this
    have e : 120 * Real.log (400 * Λ ^ 2) ^ 4 / Real.log (Real.log (400 * Λ ^ 2)) =
        120 * (Real.log (400 * Λ ^ 2) ^ 4 / Real.log (Real.log (400 * Λ ^ 2))) := by ring
    have e' : 120 * Real.log L ^ 4 / Real.log (Real.log L) =
        120 * (Real.log L ^ 4 / Real.log (Real.log L)) := by ring
    rw [e'] ; rw [e] at hB
    nlinarith

/-- `G` is non-decreasing on `[400Λ², ∞)`. -/
lemma winG_mono (hΛ : 10 ^ 8 ≤ Λ) {a b : ℝ} (ha : 400 * Λ ^ 2 ≤ a) (hab : a ≤ b) :
    winG Λ a ≤ winG Λ b := by
  have he2 : Real.exp 2 ≤ a := by
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    nlinarith
  have ha1 : (1 : ℝ) ≤ a := by nlinarith
  unfold winG
  refine max_le_max le_rfl (max_le_max ?_ ?_)
  · exact monotoneOn_G1 (by linarith) (mem_Ici.mpr ha1) (mem_Ici.mpr (ha1.trans hab)) hab
  · have := monotoneOn_G2 (mem_Ici.mpr he2) (mem_Ici.mpr (he2.trans hab)) hab
    simp only at this
    have e : ∀ L : ℝ, 120 * Real.log L ^ 4 / Real.log (Real.log L) =
        120 * (Real.log L ^ 4 / Real.log (Real.log L)) := fun L => by ring
    rw [e, e]; exact this

/-- `L/8 - G(L)` is non-decreasing on `[400Λ², ∞)`. -/
lemma sub_winG_mono (hΛ : 10 ^ 8 ≤ Λ) {a b : ℝ} (ha : 400 * Λ ^ 2 ≤ a) (hab : a ≤ b) :
    a / 8 - winG Λ a ≤ b / 8 - winG Λ b := by
  have hA := mem_Ici.mpr ha
  have hB := mem_Ici.mpr (ha.trans hab)
  have h1 := monotoneOn_sub_G1 hΛ hA hB hab
  have h2 := monotoneOn_sub_G2 hΛ hA hB hab
  simp only at h1 h2
  have e : ∀ L : ℝ, 120 * Real.log L ^ 4 / Real.log (Real.log L) =
      120 * (Real.log L ^ 4 / Real.log (Real.log L)) := fun L => by ring
  unfold winG
  rw [e, e]
  -- `b/8 - max(c, f1 b, f2 b) = min(b/8 - c, b/8 - f1 b, b/8 - f2 b)`
  have key : ∀ (c p q r s t : ℝ), c ≤ s → p ≤ t → q ≤ r →
      (a / 8 - max c (max p q) ≤ b / 8 - max s (max t r)) ∨ True := fun _ _ _ _ _ _ _ _ _ =>
    Or.inr trivial
  clear key
  rcases le_total (50 * Λ ^ 2) (max (27 * Λ * Real.log b ^ 2)
      (120 * (Real.log b ^ 4 / Real.log (Real.log b)))) with hc | hc
  · rw [max_eq_right hc]
    rcases le_total (27 * Λ * Real.log b ^ 2)
        (120 * (Real.log b ^ 4 / Real.log (Real.log b))) with hd | hd
    · rw [max_eq_right hd]
      have : 120 * (Real.log a ^ 4 / Real.log (Real.log a)) ≤
          max (50 * Λ ^ 2) (max (27 * Λ * Real.log a ^ 2)
            (120 * (Real.log a ^ 4 / Real.log (Real.log a)))) :=
        le_max_of_le_right (le_max_right _ _)
      linarith
    · rw [max_eq_left hd]
      have : 27 * Λ * Real.log a ^ 2 ≤
          max (50 * Λ ^ 2) (max (27 * Λ * Real.log a ^ 2)
            (120 * (Real.log a ^ 4 / Real.log (Real.log a)))) :=
        le_max_of_le_right (le_max_left _ _)
      linarith
  · rw [max_eq_left hc]
    have : 50 * Λ ^ 2 ≤
        max (50 * Λ ^ 2) (max (27 * Λ * Real.log a ^ 2)
          (120 * (Real.log a ^ 4 / Real.log (Real.log a)))) := le_max_left _ _
    linarith

/-- The first piece: `log h = L/8` for `L ≤ 400Λ²`. -/
lemma winLog_eq_left (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : L ≤ 400 * Λ ^ 2) : winLog Λ L = L / 8 := by
  unfold winLog
  rw [max_eq_right hL, winG_L0 hΛ]
  exact min_eq_left (by linarith)

/-- The second piece: `log h = max(50Λ², 27Λℓ², 120ℓ⁴/log ℓ)` for `L ≥ 400Λ²`. -/
lemma winLog_eq_right (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : 400 * Λ ^ 2 ≤ L) :
    winLog Λ L = winG Λ L := by
  unfold winLog
  rw [max_eq_left hL]
  exact min_eq_right (winG_le hΛ hL)

lemma winLog_le (Λ L : ℝ) : winLog Λ L ≤ L / 8 := min_le_left _ _

lemma winLog_nonneg (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ winLog Λ L := by
  unfold winLog
  refine le_min (by linarith) ?_
  unfold winG
  exact le_trans (by positivity) (le_max_left _ _)

/-- `winLog` is non-decreasing. -/
lemma winLog_mono (hΛ : 10 ^ 8 ≤ Λ) : Monotone (winLog Λ) := by
  intro a b hab
  unfold winLog
  refine min_le_min (by linarith) (winG_mono hΛ (le_max_right _ _) (max_le_max hab le_rfl))

/-- The slope of `winLog` is at most `1/8`: `winLog b - winLog a ≤ (b - a)/8` for `a ≤ b`. -/
lemma winLog_sub_le (hΛ : 10 ^ 8 ≤ Λ) {a b : ℝ} (hab : a ≤ b) :
    winLog Λ b - winLog Λ a ≤ (b - a) / 8 := by
  -- `L/8 - winLog L = max(0, L/8 - G(max(L, L₀)))` is non-decreasing
  have hφ : ∀ L, L / 8 - winLog Λ L = max 0 (L / 8 - winG Λ (max L (400 * Λ ^ 2))) := by
    intro L; unfold winLog
    rcases le_total (L / 8) (winG Λ (max L (400 * Λ ^ 2))) with h | h
    · rw [min_eq_left h, sub_self]
      exact (max_eq_left (show L / 8 - winG Λ (max L (400 * Λ ^ 2)) ≤ 0 by linarith)).symm
    · rw [min_eq_right h]
      exact (max_eq_right (by linarith : 0 ≤ L / 8 - winG Λ (max L (400 * Λ ^ 2)))).symm
  have hmono : b / 8 - winG Λ (max b (400 * Λ ^ 2)) ≥ a / 8 - winG Λ (max a (400 * Λ ^ 2)) ∨
      a / 8 - winG Λ (max a (400 * Λ ^ 2)) ≤ 0 := by
    rcases le_total a (400 * Λ ^ 2) with ha | ha
    · right
      rw [max_eq_right ha, winG_L0 hΛ]; nlinarith
    · left
      rw [max_eq_left ha, max_eq_left (ha.trans hab)]
      exact sub_winG_mono hΛ ha hab
  have h1 := hφ a
  have h2 := hφ b
  have : a / 8 - winLog Λ a ≤ b / 8 - winLog Λ b := by
    rw [h1, h2]
    rcases hmono with h | h
    · exact max_le_max le_rfl h
    · exact max_le (le_max_left _ _) (h.trans (le_max_left _ _))
  linarith

lemma continuous_winLog (hΛ : 10 ^ 8 ≤ Λ) : Continuous (winLog Λ) := by
  unfold winLog winG
  have hL0 := L0_ge hΛ
  have hm : Continuous fun L : ℝ => max L (400 * Λ ^ 2) := continuous_id.max continuous_const
  have hlog : Continuous fun L : ℝ => Real.log (max L (400 * Λ ^ 2)) :=
    hm.log fun L => by have := le_max_right L (400 * Λ ^ 2); linarith
  have hll : ∀ L : ℝ, 1 < Real.log (max L (400 * Λ ^ 2)) := fun L => by
    have h1 := le_max_right L (400 * Λ ^ 2)
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hloglog : Continuous fun L : ℝ => Real.log (Real.log (max L (400 * Λ ^ 2))) :=
    hlog.log fun L => by linarith [hll L]
  refine (continuous_id.div_const 8).min (continuous_const.max
    ((continuous_const.mul (hlog.pow 2)).max ((continuous_const.mul (hlog.pow 4)).div
      hloglog fun L => (Real.log_pos (hll L)).ne')))

end G

/-! ### The window `h` -/

section H

variable {X₀ : ℝ}

lemma winH_pos (X₀ u : ℝ) : 0 < winH X₀ u := Real.exp_pos _

lemma log_winH (X₀ u : ℝ) : Real.log (winH X₀ u) = winLog (Real.log X₀) (Real.log u) :=
  Real.log_exp _

lemma winH_le_rpow (X₀ : ℝ) {u : ℝ} (hu : 0 < u) : winH X₀ u ≤ u ^ (1 / 8 : ℝ) := by
  unfold winH
  rw [Real.rpow_def_of_pos hu, Real.exp_le_exp]
  have := winLog_le (Real.log X₀) (Real.log u)
  linarith

lemma winH_one_le (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu : 1 ≤ u) : 1 ≤ winH X₀ u :=
  Real.one_le_exp (winLog_nonneg hX (Real.log_nonneg hu))

lemma winH_mono (hX : 10 ^ 8 ≤ Real.log X₀) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    winH X₀ u ≤ winH X₀ v := by
  unfold winH
  exact Real.exp_le_exp.mpr (winLog_mono hX (Real.log_le_log hu huv))

lemma winH_ratio (hX : 10 ^ 8 ≤ Real.log X₀) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    winH X₀ v ≤ winH X₀ u * (v / u) ^ (1 / 8 : ℝ) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  unfold winH
  rw [Real.rpow_def_of_pos (div_pos hv hu), ← Real.exp_add, Real.exp_le_exp,
    Real.log_div hv.ne' hu.ne']
  have := winLog_sub_le hX (Real.log_le_log hu huv)
  linarith

lemma winH_continuousOn (hX : 10 ^ 8 ≤ Real.log X₀) : ContinuousOn (winH X₀) (Ioi 0) := by
  intro u hu
  have hu0 : (u : ℝ) ≠ 0 := (ne_of_gt hu)
  unfold winH
  exact (Real.continuous_exp.continuousAt.comp ((continuous_winLog hX).continuousAt.comp
    (Real.continuousAt_log hu0))).continuousWithinAt

/-- **The window is a window**: `winH X₀` has the properties `IsWin` (for `log X₀ ≥ 10⁸`). -/
theorem winH_isWin (hX : 10 ^ 8 ≤ Real.log X₀) : IsWin (winH X₀) where
  pos _ _ := winH_pos _ _
  one_le _ hv := winH_one_le hX hv
  le_rpow _ hv := winH_le_rpow X₀ hv
  mono _ hu _ hv huv := winH_mono hX hu huv
  ratio _ _ hu huv := winH_ratio hX hu huv
  cont := winH_continuousOn hX

/-- The first piece of the window: `h(u) = u^{1/8}` for `log u ≤ 400Λ²`. -/
lemma winH_eq_rpow (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu : 0 < u)
    (hL : Real.log u ≤ 400 * Real.log X₀ ^ 2) : winH X₀ u = u ^ (1 / 8 : ℝ) := by
  unfold winH
  rw [winLog_eq_left hX hL, Real.rpow_def_of_pos hu]
  congr 1; ring

/-- The second piece of the window: `log h(u) = max(50Λ², 27Λℓ², 120ℓ⁴/log ℓ)` for
`log u ≥ 400Λ²`. -/
lemma log_winH_eq_right (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ}
    (hL : 400 * Real.log X₀ ^ 2 ≤ Real.log u) :
    Real.log (winH X₀ u) = max (50 * Real.log X₀ ^ 2)
      (max (27 * Real.log X₀ * Real.log (Real.log u) ^ 2)
        (120 * Real.log (Real.log u) ^ 4 / Real.log (Real.log (Real.log u)))) := by
  rw [log_winH, winLog_eq_right hX hL]; rfl

/-- `log h ≥ min(L/8, 50Λ²)`, `log h ≥ min(L/8, 27Λℓ²)` and `log h ≥ min(L/8, 120ℓ⁴/log ℓ)`
for `L ≥ 400Λ²` (the lower bounds used in Lemma P). -/
lemma winLog_ge (hΛ : 10 ^ 8 ≤ Λ) {L : ℝ} (hL : 400 * Λ ^ 2 ≤ L) :
    50 * Λ ^ 2 ≤ winLog Λ L ∧ 27 * Λ * Real.log L ^ 2 ≤ winLog Λ L ∧
      120 * Real.log L ^ 4 / Real.log (Real.log L) ≤ winLog Λ L := by
  rw [winLog_eq_right hΛ hL]
  unfold winG
  exact ⟨le_max_left _ _, le_max_of_le_right (le_max_left _ _),
    le_max_of_le_right (le_max_right _ _)⟩

/-- **`h = x^{o(1)}`**: for every `ε > 0` there is `C` with `h(x) ≤ C x^ε` for `x ≥ 1`. -/
theorem winH_le_rpow_eps (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ), winH X₀ x ≤ C * x ^ ε := by
  set Λ := Real.log X₀ with hΛ
  -- `G(L) ≤ εL` for large `L`: each piece is `o(L)`
  have h1 : Tendsto (fun L : ℝ => Real.log L ^ 4 / L) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero
    simpa using this
  have h2 : Tendsto (fun L : ℝ => Real.log L ^ 2 / L) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simpa using this
  have hev1 : ∀ᶠ L in atTop, Real.log L ^ 4 / L ≤ ε / 120 :=
    h1.eventually (ge_mem_nhds (by positivity))
  have hev2 : ∀ᶠ L in atTop, Real.log L ^ 2 / L ≤ ε / (27 * Λ) :=
    h2.eventually (ge_mem_nhds (by positivity))
  obtain ⟨L₁, hL₁⟩ := (hev1.and hev2).exists_forall_of_atTop
  set L₂ := max (max L₁ (400 * Λ ^ 2)) (50 * Λ ^ 2 / ε) with hL₂
  refine ⟨Real.exp (L₂ / 8), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases le_total (Real.log x) L₂ with hle | hge
  · have h3 : winH X₀ x ≤ Real.exp (L₂ / 8) := by
      unfold winH
      exact Real.exp_le_exp.mpr ((winLog_le _ _).trans (by linarith))
    have : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
    nlinarith [Real.exp_pos (L₂ / 8)]
  · -- `log h ≤ ε log x`
    have hL₀ : 400 * Λ ^ 2 ≤ Real.log x :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hge
    have hL1 : L₁ ≤ Real.log x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hge
    have hL3 : 50 * Λ ^ 2 / ε ≤ Real.log x := le_trans (le_max_right _ _) hge
    obtain ⟨hb1, hb2⟩ := hL₁ (Real.log x) hL1
    set L := Real.log x with hL
    have hLpos : 0 < L := by nlinarith
    have hll : 1 ≤ Real.log (Real.log L) := by
      have h40 : Real.exp (Real.exp 1) ≤ L := by
        have e1 := Real.exp_one_lt_d9
        have : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
        have h3 : Real.exp 3 < 21 := by
          have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          rw [e]
          calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
                pow_le_pow_left₀ (Real.exp_pos 1).le e1.le 3
            _ < 21 := by norm_num
        nlinarith
      rw [Real.le_log_iff_exp_le (by
        have := Real.add_one_le_exp (Real.exp 1)
        have h0 : 0 < Real.log L := by
          rw [Real.lt_log_iff_exp_lt hLpos]
          exact lt_of_lt_of_le (Real.exp_lt_exp.mpr (by linarith [Real.exp_pos 1])) h40
        exact h0), Real.le_log_iff_exp_le hLpos]
      exact h40
    have hG : winG Λ L ≤ ε * L := by
      unfold winG
      refine max_le ?_ (max_le ?_ ?_)
      · rw [div_le_iff₀ hε] at hL3; linarith
      · rw [div_le_iff₀ hLpos] at hb2
        have hΛ0 : 0 < Λ := by linarith
        have := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 27 * Λ by positivity)
        have e : 27 * Λ * (ε / (27 * Λ) * L) = ε * L := by field_simp
        nlinarith
      · rw [div_le_iff₀ hLpos] at hb1
        have hl4 : 0 ≤ Real.log L ^ 4 := by positivity
        rw [div_le_iff₀ (by linarith)]
        have : 120 * Real.log L ^ 4 ≤ ε * L := by nlinarith
        have hεL : 0 ≤ ε * L := by positivity
        nlinarith
    have h3 : winH X₀ x ≤ x ^ ε := by
      unfold winH
      rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, winLog_eq_right hX hL₀]
      linarith
    have : 1 ≤ Real.exp (L₂ / 8) := Real.one_le_exp (by
      have : 0 ≤ L₂ := le_trans (by positivity) (le_trans (le_max_right _ _) (le_max_left _ _))
      linarith)
    have := Real.rpow_nonneg hx0.le ε
    nlinarith

end H

end Absorbed

export Absorbed (winH winH_isWin winH_pos winH_le_rpow winH_one_le)

end
