module

public import RequestProject.Beurling.Noise.MarginPoint

/-!
# Proposition 5.38, Step 6: the relations of (a) and the range (c)

* `Margin.Var.Bavg_le_add_var` : `(Bm)(t) ≤ m(t) + v(t)` when `|m(y) - m(t)| ≤ v(t)` on the window
  `W_t` (the paper's `v(t) = sup_{|h| ≤ 1.01H(t)} |m(t+h) - m(t)|` covers `|h| ≤ H(t)/2`); this is
  `m ≥ Bm - v` of Step 6(a), the input `hm` of `Margin.prop_5_38_a`;
* `Margin.Var.Bm_ge` : from `M = Bm + B NT_pt + ϑ/H`, `|B NT_pt| ≤ 54η` and `|ϑ| ≤ 6`:
  `Bm ≥ M - 54η - 6/H` (the input `hB`, in the `log t` scaling);
* `Margin.Var.prop_5_38_a_of` : Proposition 5.38(a) at a point, from the two relations above,
  Theorem 5.37, the variation bound of Steps 1–5 and the sizes of the error terms;
* `Margin.Var.prop_5_38_c_low`, `prop_5_38_c_high` : **Proposition 5.38(c)**, Step 6(c), the
  arithmetic: on `[X₀, 2X₀⁻)`, `m = T' ≥ (0.99 - 10⁻⁹)/log t`; on `[2X₀⁻, 2X₀)`,
  `m = T' - ½ρ̃(t/2)` with `ρ̃(t/2) ≤ 0.5001/Λ` and `log t ≤ Λ + 0.7`; so `m log t ≥ 0.739`.
  The inputs (`(huxley)` with Lemma 5.36(a), and the slot count `ρ̃(t/2) ≤ 0.5001/Λ`) are
  hypotheses.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace Margin.Var

/-- `m ≥ Bm - v` (Step 6(a)): `(Bm)(t) ≤ m(t) + v(t)` if `|m(y) - m(t)| ≤ v(t)` on `W_t`. -/
theorem Bavg_le_add_var {H t vt : ℝ} {m : ℝ → ℝ} (hH : 0 < H)
    (hm : IntervalIntegrable m volume (t - H / 2) (t + H / 2))
    (hvar : ∀ y, t - H / 2 ≤ y → y ≤ t + H / 2 → |m y - m t| ≤ vt) :
    Bavg H m t ≤ m t + vt := by
  have hc : IntervalIntegrable (fun _ : ℝ => m t + vt) volume (t - H / 2) (t + H / 2) :=
    _root_.intervalIntegrable_const
  have h := Bavg_mono hH hm hc fun y hy1 hy2 => by
    have := hvar y hy1 hy2
    linarith [le_abs_self (m y - m t)]
  rwa [Bavg_const hH] at h

/-- `Bm ≥ M - 54η - 6/H` (Step 6(a)), multiplied by `log t ≥ 0`. -/
theorem Bm_ge {M Bm BNT ϑ H η lt sη : ℝ} (hH : 0 < H) (hlt : 0 ≤ lt)
    (hdec : M = Bm + BNT + ϑ / H) (hBNT : |BNT| ≤ 54 * η) (hϑ : |ϑ| ≤ 6)
    (hsη : lt * η ≤ sη) :
    lt * M - 54 * sη - 6 * lt / H ≤ lt * Bm := by
  have h1 : BNT ≤ 54 * η := (le_abs_self _).trans hBNT
  have h2 : ϑ / H ≤ 6 / H := div_le_div_of_nonneg_right ((le_abs_self _).trans hϑ) hH.le
  have h3 : lt * BNT ≤ 54 * sη := by nlinarith [mul_le_mul_of_nonneg_left h1 hlt]
  have h4 : lt * (ϑ / H) ≤ 6 * lt / H := by
    have := mul_le_mul_of_nonneg_left h2 hlt
    linarith [show lt * (6 / H) = 6 * lt / H by ring]
  rw [hdec]; nlinarith

/-- **Proposition 5.38(a)** at a point `t` (Step 6(a)), from: the window bound
`|m(y) - m(t)| ≤ v(t)` on `W_t`; the variation bound `v(t) log t ≤ 6.5 E_S + V_{X₀}(t)`
(Steps 1–5); the decomposition `M = Bm + B_t`, `B_t = B NT_pt + ϑ/H`, with
`|B_t| ≤ 54η + 6/H` (from `|B NT_pt| ≤ 54η`, `|ϑ| ≤ 6`, cf. `Bm_ge`);
Theorem 5.37 with `c_sh = 0.97`; and the sizes of the error terms. -/
theorem prop_5_38_a_of {H t vt M Bt η sη o epsN EBR j ES V : ℝ} {m : ℝ → ℝ} (hH : 0 < H)
    (ht : 1 < t) (hm : IntervalIntegrable m volume (t - H / 2) (t + H / 2))
    (hvar : ∀ y, t - H / 2 ≤ y → y ≤ t + H / 2 → |m y - m t| ≤ vt)
    (hv : vt * Real.log t ≤ 6.5 * ES + V)
    (hdec : M = Bavg H m t + Bt) (hBt : |Bt| ≤ 54 * η + 6 / H)
    (hsη : Real.log t * η ≤ sη)
    (hM : 0.97 - o - epsN - EBR - j ≤ Real.log t * M)
    (hsmall : o + epsN + EBR + j + 54 * sη + 6 * Real.log t / H + 6.5 * ES + V ≤ 0.01) :
    0.96 ≤ m t * Real.log t := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have hB := Bavg_le_add_var hH hm hvar
  have h1 : Bt ≤ 54 * η + 6 / H := (le_abs_self Bt).trans hBt
  have h2 : Real.log t * Bt ≤ 54 * sη + 6 * Real.log t / H := by
    have := mul_le_mul_of_nonneg_left h1 hlt.le
    have e : Real.log t * (54 * η + 6 / H) = 54 * (Real.log t * η) + 6 * Real.log t / H := by
      ring
    nlinarith
  have h3 : Real.log t * Bavg H m t ≤ Real.log t * m t + Real.log t * vt := by
    nlinarith [mul_le_mul_of_nonneg_left hB hlt.le]
  rw [hdec] at hM
  nlinarith

/-- **Proposition 5.38(c)** on `[X₀, 2X₀⁻)`: `m = T' = 1 - ρ_det ≥ (0.99 - 10⁻⁹)/log t`. -/
theorem prop_5_38_c_low {mt Tp lt : ℝ} (hlt : 0 < lt) (hm : mt = Tp)
    (hT : (0.99 - 1 / 10 ^ 9) / lt ≤ Tp) : 0.73 ≤ mt * lt := by
  rw [hm]
  have := mul_le_mul_of_nonneg_right hT hlt.le
  rw [div_mul_cancel₀ _ hlt.ne'] at this
  linarith

/-- **Proposition 5.38(c)** on `[2X₀⁻, 2X₀)`: `m = T' - ½ ρ̃(t/2)` with
`T' ≥ (0.99 - 10⁻⁹)/log t`, `0 ≤ ρ̃(t/2) ≤ 0.5001/Λ`, `log t ≤ Λ + 0.7`, `Λ ≥ 10⁸`:
`m log t ≥ 0.99 - 0.2501(1 + 0.7/Λ) - 10⁻⁹ ≥ 0.739`. -/
theorem prop_5_38_c_high {mt Tp rt lt Λ : ℝ} (hlt : 0 < lt) (hΛ : 100000000 ≤ Λ)
    (hm : mt = Tp - rt / 2) (hT : (0.99 - 1 / 10 ^ 9) / lt ≤ Tp) (hr : rt ≤ 0.5001 / Λ)
    (hl : lt ≤ Λ + 0.7) : 0.739 ≤ mt * lt := by
  rw [hm]
  have hΛ0 : 0 < Λ := by linarith
  have h1 := mul_le_mul_of_nonneg_right hT hlt.le
  rw [div_mul_cancel₀ _ hlt.ne'] at h1
  have h2 : rt * lt ≤ 0.5001 / Λ * (Λ + 0.7) := by
    rcases le_or_gt rt 0 with h0 | h0
    · have : rt * lt ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hlt.le
      have : 0 ≤ 0.5001 / Λ * (Λ + 0.7) := by positivity
      linarith
    · exact mul_le_mul hr hl hlt.le (by positivity)
  have h3 : 0.5001 / Λ * (Λ + 0.7) ≤ 0.50011 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hΛ0]; nlinarith
  nlinarith

end Margin.Var

end
