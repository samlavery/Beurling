module

public import RequestProject.Beurling.Noise.MarginCor

/-!
# Theorem 5.37 and Proposition 5.38: the deterministic assembly

* `Margin.thm_5_37` : **Theorem 5.37** (the margin on `H`-windows) from its three inputs, each a
  named hypothesis:
  - (predictable) eq. (predictable) with **Lemma 5.34**: `log x · M(x) ≥ log x · (B R T')(x) - ε_N`;
  - (bridge) **Proposition 5.26** with **Lemma 5.27** and (jX0), at every point `y` of the window
    `W_x = [x - H/2, x + H/2]`: `R T'(y) ≥ ρ^sh(y) - (E_BR + j_{X₀}(x))/log y`;
  - (g1) **Proposition 5.35** at the points of `W_x`, averaged:
    `log x · (B ρ^sh)(x) ≥ c_sh(x) - o(1)`.

  Conclusion: `log x · M(x) ≥ c_sh - o - ε_N - (E_BR + j) · log x/log(x - H/2)`. The factor
  `log x/log(x - H/2) - 1` is the passage from `log y` to `log x` (at most `X₀^{-0.9}`, part of
  the paper's `o(1)`), made explicit in `thm_5_37'`.
* `Margin.prop_5_38_a` : **Proposition 5.38(a)**, Step 6(a): from `m ≥ Bm - v`,
  `Bm ≥ M - 54η - 6/H`, Theorem 5.37 with `c_sh = 0.97`, and the variation bound
  `v(t) log t ≤ 6.5 E_S + V_{X₀}(t)` (Steps 1–5, a named input), with the sizes of the error
  terms, `m(t) log t ≥ 0.96`.
* `Margin.prop_5_38_b` : **Proposition 5.38(b)**, Step 6(b), last bullet: from
  `m(t) log t ≥ ρ^sh(t) log t - j_{X₀}(t) - 10⁻¹²`, `ρ^sh(t) log t ≥ 0.82` (Proposition 5.35(A))
  and `j_{X₀}(t) ≤ 0.4209` (Proposition 5.33), `m(t) log t ≥ 0.399`.
* `Margin.pointwiseMargin_of` : the three ranges (a)–(c) give `PointwiseMargin m X₀`, the input
  of Corollary 5.40.
-/

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace Margin

/-- The output-scale average `(Bg)(x) = H⁻¹ ∫_{x-H/2}^{x+H/2} g` (window of width `H = H(x)`). -/
noncomputable def Bavg (H : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  H⁻¹ * ∫ y in (x - H / 2)..(x + H / 2), g y

lemma Bavg_mono {H : ℝ} (hH : 0 < H) {f g : ℝ → ℝ} {x : ℝ}
    (hf : IntervalIntegrable f volume (x - H / 2) (x + H / 2))
    (hg : IntervalIntegrable g volume (x - H / 2) (x + H / 2))
    (hfg : ∀ y, x - H / 2 ≤ y → y ≤ x + H / 2 → f y ≤ g y) : Bavg H f x ≤ Bavg H g x := by
  unfold Bavg
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hH).le
  exact intervalIntegral.integral_mono_on (by linarith) hf hg fun y hy => hfg y hy.1 hy.2

lemma Bavg_const {H : ℝ} (hH : 0 < H) (c x : ℝ) : Bavg H (fun _ => c) x = c := by
  unfold Bavg
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma Bavg_sub {H : ℝ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : IntervalIntegrable f volume (x - H / 2) (x + H / 2))
    (hg : IntervalIntegrable g volume (x - H / 2) (x + H / 2)) :
    Bavg H (fun y => f y - g y) x = Bavg H f x - Bavg H g x := by
  unfold Bavg
  rw [intervalIntegral.integral_sub hf hg]
  ring

/-- **Theorem 5.37 (the margin on `H`-windows)**, deterministic assembly: see the module
docstring for the three inputs. -/
theorem thm_5_37 {H x M epsN EBR j o csh : ℝ} {RT rhosh : ℝ → ℝ} (hH : 0 < H)
    (hx : 1 < x - H / 2) (hEj : 0 ≤ EBR + j)
    (hRT : IntervalIntegrable RT volume (x - H / 2) (x + H / 2))
    (hrs : IntervalIntegrable rhosh volume (x - H / 2) (x + H / 2))
    (hpred : Real.log x * Bavg H RT x - epsN ≤ Real.log x * M)
    (hbr : ∀ y, x - H / 2 ≤ y → y ≤ x + H / 2 → rhosh y - (EBR + j) / Real.log y ≤ RT y)
    (hg1 : csh - o ≤ Real.log x * Bavg H rhosh x) :
    csh - o - epsN - (EBR + j) * (Real.log x / Real.log (x - H / 2)) ≤ Real.log x * M := by
  have hlx : 0 < Real.log (x - H / 2) := Real.log_pos hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set c := (EBR + j) / Real.log (x - H / 2)
  -- `(EBR + j)/log y ≤ c` on the window
  have hpt : ∀ y, x - H / 2 ≤ y → y ≤ x + H / 2 → rhosh y - c ≤ RT y := by
    intro y hy1 hy2
    have hly : Real.log (x - H / 2) ≤ Real.log y := Real.log_le_log (by linarith) hy1
    have : (EBR + j) / Real.log y ≤ c := div_le_div_of_nonneg_left hEj hlx hly
    linarith [hbr y hy1 hy2]
  have hB : Bavg H rhosh x - c ≤ Bavg H RT x := by
    have hc : IntervalIntegrable (fun _ : ℝ => c) volume (x - H / 2) (x + H / 2) :=
      _root_.intervalIntegrable_const
    have h1 := Bavg_mono hH (f := fun y => rhosh y - c) (g := RT) (hrs.sub hc) hRT hpt
    rw [Bavg_sub hrs hc, Bavg_const hH] at h1
    exact h1
  have e : (EBR + j) * (Real.log x / Real.log (x - H / 2)) = Real.log x * c := by
    simp only [c]; field_simp
  rw [e]
  nlinarith

/-- Theorem 5.37 with the passage factor bounded: if `log x/log(x - H/2) ≤ 1 + δ`,
`log x · M(x) ≥ c_sh - o - ε_N - E_BR - j - δ (E_BR + j)`. -/
theorem thm_5_37' {H x M epsN EBR j o csh δ : ℝ} {RT rhosh : ℝ → ℝ} (hH : 0 < H)
    (hx : 1 < x - H / 2) (hEj : 0 ≤ EBR + j)
    (hRT : IntervalIntegrable RT volume (x - H / 2) (x + H / 2))
    (hrs : IntervalIntegrable rhosh volume (x - H / 2) (x + H / 2))
    (hpred : Real.log x * Bavg H RT x - epsN ≤ Real.log x * M)
    (hbr : ∀ y, x - H / 2 ≤ y → y ≤ x + H / 2 → rhosh y - (EBR + j) / Real.log y ≤ RT y)
    (hg1 : csh - o ≤ Real.log x * Bavg H rhosh x)
    (hδ : Real.log x / Real.log (x - H / 2) ≤ 1 + δ) :
    csh - o - epsN - EBR - j - δ * (EBR + j) ≤ Real.log x * M := by
  have h := thm_5_37 hH hx hEj hRT hrs hpred hbr hg1
  have : (EBR + j) * (Real.log x / Real.log (x - H / 2)) ≤ (EBR + j) * (1 + δ) :=
    mul_le_mul_of_nonneg_left hδ hEj
  nlinarith

/-- **Proposition 5.38(a)**, Step 6(a), at a point `t ≥ X₀^{1.01}` (all quantities at `t`,
multiplied by `log t`): `mL = m(t) log t`, `BmL = (Bm)(t) log t`, `ML = M(t) log t`,
`vL = v(t) log t`; `sη = sup_y log y · η(y)`. -/
theorem prop_5_38_a {mL BmL ML vL o epsN EBR j sη ES V hterm : ℝ}
    (hm : BmL - vL ≤ mL)                         -- `m ≥ Bm - v`
    (hB : ML - 54 * sη - hterm ≤ BmL)            -- `Bm ≥ M - 54η - 6/H`
    (hM : 0.97 - o - epsN - EBR - j ≤ ML)        -- Theorem 5.37, `c_sh = 0.97`
    (hv : vL ≤ 6.5 * ES + V)                     -- Steps 1-5
    (hsmall : o + epsN + EBR + j + 54 * sη + hterm + 6.5 * ES + V ≤ 0.01) :
    0.97 - o - epsN - EBR - 54 * sη - 6.5 * ES - j - V - hterm ≤ mL ∧ 0.96 ≤ mL := by
  constructor <;> linarith

/-- **Proposition 5.38(b)**, Step 6(b), "Sum": `m(t) log t ≥ ρ^sh(t) log t - j_{X₀}(t) - 10⁻¹²`
with `ρ^sh(t) log t ≥ 0.82` and `j_{X₀}(t) ≤ 0.4209` gives `m(t) log t ≥ 0.399`. -/
theorem prop_5_38_b {mL rsL j : ℝ} (hm : rsL - j - 1 / 10 ^ 12 ≤ mL) (hrs : 0.82 ≤ rsL)
    (hj : j ≤ 0.4209) : 0.399 ≤ mL := by
  have : (1 : ℝ) / 10 ^ 12 ≤ 1 / 10000 := by norm_num
  linarith

/-- The three ranges of Proposition 5.38 give the input of Corollary 5.40. -/
theorem pointwiseMargin_of {m : ℝ → ℝ} {X0 X1 : ℝ}
    (ha : ∀ t, X1 ≤ t → 0.96 ≤ m t * Real.log t)
    (hb : ∀ t, 2 * X0 ≤ t → t ≤ X1 → 0.399 ≤ m t * Real.log t)
    (hc : ∀ t, X0 ≤ t → t < 2 * X0 → 0.73 ≤ m t * Real.log t)
    (hz : ∀ t, t < X0 → m t = 0) : PointwiseMargin m X0 := by
  refine ⟨fun t ht => ?_, hz⟩
  rcases lt_or_ge t (2 * X0) with h1 | h1
  · linarith [hc t ht h1]
  rcases le_or_gt t X1 with h2 | h2
  · exact hb t h1 h2
  · linarith [ha t h2.le]

end Margin

end
