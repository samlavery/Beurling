module

public import RequestProject.Beurling.Noise.BridgeNear
public import RequestProject.Beurling.Noise.BridgeXBTau
public import RequestProject.Beurling.Noise.BridgeG1
public import RequestProject.Beurling.Noise.MarginVar

/-!
# The chain Bridge → Theorem 5.37: the three inputs at the level of the realised operators

* `rhoSh_add_smul`, `Rres_add_smul` : `ρ^sh` and `R_res` are linear in `T' = T_c + j₀ 1_{[X₀,∞)}`
  (`R_res` needs `T_c` bounded measurable, so that every `∫ T_c dC_n` exists);
* `hbr_of` : the input (bridge) of Theorem 5.37 at a point `y`, from **Proposition 5.26**
  (`prop_5_26_hbs`, for `T_c`) and **Lemma 5.27** (`lemma_5_27`, for the jump `J`):
  `R_res T'(y) ≥ ρ^sh T'(y) - (E_BR + j)/log y`, where `E_BR` bounds the right side of
  Proposition 5.26 and `j` bounds `j₀ (log y · 𝔅(y) + 4.3 C_N E_θ)` (eq. (jX0));
* `avg_ge` : an average of `c/log y` over `W_x` (the input (g1) of Theorem 5.37 from
  **Proposition 5.35** at every point of the window);
* `hpred_of` : the input (predictable) of Theorem 5.37 from **Lemma 5.34** (the identity
  `Pred.predictable_identity` and the bound `Pred.lemma_5_34_bound`), with `B` the window average.
-/

@[expose] public section

open Real MeasureTheory Set BeurlingSystem

namespace KR.Chain

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- `ρ^sh` is linear. -/
lemma rhoSh_add_smul (y : ℝ) (f g : ℝ → ℝ) (c : ℝ) :
    rhoSh P tw X0m y (fun t => f t + c * g t) =
      rhoSh P tw X0m y f + c * rhoSh P tw X0m y g := by
  unfold rhoSh
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- `R_res` is linear on bounded measurable functions. -/
lemma Rres_add_smul (hW : WidthReg H) (y : ℝ) {f g : ℝ → ℝ} (hfm : Measurable f)
    (hfb : ∀ t, |f t| ≤ 2) (hgm : Measurable g) (hgb : ∀ t, |g t| ≤ 1) (c : ℝ) :
    Rres P H tw X0m y (fun t => f t + c * g t) =
      Rres P H tw X0m y f + c * Rres P H tw X0m y g := by
  unfold Rres
  rw [mul_add, Finset.mul_sum]
  have hsum : ∀ n ∈ levels P X0m y,
      (∫ t, (f t + c * g t) * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n =
        (∫ t, f t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n +
          c * ((∫ t, g t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n) := by
    intro n _
    have hgk := integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hW n
    have hbf : ∀ᵐ t ∂volume, ‖f t‖ ≤ 2 :=
      Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hfb t
    have hbg : ∀ᵐ t ∂volume, ‖g t‖ ≤ 1 :=
      Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hgb t
    have i1 := hgk.1.bdd_mul (c := 2) hfm.aestronglyMeasurable hbf
    have i2 := hgk.1.bdd_mul (c := 1) hgm.aestronglyMeasurable hbg
    have e : (fun t => (f t + c * g t) * gK P.labelVal y H (phiT tw X0m) n t) =
        fun t => f t * gK P.labelVal y H (phiT tw X0m) n t +
          c * (g t * gK P.labelVal y H (phiT tw X0m) n t) := by
      funext t; ring
    rw [e, integral_add i1 (i2.const_mul c), integral_const_mul]
    ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
  ring

/-- The jump indicator `1_{[X₀, ∞)}`. -/
noncomputable abbrev ind (X0 : ℝ) : ℝ → ℝ := (Ici X0).indicator fun _ => 1

lemma ind_measurable (X0 : ℝ) : Measurable (ind X0) :=
  measurable_const.indicator measurableSet_Ici

lemma ind_abs_le (X0 t : ℝ) : |ind X0 t| ≤ 1 := by
  unfold ind Set.indicator; split_ifs <;> simp

/-- **The input (bridge) of Theorem 5.37 at a point `y`**: if `log y |BR_c(y)| ≤ E`
(Proposition 5.26), `|R_res 1_{[X₀,∞)} - ρ^sh 1_{[X₀,∞)}|(y) ≤ b` (Lemma 5.27), and the sizes
`E ≤ E_BR`, `j₀ b log y ≤ j` with `0 ≤ j₀`, then for `T' = T_c + j₀ 1_{[X₀,∞)}`:
`ρ^sh T'(y) - (E_BR + j)/log y ≤ R_res T'(y)`. -/
theorem hbr_of (hW : WidthReg H) {y X0 j0 E b EBR j : ℝ} (hly : 0 < Real.log y)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) (hj0 : 0 ≤ j0)
    (hBR : Real.log y * |BRc P H tw X0m y Tc| ≤ E)
    (hXB : |Rres P H tw X0m y (ind X0) - rhoSh P tw X0m y (ind X0)| ≤ b)
    (hE : E ≤ EBR) (hj : j0 * b * Real.log y ≤ j) :
    rhoSh P tw X0m y (fun t => Tc t + j0 * ind X0 t) - (EBR + j) / Real.log y ≤
      Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t) := by
  rw [rhoSh_add_smul, Rres_add_smul hW y hTm hTb (ind_measurable X0) (ind_abs_le X0)]
  unfold BRc at hBR
  have h1 : rhoSh P tw X0m y Tc - Rres P H tw X0m y Tc ≤ E / Real.log y := by
    rw [le_div_iff₀ hly]
    have := neg_abs_le (Rres P H tw X0m y Tc - rhoSh P tw X0m y Tc)
    nlinarith
  have h2 : j0 * (rhoSh P tw X0m y (ind X0) - Rres P H tw X0m y (ind X0)) ≤ j / Real.log y := by
    rw [le_div_iff₀ hly]
    have h3 := neg_abs_le (Rres P H tw X0m y (ind X0) - rhoSh P tw X0m y (ind X0))
    have h4 : j0 * (rhoSh P tw X0m y (ind X0) - Rres P H tw X0m y (ind X0)) ≤ j0 * b :=
      mul_le_mul_of_nonneg_left (by linarith) hj0
    nlinarith
  have h5 : E / Real.log y ≤ EBR / Real.log y := div_le_div_of_nonneg_right hE hly.le
  rw [add_div]
  linarith

/-- **Averaging** (the input (g1) of Theorem 5.37): if `c ≤ f(y) log y` on `W_x`, `0 ≤ c`,
`x - H/2 > 1`, then `log x · (B f)(x) ≥ c log x/log(x + H/2)`. -/
theorem avg_ge {Hx x c : ℝ} {f : ℝ → ℝ} (hH : 0 < Hx) (hx : 1 < x - Hx / 2) (hc : 0 ≤ c)
    (hf : IntervalIntegrable f volume (x - Hx / 2) (x + Hx / 2))
    (hpt : ∀ y, x - Hx / 2 ≤ y → y ≤ x + Hx / 2 → c ≤ f y * Real.log y) :
    c * (Real.log x / Real.log (x + Hx / 2)) ≤ Real.log x * Margin.Bavg Hx f x := by
  have hlt : 0 < Real.log (x + Hx / 2) := Real.log_pos (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set k := c / Real.log (x + Hx / 2)
  have hk : ∀ y, x - Hx / 2 ≤ y → y ≤ x + Hx / 2 → k ≤ f y := by
    intro y hy1 hy2
    have hly : 0 < Real.log y := Real.log_pos (by linarith)
    have hl : Real.log y ≤ Real.log (x + Hx / 2) := Real.log_le_log (by linarith) hy2
    have h1 : c / Real.log (x + Hx / 2) ≤ c / Real.log y := div_le_div_of_nonneg_left hc hly hl
    have h2 : c / Real.log y ≤ f y := by rw [div_le_iff₀ hly]; exact hpt y hy1 hy2
    linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => k) volume (x - Hx / 2) (x + Hx / 2) :=
    _root_.intervalIntegrable_const
  have hB := Margin.Bavg_mono hH hconst hf hk
  rw [Margin.Bavg_const hH] at hB
  have e : c * (Real.log x / Real.log (x + Hx / 2)) = Real.log x * k := by
    simp only [k]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hB hlx.le

/-- **The input (predictable) of Theorem 5.37 from Lemma 5.34.** `B`, `K_pt`, `R_res` are
additive maps (`hR`: `R_res` inverts `1 + K_pt B`; `hinj`: the push-through form determines
`ρ̃`, §5.3), `hmargin` is the margin identity (Proposition 5.11 with (Ttilde), `vt = ϑ/H`), `B`
is the window average at `x` (`hBx`), the three bullet bounds hold at `x`; then with
`M = ρ̃ + ν + NT`, `log x · (B R_res T')(x) - ε_N ≤ log x · M(x)`,
`ε_N = a + b + 6 log x/H(x)`. -/
theorem hpred_of (B K R : (ℝ → ℝ) →+ (ℝ → ℝ)) (hR : ∀ g, R g + K (B (R g)) = g)
    (hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f')
    (ρ ν NT ϑ Tc J : ℝ → ℝ) (Hf : ℝ → ℝ)
    (hmargin : ρ + B (K ρ) = B (Tc + J) + (fun z => ϑ z / Hf z) - ν - NT)
    {x a b : ℝ} (hlx : 0 ≤ Real.log x) (hH : 0 < Hf x)
    (hBx : ∀ g, B g x = Margin.Bavg (Hf x) g x)
    (hK : Real.log x * |B (K (B (R ((B Tc - Tc) + (fun z => ϑ z / Hf z) - ν - NT)))) x| ≤ a)
    (hG : Real.log x * |B (R (K ((B (Tc + J) + (fun z => ϑ z / Hf z) - ν - NT - B J) -
      B (B (Tc + J) + (fun z => ϑ z / Hf z) - ν - NT - B J)))) x| ≤ b)
    (hϑ : |ϑ x| ≤ 6) :
    Real.log x * Margin.Bavg (Hf x) (R (Tc + J)) x - (a + b + 6 * Real.log x / Hf x) ≤
      Real.log x * (ρ x + ν x + NT x) := by
  have hid := Pred.predictable_identity B K R hR hinj ρ ν NT (fun z => ϑ z / Hf z) Tc J hmargin
  simp only at hid
  have hDx := congrFun hid x
  simp only [Pi.add_apply, Pi.sub_apply] at hDx
  set D : ℝ → ℝ := fun z => ρ z + ν z + NT z - B (R (Tc + J)) z
  have hD : D x = ϑ x / Hf x -
      B (K (B (R ((B Tc - Tc) + (fun z => ϑ z / Hf z) - ν - NT)))) x -
      B (R (K ((B (Tc + J) + (fun z => ϑ z / Hf z) - ν - NT - B J) -
        B (B (Tc + J) + (fun z => ϑ z / Hf z) - ν - NT - B J)))) x := by
    simp only [D]; linarith
  have hb := Pred.lemma_5_34_bound (D := D) (vt := ϑ) (H := Hf) (x := x) hD hlx hH hK hG hϑ
  have habs := neg_abs_le (D x)
  simp only [D] at habs hb
  rw [← hBx]
  nlinarith

end KR.Chain

end
