module

public import RequestProject.Beurling.DesignedZero
public import RequestProject.Beurling.TargetError

/-!
# Theorem 4.10 (Zeros) from Lemma 4.6 and the perturbation bound

* `differentiable_phiTransform` : `Φ` is entire;
* `differentiableAt_Mk` : `M_k` is holomorphic away from `w = 0`;
* `Theorem410InputsDesigned` : the inputs of Theorem 4.10 in the form used in the paper: for each
  `k`, the hypotheses of Lemma 4.6 hold for `Z_B` and the data `(α_k, γ_k, x_k)`, and the
  perturbation `ζ_P - (Z_B + M_k)` is `< 1/4` on the disc `|s - (1 + iγ_k)| ≤ δ_k`;
* `theorem410Inputs_of_designed` : these imply the earlier `Theorem410Inputs`, via Lemma 4.6
  (which supplies the zeros `s*_k`, the estimate of `Re s*_k`, and `|Z_B + M_k| ≥ 1/4` on the
  circles, so that `|ζ_P - (Z_B + M_k)| < |Z_B + M_k|` there);
* `Theorem21InputsDesigned` and `corollary_2_2_of_designed` : the corresponding refinement of the
  hypothesis for Theorem 2.1 and Corollary 2.2.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep BeurlingSystem DesignedZero

namespace DesignedZero

/-- `Φ'(w) = -∫₀¹ v e^{-wv} ϕ'(v) dv`. -/
theorem hasDerivAt_phiTransform (w₀ : ℂ) :
    HasDerivAt phiTransform (∫ v in (0:ℝ)..1,
      (-(v:ℂ)) * Complex.exp (-w₀ * v) * ((deriv Real.smoothTransition v : ℝ) : ℂ)) w₀ := by
  have hc := continuous_deriv_smoothTransition
  set B : ℝ := 2 * Real.exp (‖w₀‖ + 1)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (bound := fun _ => B)
    (F := fun w v => Complex.exp (-w * v) * ((deriv Real.smoothTransition v : ℝ) : ℂ))
    (F' := fun w v =>
      (-(v:ℂ)) * Complex.exp (-w * v) * ((deriv Real.smoothTransition v : ℝ) : ℂ))
    (x₀ := w₀) (s := ball w₀ 1) (ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun w => (continuous_phiIntegrand w).aestronglyMeasurable)
    ((continuous_phiIntegrand w₀).intervalIntegrable _ _)
    (by
      apply Continuous.aestronglyMeasurable
      exact ((continuous_neg.comp Complex.continuous_ofReal).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).mul
        (Complex.continuous_ofReal.comp hc))
    (by
      refine Filter.Eventually.of_forall fun v hv w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hv
      have hv0 : 0 ≤ v := hv.1.le
      have hv1 : v ≤ 1 := hv.2
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hv0, abs_of_nonneg (deriv_smoothTransition_nonneg v),
        Complex.norm_exp]
      have h1 : (-w * (v:ℂ)).re ≤ ‖w₀‖ + 1 := by
        have : (-w * (v:ℂ)).re = -(w.re * v) := by simp
        rw [this]
        have hw' : ‖w‖ ≤ ‖w₀‖ + 1 := by
          have := norm_le_norm_add_norm_sub' w w₀
          rw [mem_ball, dist_eq_norm] at hw; linarith
        have := Complex.abs_re_le_norm w
        have : |w.re * v| ≤ ‖w‖ := by
          rw [abs_mul, abs_of_nonneg hv0]; nlinarith [abs_nonneg w.re]
        linarith [neg_abs_le (w.re * v), abs_nonneg (w.re * v)]
      have h2 := deriv_smoothTransition_le_two v
      have h3 := Real.exp_le_exp.mpr h1
      have h4 := deriv_smoothTransition_nonneg v
      have h5 := Real.exp_pos (-w * (v:ℂ)).re
      calc v * Real.exp (-w * (v:ℂ)).re * deriv Real.smoothTransition v
          ≤ 1 * Real.exp (‖w₀‖ + 1) * 2 := by gcongr
        _ = B := by ring)
    intervalIntegrable_const
    (by
      refine Filter.Eventually.of_forall fun v _ w _ => ?_
      have := ((hasDerivAt_id w).neg.mul_const (v:ℂ)).cexp.mul_const
        ((deriv Real.smoothTransition v : ℝ) : ℂ)
      convert this using 1
      simp only [Pi.neg_apply, id]; ring)
  exact key.2

/-- `Φ` is entire. -/
theorem differentiable_phiTransform : Differentiable ℂ phiTransform :=
  fun w => (hasDerivAt_phiTransform w).differentiableAt

/-- `M_k` is holomorphic wherever `w = s - θ - iγ ≠ 0`. -/
theorem differentiableAt_Mk {θ α γ x : ℝ} (hx : 0 < x) {s : ℂ} (hw : s - θ - γ * I ≠ 0) :
    DifferentiableAt ℂ (Mk θ α γ x) s := by
  unfold Mk
  have hW : DifferentiableAt ℂ (fun s : ℂ => s - θ - γ * I) s :=
    (differentiableAt_id.sub_const _).sub_const _
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ((differentiableAt_const _).mul differentiableAt_id).div_const _ |>.mul ?_
  refine DifferentiableAt.div ?_ hW hw
  exact (hW.neg.const_cpow (Or.inl hx')).mul (differentiable_phiTransform.differentiableAt.comp s hW)

namespace Lemma46Hyp

variable {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}

/-- The disc of Lemma 4.6 lies in the punctured half-plane `Re s > a` for `a ≤ 3/4`. -/
lemma closedBall_subset (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {a : ℝ} (ha : a ≤ 3 / 4) :
    closedBall (1 + γ * I) (designRadius x) ⊆ puncturedHalfPlane a := by
  intro s hs
  rw [mem_closedBall, dist_eq_norm] at hs
  have hδ := h.δ_le
  have h1 := Complex.abs_re_le_norm (s - (1 + γ * I))
  have h2 := Complex.abs_im_le_norm (s - (1 + γ * I))
  simp at h1 h2
  refine ⟨?_, ?_⟩
  · show a < s.re
    linarith [(abs_le.mp (h1.trans hs)).1]
  · intro h0
    rw [Set.mem_singleton_iff] at h0
    have him : s.im = 0 := by rw [h0]; simp
    have := h.γ_ge
    have h3 := Complex.abs_im_le_norm (s - (1 + γ * I))
    rw [Complex.sub_im, him] at h3
    simp at h3
    rw [abs_of_pos (by linarith)] at h3
    linarith

/-- On the disc `|s - (1 + iγ)| ≤ δ`, `w = s - θ - iγ ≠ 0`. -/
lemma w_ne_zero_of_mem (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) {s : ℂ}
    (hs : s ∈ closedBall (1 + γ * I) (designRadius x)) : s - θ - γ * I ≠ 0 := by
  have hw : s - θ - γ * I ∈ closedBall (cen θ) (designRadius x) := by
    rw [mem_closedBall, dist_eq_norm] at hs ⊢
    convert hs using 2; simp only [cen]; push_cast; ring
  exact h.w_ne_zero hw

end Lemma46Hyp

end DesignedZero

/-- **The inputs of Theorem 4.10, in the form of the paper.** Along `x_k → ∞`, with fixed
`θ`, `Λ`, `κ₀` and data `α_k`, `γ_k` and base factor `Z_B` (which may depend on `k`):

* the hypotheses of Lemma 4.6 (`Lemma46Hyp`) hold for each `k`;
* the perturbation `F - (Z_B + M_k)` (in the paper `E_k + ∑_{j≠k} R̂_j + D̂_{<a_k} + D̂_{≥a_k} +
  Ê_A`) is `< 1/4` on the disc `|s - (1 + iγ_k)| ≤ δ_k`, which contains the Rouché circle. -/
def Theorem410InputsDesigned (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (Λ κ₀ : ℝ) (α γ xk : ℕ → ℝ) (ZB : ℕ → ℂ → ℂ),
    Tendsto xk atTop atTop ∧
    (∀ k, Lemma46Hyp θ Λ κ₀ (α k) (γ k) (xk k) (ZB k)) ∧
    ∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xk k)),
      ‖F s - (ZB k s + Mk θ (α k) (γ k) (xk k) s)‖ < 1 / 4

/-- **The inputs of Theorem 4.10, with the perturbation bounded on the Rouché circles.** As
`Theorem410InputsDesigned`, but the perturbation bound `|F - (Z_B + M_k)| < 1/4` is only required
on the circle `|s - s₀| = 1/log x_k` around any zero `s₀` of `Z_B + M_k` whose circle lies in the
disc `|s - (1 + iγ_k)| ≤ δ_k` (as in the paper, where Lemma 4.7 is a bound on that circle). -/
def Theorem410InputsCircle (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (Λ κ₀ : ℝ) (α γ xk : ℕ → ℝ) (ZB : ℕ → ℂ → ℂ),
    Tendsto xk atTop atTop ∧
    (∀ k, Lemma46Hyp θ Λ κ₀ (α k) (γ k) (xk k) (ZB k)) ∧
    ∀ k (s₀ : ℂ), ZB k s₀ + Mk θ (α k) (γ k) (xk k) s₀ = 0 →
      ‖s₀ - (1 + γ k * I)‖ + 1 / Real.log (xk k) ≤ designRadius (xk k) →
      ∀ s ∈ sphere s₀ (1 / Real.log (xk k)),
        ‖F s - (ZB k s + Mk θ (α k) (γ k) (xk k) s)‖ < 1 / 4

/-- The disc form of the inputs implies the circle form. -/
theorem Theorem410InputsDesigned.circle {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsDesigned θ F) :
    Theorem410InputsCircle θ F := by
  obtain ⟨Λ, κ₀, α, γ, xk, ZB, hx, hH, hpert⟩ := h
  refine ⟨Λ, κ₀, α, γ, xk, ZB, hx, hH, fun k s₀ _ hdisc s hs => hpert k s ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  rw [mem_sphere, dist_eq_norm] at hs
  calc ‖s - (1 + γ k * I)‖ = ‖(s - s₀) + (s₀ - (1 + γ k * I))‖ := by ring_nf
    _ ≤ ‖s - s₀‖ + ‖s₀ - (1 + γ k * I)‖ := norm_add_le _ _
    _ ≤ designRadius (xk k) := by linarith

/-- **Theorem 4.10 inputs from Lemma 4.6**: the circle-form inputs give the inputs of
`theorem_4_10` (zeros `s*_k` of `Z_B + M_k` with the stated real parts, and the Rouché
inequality on the circles `|s - s*_k| = 1/log x_k`), on any half-plane `Re s > a`, `a ≤ 3/4`. -/
theorem theorem410Inputs_of_circle {θ a : ℝ} {F : ℂ → ℂ} (ha : a ≤ 3 / 4)
    (h : Theorem410InputsCircle θ F) : Theorem410Inputs F a := by
  obtain ⟨Λ, κ₀, α, γ, xk, ZB, hx, hH, hpert⟩ := h
  choose sstar hzero hdisc hre hcirc using fun k => lemma_4_6 (hH k)
  have hsub : ∀ k, closedBall (sstar k) (1 / Real.log (xk k)) ⊆
      closedBall (1 + γ k * I) (designRadius (xk k)) := fun k s hs => by
    rw [mem_closedBall, dist_eq_norm] at hs ⊢
    calc ‖s - (1 + γ k * I)‖ = ‖(s - sstar k) + (sstar k - (1 + γ k * I))‖ := by ring_nf
      _ ≤ ‖s - sstar k‖ + ‖sstar k - (1 + γ k * I)‖ := norm_add_le _ _
      _ ≤ designRadius (xk k) := by linarith [hdisc k]
  refine ⟨sstar, xk, fun k s => ZB k s + Mk θ (α k) (γ k) (xk k) s, 2 * Λ + 4, hx,
    fun k => (hH k).one_lt_x, fun k => (hsub k).trans ((hH k).closedBall_subset ha),
    fun k => ?_, hzero, fun k s hs => ?_, hre⟩
  · intro s hs
    have hs' := hsub k hs
    exact (((hH k).diff s hs').add (differentiableAt_Mk (by linarith [(hH k).one_lt_x])
      ((hH k).w_ne_zero_of_mem hs'))).differentiableWithinAt
  · exact lt_of_lt_of_le (hpert k _ (hzero k) (hdisc k) s hs) (hcirc k s hs)

/-- **Theorem 4.10 inputs from Lemma 4.6** (disc form of the perturbation bound). -/
theorem theorem410Inputs_of_designed {θ a : ℝ} {F : ℂ → ℂ} (ha : a ≤ 3 / 4)
    (h : Theorem410InputsDesigned θ F) : Theorem410Inputs F a :=
  theorem410Inputs_of_circle ha h.circle

open Target

/-- Refined inputs for one system: part (i) with the concrete target (6), and the paper-form
inputs of Theorem 4.10 for the canonical continuation `zetaCont P 1`. -/
def TheoremAInputsDesigned (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsDesigned θ (P.zetaCont 1)

theorem TheoremAInputsDesigned.target {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hθ : θ ≤ 1 / 2) (h : TheoremAInputsDesigned θ X₀ P) : TheoremAInputsTarget θ X₀ P :=
  ⟨h.1, (θ + 1) / 2, by linarith, by linarith, theorem410Inputs_of_designed (by linarith) h.2⟩

/-- **Theorem 2.1, refined hypothesis (Lemma 4.6 discharged)**: as `Theorem21InputsTarget`, but
part (ii) is reduced to the hypotheses of Lemma 4.6 and the perturbation bound `< 1/4`. -/
def Theorem21InputsDesigned : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsDesigned θ X₀ (P ω)

theorem theorem21InputsTarget_of_designed (h : Theorem21InputsDesigned) :
    Theorem21InputsTarget := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => (hP ω hω).target (by linarith [hθ.2])⟩

/-- The refined hypothesis (Lemma 4.6 discharged) implies Theorem 2.1. -/
theorem theorem21_of_designed (h : Theorem21InputsDesigned) : Theorem21 :=
  theorem21_of_target (theorem21InputsTarget_of_designed h)

/-- **Corollary 2.2** from the refined hypothesis (Lemma 4.6 discharged). -/
theorem corollary_2_2_of_designed (h : Theorem21InputsDesigned) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_designed h)

end
