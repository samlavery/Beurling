module

public import RequestProject.Beurling.Remark12

/-!
# The continuation of `ζ_P`, Rouché's theorem, and the deduction of Theorem 4.10

* `BeurlingSystem.zetaCont_isZetaContinuation`: if `N_P(x) = A x + O(x^β)` with `β < 1`, then
  `ζ_P` continues analytically to `Re s > β`, `s ≠ 1`, by
  `A s/(s-1) + s ∫_1^∞ (N_P(x) - A x) x^{-s-1} dx` (first display in the proof of Remark 1.2).
* `rouche_exists_zero`: Rouché's theorem (existence form), proved from the maximum modulus
  principle.
* `theorem_4_10`: the deduction of Theorem 4.10 (designed zeros of `ζ_P`) from the inputs of its
  proof — the zeros `s*_k` of the comparison functions (Lemma 4.6) and the perturbation bound on
  the circles `|s - s*_k| = 1/log x_k` — via Rouché's theorem.
* `Theorem21Inputs` / `theorem21_of_inputs`: Theorem 2.1 with part (ii) replaced by those inputs
  for the canonical continuation implies Theorem 2.1, hence Corollary 2.2.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set Metric BeurlingSystem Remark12

namespace BeurlingSystem

/-- The canonical continuation of `ζ_P`: `A s/(s-1) + s ∫_1^∞ (N_P(x) - A x) x^{-s-1} dx`. -/
noncomputable def zetaCont (P : BeurlingSystem) (A : ℝ) (s : ℂ) : ℂ :=
  A * s / (s - 1) + s * tailMellin (fun x => P.N x - A * x) s

/-- **Analytic continuation of `ζ_P`**: if `N_P(x) = A x + O(x^β)` (for `x ≥ 1`) with `β < 1`,
then `zetaCont P A` is holomorphic on `Re s > β`, `s ≠ 1`, and equals `ζ_P` on `Re s > 1`. -/
theorem zetaCont_isZetaContinuation (P : BeurlingSystem) {A C β : ℝ} (hβ : β < 1)
    (hN : ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) :
    P.IsZetaContinuation β (P.zetaCont A) := by
  have hNH : AbelMellin.Hyp P.val (fun _ => (1 : ℝ)) 1 := by
    refine ⟨P.one_le_val, fun _ => zero_le_one, P.summable_N_ite, A + |C|, fun x hx => ?_⟩
    rw [← P.N_eq_cnt, Real.rpow_one]
    have h1 := (abs_le.mp (hN x hx)).2
    have h2 : x ^ β ≤ x := by
      calc x ^ β ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hβ.le
        _ = x := Real.rpow_one x
    have h3 : C * x ^ β ≤ |C| * x :=
      calc C * x ^ β ≤ |C| * x ^ β :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |C| * x := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    nlinarith
  have hNmono : Monotone P.N := fun x y h => by
    rw [P.N_eq_cnt, P.N_eq_cnt]; exact AbelMellin.cnt_mono hNH h
  have hNli : LocallyIntegrable (fun x => P.N x - A * x) :=
    hNmono.locallyIntegrable.sub (continuous_const.mul continuous_id).locallyIntegrable
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
    have hT := (tailMellin_differentiableOn hNli hN).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show β < s.re from hs.1))
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (A : ℂ) * s / (s - 1)) s :=
      ((differentiableAt_const _).mul differentiableAt_id).div
        (differentiableAt_id.sub_const 1) hs1
    have h2 : DifferentiableAt ℂ
        (fun s : ℂ => s * tailMellin (fun x => P.N x - A * x) s) s :=
      differentiableAt_id.mul hT
    exact h1.add h2
  · have h := AbelMellin.hasSum_cpow hNH (s := s) (by linarith) hs
    have hcnt : AbelMellin.cnt P.val (fun _ => (1:ℝ)) = P.N :=
      funext fun x => (P.N_eq_cnt x).symm
    rw [hcnt, integral_split P.N A hNli hN (by linarith) hs] at h
    have : P.zeta s = s * (tailMellin (fun x => P.N x - A * x) s + A / (s - 1)) := by
      rw [← h.tsum_eq]; unfold zeta; simp
    rw [this]
    have hs1 : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    simp only [zetaCont]
    field_simp
    ring

end BeurlingSystem

/-- **Rouché's theorem** (existence form). If `f`, `g` are holomorphic on the closed disc
`|z - c| ≤ r`, `|f - g| < |g|` on the circle `|z - c| = r`, and `g` has a zero inside, then so
does `f`. (Proof: otherwise `Re (g/f) > 1/2` on the circle, and the maximum modulus principle for
`exp(-g/f)` contradicts `g/f = 0` at the zero of `g`.) -/
theorem rouche_exists_zero {f g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r)) (hg : DifferentiableOn ℂ g (closedBall c r))
    (hfg : ∀ z ∈ sphere c r, ‖f z - g z‖ < ‖g z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r)
    (hg0 : g z₀ = 0) :
    ∃ z ∈ ball c r, f z = 0 := by
  by_contra hcon
  push_neg at hcon
  have hfne : ∀ z ∈ closedBall c r, f z ≠ 0 := by
    intro z hz
    rcases (mem_closedBall.mp hz).lt_or_eq with h | h
    · exact hcon z (mem_ball.mpr h)
    · intro h0
      have := hfg z (mem_sphere.mpr h)
      rw [h0, zero_sub, norm_neg] at this
      exact lt_irrefl _ this
  set φ : ℂ → ℂ := fun z => Complex.exp (-(g z / f z))
  have hφ : DifferentiableOn ℂ φ (closedBall c r) :=
    ((hg.div hf hfne).neg).cexp
  rw [← closure_ball c hr.ne'] at hφ
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c r) isBounded_ball
    hφ.diffContOnCl (C := Real.exp (-(1/2))) ?_ (subset_closure hz₀)
  · simp only [φ, hg0, zero_div, neg_zero, Complex.exp_zero, norm_one] at key
    linarith [Real.exp_lt_one_iff.mpr (show (-(1/2):ℝ) < 0 by norm_num)]
  · intro z hz
    rw [frontier_ball c hr.ne'] at hz
    have h1 := hfg z hz
    have hfz := hfne z (sphere_subset_closedBall hz)
    simp only [φ, Complex.norm_exp, Real.exp_le_exp, Complex.neg_re, neg_le_neg_iff]
    set w := g z / f z
    have hw : ‖1 - w‖ < ‖w‖ := by
      have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
      have e1 : f z - g z = f z * (1 - w) := by simp only [w]; field_simp
      have e2 : g z = f z * w := by simp only [w]; field_simp
      rw [e1, e2, norm_mul, norm_mul] at h1
      exact lt_of_mul_lt_mul_left h1 hpos.le
    have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by gcongr
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
    simp at h2
    nlinarith

/-- **The inputs of Theorem 4.10** for a function `F` on the punctured half-plane `Re s > a`:
along `x_k → ∞` there are points `s*_k` with
`Re s*_k = 1 - (3 log log x_k + O(1))/log x_k` and comparison functions `Φ_k` (in the paper
`Z_B + M_k`), holomorphic on the closed discs `|s - s*_k| ≤ 1/log x_k` (which lie in the
half-plane), with `Φ_k(s*_k) = 0` (Lemma 4.6) and `|F - Φ_k| < |Φ_k|` on the circles
`|s - s*_k| = 1/log x_k` (the perturbation bound in the proof of Theorem 4.10). -/
def Theorem410Inputs (F : ℂ → ℂ) (a : ℝ) : Prop :=
  ∃ (sstar : ℕ → ℂ) (xk : ℕ → ℝ) (Φ : ℕ → ℂ → ℂ) (C : ℝ),
    Tendsto xk atTop atTop ∧ (∀ k, 1 < xk k) ∧
    (∀ k, closedBall (sstar k) (1 / Real.log (xk k)) ⊆ puncturedHalfPlane a) ∧
    (∀ k, DifferentiableOn ℂ (Φ k) (closedBall (sstar k) (1 / Real.log (xk k)))) ∧
    (∀ k, Φ k (sstar k) = 0) ∧
    (∀ k, ∀ s ∈ sphere (sstar k) (1 / Real.log (xk k)), ‖F s - Φ k s‖ < ‖Φ k s‖) ∧
    ∀ k, |(1 - (sstar k).re) * Real.log (xk k) - 3 * Real.log (Real.log (xk k))| ≤ C

/-- **Theorem 4.10 (Zeros)**, deduced from its inputs by Rouché's theorem: `F` has zeros `ρ_k`
with `|ρ_k - s*_k| < 1/log x_k`, hence `Re ρ_k = 1 - (3 log log x_k + O(1))/log x_k`. -/
theorem theorem_4_10 {P : BeurlingSystem} {a : ℝ} {F : ℂ → ℂ} (hF : P.IsZetaContinuation a F)
    (h : Theorem410Inputs F a) :
    ∃ (ρ : ℕ → ℂ) (xk : ℕ → ℝ) (C : ℝ), Tendsto xk atTop atTop ∧
      (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
      ∀ k, |(1 - (ρ k).re) * Real.log (xk k) - 3 * Real.log (Real.log (xk k))| ≤ C := by
  obtain ⟨sstar, xk, Φ, C, hx, hx1, hball, hΦ, hΦ0, hpert, hC⟩ := h
  have hr : ∀ k, 0 < 1 / Real.log (xk k) := fun k => by
    have := Real.log_pos (hx1 k); positivity
  have hzero : ∀ k, ∃ z ∈ ball (sstar k) (1 / Real.log (xk k)), F z = 0 := fun k =>
    rouche_exists_zero (hr k) (hF.1.mono (hball k)) (hΦ k) (hpert k)
      (mem_ball_self (hr k)) (hΦ0 k)
  choose ρ hρ hρ0 using hzero
  refine ⟨ρ, xk, C + 1, hx, fun k => ⟨hball k (ball_subset_closedBall (hρ k)), hρ0 k⟩,
    fun k => ?_⟩
  have hlog : 0 < Real.log (xk k) := Real.log_pos (hx1 k)
  have hd : |(ρ k).re - (sstar k).re| * Real.log (xk k) ≤ 1 := by
    have h1 : |(ρ k).re - (sstar k).re| ≤ ‖ρ k - sstar k‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖ρ k - sstar k‖ < 1 / Real.log (xk k) := mem_ball_iff_norm.mp (hρ k)
    rw [lt_div_iff₀ hlog] at h2
    nlinarith [abs_nonneg ((ρ k).re - (sstar k).re)]
  have e : (1 - (ρ k).re) * Real.log (xk k) - 3 * Real.log (Real.log (xk k)) =
      ((1 - (sstar k).re) * Real.log (xk k) - 3 * Real.log (Real.log (xk k))) -
        ((ρ k).re - (sstar k).re) * Real.log (xk k) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos hlog]
  linarith [hC k]

/-- `N_P(x) = x + O(x^β)` for every `β > θ`, from part (i) of Theorem 2.1 alone. -/
theorem N_bound_of_part_i {θ : ℝ} {P : BeurlingSystem} (hθ : 0 < θ)
    (h : ∃ C : ℝ, ∀ x ≥ (1 : ℝ),
      |P.N x - x| ≤ C * x ^ θ + 3 * x ^ θ * (logStar x : ℝ) + x ^ lagExponent θ)
    {β : ℝ} (hβ : θ < β) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - 1 * x| ≤ C * x ^ β := by
  obtain ⟨C, hC⟩ := h
  set δ := β - θ with hδdef
  have hδ : 0 < δ := by linarith
  refine ⟨|C| + 3 * (1 / δ + 1) + 1, fun x hx => ?_⟩
  rw [one_mul]
  have h0 := hC x hx
  have hxθβ : x ^ θ ≤ x ^ β := Real.rpow_le_rpow_of_exponent_le hx hβ.le
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) θ
  have h1 : C * x ^ θ ≤ |C| * x ^ β :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hxθ).trans
      (mul_le_mul_of_nonneg_left hxθβ (abs_nonneg C))
  have h2 : x ^ θ * (logStar x : ℝ) ≤ (1 / δ + 1) * x ^ β := by
    have := mul_le_mul_of_nonneg_left (logStar_le_rpow hx hδ) hxθ
    have e : x ^ β = x ^ θ * x ^ δ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [e]; linarith
  have h3 : x ^ lagExponent θ ≤ x ^ β := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have : min θ (1 / 2 - θ) ≤ θ := min_le_left _ _
    unfold lagExponent; linarith
  nlinarith

/-- **Theorem 2.1 with part (ii) replaced by the inputs of Theorem 4.10**: (i) as in
Theorem 2.1, and the inputs of Theorem 4.10 for the canonical continuation `zetaCont P 1` on some
punctured half-plane `Re s > a` with `θ < a < 1`. -/
def TheoremAInputs (θ : ℝ) (P : BeurlingSystem) : Prop :=
  (∃ C : ℝ, ∀ x ≥ (1 : ℝ),
      |P.N x - x| ≤ C * x ^ θ + 3 * x ^ θ * (logStar x : ℝ) + x ^ lagExponent θ) ∧
  ∃ a, θ < a ∧ a < 1 ∧ Theorem410Inputs (P.zetaCont 1) a

/-- From (i) and the inputs of Theorem 4.10, the conclusions (i), (ii) of Theorem 2.1 follow:
the continuation is `zetaCont P 1`, and the zeros come from Rouché's theorem. -/
theorem TheoremAInputs.conclusion {θ : ℝ} {P : BeurlingSystem} (hθ : 0 < θ)
    (h : TheoremAInputs θ P) : TheoremAConclusion θ P := by
  obtain ⟨h1, a, hθa, ha1, h410⟩ := h
  obtain ⟨C, hC⟩ := N_bound_of_part_i hθ h1 hθa
  have hcont := P.zetaCont_isZetaContinuation ha1 hC
  exact ⟨h1, a, ha1, P.zetaCont 1, hcont, theorem_4_10 hcont h410⟩

/-- Theorem 2.1, with part (ii) replaced by the inputs of Theorem 4.10 (see `TheoremAInputs`). -/
def Theorem21Inputs : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputs θ (P ω)

theorem theorem21_of_inputs (h : Theorem21Inputs) : Theorem21 := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hθ0 : 0 < θ := by linarith [hθ.1]
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => (hP ω hω).conclusion hθ0⟩

/-- **Corollary 2.2** from the refined assumption `Theorem21Inputs`. -/
theorem corollary_2_2_of_inputs (h : Theorem21Inputs) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_inputs h)

/-- **Corollary 2.2, second form**, from the refined assumption `Theorem21Inputs`. -/
theorem corollary_2_2_one_beta_system_of_inputs (h : Theorem21Inputs) :
    ∃ P : BeurlingSystem,
      (∀ β > (1 / 4 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ β) ∧
      ∀ ε' > (0 : ℝ), ¬ ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.psi x - x| ≤ C * x ^ (1 - ε') :=
  corollary_2_2_one_beta_system' (theorem21_of_inputs h)

end
