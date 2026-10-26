module

public import RequestProject.Beurling.Lemmas

/-!
# Theorem 2.1 (Theorem A) and Corollary 2.2

The 145-page construction of the paper (Sections 3–7 and the computer-assisted Appendix B)
is not formalized. Following the request, everything that is not available in Mathlib is
taken as an explicit **hypothesis** (we never add Lean `axiom`s, for soundness reasons):

* `Theorem21` : the statement of Theorem 2.1 (the random system exists, and on an event of
  probability `≥ 1 - 1.5 / log X₀` it satisfies (i) and (ii));
* `Remark12_ba` : direction (b) ⇒ (a) of Remark 1.2 (a power saving in the prime number
  theorem gives a zero-free half-plane).

From these we prove, in Lean, the parts of the paper's argument that are pure logic and
elementary analysis:

* `exists_realisation` : one realisation `ω ∈ G` exists (since `1 - 1.5/log X₀ > 0`);
* `TheoremAConclusion.re_tendsto_one` : `Re ρ_k = 1 - (3 log log x_k + O(1)) / log x_k → 1`;
* `TheoremAConclusion.N_bound` : `N(x) = x + O(x^β)` for every `β > θ` (absorbing `log* x`);
* `TheoremAConclusion.not_hasZeroFreeHalfPlane` : no zero-free half-plane (identity theorem);
* `corollary_2_2` : the answer to Question Q is negative;
* `corollary_2_2_one_beta_system` : a discrete `[1, β]`-system with `β ≤ 1/4 < 1/2` exists;
* `theorem21_part_i_of_bounds` : the derivation of Theorem 2.1(i) from the target error (8),
  the bound `|R| ≤ 2 x^θ log* x` of Lemma 3.4 and the lag bound (13).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory BeurlingSystem

/-- The lag exponent `η := min(θ, 1/2 - θ) / 2` of (13). -/
noncomputable def lagExponent (θ : ℝ) : ℝ := min θ (1 / 2 - θ) / 2

/-- The conclusions (i) and (ii) of Theorem 2.1 for one fixed (realised) system `P`:

(i) `|N_P(x) - x| ≤ C x^θ + 3 x^θ log* x + x^η` for all `x ≥ 1`;

(ii) `ζ_P` continues analytically to a punctured half-plane `Re s > a` (`a < 1`) and has zeros
`ρ_k` there with `Re ρ_k = 1 - (3 log log x_k + O(1)) / log x_k` along a sequence `x_k → ∞`. -/
def TheoremAConclusion (θ : ℝ) (P : BeurlingSystem) : Prop :=
  (∃ C : ℝ, ∀ x ≥ (1 : ℝ),
      |P.N x - x| ≤ C * x ^ θ + 3 * x ^ θ * (logStar x : ℝ) + x ^ lagExponent θ) ∧
  (∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, P.IsZetaContinuation a F ∧
    ∃ (ρ : ℕ → ℂ) (xk : ℕ → ℝ) (C : ℝ), Tendsto xk atTop atTop ∧
      (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
      ∀ k, |(1 - (ρ k).re) * Real.log (xk k) - 3 * Real.log (Real.log (xk k))| ≤ C)

/-- **Theorem 2.1 (Theorem A)**, taken as a hypothesis. For every `θ ∈ [1/4, 1/2 - 10⁻⁴]`
there is a threshold `X_Hux` such that for every even integer `X₀ ≥ max(e^{10^8}, X_Hux)` the
random system `P` of Section 3 (on some probability space) satisfies the conclusions (i), (ii)
on an event `G` of probability at least `1 - 1.5 / log X₀`. -/
def Theorem21 : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAConclusion θ (P ω)

/-- **Remark 1.2, direction (b) ⇒ (a)**, taken as a hypothesis: if `N_P(x) = A x + O(x^β)`
with `A > 0`, `β < 1/2`, and `ψ_P(x) = x + O(x^{1-ε'})` for some `ε' > 0`, then `ζ_P` is
zero-free on some half-plane `Re s > 1 - ε`. -/
def Remark12_ba : Prop :=
  ∀ (P : BeurlingSystem) (A β : ℝ), 0 < A → β < 1 / 2 →
    (∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - A * x| ≤ C * x ^ β) →
    ∀ ε' > (0 : ℝ), (∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.psi x - x| ≤ C * x ^ (1 - ε')) →
      P.HasZeroFreeHalfPlane

/-- "Fix any `ω ∈ G`": since `P(G) ≥ 1 - 1.5 / log X₀ > 0`, Theorem 2.1 yields a fixed
(deterministic) discrete Beurling system satisfying (i) and (ii). -/
theorem exists_realisation (h : Theorem21) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) :
    ∃ P : BeurlingSystem, TheoremAConclusion θ P := by
  obtain ⟨XHux, hX⟩ := h θ hθ
  set n : ℕ := ⌈max (Real.exp (10 ^ 8)) XHux⌉₊
  have hn : max (Real.exp (10 ^ 8)) XHux ≤ ((2 * n : ℕ) : ℝ) := by
    have := Nat.le_ceil (max (Real.exp (10 ^ 8)) XHux)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast; linarith
  have h1 : Real.exp (10 ^ 8) ≤ ((2 * n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  obtain ⟨Ω, _, μ, P, G, -, hG, hP⟩ :=
    hX (2 * n) (even_two_mul n) h1 ((le_max_right _ _).trans hn)
  have hlog : (10 : ℝ) ^ 8 ≤ Real.log ((2 * n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hpos : 0 < 1 - 1.5 / Real.log ((2 * n : ℕ) : ℝ) := by
    have hl : 0 < Real.log ((2 * n : ℕ) : ℝ) := by linarith [show (0:ℝ) < 10 ^ 8 by norm_num]
    rw [sub_pos, div_lt_one hl]
    linarith [show (1.5 : ℝ) < 10 ^ 8 by norm_num]
  have hμ : μ G ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hG)
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measure_ne_zero hμ
  exact ⟨P ω, hP ω hω⟩

namespace TheoremAConclusion

variable {θ : ℝ} {P : BeurlingSystem}

/-- Theorem 2.1(ii): the designed zeros satisfy `Re ρ_k → 1`. -/
theorem re_tendsto_one (h : TheoremAConclusion θ P) :
    ∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, P.IsZetaContinuation a F ∧ ∃ ρ : ℕ → ℂ,
      (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
      Tendsto (fun k => (ρ k).re) atTop (𝓝 1) := by
  obtain ⟨a, ha, F, hF, ρ, xk, C, hx, hz, hb⟩ := h.2
  exact ⟨a, ha, F, hF, ρ, hz, tendsto_one_of_log_asymptotic _ xk C hx hb⟩

/-- Theorem 2.1(i) gives `N_P(x) = x + O(x^β)` for every `β > θ`. -/
theorem N_bound (h : TheoremAConclusion θ P) (hθ : 0 < θ) {β : ℝ} (hβ : θ < β) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - 1 * x| ≤ C * x ^ β := by
  obtain ⟨C, hC⟩ := h.1
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

/-- Theorem 2.1(ii) implies that `ζ_P` is zero-free in no half-plane `Re s > 1 - ε`. -/
theorem not_hasZeroFreeHalfPlane (h : TheoremAConclusion θ P) : ¬ P.HasZeroFreeHalfPlane := by
  rintro ⟨ε, hε, F', hF', hnz⟩
  obtain ⟨a, ha, F, hF, ρ, hz, hre⟩ := h.re_tendsto_one
  have hb : max (1 - ε) a < 1 := max_lt (by linarith) ha
  obtain ⟨k, hk⟩ := (hre.eventually (lt_mem_nhds hb)).exists
  have hmem : ρ k ∈ puncturedHalfPlane (max (1 - ε) a) := ⟨hk, (hz k).1.2⟩
  have heq := hF'.eqOn hF hmem
  exact hnz (ρ k) (puncturedHalfPlane_mono (le_max_left _ _) hmem) (heq.trans (hz k).2)

end TheoremAConclusion

/-- **Corollary 2.2**: assuming Theorem 2.1, the answer to Question Q is negative. -/
theorem corollary_2_2 (h : Theorem21) : ¬ QuestionQ := by
  intro hQ
  have hθ : (1 / 4 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000) := by
    constructor <;> norm_num
  obtain ⟨P, hP⟩ := exists_realisation h hθ
  obtain ⟨C, hC⟩ := hP.N_bound (by norm_num) (β := 1 / 3) (by norm_num)
  exact hP.not_hasZeroFreeHalfPlane (hQ P ⟨1, one_pos, 1 / 3, by norm_num, C, hC⟩)

/-- **Corollary 2.2, second form**: assuming Theorem 2.1 and Remark 1.2 (b) ⇒ (a), there is a
discrete `[1, β]`-system with `β ≤ 1/4 < 1/2`: `N_P(x) = x + O(x^β)` for every `β > 1/4`,
while `ψ_P(x) - x` admits no power saving `O(x^{1-ε'})`. -/
theorem corollary_2_2_one_beta_system (h : Theorem21) (hR : Remark12_ba) :
    ∃ P : BeurlingSystem,
      (∀ β > (1 / 4 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ β) ∧
      ∀ ε' > (0 : ℝ), ¬ ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.psi x - x| ≤ C * x ^ (1 - ε') := by
  have hθ : (1 / 4 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000) := by
    constructor <;> norm_num
  obtain ⟨P, hP⟩ := exists_realisation h hθ
  refine ⟨P, fun β hβ => ?_, fun ε' hε' hψ => ?_⟩
  · obtain ⟨C, hC⟩ := hP.N_bound (by norm_num) hβ
    exact ⟨C, fun x hx => by simpa using hC x hx⟩
  · obtain ⟨C, hC⟩ := hP.N_bound (by norm_num) (β := 1 / 3) (by norm_num)
    exact hP.not_hasZeroFreeHalfPlane (hR P 1 (1 / 3) one_pos (by norm_num) ⟨C, hC⟩ ε' hε' hψ)

/-- **Proof of Theorem 2.1(i)** from the section-level bounds. Write `D := N - T` (the lag),
`E := T - x - R` (the target error) and `R` (the oscillations). If, for `x ≥ X₀`,
the target error (8) `|E(x)| ≤ C₀ x^θ + 2 x^{θ/2}`, the oscillation bound
`|R(x)| ≤ 2 x^θ log* x` (Lemma 3.4) and the lag bound (13) `|D(x)| ≤ x^η` hold, and `N` is
bounded on `[1, X₀)`, then `|N(x) - x| ≤ C x^θ + 3 x^θ log* x + x^η` for all `x ≥ 1`.
(Here `X₀^{θ/2} ≥ 2`, which holds for the paper's `X₀ ≥ e^{10^8}`.) -/
theorem theorem21_part_i_of_bounds {θ η C₀ X₀ : ℝ} (N T R : ℝ → ℝ) (hθ : 0 < θ)
    (hX₀ : 1 < X₀) (hX₀θ : 2 ≤ X₀ ^ (θ / 2))
    (hE : ∀ x ≥ X₀, |T x - x - R x| ≤ C₀ * x ^ θ + 2 * x ^ (θ / 2))
    (hR : ∀ x ≥ X₀, |R x| ≤ 2 * x ^ θ * (logStar x : ℝ))
    (hD : ∀ x ≥ X₀, |N x - T x| ≤ x ^ η)
    (hN : ∃ B : ℝ, ∀ x, 1 ≤ x → x < X₀ → |N x| ≤ B) :
    ∃ C : ℝ, ∀ x ≥ (1 : ℝ),
      |N x - x| ≤ C * x ^ θ + 3 * x ^ θ * (logStar x : ℝ) + x ^ η := by
  obtain ⟨B, hB⟩ := hN
  refine ⟨|C₀| + |B| + X₀, fun x hx => ?_⟩
  have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ.le
  have hL : (0 : ℝ) ≤ logStar x := Nat.cast_nonneg _
  have hxη : 0 ≤ x ^ η := Real.rpow_nonneg (by linarith) η
  have hC : 0 ≤ |C₀| + |B| + X₀ := by positivity
  have hCx : |C₀| + |B| + X₀ ≤ (|C₀| + |B| + X₀) * x ^ θ := le_mul_of_one_le_right hC hxθ
  have hθL : 0 ≤ x ^ θ * (logStar x : ℝ) := by positivity
  rcases lt_or_ge x X₀ with hlt | hge
  · have h1 := hB x hx hlt
    have h2 : |N x - x| ≤ |N x| + |x| := abs_sub _ _
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at h2
    have := abs_nonneg C₀
    have := le_abs_self B
    linarith
  · have hL1 : (1 : ℝ) ≤ logStar x := by exact_mod_cast one_le_logStar (by linarith)
    have hx2 : 2 ≤ x ^ (θ / 2) :=
      hX₀θ.trans (Real.rpow_le_rpow (by linarith) hge (by linarith))
    have hsq : x ^ θ = x ^ (θ / 2) * x ^ (θ / 2) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    have h2 : 2 * x ^ (θ / 2) ≤ x ^ θ := by
      rw [hsq]; have : 0 ≤ x ^ (θ / 2) := by linarith
      nlinarith
    have h3 : x ^ θ ≤ x ^ θ * (logStar x : ℝ) := le_mul_of_one_le_right (by linarith) hL1
    have h4 : C₀ * x ^ θ ≤ (|C₀| + |B| + X₀) * x ^ θ := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      have := le_abs_self C₀; have := abs_nonneg B; linarith
    have e : N x - x = (N x - T x) + (T x - x - R x) + R x := by ring
    have htri : |N x - x| ≤ |N x - T x| + |T x - x - R x| + |R x| := by
      rw [e]; exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans
        (by linarith)
    have := hE x hge
    have := hR x hge
    have := hD x hge
    linarith

end
