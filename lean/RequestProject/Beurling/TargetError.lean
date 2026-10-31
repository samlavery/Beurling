module

public import RequestProject.Beurling.Rankin
public import RequestProject.Beurling.PartI

/-!
# The target `T` (Section 3.2, (6)) and the target error (8)

The rigid density (4) is `ρ_det(u) = Ψ([u, (1+κ)u], X₀)/(κu)`. For `x ≥ X₀` the target (6) is

  `T(x) = X₀ + Ψ(x, X₀) - Ψ(X₀, X₀) + #(A ∩ [X₀, x]) + ∫_{X₀}^x (1 - ρ_det - ρ̄_A + R')`.

We take the counting function `#(A ∩ [X₀, x])` and the capped density `ρ̄_A` of the absorbed set
as data, and write `∫_{X₀}^x R' = R(x) - R(X₀)`. Then

  `T(x) - x - R(x) = E_rig(x) + E_A(x) - R(X₀)`,

with the rigid error `E_rig(x) = Ψ(x, X₀) - Ψ(X₀, X₀) - ∫_{X₀}^x ρ_det` and the absorbed error
`E_A(x) = #(A ∩ [X₀, x]) - ∫_{X₀}^x ρ̄_A`.

* `abs_rigidErr_le` : `|E_rig(x)| ≤ Ψ(2x, X₀)` for `0 < κ ≤ 1` (each rigid `d` carries ramp mass
  at most `1`, and only `d ≤ (1+κ)x` contribute);
* `abs_rigidErr_le_rankin` : with Rankin's bound, `|E_rig(x)| ≤ (2x)^θ ∏_{p<X₀}(1 - p^{-θ})^{-1}`;
* `target_error` : the target error (8) from the absorbed-part bound `|E_A(x)| ≤ 2 x^{θ/2}` of
  Lemma 3.4 (which rests on Lemma 6.26);
* `Theorem21InputsTarget`, `theorem21_of_target`, `corollary_2_2_of_target` : the refined
  hypothesis in which part (i) of Theorem 2.1 is reduced to the absorbed-part bound and the lag
  bound (13) for this concrete target.
-/

@[expose] public section

open Set Filter MeasureTheory Finset Rankin Oscillation

namespace Target

open Classical in
/-- `Ψ([a, b], X₀)`: the number of `X₀`-smooth integers in `[a, b]` (for `b ≥ 0`). -/
noncomputable def rigidCount (X₀ : ℕ) (a b : ℝ) : ℕ :=
  ((Nat.smoothNumbersUpTo ⌊b⌋₊ X₀).filter fun n : ℕ => a ≤ (n : ℝ)).card

/-- The rigid density (4): `ρ_det(u) = Ψ([u, (1+κ)u], X₀)/(κu)`. -/
noncomputable def rhoDet (X₀ : ℕ) (κ u : ℝ) : ℝ := rigidCount X₀ u ((1 + κ) * u) / (κ * u)

/-- The rigid error `E_rig(x) = Ψ(x, X₀) - Ψ(X₀, X₀) - ∫_{X₀}^x ρ_det`. -/
noncomputable def rigidErr (X₀ : ℕ) (κ x : ℝ) : ℝ :=
  ((smoothCount X₀ x : ℝ) - smoothCount X₀ X₀) - ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u

/-- The target (6) for `x ≥ X₀` (and `⌊x⌋` below `X₀`), with the absorbed count `cntA`, the capped
absorbed density `rhoA` and the oscillation `R` as data. -/
noncomputable def target (X₀ : ℕ) (κ : ℝ) (cntA rhoA R : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < X₀ then (⌊x⌋₊ : ℝ) else
    X₀ + ((smoothCount X₀ x : ℝ) - smoothCount X₀ X₀) + cntA x +
      ((x - X₀) - (∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u) - (∫ u in (X₀ : ℝ)..x, rhoA u) +
        (R x - R X₀))

lemma smoothCount_mono (X₀ : ℕ) {x y : ℝ} (hxy : x ≤ y) : smoothCount X₀ x ≤ smoothCount X₀ y := by
  unfold smoothCount
  apply Finset.card_le_card
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans (Nat.floor_mono hxy), hn.2⟩

lemma integral_rhoDet_nonneg (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hX : (X₀ : ℝ) ≤ x) :
    0 ≤ ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u := by
  refine intervalIntegral.integral_nonneg hX fun u hu => ?_
  have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg _) hu.1
  unfold rhoDet
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hu0)

/-- The total ramp mass of the rigid integers up to `x` is at most `Ψ(2x, X₀)`. -/
lemma integral_rhoDet_le (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) :
    ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u ≤ smoothCount X₀ (2 * x) := by
  classical
  set S := Nat.smoothNumbersUpTo ⌊2 * x⌋₊ X₀ with hS
  have hX01 : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX0
  have hS0 : ∀ n ∈ S, (0 : ℝ) < n := by
    intro n hn
    rw [hS, Nat.mem_smoothNumbersUpTo] at hn
    exact_mod_cast Nat.pos_of_ne_zero hn.2.1
  set c : ℕ → ℝ := fun n => (1 + κ) / (κ * n) with hc
  set G : ℝ → ℝ := fun u => ∑ n ∈ S, (Icc ((n : ℝ) / (1 + κ)) n).indicator (fun _ => c n) u
    with hG
  -- pointwise domination
  have hpt : ∀ u ∈ Ioc (X₀ : ℝ) x, rhoDet X₀ κ u ≤ G u := by
    intro u hu
    have hu1 : 1 ≤ u := le_trans hX01 hu.1.le
    have hu0 : 0 < u := by linarith
    have hκu : 0 < κ * u := mul_pos hκ hu0
    set P : ℕ → Prop := fun n => u ≤ n ∧ (n : ℝ) ≤ (1 + κ) * u with hP
    have hsub : ((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)) ⊆
        S.filter P := by
      intro n hn
      rw [Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
      have h1 : (n : ℝ) ≤ (1 + κ) * u :=
        (Nat.cast_le.mpr hn.1.1).trans (Nat.floor_le (by positivity))
      rw [Finset.mem_filter, hS, Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨Nat.le_floor ?_, hn.1.2⟩, hn.2, h1⟩
      nlinarith [hu.2]
    have hcard := Finset.card_le_card hsub
    unfold rhoDet rigidCount
    calc (((Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X₀).filter fun n : ℕ => u ≤ (n : ℝ)).card : ℝ)
          / (κ * u)
        ≤ ((S.filter P).card : ℝ) / (κ * u) := by
          gcongr
      _ = ∑ n ∈ S, if P n then 1 / (κ * u) else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ G u := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hPn : P n
          · rw [if_pos hPn]
            have hmem : u ∈ Icc ((n : ℝ) / (1 + κ)) n :=
              ⟨by rw [div_le_iff₀ (by linarith)]; linarith [hPn.2], hPn.1⟩
            rw [Set.indicator_of_mem hmem, hc]
            simp only
            rw [div_le_div_iff₀ hκu (mul_pos hκ (hS0 n hn))]
            nlinarith [hPn.2]
          · rw [if_neg hPn]
            exact Set.indicator_nonneg (fun _ _ => by
              simp only [hc]; exact div_nonneg (by linarith) (mul_nonneg hκ.le (hS0 n hn).le)) _
  -- integrability of the majorant on `Ioc X₀ x`
  have hind : ∀ n : ℕ, IntegrableOn (fun u => (Icc ((n : ℝ) / (1 + κ)) n).indicator
      (fun _ => c n) u) (Ioc (X₀ : ℝ) x) := fun n =>
    (integrableOn_const (C := c n) measure_Ioc_lt_top.ne).indicator measurableSet_Icc
  have hGint : IntegrableOn G (Ioc (X₀ : ℝ) x) := by
    simp only [hG]
    exact integrable_finset_sum _ fun n _ => hind n
  have hint_le : ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u ≤ ∫ u in Ioc (X₀ : ℝ) x, G u := by
    rw [intervalIntegral.integral_of_le hX]
    refine integral_mono_of_nonneg ?_ hGint ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg _) hu.1.le
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hu0)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
  have hG_le : ∫ u in Ioc (X₀ : ℝ) x, G u ≤ (S.card : ℝ) := by
    simp only [hG]
    rw [integral_finset_sum _ fun n _ => hind n]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 := hS0 n hn
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    have hvol : (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((n : ℝ) / (1 + κ)) n) ≤
        n - n / (1 + κ) := by
      unfold Measure.real
      apply ENNReal.toReal_le_of_le_ofReal
      · have : (n : ℝ) / (1 + κ) ≤ n := div_le_self hn0.le (by linarith)
        linarith
      · refine (Measure.restrict_le_self _).trans ?_
        rw [Real.volume_Icc]
    have hc0 : 0 ≤ c n := div_nonneg (by linarith) (mul_nonneg hκ.le hn0.le)
    calc (volume.restrict (Ioc (X₀ : ℝ) x)).real (Icc ((n : ℝ) / (1 + κ)) n) * c n
        ≤ (n - n / (1 + κ)) * c n := mul_le_mul_of_nonneg_right hvol hc0
      _ = 1 := by
          simp only [hc]
          field_simp
          ring
  calc ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u ≤ ∫ u in Ioc (X₀ : ℝ) x, G u := hint_le
    _ ≤ (S.card : ℝ) := hG_le
    _ = smoothCount X₀ (2 * x) := rfl

/-- **The rigid part of the target error**: `|E_rig(x)| ≤ Ψ(2x, X₀)`. -/
theorem abs_rigidErr_le (X₀ : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) :
    |rigidErr X₀ κ x| ≤ smoothCount X₀ (2 * x) := by
  have hx0 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hX0) hX
  have h1 : (smoothCount X₀ (X₀ : ℝ) : ℝ) ≤ smoothCount X₀ x := by
    exact_mod_cast smoothCount_mono X₀ hX
  have h2 : (smoothCount X₀ x : ℝ) ≤ smoothCount X₀ (2 * x) := by
    exact_mod_cast smoothCount_mono X₀ (by linarith)
  have h3 := integral_rhoDet_nonneg X₀ hκ hX
  have h4 := integral_rhoDet_le X₀ hκ hκ1 hX0 hX
  have h5 : (0 : ℝ) ≤ smoothCount X₀ (X₀ : ℝ) := Nat.cast_nonneg _
  unfold rigidErr
  rw [abs_le]
  constructor <;> linarith

/-- With Rankin's bound: `|E_rig(x)| ≤ (2x)^θ ∏_{p<X₀} (1 - p^{-θ})^{-1}` for `θ > 0`. -/
theorem abs_rigidErr_le_rankin (X₀ : ℕ) {κ x θ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hX0 : 1 ≤ X₀)
    (hX : (X₀ : ℝ) ≤ x) (hθ : 0 < θ) :
    |rigidErr X₀ κ x| ≤ (2 * x) ^ θ * rankinConst X₀ θ := by
  have hx0 : (0 : ℝ) ≤ 2 * x := by
    have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    linarith
  exact (abs_rigidErr_le X₀ hκ hκ1 hX0 hX).trans (smoothCount_le_rankin X₀ hθ hx0)

/-- The identity `T(x) - x - R(x) = E_rig(x) + E_A(x) - R(X₀)` for `x ≥ X₀`. -/
lemma target_sub_eq (X₀ : ℕ) (κ : ℝ) (cntA rhoA R : ℝ → ℝ) {x : ℝ} (hX : (X₀ : ℝ) ≤ x) :
    target X₀ κ cntA rhoA R x - x - R x =
      rigidErr X₀ κ x + (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u) - R X₀ := by
  unfold target rigidErr
  rw [if_neg (not_lt.mpr hX)]
  ring

/-- **The target error (8)**: if the oscillation vanishes at `X₀` and the absorbed error satisfies
`|#(A ∩ [X₀,x]) - ∫_{X₀}^x ρ̄_A| ≤ 2 x^{θ/2}` (Lemma 3.4, absorbed part), then
`|T(x) - x - R(x)| ≤ C x^θ + 2 x^{θ/2}` for `x ≥ X₀`, with `C = 2^θ ∏_{p<X₀}(1 - p^{-θ})^{-1}`. -/
theorem target_error (X₀ : ℕ) {κ θ : ℝ} (cntA rhoA R : ℝ → ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hX0 : 1 ≤ X₀) (hθ : 0 < θ) (hR0 : R X₀ = 0)
    (hA : ∀ x ≥ (X₀ : ℝ), |cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u| ≤ 2 * x ^ (thetaB θ)) :
    ∀ x ≥ (X₀ : ℝ), |target X₀ κ cntA rhoA R x - x - R x| ≤
      (2 ^ θ * rankinConst X₀ θ) * x ^ θ + 2 * x ^ (thetaB θ) := by
  intro x hx
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
  rw [target_sub_eq X₀ κ cntA rhoA R hx, hR0, sub_zero]
  have h1 := abs_rigidErr_le_rankin X₀ hκ hκ1 hX0 hx hθ
  rw [Real.mul_rpow (by norm_num) hx0] at h1
  have h2 := hA x hx
  calc |rigidErr X₀ κ x + (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u)|
      ≤ |rigidErr X₀ κ x| + |cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u| := abs_add_le _ _
    _ ≤ (2 ^ θ * rankinConst X₀ θ) * x ^ θ + 2 * x ^ (thetaB θ) := by nlinarith

lemma osc_eq_zero_of_le {θ : ℝ} {α γ xp : ℕ → ℝ} (h : Spacing xp) {x : ℝ} (hx : 0 < x)
    (hxp : x ≤ xp 0) : osc θ α γ xp x = 0 := by
  unfold osc
  rw [show (fun k => oscTerm θ (α k) (γ k) (xp k) x) = fun _ => 0 from funext fun k =>
    oscTerm_eq_zero_of_le hx (hxp.trans (h.strictMono.monotone (Nat.zero_le k)))]
  exact tsum_zero

end Target

open Target

/-- The inputs for Theorem 2.1(i) with the **concrete target** (6): for some window `κ ∈ (0, 1]`,
absorbed count `cntA` and capped absorbed density `rhoA`, and oscillation `R = osc θ α γ x⁺`
(`|α_k| ≤ 2`, spacing, switched on above `X₀`):

* the absorbed part of the target error (Lemma 3.4, resting on Lemma 6.26):
  `|#(A ∩ [X₀, x]) - ∫_{X₀}^x ρ̄_A| ≤ 2 x^{θ/2}`;
* the lag bound (13): `|N_P(x) - T(x)| ≤ x^η`,

both for `x ≥ X₀`. -/
def PartIInputsTarget (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (cntA rhoA : ℝ → ℝ) (α γ xp : ℕ → ℝ), 0 < κ ∧ κ ≤ 1 ∧ Spacing xp ∧
    (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ x ≥ (X₀ : ℝ), |cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u| ≤ 2 * x ^ (thetaB θ)) ∧
    (∀ x ≥ (X₀ : ℝ), |P.N x - target X₀ κ cntA rhoA (osc θ α γ xp) x| ≤ x ^ lagExponent θ)

theorem PartIInputsTarget.partIInputs {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem} (hθ : 0 < θ)
    (hX0 : 1 ≤ X₀) (h : PartIInputsTarget θ X₀ P) : PartIInputs θ X₀ P := by
  obtain ⟨κ, cntA, rhoA, α, γ, xp, hκ, hκ1, hsp, hα, hxp, hA, hD⟩ := h
  have hR0 : osc θ α γ xp X₀ = 0 :=
    osc_eq_zero_of_le hsp (by exact_mod_cast hX0) hxp
  exact ⟨target X₀ κ cntA rhoA (osc θ α γ xp), α, γ, xp, 2 ^ θ * rankinConst X₀ θ, hsp, hα,
    target_error X₀ cntA rhoA _ hκ hκ1 hX0 hθ hR0 hA, hD⟩

/-- Refined inputs for one system, with the concrete target (6). -/
def TheoremAInputsTarget (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ ∃ a, θ < a ∧ a < 1 ∧ Theorem410Inputs (P.zetaCont 1) a

/-- **Theorem 2.1, refined hypothesis with the concrete target**: as `Theorem21Inputs'`, but
part (i) is reduced to the absorbed part of the target error and the lag bound (13) for the
concrete target (6). -/
def Theorem21InputsTarget : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsTarget θ X₀ (P ω)

theorem theorem21Inputs'_of_target (h : Theorem21InputsTarget) : Theorem21Inputs' := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hX0 : 1 ≤ X₀ := by
    have : (1 : ℝ) ≤ X₀ := le_trans (Real.one_le_exp (by norm_num)) h1
    exact_mod_cast this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.partIInputs (by linarith [hθ.1]) hX0, (hP ω hω).2⟩⟩

/-- The refined hypothesis with the concrete target implies Theorem 2.1. -/
theorem theorem21_of_target (h : Theorem21InputsTarget) : Theorem21 :=
  theorem21_of_inputs' (theorem21Inputs'_of_target h)

/-- **Corollary 2.2** from the refined hypothesis with the concrete target. -/
theorem corollary_2_2_of_target (h : Theorem21InputsTarget) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_target h)

end
