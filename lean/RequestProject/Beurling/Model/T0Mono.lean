module

public import RequestProject.Beurling.Model.Valid
public import RequestProject.Beurling.LocalPNT.Theorem524

/-!
# `T₀` is non-decreasing on `[X₀, ∞)` (Lemma 3.3) and Theorem 5.24 for the construction

The `A`-free target `T₀ = target X₀ κ 0 0 R` of §5.6 (`LocalPNT.T0`) splits on `[X₀, ∞)` as
`X₀ + J + C` (`target_eq_split`), with `J(x) = Ψ(x, X₀) - Ψ(X₀, X₀)` non-decreasing and
`C(x') - C(x) ≥ 0.08 (x' - x)/log x' ≥ 0` (`contPart_lower`, Lemma 3.3, with the empty absorbed
set: the capped density of `∅` vanishes on `[X₀, ∞)`).

* `T0_mono_designed` : `T₀` is monotone on `[X₀, ∞)` for designed heights `γ`, the designed
  amplitudes and the switch-on points `x_k = switchOn X₀ k`, under (84) (`ShortIntervalPNTFrom`);
* `theorem_5_24_data` : `LocalPNT.theorem_5_24_of_lag` with `hmono`, `hα`, `h0`, `hsp`
  discharged, for the heights and amplitudes `gammaD`, `alphaD` of any prime data (in
  particular the realised data `DM (Mcl θ X₀ ω) (Ucl ω)` of the construction).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero

namespace BModel

/-- `Ψ(x, X₀)` is non-decreasing in `x`. -/
lemma smoothCount_mono (X₀ : ℕ) {x x' : ℝ} (h : x ≤ x') :
    (Rankin.smoothCount X₀ x : ℝ) ≤ Rankin.smoothCount X₀ x' := by
  unfold Rankin.smoothCount
  exact_mod_cast Finset.card_le_card fun d hd => by
    rw [Nat.mem_smoothNumbersUpTo] at hd ⊢
    exact ⟨hd.1.trans (Nat.floor_mono h), hd.2⟩

/-- On `[X₀, ∞)` the continuous part with `ρ̄_A = 0` is that with the empty absorbed set. -/
lemma contPart_zero_eq {X₀ : ℕ} (hX1 : (1 : ℝ) < X₀) (κ b : ℝ) (u R : ℝ → ℝ) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) :
    contPart X₀ κ (fun _ => 0) R x = contPart X₀ κ (absorbedDensityCap b ∅ u) R x := by
  unfold contPart
  congr 2
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hx] at hv
  have hlog : 0 < Real.log v := Real.log_pos (by linarith [hv.1])
  simp only [absorbedDensityCap, absorbedDensity, absorbedBump, mem_empty_iff_false, if_false,
    tsum_zero]
  exact (min_eq_left (by positivity)).symm

/-- **`T₀` is non-decreasing on `[X₀, ∞)`** (positivity of the target, Lemma 3.3), for designed
heights `γ`, the designed amplitudes and `x_k = switchOn X₀ k`. -/
theorem T0_mono_designed {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) {X₀ : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (hHB : ShortIntervalPNTFrom X₀) {γ : ℕ → ℝ}
    (hγ : DesignedRange θ X₀ γ) :
    MonotoneOn (LocalPNT.T0 θ X₀ (amplitudes θ kappa0Param (switchOn X₀) γ) γ (switchOn X₀))
      (Ici (X₀ : ℝ)) := by
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  intro x hx x' hx' hxx
  simp only [mem_Ici] at hx hx'
  unfold LocalPNT.T0
  rw [target_eq_split hx, target_eq_split hx']
  have hJ : jumpPart X₀ (fun _ => 0) x ≤ jumpPart X₀ (fun _ => 0) x' := by
    unfold jumpPart
    linarith [smoothCount_mono X₀ hxx]
  have hC := contPart_lower hθ hX hγ ∅ (fun x => by simp) hHB hx hxx
  rw [← contPart_zero_eq hX1, ← contPart_zero_eq hX1] at hC
  · have hpos : 0 ≤ 0.08 * (x' - x) / Real.log x' := by
      have := Real.log_pos (by linarith : (1 : ℝ) < x')
      have : 0 ≤ x' - x := by linarith
      positivity
    linarith
  · exact hx
  · exact hx'

/-- **Theorem 5.24 on `Good(<z)` for the designed oscillation of prime data `D`**:
`LocalPNT.theorem_5_24_of_lag` at `α = alphaD`, `γ = gammaD`, `x_k = switchOn X₀ k`, with the
positivity margin (`T₀` monotone, Lemma 3.3), `|α_k| ≤ 2`, `x₀ ≥ e^{X₀²}` and the spacing
discharged. The remaining inputs are those of `theorem_5_24_of_lag` (the queue-lag bound up to
the horizon, the absorbed-count bound and the floor of `P`) and (84). -/
theorem theorem_5_24_data {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} (D : PrimeData)
    {Xm zc y : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hev : Even X₀) (hHB : ShortIntervalPNTFrom X₀) (cntA rhoA : ℝ → ℝ)
    (hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ Xm) (hXmX : Xm ≤ X₀)
    (hfl : ∀ u, u < Xm → P.N u = ⌊u⌋₊)
    (hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |P.N u - Target.target X₀ (LocalPNT.kap X₀) cntA rhoA
        (osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀)) u| ≤ u ^ lagExponent θ)
    (hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → |cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v| ≤ 2 * u ^ (θ / 2))
    (hy : (X₀ : ℝ) ≤ y) (hyz : y ≤ zc) :
    LocalPNT.Theorem524Concl P X₀ y :=
  LocalPNT.theorem_5_24_of_lag hθ hX hev (fun k => abs_alphaD_le hX D k) le_rfl
    (switchOn_spacing X₀).exp_le (T0_mono_designed hθ hX hHB (gammaD_range hX D)) cntA rhoA
    hXm hXmX hfl hlag hA hy hyz

end BModel
