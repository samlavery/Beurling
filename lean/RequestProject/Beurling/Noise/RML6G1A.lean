module

public import RequestProject.Beurling.Noise.MarginChain
public import RequestProject.Beurling.BaseRange.Mu0b

/-!
# Field `g1` of `BModel.RealMarginLoc`, range (A): eq. (86) and the `σ_𝒜` response

The range-(A) part of `KR.Chain.G1At` (the residual inputs of Proposition 5.35) asks for a
remainder `r_A` with

* eq. (86): `ρ^sh T'(y) = MA[ℙ](y) + ρ_edge(y) + R_sh μ₀(y) + R_sh μ₁(y) + r_A`, and
* `|r_A log y| ≤ e^{-80}`,

for `log y ≤ X₀^{1/100}`. With the realised objects of §7 (`BaseRange.mu0R`, `KR.Sharp.mu1R`,
`KR.Sharp.rhoEdge`), eq. (86) is BaseRange's `shdecomp` applied to the base source
`S = 1_{[X₀,∞)}(1 - ρ_det)` (`BaseRange.srcBase`), and the remainder is the response
`r_A = ρ^sh(T' - S)(y)` (`g1A_of`). On range (A) no designed oscillation is active
(`x₁ ≥ exp(X₀²)`), so `T' - S = σ_𝒜` there and `|r_A log y| ≤ e^{-80}` is the paper's `σ_𝒜`
bullet in the proof of Proposition 5.35(A). That bound is the named input `SigmaAResp`
(owner: the Model agent, which owns `T'`, `ρ_det`, `R'` and `σ_𝒜`); the absorbed set enters only
through it.
-/

@[expose] public section

open Real Finset

namespace KR.RML6

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ}

/-- `ρ^sh` is additive in the source. -/
lemma rhoSh_sub (x : ℝ) (f g : ℝ → ℝ) :
    rhoSh P tw X0m x (fun t => f t - g t) = rhoSh P tw X0m x f - rhoSh P tw X0m x g := by
  unfold rhoSh
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- **The `σ_𝒜` response on range (A)** (proof of Proposition 5.35(A), third bullet; owner:
Model): for `log y ≤ X₀^{1/100}`, the response of `T' - 1_{[X₀,∞)}(1 - ρ_det)` (which is `σ_𝒜` on
range (A), as `R' = 0` below `x₁ ≥ exp(X₀²)`) satisfies
`log y · |ρ^sh(T' - S)(y)| ≤ e^{-80}`. -/
def SigmaAResp (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (Tp : ℝ → ℝ) (y : ℝ) :
    Prop :=
  Real.log y ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) →
    |rhoSh P tw X0m y (fun t => Tp t - BaseRange.srcBase X0 t) * Real.log y| ≤ Real.exp (-80)

/-- **Range (A) of the field `g1`**: eq. (86) from `BaseRange.shdecomp`, with the realised
`ρ_edge`, `μ₀`, `μ₁`, and the remainder `r_A = ρ^sh(T' - S)(y)` bounded by `SigmaAResp`. -/
theorem g1A_of (hXm : 0 < X0m) (X0 : ℕ) (hX0m : X0m ≤ X0) {y : ℝ} (hy : (X0 : ℝ) ≤ y)
    (Tp : ℝ → ℝ) (hresp : SigmaAResp P tw X0m X0 Tp y) :
    ∃ rA : ℝ,
      (Real.log y ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) →
        rhoSh P tw X0m y Tp = BaseRange.MAP X0 (Construction.kappaParam X0) y +
          KR.Sharp.rhoEdge P tw X0m X0 y + rhoSh P tw X0m y (BaseRange.mu0R P tw X0m X0) +
          rhoSh P tw X0m y (KR.Sharp.mu1R P tw X0m X0) + rA) ∧
      (Real.log y ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) → |rA * Real.log y| ≤ Real.exp (-80)) := by
  refine ⟨rhoSh P tw X0m y (fun t => Tp t - BaseRange.srcBase X0 t), fun _ => ?_, hresp⟩
  have hd := BaseRange.shdecomp P tw hXm X0 (hX0m.trans hy)
  rw [KR.Sharp.Rsh_eq_rhoSh, KR.Sharp.Rsh_eq_rhoSh, KR.Sharp.Rsh_eq_rhoSh] at hd
  have hMA : BaseRange.MAPcut X0 y = BaseRange.MAP X0 (Construction.kappaParam X0) y := by
    unfold BaseRange.MAPcut; rw [if_pos hy]
  rw [hMA] at hd
  rw [rhoSh_sub, ← hd]
  ring

end KR.RML6

end
