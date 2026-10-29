module

public import RequestProject.Beurling.BaseRange.KptF1

/-!
# Lemma 7.3(c) for the realised `μ₁`, and the realised inputs of Lemma 7.3

* `lemma73c_realised` : **Lemma 7.3(c)** (`BaseRange.Lemma73c`) for
  `μ₁ = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})` (`KR.Sharp.mu1R`), from (84), (HBS) on `[1, Z]` with
  `xmax/X₀ ≤ Z`, `X₀/2 ≤ X₀⁻ ≤ X₀` and the decision-order bound `labelVal p ≤ 2 t(p)`:
  the two named halves of `KR.Sharp.lemma73c_of` are `kshQF1Second` and `kptF1Bound`;
* `lemma73Inputs_realised` : `BaseRange.Lemma73Inputs` for the realised `μ₁`, `ρ_edge`, with the
  remaining inputs (b) (`Lemma73b`) and (d)(iii) (`Lemma73diii`).
-/

@[expose] public section

namespace BaseRange

variable (P : BeurlingSystem)

/-- **Lemma 7.3(c)** for the realised `μ₁`. -/
theorem lemma73c_realised {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) {tw : ℕ → ℝ} (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p)
    {xmax : ℝ} (hZ : xmax / X0 ≤ Z) :
    Lemma73c X0 xmax (KR.Sharp.mu1R P tw X0m X0) :=
  KR.Sharp.lemma73c_of P hX hH (kptF1Bound P h hX hH hXm1 hXm2 hdec2 hZ) (kshQF1Second hX hH)

/-- **The realised inputs of Lemma 7.3**, with (c) and the edge expansion proved: only (b) and
(d)(iii) remain. -/
theorem lemma73Inputs_realised {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) (hXZ : (X0 : ℝ) ≤ Z) {tw : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p)
    (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p) {xmax : ℝ} (hZ : xmax / X0 ≤ Z)
    {μ0 : ℝ → ℝ} (hb : Lemma73b X0 xmax μ0)
    (hd : Lemma73diii X0 xmax (KR.Sharp.rhoEdge P tw X0m X0)) :
    Lemma73Inputs X0 xmax μ0 (KR.Sharp.mu1R P tw X0m X0) (KR.Sharp.rhoEdge P tw X0m X0) :=
  KR.Sharp.lemma73Inputs_of P h hX hH hXm1 hXm2 hXZ ht hdec hb
    (kptF1Bound P h hX hH hXm1 hXm2 hdec2 hZ) (kshQF1Second hX hH) hd

end BaseRange
