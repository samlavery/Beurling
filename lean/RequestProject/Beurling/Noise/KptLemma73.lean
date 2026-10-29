module

public import RequestProject.Beurling.Noise.KptEdge
public import RequestProject.Beurling.BaseRange.Split

/-!
# The realised inputs of Lemma 7.3, with the realised `K_pt`

With the realised operator `K_pt` (`KptDefs.lean`):

* `rhoEdge` (`KptEdge.lean`) is `ρ_edge = (1 + K_pt)⁻¹ μ_edge`, and its expansion (★)
  (`BaseRange.EdgeExpansion`) is proved (`edgeExpansion`);
* `mu1R = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})` is the realised `μ₁` of §7.2 (correction #74);
  `lemma73c_of` proves Lemma 7.3(c) (`BaseRange.Lemma73c`) from the rational half
  `BaseRange.KshQ_f1_le` and two named bounds, one per operator, each exactly a bullet of the
  proof of (c): `KptF1Bound` (the `K_pt` half: the first bound with
  `∑_{w ≤ x/X₀} 1/(w log(x/w)) ≤ log v + 0.01`, and the second bound) and `KshQF1Second`
  (the second bound for `K^sh_ℚ`);
* `lemma73Inputs_of` packages `BaseRange.Lemma73Inputs` with `EdgeExpansion` discharged.

Lemma 7.3(b) (`Lemma73b`, the smooth part `μ₀`) and (d)(iii) (`Lemma73diii` for `rhoEdge`) stay
inputs: their proofs (Steps 1–3 of (b), and the telescoping of `(K'_ℚ - K_pt) g` in (d)(iii)) use
the lag bound, the prime-count difference `|ψ_𝒩 - ψ| ≤ 5κ t log² t` and the decision-order
count on `Good(<u)`.
-/

@[expose] public section

open Finset BeurlingSystem Real BSCert.Consts BSCert.EiFn

namespace KR.Sharp

variable (P : BeurlingSystem)

/-- `f₁ 1_{[X₀,∞)}`. -/
noncomputable def f1cut (X0 : ℕ) (q : ℝ) : ℝ :=
  if (X0 : ℝ) ≤ q then BaseRange.f1 X0 (Construction.kappaParam X0) q else 0

/-- The realised `μ₁ = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})`. -/
noncomputable def mu1R (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (x : ℝ) : ℝ :=
  BaseRange.KshQ X0 (BaseRange.f1 X0 (Construction.kappaParam X0)) x - Kpt P tw X0m (f1cut X0) x

/-- Half of the second bound of Lemma 7.3(c), `v = log x/Λ`, `U = 1 + 2 log v`. -/
noncomputable def secondHalf (X0 : ℕ) (x : ℝ) : ℝ :=
  (Uf (Real.log x / Real.log X0) / Real.log x) ^ 3 *
      (Real.log (Uf (Real.log x / Real.log X0)) + 1.01) +
    2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) *
      ((Real.log x / Real.log X0) / Uf (Real.log x / Real.log X0)) /
      (Real.log x / Real.log X0) ^ 4 / Real.log X0 ^ 3

/-- **The `K_pt` half of Lemma 7.3(c)** (proof of (c), bullets 1–3, for the realised operator),
on `Good(<xmax)`: `|K_pt(f₁ 1_{[X₀,∞)})(x)| ≤ Λ⁻³(log v + 0.01)`, and for `v ≥ 4` it is at most
the second-bound half `secondHalf`. -/
def KptF1Bound (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (xmax : ℝ) : Prop :=
  ∀ x : ℝ, (X0 : ℝ) ≤ x → x ≤ xmax →
    |Kpt P tw X0m (f1cut X0) x| ≤
        1 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 0.01) ∧
      (4 ≤ Real.log x / Real.log X0 → |Kpt P tw X0m (f1cut X0) x| ≤ secondHalf X0 x)

/-- **The `K^sh_ℚ` half of the second bound of Lemma 7.3(c)** (bullets 1–2 of the proof of (c),
for the rational operator): for `v ≥ 4`, `|K^sh_ℚ(f₁ 1_{[X₀,∞)})(x)| ≤ secondHalf`. -/
def KshQF1Second (X0 : ℕ) : Prop :=
  ∀ x : ℝ, (X0 : ℝ) ≤ x → 4 ≤ Real.log x / Real.log X0 →
    |BaseRange.KshQ X0 (BaseRange.f1 X0 (Construction.kappaParam X0)) x| ≤ secondHalf X0 x

lemma log_v_nonneg {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx : (X0 : ℝ) ≤ x) :
    0 ≤ Real.log (Real.log x / Real.log X0) := by
  have hX1 := BaseRange.one_lt_of_log hX
  have hL : Real.log X0 ≤ Real.log x := Real.log_le_log (by linarith) hx
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]; linarith

lemma secondHalf_nonneg {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx : (X0 : ℝ) ≤ x) :
    0 ≤ secondHalf X0 x := by
  have hlv := log_v_nonneg hX hx
  have hX1 := BaseRange.one_lt_of_log hX
  have hL : Real.log X0 ≤ Real.log x := Real.log_le_log (by linarith) hx
  have hΛ : 0 < Real.log X0 := by linarith
  have hv : 0 ≤ Real.log x / Real.log X0 := div_nonneg (by linarith) hΛ.le
  have hU : 1 ≤ Uf (Real.log x / Real.log X0) := by unfold Uf; linarith
  have hlU : 0 ≤ Real.log (Uf (Real.log x / Real.log X0)) := Real.log_nonneg hU
  unfold secondHalf
  have : 0 ≤ Real.log x := by linarith
  positivity

/-- **Lemma 7.3(c) for the realised `μ₁`**, from the rational half `KshQ_f1_le` and the two
named halves. -/
theorem lemma73c_of {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : BaseRange.HuxleyFrom X0)
    {tw : ℕ → ℝ} {X0m xmax : ℝ} (hK : KptF1Bound P tw X0m X0 xmax) (hQ : KshQF1Second X0) :
    BaseRange.Lemma73c X0 xmax (mu1R P tw X0m X0) := by
  unfold BaseRange.Lemma73c BaseRange.Mu1Pointwise
  have hX1 := BaseRange.one_lt_of_log hX
  have hΛ : 0 < Real.log X0 := by linarith
  refine ⟨fun x hx => ?_, fun x hx hv => ?_⟩
  · have hlv := log_v_nonneg hX hx
    dsimp only
    split_ifs with hxm
    · obtain ⟨h1, -⟩ := hK x hx hxm
      have h2 := BaseRange.KshQ_f1_le hX hH hx
      unfold mu1R
      calc |_ - _| ≤ |BaseRange.KshQ X0 (BaseRange.f1 X0 (Construction.kappaParam X0)) x| +
            |Kpt P tw X0m (f1cut X0) x| := abs_sub _ _
        _ ≤ 1 / Real.log X0 ^ 3 * Real.log (Real.log x / Real.log X0) +
            1 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 0.01) :=
            add_le_add h2 h1
        _ ≤ 2 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 1.01) := by
            have hp : 0 < 1 / Real.log X0 ^ 3 := by positivity
            have e : 2 / Real.log X0 ^ 3 = 2 * (1 / Real.log X0 ^ 3) := by ring
            rw [e]; nlinarith
    · rw [abs_zero]; positivity
  · have hs := secondHalf_nonneg hX hx
    dsimp only
    split_ifs with hxm
    · have h1 := (hK x hx hxm).2 hv
      have h2 := hQ x hx hv
      unfold mu1R
      calc |_ - _| ≤ |BaseRange.KshQ X0 (BaseRange.f1 X0 (Construction.kappaParam X0)) x| +
            |Kpt P tw X0m (f1cut X0) x| := abs_sub _ _
        _ ≤ secondHalf X0 x + secondHalf X0 x := add_le_add h2 h1
        _ = 2 * secondHalf X0 x := by ring
    · rw [abs_zero]
      have : 0 ≤ 2 * secondHalf X0 x := by positivity
      exact this

/-- **The realised inputs of Lemma 7.3** with the realised `ρ_edge = (1 + K_pt)⁻¹ μ_edge` and
`μ₁ = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})`: `EdgeExpansion` is proved, (c) is reduced to the two
named halves, and (b), (d)(iii) are the remaining inputs. -/
theorem lemma73Inputs_of {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hH : BaseRange.HuxleyFrom X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) (hZ : (X0 : ℝ) ≤ Z) {tw : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < tw p)
    (hdec : ∀ p, p.Prime → P.labelVal p < X0m → tw p ≤ P.labelVal p) {xmax : ℝ}
    {μ0 : ℝ → ℝ} (hb : BaseRange.Lemma73b X0 xmax μ0) (hK : KptF1Bound P tw X0m X0 xmax)
    (hQ : KshQF1Second X0) (hd : BaseRange.Lemma73diii X0 xmax (rhoEdge P tw X0m X0)) :
    BaseRange.Lemma73Inputs X0 xmax μ0 (mu1R P tw X0m X0) (rhoEdge P tw X0m X0) :=
  ⟨hb, lemma73c_of P hX hH hK hQ, edgeExpansion P h hX hXm1 hXm2 hZ ht hdec, hd⟩

end KR.Sharp

end
