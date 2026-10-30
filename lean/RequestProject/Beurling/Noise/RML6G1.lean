module

public import RequestProject.Beurling.Noise.RML6G1A
public import RequestProject.Beurling.Noise.RML6G1B3

/-!
# The field `g1` of `BModel.RealMarginLoc` (Proposition 5.35's residual inputs)

`KR.Chain.G1At P tw X₀⁻ X₀ μ₀ μ₁ ρ_edge T' y` has two parts.

* **Range (A)** (`log y ≤ X₀^{1/100}`): proved in `RML6G1A.lean` (`g1A_of`) from eq. (86)
  (BaseRange's `shdecomp`) with the realised `μ₀ = BaseRange.mu0R`, `μ₁ = KR.Sharp.mu1R`,
  `ρ_edge = KR.Sharp.rhoEdge`, and the `σ_𝒜` response `SigmaAResp` (owner: Model).
* **Range (B)** (`log y > X₀^{1/100}`): the conclusions of Steps 1–4 of the proof of
  Proposition 5.35(B) with the paper's sizes. Here they are derived (`g1B_of`) from the inputs
  collected in `G1BInputs`, by `step1_g1` (Step 1 with the size of its error), `step2_avg`,
  `window_small` (Step 2), `step34_avg`, `thresh_small`, `jump_small`, `det_small` (Step 3), and
  the size check `o₁ + o₂ + o₃ ≤ 10⁻²⁴`.

`g1_of` combines the two: it is the field `g1` for the realised objects.

## The inputs of `G1BInputs`, with their owners

* **Model** (construction objects): the window parameter `δ` (the paper's
  `δ = min(γ_*^{-2} log^{-4} y, X₀^{-1/2})`, with `γ_*` the largest resolvable frequency of the
  designed oscillation) and its bounds `hδ`, `hδlow`, `hδL`; Theorem 5.24 at the height
  `y(1-δ)` (`hT`; from `LocalPNT.theorem_5_24_of_lag` on the good event); the realised `ρ̃`
  (`ρt`) and its window integral; the decomposition of `ρ^sh(z) - ρ^sh(y)` on `J` into its
  parts (`hdec34`, through `T' = 1 - ρ_det + R' + σ_𝒜` and the jump at `X₀`); the jump count
  `hjS` (the lag bound and the absorbed count on `I`); the `ρ_det` per-level bound `hdet`
  (Rankin for `Ψ(2v, X₀)`); the parts `hoth` (resolvable `R'_j` with `F_θ ≤ 1.33`, `σ_𝒜`,
  and the current oscillation of Step 4).
* **Queue6**: the first bullet of Step 1, `hcount` (`∫_J ρ̃ ≥ Π(J) - E_loc`: the partial boxes,
  the local count of Corollary 6.3, the prime powers), with `E_loc ≤ 40√y`; the
  `ThreshHyp` fields giving `hthr` (Lemma 5.23 at `2δ`, via `threshold_mass`) and the sizes of
  `H`, `K_loc` there; the bound `|ν| ≤ ν̄` (Lemma 5.22 on the slot windows).
* **§5 (this front)**, conclusions of other §5 results at the starts `z ∈ J`, as stated in
  Step 2: Lemma 5.34 (`h34`), Proposition 5.26 with Lemma 5.27 (`hbr`), `|NT| ≤ 54η`
  (`hNT`), the boundary term `∫_J (Bρ^sh - ρ^sh) ≤ Bnd ≤ 40√y` (`hbd`), the sizes
  `L(ν̄ + 54η) ≤ 10⁻²⁶`, `ε_N ≤ 10⁻¹³` (Lemma 5.34's (sw-sums)), `E_BR ≤ e^{-76}` ((osc)),
  `j ≤ e^{-59}` (Proposition 5.33).
-/

@[expose] public section

open Real Set MeasureTheory

namespace KR.RML6

/-- **The inputs of Proposition 5.35(B) at a start `y`** (see the module docstring for the
owners). `L = log y`, `J = [y(1-2δ), y(1-δ)]`, `ρ^sh = (z ↦ ρ^sh T'(z))`. -/
structure G1BInputs (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (Tp : ℝ → ℝ)
    (y : ℝ) where
  /-- the window parameter (Model) -/
  δ : ℝ
  hδ0 : 0 < δ
  hδ : δ ≤ (X0 : ℝ) ^ (-(1 / 2) : ℝ)
  hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X0) * √(Real.log y) / 2) *
    Real.log y ^ 4 + (X0 : ℝ) ^ (1 / 2 : ℝ)
  hδL : δ ≤ 1 / Real.log y ^ 4
  /-- Theorem 5.24 below the certified horizon (Model / LocalPNT) -/
  hT : LocalPNT.Theorem524Concl P X0 (y * (1 - δ))
  /-- the realised `ρ̃` (Model) -/
  ρt : ℝ → ℝ
  /-- Step 1, first bullet (Queue6) -/
  Eloc : ℝ
  hE0 : 0 ≤ Eloc
  hE : Eloc ≤ 40 * √y
  hcount : LocalPNT.piCount P (y * (1 - δ)) - LocalPNT.piCount P (y * (1 - 2 * δ)) - Eloc ≤
    ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), ρt z
  -- Step 2
  ν : ℝ → ℝ
  NT : ℝ → ℝ
  BRT : ℝ → ℝ
  Bρs : ℝ → ℝ
  εN : ℝ
  EBR : ℝ
  j : ℝ
  nb : ℝ
  η : ℝ
  Bnd : ℝ
  hit : IntervalIntegrable ρt volume (y * (1 - 2 * δ)) (y * (1 - δ))
  his : IntervalIntegrable (fun z => rhoSh P tw X0m z Tp) volume (y * (1 - 2 * δ)) (y * (1 - δ))
  hiB : IntervalIntegrable Bρs volume (y * (1 - 2 * δ)) (y * (1 - δ))
  /-- Lemma 5.34 on `J` (§5) -/
  h34 : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    |ρt z + ν z + NT z - BRT z| ≤ εN / Real.log y
  /-- Proposition 5.26 with Lemma 5.27 on `J` (§5) -/
  hbr : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |BRT z - Bρs z| ≤ (EBR + j) / Real.log y
  /-- `|ν| ≤ ν̄` (Lemma 5.22; Queue6) -/
  hν : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |ν z| ≤ nb
  /-- `|NT| ≤ 54η` (§5) -/
  hNT : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |NT z| ≤ 54 * η
  /-- the boundary term of Step 2 (§5) -/
  hbd : ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), (Bρs z - rhoSh P tw X0m z Tp) ≤ Bnd
  hBnd0 : 0 ≤ Bnd
  hBnd : Bnd ≤ 40 * √y
  /-- sizes of Step 2 (§5: Lemma 5.20, Lemma 5.22) -/
  hsmall2 : Real.log y * (nb + 54 * η) ≤ 1 / 10 ^ 26
  hεN : εN ≤ 1 / 10 ^ 13
  hEBR : EBR ≤ Real.exp (-76)
  hj : j ≤ Real.exp (-59)
  -- Steps 3–4
  thrS : ℝ
  j0 : ℝ
  jS : ℝ
  detS : ℝ
  othS : ℝ
  /-- the decomposition of Step 3 (Model) -/
  hdec34 : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    rhoSh P tw X0m z Tp - rhoSh P tw X0m y Tp ≤ 4 * thrS + j0 * jS + detS + othS
  /-- Lemma 5.23 at `2δ` (via `threshold_mass`; Queue6) -/
  Hy : ℝ
  Kloc : ℝ
  hthr : thrS ≤ 55 * (2 * δ) * Real.log y * (Real.log Hy + Real.log (1 / (2 * δ)) + 2) +
    14 * (Kloc + 2) * Real.log y * √(Hy / (2 * δ * y))
  hH1 : 1 ≤ Hy
  hH : Hy ≤ Real.exp (Real.log y / 8)
  hK0 : 0 ≤ Kloc
  hK : Kloc ≤ Hy
  /-- the jump at `X₀` (Model) -/
  N : ℝ
  HN : ℝ
  θ : ℝ
  hj0 : 0 ≤ j0
  hj1 : j0 ≤ 1
  hjS : jS ≤ 4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1)
  hN : Real.exp (Real.log y / 2) ≤ N
  hHN0 : 0 ≤ HN
  hHN : HN ≤ N ^ (1 / 8 : ℝ)
  hθ0 : 0 ≤ θ
  hθ : θ ≤ 1 / 2
  /-- the smooth change of `ρ_det` (Model) -/
  CS : ℝ
  hCS0 : 0 ≤ CS
  hCS : CS ≤ 77
  hdet : Real.log y * detS ≤ CS * (7 * Real.log X0 ^ 4 * (X0 : ℝ) ^ (-(1 / 12) : ℝ) +
    90 * Real.log X0 ^ (4.7 : ℝ) * Real.exp (-(Real.log X0 / 12)))
  /-- the resolvable `R'_j`, `σ_𝒜` and the current oscillation (Model) -/
  hoth : Real.log y * othS ≤ 1 / 10 ^ 27

/-- **Proposition 5.35(B) at a start `y`**: the range-(B) part of `G1At`, from `G1BInputs`. -/
theorem g1B_of {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ} {Tp : ℝ → ℝ} {y : ℝ}
    (hΛ : 100000000 ≤ Real.log X0) (hy0 : 0 < y) (hy : (X0 : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log y)
    (I : G1BInputs P tw X0m X0 Tp y) :
    ∃ avgR avgS εN EBR j o1 o2 o3 : ℝ,
      LocalPNT.pi0Dens y - o1 / Real.log y ≤ avgR ∧
      avgR - (εN + EBR + j + o2) / Real.log y ≤ avgS ∧
      avgS - o3 / Real.log y ≤ rhoSh P tw X0m y Tp ∧ εN ≤ 1 / 10 ^ 13 ∧
      EBR ≤ Real.exp (-76) ∧ j ≤ Real.exp (-59) ∧ o1 + o2 + o3 ≤ 1 / 10 ^ 24 := by
  set L := Real.log y with hLdef
  have hX0 : (0 : ℝ) < X0 := by
    by_contra hc; push_neg at hc
    have : (X0 : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hLe : Real.exp (Real.log X0 / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hX0] at hy; convert! hy using 2; ring
  have hLbig := logx_big hΛ hLe
  have hL0 : 0 < L := by linarith
  set a := y * (1 - 2 * I.δ)
  set b := y * (1 - I.δ)
  have hba : b - a = I.δ * y := by simp only [a, b]; ring
  have hδy : 0 < I.δ * y := mul_pos I.hδ0 hy0
  have hab : a < b := by linarith
  -- Step 1
  obtain ⟨o1, ho1, h1⟩ := step1_g1 hΛ hy0 hy I.hT I.hδ0 I.hδ I.hδlow I.hE0 I.hE I.hcount
  -- Step 2
  have h2 := step2_avg (εN := I.εN) (EBR := I.EBR) (j := I.j) (nb := I.nb) (η := I.η)
    hab hL0 I.hit I.his I.hiB I.h34 I.hbr I.hν I.hNT I.hbd
  rw [hba] at h2
  have hw := window_small hΛ hy0 hy I.hδ0 I.hδlow I.hBnd0 I.hBnd
  have ho2 : L * (I.nb + 54 * I.η) + L * I.Bnd / (I.δ * y) ≤
      1 / 10 ^ 26 + Real.exp (-71) := by
    have e : L * I.Bnd / (I.δ * y) = L * (1 / I.δ) * (I.Bnd / y) := by field_simp
    rw [e]; linarith [I.hsmall2]
  -- Steps 3–4
  set o3 := L * (4 * I.thrS + I.j0 * I.jS + I.detS + I.othS)
  have hpt : ∀ z ∈ Icc a b, rhoSh P tw X0m z Tp - rhoSh P tw X0m y Tp ≤ o3 / L := by
    intro z hz
    rw [show o3 / L = 4 * I.thrS + I.j0 * I.jS + I.detS + I.othS by
      simp only [o3]; field_simp]
    exact I.hdec34 z hz
  have h3 := step34_avg hab I.his hpt
  rw [hba] at h3
  have hthr := thresh_small hΛ hy0 hy I.hδ0 I.hδlow I.hδL I.hH1 I.hH I.hK0 I.hK
  have hjmp := jump_small hΛ hy0 hy I.hδ0 I.hδL I.hj0 I.hj1 I.hN I.hHN0 I.hHN I.hθ0 I.hθ
  have hdet := det_small hΛ I.hCS0 I.hCS
  have ho3 : o3 ≤ 1 / 10 ^ 27 + 1 / 10 ^ 27 + Real.exp (-1000000) + 1 / 10 ^ 27 := by
    have e : o3 = L * 4 * I.thrS + L * (I.j0 * I.jS) + L * I.detS + L * I.othS := by
      simp only [o3]; ring
    have t1 : L * 4 * I.thrS ≤ L * 4 * (55 * (2 * I.δ) * L *
        (Real.log I.Hy + Real.log (1 / (2 * I.δ)) + 2) +
        14 * (I.Kloc + 2) * L * √(I.Hy / (2 * I.δ * y))) :=
      mul_le_mul_of_nonneg_left I.hthr (by positivity)
    have t2 : L * (I.j0 * I.jS) ≤ L * I.j0 * (4.1 * I.δ + 3 * I.HN / I.N +
        2 * I.N ^ (I.θ / 2 - 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left I.hjS I.hj0) hL0.le
    rw [e]
    linarith [I.hdet, I.hoth]
  -- the sizes
  have h71 := exp_neg_71_le
  have h6 : Real.exp (-1000000) ≤ Real.exp (-71) := Real.exp_le_exp.mpr (by norm_num)
  refine ⟨(∫ z in a..b, I.ρt z) / (I.δ * y), (∫ z in a..b, rhoSh P tw X0m z Tp) / (I.δ * y),
    I.εN, I.EBR, I.j, o1, L * (I.nb + 54 * I.η) + L * I.Bnd / (I.δ * y), o3, h1, h2, h3,
    I.hεN, I.hEBR, I.hj, ?_⟩
  have : (1 : ℝ) / 10 ^ 25 + (1 / 10 ^ 26 + 1 / (2 * 10 ^ 25)) +
      (3 / 10 ^ 27 + 1 / (2 * 10 ^ 25)) ≤ 1 / 10 ^ 24 := by norm_num
  linarith

/-- **The field `g1` of `BModel.RealMarginLoc` at a start `y`**, for the realised objects of
§7: range (A) from eq. (86) and `SigmaAResp`, range (B) from `G1BInputs`. -/
theorem g1_of {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ} {Tp : ℝ → ℝ} {y : ℝ}
    (hΛ : 100000000 ≤ Real.log X0) (hXm : 0 < X0m) (hX0m : X0m ≤ X0) (hy : (X0 : ℝ) ≤ y)
    (hA : SigmaAResp P tw X0m X0 Tp y)
    (hB : (X0 : ℝ) ^ (1 / 100 : ℝ) < Real.log y → G1BInputs P tw X0m X0 Tp y) :
    KR.Chain.G1At P tw X0m X0 (BaseRange.mu0R P tw X0m X0) (KR.Sharp.mu1R P tw X0m X0)
      (KR.Sharp.rhoEdge P tw X0m X0) Tp y := by
  obtain ⟨rA, hdA, hrA⟩ := g1A_of hXm X0 hX0m hy Tp hA
  have hy0 : 0 < y := lt_of_lt_of_le hXm (hX0m.trans hy)
  exact ⟨rA, hdA, hrA, fun h => g1B_of hΛ hy0 h.le (hB h)⟩

end KR.RML6

end
