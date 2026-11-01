module

public import RequestProject.Beurling.Noise.BridgeG1A
public import RequestProject.Beurling.Noise.BridgeG1B
public import RequestProject.Beurling.Noise.BridgePred

/-!
# Proposition 5.35 (positivity of the sharp reference)

`KR.G1.prop_5_35` : on `Good(<x)`,
`ρ^sh(x) log x ≥ 0.82` for `X₀ ≤ x ≤ X₀^{1.01}` and `≥ 0.97` for `x ≥ X₀^{1.01}/2`.

Range (A) (`log x ≤ X₀^{1/100}`) is `G1.prop_5_35_A`; range (B) is `G1B.prop_5_35_B`, whose
inputs are the conclusions of Steps 1–4 of the paper's proof (Step 1 from Theorem 5.24(ii):
`G1B.step1_avg`).
-/

@[expose] public section

open Real BeurlingSystem

namespace KR.G1

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m x : ℝ}

/-- **Proposition 5.35 (positivity of the sharp reference).** The range-(A) inputs are those of
`prop_5_35_A` (they are used only when `log x ≤ X₀^{1/100}`); the range-(B) inputs are the
three step inequalities of `G1B.prop_5_35_B` with the paper's sizes (used only when
`log x > X₀^{1/100}`). -/
theorem prop_5_35 {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
    (hHux : BaseRange.HuxleyFrom X0) {xmax : ℝ} {μ0 μ1 ρedge : ℝ → ℝ}
    (hin : BaseRange.Lemma73Inputs X0 xmax μ0 μ1 ρedge)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hX0m : X0m ≤ X0) (hx : (X0 : ℝ) ≤ x) (hxmax : x ≤ xmax) (hZ : 2 * x / X0m ≤ Z)
    (hμ0 : ∀ u : ℝ, u < X0 → μ0 u = 0) (hμ1 : ∀ u : ℝ, u < X0 → μ1 u = 0)
    {Tp : ℝ → ℝ} {rA : ℝ}
    (hdec : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) →
      rhoSh P tw X0m x Tp = BaseRange.MAP X0 (Construction.kappaParam X0) x + ρedge x +
        rhoSh P tw X0m x μ0 + rhoSh P tw X0m x μ1 + rA)
    (hA : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) → |rA * Real.log x| ≤ Real.exp (-80))
    (hB : (X0 : ℝ) ^ (1 / 100 : ℝ) < Real.log x →
      ∃ avgR avgS εN EBR j o1 o2 o3 : ℝ,
        LocalPNT.pi0Dens x - o1 / Real.log x ≤ avgR ∧
        avgR - (εN + EBR + j + o2) / Real.log x ≤ avgS ∧
        avgS - o3 / Real.log x ≤ rhoSh P tw X0m x Tp ∧ εN ≤ 1 / 10 ^ 13 ∧
        EBR ≤ Real.exp (-76) ∧ j ≤ Real.exp (-59) ∧ o1 + o2 + o3 ≤ 1 / 10 ^ 24) :
    (x ≤ (X0 : ℝ) ^ (1.01 : ℝ) → 0.82 ≤ rhoSh P tw X0m x Tp * Real.log x) ∧
    ((X0 : ℝ) ^ (1.01 : ℝ) / 2 ≤ x → 0.97 ≤ rhoSh P tw X0m x Tp * Real.log x) := by
  have hX1 : (1 : ℝ) < X0 := BaseRange.one_lt_of_log hX
  have hX0p : (0 : ℝ) < X0 := by linarith
  -- `x ≤ X₀^{1.01}` forces `log x ≤ X₀^{1/100}`
  have hsmall : x ≤ (X0 : ℝ) ^ (1.01 : ℝ) → Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) := by
    intro hx2
    have hx0 : 0 < x := by linarith
    have h1 : Real.log x ≤ 1.01 * Real.log X0 := by
      have := Real.log_le_log hx0 hx2
      rwa [Real.log_rpow hX0p] at this
    have h2 := (G1B.range_fit (Λ := Real.log X0) (by norm_num at hX ⊢; linarith)).1
    have e : (X0 : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Real.log X0 / 100) := by
      rw [Real.rpow_def_of_pos hX0p]; ring_nf
    rw [e]; linarith
  constructor
  · intro hx2
    have hl := hsmall hx2
    have := (prop_5_35_A h hXm hX hHux hin ht htv hX0m hx hxmax hZ hl hμ0 hμ1 (hdec hl)
      (hA hl)).1 hx2
    linarith
  · intro hx2
    rcases le_or_gt (Real.log x) ((X0 : ℝ) ^ (1 / 100 : ℝ)) with hl | hl
    · have := (prop_5_35_A h hXm hX hHux hin ht htv hX0m hx hxmax hZ hl hμ0 hμ1 (hdec hl)
        (hA hl)).2 hx2
      linarith
    · obtain ⟨avgR, avgS, εN, EBR, j, o1, o2, o3, h1, h2, h3, h4, h5, h6, h7⟩ := hB hl
      have hx10 : (10 : ℝ) ^ 10 ≤ x := by
        have hlX : (10 : ℝ) ^ 8 ≤ Real.log x :=
          hX.trans (Real.log_le_log hX0p hx)
        have h23 : (30 : ℝ) ≤ Real.log x := by norm_num at hlX; linarith
        have hx0 : 0 < x := by linarith
        have : Real.exp 30 ≤ x := by
          rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr h23
        have he : (10 : ℝ) ^ 10 ≤ Real.exp 30 := by
          have := Real.pow_div_factorial_le_exp (x := (30 : ℝ)) (by norm_num) 20
          norm_num [Nat.factorial] at this ⊢; linarith
        linarith
      exact G1B.prop_5_35_B hx10 h1 h2 h3 h4 h5 h6 h7

end KR.G1

end
