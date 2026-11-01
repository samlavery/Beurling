module

public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.Noise.RML7XBJ
public import RequestProject.Beurling.BaseRange.MarginHc

/-!
# Proposition 5.31(i) / 5.33 for the realised system: `j_{X₀}(t) ≤ 0.4209`

`hjb_R` : for the realised system `P(ω)` on `SG`, with (H_BS) on `[1, Z]`, `X₀⁻ ≤ Z`,
`2500 ≤ Z`, the width inputs of `paperWidth_Hc`, (huxley), `1 + 3ε/10 ≤ λ₀ ≤ 1.00003` and the
scale horizon at the starts of the windows, **`j_{X₀}(t) = jXdef … (jzX X₀) NK t ≤ 0.4209`** for
`2X₀ ≤ t ≤ X₀^{1.01}`, `t ≤ b`. This is `KR.XB7.hjb_of` (the level reduction `𝔅 ≤ 5/12`,
Proposition 5.31(i), with the certificate `BSCert.X0Band`) with all its inputs discharged for
the construction, `j₀ = jzX X₀ ≤ 1.0001/Λ` by `jzX_le`.

`hjb_Rc` : the same at the Model choices `Z = Zc X₀ b`, `NK = NKc X₀`.
-/

@[expose] public section

open Real Construction BModel CaplLink KR.Chain

namespace BaseRange

variable {θ : ℝ} {X₀ : ℕ}

/-- **`j_{X₀}(t) ≤ 0.4209`** on `[2X₀, X₀^{1.01}]` for the realised system. -/
theorem hjb_R (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    {Z η1 η2 ε : ℝ} {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : KR.WidthReal.CapHSlope X₀ ε)
    (hD : KR.WidthReal.CapHDiff X₀) (hH : HuxleyFrom X₀) (hXZ : Xm X₀ ≤ Z) (hZ0 : 2500 ≤ Z)
    {lam0 : ℝ} (hlam : 1 + 3 * (ε / 10) ≤ lam0) (hlamS : lam0 ≤ 1.00003)
    {NK : ℝ → ℕ × ℕ} {b : ℝ}
    (hwin : ∀ t y, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      InW (Queue6.Hc X₀ t) t y → 18 * y ≤ Z ^ 2 ∧ √(2 * y) ≤ KR.TNP.Pk (Xm X₀) (NK y).2) :
    ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      BModel.jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
        (jzX X₀) NK t ≤ 0.4209 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hX
  have hT := Queue6.tnpHyp_R hc hev hSG hX1 hbs (KR.WidthReal.paperWidth_Hc hX hε0 hε hS hD)
  rw [twR_eq hc ω]
  have hHX : Queue6.Hc X₀ X₀ ≤ (X₀ : ℝ) ^ (1 / 8 : ℝ) := by
    unfold Queue6.Hc; rw [max_self]
    exact InitialRange.capH_le_rpow hX0.le hX le_rfl
  exact KR.XB7.hjb_of hT hXZ (Queue6.Xm_eq_Hc (θ := θ))
    (BeurlingSystem.HBS.two_le_p hbs (by linarith)) (tnp_dec hT).1 (by linarith) hlamS
    (by linarith) hHX
    (KR.WidthReal.Hc_Xm_half_le hX) (jzX_nonneg hc) (jzX_le hX hH) hZ0 hwin

/-- **`hjb_R` at the Model choices** `Z = Zc X₀ b`, `NK = NKc X₀` (any `λ₀` with
`1 + 3ε/10 ≤ λ₀ ≤ 1.00003`). -/
theorem hjb_Rc (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {η1 η2 ε : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) η1 η2 ε1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : KR.WidthReal.CapHSlope X₀ ε)
    (hD : KR.WidthReal.CapHDiff X₀) (hH : HuxleyFrom X₀)
    {lam0 : ℝ} (hlam : 1 + 3 * (ε / 10) ≤ lam0) (hlamS : lam0 ≤ 1.00003) :
    ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      BModel.jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
        (jzX X₀) (NKc X₀) t ≤ 0.4209 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := X0_pos' hX
  obtain ⟨h1, h2, h3, -⟩ := Zc_facts hc hb
  refine hjb_R hc hev hSG hX1 hbs hε0 hε hS hD hH h1 (by linarith) hlam hlamS ?_
  intro t y ht2 _ htb hW
  refine ⟨?_, (NKc_spec hc y).2.2⟩
  have hHt : Queue6.Hc X₀ t ≤ Queue6.Hc X₀ b := by
    unfold Queue6.Hc
    exact capH_monotoneOn hX0.le hX (Set.mem_Ici.mpr (le_max_right _ _))
      (Set.mem_Ici.mpr (le_max_right _ _)) (max_le_max htb le_rfl)
  have hH0 : 0 ≤ Queue6.Hc X₀ t := capH_nonneg _ _
  have hy : y ≤ b + Queue6.Hc X₀ b := by
    have := hW.2; linarith
  linarith

end BaseRange
