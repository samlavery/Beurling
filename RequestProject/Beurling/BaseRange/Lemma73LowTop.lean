module

public import RequestProject.Beurling.BaseRange.Lemma73Low
public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.Noise.MarginRealTop

/-!
# `BModel.Lemma73Low` from (H_BS) on `[1, Zc b]`

`lemma73Low_of` : for `X₀ ≤ b`, on `SG`, with (H_BS) on `[1, Zc X₀ b]` (`BModel.hbs_Zc`) and
the local count on `[X₀⁻, Zc X₀ b]` (`BModel.hbs_local`), **`Lemma73Low θ X₀ ω b`** holds (in
fact `Lemma73Inputs` at `x_max = b + H(b)` for every `b ≥ X₀`, via `lemma73Inputs_R'`; the
hypothesis `b < 4X₀ + 2` is not needed).
-/

@[expose] public section

open Real Construction BModel CaplLink

namespace BaseRange

variable {θ : ℝ} {X₀ : ℕ}

/-- **`Lemma73Low`** from (H_BS) on `[1, Zc b]` and the local count. -/
theorem lemma73Low_of (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ}
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {η1 η2 ε : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) η1 η2 ε1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : KR.WidthReal.CapHSlope X₀ ε)
    (hD : KR.WidthReal.CapHDiff X₀)
    (hloc : ∀ v, Xm X₀ ≤ v → v ≤ Zc X₀ b →
      |(PR θ X₀ ω).N v - ⌊v⌋₊| ≤ Construction.hbsEps X₀ v * v) :
    Lemma73Low θ X₀ ω b := by
  intro _ hH
  obtain ⟨h1, -, -, h4⟩ := Zc_facts hc hb
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hH0 : 0 ≤ Queue6.Hc X₀ b := capH_nonneg _ _
  have hx0 : 0 ≤ b + Queue6.Hc X₀ b := by
    have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    linarith
  have hZ : (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ h4
    apply div_le_div_of_nonneg_right _ hXm0.le
    linarith
  rw [twR_eq hc ω]
  exact lemma73Inputs_R' hc hev hSG hX1 hbs hε0 hε hS hD hH h1 hZ hloc

end BaseRange
