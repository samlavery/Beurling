module

public import RequestProject.Beurling.Model.MarginFinal
public import RequestProject.Beurling.Noise.RML15Eta

/-!
# `RestMarginR` cannot be built: its field `ho` is false

`BModel.RML15.restMarginR_isEmpty`: under (huxley) and the standing facts, `RestMarginR θ X₀ ω b`
is empty for every `b ≥ X₀`. Its field `ho` would give `log X₀ · o_V(X₀) ≤ so`, while `hη`
and `hsize` force `so ≤ 0.0013`; but `o_V` (`BModel.oVc`) oscillates `T' = T_c + j₀ 1_{[X₀,∞)}`,
so `log X₀ · o_V(X₀) ≥ log X₀ · j₀ ≥ 0.98` (`ho_false`). The paper's `o_t` is the oscillation of
`T_c`; the jump is the separate base term `j₀ 1[|t - X₀| ≤ 1.01 H(t)]` (04g Steps 3, 5).
-/

@[expose] public section

open Real BModel

namespace BModel.RML15

variable {θ : ℝ} {X₀ : ℕ}

theorem restMarginR_isEmpty (hc : Cond θ X₀) (hev : Even X₀) (ω : Construction.JitterΩ)
    {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) η1 η2 ε1
      εT θT)
    (hH : BaseRange.HuxleyFrom (X₀ : ℝ)) : IsEmpty (RestMarginR θ X₀ ω b) := by
  constructor
  intro R
  have hX := hc.hX
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ (Zc_18 hc hb)
    have : 0 ≤ b + Queue6.Hc X₀ b := by
      have := (KR.WidthReal.Hc_pos hX b).le; linarith
    exact div_le_div_of_nonneg_right (by linarith) hXm0.le
  have hT : (RML7.canonP X₀ epsH RML13.ESH (jzX X₀)).cinf +
      (RML7.canonP X₀ epsH RML13.ESH (jzX X₀)).Kc ≤ X₀ :=
    hT0T_c hc RML13.ESH (jzX X₀) (b := X₀) le_rfl
  -- `sη ≥ 0`
  have hη0 : 0 ≤ ηVc θ X₀ ω (RML7.canonP X₀ epsH RML13.ESH (jzX X₀)) X₀ := by
    have h := hsw_c hc hev ω (RML7.canonP X₀ epsH RML13.ESH (jzX X₀)) (b := X₀) (t := X₀)
      le_rfl (hh := 0) (by simp; linarith [KR.WidthReal.Hc_pos hX (X₀ : ℝ)])
    have : 0 ≤ Gsw θ X₀ ω (RML7.canonP X₀ epsH RML13.ESH (jzX X₀)) X₀ 0 := by
      unfold Gsw; positivity
    linarith
  have hlX : 0 < Real.log X₀ := by linarith
  have hs := R.hη X₀ hT hb
  have hsη : 0 ≤ R.sη := le_trans (mul_nonneg hlX.le hη0) hs
  have hso : R.so < 0.98 := by linarith [R.hsize]
  exact ho_false hc hev ω htnp hH hb hZ RML13.ESH (jzX X₀) hso R.ho

end BModel.RML15

end
