module

public import RequestProject.Beurling.Noise.MarginVarStep4

/-!
# Proposition 5.38: the fields `hoscV`, `hsw`, `hS4`, and Proposition 5.31(i) (`hjb`)

* `supW`, `le_supW` : the supremum over the shifts `|h| ≤ c` of a bounded family; with
  `oV t := supW …` (resp. `ηV t := ½ supW …`) the fields `hoscV` (resp. `hsw`) of
  `BModel.RealMarginLoc` hold by `le_supW` as soon as the expression is bounded (`hoscV_of`,
  `hsw_of`); their content moves to the size bound `hS4`.
* `hS4_of` : the field `hS4` (`oV + 2ηV + ∑ e/w ≤ E_S/log t`) from `Margin.Var.step4` and the
  Step 4 decomposition of the source (the hypothesis `hS` of `step4`).
* `jX0_small`, `logy_jz_le` : the conclusion of Proposition 5.31(i) (`j_{X₀} ≤ 0.4209`, the
  field `hjb` for `jb := j_{X₀}`), from `𝔅(y) ≤ 5/12` (the certified `B(n) ≤ 5/12`,
  `BSCert.X0Band.Bx_le_five_twelfths`, at the single level `n₀`), `log y · j₀ ≤ 1.010102` and the
  `τ`-term `j₀ · 4.3 C_N E_θ ≤ 10⁻⁶`.
-/

@[expose] public section

open Real

namespace Margin.RML6

/-- The supremum of `F h` over the shifts `|h| ≤ c` (`0` if the family is unbounded). -/
noncomputable def supW (F : ℝ → ℝ) (c : ℝ) : ℝ := ⨆ h : {h : ℝ // |h| ≤ c}, F h

lemma le_supW {F : ℝ → ℝ} {c C : ℝ} (hb : ∀ h, |h| ≤ c → F h ≤ C) {h : ℝ} (hh : |h| ≤ c) :
    F h ≤ supW F c := by
  unfold supW
  refine le_ciSup (f := fun h : {h : ℝ // |h| ≤ c} => F h) ?_ ⟨h, hh⟩
  exact ⟨C, by rintro _ ⟨⟨h', hh'⟩, rfl⟩; exact hb h' hh'⟩

/-- **The field `hoscV`**, for `oV t := supW (fun h => |T'(t+h) - T'(t)|) (1.01 H(t))`, from a
bound `|T'| ≤ C`. -/
theorem hoscV_of {Tp : ℝ → ℝ} {C : ℝ} (hT : ∀ y, |Tp y| ≤ C) (Hc : ℝ → ℝ) (t : ℝ) {hh : ℝ}
    (hh1 : |hh| ≤ 1.01 * Hc t) :
    |Tp (t + hh) - Tp t| ≤ supW (fun h => |Tp (t + h) - Tp t|) (1.01 * Hc t) :=
  le_supW (F := fun h => |Tp (t + h) - Tp t|) (C := 2 * C)
    (fun h _ => (abs_sub (Tp (t + h)) (Tp t)).trans (by linarith [hT (t + h), hT t])) hh1

/-- **The field `hsw`**, for `ηV t := ½ supW (G t) (1.01 H(t))`, from a bound on the switching
expression `G t h` (the filter switching plus `|ΔNT_pt|`). -/
theorem hsw_of {G : ℝ → ℝ → ℝ} {C : ℝ} (hG : ∀ t h, G t h ≤ C) (Hc : ℝ → ℝ) (t : ℝ)
    {hh : ℝ} (hh1 : |hh| ≤ 1.01 * Hc t) :
    G t hh ≤ 2 * (1 / 2 * supW (G t) (1.01 * Hc t)) := by
  have := le_supW (C := C) (fun h _ => hG t h) hh1
  linarith

/-- **The field `hS4`** (Step 4): from `Margin.Var.step4`, with the Step 4 decomposition of the
source `S(t) = oV + 2ηV + ∑ e/w` (`hS`), and the size `so + 2sη + 27∑ log(3v)ν + 4.3∑ log(3v)δ
≤ E_S`. -/
theorem hS4_of {t oVt ηVt ew o η so sη ES : ℝ} (Vs : Finset ℝ) (ω ν δ : ℝ → ℝ)
    (ht : 1 < t) (ho : Real.log t * o ≤ so) (hη : Real.log t * η ≤ sη)
    (hν : ∀ v ∈ Vs, 0 ≤ ν v) (hδ : ∀ v ∈ Vs, 0 ≤ δ v) (hω0 : ∀ v ∈ Vs, 0 ≤ ω v)
    (hω : ∀ v ∈ Vs, Real.log t * ω v ≤ 2.9 * Real.log (3 * v))
    (hS : oVt + 2 * ηVt + ew ≤ o + 2 * η + 4 * ∑ v ∈ Vs, ω v * ν v +
      1.0001 * ∑ v ∈ Vs, ω v * δ v)
    (hES : so + 2 * sη + 27 * ∑ v ∈ Vs, Real.log (3 * v) * ν v +
      4.3 * ∑ v ∈ Vs, Real.log (3 * v) * δ v ≤ ES) :
    oVt + 2 * ηVt + ew ≤ ES / Real.log t := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have := Margin.Var.step4 Vs ω ν δ hlt.le ho hη hν hδ hω0 hω hS
  rw [le_div_iff₀ hlt]
  linarith

/-- `log y · j₀ ≤ 1.010102` in the small range (Proposition 5.31(i), conclusion): from
`j₀ ≤ 1.0001/Λ` (eq. (huxley)) and `log y ≤ 1.01Λ + 10⁻¹⁰`. -/
theorem logy_jz_le {Λ jz ly : ℝ} (hΛ : 100000000 ≤ Λ) (hjz0 : 0 ≤ jz)
    (hjz : jz ≤ 1.0001 / Λ) (hly : ly ≤ 1.01 * Λ + 1 / 10 ^ 10) :
    ly * jz ≤ 1.010102 := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : ly * jz ≤ (1.01 * Λ + 1 / 10 ^ 10) * (1.0001 / Λ) :=
    mul_le_mul hly hjz hjz0 (by positivity)
  have h2 : (1.01 * Λ + 1 / 10 ^ 10) * (1.0001 / Λ) = 1.010101 + 1.0001 / (10 ^ 10 * Λ) := by
    field_simp; ring
  have h3 : 1.0001 / (10 ^ 10 * Λ) ≤ 1.0001 / (10 ^ 10 * 100000000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have h4 : (1.0001 : ℝ) / (10 ^ 10 * 100000000) ≤ 1 / 10 ^ 6 := by norm_num
  linarith

/-- **Proposition 5.31(i), conclusion**: `log y · j₀ (𝔅(y) + 4.3 C_N E_θ/log y) ≤ 0.4209` from
`0 ≤ 𝔅(y) ≤ 5/12`, `log y · j₀ ≤ 1.010102` and `j₀ · 4.3 C_N E_θ ≤ 10⁻⁶`. -/
theorem jX0_small {ly jz B τt : ℝ} (hly : 0 < ly) (hB0 : 0 ≤ B)
    (hB : B ≤ 5 / 12) (hlj : ly * jz ≤ 1.010102) (hτ : jz * τt ≤ 1 / 10 ^ 6) :
    ly * jz * (B + τt / ly) ≤ 0.4209 := by
  have e : ly * jz * (B + τt / ly) = (ly * jz) * B + jz * τt := by field_simp
  rw [e]
  have h1 : (ly * jz) * B ≤ 1.010102 * (5 / 12) :=
    mul_le_mul hlj hB hB0 (by norm_num)
  have h2 : (1.010102 : ℝ) * (5 / 12) + 1 / 10 ^ 6 ≤ 0.4209 := by norm_num
  linarith

end Margin.RML6

end
