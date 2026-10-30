module

public import RequestProject.Beurling.Noise.RML6PredOps
public import RequestProject.Beurling.Noise.RML6PredBug
public import RequestProject.Beurling.Noise.MarginChainLin
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# Lemma 5.34 with the operators of §5.3 on `LocInt`

* `Pred.predictable_identity_gen` : the identity (predictable) of Lemma 5.34 for additive maps on
  an arbitrary additive group (the proof of `Pred.predictable_identity` only uses additivity);
* `KR.Ops.hpred_of_ops` : the input (predictable) of Theorem 5.37 with the concrete operators
  `B = Bop` (window average), `K = Kop` (realised `K_pt`), `R = Nop` (the Neumann series of
  `(1 + K_pt B)⁻¹`) on `LocInt`. Here `hR` (`Nop_spec`), `hinj` (`inj_spec`) and `hBx`
  (definitional) are theorems; the remaining inputs are the margin identity (Proposition 5.11),
  the two bullets of Lemma 5.34 and `|ϑ| ≤ 6`;
* `KR.Ops.opHyp_of` : the hypotheses `OpHyp` from `PaperWidth`, `H` monotone, prime values
  `≥ 2` and `X₀⁻ ≥ 1`; `KR.Ops.opHyp_Hc` for the realised width `Hc X₀`.
-/

@[expose] public section

open MeasureTheory Set

namespace Pred

variable {E : Type*} [AddCommGroup E] (B K R : E →+ E)

/-- **The identity (predictable)** of Lemma 5.34, for additive maps on any additive group. -/
theorem predictable_identity_gen
    (hR : ∀ g, R g + K (B (R g)) = g)
    (hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f')
    (ρ ν NT vt Tc J : E)
    (hmargin : ρ + B (K ρ) = B (Tc + J) + vt - ν - NT) :
    (ρ + ν + NT) - B (R (Tc + J)) =
      vt - B (K (B (R ((B Tc - Tc) + vt - ν - NT)))) -
        B (R (K ((B (Tc + J) + vt - ν - NT - B J) - B (B (Tc + J) + vt - ν - NT - B J)))) := by
  set Tp := Tc + J
  set F := B Tp + vt - ν - NT
  set Fc := F - B J
  set Fr := (B Tc - Tc) + vt - ν - NT
  set G := K (Fc - B Fc)
  set ρ' := B (R Tp) + vt - B (K (B (R Fr))) - B (R G) - ν - NT with hρ'
  have key : ρ' + B (K ρ') = F := by
    have eG : G = K Fc - K (B Fc) := by simp only [G, map_sub]
    have eFc : Fc = B Tc + vt - ν - NT := by
      simp only [Fc, F, Tp, map_add]; abel
    have hBR : ∀ g, B (R g) + B (K (B (R g))) = B g := fun g => by
      rw [← map_add, hR]
    simp only [hρ', map_add, map_sub]
    have e1 := hBR Tp
    have e3 := hBR G
    have hKBe2 : B (K (B (R Fr))) + B (K (B (K (B (R Fr))))) = B (K (B Fr)) := by
      rw [← map_add, ← map_add, ← map_add, hR]
    have hzero : B (K (B Fr)) + B G = B (K vt) - B (K ν) - B (K NT) := by
      rw [eG, eFc]
      simp only [Fr, map_add, map_sub]
      abel
    simp only [F]
    linear_combination (norm := abel) e1 - hKBe2 - e3 - hzero
  have : ρ = ρ' := hinj ρ ρ' (by rw [hmargin, key])
  rw [this, hρ']
  abel

end Pred

namespace KR.Ops

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {H : ℝ → ℝ} {X0m : ℝ}

/-- `OpHyp` from `PaperWidth`, `H` non-decreasing, prime values `≥ 2` and `X₀⁻ ≥ 1`. -/
theorem opHyp_of {ε θ : ℝ} (hP : PaperWidth H X0m ε θ) (hmono : Monotone H)
    (hp2 : ∀ j, 2 ≤ P.p j) (h1 : 1 ≤ X0m) : OpHyp P H X0m where
  cont := hP.reg.lip.continuous
  pos := hP.reg.pos
  small := hP.small
  low y hy := by
    have h := hP.small (X0m / 2) le_rfl
    have := hmono hy.le
    linarith
  p2 := hp2
  one_le := h1

variable (hO : OpHyp P H X0m)

/-- The three operators of §5.3 on `LocInt`. -/
noncomputable abbrev Bo : LocInt →+ LocInt := Bop hO.cont hO.pos
noncomputable abbrev Ko : LocInt →+ LocInt := Kop (P := P) (tw := tw) hO.X0m_pos
noncomputable abbrev Ro : LocInt →+ LocInt := Nop (tw := tw) hO

/-- **The input (predictable) of Theorem 5.37** (Lemma 5.34) with the concrete operators of
§5.3 on `LocInt`: `R_res` inverts `1 + K_pt B` (`Nop_spec`) and `1 + B K_pt` is injective
(`inj_spec`), both proved; `B` is the window average by definition. The remaining inputs are
the margin identity `hmargin` (Proposition 5.11 with (Ttilde)), the two bullets `hK`, `hG` of
the proof of Lemma 5.34 and `|ϑ(x)| ≤ 6`. All functions are in `LocInt`. -/
theorem hpred_of_ops (ρ ν NT vtH Tc J : LocInt) (ϑ : ℝ → ℝ)
    (hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / H z)
    (hmargin : ρ + Bo hO (Ko (tw := tw) hO ρ) = Bo hO (Tc + J) + vtH - ν - NT)
    {x a b : ℝ} (hlx : 0 ≤ Real.log x)
    (hK : Real.log x * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO Tc - Tc) + vtH - ν - NT)))) : ℝ → ℝ) x| ≤ a)
    (hG : Real.log x * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (Tc + J) + vtH - ν - NT - Bo hO J) -
        Bo hO (Bo hO (Tc + J) + vtH - ν - NT - Bo hO J)))) : ℝ → ℝ) x| ≤ b)
    (hϑ : |ϑ x| ≤ 6) :
    Real.log x * Margin.Bavg (H x) (Ro (tw := tw) hO (Tc + J)) x -
        (a + b + 6 * Real.log x / H x) ≤
      Real.log x * ((ρ : ℝ → ℝ) x + (ν : ℝ → ℝ) x + (NT : ℝ → ℝ) x) := by
  have hid := Pred.predictable_identity_gen (Bo hO) (Ko (tw := tw) hO) (Ro (tw := tw) hO)
    (Nop_spec hO) (fun f f' h => inj_spec hO f f' h) ρ ν NT vtH Tc J hmargin
  have hDx := congrArg (fun u : LocInt => (u : ℝ → ℝ) x) hid
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.add_apply, Pi.sub_apply] at hDx
  have hH := hO.pos x
  have hb := Pred.lemma_5_34_bound (D := fun z => (ρ : ℝ → ℝ) z + (ν : ℝ → ℝ) z +
      (NT : ℝ → ℝ) z - (Bo hO (Ro (tw := tw) hO (Tc + J)) : ℝ → ℝ) z) (vt := ϑ) (H := H)
    (x := x) (by rw [hDx, hvt]) hlx hH hK hG hϑ
  have habs := neg_abs_le ((ρ : ℝ → ℝ) x + (ν : ℝ → ℝ) x + (NT : ℝ → ℝ) x -
    (Bo hO (Ro (tw := tw) hO (Tc + J)) : ℝ → ℝ) x)
  have hBx : (Bo hO (Ro (tw := tw) hO (Tc + J)) : ℝ → ℝ) x =
      Margin.Bavg (H x) (Ro (tw := tw) hO (Tc + J)) x := rfl
  rw [hBx] at habs hb
  nlinarith

/-! ## The realised width -/

variable {X₀ : ℕ}

/-- `OpHyp` for the realised width `Hc X₀`, from `PaperWidth` (`KR.WidthReal.paperWidth_Hc`)
and prime values `≥ 2`. -/
theorem opHyp_Hc (hX : 10 ^ 8 ≤ Real.log X₀) {ε θ : ℝ}
    (hP : PaperWidth (Queue6.Hc X₀) (BModel.Xm X₀) ε θ) (hp2 : ∀ j, 2 ≤ P.p j) :
    OpHyp P (Queue6.Hc X₀) (BModel.Xm X₀) := by
  refine opHyp_of hP (KR.WidthReal.Hc_mono hX) hp2 ?_
  have h1 := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have h2 : (2 : ℝ) ≤ X₀ := by
    have hX0 : (0 : ℝ) < X₀ := KR.WidthReal.X0_pos hX
    by_contra hc
    push_neg at hc
    have : Real.log X₀ ≤ Real.log 2 := Real.log_le_log hX0 hc.le
    have := Real.log_two_lt_d9
    linarith
  linarith

end KR.Ops

end
