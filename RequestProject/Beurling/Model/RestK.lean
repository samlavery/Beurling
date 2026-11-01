module

public import RequestProject.Beurling.Model.RestWire
public import RequestProject.Beurling.Model.MarginMine
public import RequestProject.Beurling.Model.Wire3

/-!
# Lemma 5.34, first bullet, for the realised system (the field `hK`)

`hK_c` : `BModel.RML7.hK_field` at the Model data (`ρ̃`, `T_c`, `NT = B NT_pt`, `ϑ = 0`,
`N, K` from `NKc`), with `a(x) = aK C_N S(x) H x`. Its remaining input is the scale-wise bound
`FrScaleBound` of `|F_r|` with sums `S(x)` (`hFr`); the local boundedness and measurability of
`F_r` are `LMb_Frx`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **The field `hK`** (Lemma 5.34, first bullet) at the Model data. -/
theorem hK_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) θ (b + Queue6.Hc X₀ b))
    (S : ℝ → ℝ) (FbK : ℝ → ℝ → ℝ → ℝ)
    (hFr : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      KR.TNP.FrScaleBound (PR θ X₀ ω) (Queue6.Hc X₀) X₀
        ((Frx hO (ρLd θ X₀ ω) (TcLd θ X₀ ω) (NTd θ X₀ ω) 0 (jzX X₀) : KR.Ops.LocInt) :
          ℝ → ℝ) x (S x) (fun y => (NKc X₀ y).1) (FbK x)) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO (KR.Ops.Bo hO
        (KR.Ops.Ro (tw := twR θ X₀ ω) hO ((KR.Ops.Bo hO (TcLd θ X₀ ω) - TcLd θ X₀ ω) + 0 -
          nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) -
            NTd θ X₀ ω)))) : ℝ → ℝ) x| ≤
        (fun x => KR.RML6K.aK (CNt X₀) (S x) (Queue6.Hc X₀) x) x := by
  have hX := hc.hX
  obtain ⟨h1, h2, h3, h4⟩ := Zc_facts hc hb
  refine RML7.hK_field hT hX (KR.Chain.p_ge_two_of hT (Xm_le_Zc' hc b))
    (by norm_num [epsH, lamH]) (by norm_num [lamH]) (lam0 := lamH) h4 h3 x0s _ _ _ _
    (fun y => (NKc X₀ y).1) (fun y => (NKc X₀ y).2) (fun y => (NKc_spec hc y).2.1)
    (fun y => (NKc_spec hc y).2.2) S FbK (fun hO => ⟨?_, ?_, hFr hO⟩)
  · exact (LMb_Frx hO (jzX X₀) (LMb_ρLd hc hev ω) (LMb_TcLd hc hev ω) (LMb_NTd hc hev ω)
      LMb.zero).1
  · exact (LMb_Frx hO (jzX X₀) (LMb_ρLd hc hev ω) (LMb_TcLd hc hev ω) (LMb_NTd hc hev ω)
      LMb.zero).2

end BModel

end
