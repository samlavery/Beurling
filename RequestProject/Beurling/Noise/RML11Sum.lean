module

public import RequestProject.Beurling.Noise.RML10Rest
public import RequestProject.Beurling.Noise.RML11Pt

/-!
# The field `hsum` of `RestMargin` with Proposition 5.26 and Lemma 5.27 instantiated

`hsum_11` is `BModel.RML10.hsum_10` with the two §5 items of its input `hin` (Proposition 5.26
and Lemma 5.27 at each `t ∈ [2X₀, X₀^{1.01}]`, `t ≤ b`) proved by `KR.RML11.brs_pt` and
`KR.RML11.xbs_pt` at the scale indices `NKc X₀ t`. What remains is, at each such `t`, the
standing data `PtGlob` (Queue6's `TNP.Hyp`, and Model facts), the start data `PtAt` (step (iii),
eq. (osc), the terminal oscillation), the boundedness of the `j_{X₀}` family on `W_t` and the
margin decomposition.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML11

open KR.TNP KR.Chain KR.RML11

variable {θ : ℝ} {X₀ : ℕ}

/-- **The field `hsum`** of `RestMargin` (Step 6(b)), with Proposition 5.26 and Lemma 5.27
proved. -/
theorem hsum_11 (hc : Cond θ X₀) (ω : JitterΩ) (b : ℝ)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {εW θW : ℝ} (hP : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) εW θW)
    (hj00 : 0 ≤ jzX X₀) (hTm : Measurable (TcR θ X₀ ω (jzX X₀))) {Z η1 η2 : ℝ}
    {ε1 : ℝ → ℝ}
    (G : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      PtGlob (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ Z η1 η2 ε1 epsH (epsH / 10) lamH
        (TcR θ X₀ ω (jzX X₀)) t)
    (W : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      PtAt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (TcR θ X₀ ω (jzX X₀)) t
        (NKc X₀ t).1 (NKc X₀ t).2)
    (hbdd : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ t) t y} =>
        jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
          (NKc X₀ y.1).1 (NKc X₀ y.1).2 y.1))
    (hRm : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
          (fun s => TcR θ X₀ ω (jzX X₀) s + (jzX X₀) * ind X₀ s) - marginM θ X₀ ω t) *
        Real.log t ≤ 1 / 10 ^ 12 - EBRc) :
    ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω (jzX X₀) s +
        (jzX X₀) * ind X₀ s) *
        Real.log t - (fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀
          (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t - 1 / 10 ^ 12 ≤ marginM θ X₀ ω t *
            Real.log t := by
  refine RML10.hsum_10 hc.hX ω b hO hP hj00 hTm ?_
  intro t h1 h2 h3
  have Gt := G t h1 h2 h3
  obtain ⟨hN2, hN, hK⟩ := NKc_spec hc t
  have h4 := (sizes Gt.htnp Gt.hX0e Gt.hX0m).2.2.2.1
  have hX0t := Gt.hX0s
  refine ⟨Gt.hX0m.trans hX0t, Real.log_pos (by linarith), Gt.hTb, ?_, ?_, hbdd t h1 h2 h3,
    hRm t h1 h2 h3⟩
  · exact brs_pt Gt hN2 hN hK (W t h1 h2 h3)
  · exact xbs_pt Gt hN2 hN hK (W t h1 h2 h3)

end BModel.RML11

end
