module

public import RequestProject.Beurling.Noise.RML7Wop
public import RequestProject.Beurling.Noise.MarginRealLoc

/-!
# The fields `hK` and `hG` of `BModel.RealMarginLoc` (round 7)

* `BModel.RML7.hK_field` : the field `hK` (Lemma 5.34, first bullet) with
  `a x = aK C_N (S x) (Hc X₀) x`, from Proposition 5.18 at the localized horizon
  (`KR.TNP.hK_loc`, `wop_start`) and the scale-wise bounds on `F_r` (`FrScaleBound`).
* `BModel.RML7.hG_field` : the field `hG` (Lemma 5.34, second bullet) with
  `bb x = bG C_N (A x) (Hc X₀) x`, from the same weights and the scale-wise bounds on
  `G = K_pt((1 - B)F_c)` (`GScaleBound`, the Lemma 5.21(iii) form).

Both take, besides the `TNP.Hyp` of the realised system (`Queue6.tnpHyp_R`) and the fields of
`RealMarginLoc` they read (`hlam`, `hlam1`, `hZ`, `x0s`), the horizon `18(b + H(b)) ≤ Z²` of
Lemma 5.20 (which follows from `X₀⁻ ≤ Z` and `18(b + H(b))/X₀⁻ ≤ Z`,
`KR.Chain.sq18_of_cofactor`) and the
scale data `Nf`, `Kf` (any choice; `KR.Chain.exists_NK`).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP KR.Chain

namespace BModel.RML7

variable {θ : ℝ} {X₀ : ℕ} {ω : JitterΩ}

/-- The standing facts at the heights `X₀^{1.01} ≤ x ≤ b`, `y` in the window of `x`. -/
lemma win_facts (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ}
    (hP : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) ε (ε / 10)) {Z b x : ℝ}
    (hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z) (hZ18 : 18 * (b + Queue6.Hc X₀ b) ≤ Z ^ 2)
    (hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x) (hxb : x ≤ b) :
    Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 ∧ Xm X₀ ≤ X₀ ∧
      Xm X₀ + Queue6.Hc X₀ x / 2 ≤ x ∧
      ∀ y, x - Queue6.Hc X₀ x / 2 ≤ y → y ≤ x + Queue6.Hc X₀ x / 2 →
        y ≤ b + Queue6.Hc X₀ b ∧ 2 * y / Xm X₀ ≤ Z ∧ 18 * y ≤ Z ^ 2 := by
  have hX0e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
    unfold Xm Queue6.Hc; rw [max_self]
  have hHpos := KR.WidthReal.Hc_pos hX
  have hXmX : Xm X₀ ≤ X₀ := by rw [hX0e]; linarith [hHpos (X₀ : ℝ)]
  have hX0pos : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hX; linarith
  -- `X₀^{1.01} ≥ 2 X₀`
  have hpow : 2 * (X₀ : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) := by
    rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add hX0pos, Real.rpow_one]
    have h2 : (2 : ℝ) ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := by
      rw [Real.rpow_def_of_pos hX0pos]
      have := Real.add_one_le_exp (Real.log (X₀ : ℝ) * 0.01)
      nlinarith
    nlinarith
  have hXm0 := hP.X0m_pos
  have hxsmall : Queue6.Hc X₀ x ≤ x / 10 := hP.small x (by linarith)
  have hHm : Queue6.Hc X₀ x ≤ Queue6.Hc X₀ b := KR.WidthReal.Hc_mono hX hxb
  refine ⟨hX0e, hXmX, by linarith, fun y _ hy2 => ?_⟩
  have hyb : y ≤ b + Queue6.Hc X₀ b := by linarith [hHpos x]
  refine ⟨hyb, le_trans ?_ hZ, by linarith⟩
  apply div_le_div_of_nonneg_right _ hXm0.le
  linarith

/-- **The field `hK` of `RealMarginLoc`** (Lemma 5.34, first bullet), with
`a x = aK C_N (S x) (Hc X₀) x`. -/
theorem hK_field {Z η1 η2 ε lam0 b j0 : ℝ} {ε1 : ℝ → ℝ}
    (htnp : TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε (ε / 10))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j)
    (hlam : 1 + 3 * (ε / 10) ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z) (hZ18 : 18 * (b + Queue6.Hc X₀ b) ≤ Z ^ 2)
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θ
      (b + Queue6.Hc X₀ b))
    (ρL TcL NT vtH : KR.Ops.LocInt)
    (Nf Kf : ℝ → ℕ) (hNf : ∀ y, y < (X₀ : ℝ) * 2 ^ Nf y / 4)
    (hKf : ∀ y, √(2 * y) ≤ Pk (Xm X₀) (Kf y)) (S : ℝ → ℝ) (Fb : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀),
      KR.Ops.LBd ((((KR.Ops.Bo hO TcL - TcL) + vtH -
        nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT : KR.Ops.LocInt)) : ℝ → ℝ) ∧
      Measurable ((((KR.Ops.Bo hO TcL - TcL) + vtH -
        nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT : KR.Ops.LocInt)) : ℝ → ℝ) ∧
      ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
        FrScaleBound (PR θ X₀ ω) (Queue6.Hc X₀) X₀ ((((KR.Ops.Bo hO TcL - TcL) + vtH -
          nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT : KR.Ops.LocInt)) : ℝ → ℝ)
          x (S x) Nf (Fb x)) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ko (tw := twR θ X₀ ω) hO (KR.Ops.Bo hO
        (KR.Ops.Ro (tw := twR θ X₀ ω) hO ((KR.Ops.Bo hO TcL - TcL) + vtH -
          nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT)))) : ℝ → ℝ) x| ≤
        (fun x => RML6K.aK (CNt X₀) (S x) (Queue6.Hc X₀) x) x := by
  intro hO x hx hxb
  obtain ⟨hX0e, hXmX, hxH, hwin⟩ := win_facts hX htnp.width hZ hZ18 hx hxb
  obtain ⟨hFL, hFm, hFb⟩ := hF hO
  obtain ⟨ht, htv⟩ := dec_R htnp
  have hθ0 := htnp.width.theta_nonneg
  exact hK_loc htnp (KR.WidthReal.Hc_Xm_half_le hX) hO hX0e hXmX hp2 ht htv
    (by linarith) hlam1 _ hFL hFm hxH x0s.hZ
    (fun y h1 h2 => ⟨(hwin y h1 h2).2.1, (hwin y h1 h2).2.2⟩)
    Nf Kf hNf hKf (fun _ => KR.X0S.sX0 X₀)
    (fun y h1 h2 => x0s.etaX0SumLoc_of dyScales_dyadic (hwin y h1 h2).1) (Fb x) (hFb x hx hxb)

/-- **The field `hG` of `RealMarginLoc`** (Lemma 5.34, second bullet), with
`bb x = bG C_N (A x) (Hc X₀) x`. -/
theorem hG_field {Z η1 η2 ε lam0 b j0 : ℝ} {ε1 : ℝ → ℝ}
    (htnp : TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε (ε / 10))
    (hX : 10 ^ 8 ≤ Real.log X₀) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j)
    (hlam : 1 + 3 * (ε / 10) ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hZ : 2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Z) (hZ18 : 18 * (b + Queue6.Hc X₀ b) ≤ Z ^ 2)
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θ
      (b + Queue6.Hc X₀ b))
    (ρL TcL NT vtH : KR.Ops.LocInt)
    (Nf Kf : ℝ → ℕ) (hNf : ∀ y, y < (X₀ : ℝ) * 2 ^ Nf y / 4)
    (hKf : ∀ y, √(2 * y) ≤ Pk (Xm X₀) (Kf y)) (A : ℝ → ℝ) (Gb : ℝ → ℝ → ℝ → ℝ)
    (hGf : ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀),
      KR.Ops.LBd ((KR.Ops.Ko (tw := twR θ X₀ ω) hO
        ((KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT -
            NT - KR.Ops.Bo hO (JL j0 X₀)) -
          KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
            nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀))) :
          KR.Ops.LocInt) : ℝ → ℝ) ∧
      Measurable ((KR.Ops.Ko (tw := twR θ X₀ ω) hO
        ((KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH - nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT -
            NT - KR.Ops.Bo hO (JL j0 X₀)) -
          KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
            nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀))) :
          KR.Ops.LocInt) : ℝ → ℝ) ∧
      ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
        GScaleBound (PR θ X₀ ω) (Queue6.Hc X₀) X₀ ((KR.Ops.Ko (tw := twR θ X₀ ω) hO
          ((KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
              nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀)) -
            KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
              nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀))) :
            KR.Ops.LocInt) : ℝ → ℝ) x (A x) Nf (Gb x)) :
    ∀ hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀), ∀ x,
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      Real.log x * |(KR.Ops.Bo hO (KR.Ops.Ro (tw := twR θ X₀ ω) hO
        (KR.Ops.Ko (tw := twR θ X₀ ω) hO
          ((KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
              nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT - KR.Ops.Bo hO (JL j0 X₀)) -
            KR.Ops.Bo hO (KR.Ops.Bo hO (TcL + JL j0 X₀) + vtH -
              nuRes hO (twR θ X₀ ω) ρL TcL (JL j0 X₀) vtH NT - NT -
                KR.Ops.Bo hO (JL j0 X₀))))) : ℝ → ℝ) x| ≤
        (fun x => bG (CNt X₀) (A x) (Queue6.Hc X₀) x) x := by
  intro hO x hx hxb
  obtain ⟨hX0e, hXmX, hxH, hwin⟩ := win_facts hX htnp.width hZ hZ18 hx hxb
  obtain ⟨hGL, hGm, hGb⟩ := hGf hO
  obtain ⟨ht, htv⟩ := dec_R htnp
  have hθ0 := htnp.width.theta_nonneg
  exact hG_loc htnp (KR.WidthReal.Hc_Xm_half_le hX) hO hX0e hXmX hp2 ht htv
    (by linarith) hlam1 _ hGL hGm hxH x0s.hZ
    (fun y h1 h2 => ⟨(hwin y h1 h2).2.1, (hwin y h1 h2).2.2⟩)
    Nf Kf hNf hKf (fun _ => KR.X0S.sX0 X₀)
    (fun y h1 h2 => x0s.etaX0SumLoc_of dyScales_dyadic (hwin y h1 h2).1) (Gb x) (hGb x hx hxb)

end BModel.RML7

end
