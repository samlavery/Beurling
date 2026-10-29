module

public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.Model.RestMargin10
public import RequestProject.Beurling.Noise.RML10Rest

/-!
# `RestMargin` from §5's `RML10` field theorems and the residual inputs `RestMarginH`

At `j = jzX X₀`, `s2mst = m*` (`Mm`), `e = e10 X₀ P m*`: Steps 2–3 (`hS2sp`, `hS2sm`, `hS2e`,
`he0`) are `RML10.hS2sp_10` etc. with `hm10` and `capHSlope`; Step 4 (`hS4`), the sizes of
Step 5 (`hsmall`) and Step 6(b) (`hsum`) are `RML10.hS4_10`, `hsmall_10`, `hsum_10` from the
residual inputs collected in `RestMarginH` (owners in the field docstrings).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction KR KR.TNP KR.Chain CaplLink Queue6

namespace BModel

/-- **The open inputs of `RestMargin`** (Proposition 5.38, Steps 4–6) at `(ω, b)`. -/
structure RestMarginH (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) (nb : ℕ → ℝ) where
  /-- the size parameter `E_S ≥ 0` of the recursion (`RML7.canonP`, `j = jzX X₀`; §5) -/
  ES : ℝ
  hES0 : 0 ≤ ES
  /-- **Step 4 of Proposition 5.38** (§5; input `h4` of `RML10.hS4_10`): at `T₀ ≤ t ≤ b`,
  `log t (o_V + 2η_V + ∑_w e/w) ≤ E_S` -/
  h4 : ∀ t, ((RML7.canonP X₀ epsH ES (jzX X₀)).cinf + (RML7.canonP X₀ epsH ES (jzX X₀)).Kc) ≤ t →
    t ≤ b → Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES (jzX X₀))) t +
      ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES (jzX X₀)) t,
        RML10.e10 X₀ (PR θ X₀ ω) (Mm θ X₀ ω b) t w / KR.Vl (PR θ X₀ ω) w) ≤ ES
  /-- **Step 6(b), "Sum"** (§5; input `hin` of `RML10.hsum_10`): Proposition 5.26, Lemma 5.27,
  the `j_{X₀}` family bounded, and the margin decomposition, on `[2X₀, X₀^{1.01}]` -/
  hin : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
    Xm X₀ ≤ t ∧ 0 < Real.log t ∧
    (∀ u, u ≤ 1.2 * t → |TcR θ X₀ ω (jzX X₀) u| ≤ 2) ∧
    Real.log t * |BRc (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
      (TcR θ X₀ ω (jzX X₀))| ≤ EBRc ∧
    |Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t (KR.Chain.ind X₀) -
        rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (KR.Chain.ind X₀)| ≤
      xbB (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t X₀ (epsH / 10) lamH +
        4.3 * CNc X₀ * (∑ v ∈ dyScales X₀ t (NKc X₀ t).1, Real.log (2 * v) *
          TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NKc X₀ t).2 v) / Real.log t ∧
    BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ t) t y} =>
      jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀ y.1).1 (NKc X₀ y.1).2 y.1) ∧
    (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
        (fun s => TcR θ X₀ ω (jzX X₀) s + (jzX X₀) * ind X₀ s) - marginM θ X₀ ω t) *
      Real.log t ≤ 1 / 10 ^ 12 - EBRc
  /-- **The sizes of Step 5** (inputs of `RML10.hsmall_10`): `a₂ ≥ a_K` (Lemma 5.34, first
  bullet; Model, needs the Lemma 5.20 sums of `s_η`), `a₃ ≥` the `G`-term (second bullet;
  idem), `a₄ ≥ j_{X₀}` on `[X₁, b]` (§5, Proposition 5.31), `a₅ ≥ 6.5 E_S + V_{X₀}` (§5) -/
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a5 : ℝ
  hjA : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
      (NKc X₀) t ≤ a4
  ha4 : a4 ≤ 1 / 2
  haK : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    KR.RML6K.aK (CNt X₀) (SK θ X₀ ω nb t) (Queue6.Hc X₀) t ≤ a2
  hGa : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    35.8 * CNt X₀ * 10 * ∑ i ∈ Finset.range (Jc X₀ t + 1), Real.log (3 *
      (Xm X₀ * 2 ^ i)) ^ 2 * (obG X₀ i + FrBv θ X₀ ω nb i) ≤ a3
  hEV : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    6.5 * (RML7.canonP X₀ epsH ES (jzX X₀)).ES +
      VX (PR θ X₀ ω) (RML7.canonP X₀ epsH ES (jzX X₀)) t ≤ a5
  hsum4 : a2 + a3 + a4 + a5 ≤ 0.0099

variable {θ : ℝ} {X₀ : ℕ}

set_option maxHeartbeats 2000000 in
/-- **`RestMargin` from `RestMarginH`** (Proposition 5.38, Steps 2–6, at `j = jzX X₀`,
`s2mst = m*`, `e = e10`). -/
noncomputable def restMargin_of (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {nb : ℕ → ℝ} (R : RestMarginH θ X₀ ω b nb) :
    RestMargin θ X₀ ω b nb where
  ES := R.ES
  jP := jzX X₀
  hES0 := R.hES0
  hjP0 := jzX_nonneg hc
  e := RML10.e10 X₀ (PR θ X₀ ω) (Mm θ X₀ ω b)
  s2mst := fun _ => Mm θ X₀ ω b
  hS2sp := RML10.hS2sp_10 hc.hX (by norm_num) (by norm_num) (CapHSlopeProof.capHSlope hc.hX) ω
    (Mm_nonneg hc ω b) R.ES (jzX X₀) b (hm10 hc hev ω R.ES (jzX X₀) b hb)
  hS2sm := RML10.hS2sm_10 hc.hX (by norm_num) (by norm_num) (CapHSlopeProof.capHSlope hc.hX) ω
    (Mm_nonneg hc ω b) R.ES (jzX X₀) b (hm10 hc hev ω R.ES (jzX X₀) b hb)
  hS2e := RML10.hS2e_10 hc.hX ω (Mm_nonneg hc ω b) R.ES (jzX X₀) b
  he0 := RML10.he0_10 hc.hX ω (Mm_nonneg hc ω b) R.ES (jzX X₀) b
  hS4 := RML10.hS4_10 hc.hX ω R.ES (jzX X₀) b R.h4
  hsmall := RML10.hsmall_10 hc.hX ω nb R.ES (jzX X₀) b R.a2 R.a3 R.a4 R.a5
    (fun t ht htb => ⟨jXnn_c hc hev (tnpR hc hev hbs hN.2.1 hX1) (by norm_num [lamH])
      (jzX_nonneg hc) (NKc X₀) t, R.hjA t ht htb⟩) R.ha4 R.haK R.hGa R.hEV
    (KR.WidthReal.Phi_tiny (tnpR hc hev hbs hN.2.1 hX1) (KR.WidthReal.Hc_Xm_half_le hc.hX)
      (by norm_num)) R.hsum4
  hsum := RML10.hsum_10 hc.hX ω b (opR hc hev hbs hN.2.1 hX1) (tnpR hc hev hbs hN.2.1 hX1).width
    (jzX_nonneg hc) (measurable_TcR hc ω _) R.hin

end BModel

end
