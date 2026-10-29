module

public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.Model.RestMargin10
public import RequestProject.Beurling.Noise.RML10Rest
public import RequestProject.Beurling.Noise.RML11Sum
public import RequestProject.Beurling.Noise.RML11Small
public import RequestProject.Beurling.Model.G1BSec5
public import RequestProject.Beurling.Model.R27
public import RequestProject.Beurling.Noise.RML14H

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

/-- **The open inputs of `RestMargin`** (Proposition 5.38, Steps 4–5) at `(ω, b)`. -/
structure RestMarginH (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) (nb : ℕ → ℝ) where
  /-- the size parameter `E_S ≥ 0` of the recursion (`RML7.canonP`, `j = jzX X₀`; §5) -/
  ES : ℝ
  hES0 : 0 ≤ ES
  /-- **Step 4 of Proposition 5.38** (§5; input `h4` of `RML14.hS4_12_kap`, filtered by
  `κ_w(t)`): at `T₀ ≤ t ≤ b`,
  `log t (o_V + 2η_V + ∑_w e/w) ≤ E_S`, with `e = e12` at the local bound `m* = MfH` -/
  h4 : ∀ t, ((RML7.canonP X₀ epsH ES (jzX X₀)).cinf + (RML7.canonP X₀ epsH ES (jzX X₀)).Kc) ≤ t →
    t ≤ b → Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES (jzX X₀))) t +
      ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES (jzX X₀)) t,
        Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
          (RML12M.e12 X₀ (PR θ X₀ ω) (MfH θ X₀ ω) t w / KR.Vl (PR θ X₀ ω) w)) ≤ ES
  /-- **The sizes of Step 5** (§5, inputs of `RML11.hsmall_11`): `a₅ ≥ 6.5 E_S + V_{X₀}` on
  `[X₁, b]` and `a₅ ≤ 0.0097` (with `j_{X₀} ≤ e^{-59}`, `hjA_c`) -/
  a5 : ℝ
  hEV : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    6.5 * (RML7.canonP X₀ epsH ES (jzX X₀)).ES +
      VX (PR θ X₀ ω) (RML7.canonP X₀ epsH ES (jzX X₀)) t ≤ a5
  ha5 : a5 ≤ 0.0097

variable {θ : ℝ} {X₀ : ℕ}

section Pt

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **The start records `PtAt`** of Step 6(b) at `2X₀ ≤ s ≤ b` (scales `NKc`), from the bridge
record at `s` (`bridge_c2`), `hosc_c2`, `hbdd_c2` and Proposition 5.18(iii). -/
noncomputable def ptAt_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {s : ℝ} (hs : 2 * (X₀ : ℝ) ≤ s) (hsb : s ≤ b) :
    KR.RML11.PtAt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (TcR θ X₀ ω (jzX X₀)) s
      (NKc X₀ s).1 (NKc X₀ s).2 :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n :=
    fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have hH := KR.WidthReal.Hc_pos hX (X₀ := X₀) s
  have hW : InW (Queue6.Hc X₀ s) s s := ⟨by linarith, by linarith⟩
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  have x0s := Queue6.x0sHyp_G0 (e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  let R := bridge_c2 hc hev hb hbs hN.2.1 hX1 hs hsb hW
    (hosc_c2 hc hev hb hbt hG.1 hE1 hN hT hs hsb hW) (hbdd_c2 hc hev hb hT s hs hsb)
  { s0 := KR.X0S.sX0 (X₀ : ℝ)
    o := R.o
    etaX0 := x0s.etaX0SumLoc_of dyScales_dyadic (by linarith)
    etaX0Sum := R.etaX0Sum
    osc := R.osc
    hosc := hosc_c2 hc hev hb hbt hG.1 hE1 hN hT hs hsb hW
    termOsc := R.termOsc }

/-- **The standing inputs `PtGlob`** of Step 6(b) at `X₀ ≤ s ≤ b`. -/
theorem ptGlob_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {s : ℝ} (hs : (X₀ : ℝ) ≤ s) (hsb : s ≤ b) :
    KR.RML11.PtGlob (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) epsH (epsH / 10) lamH (TcR θ X₀ ω (jzX X₀)) s := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hZ := Zc_facts hc hb
  have hZ18 := Zc_18 hc hb
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  exact { htnp := hT
          hO := opR hc hev hbs hN.2.1 hX1
          hHw := KR.WidthReal.Hc_Xm_half_le hX
          hX0e := by unfold Xm Queue6.Hc; rw [max_self]
          hX0m := Xm_le_X0 hc
          hXmZ := hZ.1
          ht := (KR.Chain.dec_R hT).1
          htv := (KR.Chain.dec_R hT).2
          hlam := by norm_num [epsH, lamH]
          hlam1 := by norm_num [lamH]
          hTm := measurable_TcR hc ω _
          hTb := fun u hu => TcR_abs_le hc hev ω hT (le_trans
            (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ18)
          hZ0 := hZ.2.1
          hX0s := hs
          hZ2 := le_trans (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ.2.2.2
          hZ18 := le_trans (by linarith) hZ.2.2.1 }

end Pt

set_option maxHeartbeats 2000000 in
/-- **`RestMargin` from `RestMarginH`** (Proposition 5.38, Steps 2–6, at `j = jzX X₀`,
`s2mst = m* = MfH`, `e = e12`), on `Good(< t)`, `b ≤ t`, given (huxley) and the Step 6(b)
margin decomposition `hRm` (BaseRange, `hRm_ae`). -/
noncomputable def restMargin_of (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t)
    (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) (hH : BaseRange.HuxleyFrom (X₀ : ℝ))
    (hRm : ∀ s, 2 * (X₀ : ℝ) ≤ s → s ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → s ≤ b →
      (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) s
          (fun r => TcR θ X₀ ω (jzX X₀) r + (jzX X₀) * ind X₀ r) - marginM θ X₀ ω s) *
        Real.log s ≤ 1 / 10 ^ 12 - EBRc)
    (R : RestMarginH θ X₀ ω b (Queue6.nbQ X₀)) :
    RestMargin θ X₀ ω b (Queue6.nbQ X₀) :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hnb0 := Queue6.nbQ_nonneg hc
  have hSK0 : ∀ t, 0 ≤ SK θ X₀ ω (Queue6.nbQ X₀) t := fun t => by
    unfold SK
    refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (GK_nonneg hc hev hT hnb0 _)
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have := KR.WidthReal.X0_ge hX (X₀ := X₀)
    exact Real.log_nonneg (by nlinarith)
  have hG0 : ∀ t, 0 ≤ Gsum θ X₀ ω (Queue6.nbQ X₀) t := fun t => by
    unfold Gsum
    refine Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) ?_
    have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
    have h1 := Bsc_nonneg hc (u := Xm X₀ * 2 ^ i) (by positivity)
    have h2 := FrBv_nonneg hc hev hT hnb0 i
    unfold obG; linarith
  have hJ := JcBound_c hc b
  { ES := R.ES
    jP := jzX X₀
    hES0 := R.hES0
    hjP0 := jzX_nonneg hc
    e := RML12M.e12 X₀ (PR θ X₀ ω) (MfH θ X₀ ω)
    s2mst := MfH θ X₀ ω
    hS2sp := RML12M.hS2sp_12 hc.hX (by norm_num) (by norm_num) (CapHSlopeProof.capHSlope hc.hX)
      ω (MfH_nonneg hc hev ω) R.ES (jzX X₀) b (fun z _ => hmH hc hev ω z)
    hS2sm := RML12M.hS2sm_12 hc.hX (by norm_num) (by norm_num) (CapHSlopeProof.capHSlope hc.hX)
      ω (MfH_nonneg hc hev ω) R.ES (jzX X₀) b (fun z _ => hmH hc hev ω z)
    hS2e := RML12M.hS2e_12 hc.hX ω (MfH_nonneg hc hev ω) (MfH_mono hc hev ω) R.ES (jzX X₀) b
    he0 := RML12M.he0_12 hc.hX ω (MfH_nonneg hc hev ω) (MfH_mono hc hev ω) R.ES (jzX X₀) b
    hS4 := RML14.hS4_12_kap hc.hX ω R.ES (jzX X₀) b R.h4
    hsmall := RML11.hsmall_11 hc.hX ω (Queue6.nbQ X₀) R.ES (jzX X₀) b (Real.exp (-59)) R.a5
      (1 / 10 ^ 20) (Real.exp (-41) + 2 / 10 ^ 22) hT (opR hc hev hbs hN.2.1 hX1) (Xm_le_X0 hc)
      (hjA_c hc hev hb hG hbt hN hbs hX1 hH) (by
        have := Real.exp_le_exp.mpr (show (-59 : ℝ) ≤ -41 by norm_num)
        have := KR.RML8E.exp_neg41_le
        linarith)
      (fun t ht htb => ⟨hSK0 t, RML12.hSbX_c hc hev hb hT hJ t ht htb⟩)
      (fun t ht htb => ⟨hG0 t, RML12.hGX_c hc hev hb hT hJ t ht htb⟩) R.hEV (by
        have := KR.RML8E.exp_neg41_le
        have h59 : Real.exp (-59) ≤ Real.exp (-41) :=
          Real.exp_le_exp.mpr (by norm_num)
        have := R.ha5
        linarith)
    hsum := RML11.hsum_11 hc ω b (opR hc hev hbs hN.2.1 hX1) hT.width (jzX_nonneg hc)
      (measurable_TcR hc ω _)
      (fun s hs1 _ hs3 => ptGlob_c hc hev hb hN hbs hX1 (by linarith) hs3)
      (fun s hs1 _ hs3 => ptAt_c hc hev hb hG hbt hN hbs hX1 hs1 hs3)
      (fun s hs1 _ hs3 => hbdd_c2 hc hev hb hT s hs1 hs3) hRm }

end BModel

end
