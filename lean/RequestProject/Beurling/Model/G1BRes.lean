module

public import RequestProject.Beurling.Model.G1BWire
public import RequestProject.Beurling.Model.G1BJumpProof
public import RequestProject.Beurling.Model.G1BRprime
public import RequestProject.Beurling.Model.FrBound
public import RequestProject.Beurling.Noise.RML9G1

/-!
# The Model group `G1ResModel` of `KR.RML9.g1BInputs_of` (Proposition 5.35(B))

At the realised system (`P = PR θ X₀ ω`, `tw = twR`, `X₀⁻ = Xm X₀`), the Model data
`ρ̃ = ρLd`, `T_c = TcLd`, `J = JL j₀ X₀`, `ϑ = 0`, `NT = B NT_pt`, `ν = nuLd` (the residual of the
margin identity), `δ = deltaB`, the threshold mass `thrS = threshSum tJ y (2δ)`, and the horizon
`Z = Zc b`: `g1ResModel_c` supplies every field of `KR.RML9.G1ResModel` on `Good(< t)`, from
`hT_c` (Theorem 5.24 at `y(1-δ)`), `deltaB_*` (the `δ` bounds), `step3_R` with `jumpCount_c` and
`rprimeChange_c` (Steps 3–4), `capHSlope`, `tnpR` (width, `dec_R`), `Zc_facts`/`Zc_18`
(horizons), `TcR_abs_le` (`|T_c| ≤ 2` below `3y`), `margin_nuRes` (`hmargin`), `hTLBd_c`,
`NTd_eq` and `NTpt_abs_le_eta` (`|NT_pt| ≤ 2η ≤ 54η`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

open Classical in
variable (θ X₀) in
/-- **`ν` of the Model** (the residual of the margin identity at `ϑ = 0`), as a function of
`(θ, X₀, ω)`. -/
noncomputable def nuLd (ω : JitterΩ) : KR.Ops.LocInt :=
  if h : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) then
    nuRes h (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω)
  else 0

lemma nuLd_eq (ω : JitterΩ) (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    nuLd θ X₀ ω =
      nuRes hO (twR θ X₀ ω) (ρLd θ X₀ ω) (TcLd θ X₀ ω) (JL (jzX X₀) X₀) 0 (NTd θ X₀ ω) := by
  unfold nuLd; rw [dif_pos hO]

lemma etaG_nonneg (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m s : ℝ) :
    0 ≤ KR.etaG P H tw X0m (fun _ => 1) s := by
  unfold KR.etaG
  exact Finset.sum_nonneg fun m _ => div_nonneg zero_le_one (KR.Sharp.Vl_pos P m).le

lemma y_pos_c (hc : Cond θ X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) : 0 < y := by
  have := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **The Model group of `KR.RML9.g1BInputs_of`** at a range-(B) start `y`, on `Good(< t)`. -/
noncomputable def g1ResModel_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hbt : b ≤ t) (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    KR.RML9.G1ResModel (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ y (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) epsH (epsH / 10) (4 / 1000000) (deltaB θ X₀ ω y)
      ((PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y))
      (ρLd θ X₀ ω) (nuLd θ X₀ ω) (NTd θ X₀ ω) 0 (TcLd θ X₀ ω) (JL (jzX X₀) X₀) (fun _ => 0)
      (NTpt θ X₀ ω) (TcR θ X₀ ω (jzX X₀)) hO :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hZ := Zc_facts hc hb
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  let S := step3_R hc hev hb hbt hQC hE1 hN hT hy hyb hyL (deltaB_pos hc ω hy)
    (deltaB_le (θ := θ) ω y)
    (jumpCount_c hc hev hb hbt hQC hE1 hN hy hyb hyL) (rprimeChange_c hc ω hb hT hy hyb)
  { θc := θ
    hc := hc
    hδ0 := deltaB_pos hc ω hy
    hδ := deltaB_le (θ := θ) ω y
    hδlow := deltaB_low hc ω hy
    hδL := deltaB_L hc ω hy
    hT := hT_c hc hev hb hbt hQC hE1 hN hy hyb hyL
    hbs := hbs
    hS := CapHSlopeProof.capHSlope hX
    hεS0 := by norm_num
    hεS1 := by norm_num
    hPW := hT.width
    hXm1 := hO.one_le
    hX0m := Xm_le_X0 hc
    htw := (KR.Chain.dec_R hT).1
    hZ := le_trans (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ.2.2.2
    hZ0 := hZ.2.1
    hZ18 := le_trans (by linarith) hZ.2.2.1
    hTm := measurable_TcR hc ω _
    hTb := fun s hs => TcR_abs_le hc hev ω hT (le_trans
      (div_le_div_of_nonneg_right (by linarith) hXm0.le) (Zc_18 hc hb))
    hTcL := TcLd_coe hc hev ω
    hJl := rfl
    hvt := fun z => by simp
    hmargin := by
      rw [nuLd_eq ω hO]
      exact margin_nuRes hO (twR θ X₀ ω) _ _ _ _ _
    hLBd := by
      have h := hTLBd_c hc hev ω
      have e : ((TcLd θ X₀ ω + JL (jzX X₀) X₀ : KR.Ops.LocInt) : ℝ → ℝ) =
          fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t := by
        funext t
        show (TcLd θ X₀ ω : ℝ → ℝ) t + jzX X₀ * KR.Chain.ind X₀ t = _
        rw [TcLd_coe hc hev ω]
      rw [e]; exact h
    hNTeq := fun z => by
      rw [NTd_eq ω hO]
      show Margin.Bavg (Queue6.Hc X₀ z) (NTptLd θ X₀ ω : ℝ → ℝ) z = _
      rw [NTptLd_coe hc hev ω]
    hNTpt := fun s _ _ => by
      have h1 := NTpt_abs_le_eta hc hev ω s
      have h2 := etaG_nonneg (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) s
      linarith
    j0 := S.j0
    jS := S.jS
    detS := S.detS
    othS := S.othS
    hdec34 := S.hdec34
    N := S.N
    HN := S.HN
    θ := S.θ
    hj0 := S.hj0
    hj1 := S.hj1
    hjS := S.hjS
    hN := S.hN
    hHN0 := S.hHN0
    hHN := S.hHN
    hθ0 := S.hθ0
    hθ := S.hθ
    CS := S.CS
    hCS0 := S.hCS0
    hCS := S.hCS
    hdet := S.hdet
    hoth := S.hoth }

end BModel

end
