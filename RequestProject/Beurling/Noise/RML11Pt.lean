module

public import RequestProject.Beurling.Noise.RML10G1Win

/-!
# Proposition 5.26 and Lemma 5.27 at a single start `s`, with given scale indices

`RML10G1Win.brs_of`/`xbs_of` are stated at the window heights of a range-(B) start. Here the
same two statements are proved at one start `s` with prescribed scale indices `N, K` (as the
field `hsum` of `RestMargin` needs at `t ∈ [2X₀, X₀^{1.01}]`, with `(N, K) = NKc X₀ t`):

* `brs_pt` : `log s · |BR_c(s)| ≤ e^{-76}` (Proposition 5.26 via `KR.TcLoc.prop_5_26_loc`, the
  size `sizeE_le9`, Lemma 5.20 at `s` by `l520At_of_loc`);
* `xbs_pt` : Lemma 5.27 at `s`, in exactly the form of `RestMargin.hsum`'s input.

The start-dependent inputs (step (iii), eq. (osc), the terminal oscillation) are bundled in
`PtAt`.
-/

@[expose] public section

open Real Set Finset BeurlingSystem

namespace KR.RML11

open KR.TNP KR.Chain KR.RML10

/-- **The start-dependent inputs at a start `s`, for the scale indices `N, K`.** -/
structure PtAt (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (Tc : ℝ → ℝ)
    (s : ℝ) (N K : ℕ) : Type where
  s0 : ℝ → ℝ
  o : ℝ → ℝ
  /-- Proposition 5.18, step (iii), at the positions `≤ s` (`X0S.etaX0SumLoc_of`) -/
  etaX0 : EtaX0SumLoc P (Queue6.Hc X₀) X0m X₀ (dyScales X₀ s N) s0 s
  etaX0Sum : ∑ v ∈ dyScales (X₀ : ℝ) s N, s0 v ≤ 1.52
  /-- eq. (osc): the oscillation of `T_c` at the scales of `s`, and its first display -/
  osc : OscBound P (Queue6.Hc X₀) s Tc (dyScales X₀ s N) o
  hosc : ∑ u ∈ dyScales (X₀ : ℝ) s N, Real.log (2 * u) * o u ≤ Real.exp (-83)
  /-- the terminal oscillation (proof of Proposition 5.26, second bullet) -/
  termOsc : TermOsc P (Queue6.Hc X₀) tw X0m s Tc (o X₀)

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X₀ : ℕ} {Z η1 η2 : ℝ}
  {ε1 : ℝ → ℝ} {εW θW lam0 : ℝ} {Tc : ℝ → ℝ}

/-- **The standing inputs at a start `s`.** -/
structure PtGlob (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (Z η1 η2 : ℝ)
    (ε1 : ℝ → ℝ) (εW θW lam0 : ℝ) (Tc : ℝ → ℝ) (s : ℝ) : Prop where
  htnp : Hyp P (Queue6.Hc X₀) tw X0m Z η1 η2 ε1 εW θW
  hO : KR.Ops.OpHyp P (Queue6.Hc X₀) X0m
  hHw : Queue6.Hc X₀ (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)
  hX0e : X0m = X₀ - Queue6.Hc X₀ X₀ / 2
  hX0m : X0m ≤ X₀
  hXmZ : X0m ≤ Z
  ht : ∀ r, r.Prime → 0 < tw r
  htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r
  hlam : 1 + 3 * θW ≤ lam0
  hlam1 : lam0 ≤ 1.001
  hTm : Measurable Tc
  hTb : ∀ t, t ≤ 1.2 * s → |Tc t| ≤ 2
  hZ0 : 2500 ≤ Z
  hX0s : (X₀ : ℝ) ≤ s
  hZ2 : 2 * s / X0m ≤ Z
  hZ18 : 18 * s ≤ Z ^ 2

/-- The `BridgeAt` data at a start `s` with scale indices `N, K`. -/
noncomputable def bridgeAt_pt {s : ℝ} (G : PtGlob P tw X0m X₀ Z η1 η2 ε1 εW θW lam0 Tc s)
    {N K : ℕ} (hN2 : 2 < N) (hN : s < (X₀ : ℝ) * 2 ^ N / 4) (hK : √(2 * s) ≤ Pk X0m K)
    (W : PtAt P tw X0m X₀ Tc s N K) :
    BridgeAt P (Queue6.Hc X₀) tw X0m X₀ θW lam0 Tc 0 s
      ((5.1 * CNc X₀ + CSc) * ∑ u ∈ dyScales (X₀ : ℝ) s N, Real.log (2 * u) * W.o u +
        8.4 * CNc X₀ * ∑ v ∈ dyScales (X₀ : ℝ) s N,
          Real.log (2 * v) * sTheta P (Queue6.Hc X₀) X0m K v) 0 := by
  have hθ0 := G.htnp.width.theta_nonneg
  have hl1 := G.hlam1
  have hl0 := G.hlam
  exact BridgeAtL.toBridgeAt (Z := Z) (η1 := η1) (η2 := η2) (ε1 := ε1) (ε := εW)
    { N := N
      K := K
      hN2 := hN2
      hN := hN
      hK := hK
      s0 := W.s0
      o := W.o
      etaX0 := W.etaX0
      etaX0Sum := W.etaX0Sum
      osc := W.osc
      termOsc := W.termOsc
      sizeE := le_rfl
      sizeJ := by simp
      l520 := l520At_of_loc G.htnp G.hHw G.hX0e G.hX0m G.hZ0 G.hZ18 hK
        (by linarith) (by linarith) }
    G.htnp G.hX0e G.hX0m G.hX0s

/-- **Proposition 5.26 at a start `s`**: `log s · |BR_c(s)| ≤ e^{-76}`. -/
theorem brs_pt {s : ℝ} (G : PtGlob P tw X0m X₀ Z η1 η2 ε1 εW θW lam0 Tc s)
    {N K : ℕ} (hN2 : 2 < N) (hN : s < (X₀ : ℝ) * 2 ^ N / 4) (hK : √(2 * s) ≤ Pk X0m K)
    (W : PtAt P tw X0m X₀ Tc s N K) :
    Real.log s * |KR.BRc P (Queue6.Hc X₀) tw X0m s Tc| ≤ Real.exp (-76) := by
  have hθ0 := G.htnp.width.theta_nonneg
  have hΛ := (sizes G.htnp G.hX0e G.hX0m).2.1
  have hp2 := KR.Chain.p_ge_two_of G.htnp G.hXmZ
  set D := bridgeAt_pt G hN2 hN hK W
  have hBR := KR.TcLoc.prop_5_26_loc G.htnp.hbs G.htnp.hXm G.htnp.width G.hO G.hX0e hp2 G.ht
    G.htv (lam0 := lam0) (by linarith [G.hlam]) G.hlam1 (G.hX0m.trans G.hX0s) G.hZ2
    (by linarith) G.hX0m G.hX0s D.cov D.covL D.sc1 D.sc D.eta D.etaSmall D.etaX0 D.theta
    G.hTm G.hTb D.osc D.X0mem D.termOsc
  have hsz := sizeE_le9 G.htnp G.hHw hΛ G.hX0e G.hX0m G.hZ0 G.hZ18 hK W.hosc
  have he := Real.exp_pos (-76)
  exact hBR.trans (hsz.trans (by linarith))

/-- **Lemma 5.27 at a start `s`**: `|R_res 1 - ρ^sh 1|(s) ≤ 𝔅(s) + 4.3 C_N E_θ/log s`. -/
theorem xbs_pt {s : ℝ} (G : PtGlob P tw X0m X₀ Z η1 η2 ε1 εW θW lam0 Tc s)
    {N K : ℕ} (hN2 : 2 < N) (hN : s < (X₀ : ℝ) * 2 ^ N / 4) (hK : √(2 * s) ≤ Pk X0m K)
    (W : PtAt P tw X0m X₀ Tc s N K) :
    |KR.Rres P (Queue6.Hc X₀) tw X0m s (KR.Chain.ind X₀) -
      KR.rhoSh P tw X0m s (KR.Chain.ind X₀)| ≤
      xbB P (Queue6.Hc X₀) tw X0m s X₀ θW lam0 +
        4.3 * CNc X₀ * (∑ v ∈ dyScales (X₀ : ℝ) s N, Real.log (2 * v) *
          sTheta P (Queue6.Hc X₀) X0m K v) / Real.log s := by
  have hΛ := (sizes G.htnp G.hX0e G.hX0m).2.1
  have hp2 := KR.Chain.p_ge_two_of G.htnp G.hXmZ
  set D := bridgeAt_pt G hN2 hN hK W
  have hXB := lemma_5_27 G.htnp.hbs G.htnp.hXm G.htnp.width G.hX0e hp2 G.ht G.htv
    (lam0 := lam0) G.hlam G.hlam1 (G.hX0m.trans G.hX0s) G.hZ2 (by linarith) G.hX0m D.cov
    D.sc1 D.sc D.eta D.etaSmall D.etaX0.1 D.etaX0Sum D.theta
  exact hXB

end KR.RML11

end
