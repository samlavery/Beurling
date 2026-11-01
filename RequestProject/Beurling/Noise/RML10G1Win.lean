module

public import RequestProject.Beurling.Noise.RML10G1Size
public import RequestProject.Beurling.Noise.RML9HJ
public import RequestProject.Beurling.Noise.L520Loc
public import RequestProject.Beurling.Noise.MarginChainLoc

/-!
# Proposition 5.26, Lemma 5.27 and Proposition 5.31(iii) at the window heights

At the heights `s ∈ [y/4, 2y]` read by `KR.RML6.G1BInputs` at a range-(B) start `y`
(`X₀^{1/100} < log y`), for `H = H_c`:

* `brs_of` : `|BR_c(s)| ≤ e^{-76}/log y` (Proposition 5.26 via `KR.TcLoc.prop_5_26_loc`, with
  the size `≤ 0.9 e^{-76}` of `sizeE_le9`, a sharpening of `sizeE_le`, and Lemma 5.20 at `s`
  by `l520At_of_loc`);
* `xbs_of` : `|R_res 1 - ρ^sh 1|(s) ≤ 𝔅_y` with
  `𝔅_y = (2·10⁵ H(X₀)/X₀ + e^{-61}) Λ/(log y - log 4 - Λ) + e^{-178}/(log y - log 4)`
  (Lemma 5.27, Proposition 5.31(iii) `xbB_huge`, `cne_le`);
* `hBx_of` : `𝔅_y ≤ (400 δ_x + e^{-60}) τ₀/(log y - Λ)` with `δ_x = e^{-60}/800`,
  `τ₀ = 1.0001 Λ`.

The start-dependent inputs at `s` are bundled in `WinAt` (the scale indices, the step (iii)
data, eq. (osc), the terminal oscillation, Theorem 5.24 at `2(s/X₀)^{0.55}` and Lemma 5.29).
-/

@[expose] public section

open Real Set Finset BeurlingSystem

namespace KR.RML10

open KR.TNP KR.Chain

/-- `600 Λ⁴ + Λ + 2 ≤ e^{Λ/100}` for `Λ ≥ 10⁸`. -/
lemma huge_exp {Λ : ℝ} (hΛ : 100000000 ≤ Λ) : 600 * Λ ^ 4 + Λ + 2 ≤ Real.exp (Λ / 100) := by
  have ht : 0 ≤ Λ / 100 := by positivity
  have h8 := Real.pow_div_factorial_le_exp (x := Λ / 100) ht 8
  have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hf] at h8
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have e : (Λ / 100) ^ 8 / 40320 = Λ ^ 4 * (Λ ^ 4 / (10 ^ 16 * 40320)) := by ring
  have h1 : 601 ≤ Λ ^ 4 / (10 ^ 16 * 40320) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hΛ1 : Λ ≤ Λ ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have : 600 * Λ ^ 4 + Λ + 2 ≤ (Λ / 100) ^ 8 / 40320 := by rw [e]; nlinarith
  linarith

lemma log4_lt : Real.log 4 < 1.4 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9; linarith

lemma log4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- **The start-dependent inputs at a window height `s`.** -/
structure WinAt (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (Tc : ℝ → ℝ)
    (s : ℝ) : Type where
  /-- the scale indices (`KR.Chain.exists_NK`) -/
  N : ℕ
  K : ℕ
  hN2 : 2 < N
  hN : s < (X₀ : ℝ) * 2 ^ N / 4
  hK : √(2 * s) ≤ Pk X0m K
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
  /-- Theorem 5.24 at `2(s/X₀)^{0.55}` (Model / LocalPNT) -/
  hT : LocalPNT.Theorem524Concl P X₀ (2 * (s / X₀) ^ (0.55 : ℝ))
  /-- Lemma 5.29 on `Good(< s)` (Queue6) -/
  hSR : KR.RML9.ShortRecipLow P X₀ s

/-- **The right side of Proposition 5.26 is at most `0.9 e^{-76}`** (as `sizeE_le`). -/
theorem sizeE_le9 {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ}
    {ε1 : ℝ → ℝ} {ε θ : ℝ} (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 y : ℝ} (hX0 : 100000000 ≤ Real.log X0)
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hZ0 : 2500 ≤ Z) (h18 : 18 * y ≤ Z ^ 2)
    {N K : ℕ} (hK : √(2 * y) ≤ Pk X0m K) {o : ℝ → ℝ}
    (hosc : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u ≤ Real.exp (-83)) :
    (5.1 * CNc X0 + CSc) * ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u +
      8.4 * CNc X0 * ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v ≤
        0.9 * Real.exp (-76) := by
  obtain ⟨-, -, -, h4, hX0p⟩ := sizes h hX0e hX0m
  have h1 : Sep (dyScales X0 y N) := dyScales_sep hX0p
  have h2 : ∀ v ∈ dyScales X0 y N, 1 ≤ v := fun v hv => dyScales_ge h4 hv
  have h3 : ∀ v ∈ dyScales X0 y N, 18 * v ≤ Z ^ 2 := fun v hv => by
    have := dyScales_le hv; linarith
  have h5 : ∀ v ∈ dyScales X0 y N, √(2 * v) ≤ Pk X0m K := fun v hv =>
    sqrt_le_Pk hK (dyScales_le hv)
  have hθ := (thetaBlk_sum_loc h h1 h2 hZ0 h3 h5).2
  have hΦ := WidthReal.Phi_tiny h hH (a := 3) (by norm_num)
  obtain ⟨hCN0, hCN⟩ := CNc_bounds hX0
  obtain ⟨hCS0, hCS⟩ := CSc_bounds
  set S1 := ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u
  set S2 := ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v
  have hS2 : S2 ≤ 2493700 * Real.exp (-200) := hθ.trans (by nlinarith)
  have hS20 : 0 ≤ S2 := by
    apply Finset.sum_nonneg
    intro v hv
    apply mul_nonneg (Real.log_nonneg (by linarith [h2 v hv]))
    exact blk_nonneg (P := P) (H := H) (X0m := X0m) h.width K
      (fun k => by have := log_Pk_ge h.width.X0m_pos h.hXm k; linarith) v
  have hA : 5.1 * CNc X0 + CSc ≤ 883 := by nlinarith
  have hA0 : 0 ≤ 5.1 * CNc X0 + CSc := by positivity
  have he83 : Real.exp (-76) = Real.exp 7 * Real.exp (-83) := by
    rw [← Real.exp_add]; norm_num
  have he200 : Real.exp (-200) = Real.exp (-117) * Real.exp (-83) := by
    rw [← Real.exp_add]; norm_num
  have he117 := exp_neg117_le
  have h83 := Real.exp_pos (-83)
  have he7 := exp7_ge
  have hS1 : (5.1 * CNc X0 + CSc) * S1 ≤ 883 * Real.exp (-83) := by
    rcases le_total 0 S1 with hS1 | hS1
    · exact (mul_le_mul_of_nonneg_left hosc hA0).trans
        (mul_le_mul_of_nonneg_right hA h83.le)
    · nlinarith
  have hT : 8.4 * CNc X0 * S2 ≤ 8.4 * 158 * (2493700 * (Real.exp (-117) * Real.exp (-83))) := by
    rw [← he200]
    apply mul_le_mul (by nlinarith) hS2 hS20 (by norm_num)
  have h117 : 8.4 * 158 * (2493700 * (Real.exp (-117) * Real.exp (-83))) ≤ Real.exp (-83) := by
    have : 8.4 * 158 * 2493700 * Real.exp (-117) ≤ 1 := by
      have : (8.4 : ℝ) * 158 * 2493700 * (1 / 10 ^ 40) ≤ 1 := by norm_num
      nlinarith [Real.exp_pos (-117)]
    nlinarith
  rw [he83]
  nlinarith

variable {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} {X₀ : ℕ} {y Z η1 η2 : ℝ}
  {ε1 : ℝ → ℝ} {εW θW : ℝ} {Tc : ℝ → ℝ}

/-- **The standing inputs at the window heights** (all owned by the Model agent, except
`htnp`, Queue6's `tnpHyp_R`). -/
structure WinGlob (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X₀ : ℕ) (y Z η1 η2 : ℝ)
    (ε1 : ℝ → ℝ) (εW θW : ℝ) (Tc : ℝ → ℝ) : Prop where
  htnp : Hyp P (Queue6.Hc X₀) tw X0m Z η1 η2 ε1 εW θW
  hO : KR.Ops.OpHyp P (Queue6.Hc X₀) X0m
  /-- `H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}` (`KR.WidthReal.Hc_Xm_half_le`) -/
  hHw : Queue6.Hc X₀ (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)
  hX0e : X0m = X₀ - Queue6.Hc X₀ X₀ / 2
  hX0m : X0m ≤ X₀
  hXmZ : X0m ≤ Z
  ht : ∀ r, r.Prime → 0 < tw r
  htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r
  /-- `3 θ ≤ 10⁻³` (so `λ₀ = 1 + 3θ ≤ 1.001`; `θ = ε/10`) -/
  hθ3 : 3 * θW ≤ 1 / 1000
  hTm : Measurable Tc
  hTb : ∀ t, t ≤ 1.2 * y → |Tc t| ≤ 2
  /-- the horizons at the heights read, `s ≤ y` (`KR.RML9.Ytop_le`) -/
  hZ0 : 2500 ≤ Z
  hZ : 2 * y / X0m ≤ Z
  hZ18 : 18 * y ≤ Z ^ 2
  /-- `capH` at `X₀` (`capH_ge_one`, `capH_le_rpow`) -/
  hH1 : 1 ≤ Queue6.Hc X₀ X₀
  hδ : Queue6.Hc X₀ X₀ / X₀ ≤ 1 / 1000
  hδs : 200000 * (Queue6.Hc X₀ X₀ / X₀) ≤ Real.exp (-61)

/-- The window facts at `s ∈ [y/4, y]`. -/
lemma win_facts (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc) (hy4 : 4 * (X₀ : ℝ) ≤ y)
    {s : ℝ} (hs1 : y / 4 ≤ s) (hs2 : s ≤ y) :
    X0m ≤ s ∧ (X₀ : ℝ) ≤ s ∧ 2 * s / X0m ≤ Z ∧ 18 * s ≤ Z ^ 2 ∧
      (∀ t, t ≤ 1.2 * s → |Tc t| ≤ 2) ∧ Real.log y - Real.log 4 ≤ Real.log s := by
  have hXm0 := G.htnp.width.X0m_pos
  have hX0p := (sizes G.htnp G.hX0e G.hX0m).2.2.2.2
  have hX0s : (X₀ : ℝ) ≤ s := by linarith
  have hy0 : 0 < y := by linarith
  refine ⟨G.hX0m.trans hX0s, hX0s, ?_, by linarith [G.hZ18], fun t ht => G.hTb t (by linarith),
    ?_⟩
  · refine le_trans ?_ G.hZ
    exact div_le_div_of_nonneg_right (by linarith) hXm0.le
  · have : Real.log (y / 4) ≤ Real.log s := Real.log_le_log (by positivity) hs1
    rwa [Real.log_div hy0.ne' (by norm_num)] at this

/-- The `BridgeAt` data at a window height `s`. -/
noncomputable def bridgeAt_win (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc)
    (hy4 : 4 * (X₀ : ℝ) ≤ y) {s : ℝ} (hs1 : y / 4 ≤ s) (hs2 : s ≤ y)
    (W : WinAt P tw X0m X₀ Tc s) :
    BridgeAt P (Queue6.Hc X₀) tw X0m X₀ θW (1 + 3 * θW) Tc 0 s
      ((5.1 * CNc X₀ + CSc) * ∑ u ∈ dyScales (X₀ : ℝ) s W.N, Real.log (2 * u) * W.o u +
        8.4 * CNc X₀ * ∑ v ∈ dyScales (X₀ : ℝ) s W.N,
          Real.log (2 * v) * sTheta P (Queue6.Hc X₀) X0m W.K v) 0 := by
  have hθ0 := G.htnp.width.theta_nonneg
  have hθ3 := G.hθ3
  have hf := win_facts G hy4 hs1 hs2
  exact BridgeAtL.toBridgeAt (Z := Z) (η1 := η1) (η2 := η2) (ε1 := ε1) (ε := εW)
    { N := W.N
      K := W.K
      hN2 := W.hN2
      hN := W.hN
      hK := W.hK
      s0 := W.s0
      o := W.o
      etaX0 := W.etaX0
      etaX0Sum := W.etaX0Sum
      osc := W.osc
      termOsc := W.termOsc
      sizeE := le_rfl
      sizeJ := by simp
      l520 := l520At_of_loc G.htnp G.hHw G.hX0e G.hX0m G.hZ0 hf.2.2.2.1 W.hK
        (by linarith) (by linarith) }
    G.htnp G.hX0e G.hX0m hf.2.1

/-- **Proposition 5.26 at the window heights**: `|BR_c(s)| ≤ e^{-76}/log y`. -/
theorem brs_of (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc) (hy4 : 4 * (X₀ : ℝ) ≤ y)
    (hly : 100000000 ≤ Real.log y) {s : ℝ} (hs1 : y / 4 ≤ s) (hs2 : s ≤ y)
    (W : WinAt P tw X0m X₀ Tc s) :
    |KR.BRc P (Queue6.Hc X₀) tw X0m s Tc| ≤ Real.exp (-76) / Real.log y := by
  have hθ0 := G.htnp.width.theta_nonneg
  have hθ3 := G.hθ3
  have hf := win_facts G hy4 hs1 hs2
  have hXm0 := G.htnp.width.X0m_pos
  have hΛ := (sizes G.htnp G.hX0e G.hX0m).2.1
  have hp2 := KR.Chain.p_ge_two_of G.htnp G.hXmZ
  set D := bridgeAt_win G hy4 hs1 hs2 W
  have hBR := KR.TcLoc.prop_5_26_loc G.htnp.hbs G.htnp.hXm G.htnp.width G.hO G.hX0e hp2 G.ht
    G.htv (lam0 := 1 + 3 * θW) (by linarith) (by linarith) hf.1 hf.2.2.1 (by linarith)
    G.hX0m hf.2.1 D.cov D.covL D.sc1 D.sc D.eta D.etaSmall D.etaX0 D.theta G.hTm hf.2.2.2.2.1
    D.osc D.X0mem D.termOsc
  have hsz := sizeE_le9 G.htnp G.hHw hΛ G.hX0e G.hX0m G.hZ0 hf.2.2.2.1 W.hK W.hosc
  have hls : 0 < Real.log s := by linarith [hf.2.2.2.2.2, log4_lt]
  have h1 : Real.log s * |KR.BRc P (Queue6.Hc X₀) tw X0m s Tc| ≤ 0.9 * Real.exp (-76) :=
    hBR.trans hsz
  have hly0 : 0 < Real.log y := by linarith
  have hratio : 0.9 * Real.log y ≤ Real.log s := by linarith [hf.2.2.2.2.2, log4_lt]
  rw [le_div_iff₀ hly0]
  have hB0 := abs_nonneg (KR.BRc P (Queue6.Hc X₀) tw X0m s Tc)
  have he := Real.exp_pos (-76)
  nlinarith

/-- `𝔅_y`, the bound of `xbs_of`. -/
noncomputable def BxY (X₀ : ℕ) (y : ℝ) : ℝ :=
  (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Real.log X₀ /
      (Real.log y - Real.log 4 - Real.log X₀) +
    Real.exp (-178) / (Real.log y - Real.log 4)

/-- **Lemma 5.27 at the window heights** in the huge range:
`|R_res 1 - ρ^sh 1|(s) ≤ 𝔅_y`. -/
theorem xbs_of (G : WinGlob P tw X0m X₀ y Z η1 η2 ε1 εW θW Tc) (hy4 : 4 * (X₀ : ℝ) ≤ y)
    (hy : Real.exp (Real.log X₀ / 100) < Real.log y) {s : ℝ} (hs1 : y / 4 ≤ s)
    (hs2 : s ≤ y) (W : WinAt P tw X0m X₀ Tc s) :
    |KR.Rres P (Queue6.Hc X₀) tw X0m s (KR.Chain.ind X₀) -
      KR.rhoSh P tw X0m s (KR.Chain.ind X₀)| ≤ BxY X₀ y := by
  have hθ0 := G.htnp.width.theta_nonneg
  have hθ3 := G.hθ3
  have hf := win_facts G hy4 hs1 hs2
  have hXm0 := G.htnp.width.X0m_pos
  have hsz := sizes G.htnp G.hX0e G.hX0m
  have hΛ := hsz.2.1
  have hX0p : (0 : ℝ) < X₀ := hsz.2.2.2.2
  have hp2 := KR.Chain.p_ge_two_of G.htnp G.hXmZ
  set D := bridgeAt_win G hy4 hs1 hs2 W
  have hXB := lemma_5_27 G.htnp.hbs G.htnp.hXm G.htnp.width G.hX0e hp2 G.ht G.htv
    (lam0 := 1 + 3 * θW) le_rfl (by linarith) hf.1 hf.2.2.1 (by linarith) G.hX0m D.cov D.sc1
    D.sc D.eta D.etaSmall D.etaX0.1 D.etaX0Sum D.theta
  -- the huge range at `s`
  set Λ := Real.log X₀
  have hhe := huge_exp hΛ
  have hl4 := log4_lt
  have hl40 := log4_pos
  have hs0 : 0 < s := by linarith
  have hlsX : Real.log (s / X₀) = Real.log s - Λ := Real.log_div hs0.ne' hX0p.ne'
  have hJs : 600 * Λ ^ 4 ≤ Real.log (s / X₀) := by
    rw [hlsX]; linarith [hf.2.2.2.2.2]
  have hxb := KR.RML9.xbB_huge G.htnp.hbs G.htnp.width (lam0 := 1 + 3 * θW) G.hX0e G.hH1 G.hδ
    hp2 G.htnp.hXm G.ht G.htv (by linarith) (by linarith) hf.1 hJs hf.2.2.1 W.hT W.hSR
  have hcne := KR.RML9.cne_le G.htnp G.hHw hΛ (N := W.N) G.hZ0 hf.2.2.2.1
    (fun v hv => sqrt_le_Pk W.hK (dyScales_le hv))
  -- combine
  have hJ1 : Real.log y - Real.log 4 - Λ ≤ Real.log (s / X₀) := by
    rw [hlsX]; linarith [hf.2.2.2.2.2]
  have hΛ4 := pow_nonneg (by linarith : (0 : ℝ) ≤ Λ) 4
  have hJ0 : 0 < Real.log y - Real.log 4 - Λ := by linarith
  have hB0 : 0 ≤ (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Λ := by
    have : 0 ≤ Queue6.Hc X₀ X₀ / X₀ := div_nonneg (by linarith [G.hH1]) hX0p.le
    have := Real.exp_pos (-61)
    have : 0 ≤ Λ := by linarith
    positivity
  have t1 : (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Λ / Real.log (s / X₀) ≤
      (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Λ /
        (Real.log y - Real.log 4 - Λ) := div_le_div_of_nonneg_left hB0 hJ0 hJ1
  have hxb' : xbB P (Queue6.Hc X₀) tw X0m s (X₀ : ℝ) θW (1 + 3 * θW) ≤
      (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Λ /
        (Real.log y - Real.log 4 - Λ) := hxb.trans t1
  have hls : Real.log y - Real.log 4 ≤ Real.log s := hf.2.2.2.2.2
  have hls0 : 0 < Real.log y - Real.log 4 := by linarith
  have hSc : D.Sc = dyScales (X₀ : ℝ) s W.N := rfl
  have hth : D.th = sTheta P (Queue6.Hc X₀) X0m W.K := rfl
  rw [hSc, hth] at hXB
  set E := ∑ v ∈ dyScales (X₀ : ℝ) s W.N, Real.log (2 * v) * sTheta P (Queue6.Hc X₀) X0m W.K v
  have t2 : 4.3 * CNc (X₀ : ℝ) * E / Real.log s ≤ Real.exp (-178) / (Real.log y - Real.log 4) :=
    div_le_div₀ (Real.exp_pos _).le hcne hls0 hls
  unfold BxY
  have e : 4.3 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X₀)) * E /
      Real.log s = 4.3 * CNc (X₀ : ℝ) * E / Real.log s := rfl
  rw [e] at hXB
  linarith

/-- **Proposition 5.31(iii) in the form of `G1ResSec5`**: `𝔅_y ≤ (400 δ_x + e^{-60}) τ₀/J`
with `δ_x = e^{-60}/800`, `τ₀ = 1.0001 Λ`, `J = log y - Λ`. -/
theorem hBx_of {X₀ : ℕ} {y : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hX0 : (0 : ℝ) < X₀)
    (hy : Real.exp (Real.log X₀ / 100) < Real.log y) (hH0 : 0 ≤ Queue6.Hc X₀ X₀)
    (hδs : 200000 * (Queue6.Hc X₀ X₀ / X₀) ≤ Real.exp (-61)) :
    BxY X₀ y ≤ (400 * (Real.exp (-60) / 800) + Real.exp (-60)) * (1.0001 * Real.log X₀) /
      (Real.log y - Real.log X₀) := by
  set Λ := Real.log X₀
  set L := Real.log y
  have hhe := huge_exp hΛ
  have hl4 := log4_lt
  have hl40 := log4_pos
  have hJ : 600 * Λ ^ 4 + 2 ≤ L - Λ := by linarith
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJ0 : 0 < L - Real.log 4 - Λ := by nlinarith
  have hJp : 0 < L - Λ := by linarith
  have he61 : Real.exp (-61) ≤ 0.3679 * Real.exp (-60) := by
    have e : Real.exp (-61) = Real.exp (-1) * Real.exp (-60) := by
      rw [← Real.exp_add]; norm_num
    rw [e]
    have : Real.exp (-1) ≤ 0.3679 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hB : 200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61) ≤ 0.7358 * Real.exp (-60) := by
    linarith
  have he178 : Real.exp (-178) ≤ Real.exp (-60) := Real.exp_le_exp.mpr (by norm_num)
  have h60 := Real.exp_pos (-60)
  -- the ratio `(L - Λ)/(L - log 4 - Λ) ≤ 1.0001`
  have hr : 1 / (L - Real.log 4 - Λ) ≤ 1.0001 / (L - Λ) := by
    rw [div_le_div_iff₀ hJ0 hJp]; nlinarith
  have hr2 : 1 / (L - Real.log 4) ≤ 1.0001 / (L - Λ) := by
    rw [div_le_div_iff₀ (by linarith) hJp]; nlinarith
  unfold BxY
  have hΛ0 : 0 ≤ Λ := by linarith
  have hB0 : 0 ≤ 200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61) := by
    have : 0 ≤ Queue6.Hc X₀ X₀ / X₀ := div_nonneg hH0 hX0.le
    have := Real.exp_pos (-61); positivity
  have a1 : (200000 * (Queue6.Hc X₀ X₀ / X₀) + Real.exp (-61)) * Λ / (L - Real.log 4 - Λ) ≤
      0.7358 * Real.exp (-60) * Λ * (1.0001 / (L - Λ)) := by
    rw [div_eq_mul_one_div]
    apply mul_le_mul (mul_le_mul_of_nonneg_right hB hΛ0) hr (by positivity) (by positivity)
  have a2 : Real.exp (-178) / (L - Real.log 4) ≤ Real.exp (-60) * Λ * (1.0001 / (L - Λ)) /
      1000000 := by
    rw [div_eq_mul_one_div]
    have : Real.exp (-178) ≤ Real.exp (-60) * Λ / 1000000 := by
      have : Real.exp (-60) * 1 ≤ Real.exp (-60) * (Λ / 1000000) :=
        mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ (by norm_num)]; linarith) h60.le
      linarith
    calc Real.exp (-178) * (1 / (L - Real.log 4))
        ≤ (Real.exp (-60) * Λ / 1000000) * (1.0001 / (L - Λ)) :=
          mul_le_mul this hr2 (one_div_nonneg.mpr (by linarith)) (by
            have : 0 ≤ Real.exp (-60) * Λ := mul_nonneg h60.le hΛ0
            positivity)
      _ = _ := by ring
  have e : (400 * (Real.exp (-60) / 800) + Real.exp (-60)) * (1.0001 * Λ) / (L - Λ) =
      1.5 * (Real.exp (-60) * Λ * (1.0001 / (L - Λ))) := by ring
  rw [e]
  have hX : 0 ≤ Real.exp (-60) * Λ * (1.0001 / (L - Λ)) := by positivity
  linarith

end KR.RML10

end
