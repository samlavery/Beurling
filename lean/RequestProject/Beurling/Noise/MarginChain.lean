module

public import RequestProject.Beurling.Noise.MarginChainLin

/-!
# The chain Bridge → Theorem 5.37 → Proposition 5.38 → Corollary 5.40, for the realised system

The effective source is `T' = T_c + j₀ 1_{[X₀,∞)}` (§5.1, "The jump at `X₀`"), the long operator is
`R_res = KR.Rres` (the true kernels of §5.9.4) and the sharp reference is `ρ^sh = KR.rhoSh`
(Lemma 5.5). The inputs are collected in `ChainInputs`:

* the standing hypotheses: (HBS), `log X₀⁻, log X₀ ≥ 10⁸`, `PaperWidth`, `X₀⁻ = X₀ - H(X₀)/2`,
  prime values `≥ 2`, the decision order (`t > 0`, `p ≤ 2t(p)`), `1 + 3θ ≤ λ₀ ≤ 1.001`,
  `|T_c| ≤ 2`, `j₀ ≥ 0`, (huxley), Lemma 7.3's inputs and the supports of `μ₀, μ₁`;
* at every start `y` of a window (`BridgeAt`): the inputs of **Proposition 5.26**
  (`prop_5_26_hbs`) and **Lemma 5.27** (`lemma_5_27`) — the scale family, Lemma 5.20's
  `EtaBound`/`ThetaBlk`, step (iii)'s `EtaX0Sum`, the oscillation `OscBound`, `TermOsc` — and
  the size relations `E ≤ E_BR(x)`, `j₀ b log y ≤ j(x)` (eq. (jX0));
* at every start `y` (`G1At`): the residual inputs of **Proposition 5.35** (eq. (86) in range
  (A), Steps 1–4 in range (B));
* **Lemma 5.34**: the operators `B, K_pt, R` with the push-through facts, the margin identity
  (Proposition 5.11 with (Ttilde)), `B` = window average, `R T' = R_res T'`, and the bullet
  bounds `a(x)`, `b(x)`, `|ϑ| ≤ 6`;
* **Proposition 5.38**: the margin density `m` with its residual inputs (the variation bound of
  Steps 1–5, the Step 6(a) decomposition, the Step 6(b) "Sum", Proposition 5.33's `j ≤ 0.4209`,
  the Step 6(c) source bounds) and the sizes of the error terms;
* the window integrability of `R_res T'`, `ρ^sh T'` and `m`.

Main results:

* `ChainInputs.thm_5_37` : **Theorem 5.37** at `x ≥ X₀^{1.01}`;
* `ChainInputs.prop_5_38` : **Proposition 5.38** (a)–(c), i.e. `PointwiseMargin m X₀`;
* `ChainInputs.cor_5_40`, `cor_5_40_queue` : **Corollary 5.40** on every window with the
  bookkeeping identity of §5.3.
-/

@[expose] public section

open Real MeasureTheory Set BeurlingSystem

namespace KR.Chain

/-- `C_N = C_S (2.04 + 4.71/log X₀)` (Corollary 5.17(b)). -/
noncomputable abbrev CNc (X0 : ℝ) : ℝ :=
  max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)

/-- `C_S = max(2.01 C_BS, 1.4)` (Corollary 5.9). -/
noncomputable abbrev CSc : ℝ := max (2.01 * BSaias.PhiInf 100000000) 1.4

/-- **The bridge data at a start `y`**: the inputs of Proposition 5.26 and Lemma 5.27 at `y`
and the size relations to `E_BR` and `j` (of the window containing `y`). -/
structure BridgeAt (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 : ℝ)
    (Tc : ℝ → ℝ) (j0 y EBR j : ℝ) where
  Sc : Finset ℝ
  s : ℝ → ℝ
  s0 : ℝ → ℝ
  th : ℝ → ℝ
  o : ℝ → ℝ
  /-- the scales cover the levels (Proposition 5.18, step (ii)) -/
  cov : ∀ d ∈ NAll P y X0m, ∃ v ∈ Sc, d ∈ NW P y v
  covL : ∀ n ∈ levels P X0m y, ∃ u ∈ Sc, n ∈ NW P y u
  sc1 : ∀ u ∈ Sc, 1 / 2 ≤ u
  sc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u
  /-- **Lemma 5.20**: `E_η` -/
  eta : EtaBound P H tw X0m Sc s
  etaSmall : lam0 * CNc X0 * ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2
  /-- **Proposition 5.18, step (iii)** -/
  etaX0 : EtaX0Sum P H X0m X0 Sc s0
  etaX0Sum : ∑ v ∈ Sc, s0 v ≤ 1.52
  /-- **Lemma 5.20**: `E_θ` -/
  theta : ThetaBlk P H tw X0m Sc th
  /-- the oscillation of `T_c` (eq. (osc)) -/
  osc : OscBound P H y Tc Sc o
  X0mem : X0 ∈ Sc
  /-- the terminal oscillation (proof of Proposition 5.26, second bullet) -/
  termOsc : TermOsc P H tw X0m y Tc (o X0)
  /-- `E_BR` bounds the right side of Proposition 5.26 -/
  sizeE : (5.1 * CNc X0 + CSc) * ∑ u ∈ Sc, Real.log (2 * u) * o u +
      8.4 * CNc X0 * ∑ v ∈ Sc, Real.log (2 * v) * th v ≤ EBR
  /-- eq. (jX0): `j` bounds `j₀ log y` times the bound of Lemma 5.27 -/
  sizeJ : j0 * (xbB P H tw X0m y X0 θ lam0 +
      4.3 * CNc X0 * (∑ v ∈ Sc, Real.log (2 * v) * th v) / Real.log y) * Real.log y ≤ j

/-- **The residual inputs of Proposition 5.35 at a start `y`**: eq. (86) and the `σ_𝒜`
response in range (A), the conclusions of Steps 1–4 in range (B). -/
def G1At (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (μ0 μ1 ρedge Tp : ℝ → ℝ)
    (y : ℝ) : Prop :=
  ∃ rA : ℝ,
    (Real.log y ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) →
      rhoSh P tw X0m y Tp = BaseRange.MAP X0 (Construction.kappaParam X0) y + ρedge y +
        rhoSh P tw X0m y μ0 + rhoSh P tw X0m y μ1 + rA) ∧
    (Real.log y ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) → |rA * Real.log y| ≤ Real.exp (-80)) ∧
    ((X0 : ℝ) ^ (1 / 100 : ℝ) < Real.log y →
      ∃ avgR avgS εN EBR j o1 o2 o3 : ℝ,
        LocalPNT.pi0Dens y - o1 / Real.log y ≤ avgR ∧
        avgR - (εN + EBR + j + o2) / Real.log y ≤ avgS ∧
        avgS - o3 / Real.log y ≤ rhoSh P tw X0m y Tp ∧ εN ≤ 1 / 10 ^ 13 ∧
        EBR ≤ Real.exp (-76) ∧ j ≤ Real.exp (-59) ∧ o1 + o2 + o3 ≤ 1 / 10 ^ 24)

/-- The window `W_x = [x - H/2, x + H/2]`. -/
def InW (Hx x y : ℝ) : Prop := x - Hx / 2 ≤ y ∧ y ≤ x + Hx / 2

/-- The total `o(1)` at `x` in Theorem 5.37: the averaging loss of (g1) and the passage
from `log y` to `log x` in (bridge). -/
noncomputable def oTot (Hx x EBR j : ℝ) : ℝ :=
  0.97 * (1 - Real.log x / Real.log (x + Hx / 2)) +
    (Real.log x / Real.log (x - Hx / 2) - 1) * (EBR + j)

/-- **All inputs of the chain** (see the module docstring); `X₁ = X₀^{1.01}`. -/
structure ChainInputs (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ)
    (Z η1 η2 : ℝ) (ε1 : ℝ → ℝ) (ε θ lam0 : ℝ) (Tc : ℝ → ℝ) (j0 xmax : ℝ)
    (μ0 μ1 ρedge m : ℝ → ℝ) where
  -- standing hypotheses
  hbs : P.HBS X0m Z η1 η2 ε1
  hXm : 100000000 ≤ Real.log X0m
  hX : 10 ^ 8 ≤ Real.log X0
  hP : PaperWidth H X0m ε θ
  hX0e : X0m = X0 - H X0 / 2
  hp2 : ∀ j, 2 ≤ P.p j
  ht : ∀ r, r.Prime → 0 < tw r
  htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r
  hlam : 1 + 3 * θ ≤ lam0
  hlam1 : lam0 ≤ 1.001
  hTm : Measurable Tc
  hTb : ∀ t, |Tc t| ≤ 2
  hj0 : 0 ≤ j0
  /-- (huxley) and Lemma 7.3's inputs (§7) -/
  hHux : BaseRange.HuxleyFrom X0
  hin : BaseRange.Lemma73Inputs X0 xmax μ0 μ1 ρedge
  hμ0 : ∀ u : ℝ, u < X0 → μ0 u = 0
  hμ1 : ∀ u : ℝ, u < X0 → μ1 u = 0
  /-- the heights read: `y ≤ xmax` and `2y/X₀⁻ ≤ Z` on the windows used -/
  hxmax : ∀ y, (X0 : ℝ) ≤ y → y ≤ xmax
  hZ : ∀ y, (X0 : ℝ) ≤ y → 2 * y / X0m ≤ Z
  -- the window quantities, as functions of the centre `x`
  EBR : ℝ → ℝ
  jX : ℝ → ℝ
  EBR_nonneg : ∀ x, 0 ≤ EBR x
  jX_nonneg : ∀ x, 0 ≤ jX x
  /-- **Propositions 5.26 and Lemma 5.27** at every start of the windows of `x ≥ X₀^{1.01}/2` -/
  bridge : ∀ x y, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → InW (H x) x y →
    BridgeAt P H tw X0m X0 θ lam0 Tc j0 y (EBR x) (jX x)
  /-- **Proposition 5.35**, residual inputs, at every start `y ≥ X₀` -/
  g1 : ∀ y, (X0 : ℝ) ≤ y → G1At P tw X0m X0 μ0 μ1 ρedge (fun t => Tc t + j0 * ind X0 t) y
  -- **Lemma 5.34**
  B : (ℝ → ℝ) →+ (ℝ → ℝ)
  K : (ℝ → ℝ) →+ (ℝ → ℝ)
  R : (ℝ → ℝ) →+ (ℝ → ℝ)
  /-- `R_res` inverts `1 + K_pt B` (§5.3) -/
  hR : ∀ g, R g + K (B (R g)) = g
  /-- the push-through form determines `ρ̃` (§5.3) -/
  hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f'
  ρ : ℝ → ℝ
  ν : ℝ → ℝ
  NT : ℝ → ℝ
  ϑ : ℝ → ℝ
  /-- the margin identity (Proposition 5.11 with (Ttilde)) -/
  hmargin : ρ + B (K ρ) = B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT
  /-- `B` is the window average -/
  hBx : ∀ g x, B g x = Margin.Bavg (H x) g x
  /-- `R` is the long operator on `T'` -/
  hRres : R (Tc + fun t => j0 * ind X0 t) =
    fun y => Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t)
  a : ℝ → ℝ
  b : ℝ → ℝ
  /-- Lemma 5.34, first bullet (from Proposition 5.18) -/
  hK : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → Real.log x *
    |B (K (B (R ((B Tc - Tc) + (fun z => ϑ z / H z) - ν - NT)))) x| ≤ a x
  /-- Lemma 5.34, second bullet (from Lemma 5.21(iii)) -/
  hG : ∀ x, (X0 : ℝ) ^ (1.01 : ℝ) ≤ x → Real.log x *
    |B (R (K ((B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t)) -
      B (B (Tc + fun t => j0 * ind X0 t) + (fun z => ϑ z / H z) - ν - NT -
        B (fun t => j0 * ind X0 t))))) x| ≤ b x
  /-- `|ϑ| ≤ 6` (eq. (Ttilde)) -/
  hϑ : ∀ x, |ϑ x| ≤ 6
  /-- window integrability of `R_res T'` and `ρ^sh T'` -/
  intRT : ∀ x, IntervalIntegrable (fun y => Rres P H tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  intRS : ∀ x, IntervalIntegrable (fun y => rhoSh P tw X0m y (fun t => Tc t + j0 * ind X0 t))
    volume (x - H x / 2) (x + H x / 2)
  -- **Proposition 5.38(a)**
  vt : ℝ → ℝ
  Bt : ℝ → ℝ
  η : ℝ → ℝ
  sη : ℝ
  ES : ℝ → ℝ
  V : ℝ → ℝ
  intm : ∀ t, IntervalIntegrable m volume (t - H t / 2) (t + H t / 2)
  /-- the window variation of `m` (Step 6(a)) -/
  hvar : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → ∀ y, InW (H t) t y → |m y - m t| ≤ vt t
  /-- **Steps 1–5** of the proof of Proposition 5.38: `v(t) log t ≤ 6.5 E_S + V_{X₀}(t)` -/
  hv : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → vt t * Real.log t ≤ 6.5 * ES t + V t
  /-- Step 6(a): `M = Bm + B NT_pt + ϑ/H` with `|B NT_pt + ϑ/H| ≤ 54η + 6/H` -/
  hdec : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → ρ t + ν t + NT t = Margin.Bavg (H t) m t + Bt t
  hBt : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → |Bt t| ≤ 54 * η t + 6 / H t
  hsη : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t → Real.log t * η t ≤ sη
  /-- the sizes of the error terms (`o(1)`, §5.1; Step 5 of Proposition 5.35) -/
  hsmall : ∀ t, (X0 : ℝ) ^ (1.01 : ℝ) ≤ t →
    oTot (H t) t (EBR t) (jX t) + (a t + b t + 6 * Real.log t / H t) + EBR t + jX t +
      54 * sη + 6 * Real.log t / H t + 6.5 * ES t + V t ≤ 0.01
  -- **Proposition 5.38(b)**
  jb : ℝ → ℝ
  /-- Step 6(b), "Sum": `m log t ≥ ρ^sh log t - j_{X₀} - 10⁻¹²` -/
  hsum : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) →
    rhoSh P tw X0m t (fun s => Tc s + j0 * ind X0 s) * Real.log t - jb t - 1 / 10 ^ 12 ≤
      m t * Real.log t
  /-- **Proposition 5.33**: `j_{X₀} ≤ 0.4209` -/
  hjb : ∀ t, 2 * (X0 : ℝ) ≤ t → t ≤ (X0 : ℝ) ^ (1.01 : ℝ) → jb t ≤ 0.4209
  -- **Proposition 5.38(c)** (Step 6(c)): the source bounds on `[X₀, 2X₀)`
  hc : ∀ t, (X0 : ℝ) ≤ t → t < 2 * X0 →
    (∃ Tp, m t = Tp ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp) ∨
    (∃ Tp rt, m t = Tp - rt / 2 ∧ (0.99 - 1 / 10 ^ 9) / Real.log t ≤ Tp ∧
      rt ≤ 0.5001 / Real.log X0 ∧ Real.log t ≤ Real.log X0 + 0.7)
  /-- `m = 0` below `X₀` -/
  hz : ∀ t : ℝ, t < X0 → m t = 0

namespace ChainInputs

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ} {X0 : ℕ}
  {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} {ε θ lam0 : ℝ} {Tc : ℝ → ℝ} {j0 xmax : ℝ}
  {μ0 μ1 ρedge m : ℝ → ℝ}

/-- The effective source `T'`. -/
noncomputable abbrev Tp (j0 : ℝ) (X0 : ℕ) (Tc : ℝ → ℝ) : ℝ → ℝ := fun t => Tc t + j0 * ind X0 t

lemma X0_gt (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    (1 : ℝ) < X0 := BaseRange.one_lt_of_log I.hX

lemma X1_ge (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) :=
  Real.self_le_rpow_of_one_le I.X0_gt.le (by norm_num)

lemma X0m_le (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    X0m ≤ X0 := by
  have := I.hP.reg
  have hX1 := I.X0_gt
  have hH : 0 ≤ H X0 := (I.hP.reg.pos _).le
  rw [I.hX0e]; linarith

/-- The window at `x ≥ X₀^{1.01}` lies in `[X₀^{1.01}/2, ∞) ∩ [X₀, ∞)`, and `x - H/2 > 1`. -/
lemma window_bounds (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {x : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) :
    0 < H x ∧ (X0 : ℝ) ^ (1.01 : ℝ) / 2 ≤ x - H x / 2 ∧ (X0 : ℝ) ≤ x - H x / 2 ∧
      1 < x - H x / 2 := by
  have hX1 := I.X0_gt
  have hX1' := I.X1_ge
  have hXm0 := I.hP.X0m_pos
  have hXmle := I.X0m_le
  have hHs : H x ≤ x / 10 := I.hP.small x (by linarith)
  have hH0 : 0 < H x := I.hP.reg.pos x
  -- `X₀ ≤ 0.95 X₀^{1.01}`
  have hlog : Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) = 1.01 * Real.log X0 :=
    Real.log_rpow (by linarith) _
  have hbig : 2 * (X0 : ℝ) ≤ (X0 : ℝ) ^ (1.01 : ℝ) := by
    have hX0p : (0 : ℝ) < X0 := by linarith
    have h2 : Real.log (2 * (X0 : ℝ)) ≤ Real.log ((X0 : ℝ) ^ (1.01 : ℝ)) := by
      rw [hlog, Real.log_mul (by norm_num) hX0p.ne']
      have := Real.log_two_lt_d9
      have := I.hX
      norm_num at this ⊢; nlinarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h2
  refine ⟨hH0, by linarith, by linarith, by linarith⟩

/-- **Theorem 5.37 (the margin on `H`-windows)** at `x ≥ X₀^{1.01}`, for the realised system:
`log x · M(x) ≥ 0.97 - o(x) - ε_N(x) - E_BR(x) - j(x)`, with `M = ρ̃ + ν + NT`,
`ε_N = a + b + 6 log x/H(x)` (Lemma 5.34) and `o = oTot`. -/
theorem thm_5_37 (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {x : ℝ} (hx : (X0 : ℝ) ^ (1.01 : ℝ) ≤ x) :
    0.97 - oTot (H x) x (I.EBR x) (I.jX x) - (I.a x + I.b x + 6 * Real.log x / H x) -
        I.EBR x - I.jX x ≤ Real.log x * (I.ρ x + I.ν x + I.NT x) := by
  obtain ⟨hH0, hw1, hw2, hw3⟩ := I.window_bounds hx
  have hX1 := I.X0_gt
  have hXmle := I.X0m_le
  have hlam2 : 1 + 2 * θ ≤ lam0 := by linarith [I.hP.theta_nonneg, I.hlam]
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- (predictable)
  have hpred := hpred_of I.B I.K I.R I.hR I.hinj I.ρ I.ν I.NT I.ϑ Tc
    (fun t => j0 * ind X0 t) H I.hmargin hlx0 hH0 (fun g => I.hBx g x) (I.hK x hx) (I.hG x hx)
    (I.hϑ x)
  rw [I.hRres] at hpred
  -- (bridge)
  have hbr : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      rhoSh P tw X0m y (Tp j0 X0 Tc) - (I.EBR x + I.jX x) / Real.log y ≤
        Rres P H tw X0m y (Tp j0 X0 Tc) := by
    intro y hy1 hy2
    have D := I.bridge x y hx ⟨hy1, hy2⟩
    have hy : (X0 : ℝ) ≤ y := by linarith
    have hly : 0 < Real.log y := Real.log_pos (by linarith)
    have hBR := prop_5_26_hbs I.hbs I.hXm I.hP I.hX0e I.hp2 I.ht I.htv hlam2 I.hlam1
      (hXmle.trans hy) (I.hZ y hy) (Real.log_pos hX1) hXmle D.cov D.covL D.sc1 D.sc D.eta
      D.etaSmall D.etaX0 D.theta I.hTm I.hTb D.osc D.X0mem D.termOsc
    have hXB := lemma_5_27 I.hbs I.hXm I.hP I.hX0e I.hp2 I.ht I.htv I.hlam I.hlam1
      (hXmle.trans hy) (I.hZ y hy) (Real.log_pos hX1) hXmle D.cov D.sc1 D.sc D.eta D.etaSmall
      D.etaX0.1 D.etaX0Sum D.theta
    exact hbr_of I.hP.reg hly I.hTm I.hTb I.hj0 hBR hXB D.sizeE D.sizeJ
  -- (g1)
  have hg1pt : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      0.97 ≤ rhoSh P tw X0m y (Tp j0 X0 Tc) * Real.log y := by
    intro y hy1 hy2
    have hy : (X0 : ℝ) ≤ y := by linarith
    obtain ⟨rA, hd, hA, hB⟩ := I.g1 y hy
    have := (KR.G1.prop_5_35 I.hbs I.hXm I.hX I.hHux I.hin I.ht I.htv hXmle hy (I.hxmax y hy)
      (I.hZ y hy) I.hμ0 I.hμ1 hd hA hB).2 (by linarith)
    exact this
  have hg1 := avg_ge hH0 hw3 (by norm_num) (I.intRS x) hg1pt
  have hg1' : 0.97 - 0.97 * (1 - Real.log x / Real.log (x + H x / 2)) ≤
      Real.log x * Margin.Bavg (H x) (fun y => rhoSh P tw X0m y (Tp j0 X0 Tc)) x := by
    linarith
  have hδ : Real.log x / Real.log (x - H x / 2) ≤
      1 + (Real.log x / Real.log (x - H x / 2) - 1) := by linarith
  have h537 := Margin.thm_5_37' hH0 hw3 (by linarith [I.EBR_nonneg x, I.jX_nonneg x])
    (I.intRT x) (I.intRS x) hpred hbr hg1' hδ
  unfold oTot
  linarith

/-- **Proposition 5.38 (the pointwise margin)**, (a)–(c), for the realised system:
`m(t) log t ≥ 0.399` for `t ≥ X₀` (and `≥ 0.96` above `X₀^{1.01}`), `m = 0` below `X₀`. -/
theorem prop_5_38 (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m) :
    Margin.PointwiseMargin m X0 := by
  have hX1 := I.X0_gt
  have hXmle := I.X0m_le
  refine Margin.pointwiseMargin_of (X1 := (X0 : ℝ) ^ (1.01 : ℝ)) ?_ ?_ ?_ I.hz
  · -- (a)
    intro t ht
    obtain ⟨hH0, -, -, hw3⟩ := I.window_bounds ht
    have h37 := I.thm_5_37 ht
    exact Margin.Var.prop_5_38_a_of hH0 (by linarith) (I.intm t)
      (fun y hy1 hy2 => I.hvar t ht y ⟨hy1, hy2⟩) (I.hv t ht) (I.hdec t ht) (I.hBt t ht)
      (I.hsη t ht) (by linarith) (I.hsmall t ht)
  · -- (b)
    intro t ht1 ht2
    have hy : (X0 : ℝ) ≤ t := by linarith
    obtain ⟨rA, hd, hA, hB⟩ := I.g1 t hy
    have h35 := (KR.G1.prop_5_35 I.hbs I.hXm I.hX I.hHux I.hin I.ht I.htv hXmle hy
      (I.hxmax t hy) (I.hZ t hy) I.hμ0 I.hμ1 hd hA hB).1 ht2
    exact Margin.prop_5_38_b (I.hsum t ht1 ht2) h35 (I.hjb t ht1 ht2)
  · -- (c)
    intro t ht1 ht2
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    rcases I.hc t ht1 ht2 with ⟨Tq, hm, hT⟩ | ⟨Tq, rt, hm, hT, hr, hl⟩
    · exact Margin.Var.prop_5_38_c_low hlt hm hT
    · have hΛ : (100000000 : ℝ) ≤ Real.log X0 := by have := I.hX; norm_num at this ⊢; linarith
      have := Margin.Var.prop_5_38_c_high hlt hΛ hm hT hr hl
      linarith

/-- **Corollary 5.40 (R1′ on every window)** for the realised system: for a window `[a, b)`
with the bookkeeping identity of §5.3 and `L ≥ log t` on `[a, b) ∩ [X₀, ∞)`,
`ℓ_jit(I) - Comp(I) ≥ 0.399 |I ∩ [X₀, ∞)|/L - 2`. -/
theorem cor_5_40 (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, (X0 : ℝ) ≤ t → t ≤ b → Real.log t ≤ L) (hL0 : 0 < L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2) :
    0.399 * max (b - max a (X0 : ℝ)) 0 / L - 2 ≤ ell - comp :=
  Margin.cor_5_40 I.prop_5_38 I.X0_gt hab hm hL hL0 hbook

/-- **Corollary 5.40 in the form used in Theorem 6.6**: `Comp(I) ≤ ℓ_jit(I)(1 - 0.15/L) + 3`. -/
theorem cor_5_40_queue
    (I : ChainInputs P H tw X0m X0 Z η1 η2 ε1 ε θ lam0 Tc j0 xmax μ0 μ1 ρedge m)
    {a b L ell comp : ℝ} (hab : a ≤ b) (hm : IntervalIntegrable m volume a b)
    (hL : ∀ t, (X0 : ℝ) ≤ t → t ≤ b → Real.log t ≤ L) (hL1 : 1 ≤ L)
    (hbook : |ell - comp - ∫ t in a..b, m t| ≤ 2)
    (hell : ell ≤ 1.01 * max (b - max a (X0 : ℝ)) 0 + 1) :
    comp ≤ ell * (1 - 0.15 / L) + 3 :=
  Margin.cor_5_40_queue I.prop_5_38 I.X0_gt hab hm hL hL1 hbook hell

end ChainInputs

end KR.Chain

end
