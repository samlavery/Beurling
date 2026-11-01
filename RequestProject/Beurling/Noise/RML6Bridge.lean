module

public import RequestProject.Beurling.Noise.MarginRealLoc
public import RequestProject.Beurling.Noise.L520Loc
public import RequestProject.Beurling.Noise.RML6BridgeNum
public import RequestProject.Beurling.Noise.RML6BridgeOsc

/-!
# The bridge fields of `BModel.RealMarginLoc` (round 6)

The field `bridge` of `BModel.RealMarginLoc` asks, at every start `y ∈ W_x` (`X₁ ≤ x ≤ b`), for a
record `BModel.BridgeR … (TcR θ X₀ ω j₀) j₀ y (EBR x) (jX x)`. This file builds that record.

* `KR.Chain.l520_of_le` : the field `l520` (Lemma 5.20 at `y`) from `l520At_of_loc`, under
  `y ≤ Z` (then `2500 ≤ Z` and `18 y ≤ Z²`).
* `BModel.bridgeR_mk` : the record for a general system, with
  - `etaX0Sum` from `KR.X0S.sX0_sum_le` (step (iii), unweighted, `≤ 1.52`);
  - `osc` from `oscBound_oscR`, for the explicit oscillation `o = oscR H T_c`;
  - `termOsc` from `termOsc_oscR`, given `T_c = 0` on `(-∞, X₀]`;
  - `sizeE` from `sizeE_le` (`≤ e^{-76}`), given eq. (osc)'s first display;
  - `sizeJ` from the hypothesis `hj` (the definition of `j_{X₀}(x)` as a supremum, eq. (jX0));
  - `l520` from `l520_of_le`.
* `BModel.EBRc := e^{-76}` (the paper's `E_BR ≤ e^{-76}`) and
  `BModel.jXdef` (eq. (jX0): `sup_{y ∈ W_x}` of `log y · j₀ (𝔅(y) + 4.3 C_N E_θ/log y)`),
  with `le_jXdef` (each `y ∈ W_x` is below the supremum, given that the family is bounded,
  e.g. by Proposition 5.33).
* `BModel.bridgeR_real` : the record for the realised system `PR θ X₀ ω`, `H = Hc X₀`,
  `tw = twR θ X₀ ω`, `T_c = TcR θ X₀ ω j₀`.

Residual inputs (each a construction fact, owner in brackets):
* `TcLow` : `T_c = 0` on `(-∞, X₀]` (`T' = 0` below `X₀`, and `T_c` is continuous at `X₀`,
  `T_c(X₀) = T'(X₀⁺) - j₀ = 0`, §5.1) [Model: `TpCont`, `KAbsR`, `j₀ = jz`];
* `OscSum` : the first display of eq. (osc), `∑_u log(2u) o_u ≤ e^{-83}` at the dyadic scales of
  `y` [Model: the pieces `ρ_det`, `σ_𝒜`, `R` of `T_c`];
* `|T_c| ≤ 2` [Model, field `hTb`]; `y ≤ Z` (the start lies below the (HBS) horizon) [Model];
* the boundedness of the eq. (jX0) family over `W_x` (for `le_jXdef`) [this front, Prop 5.33].
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction KR KR.TNP

namespace KR.Chain

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **The field `l520`**: Lemma 5.20 at a start `y ≥ X₀`. (HBS) is read only up to `3√(2v)`
for the scales `v ≤ y`: the horizon conditions are `X₀⁻ ≤ Z` (so `2500 ≤ Z`) and
`18 y ≤ Z²`. -/
theorem l520_of_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 y lam0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hXmZ : X0m ≤ Z)
    (h18 : 18 * y ≤ Z ^ 2) {N K : ℕ}
    (hK : √(2 * y) ≤ Pk X0m K) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
    L520At P H tw X0m X0 lam0 y N K := by
  have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  have hZ0 : 2500 ≤ Z := by norm_num at hXm7; linarith
  exact l520At_of_loc h hH hX0e hX0m hZ0 h18 hK hlam0 hlam

/-- `18 y ≤ Z²` from `X₀⁻ ≤ Z` and the cofactor horizon `18 y/X₀⁻ ≤ Z`. -/
lemma sq18_of_cofactor {X0m Z y : ℝ} (hXm : 0 < X0m) (hXmZ : X0m ≤ Z)
    (hyZ : 18 * y / X0m ≤ Z) : 18 * y ≤ Z ^ 2 := by
  rw [div_le_iff₀ hXm] at hyZ
  nlinarith

/-- Every prime value is `≥ 2`, from (HBS) on `[1, Z]` with `X₀⁻ ≤ Z`. -/
lemma p_ge_two_of (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) (hZ : X0m ≤ Z) (j : ℕ) : 2 ≤ P.p j := by
  rcases le_or_gt (P.p j) Z with hj | hj
  · exact h.hbs.p_ge_two hj
  · have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
    norm_num at hXm7
    linarith

/-- The dyadic scales are positive. -/
lemma dyScales_pos {X0 y : ℝ} {N : ℕ} (hX : 0 < X0) {u : ℝ} (hu : u ∈ dyScales X0 y N) :
    0 < u := by
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
  positivity

/-- There are scale indices `N`, `K` for every start. -/
lemma exists_NK {X0 : ℝ} (hX : 0 < X0) (hXm : 0 < X0m) (y : ℝ) :
    ∃ N K : ℕ, 2 < N ∧ y < X0 * 2 ^ N / 4 ∧ √(2 * y) ≤ Pk X0m K := by
  obtain ⟨N, hN2, hN⟩ := exists_N hX y
  obtain ⟨K, hK⟩ := exists_K hXm (√(2 * y))
  exact ⟨N, K, hN2, hN, hK⟩

end KR.Chain

namespace BModel

open KR.Chain

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

lemma ten96_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : (10 : ℝ) ^ 96 ≤ X₀ := by
  have hX0p : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hX; linarith
  have h1 := Real.exp_one_gt_d9
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h10 : (10 : ℝ) ≤ Real.exp 3 := by
    rw [e3]
    have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
    have h3 : (10 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    linarith
  have e288 : Real.exp 288 = Real.exp 3 ^ 96 := by rw [← Real.exp_nat_mul]; norm_num
  have h96 : (10 : ℝ) ^ 96 ≤ Real.exp 288 := by
    rw [e288]; exact pow_le_pow_left₀ (by norm_num) h10 96
  calc (10 : ℝ) ^ 96 ≤ Real.exp 288 := h96
    _ ≤ Real.exp (Real.log X₀) := Real.exp_le_exp.mpr (by linarith)
    _ = X₀ := Real.exp_log hX0p

/-- `E_BR := e^{-76}` (eq. (osc), last item). -/
noncomputable def EBRc : ℝ := Real.exp (-76)

/-- The quantity of eq. (jX0) at a start `y` (for the scale index `K`). -/
noncomputable def jXat (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 j0 : ℝ)
    (N K : ℕ) (y : ℝ) : ℝ :=
  j0 * (xbB P H tw X0m y X0 θ lam0 +
    4.3 * CNc X0 * (∑ v ∈ dyScales X0 y N, Real.log (2 * v) * TNP.sTheta P H X0m K v) /
      Real.log y) * Real.log y

/-- **`j_{X₀}(x)`** (eq. (jX0)): the supremum over the window `W_x` of `jXat` at the chosen scale
indices `N(y)`, `K(y)`. -/
noncomputable def jXdef (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m X0 θ lam0 j0 : ℝ)
    (NK : ℝ → ℕ × ℕ) (x : ℝ) : ℝ :=
  ⨆ y : {y : ℝ // InW (H x) x y}, jXat P H tw X0m X0 θ lam0 j0 (NK y.1).1 (NK y.1).2 y.1

/-- Each start of the window is below `j_{X₀}(x)`, if the family is bounded. -/
lemma le_jXdef {X0 θ lam0 j0 : ℝ} {NK : ℝ → ℕ × ℕ} {x y : ℝ} (hy : InW (H x) x y)
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // InW (H x) x y} =>
      jXat P H tw X0m X0 θ lam0 j0 (NK y.1).1 (NK y.1).2 y.1)) :
    jXat P H tw X0m X0 θ lam0 j0 (NK y).1 (NK y).2 y ≤ jXdef P H tw X0m X0 θ lam0 j0 NK x :=
  le_ciSup hbdd (⟨y, hy⟩ : {y : ℝ // InW (H x) x y})

/-- **The bridge record at a start `y`**, for a general system. -/
noncomputable def bridgeR_mk (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 θH lam0 j0 y EBR j : ℝ}
    {Tc : ℝ → ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0)
    (hX96 : (10 : ℝ) ^ 96 ≤ X0)
    (hy : X0 ≤ y) (hXmZ : X0m ≤ Z) (h18 : 18 * y ≤ Z ^ 2) (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hTb : ∀ t, |Tc t| ≤ 2) (hTlow : ∀ t, t ≤ X0 → Tc t = 0)
    (N K : ℕ) (hN2 : 2 < N) (hN : y < X0 * 2 ^ N / 4) (hK : √(2 * y) ≤ Pk X0m K)
    (hosc : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * oscR H Tc u ≤ Real.exp (-83))
    (hEBR : Real.exp (-76) ≤ EBR)
    (hj : jXat P H tw X0m X0 θH lam0 j0 N K y ≤ j) :
    BridgeR P H tw X0m X0 θH lam0 Tc j0 y EBR j where
  N := N
  K := K
  hN2 := hN2
  hN := hN
  hK := hK
  o := oscR H Tc
  etaX0Sum := KR.X0S.sX0_sum_le hX96 dyScales_dyadic
  osc := oscBound_oscR P hTb y _
    (fun u hu => dyScales_pos (sizes h hX0e hX0m).2.2.2.2 hu) (fun t => (h.width.reg.pos t).le)
  termOsc := termOsc_oscR P h.width hX0e (p_ge_two_of h hXmZ) hTb hTlow y
  sizeE := by
    have hlX := (sizes h hX0e hX0m).2.1
    have hX0p := (sizes h hX0e hX0m).2.2.2.2
    have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
    have hZ0 : 2500 ≤ Z := by norm_num at hXm7; linarith
    exact (sizeE_le h hH hlX hX0e hX0m hZ0 h18 hK hosc).trans hEBR
  sizeJ := hj
  l520 := l520_of_le h hH hX0e hX0m hXmZ h18 hK hlam0 hlam

/-- **The bridge record for the realised system** `PR θ X₀ ω`, `H = Hc X₀`, `tw = twR θ X₀ ω`,
`T_c = TcR θ X₀ ω j₀`, with `E_BR = e^{-76}` and `j = j_{X₀}(x)`. -/
noncomputable def bridgeR_real {θ' : ℝ} {X₀ : ℕ} {ω : JitterΩ} {Z η1 η2 ε : ℝ} {ε1 : ℝ → ℝ}
    (h : Hyp (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) Z η1 η2 ε1 ε (ε / 10))
    (hX : 10 ^ 8 ≤ Real.log X₀) {lam0 j0 x y : ℝ} (NK : ℝ → ℕ × ℕ)
    (hy : (X₀ : ℝ) ≤ y) (hXmZ : Xm X₀ ≤ Z) (h18 : 18 * y ≤ Z ^ 2) (hlam0 : 0 ≤ lam0)
    (hlam : lam0 ≤ 2) (hTb : ∀ t, |TcR θ' X₀ ω j0 t| ≤ 2)
    (hTlow : ∀ t : ℝ, t ≤ (X₀ : ℝ) → TcR θ' X₀ ω j0 t = 0)
    (hNK : 2 < (NK y).1 ∧ y < X₀ * 2 ^ (NK y).1 / 4 ∧ √(2 * y) ≤ Pk (Xm X₀) (NK y).2)
    (hosc : ∑ u ∈ dyScales X₀ y (NK y).1, Real.log (2 * u) *
      oscR (Queue6.Hc X₀) (TcR θ' X₀ ω j0) u ≤ Real.exp (-83))
    (hW : InW (Queue6.Hc X₀ x) x y)
    (hbdd : BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ x) x y} =>
      jXat (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0
        (NK y.1).1 (NK y.1).2 y.1)) :
    BridgeR (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0
      (TcR θ' X₀ ω j0) j0 y EBRc
      (jXdef (PR θ' X₀ ω) (Queue6.Hc X₀) (twR θ' X₀ ω) (Xm X₀) X₀ (ε / 10) lam0 j0 NK x) :=
  bridgeR_mk h (KR.WidthReal.Hc_Xm_half_le hX)
    (by unfold Xm Queue6.Hc; rw [max_self]) (by
      have e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
        unfold Xm Queue6.Hc; rw [max_self]
      have := h.width.reg.pos (X₀ : ℝ)
      linarith)
    (ten96_le hX)
    hy hXmZ h18 hlam0 hlam hTb hTlow
    (NK y).1 (NK y).2 hNK.1 hNK.2.1 hNK.2.2 hosc le_rfl (le_jXdef hW hbdd)

end BModel

end
