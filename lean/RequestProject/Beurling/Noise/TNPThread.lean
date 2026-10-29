module

public import RequestProject.Beurling.Noise.TNPScales
public import RequestProject.Beurling.Noise.KRNorm2
public import RequestProject.Beurling.Noise.BridgeXBTau

/-!
# Lemma 5.20 threaded into Propositions 5.18, 5.26 and Lemma 5.27

The consumers took the Lemma 5.20 quantities as hypotheses (`EtaBound` with `λ₀ C_N E_η ≤ ½`,
`ThetaStar`, `EtaBlk` with `2.04 ∑ s ≤ 0.02`, `ThetaBlk`). Here they are discharged by the proof of
Lemma 5.20 (`TauNearProof*.lean`, `KR.TNP`) on the dyadic scales `dyScales X₀ x N`
(`TNPScales.lean`), which also discharge the covering hypotheses.

Standing hypotheses of every theorem below:

* `h : TNP.Hyp …`: (HBS) on `[1, Z]`, `log X₀⁻ ≥ 10⁸`, `PaperWidth`, the decision order, and the
  local count of Corollary 6.3(ii) (field `count`, still a hypothesis);
* `hH : H(X₀⁻/2) ≤ exp(8 (log log(X₀⁻/2))²)`: the standard width at `X₀⁻/2` (§5.1);
* `h18 : 18 x ≤ Z`: the horizon. The proof of Lemma 5.20 in `TauNearProof*.lean` reads `𝒩` up to
  `18 v` for the scales `v ≤ x` (Euler products over `3P_k`-smooth cofactors); this is a stronger
  horizon than the `2x/X₀⁻ ≤ Z` of the consumers (the paper reads `𝒩` only up to about `x`);
* the scale data `N` (`x < X₀ 2^N/4`) and `K` (`√(2x) ≤ P_K`), which exist (`exists_N`,
  `exists_K`).

What remains a hypothesis: `EtaX0Sum` / the `η_{X₀}` scale bounds (step (iii) of
Proposition 5.18), and, for Proposition 5.26, `OscBound` and `TermOsc`.
-/

@[expose] public section

open Finset Real BeurlingSystem MeasureTheory Set

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `C_N = C_S (2.04 + 4.71/log X₀)`. -/
noncomputable abbrev CNt (X0 : ℝ) : ℝ :=
  max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)

lemma CNt_bounds {X0 : ℝ} (hX0 : 100000000 ≤ Real.log X0) : 0 ≤ CNt X0 ∧ CNt X0 ≤ 158 := by
  have hPhi := BSaias.PhiInf_le (τ := 100000000) le_rfl
  have hCS : max (2.01 * BSaias.PhiInf 100000000) 1.4 ≤ 77 := by
    rw [max_le_iff]; constructor <;> linarith
  have hCS0 : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_of_le_right (by norm_num)
  have hl : 4.71 / Real.log X0 ≤ 1 / 1000000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hl0 : 0 ≤ 4.71 / Real.log X0 := div_nonneg (by norm_num) (by linarith)
  unfold CNt
  refine ⟨by positivity, ?_⟩
  nlinarith

/-- The standing size facts. -/
lemma sizes (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 : ℝ} (hX0e : X0m = X0 - H X0 / 2)
    (hX0m : X0m ≤ X0) :
    0 < X0m ∧ 100000000 ≤ Real.log X0 ∧ X0 / 2 ≤ X0m ∧ 4 ≤ X0 ∧ 0 < X0 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hl : 100000000 ≤ Real.log X0 := h.hXm.trans (Real.log_le_log hX hX0m)
  have hsm := hP.small X0 (by linarith)
  have hX0m7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  refine ⟨hX, hl, by linarith, by norm_num at hX0m7; linarith, by linarith⟩

lemma xZ_of (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {x : ℝ} (hx : X0m ≤ x) (h18 : 18 * x ≤ Z) :
    2 * x / X0m ≤ Z := by
  have hX0m7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  have hX : 0 < X0m := by norm_num at hX0m7; linarith
  rw [div_le_iff₀ hX]
  nlinarith

lemma sqrt_le_Pk {X0m x v : ℝ} {K : ℕ} (hK : √(2 * x) ≤ Pk X0m K) (hv : v ≤ x) :
    √(2 * v) ≤ Pk X0m K :=
  (Real.sqrt_le_sqrt (by linarith)).trans hK

/-- The scale facts used by `TauNearProof*` on `dyScales X₀ x N`. -/
lemma scale_facts (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2)
    (hX0m : X0m ≤ X0) (h18 : 18 * x ≤ Z) {N K : ℕ} (hK : √(2 * x) ≤ Pk X0m K) :
    Sep (dyScales X0 x N) ∧ (∀ v ∈ dyScales X0 x N, 1 ≤ v) ∧
      (∀ v ∈ dyScales X0 x N, 18 * v ≤ Z) ∧ (∀ v ∈ dyScales X0 x N, √(2 * v) ≤ Pk X0m K) := by
  obtain ⟨-, -, -, h4, hX0⟩ := sizes h hX0e hX0m
  refine ⟨dyScales_sep hX0, fun v hv => dyScales_ge h4 hv, fun v hv => ?_, fun v hv =>
    sqrt_le_Pk hK (dyScales_le hv)⟩
  have := dyScales_le hv; linarith

/-- The `η̃`-blocks of Lemma 5.20. -/
noncomputable abbrev sEta (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) (K : ℕ) : ℝ → ℝ :=
  blk P H X0m K fun k => 1 / (Real.log (Pk X0m k) - 0.18)

/-- The `θ`-blocks of Lemma 5.20. -/
noncomputable abbrev sTheta (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) (K : ℕ) : ℝ → ℝ :=
  blk P H X0m K fun k => Real.log (Pk X0m k) + 2

/-- The `η`-blocks of Lemma 5.20. -/
noncomputable abbrev sEta0 (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) (K : ℕ) : ℝ → ℝ :=
  blk P H X0m K fun _ => 1

/-- `θ_* = 207800 Φ₂(X₀⁻/2)`. -/
noncomputable abbrev thetaS (H : ℝ → ℝ) (X0m : ℝ) : ℝ := 207800 * Phi H 2 (X0m / 2)

/-- **Proposition 5.18, window bounds**, with Lemma 5.20 discharged on the dyadic scales. -/
theorem prop_5_18_tnp (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    {lam0 X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (h18 : 18 * x ≤ Z)
    {N K : ℕ} (hN : x < X0 * 2 ^ N / 4) (hK : √(2 * x) ≤ Pk X0m K) :
    ∀ u ∈ dyScales X0 x N, WopNT P H tw X0m x X0 u ≤
        2 * CNt X0 * Real.log (2 * u) / Real.log x ∧
      (2 * X0 ≤ u → Wop P H tw X0m x u ≤ 2 * CNt X0 * Real.log (2 * u) / Real.log x) := by
  obtain ⟨hX, hl, h2, -, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hS, hS1, hSZ, hSK⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  obtain ⟨hC0, hC⟩ := CNt_bounds hl
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  exact prop_5_18_hbs P h.hbs h.hXm h.width hX0e hp2 ht htv hlam hlam1 hx (xZ_of h hx h18)
    (by linarith) hX0m (cover_NAll hX0 hX (by linarith) hN) (fun u hu => by linarith [hS1 u hu])
    (fun u hu => dyScales_kind hX0 h2 hu) (etaBound_energy h hS hS1 hSZ hSK).1
    (energy_small h hH hS hS1 hSZ hSK hlam0 (by linarith) hC0 hC)

/-- **Proposition 5.18, terminal blocks**, with Lemma 5.20 discharged; `EtaX0Sum` (step (iii))
remains. -/
theorem prop_5_18_terminal_tnp (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    {lam0 X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (h18 : 18 * x ≤ Z)
    {N K : ℕ} (hN : x < X0 * 2 ^ N / 4) (hK : √(2 * x) ≤ Pk X0m K) {s0 : ℝ → ℝ}
    (hX0s : EtaX0Sum P H X0m X0 (dyScales X0 x N) s0) {u : ℝ} (hu : u ∈ dyScales X0 x N)
    (hlog : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u)) :
    Wop P H tw X0m x u ≤ 5.1 * CNt X0 * Real.log (2 * u) / Real.log x := by
  obtain ⟨hX, hl, h2, -, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hS, hS1, hSZ, hSK⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  obtain ⟨hC0, hC⟩ := CNt_bounds hl
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  exact prop_5_18_terminal_hbs P h.hbs h.hXm h.width hX0e hp2 ht htv hlam hlam1 hx
    (xZ_of h hx h18) (by linarith) hX0m (cover_NAll hX0 hX (by linarith) hN)
    (fun u hu => by linarith [hS1 u hu]) (fun u hu => dyScales_kind hX0 h2 hu)
    (etaBound_energy h hS hS1 hSZ hSK).1
    (energy_small h hH hS hS1 hSZ hSK hlam0 (by linarith) hC0 hC) hX0s hu hlog

/-- The horizon-restricted `θ_*` at the heights read by `Sall_rec_on`. -/
lemma theta_on_levels (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {x : ℝ} (hx : X0m ≤ x)
    (h18 : 18 * x ≤ Z) :
    ∀ d ∈ NAll P x X0m,
      etaG P H tw X0m (fun y => Real.log y + 1) (posn P.labelVal x d) ≤ thetaS H X0m := by
  intro d hd
  have hX := h.width.X0m_pos
  have hy1 := posn_ge_of_mem_NAll hd hX
  have hy2 : posn P.labelVal x d ≤ x := by
    unfold posn
    have := LemmaM.one_le_valN P.labelVal (fun r _ => P.one_le_labelVal r) (n := d)
    exact div_le_self (by linarith) this
  exact thetaStar_on h (by linarith) (by linarith)

/-- **Proposition 5.18, the `∞`-norm bound**, with Lemma 5.20 (`θ_*` on the horizon, `E⁰_η`)
discharged; the `η_{X₀}` scale bounds (step (iii)) remain. -/
theorem prop_5_18_inf_tnp (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    {lam0 X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hx : X0m ≤ x) (h18 : 18 * x ≤ Z) {N K : ℕ} (hN : x < X0 * 2 ^ N / 4)
    (hK : √(2 * x) ≤ Pk X0m K) {s0 : ℝ → ℝ}
    (hX0s : ∀ v ∈ dyScales X0 x N, 0 ≤ s0 v ∧ ∀ y, v ≤ y → y < 2 * v →
      etaX0 P H X0m y ≤ s0 v)
    (hs0 : ∑ v ∈ dyScales X0 x N, s0 v ≤ 1.52) :
    ∑ n ∈ NAll P x (X0m / 2), TVt P H tw X0m x n / Vl P n ≤
        2.04 * (Real.log x + 1) / (1 - 2.04 * lam0 * thetaS H X0m) + 3.2 ∧
      ∑ n ∈ NAll P x (X0m / 2), TVt P H tw X0m x n / Vl P n ≤ 2.1 * (Real.log x + 1) + 3.2 := by
  obtain ⟨hX, hl, h2, -, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hS, hS1, hSZ, hSK⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  obtain ⟨hθ0, hθs⟩ := thetaStar_small h hH hlam0 (by linarith)
  have hS0 : ∀ v ∈ dyScales X0 x N, 0 < v := fun v hv => by linarith [hS1 v hv]
  exact prop_5_18_inf_on h.hbs h.hXm h.width hX0e hp2 ht hlam hlam1 hx (xZ_of h hx h18)
    (cover_NAll hX0 hX (by linarith) hN) hS0 hθ0 (theta_on_levels h hx h18) hθs
    (etaBlk_sum h hS hS0 hSZ hSK).1 (etaBlk_small h hH hS hS0 hSZ hSK) hX0s hs0

/-- **Proposition 5.26**, with Lemma 5.20 (`E_η`, `E_θ`) discharged on the dyadic scales and
`E_θ ≤ 10⁻⁷`; `EtaX0Sum`, `OscBound` and `TermOsc` remain. -/
theorem prop_5_26_tnp (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    {lam0 X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0 ≤ x) (h18 : 18 * x ≤ Z)
    {N K : ℕ} (hN2 : 2 < N) (hN : x < X0 * 2 ^ N / 4) (hK : √(2 * x) ≤ Pk X0m K)
    {s0 : ℝ → ℝ} (hX0s : EtaX0Sum P H X0m X0 (dyScales X0 x N) s0)
    {Tc : ℝ → ℝ} (hTm : Measurable Tc) (hTb : ∀ t, |Tc t| ≤ 2) {o : ℝ → ℝ}
    (hosc : OscBound P H x Tc (dyScales X0 x N) o) (hTo : TermOsc P H tw X0m x Tc (o X0)) :
    Real.log x * |BRc P H tw X0m x Tc| ≤
      (5.1 * CNt X0 + max (2.01 * BSaias.PhiInf 100000000) 1.4) *
          ∑ u ∈ dyScales X0 x N, Real.log (2 * u) * o u +
        8.4 * CNt X0 * ∑ v ∈ dyScales X0 x N, Real.log (2 * v) * sTheta P H X0m K v ∧
      ∑ v ∈ dyScales X0 x N, Real.log (2 * v) * sTheta P H X0m K v ≤ 1 / 10000000 := by
  obtain ⟨hX, hl, h2, -, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hS, hS1, hSZ, hSK⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  obtain ⟨hC0, hC⟩ := CNt_bounds hl
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  have hxm : X0m ≤ x := hX0m.trans hx
  refine ⟨?_, thetaE_small h hH hS hS1 hSZ hSK⟩
  exact prop_5_26_hbs h.hbs h.hXm h.width hX0e hp2 ht htv hlam hlam1 hxm (xZ_of h hxm h18)
    (by linarith) hX0m (cover_NAll hX0 hX (by linarith) hN) (cover_levels hX0 hX h2 hN)
    (fun u hu => by linarith [hS1 u hu]) (fun u hu => dyScales_kind hX0 h2 hu)
    (etaBound_energy h hS hS1 hSZ hSK).1
    (energy_small h hH hS hS1 hSZ hSK hlam0 (by linarith) hC0 hC) hX0s
    (thetaBlk_sum h hS hS1 hSZ hSK).1 hTm hTb hosc (X0_mem_dyScales hN2 hx) hTo

/-- **Lemma 5.27**, with Lemma 5.20 discharged on the dyadic scales and `E_θ ≤ 10⁻⁷`; the
`η_{X₀}` scale bounds (step (iii) of Proposition 5.18) remain. -/
theorem lemma_5_27_tnp (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ Real.exp (8 * Real.log (Real.log (X0m / 2)) ^ 2))
    {lam0 X0 x : ℝ} (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 3 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (h18 : 18 * x ≤ Z)
    {N K : ℕ} (hN : x < X0 * 2 ^ N / 4) (hK : √(2 * x) ≤ Pk X0m K) {s0 : ℝ → ℝ}
    (hX0b : ∀ v ∈ dyScales X0 x N, 0 ≤ s0 v ∧ ∀ y, v ≤ y → y < 2 * v →
      etaX0 P H X0m y ≤ s0 v)
    (hs0 : ∑ v ∈ dyScales X0 x N, s0 v ≤ 1.52) :
    |Rres P H tw X0m x ((Ici X0).indicator fun _ => 1) -
        rhoSh P tw X0m x ((Ici X0).indicator fun _ => 1)| ≤
      xbB P H tw X0m x X0 θ lam0 +
        4.3 * CNt X0 * (∑ v ∈ dyScales X0 x N, Real.log (2 * v) * sTheta P H X0m K v) /
          Real.log x ∧
      ∑ v ∈ dyScales X0 x N, Real.log (2 * v) * sTheta P H X0m K v ≤ 1 / 10000000 := by
  obtain ⟨hX, hl, h2, -, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hS, hS1, hSZ, hSK⟩ := scale_facts h hX0e hX0m h18 (N := N) hK
  obtain ⟨hC0, hC⟩ := CNt_bounds hl
  have hlam0 : 0 ≤ lam0 := by linarith [h.width.theta_nonneg]
  refine ⟨?_, thetaE_small h hH hS hS1 hSZ hSK⟩
  exact lemma_5_27 h.hbs h.hXm h.width hX0e hp2 ht htv hlam hlam1 hx (xZ_of h hx h18)
    (by linarith) hX0m (cover_NAll hX0 hX (by linarith) hN)
    (fun u hu => by linarith [hS1 u hu]) (fun u hu => dyScales_kind hX0 h2 hu)
    (etaBound_energy h hS hS1 hSZ hSK).1
    (energy_small h hH hS hS1 hSZ hSK hlam0 (by linarith) hC0 hC) hX0b hs0
    (thetaBlk_sum h hS hS1 hSZ hSK).1

end KR.TNP

end
