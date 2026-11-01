module

public import RequestProject.Beurling.PartIConcrete
public import RequestProject.BSCert.CaplRaise

/-!
# Theorem 6.23(c) from the certificate `raise_max.py`: the jitter width `H`

In Theorem 2.1(i) the lag bound (13) is derived (Proposition 4.1, `Bookkeeping.lag_bound`) from
three conditions on the jitter width `H` and the parameter `M₁` of the queue bound (75):

  `M₁² ≤ H`,   `H_std = e^{8ℓ²} ≤ H`,   `log H - log H_std ≤ 10⁻⁶ L`,

where `L = log x` and `ℓ = log L`. In `PartIInputsConcrete` these were hypotheses. Here they are
**proved** for the paper's choice

  `H = max(H_std, M̄₁²)`,

with `M̄₁ = M̄₁(Λ, s)` the explicit value of Theorem 6.23 (`BSCert.Capl.Mbar1`), at
`Λ = log X₀` and capacity parameter `s = ℓ - 2 log Λ` (so that `ℓ = 2 log Λ + s` and `L = e^ℓ`).
The third condition is exactly the certificate `raise_max.py`
(`BSCert.Capl.raise_le`: `max(0, 2 log M̄₁ - 8ℓ²)/L ≤ 10⁻⁶` for `Λ ≥ 10⁸`, `s ≥ -log Λ`), at
the break point `s_H` of `γ(s)` (the root of `γ*(s_H) = 1/3 - 10⁻⁵`, `BSCert.Capl.sH_spec`).
The range `s ≥ -log Λ` is exactly `x ≥ X₀`.

* `CaplLink.capH_conditions` : the three conditions, for all `x ≥ X₀`, `log X₀ ≥ 10⁸`;
* `PartIInputsCapl` : `PartIInputsConcrete` with `M₁ = M̄₁` and `H = max(H_std, M̄₁²)`; only the
  queue bound `B ≤ 34 M̄₁ L²` (75) and the lag decomposition remain as hypotheses;
* `corollary_2_2_of_capl` : Corollary 2.2 from the corresponding refined hypothesis.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed

namespace CaplLink

open BSCert.Capl

/-- The break point `s_H` of `γ(s)`: the unique root in `[0, 10]` of `γ*(s) = 1/3 - 10⁻⁵`. -/
noncomputable def sHroot : ℝ := Classical.choose sH_spec

lemma sHroot_mem : sHroot ∈ Set.Ioo (5.9745 : ℝ) 5.9746 := (Classical.choose_spec sH_spec).1

lemma gstar_sHroot : gstar sHroot = gTarget := (Classical.choose_spec sH_spec).2.1

/-- The capacity parameter `s(x) = log log x - 2 log Λ`, `Λ = log X₀`. -/
noncomputable def capS (X₀ x : ℝ) : ℝ := Real.log (Real.log x) - 2 * Real.log (Real.log X₀)

/-- `M̄₁` of Theorem 6.23 at `Λ = log X₀`, `s = s(x)` and the break point `s_H`. -/
noncomputable def capM1 (X₀ x : ℝ) : ℝ := Mbar1 sHroot (Real.log X₀) (capS X₀ x)

/-- The jitter width `H = max(H_std, M̄₁²)`, `H_std = e^{8 (log log x)²}`. -/
noncomputable def capH (X₀ x : ℝ) : ℝ :=
  max (Real.exp (8 * Real.log (Real.log x) ^ 2)) (capM1 X₀ x ^ 2)

lemma ell_eq (X₀ x : ℝ) : 2 * Real.log (Real.log X₀) + capS X₀ x = Real.log (Real.log x) := by
  unfold capS; ring

lemma logs_of_ge {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    10 ^ 8 ≤ Real.log x ∧ Real.log (Real.log X₀) ≤ Real.log (Real.log x) ∧
      0 < Real.log (Real.log x) := by
  have hX1 : 0 < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have h1 : Real.log X₀ ≤ Real.log x := Real.log_le_log hX1 hx
  refine ⟨hX.trans h1, Real.log_le_log (by linarith) h1, Real.log_pos (by linarith)⟩

lemma capM1_pos {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    0 < capM1 X₀ x := by
  obtain ⟨-, -, h3⟩ := logs_of_ge hX0 hX hx
  unfold capM1 Mbar1 rbar0
  rw [ell_eq]
  positivity

/-- **Theorem 6.23(c)** for `H = max(H_std, M̄₁²)`: for `log X₀ ≥ 10⁸` and `x ≥ X₀`,
`M̄₁² ≤ H`, `H_std ≤ H` and `log H - 8 (log log x)² ≤ 10⁻⁶ log x`. -/
theorem capH_conditions {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capM1 X₀ x ^ 2 ≤ capH X₀ x ∧
    Real.exp (8 * Real.log (Real.log x) ^ 2) ≤ capH X₀ x ∧
    Real.log (capH X₀ x) - 8 * Real.log (Real.log x) ^ 2 ≤ 1e-6 * Real.log x := by
  obtain ⟨h1, h2, h3⟩ := logs_of_ge hX0 hX hx
  refine ⟨le_max_right _ _, le_max_left _ _, ?_⟩
  have hM := capM1_pos hX0 hX hx
  have hS := sHroot_mem
  have hr := raise_le (sH := sHroot) (Λ := Real.log X₀) (s := capS X₀ x) hS.1.le
    (by linarith [hS.2]) (by rw [gstar_sHroot]; unfold gTarget; norm_num) (by linarith)
    (by have := ell_eq X₀ x; linarith)
  unfold raise at hr
  rw [ell_eq, Real.exp_log (by linarith), div_le_iff₀ (by linarith)] at hr
  have hlogH : Real.log (capH X₀ x) =
      max (8 * Real.log (Real.log x) ^ 2) (2 * Real.log (capM1 X₀ x)) := by
    unfold capH
    rcases le_total (Real.exp (8 * Real.log (Real.log x) ^ 2)) (capM1 X₀ x ^ 2) with h | h
    · rw [max_eq_right h, Real.log_pow, max_eq_right]
      · push_cast; ring
      · have := Real.log_le_log (Real.exp_pos _) h
        rw [Real.log_exp, Real.log_pow] at this; push_cast at this; linarith
    · rw [max_eq_left h, Real.log_exp, max_eq_left]
      have := Real.log_le_log (by positivity) h
      rw [Real.log_exp, Real.log_pow] at this; push_cast at this; linarith
  rw [hlogH]
  unfold capM1
  have := le_max_right 0 (2 * Real.log (Mbar1 sHroot (Real.log X₀) (capS X₀ x)) -
    8 * Real.log (Real.log x) ^ 2)
  rcases le_total (8 * Real.log (Real.log x) ^ 2)
      (2 * Real.log (Mbar1 sHroot (Real.log X₀) (capS X₀ x))) with h | h
  · rw [max_eq_right h]; norm_num at hr ⊢; linarith
  · rw [max_eq_left h]; norm_num; positivity

/-- **The standard regime** (`ℓ ≥ ℓ_std`): if `s(x) > s_H` and `4ℓ² - log 4 ≥ 7.5Λ`, then
`log c = 4ℓ² - log 4`, `M̄₁ ≤ 2c = e^{4ℓ²}/2` and `H = H_std = e^{8ℓ²}`. -/
theorem capH_eq_std {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hs : sHroot < capS X₀ x)
    (hl : 7.5 * Real.log X₀ + Real.log 4 ≤ 4 * Real.log (Real.log x) ^ 2) :
    capM1 X₀ x ≤ Real.exp (4 * Real.log (Real.log x) ^ 2) / 2 ∧
      capH X₀ x = Real.exp (8 * Real.log (Real.log x) ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := logs_of_ge hX0 hX hx
  set ℓ := Real.log (Real.log x) with hℓ
  have hl18 : 18 ≤ 2 * Real.log (Real.log X₀) + capS X₀ x := by
    rw [ell_eq]
    have : (18 : ℝ) ^ 2 ≤ ℓ ^ 2 := by
      have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
      nlinarith
    nlinarith
  have hM := Mbar1_le (sH := sHroot) hl18
  have hg : gam sHroot (capS X₀ x) ≤ 7.5 :=
    gam_le_of_gt (by rw [gstar_sHroot]; unfold gTarget; norm_num) hs
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hlogc : logc sHroot (Real.log X₀) (capS X₀ x) = 4 * ℓ ^ 2 - Real.log 4 := by
    unfold logc
    rw [ell_eq, ← hℓ]
    apply max_eq_left
    nlinarith
  have hc : Real.exp (logc sHroot (Real.log X₀) (capS X₀ x)) = Real.exp (4 * ℓ ^ 2) / 4 := by
    rw [hlogc, Real.exp_sub, Real.exp_log (by norm_num)]
  have hM1 : capM1 X₀ x ≤ Real.exp (4 * ℓ ^ 2) / 2 := by
    unfold capM1; rw [hc] at hM; linarith
  refine ⟨hM1, ?_⟩
  have hM0 := capM1_pos hX0 hX hx
  have hsq : capM1 X₀ x ^ 2 ≤ Real.exp (8 * ℓ ^ 2) := by
    have e : Real.exp (8 * ℓ ^ 2) = Real.exp (4 * ℓ ^ 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e]
    have := Real.exp_pos (4 * ℓ ^ 2)
    nlinarith
  unfold capH
  exact max_eq_left hsq

/-- **`H = x^{o(1)}`** (for `ℓ ≥ ℓ_std`, `H = H_std = e^{8ℓ²}`; below, `H ≤ e^{8ℓ² + 10⁻⁶ L}`). -/
theorem subPow_capH {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    SubPow (capH X₀) X₀ := fun ε hε => by
  set Λ := Real.log X₀ with hΛ
  have h2 : Filter.Tendsto (fun L : ℝ => Real.log L ^ 2 / L) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simpa using this
  obtain ⟨L₁, hL₁⟩ := (h2.eventually (ge_mem_nhds (show (0 : ℝ) < ε / 8 by positivity))).exists_forall_of_atTop
  set ℓ₀ := 2 * Real.log Λ + 6 + 2 * Λ with hℓ₀
  set L₂ := max (max L₁ (Real.exp ℓ₀)) Λ with hL₂
  refine ⟨Real.exp (8 * Real.log L₂ ^ 2 + 1e-6 * L₂), fun x hx => ?_⟩
  obtain ⟨hLx, hll, hl0⟩ := logs_of_ge hX0 hX hx
  have hX1 : 1 < X₀ := by
    by_contra hc; push_neg at hc; linarith [Real.log_nonpos hX0 hc]
  have hx0 : 0 < x := by linarith
  have hxε : 1 ≤ x ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hΛ0 : 0 < Λ := by linarith
  have hlΛ : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  rcases le_total (Real.log x) L₂ with hle | hge
  · -- below `L₂`: `log H ≤ 8ℓ² + 10⁻⁶ L ≤ 8 (log L₂)² + 10⁻⁶ L₂`
    obtain ⟨-, -, hr⟩ := capH_conditions hX0 hX hx
    have hH0 : 0 < capH X₀ x := lt_of_lt_of_le (Real.exp_pos _) (capH_conditions hX0 hX hx).2.1
    have hll2 : Real.log (Real.log x) ≤ Real.log L₂ := Real.log_le_log (by linarith) hle
    have hsq : Real.log (Real.log x) ^ 2 ≤ Real.log L₂ ^ 2 :=
      pow_le_pow_left₀ hl0.le hll2 2
    have : capH X₀ x ≤ Real.exp (8 * Real.log L₂ ^ 2 + 1e-6 * L₂) := by
      rw [← Real.exp_log hH0, Real.exp_le_exp]; nlinarith
    have hC0 := Real.exp_pos (8 * Real.log L₂ ^ 2 + 1e-6 * L₂)
    nlinarith
  · -- above `L₂`: the standard regime, `H = e^{8ℓ²} ≤ e^{εL} = x^ε`
    set L := Real.log x with hL
    have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hge
    have hLe : Real.exp ℓ₀ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hge
    have hℓ : ℓ₀ ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hLe
    have hs : sHroot < capS X₀ x := by
      unfold capS; rw [← hL, ← hΛ]; linarith [sHroot_mem.2]
    have hstd : 7.5 * Λ + Real.log 4 ≤ 4 * Real.log L ^ 2 := by
      have h4 : Real.log 4 < 2 := by
        have := Real.log_two_lt_d9
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      have : 2 * Λ ≤ Real.log L := by linarith
      nlinarith
    obtain ⟨-, hH⟩ := capH_eq_std hX0 hX hx hs hstd
    rw [hH]
    have hb := hL₁ L hL1
    have hLp : 0 < L := by linarith
    rw [div_le_iff₀ hLp] at hb
    have h1 : Real.exp (8 * Real.log L ^ 2) ≤ x ^ ε := by
      rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, ← hL]; nlinarith
    have hC : 1 ≤ Real.exp (8 * Real.log L₂ ^ 2 + 1e-6 * L₂) := Real.one_le_exp (by
      have : 0 ≤ L₂ := le_trans hΛ0.le (le_max_right _ _)
      positivity)
    nlinarith

end CaplLink

open CaplLink

/-- The inputs for Theorem 2.1(i) with the concrete absorbed density and the concrete jitter
width: as `PartIInputsConcrete`, with `M₁ = M̄₁` and `H = max(H_std, M̄₁²)` of Theorem 6.23. The
conditions of Theorem 6.23(c) on `H` are no longer assumed (they are `capH_conditions`). -/
def PartIInputsCapl (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (B : ℝ → ℝ), 0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + winH X₀ (u a) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (winH X₀) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x ≥ (X₀ : ℝ), B x ≤ 34 * capM1 X₀ x * Real.log x ^ 2) ∧
    (∀ x ≥ (X₀ : ℝ),
      |P.N x - target X₀ κ (countA A) (absorbedDensityCap (winH X₀) A u) (osc θ α γ xp) x| ≤
        B x + 3 * capH X₀ x + 3)

/-- Theorem 6.23(c) (`capH_conditions`) turns `PartIInputsCapl` into `PartIInputsConcrete`. -/
theorem PartIInputsCapl.toConcrete {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hX : 10 ^ 8 ≤ Real.log X₀) (h : PartIInputsCapl θ X₀ P) : PartIInputsConcrete θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, B, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hB, hD⟩ := h
  exact ⟨κ, A, u, α, γ, xp, B, capH X₀, capM1 X₀, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hB,
    fun x hx => (capH_conditions (Nat.cast_nonneg _) hX hx).1,
    fun x hx => (capH_conditions (Nat.cast_nonneg _) hX hx).2.1,
    fun x hx => (capH_conditions (Nat.cast_nonneg _) hX hx).2.2,
    subPow_capH (Nat.cast_nonneg _) hX, hD⟩

/-- Refined inputs for one system: `PartIInputsCapl` and the inputs of Theorem 4.10. -/
def TheoremAInputsCapl (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsCapl θ X₀ P ∧ Theorem410InputsZB48 θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis** with the jitter width `H = max(H_std, M̄₁²)` of
Theorem 6.23 (whose condition (c) is now proved from the certificate `raise_max.py`). -/
def Theorem21InputsCapl : Prop :=
  ∃ XHux : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) (1 / 2 - 1 / 10000), ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsCapl θ X₀ (P ω)

theorem theorem21InputsConcrete_of_capl (h : Theorem21InputsCapl) : Theorem21InputsConcrete := by
  obtain ⟨XHux, hX⟩ := h
  refine ⟨XHux, fun θ hθ X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX θ hθ X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1.toConcrete hlog, (hP ω hω).2⟩⟩

/-- The refined hypothesis implies Theorem 2.1. -/
theorem theorem21_of_capl (h : Theorem21InputsCapl) : Theorem21 :=
  theorem21_of_concrete (theorem21InputsConcrete_of_capl h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsCapl`. -/
theorem corollary_2_2_of_capl (h : Theorem21InputsCapl) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_capl h)

end
