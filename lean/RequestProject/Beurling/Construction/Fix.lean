module

public import RequestProject.Beurling.Construction.Design
public import RequestProject.Beurling.Construction.JitterFloor
public import RequestProject.Beurling.Construction.LocalCount

/-!
# Theorem 2.1 / Corollary 2.2 with the parameters fixed and the heights designed

`Theorem21InputsFix` is `Theorem21InputsCon` with the following former hypotheses **removed**
(they are now proved):

* the parameters of Section 2.2 are fixed: `κ = X₀^{-5/12+2ε_κ}`, `κ₀ = 1/4`,
  `x⁺_0 = exp(X₀²)`, `x⁺_{k+1} = exp(x⁺_k)`; their required properties (`0 < κ ≤ 1`,
  `κ, κ₀ ≥ X₀⁻¹`, `κ₀ ≤ 1/4`, the spacing, `x⁺_0 ≥ X₀`, `log x⁺_0 ≥ X₀²`) are proved;
* the heights `γ_k` and amplitudes `α_k` are *defined* by the recursive rule of Lemma 4.8
  (`designedGamma`, `designedAlpha`); the fixed-point condition and `|α_k| ≤ 2` are proved;
* the monotonicity of `v - H(v)/2` is no longer assumed: the floor `s - H(s)/2 ≥ X₀ - H(X₀)/2`
  for slots `s ≥ X₀`, which is what the placement of the jittered primes uses, is proved
  (`JitterFloor.capH_floor`);
* `ρ_A ≤ (log v)^{-4}` (Lemma 6.27(a)) is derived from the pointwise sparsity of Lemma 6.26,
  `#(A ∩ [v, v + v^{θ/2}]) ≤ v^{θ/2} (log v)^{-4}`, which takes its place (as in the paper,
  "(a) is Lemma 6.26");
* the weight hypotheses on `A` (`AbsorbedHyp`) are derived from `u_a + u_a^{θ/2} = a`, `u_a ≥ X₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex Metric Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize CaplLink
  QueueBound LagSplit SlotModel Decomp QueueMono Bookkeeping

namespace Construction

/-- The remaining inputs of Part I, for the absorbed set `A` (with `u_a`), the construction
scales `a_k` and the slot model `M`; `κ`, `x⁺`, `γ`, `α` are the fixed / designed ones. -/
def PartIRest (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ)
    (M : SlotModel X₀) : Prop :=
  (∀ n ∈ A, (X₀ : ℝ) ≤ u n ∧ u n + u n ^ (θ / 2) = n) ∧ LocFin A ∧
    (∀ v ≥ (X₀ : ℝ),
      (localCountA A v (v + v ^ (θ / 2)) : ℝ) ≤ v ^ (θ / 2) * Real.log v ^ (-4 : ℤ)) ∧
    (∀ x, M.T x = target X₀ (kappaParam X₀) (countA A) (absorbedDensityCap (θ / 2) A u)
      (osc θ (designedAlpha P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (switchOn X₀)) x) ∧
    M.QueueWindowData ∧
    ∃ κp : ℝ → ℝ,
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (P.N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)

/-- The remaining inputs of Theorem 4.10: `A` is contained in the absorbed set (5) (for the
jittered primes `jit` and the latest-prime map `latest`); the pieces of `D̂_{<a_k}`
(Lemma 4.8(ii)); the construction scales `a_k ≤ x⁺_k ≤ 1.001 a_k`; and the Rankin bound for `A`
(Lemma 6.26) above `log x = (log X₀)²`. -/
def Theorem410Rest (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ)
    (jit : Set ℝ) (latest : ℝ → ℝ) : Prop :=
  A ⊆ absorbedRule (10 ^ 7) jit latest (absorbY X₀) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ (kappa0Param X₀) (switchOn X₀ k))
      (earlyOf P θ X₀ (kappaParam X₀) A u
        (designedAlpha P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (designedGamma P θ X₀ (kappaParam X₀) A u (kappa0Param X₀) (switchOn X₀) a)
        (switchOn X₀) a k)) ∧
    (∀ k, 0 < a k ∧ a k ≤ switchOn X₀ k ∧ switchOn X₀ k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x)))

/-- **Theorem 2.1, hypothesis on the concrete construction, with the parameters fixed and the
heights designed.** As `Theorem21InputsCon`, without the monotonicity of `v - H(v)/2`, without
the parameter conditions of Section 2.2 and without the fixed-point condition on `γ_k, α_k`; the
density bound `ρ_A ≤ (log v)^{-4}` is replaced by Lemma 6.26. -/
def Theorem21InputsFix : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (P : JitterΩ → BeurlingSystem) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      FailureAdapted jitterFiltration E time ∧
      ∑' i, jitterMeasure (E i)ᶜ ≤ ENNReal.ofReal (1.5 / Real.log X₀) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ∃ (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ) (M : SlotModel X₀) (latest : ℝ → ℝ),
          PartIRest θ X₀ (P ω) A u a M ∧
          Theorem410Rest θ X₀ (P ω) A u a (jitteredPrimesOf M (capH X₀) ω) latest

/-- **Placement of the jittered primes from the floor property**: if the jitters lie in
`[0, 1]`, `H ≥ 0`, and `s - H(s)/2 ≥ X₀ - H(X₀)/2` for `s ≥ X₀`, every jittered prime is
`≥ X₀ - H(X₀)/2`. -/
theorem GreedyRun.jittered_ge_of_floor {X₀ : ℕ} (R : GreedyRun X₀)
    (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1) (hH : ∀ v, 0 ≤ R.H v)
    (hfloor : ∀ s ≥ (X₀ : ℝ), (X₀ : ℝ) - R.H X₀ / 2 ≤ s - R.H s / 2) :
    ∀ r ∈ R.jitteredPrimes, (X₀ : ℝ) - R.H X₀ / 2 ≤ r := by
  rintro r ⟨k, -, rfl⟩
  have hs := R.slot_ge (k + 1)
  have h1 := (landing_mem_box (s := R.M.slot (k + 1)) (hH (R.M.slot (k + 1))) (hU (k + 1))).1
  have h2 := hfloor _ hs
  unfold primeValueOf
  linarith

/-- `Γ_k > 0` for the switch-on points. -/
lemma heightScale_switchOn_pos (θ : ℝ) {X₀ : ℝ} (hX : 1 ≤ X₀) (k : ℕ) :
    0 < heightScale θ (kappa0Param X₀) (switchOn X₀ k) := by
  have h1 : 1 < switchOn X₀ k := by
    cases k with
    | zero =>
      show 1 < Real.exp (X₀ ^ 2)
      exact Real.one_lt_exp_iff.mpr (by positivity)
    | succ k => exact switchOn_gt_one X₀ k
  have hL := Real.log_pos h1
  unfold heightScale kappa0Param
  have : 0 < X₀ := by linarith
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < switchOn X₀ k) (1 - θ)
  positivity

/-- `Theorem21InputsFix` with the probability budget stated as its conclusion
`P(G) ≥ 1 - 1.5/log X₀` (for the good event `G = ⋂ E`). -/
def Theorem21InputsFixP : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (P : JitterΩ → BeurlingSystem) (ι : Type) (E : ι → Set JitterΩ),
      ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ jitterMeasure (goodAll E) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ∃ (A : Set ℝ) (u : ℝ → ℝ) (a : ℕ → ℝ) (M : SlotModel X₀) (latest : ℝ → ℝ),
          PartIRest θ X₀ (P ω) A u a M ∧
          Theorem410Rest θ X₀ (P ω) A u a (jitteredPrimesOf M (capH X₀) ω) latest

/-- `Theorem21InputsFix` gives `Theorem21InputsFixP` (the union bound). -/
theorem theorem21InputsFixP_of_fix (h : Theorem21InputsFix) : Theorem21InputsFixP := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨P, ι, hι, E, time, hE, hsum, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨P, ι, E, goodAll_prob_ge jitterFiltration hE
    (by have : 0 < Real.log X₀ := by linarith
        positivity) hsum, hP⟩

/-- **`Theorem21InputsFixP` gives the hypothesis `Theorem21InputsDec`** (and hence Theorem 2.1). -/
theorem theorem21InputsDec_of_fixP (h : Theorem21InputsFixP) : Theorem21InputsDec := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨P, ι, E, hprob, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log X₀ := by linarith
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) < X₀ := one_lt_of_logX hX0 hlog
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hXlog : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX4 : (4 : ℝ) ≤ X₀ := by linarith
  set S : Set JitterΩ := {ω | ∀ j, ω j ∈ Icc (0 : ℝ) 1} with hS
  refine ⟨JitterΩ, inferInstance, jitterMeasure, P, goodAll E ∩ S, inferInstance, ?_, ?_⟩
  · have hS0 : jitterMeasure Sᶜ = 0 := by
      have := ae_jitter_mem
      rwa [Filter.Eventually, mem_ae_iff] at this
    rw [measure_inter_conull hS0]
    exact hprob
  · rintro ω ⟨hG, hSω⟩
    obtain ⟨A, u, a, M, latest, hI, hC⟩ := hP ω hG hSω
    obtain ⟨hAu, hAfin, h626, hT, hq, κp, hκp, hland, hinit⟩ := hI
    obtain ⟨hArule, hpieces, ha, hbound⟩ := hC
    set κ := kappaParam (X₀ : ℝ) with hκdef
    set xp := switchOn (X₀ : ℝ) with hxpdef
    set γ := designedGamma (P ω) θ X₀ κ A u (kappa0Param X₀) xp a with hγdef
    set α := designedAlpha (P ω) θ X₀ κ A u (kappa0Param X₀) xp a with hαdef
    have hsp : Spacing xp := switchOn_spacing _
    have hxp0 : (X₀ : ℝ) ≤ xp 0 := switchOn_zero_ge _
    have hb : 0 < θ / 2 := by linarith [hθ.1]
    have hρ := rhoA_le_of_lemma626 hb (by linarith) hAu hAfin h626
    have hPI : PartIWith θ X₀ (P ω) κ A u α γ xp M := by
      refine ⟨kappaParam_pos (by linarith), kappaParam_le_one hX1.le, hsp, fun k => ?_,
        hxp0, hAu, hAfin, hρ, hT, hq, κp, hκp, hland, hinit⟩
      have hm := designedAlpha_mem (P ω) θ X₀ κ A u (kappa0Param X₀) xp a
        (heightScale_switchOn_pos θ hX1.le) k
      rw [abs_of_nonneg (by linarith [hm.1])]
      exact hm.2
    have hAbs : AbsorbedHyp (θ / 2) A u := by
      refine ⟨hb, by linarith [hθ.2],
        fun n hn => ⟨hb, by linarith [hθ.2], ?_, ?_, (hAu n hn).2⟩, hAfin⟩
      · have hu := (hAu n hn).1
        have hr : 0 ≤ u n ^ (θ / 2) := Real.rpow_nonneg (by linarith) _
        have := (hAu n hn).2
        nlinarith
      · linarith [(hAu n hn).1]
    have hCo : Theorem410InputsCoupled θ X₀ (P ω) κ A u α γ xp
        (jitteredPrimesOf M (capH X₀) ω) latest := by
      refine ⟨(kappa0Param X₀), a, hArule, kappaParam_ge hX1.le, kappa0Param_ge hX4,
        kappa0Param_le hX4, ?_, fun k => ?_, fun k => rfl, hpieces, ha, hAbs, hbound⟩
      · rw [hxpdef, log_switchOn_zero]
      · exact designedGamma_fixed (P ω) hsp hX1n hxp0 (fun k => ⟨(ha k).1, (ha k).2.1⟩) k
    refine ⟨hPI.toInit, hCo.toDec hθ.1 hθ.2 hlog hev ?_ hPI⟩
    have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
      intro x hx
      rw [hT x]
      simp only [target, if_pos hx]
    exact GreedyRun.jittered_ge_of_floor ⟨M, capH X₀, ω, hTlow⟩ hSω (capH_nonneg X₀)
      (fun s hs => JitterFloor.capH_floor hX0 hlog hs)

/-- **`Theorem21InputsFix` gives the hypothesis `Theorem21InputsDec`** (and hence Theorem 2.1). -/
theorem theorem21InputsDec_of_fix (h : Theorem21InputsFix) : Theorem21InputsDec :=
  theorem21InputsDec_of_fixP (theorem21InputsFixP_of_fix h)

/-- Theorem 2.1 from `Theorem21InputsFix`. -/
theorem theorem21_of_fix (h : Theorem21InputsFix) : Theorem21 :=
  theorem21_of_dec (theorem21InputsDec_of_fix h)

/-- **Corollary 2.2** from `Theorem21InputsFix`. -/
theorem corollary_2_2_of_fix (h : Theorem21InputsFix) : ¬ QuestionQ :=
  corollary_2_2_of_dec (theorem21InputsDec_of_fix h)

end Construction

end
