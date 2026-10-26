module

public import RequestProject.Beurling.Construction.Greedy
public import RequestProject.Beurling.Decomp.Theorem410Dec

/-!
# Theorem 2.1 / Corollary 2.2 from the construction of Section 3

The hypothesis `Theorem21InputsCon` is stated on the concrete probability space of the jitters
(`jitterMeasure` on `ℕ → ℝ`, i.i.d. uniform on `[0, 1]`, with the filtration of the offsets), with
the good event `G = ⋂ E` of a countable family of adapted failure events whose failure
probabilities sum to at most `1.5 / log X₀` (Definition 6.8, Lemma 6.10). On `G` (and on the
full-measure event that every jitter lies in `[0, 1]`), the data of Part I and of Theorem 4.10 are
**coupled**: the same `κ, A, u_a, α, γ, x⁺` and the same slot model enter both. As a consequence the
following are derived instead of assumed:

* the lag bound `|N - T| ≤ x^η` used in Theorem 4.10 (from the queue bound of Part I);
* the cap of (6) being inactive (from `ρ_A ≤ (log v)^{-4}`);
* the windows `u_a ≥ X₀` (Part I);
* `X₀` is `X₀`-smooth (`X₀` even, `≥ 4`);
* the placement fact for `A` (each `a ∈ A` has a prime `r` with `X₀ - H(X₀)/2 ≤ r < y(a)`), from
  the definition (5) of `A` and the box-centred placement of the jittered primes by the greedy
  rule (`GreedyRun.jittered_ge`).

Still hypotheses: the per-window inputs of Theorem 6.6(ii) (`QueueWindowData`), the landing data
of Corollary 3.8 (`Landing`, `LandingInit`), `ρ_A ≤ (log v)^{-4}` (Lemma 6.27(a)), the Rankin bound
for `A` (Lemma 6.26) above `log x = (log X₀)²`, the pieces of `D̂_{<a_k}` in Lemma 4.8(ii)
(`Lemma48PiecesCount`), the failure-probability budget, and the monotonicity of `v - H(v)/2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex Metric Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize CaplLink
  QueueBound LagSplit SlotModel Decomp QueueMono Bookkeeping

namespace Construction

/-- **The inputs of Part I for given data** `κ, A, u, α, γ, x⁺` and slot model `M`: as
`PartIInputsSlotModelInit`, with these data fixed. -/
def PartIWith (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (κ : ℝ) (A : Set ℕ) (u : ℕ → ℝ)
    (α γ xp : ℕ → ℝ) (M : SlotModel X₀) : Prop :=
  0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x, M.T x = target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A u) (osc θ α γ xp) x) ∧
    M.QueueWindowData ∧
    ∃ κp : ℝ → ℝ,
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (P.N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)

theorem PartIWith.toInit {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem} {κ : ℝ} {A : Set ℕ}
    {u : ℕ → ℝ} {α γ xp : ℕ → ℝ} {M : SlotModel X₀} (h : PartIWith θ X₀ P κ A u α γ xp M) :
    PartIInputsSlotModelInit θ X₀ P := by
  obtain ⟨hκ, hκ1, hsp, hα, hxp, hAu, hρ, hT, hq, κp, hκp, hland, hinit⟩ := h
  exact ⟨κ, A, u, α, γ, xp, κp, M, hκ, hκ1, hsp, hα, hxp, hAu, hρ, hT, hq, hκp, hland, hinit⟩

/-- **The lag bound (13) for the given data** (Proposition 4.1): `|N - T| ≤ x^η` on `[X₀, ∞)`. -/
theorem PartIWith.lag {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem} {κ : ℝ} {A : Set ℕ}
    {u : ℕ → ℝ} {α γ xp : ℕ → ℝ} {M : SlotModel X₀} (hθ1 : 1 / 4 ≤ θ)
    (hθ2 : θ ≤ 1 / 2 - 1 / 10000) (hX : 10 ^ 8 ≤ Real.log X₀)
    (h : PartIWith θ X₀ P κ A u α γ xp M) :
    ∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ x ^ lagExponent θ := by
  obtain ⟨hκ, hκ1, hsp, hα, hxp, hAu, hρ, hT, hq, κp, hκp, hland, hinit⟩ := h
  intro x hx
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have e : lagOf P θ X₀ κ A u α γ xp x = P.N x - M.T x := by
    rw [hT x]; rfl
  rw [e]
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · have hLx : 0 < Real.log x := by
      have hX1 := one_lt_of_logX hX0 hX
      exact Real.log_pos (by linarith)
    obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
    have hH : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
    have h12 := ((hland x hx hlate).toSlotData M hX hq hx).two_sided
    have e2 : -(capH X₀ x / 2 * (1 + κp x / Real.log x)) =
        -(capH X₀ x / 2) * (1 + κp x / Real.log x) := by ring
    rw [e2] at h12
    have hB := queueB_nonneg hX0 hX hx
    exact lag_rpow_of_queue hθ1 hθ2 hX0 hX hx
      (abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH hB le_rfl h12.1 h12.2)
  · exact lag_rpow_initial hθ1 hθ2 hX0 hX hx (hκp X₀ le_rfl).1 (hκp X₀ le_rfl).2
      ((hinit x hx hearly).abs_le M hX hq hx hearly)

/-- An even `X₀ ≥ 4` is `X₀`-smooth: its prime factors are at most `X₀ / 2`. -/
lemma even_mem_smoothNumbers {X₀ : ℕ} (hev : Even X₀) (h4 : 4 ≤ X₀) :
    X₀ ∈ X₀.smoothNumbers := by
  rw [Nat.mem_smoothNumbers]
  refine ⟨by omega, fun p hp => ?_⟩
  have hpd : p ∣ X₀ := Nat.dvd_of_mem_primeFactorsList hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  rcases (Nat.le_of_dvd (by omega) hpd).lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    obtain ⟨m, hm⟩ := hev
    have h2 : 2 ∣ p := ⟨m, by omega⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hpp 2 h2) with h | h <;> omega

/-- `(log v)^{-4} ≤ 0.1 / log v` for `log v ≥ 10`: the cap of (6) is inactive. -/
lemma zpow_neg_four_le {v : ℝ} (hv : 10 ≤ Real.log v) :
    Real.log v ^ (-4 : ℤ) ≤ 0.1 / Real.log v := by
  set L := Real.log v
  have hL : 0 < L := by linarith
  rw [zpow_neg, zpow_ofNat, inv_eq_one_div, div_le_div_iff₀ (by positivity) hL]
  have h2 : (10 : ℝ) ≤ L ^ 2 := by nlinarith
  have h3 : (10 : ℝ) ≤ L ^ 3 := by nlinarith
  nlinarith

/-- **The inputs of Theorem 4.10, coupled with Part I.** For the data `κ, A, u, α, γ, x⁺` of
Part I, the jittered primes `jit` and the latest-prime map `latest`: `A` is contained in the
absorbed set (5); `κ ≥ X₀⁻¹`; `κ₀ ∈ [X₀⁻¹, 1/4]`; `log x⁺_0 ≥ X₀²`; the heights and amplitudes are
the designed ones (Lemma 4.8, Theorem 4.10); the pieces of `D̂_{<a_k}` (Lemma 4.8(ii)); the
construction scales `a_k ≤ x⁺_k ≤ 1.001 a_k`; the weight hypotheses on `A`; and the Rankin bound
for `A` (Lemma 6.26) above `log x = (log X₀)²`. -/
def Theorem410InputsCoupled (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) (κ : ℝ) (A : Set ℕ)
    (u : ℕ → ℝ) (α γ xp : ℕ → ℝ) (jit : Set ℝ) (latest : ℕ → ℝ) : Prop :=
  ∃ (κ₀ : ℝ) (a : ℕ → ℝ),
    A ⊆ absorbedRule (10 ^ 7) jit latest (absorbY X₀) ∧
    Real.exp (-Real.log X₀) ≤ κ ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (X₀ : ℝ) ^ 2 ≤ Real.log (xp 0) ∧
    (∀ k, γ k = designGamma X₀ κ θ κ₀ (earlyOf P θ X₀ κ A u α γ xp a) xp k) ∧
    (∀ k, α k = amplitudeOf θ κ₀ (γ k) (xp k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (earlyOf P θ X₀ κ A u α γ xp a k)) ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    AbsorbedHyp (θ / 2) A u ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x)))

/-- **Coupled inputs give the inputs of Theorem 4.10 with the decomposition derived**: the lag
bound, the cap, `X₀`-smoothness, `u_a ≥ X₀` and the placement fact are derived. -/
theorem Theorem410InputsCoupled.toDec {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem} {κ : ℝ}
    {A : Set ℕ} {u : ℕ → ℝ} {α γ xp : ℕ → ℝ} {M : SlotModel X₀} {jit : Set ℝ}
    {latest : ℕ → ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hev : Even X₀)
    (hjit : ∀ r ∈ jit, (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ r)
    (hI : PartIWith θ X₀ P κ A u α γ xp M)
    (h : Theorem410InputsCoupled θ X₀ P κ A u α γ xp jit latest) :
    Theorem410InputsDec θ P := by
  have hlag := hI.lag hθ1 hθ2 hX
  obtain ⟨-, hκ1, hsp, -, -, hAu, hρ, -⟩ := hI
  obtain ⟨κ₀, a, hArule, hκ, hκ₀1, hκ₀2, hxp0, hγ, hα, hpieces, ha, hA, hbound⟩ := h
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h4 : 4 ≤ X₀ := by
    have : (4 : ℝ) ≤ X₀ := by linarith
    exact_mod_cast this
  have hη0 : 0 ≤ lagExponent θ := by
    unfold lagExponent; exact div_nonneg (le_min (by linarith) (by linarith)) (by norm_num)
  have hη : lagExponent θ ≤ θ / 2 := by
    unfold lagExponent; have := min_le_left θ (1 / 2 - θ); linarith
  have hxpos : ∀ k, 0 < xp k := fun k => lt_of_lt_of_le (ha k).1 (ha k).2.1
  have hlogk : ∀ k, (X₀ : ℝ) ^ 2 ≤ Real.log (xp k) := fun k =>
    hxp0.trans (Real.log_le_log (hxpos 0) (hsp.strictMono.monotone (Nat.zero_le k)))
  have haX : ∀ k, (X₀ : ℝ) ≤ a k := fun k => by
    have h1 := Real.log_le_sub_one_of_pos (hxpos k)
    have h2 := hlogk k
    have h3 := (ha k).2.2
    nlinarith
  refine ⟨X₀, κ, κ₀, lagExponent θ, 1, xp, a, A, u, α, γ, hX, even_mem_smoothNumbers hev h4,
    hθ1, by linarith, hκ, hκ1, hκ₀1, hκ₀2, hxp0, hsp.exp_le, hγ, hα, hpieces, hη0, hη, ha,
    fun x hx => by simpa using hlag x hx, fun k y hy => hlag y ((haX k).trans hy), hA,
    fun n hn => (hAu n hn).1, fun v hv => ?_, ?_, hbound⟩
  · have hlv : 10 ≤ Real.log v := by
      have := Real.log_le_log (by linarith) hv; linarith
    exact (hρ v hv).trans (zpow_neg_four_le hlv)
  · intro n hn
    exact absorbedRule_placement hjit n (hArule hn)

/-- **Theorem 2.1, hypothesis on the concrete construction.** For each admissible `θ` there is
`X_Hux` such that for every even `X₀ ≥ max(e^{10⁸}, X_Hux)`:

* `v ↦ v - H(v)/2` is non-decreasing on `[X₀, ∞)` (§3.4);
* there are systems `P(ω)` on the jitter space and a countable family of failure events `E i`,
  adapted to the filtration of the jitters, with total failure probability at most `1.5/log X₀`;
* on the good event `G = ⋂ E`, for every `ω` with all jitters in `[0, 1]`, there are data
  `κ, A, u, α, γ, x⁺`, a slot model `M` and a latest-prime map such that the Part I inputs hold
  with `M`, and the Theorem 4.10 inputs hold, coupled to the same data, with the jittered primes
  being those placed by the greedy rule from `M`, the width `H` and the jitters `ω`. -/
def Theorem21InputsCon : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    MonotoneOn (fun v => v - capH X₀ v / 2) (Ici (X₀ : ℝ)) ∧
    ∃ (P : JitterΩ → BeurlingSystem) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      FailureAdapted jitterFiltration E time ∧
      ∑' i, jitterMeasure (E i)ᶜ ≤ ENNReal.ofReal (1.5 / Real.log X₀) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Icc (0 : ℝ) 1) →
        ∃ (κ : ℝ) (A : Set ℕ) (u : ℕ → ℝ) (α γ xp : ℕ → ℝ) (M : SlotModel X₀)
          (latest : ℕ → ℝ),
          PartIWith θ X₀ (P ω) κ A u α γ xp M ∧
          Theorem410InputsCoupled θ X₀ (P ω) κ A u α γ xp (jitteredPrimesOf M (capH X₀) ω)
            latest

/-- `H ≥ 0`. -/
lemma capH_nonneg (X₀ x : ℝ) : 0 ≤ capH X₀ x :=
  le_trans (Real.exp_pos _).le (le_max_left _ _)

theorem theorem21InputsDec_of_con (h : Theorem21InputsCon) : Theorem21InputsDec := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨hmono, P, ι, hι, E, time, hE, hsum, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log X₀ := by linarith
  set S : Set JitterΩ := {ω | ∀ j, ω j ∈ Icc (0 : ℝ) 1} with hS
  refine ⟨JitterΩ, inferInstance, jitterMeasure, P, goodAll E ∩ S, inferInstance, ?_, ?_⟩
  · have hS0 : jitterMeasure Sᶜ = 0 := by
      have := ae_jitter_mem
      rwa [Filter.Eventually, mem_ae_iff] at this
    rw [measure_inter_conull hS0]
    exact goodAll_prob_ge jitterFiltration hE (by positivity) hsum
  · rintro ω ⟨hG, hSω⟩
    obtain ⟨κ, A, u, α, γ, xp, M, latest, hI, hC⟩ := hP ω hG hSω
    refine ⟨hI.toInit, hC.toDec hθ.1 hθ.2 hlog hev ?_ hI⟩
    -- the placement of the jittered primes
    have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
      intro x hx
      rw [hI.2.2.2.2.2.2.2.1 x]
      simp only [target, if_pos hx]
    exact GreedyRun.jittered_ge ⟨M, capH X₀, ω, hTlow⟩ hSω (capH_nonneg X₀) hmono

/-- The hypothesis on the concrete construction implies Theorem 2.1. -/
theorem theorem21_of_con (h : Theorem21InputsCon) : Theorem21 :=
  theorem21_of_dec (theorem21InputsDec_of_con h)

/-- **Corollary 2.2** from the hypothesis on the concrete construction. -/
theorem corollary_2_2_of_con (h : Theorem21InputsCon) : ¬ QuestionQ :=
  corollary_2_2_of_dec (theorem21InputsDec_of_con h)

end Construction

end
