module

public import RequestProject.Beurling.Decomp.Decomposition
public import RequestProject.Beurling.AbsorbEmpty

/-!
# Theorem 4.10 with the decomposition (14) derived

`Theorem410InputsAbs` assumed the decomposition (14) of `F = ζ_P` on the discs around the designed
zeros, with `D̂_{<a_k}` an unspecified entire function `Dlt k`. Here `F = ζ_P` (the continuation
`zetaCont P 1`), `D = N_P - T` is the lag for the target `T` of (6), and `Dlt k = D̂_{<a_k}` is the
early part of its transform (`earlyNoise`). The decomposition and the entireness of `Dlt k` are
then *proved* (`decomposition_14`, `differentiable_earlyNoise_of_integrableOn`), from:

* `X₀` is `X₀`-smooth, the windows of `A` start at or after `X₀`, and the cap in (6) is inactive;
* the global lag bound `|D(x)| ≤ K x^η` for `x ≥ X₀` (the lag bound (13));
* the heights and amplitudes of the oscillation are the ones designed in Lemma 4.8
  (`γ_k` chosen by the rule of Lemma 4.8 for `f = D̂_{<a_k}`, `α_k = κ₀ x_k^{1-θ}/((log x_k)³ γ_k)`).

The last item is a *consistency* condition: `D̂_{<a_k}` depends on `α_j, γ_j` only for `j < k`
(the oscillations with `x⁺_j ≥ a_k` vanish on `[1, a_k]`), so in the paper the design is a
recursive choice; here it is stated as a fixed-point equation.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory Remark12 Oscillation Absorbed Target
  BaseFactor DesignedZero SmoothStep RankinMinorant GoodHeights AbsorbEmpty DesignSize

namespace Decomp

/-- `D̂_{<a_k}` for the lag `D = N_P - T`. -/
noncomputable def earlyOf (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (α γ xp a : ℕ → ℝ) (k : ℕ) : ℂ → ℂ :=
  earlyNoise (lagOf P θ X₀ κ A u α γ xp) (a k)

/-- The lag is bounded by `max K (N(X₀) + X₀) x^η` on `(1, ∞)`. -/
lemma lag_abs_le (P : BeurlingSystem) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}
    {α γ xp : ℕ → ℝ} {η K : ℝ} (hη : 0 ≤ η)
    (hD : ∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ K * x ^ η) {x : ℝ} (hx1 : 1 < x) :
    |lagOf P θ X₀ κ A u α γ xp x| ≤ max K (P.N X₀ + X₀) * x ^ η := by
  set c : ℝ := P.N X₀ + X₀ with hc
  have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx1.le hη
  rcases le_or_gt (X₀ : ℝ) x with hxX | hxX
  · exact (hD x hxX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith) _))
  · have hT : targetOf θ X₀ κ A u α γ xp x = ⌊x⌋₊ := by
      simp only [targetOf, target, if_pos hxX]
    have hN0 : 0 ≤ P.N x := Nat.cast_nonneg _
    have hNX : P.N x ≤ P.N X₀ := BeurlingSystem.N_mono P hxX.le
    have hfl : (⌊x⌋₊ : ℝ) ≤ X₀ := (Nat.floor_le (by linarith)).trans hxX.le
    have hfl0 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
    have h1 : |lagOf P θ X₀ κ A u α γ xp x| ≤ c := by
      simp only [lagOf, hT, hc]
      rw [abs_le]; constructor <;> linarith
    have hc0 : 0 ≤ c := by rw [hc]; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc |lagOf P θ X₀ κ A u α γ xp x| ≤ c := h1
      _ ≤ max K c := le_max_right _ _
      _ = max K c * 1 := by ring
      _ ≤ max K c * x ^ η :=
          mul_le_mul_of_nonneg_left hxη (le_trans hc0 (le_max_right _ _))

/-- The lag is integrable on `(1, a]`. -/
lemma lag_integrableOn_Ioc (P : BeurlingSystem) {X₀ : ℕ} (hXs : X₀ ∈ X₀.smoothNumbers)
    {κ θ : ℝ} (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ2 : θ < 2) {A : Set ℝ} {u : ℝ → ℝ}
    (hAu : ∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (θ / 2) = a) (hAfin : LocFin A)
    (hcap : ∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ 0.1 / Real.log v)
    {α γ xp : ℕ → ℝ} (hsp : Spacing xp) {C : ℝ} (hα : ∀ k, |α k| ≤ C) (hxp : (X₀ : ℝ) ≤ xp 0)
    {η K : ℝ} (hη : 0 ≤ η) (hη2 : η < 2)
    (hD : ∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ K * x ^ η) (a : ℝ) :
    IntegrableOn (lagOf P θ X₀ κ A u α γ xp) (Ioc 1 a) := by
  set D := lagOf P θ X₀ κ A u α γ xp with hDdef
  have hg := lag_integrableOn P hXs hκ hθ0 hθ2.le hAu hAfin hcap hsp hα hxp hη hD
    (s := 2) (by simpa using hθ2) (by simpa using hη2) (by norm_num)
  have hgI : IntegrableOn (fun x : ℝ => (D x : ℂ) * (x : ℂ) ^ (-(2 : ℂ) - 1)) (Icc 1 a) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr (hg.mono_set Ioc_subset_Ioi_self)
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) ^ (3 : ℕ))) (Icc 1 a) :=
    (Complex.continuous_ofReal.pow 3).continuousOn
  have hprod : IntegrableOn _ (Icc 1 a) := (hgI.mul_continuousOn hcont isCompact_Icc).re
  refine (hprod.mono_set Ioc_subset_Icc_self).congr_fun (fun x hx => ?_) measurableSet_Ioc
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx.1
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have e : (x : ℂ) ^ (-(2 : ℂ) - 1) = ((x : ℂ) ^ (3 : ℕ))⁻¹ := by
    rw [show -(2 : ℂ) - 1 = -((3 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
  beta_reduce
  rw [e, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx0'), mul_one]
  exact Complex.ofReal_re _

/-- **The inputs of Theorem 4.10 for `ζ_P`, with the decomposition (14) derived.** As
`Theorem410InputsAbs θ (zetaCont P 1)`, but the decomposition of `ζ_P` on the discs is no longer
assumed and `D̂_{<a_k}` is the early part of the transform of the lag `D = N_P - T` (whose
entireness is derived). In their place: `X₀` is `X₀`-smooth, the windows of `A` start after `X₀`,
the cap of (6) is inactive, the lag bound `|D(x)| ≤ K x^η` holds on `[X₀, ∞)`, and `α, γ` are the
designed amplitudes and heights. -/
def Theorem410InputsDec (θ : ℝ) (P : BeurlingSystem) : Prop :=
  ∃ (X₀ : ℕ) (κ κ₀ η K : ℝ) (xp a : ℕ → ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ : ℕ → ℝ),
    10 ^ 8 ≤ Real.log X₀ ∧ X₀ ∈ X₀.smoothNumbers ∧ 1 / 4 ≤ θ ∧ θ ≤ 1 / 2 ∧
    Real.exp (-Real.log X₀) ≤ κ ∧ κ ≤ 1 ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (X₀ : ℝ) ^ 2 ≤ Real.log (xp 0) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k = designGamma X₀ κ θ κ₀ (earlyOf P θ X₀ κ A u α γ xp a) xp k) ∧
    (∀ k, α k = amplitudeOf θ κ₀ (γ k) (xp k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (earlyOf P θ X₀ κ A u α γ xp a k)) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ x ≥ (X₀ : ℝ), |lagOf P θ X₀ κ A u α γ xp x| ≤ K * x ^ η) ∧
    (∀ k, ∀ y ≥ a k, |lagOf P θ X₀ κ A u α γ xp y| ≤ y ^ η) ∧
    AbsorbedHyp (θ / 2) A u ∧
    (∀ n ∈ A, (X₀ : ℝ) ≤ u n) ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (θ / 2) A u v ≤ 0.1 / Real.log v) ∧
    (∀ n ∈ A, ∃ r : ℝ, (X₀ : ℝ) - CaplLink.capH X₀ X₀ / 2 ≤ r ∧ r < absorbY X₀ n) ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x)))

/-- The radius of the discs is tiny at the switch-on points. -/
lemma designRadius_le {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx0 : 0 < x)
    (hx : X₀ ^ 2 ≤ Real.log x) : 0 < designRadius x ∧ designRadius x ≤ 1 / 10 ^ 6 := by
  obtain ⟨hx1, hll, -⟩ := size_of_log_ge (θ := 1 / 2) (κ := 1) (κ₀ := 1) hX0 hX le_rfl
    (by rw [Real.exp_le_one_iff]; linarith) le_rfl
    (by rw [Real.exp_le_one_iff]; linarith) hx0 hx
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hbig := large_L (Λ := Real.log X₀) (by linarith) hL hll
  have hLL : 0 < Real.log (Real.log x) := by linarith
  have hδ0 : 0 < designRadius x := by unfold designRadius; positivity
  refine ⟨hδ0, ?_⟩
  unfold designRadius
  rw [div_le_div_iff₀ hL (by norm_num)]
  have h3 : (10 : ℝ) ^ 24 ≤ Real.log X₀ ^ 3 := by
    calc (10 : ℝ) ^ 24 = (10 ^ 8) ^ 3 := by norm_num
      _ ≤ Real.log X₀ ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
  nlinarith

/-- **The decomposition (14) and the entireness of `D̂_{<a_k}` are derived**:
`Theorem410InputsDec θ P` gives `Theorem410InputsAbs θ (zetaCont P 1)`. -/
theorem Theorem410InputsDec.toAbs {θ : ℝ} {P : BeurlingSystem} (h : Theorem410InputsDec θ P) :
    Theorem410InputsAbs θ (P.zetaCont 1) := by
  obtain ⟨X₀, κ, κ₀, η, K, xp, a, A, u, α, γ, hX, hXs, hθ1, hθ2, hκ, hκ1, hκ₀1, hκ₀2, hxp0,
    hspk, hγ, hα, hpieces, hη0, hη, ha, hDK, hD, hA, huX, hcap, hAy, hbound⟩ := h
  set D := lagOf P θ X₀ κ A u α γ xp with hDdef
  set Dlt := earlyOf P θ X₀ κ A u α γ xp a with hDltdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX0p : (0 : ℝ) < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos hX0p
  have hX1 : (1 : ℝ) ≤ X₀ := by linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le (Real.exp_pos _) hκ
  have hxpos : ∀ k, 0 < xp k := fun k => lt_of_lt_of_le (ha k).1 (ha k).2.1
  have hsp : Spacing xp := by
    refine ⟨?_, hspk⟩
    have := Real.log_le_sub_one_of_pos (hxpos 0)
    nlinarith
  have hlogk : ∀ k, (X₀ : ℝ) ^ 2 ≤ Real.log (xp k) := fun k =>
    hxp0.trans (Real.log_le_log (hxpos 0) (hsp.strictMono.monotone (Nat.zero_le k)))
  have hxpX : (X₀ : ℝ) ≤ xp 0 := by
    have := Real.log_le_sub_one_of_pos (hxpos 0)
    nlinarith
  have hxk2 : ∀ k, 2 ≤ xp k := fun k => by
    have := Real.log_le_sub_one_of_pos (hxpos k)
    nlinarith [hlogk k]
  have hak : ∀ k, 1 ≤ a k := fun k => by
    have := (ha k).2.2; have := hxk2 k; linarith
  have hΓ : ∀ k, 1 / 2 ≤ heightScale θ κ₀ (xp k) := fun k => by
    have := (size_of_log_ge hX0 hX hθ2 hκ hκ1 hκ₀1 (hxpos k) (hlogk k)).2.2
    have : 0 ≤ Real.exp ((X₀ : ℝ) ^ 2 / 3) / κ := div_nonneg (Real.exp_pos _).le hκ0.le
    linarith
  have hγmem : ∀ k, designGamma X₀ κ θ κ₀ Dlt xp k ∈
      Icc (heightScale θ κ₀ (xp k)) (2 * heightScale θ κ₀ (xp k)) := fun k =>
    chooseHeight_mem _ _ _ (by linarith [hΓ k])
  have hγeq : ∀ k, designGamma X₀ κ θ κ₀ Dlt xp k = γ k := fun k => (hγ k).symm
  have hαeq : ∀ k, designAlpha X₀ κ θ κ₀ Dlt xp k = α k := fun k => by
    rw [hα k]; unfold designAlpha; rw [hγeq k]
  have hαb : ∀ k, |α k| ≤ 2 := fun k => by
    have hm := hγmem k
    rw [hγeq k] at hm
    have hΓk := hΓ k
    have hγ0 : 0 < γ k := by linarith [hm.1]
    rw [hα k]
    have e : amplitudeOf θ κ₀ (γ k) (xp k) = 2 * heightScale θ κ₀ (xp k) / γ k := by
      unfold amplitudeOf; rw [heightScale_eq]
    rw [e, abs_of_nonneg (div_nonneg (by linarith) hγ0.le), div_le_iff₀ hγ0]
    linarith [hm.1]
  have hAu : ∀ n ∈ A, (X₀ : ℝ) ≤ u n ∧ u n + u n ^ (θ / 2) = n := fun n hn =>
    ⟨huX n hn, (hA.weight n hn).u_eq⟩
  have hθ0 : 0 < θ := by linarith
  have hη2 : η < 2 := by linarith
  refine ⟨X₀, κ, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκ, hκ1, hκ₀1, hκ₀2, hxp0,
    fun k => ?_, hpieces, hspk, hη0, hη, ha, hD, hA, hAy, hbound, fun k s hs => ?_⟩
  · -- `D̂_{<a_k}` is entire
    refine differentiable_earlyNoise_of_integrableOn (M := max K (P.N X₀ + X₀) * a k ^ η)
      (hak k) (lag_integrableOn_Ioc P hXs hκ0 hθ0 (by linarith) hAu hA.fin hcap hsp hαb hxpX hη0 hη2
        hDK (a k)) (fun x hx => ?_)
    refine (lag_abs_le P hη0 hDK hx.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hx.1]) hx.2 hη0) ?_)
    exact le_trans (add_nonneg (Nat.cast_nonneg _) hX0) (le_max_right _ _)
  · -- the decomposition (14) on the disc
    obtain ⟨-, hr⟩ := designRadius_le hX0 hX (hxpos k) (hlogk k)
    have hd : ‖s - (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I)‖ ≤ designRadius (xp k) := by
      rwa [mem_closedBall, dist_eq_norm] at hs
    have hre := Complex.abs_re_le_norm (s - (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I))
    have him := Complex.abs_im_le_norm (s - (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I))
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im,
      Complex.add_im, Complex.one_im, Complex.mul_im] at hre him
    have hsre : 1 - 1 / 10 ^ 6 ≤ s.re := by
      have := (abs_le.mp (hre.trans (hd.trans hr))).1
      linarith
    have hs1 : s ≠ 1 := by
      intro h1
      subst h1
      simp only [Complex.one_im] at him
      have hm := (hγmem k).1
      have := hΓ k
      have := (abs_le.mp (him.trans (hd.trans hr))).1
      linarith
    have key := decomposition_14 P hXs hκ0 hθ0 (by linarith) hAu hA.fin hcap hsp hαb hxpX hη0 hDK
      (s := s) (by linarith) (by linarith) hs1 (hak k)
    simp only [hγeq, hαeq]
    exact key

/-- Refined inputs for one system: `PartIInputsSlotModelInit` and `Theorem410InputsDec`. -/
def TheoremAInputsDec (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotModelInit θ X₀ P ∧ Theorem410InputsDec θ P

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsAbs`, with the decomposition (14) of
`ζ_P` and the entireness of `D̂_{<a_k}` derived. -/
def Theorem21InputsDec : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsDec θ X₀ (P ω)

theorem theorem21InputsAbs_of_dec (h : Theorem21InputsDec) : Theorem21InputsAbs := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toAbs⟩⟩

/-- The refined hypothesis `Theorem21InputsDec` implies Theorem 2.1. -/
theorem theorem21_of_dec (h : Theorem21InputsDec) : Theorem21 :=
  theorem21_of_abs (theorem21InputsAbs_of_dec h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsDec`. -/
theorem corollary_2_2_of_dec (h : Theorem21InputsDec) : ¬ QuestionQ :=
  corollary_2_2_of_abs (theorem21InputsAbs_of_dec h)

end Decomp

end
