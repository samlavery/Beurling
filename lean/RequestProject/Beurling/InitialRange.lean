module

public import RequestProject.Beurling.DesignSize

/-!
# Proposition 4.1 on the initial range, from the slot model

On `[X₀, X₀ + 2H(x))` the proof of Proposition 4.1 says that "the accounting in the proof of
Corollary 3.8 applies verbatim (with `j := j₀ - 1` if `x < s_{j₀}`)" and gives
`|D| ≤ B(X₀) + (H(X₀)/2)(1 + κ₊/log X₀) + 5`. In `PartIInputsSlotModel` this bound was a
hypothesis. Here it is derived in the slot model from the same landing data as on the late range
(with landing slack `ε ≤ 5/2`, which absorbs the evaluation of `H` and `κ₊` at `X₀`):

* `InitialRange.capH_le_rpow` : `H(x) ≤ x^{1/8}` for `x ≥ X₀`;
* `InitialRange.lt_two_mul_of_initial` : the initial range lies in `[X₀, 2X₀)`;
* `InitialRange.queueBScale_eq_init` : on `[1, 2X₀)` the frozen bound is `B(X₀)` (one dyadic scale);
* `SlotModel.LandingInit.abs_le` : the bound of the proof of Proposition 4.1, with the model's
  queue (slot `k = 0` of the model is the paper's `j₀ - 1`, with `V_{j₀-1} = j₀`, no arrivals and
  `Q_{j₀-1} = 0`, so the case `x < s_{j₀}` is included);
* `PartIInputsSlotModelInit` / `toSlotModel`;
* `Theorem21InputsInitSize` : the top-level refined hypothesis, combining this with
  `Theorem410InputsSize`; `theorem21_of_initSize`, `corollary_2_2_of_initSize`.
-/

@[expose] public section

open Real MeasureTheory DesignedZero Target Oscillation Absorbed CaplLink QueueBound
  Greedy QueueDet QueueMono LagSplit SlotCount

namespace InitialRange

/-- `1 ≤ H(x)` for `x ≥ X₀`. -/
lemma one_le_capH {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    1 ≤ capH X₀ x := by
  obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
  exact le_trans (Real.one_le_exp (by positivity)) hstd

/-- **`H(x) ≤ x^{1/8}`** for `x ≥ X₀` (the numerical part of Proposition 4.1 at `θ = 1/4`). -/
theorem capH_le_rpow {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capH X₀ x ≤ x ^ (1 / 8 : ℝ) := by
  have hH := one_le_capH hX0 hX hx
  have hB := queueB_nonneg hX0 hX hx
  have h := lag_rpow_of_queue (θ := 1 / 4) (D := capH X₀ x) (by norm_num) (by norm_num) hX0 hX
    hx (by rw [abs_of_nonneg (by linarith)]; linarith)
  have e : lagExponent (1 / 4) = 1 / 8 := by unfold lagExponent; norm_num
  rwa [e, abs_of_nonneg (by linarith)] at h

/-- `H(x) ≤ x^{1/40}` (the lag bound at `θ = 1/20`). -/
theorem capH_le_rpow40 {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capH X₀ x ≤ x ^ (1 / 40 : ℝ) := by
  have hH := one_le_capH hX0 hX hx
  have hB := queueB_nonneg hX0 hX hx
  have h := lag_rpow_of_queue (θ := 1 / 20) (D := capH X₀ x) (by norm_num) (by norm_num) hX0 hX
    hx (by rw [abs_of_nonneg (by linarith)]; linarith)
  have e : lagExponent (1 / 20) = 1 / 40 := by unfold lagExponent; norm_num
  rwa [e, abs_of_nonneg (by linarith)] at h

/-- `H(x) ≤ x^{1/400}` (the lag bound at `θ = 1/200`). -/
theorem capH_le_rpow400 {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capH X₀ x ≤ x ^ (1 / 400 : ℝ) := by
  have hH := one_le_capH hX0 hX hx
  have hB := queueB_nonneg hX0 hX hx
  have h := lag_rpow_of_queue (θ := 1 / 200) (D := capH X₀ x) (by norm_num) (by norm_num) hX0
    hX hx (by rw [abs_of_nonneg (by linarith)]; linarith)
  have e : lagExponent (1 / 200) = 1 / 400 := by unfold lagExponent; norm_num
  rwa [e, abs_of_nonneg (by linarith)] at h

/-- **The initial range lies in one dyadic scale**: `X₀ ≤ x < X₀ + 2H(x)` implies `x < 2X₀`. -/
theorem lt_two_mul_of_initial {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hx : X₀ ≤ x) (hearly : x < X₀ + 2 * capH X₀ x) : x < 2 * X₀ := by
  by_contra hc; push_neg at hc
  have hX1 := one_lt_of_logX hX0 hX
  have hx0 : 0 < x := by linarith
  have hH := capH_le_rpow hX0 hX hx
  set y := x ^ (1 / 8 : ℝ) with hy
  have hy8 : y ^ 8 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
  -- `x ≥ X₀ ≥ 256`, so `y ≥ 2`
  have hX256 : 256 ≤ X₀ := by
    have : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hy2 : 2 ≤ y := by
    by_contra h; push_neg at h
    have : y ^ 8 < 2 ^ 8 := pow_lt_pow_left₀ h hy0 (by norm_num)
    linarith
  have h64 : 64 * y ≤ y ^ 8 / 2 := by
    have : 2 ^ 7 ≤ y ^ 7 := pow_le_pow_left₀ (by norm_num) hy2 7
    have : y ^ 8 = y * y ^ 7 := by ring
    nlinarith
  linarith

/-- On `[X₀, 2X₀)` the dyadic scale is `X₀`. -/
lemma dyadicScale_eq_self {X₀ s : ℝ} (hX0 : 0 < X₀) (h1 : X₀ ≤ s) (h2 : s < 2 * X₀) :
    dyadicScale X₀ s = X₀ := by
  unfold dyadicScale
  have hr1 : 1 ≤ s / X₀ := by rw [le_div_iff₀ hX0]; linarith
  have hr2 : s / X₀ < 2 := by rw [div_lt_iff₀ hX0]; linarith
  have : Int.log 2 (s / X₀) = 0 := by
    rw [Int.log_of_one_le_right _ hr1]
    have hf : ⌊s / X₀⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]; norm_num; exact ⟨hr1, hr2⟩
    rw [hf]; simp
  rw [this]; simp

/-- **On `[1, 2X₀)` the frozen bound is `B(X₀)`.** -/
theorem queueBScale_eq_init {X₀ s : ℝ} (hX0 : 0 < X₀) (hs : s < 2 * X₀) :
    queueBScale X₀ s = queueB X₀ X₀ := by
  unfold queueBScale
  rw [dyadicScale_eq_self hX0 (le_max_left _ _) (max_lt (by linarith) hs)]

end InitialRange

open InitialRange

namespace SlotModel

variable {X₀ : ℕ} (M : SlotModel X₀)

/-- The landing data of Corollary 3.8 on the initial range (proof of Proposition 4.1): as
`Landing`, with the landing slack `ε ≤ 5/2`. -/
def LandingInit (N W x : ℝ) : Prop :=
  ∃ (C Ep Em ε c lp lm : ℝ) (F : ℝ → ℝ) (Sp Sm : Finset ℝ),
    Monotone F ∧ N = (M.V (M.slotIdx x) : ℝ) - C + Ep - Em ∧
    0 ≤ C ∧ C ≤ (M.slotArr (M.slotIdx x) : ℝ) ∧ 0 ≤ lp ∧ 0 ≤ lm ∧
    (∀ s ∈ Sp, x ≤ s ∧ s ≤ x + lp) ∧ (∀ s ∈ Sm, x - lm ≤ s ∧ s ≤ x) ∧
    (∀ s ∈ Sp, ∀ t ∈ Sp, s < t → 1 ≤ F t - F s) ∧
    (∀ s ∈ Sm, ∀ t ∈ Sm, s < t → 1 ≤ F t - F s) ∧
    F (x + lp) - F x ≤ c * lp ∧ F x - F (x - lm) ≤ c * lm ∧
    0 ≤ Ep ∧ Ep ≤ Sp.card ∧ 0 ≤ Em ∧ Em ≤ Sm.card ∧
    c * lp ≤ W + ε ∧ c * lm ≤ W + ε ∧ ε ≤ 5 / 2

/-- **Proposition 4.1 on the initial range, in the slot model**: for `X₀ ≤ x < X₀ + 2H(x)`, the
landing data with slack `5/2` give `|N(x) - T(x)| ≤ B(X₀) + W + 5`. The queue bound
`Q_j ≤ B(X₀)` comes from the deterministic part of Theorem 6.6(ii), since every slot `s_j ≤ x`
lies in the first dyadic scale. -/
theorem LandingInit.abs_le (hX : 10 ^ 8 ≤ Real.log X₀) (hq : M.QueueWindowData) {N W x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hearly : x < (X₀ : ℝ) + 2 * capH X₀ x) (h : M.LandingInit N W x) :
    |N - M.T x| ≤ queueB X₀ X₀ + W + 5 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast hX1.le
  obtain ⟨C, Ep, Em, ε, c, lp, lm, F, Sp, Sm, hF, hN, hC0, hCA, hlp, hlm, hSp, hSm, hgp, hgm,
    hcp, hcm, hEp0, hEp, hEm0, hEm, hWp, hWm, hε⟩ := h
  obtain ⟨hs1, -, hT1, hT2⟩ := M.mem_slot hX₀ hx
  set k := M.slotIdx x
  have hV := M.count_identity k
  have hQA := M.queue_sub_slotArr k
  have h2 := lt_two_mul_of_initial hX0 hX hx hearly
  have hQ : (M.queue k : ℝ) ≤ queueB X₀ X₀ := by
    have := M.queue_le_frozen hX hq k
    rwa [queueBScale_eq_init (by linarith) (lt_of_le_of_lt hs1 h2)] at this
  have hB0 := queueB_nonneg hX0 hX (le_refl (X₀ : ℝ))
  have hN' : N = (((X₀ : ℝ) - 1 + k) + 1 + (M.queue k : ℝ)) - C + Ep - Em := by
    rw [hN, hV]; push_cast; ring
  have := initial_lag_of_slots F hF Sp Sm hN' hT1 hT2 M.hϑ0 M.hϑ hC0 hCA
    (by exact_mod_cast hQA) hQ hlp hlm hSp hSm hgp hgm hcp hcm hEp0 hEp hEm0 hEm hWp hWm hε
  rw [_root_.abs_le]; constructor <;> linarith [this.1, this.2]

end SlotModel

open SlotModel

/-- **The inputs of Theorem 2.1(i) with the slot model on the whole range.** As
`PartIInputsSlotModel`, except that the initial-range bound of Proposition 4.1 is no longer
assumed: on `[X₀, X₀ + 2H(x))` only the landing data of Corollary 3.8 (with slack `5/2`, and
`W` evaluated at `X₀`) are assumed, as on the late range. -/
def PartIInputsSlotModelInit (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  ∃ (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ) (α γ xp : ℕ → ℝ) (κp : ℝ → ℝ) (M : SlotModel X₀),
    0 < κ ∧ κ ≤ 1 ∧
    Spacing xp ∧ (∀ k, |α k| ≤ 2) ∧ (X₀ : ℝ) ≤ xp 0 ∧
    (∀ a ∈ A, (X₀ : ℝ) ≤ u a ∧ u a + u a ^ (thetaB θ) = a) ∧
    LocFin A ∧
    (∀ v ≥ (X₀ : ℝ), absorbedDensity (thetaB θ) A u v ≤ (Real.log v) ^ (-4 : ℤ)) ∧
    (∀ x, M.T x = target X₀ κ (countA A) (absorbedDensityCap (thetaB θ) A u) (osc θ α γ xp) x) ∧
    M.QueueWindowData ∧
    (∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x) ∧
    (∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (P.N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x) ∧
    (∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (P.N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)

/-- **The initial-range bound is derived**: `PartIInputsSlotModelInit` gives
`PartIInputsSlotModel`. -/
theorem PartIInputsSlotModelInit.toSlotModel {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hX : 10 ^ 8 ≤ Real.log X₀) (h : PartIInputsSlotModelInit θ X₀ P) :
    PartIInputsSlotModel θ X₀ P := by
  obtain ⟨κ, A, u, α, γ, xp, κp, M, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hT, hq, hκp, hland,
    hinit⟩ := h
  refine ⟨κ, A, u, α, γ, xp, κp, M, hκ, hκ1, hsp, hα, hxp, hAu, hAfin, hρ, hT, hq, hκp, hland,
    fun x hx hearly => ?_⟩
  have := (hinit x hx hearly).abs_le M hX hq hx hearly
  rw [hT x] at this
  linarith

/-- Refined inputs for one system: `PartIInputsSlotModelInit` and `Theorem410InputsSize`. -/
def TheoremAInputsInitSize (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsSlotModelInit θ X₀ P ∧ Theorem410InputsSize θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsSlotModel`, without the initial-range
bound of Proposition 4.1 (derived from the slot model) and without the size conditions on `κ₀`
and `x⁺_k` beyond the parameter choices of Section 2.2 (`Theorem410InputsSize`). -/
def Theorem21InputsInitSize : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsInitSize θ X₀ (P ω)

theorem theorem21InputsSlotModel_of_initSize (h : Theorem21InputsInitSize) :
    Theorem21InputsSlotModel := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω =>
    ⟨(hP ω hω).1.toSlotModel hlog, (hP ω hω).2.toRankin⟩⟩

/-- The refined hypothesis `Theorem21InputsInitSize` implies Theorem 2.1. -/
theorem theorem21_of_initSize (h : Theorem21InputsInitSize) : Theorem21 :=
  theorem21_of_slotModel (theorem21InputsSlotModel_of_initSize h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsInitSize`. -/
theorem corollary_2_2_of_initSize (h : Theorem21InputsInitSize) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_initSize h)

end
