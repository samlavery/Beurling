module

public import RequestProject.Beurling.Theorem410Count

/-!
# The design parameters, the choice rule for `γ_k` and the absorbed-set growth

In `Theorem410InputsCount` the following were hypotheses about free sequences `α_k`, `γ_k`:

* the design parameters (`DesignParams`, `1 ≤ α_k ≤ 2`, `T + 1/2 ≤ γ_k`, `κ Γ_k ≥ e^{X₀²/3}`,
  `γ_k ≤ x⁺_k`);
* the choice rule of Lemma 4.8 (`ChoiceRule`);
* the absorbed-set growth `δ_k ℓ + 2 log(2 + ℓ) + 5 ≤ ς(ℓ)` for
  `0 ≤ ℓ ≤ log(γ_k + 1)/(1 - θ/2)`, one condition for every `k`.

Here the heights and the amplitudes are **defined**:

* `Γ_k = heightScale θ κ₀ x⁺_k = κ₀ (x⁺_k)^{1-θ} / (2 log x⁺_k)`;
* `γ_k = chooseHeight X₀ κ D̂_{<a_k} Γ_k`, a good height in `[Γ_k, 2Γ_k]` if one exists, and `Γ_k`
  otherwise, so the choice rule holds by construction (`chooseHeight_rule`);
* `α_k = amplitudeOf θ κ₀ γ_k x⁺_k = κ₀ (x⁺_k)^{1-θ} / (γ_k log x⁺_k)`, so `α_k γ_k` is the
  value required by Lemma 4.6 and `1 ≤ α_k ≤ 2` because `γ_k ∈ [Γ_k, 2Γ_k]` (`amplitudeOf_mem`).

The design parameters then follow from conditions on `κ₀` and the switch-on points `x⁺_k` alone
(`designParams_of_mem`). The absorbed-set growth for every `k` follows from the single uniform
condition `42 log(2 + ℓ) + 5 ≤ ς(ℓ)` for all `ℓ ≥ 0` (`growth_of_uniform`), which no longer mentions
the heights.

`Theorem410InputsDesign` collects the remaining inputs; `Theorem410InputsDesign.toCount` derives
`Theorem410InputsCount`, and `theorem21_of_design`, `corollary_2_2_of_design` follow.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  GoodHeights

namespace DesignedZero

/-- The base height `Γ(x) = κ₀ x^{1-θ} / (2 log x)`: the heights are chosen in `[Γ, 2Γ]`. -/
noncomputable def heightScale (θ κ₀ x : ℝ) : ℝ := κ₀ * x ^ (1 - θ) / (2 * Real.log x)

/-- The amplitude `α = κ₀ x^{1-θ} / (γ log x)`, so that `α γ = κ₀ x^{1-θ}/log x` (eq. (ampl),
`κ'_k = κ₀`). -/
noncomputable def amplitudeOf (θ κ₀ γ x : ℝ) : ℝ := κ₀ * x ^ (1 - θ) / Real.log x / γ

open Classical in
/-- **The choice rule for `γ_k`**: the least good height in `[Γ, 2Γ]` when one exists, `Γ`
otherwise (§3.2, `γ_k := min S_k`). The least good height is attained whenever `f` is continuous
(the good set is then closed and bounded), which holds for `f = D̂_{<a_k}`; the arbitrary good
height `h.choose` is only a fallback that keeps the rule total. Taking the minimum makes `γ_k` a
measurable function of the data, as the paper requires. -/
noncomputable def chooseHeight (X₀ : ℕ) (κ : ℝ) (f : ℂ → ℂ) (Γ : ℝ) : ℝ :=
  if h : ∃ γ, GoodHeight X₀ κ f Γ γ then
    (if GoodHeight X₀ κ f Γ (sInf {γ | GoodHeight X₀ κ f Γ γ}) then
      sInf {γ | GoodHeight X₀ κ f Γ γ} else h.choose)
  else Γ

/-- The chosen height satisfies the choice rule of Lemma 4.8. -/
theorem chooseHeight_rule (X₀ : ℕ) (κ : ℝ) (f : ℂ → ℂ) (Γ : ℝ) :
    ChoiceRule X₀ κ f Γ (chooseHeight X₀ κ f Γ) := by
  intro h
  unfold chooseHeight
  rw [dif_pos h]
  split_ifs with h'
  · exact h'
  · exact h.choose_spec

/-- The chosen height lies in `[Γ, 2Γ]` (for `Γ ≥ 0`). -/
theorem chooseHeight_mem (X₀ : ℕ) (κ : ℝ) (f : ℂ → ℂ) {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    chooseHeight X₀ κ f Γ ∈ Icc Γ (2 * Γ) := by
  unfold chooseHeight
  split_ifs with h h'
  · exact h'.1
  · exact h.choose_spec.1
  · exact ⟨le_rfl, by linarith⟩

lemma heightScale_eq {θ κ₀ x : ℝ} :
    2 * heightScale θ κ₀ x = κ₀ * x ^ (1 - θ) / Real.log x := by
  unfold heightScale; rw [mul_comm 2 (Real.log x), ← div_div]; ring

/-- `1 ≤ α ≤ 2` and `α γ = κ₀ x^{1-θ}/log x` for every `γ ∈ [Γ, 2Γ]`, `Γ > 0`. -/
theorem amplitudeOf_mem {θ κ₀ γ x : ℝ} (hΓ : 0 < heightScale θ κ₀ x)
    (hγ : γ ∈ Icc (heightScale θ κ₀ x) (2 * heightScale θ κ₀ x)) :
    1 ≤ amplitudeOf θ κ₀ γ x ∧ amplitudeOf θ κ₀ γ x ≤ 2 ∧
      amplitudeOf θ κ₀ γ x * γ = κ₀ * x ^ (1 - θ) / Real.log x := by
  have hγ0 : 0 < γ := lt_of_lt_of_le hΓ hγ.1
  have hK := heightScale_eq (θ := θ) (κ₀ := κ₀) (x := x)
  unfold amplitudeOf
  rw [← hK]
  refine ⟨?_, ?_, by field_simp⟩
  · rw [le_div_iff₀ hγ0]; linarith [hγ.2]
  · rw [div_le_iff₀ hγ0]; linarith [hγ.1]

/-- `2Γ(x) ≤ x` when `κ₀ ≤ 1/4`, `0 ≤ θ`, `x > 1` and `log x ≥ 1`. -/
lemma two_heightScale_le {θ κ₀ x : ℝ} (hθ : 0 ≤ θ) (hκ0 : 0 ≤ κ₀) (hκ : κ₀ ≤ 1 / 4)
    (hx : 1 < x) (hL : 1 ≤ Real.log x) : 2 * heightScale θ κ₀ x ≤ x := by
  have hx1 : 1 ≤ x := hx.le
  rw [heightScale_eq]
  have hxθ : x ^ (1 - θ) ≤ x := by
    calc x ^ (1 - θ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hxθ0 : 0 ≤ x ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The design parameters**: for `θ ∈ [1/20, 1/2]`, `Λ ≥ 10`, `e^{-Λ} ≤ κ₀ ≤ 1/4`, `x > 1`
with `log log x ≥ 2Λ`, `Γ(x) ≥ 2` and any `γ ∈ [Γ(x), 2Γ(x)]`, the amplitude `α = amplitudeOf`
satisfies `DesignParams`, `1 ≤ α ≤ 2`, and `γ ≤ x`. -/
theorem designParams_of_mem {θ Λ κ₀ γ x : ℝ} (hθ1 : 1 / 20 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hΛ : 10 ≤ Λ) (hκ1 : Real.exp (-Λ) ≤ κ₀) (hκ2 : κ₀ ≤ 1 / 4) (hx : 1 < x)
    (hLL : 2 * Λ ≤ Real.log (Real.log x)) (hΓ : 2 ≤ heightScale θ κ₀ x)
    (hγ : γ ∈ Icc (heightScale θ κ₀ x) (2 * heightScale θ κ₀ x)) :
    DesignParams θ Λ κ₀ (amplitudeOf θ κ₀ γ x) γ x ∧
      1 ≤ amplitudeOf θ κ₀ γ x ∧ amplitudeOf θ κ₀ γ x ≤ 2 ∧ γ ≤ x := by
  obtain ⟨h1, h2, h3⟩ := amplitudeOf_mem (by linarith) hγ
  have hκ0 : 0 ≤ κ₀ := le_trans (Real.exp_pos _).le hκ1
  have hL : 1 ≤ Real.log x := by
    have hL0 : 0 < Real.log x := Real.log_pos hx
    by_contra h; push_neg at h
    have : Real.log (Real.log x) ≤ 0 := Real.log_nonpos hL0.le h.le
    linarith
  refine ⟨⟨hθ1, hθ2, hΛ, hκ1, hκ2, hx, hLL, by linarith, by linarith [hγ.1], h3⟩, h1, h2, ?_⟩
  exact hγ.2.trans (two_heightScale_le (by linarith) hκ0 hκ2 hx hL)

/-- `log L < 2 √L` for `L > 0`. -/
lemma log_lt_two_sqrt {L : ℝ} (hL : 0 < L) : Real.log L < 2 * Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h1 : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [← Real.log_rpow hs]; norm_num [Real.sq_sqrt hL.le]
  have h2 : Real.log (Real.sqrt L) < Real.sqrt L := by
    have := Real.log_le_sub_one_of_pos hs; linarith
  linarith

/-- **The absorbed-set growth from a uniform condition**: if `42 log(2 + ℓ) + 5 ≤ ς(ℓ)` for all
`ℓ ≥ 0`, then `δ ℓ + 2 log(2 + ℓ) + 5 ≤ ς(ℓ)` for `0 ≤ ℓ ≤ log(γ + 1)/(1 - θ/2)`, where
`δ = designRadius x`, `0 ≤ γ ≤ x`, `x > 1`, `θ ≤ 1/2` and `log log x ≥ 1`. -/
theorem growth_of_uniform {ς : ℝ → ℝ} (hς : ∀ ℓ, 0 ≤ ℓ → 42 * Real.log (2 + ℓ) + 5 ≤ ς ℓ)
    {θ γ x : ℝ} (hθ : θ ≤ 1 / 2) (hγ0 : 0 ≤ γ) (hγ : γ ≤ x) (hx : 1 < x)
    (hLL : 1 ≤ Real.log (Real.log x)) :
    ∀ ℓ ∈ Icc 0 (Real.log (γ + 1) / (1 - thetaB θ)),
      designRadius x * ℓ + 2 * Real.log (2 + ℓ) + 5 ≤ ς ℓ := by
  intro ℓ hℓ
  set L := Real.log x with hLdef
  have hL0 : 0 < L := Real.log_pos hx
  have hL1 : 2 ≤ L := by
    have : Real.exp 1 ≤ L := by rw [← Real.exp_log hL0]; exact Real.exp_le_exp.mpr hLL
    linarith [Real.exp_one_gt_d9]
  have hx0 : 0 < x := by linarith
  -- `ℓ ≤ 2L`
  have hℓ2 : ℓ ≤ 2 * L := by
    have h1 : Real.log (γ + 1) ≤ L + 1 := by
      calc Real.log (γ + 1) ≤ Real.log (2 * x) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) hx0.ne']
        _ ≤ 1 + L := by linarith [Real.log_two_lt_d9]
        _ = L + 1 := by ring
    have hb := thetaB_le_quarter hθ
    have h2 : ℓ * (1 - thetaB θ) ≤ Real.log (γ + 1) :=
      (le_div_iff₀ (by linarith)).mp hℓ.2
    nlinarith [hℓ.1, mul_nonneg hℓ.1 (show 0 ≤ 1 / 4 - thetaB θ by linarith)]
  have hℓ0 := hℓ.1
  have hLL0 : 0 ≤ Real.log L := by linarith
  -- `δ ℓ ≤ 40 log(2 + ℓ)`
  have key : designRadius x * ℓ ≤ 40 * Real.log (2 + ℓ) := by
    unfold designRadius
    rw [← hLdef, div_mul_eq_mul_div, div_le_iff₀ hL0]
    have hsL := Real.sqrt_pos.mpr hL0
    have hsq := Real.sq_sqrt hL0.le
    have hlog2 := Real.log_two_gt_d9
    have hmono : Real.log 2 ≤ Real.log (2 + ℓ) := Real.log_le_log (by norm_num) (by linarith)
    rcases le_or_gt ℓ (Real.sqrt L) with h | h
    · -- small `ℓ`: `9 log L · ℓ ≤ 9 log L √L < 18 L ≤ 40 log 2 · L`
      have h3 := log_lt_two_sqrt hL0
      have : 9 * Real.log L * ℓ ≤ 9 * Real.log L * Real.sqrt L :=
        mul_le_mul_of_nonneg_left h (by positivity)
      nlinarith
    · -- large `ℓ`: `log(2 + ℓ) ≥ log √L = log L / 2`
      have h3 : Real.log L / 2 ≤ Real.log (2 + ℓ) := by
        have : Real.log (Real.sqrt L) ≤ Real.log (2 + ℓ) :=
          Real.log_le_log hsL (by linarith)
        rw [Real.log_sqrt hL0.le] at this; exact this
      have : 9 * Real.log L * ℓ ≤ 9 * Real.log L * (2 * L) :=
        mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      nlinarith
  linarith [hς ℓ hℓ0]

/-- The height `γ_k` chosen by the rule of Lemma 4.8 in `[Γ_k, 2Γ_k]`,
`Γ_k = heightScale θ κ₀ x⁺_k`, for `f = D̂_{<a_k}`. -/
noncomputable def designGamma (X₀ : ℕ) (κ θ κ₀ : ℝ) (Dlt : ℕ → ℂ → ℂ) (xp : ℕ → ℝ) (k : ℕ) : ℝ :=
  chooseHeight X₀ κ (Dlt k) (heightScale θ κ₀ (xp k))

/-- The amplitude `α_k = amplitudeOf θ κ₀ γ_k x⁺_k` for the chosen height `γ_k`. -/
noncomputable def designAlpha (X₀ : ℕ) (κ θ κ₀ : ℝ) (Dlt : ℕ → ℂ → ℂ) (xp : ℕ → ℝ) (k : ℕ) : ℝ :=
  amplitudeOf θ κ₀ (designGamma X₀ κ θ κ₀ Dlt xp k) (xp k)

/-- **The inputs of Theorem 4.10 with the heights, amplitudes and growth condition designed**: as
`Theorem410InputsCount`, but `γ_k` is chosen by the rule of Lemma 4.8 in `[Γ_k, 2Γ_k]` with
`Γ_k = κ₀ (x⁺_k)^{1-θ}/(2 log x⁺_k)`, `α_k = κ₀ (x⁺_k)^{1-θ}/(γ_k log x⁺_k)`, and the
absorbed-set growth is the single condition `42 log(2 + ℓ) + 5 ≤ ς(ℓ)` for `ℓ ≥ 0`. The remaining
conditions on the design are `θ ∈ [1/20, 1/2]`, `1/X₀ ≤ κ₀ ≤ 1/4`, `x⁺_k > 1`,
`log log x⁺_k ≥ 2 log X₀`, `Γ_k ≥ T + 1/2`, `κ Γ_k ≥ e^{X₀²/3}`. -/
def Theorem410InputsDesign (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ T κ₀ η : ℝ) (xp a : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℝ) (u : ℝ → ℝ) (ς : ℝ → ℝ),
    10 ^ 4 ≤ Real.log X₀ ∧ 1 / 20 ≤ θ ∧ θ ≤ 1 / 2 ∧ 0 < κ ∧ κ ≤ 1 ∧
    Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (∀ k, 1 < xp k) ∧ (∀ k, 2 * Real.log X₀ ≤ Real.log (Real.log (xp k))) ∧
    (∀ k, T + 1 / 2 ≤ heightScale θ κ₀ (xp k)) ∧
    (∀ k, Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * heightScale θ κ₀ (xp k)) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (Dlt k)) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (thetaB θ) A u ∧ Monotone ς ∧
    (∀ x ≥ 1, countA A x ≤ x * Real.exp (-ς (Real.log x))) ∧
    (∀ ℓ, 0 ≤ ℓ → 42 * Real.log (2 + ℓ) + 5 ≤ ς ℓ) ∧
    (∀ k, ∀ s ∈ closedBall (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s +
        (∑' j, oscHat θ (designAlpha X₀ κ θ κ₀ Dlt xp j) (designGamma X₀ κ θ κ₀ Dlt xp j)
          (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (thetaB θ) A u s)

/-- The designed inputs give `Theorem410InputsCount`: the design parameters, the choice rule and
the absorbed-set growth for every `k` are derived. -/
theorem Theorem410InputsDesign.toCount {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsDesign θ F) :
    Theorem410InputsCount θ F := by
  obtain ⟨X₀, κ, T, κ₀, η, xp, a, D, Dlt, A, u, ς, hX, hθ1, hθ2, hκ, hκ1, hT, hκ₀1, hκ₀2,
    hx1, hLL, hΓT, hΓ, hDd, hpieces, hsp, hη0, hη, ha, hD, hA, hς, hN, hgrowth, hdec⟩ := h
  -- `X₀ ≥ 2`, hence `T ≥ 7/3` and `Γ_k ≥ 2`
  have hX2 : (2 : ℝ) ≤ X₀ := by
    rcases Nat.lt_or_ge X₀ 2 with h | h
    · interval_cases X₀ <;> norm_num at hX
    · exact_mod_cast h
  have hT2 : 7 / 3 ≤ T := by
    have h1 : (X₀ : ℝ) ^ 2 / 3 + 1 ≤ Real.exp ((X₀ : ℝ) ^ 2 / 3) := Real.add_one_le_exp _
    have h2 : κ * T ≤ T := by
      have : 0 < T := by
        by_contra hT0; push_neg at hT0
        have : κ * T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ.le hT0
        linarith [Real.exp_pos ((X₀ : ℝ) ^ 2 / 3)]
      nlinarith
    nlinarith
  have hΛ : (10 : ℝ) ≤ Real.log X₀ := by linarith
  have hmem : ∀ k, designGamma X₀ κ θ κ₀ Dlt xp k ∈
      Icc (heightScale θ κ₀ (xp k)) (2 * heightScale θ κ₀ (xp k)) := fun k =>
    chooseHeight_mem X₀ κ (Dlt k) (by linarith [hΓT k])
  have hdp := fun k => designParams_of_mem hθ1 hθ2 hΛ hκ₀1 hκ₀2 (hx1 k) (hLL k)
    (by linarith [hΓT k]) (hmem k)
  refine ⟨X₀, κ, T, κ₀, η, designAlpha X₀ κ θ κ₀ Dlt xp, designGamma X₀ κ θ κ₀ Dlt xp, xp, a,
    fun k => heightScale θ κ₀ (xp k), D, Dlt, A, u, ς, hX, hκ, hκ1, hT, fun k => (hdp k).1,
    fun k => le_trans (hΓT k) (hmem k).1, hΓ, hDd, hpieces,
    fun k => chooseHeight_rule X₀ κ (Dlt k) _, fun k => ⟨(hdp k).2.1, (hdp k).2.2.1⟩, hsp,
    fun k => (hdp k).2.2.2, hη0, hη, ha, hD, hA, hς, hN, ?_, hdec⟩
  intro k
  exact growth_of_uniform hgrowth hθ2 (by linarith [(hmem k).1, hΓT k]) (hdp k).2.2.2 (hx1 k)
    (by linarith [hLL k])

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system: `PartIInputsQueue75` and `Theorem410InputsDesign`. -/
def TheoremAInputsDesign (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsQueue75 θ X₀ P ∧ Theorem410InputsDesign θ (P.zetaCont 1)

/-- **Theorem 2.1, refined hypothesis**: as `Theorem21InputsCount`, with the inputs of
Theorem 4.10 as in `Theorem410InputsDesign`. -/
def Theorem21InputsDesign : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsDesign θ X₀ (P ω)

theorem theorem21InputsCount_of_design (h : Theorem21InputsDesign) : Theorem21InputsCount := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ⟨(hP ω hω).1, (hP ω hω).2.toCount⟩⟩

/-- The refined hypothesis `Theorem21InputsDesign` implies Theorem 2.1. -/
theorem theorem21_of_design (h : Theorem21InputsDesign) : Theorem21 :=
  theorem21_of_count (theorem21InputsCount_of_design h)

/-- **Corollary 2.2** from the refined hypothesis `Theorem21InputsDesign`. -/
theorem corollary_2_2_of_design (h : Theorem21InputsDesign) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_design h)
