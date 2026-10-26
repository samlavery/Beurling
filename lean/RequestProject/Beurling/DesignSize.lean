module

public import RequestProject.Beurling.SlotModel

/-!
# The size conditions on `κ₀` and `x⁺_k` from one condition on the first switch-on point
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation Absorbed BaseFactor
  DesignedZero Target RankinMinorant GoodHeights

namespace DesignSize

/-- `e^y ≥ y⁵/120` for `y ≥ 0`. -/
lemma pow_five_div_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 5 / 120 ≤ Real.exp y := by
  have := Real.sum_le_exp_of_nonneg hy 6
  simp [Finset.sum_range_succ, Nat.factorial] at this
  nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4]

/-- **The size conditions at one switch-on point** (the computation behind (20) in the proof of
Lemma 4.8(ii)). For `X₀ ≥ 0` with `log X₀ ≥ 10⁸`, `θ ≤ 1/2`, `X₀⁻¹ ≤ κ ≤ 1`, `κ₀ ≥ X₀⁻¹` and
`x > 0` with `log x ≥ X₀²`: `x > 1`, `log log x ≥ 2 log X₀`, and
`e^{X₀²/3}/κ + 1/2 ≤ Γ(x) = κ₀ x^{1-θ}/(2 (log x)³)`. -/
theorem size_of_log_ge {X₀ θ κ κ₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hθ2 : θ ≤ 1 / 2) (hκ : Real.exp (-Real.log X₀) ≤ κ) (hκ1 : κ ≤ 1)
    (hκ₀ : Real.exp (-Real.log X₀) ≤ κ₀) (hx0 : 0 < x) (hx : X₀ ^ 2 ≤ Real.log x) :
    1 < x ∧ 2 * Real.log X₀ ≤ Real.log (Real.log x) ∧
      Real.exp (X₀ ^ 2 / 3) / κ + 1 / 2 ≤ heightScale θ κ₀ x := by
  have hX0p : 0 < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  have hlogX : Real.log X₀ ≤ X₀ := by
    have := Real.log_le_sub_one_of_pos hX0p; linarith
  have hXbig : 10 ^ 8 ≤ X₀ := hX.trans hlogX
  have hinv : Real.exp (-Real.log X₀) = 1 / X₀ := by
    rw [Real.exp_neg, Real.exp_log hX0p, one_div]
  rw [hinv] at hκ hκ₀
  have hκp : 0 < κ := lt_of_lt_of_le (by positivity) hκ
  set L := Real.log x with hLdef
  have hLbig : 2799360 ≤ L := by nlinarith
  have hLpos : 0 < L := by linarith
  have hx1 : 1 < x := (Real.log_pos_iff hx0.le).mp hLpos
  refine ⟨hx1, ?_, ?_⟩
  · have h1 : Real.log (X₀ ^ 2) ≤ Real.log L := Real.log_le_log (by positivity) hx
    rw [Real.log_pow] at h1
    push_cast at h1; linarith
  · have hxr : Real.exp (L / 2) ≤ x ^ (1 - θ) := by
      rw [Real.rpow_def_of_pos hx0, ← hLdef]
      apply Real.exp_le_exp.mpr; nlinarith
    have hsplit : Real.exp (L / 2) = Real.exp (L / 6) * Real.exp (L / 3) := by
      rw [← Real.exp_add]; ring_nf
    have hf1 : 3 * L ^ 4 ≤ Real.exp (L / 6) := by
      have := pow_five_div_le_exp (y := L / 6) (by linarith)
      have h3 : 3 * L ^ 4 ≤ (L / 6) ^ 5 / 120 := by
        have : (L / 6) ^ 5 / 120 = L ^ 4 * (L / 933120) := by ring
        rw [this]
        have : 3 ≤ L / 933120 := by linarith
        nlinarith [pow_pos hLpos 4]
      linarith
    have hf2 : Real.exp (X₀ ^ 2 / 3) ≤ Real.exp (L / 3) := Real.exp_le_exp.mpr (by linarith)
    set E := Real.exp (X₀ ^ 2 / 3) / κ with hE
    have hE1 : 1 ≤ E := by
      rw [hE, le_div_iff₀ hκp]
      have := Real.one_le_exp (show 0 ≤ X₀ ^ 2 / 3 by positivity); linarith
    have hEle : E ≤ X₀ * Real.exp (X₀ ^ 2 / 3) := by
      rw [hE, div_le_iff₀ hκp]
      have h1 : 1 ≤ X₀ * κ := by rw [div_le_iff₀ hX0p] at hκ; linarith
      nlinarith [Real.exp_pos (X₀ ^ 2 / 3)]
    have hX2L : X₀ ^ 2 ≤ L := hx
    have hprod : 3 * L ^ 3 * X₀ * E ≤ Real.exp (L / 2) := by
      rw [hsplit]
      have hL30 : 0 ≤ L ^ 3 := by positivity
      calc 3 * L ^ 3 * X₀ * E ≤ 3 * L ^ 3 * X₀ * (X₀ * Real.exp (X₀ ^ 2 / 3)) := by gcongr
        _ = (3 * L ^ 3 * X₀ ^ 2) * Real.exp (X₀ ^ 2 / 3) := by ring
        _ ≤ (3 * L ^ 4) * Real.exp (L / 3) := by
          have h4 : 3 * L ^ 3 * X₀ ^ 2 ≤ 3 * L ^ 4 := by
            calc 3 * L ^ 3 * X₀ ^ 2 ≤ 3 * L ^ 3 * L := by gcongr
              _ = 3 * L ^ 4 := by ring
          exact mul_le_mul h4 hf2 (by positivity) (by positivity)
        _ ≤ Real.exp (L / 6) * Real.exp (L / 3) := by gcongr
    unfold heightScale
    rw [← hLdef, le_div_iff₀ (by positivity)]
    have hL30 : 0 < L ^ 3 := by positivity
    calc (E + 1 / 2) * (2 * L ^ 3) ≤ 3 * L ^ 3 * E := by nlinarith
      _ = (1 / X₀) * (3 * L ^ 3 * X₀ * E) := by field_simp
      _ ≤ κ₀ * x ^ (1 - θ) := by
        apply mul_le_mul hκ₀ (hprod.trans hxr) (by positivity)
          (le_trans (by positivity) hκ₀)

/-- The switch-on points increase: `x⁺_0 ≤ x⁺_k` when `exp(x⁺_k) ≤ x⁺_{k+1}`. -/
lemma xp_ge_zero {xp : ℕ → ℝ} (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) (k : ℕ) :
    xp 0 ≤ xp k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => linarith [Real.add_one_le_exp (xp k), hsp k]

end DesignSize

open DesignSize

/-- **The inputs of Theorem 4.10 with the paper's switch-on condition.** As
`Theorem410InputsRankin`, except that the auxiliary height `T` and the size conditions
`e^{X₀²/3} ≤ κT`, `x⁺_k > 1`, `log log x⁺_k ≥ 2 log X₀`, `Γ_k ≥ T + 1/2` and
`κ Γ_k ≥ e^{X₀²/3}` (for every `k`) are replaced by the parameter choices of Section 2.2:

* the first switch-on point satisfies `log x⁺_0 ≥ X₀²` ("switch-on: `x₁ ≥ exp(X₀²)`"; the later
  points follow from the spacing `x⁺_{k+1} ≥ exp(x⁺_k)`, already an input);
* `κ ≥ X₀⁻¹` (the paper's `κ = X₀^{-5/12+2ε_κ}` satisfies this);
* `κ₀ ∈ [X₀⁻¹, 1/4]`, as before. -/
def Theorem410InputsSize (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (X₀ : ℕ) (κ κ₀ η : ℝ) (xp a : ℕ → ℝ) (D : ℝ → ℝ) (Dlt : ℕ → ℂ → ℂ)
    (A : Set ℕ) (u : ℕ → ℝ),
    10 ^ 8 ≤ Real.log X₀ ∧ 1 / 4 ≤ θ ∧ θ ≤ 1 / 2 ∧
    Real.exp (-Real.log X₀) ≤ κ ∧ κ ≤ 1 ∧
    Real.exp (-Real.log X₀) ≤ κ₀ ∧ κ₀ ≤ 1 / 4 ∧
    (X₀ : ℝ) ^ 2 ≤ Real.log (xp 0) ∧
    (∀ k, Differentiable ℂ (Dlt k)) ∧
    (∀ k, Lemma48PiecesCount X₀ (heightScale θ κ₀ (xp k)) (Dlt k)) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    AbsorbedHyp (θ / 2) A u ∧
    (∀ x ≥ (1 : ℝ), Real.log x ≤ Real.log X₀ ^ 2 → countA A x = 0) ∧
    (∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      countA A x ≤ x * Real.exp (-sigmaStar (Real.log X₀) (Real.log x))) ∧
    (∀ k, ∀ s ∈ closedBall (1 + designGamma X₀ κ θ κ₀ Dlt xp k * I) (designRadius (xp k)),
      F s = ZBcont X₀ κ s +
        (∑' j, oscHat θ (designAlpha X₀ κ θ κ₀ Dlt xp j) (designGamma X₀ κ θ κ₀ Dlt xp j)
          (xp j) s) +
        (Dlt k s + lateNoise D (a k) s) + absorbedHat (θ / 2) A u s)

/-- **The size conditions are derived**: `Theorem410InputsSize` gives `Theorem410InputsRankin`,
with `T := e^{X₀²/3}/κ`. -/
theorem Theorem410InputsSize.toRankin {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsSize θ F) :
    Theorem410InputsRankin θ F := by
  obtain ⟨X₀, κ, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκ, hκ1, hκ₀1, hκ₀2, hxp0, hDd,
    hpieces, hsp, hη0, hη, ha, hD, hA, hempty, hbound, hdec⟩ := h
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hκp : 0 < κ := lt_of_lt_of_le (Real.exp_pos _) hκ
  have hsize : ∀ k, 1 < xp k ∧ 2 * Real.log X₀ ≤ Real.log (Real.log (xp k)) ∧
      Real.exp ((X₀ : ℝ) ^ 2 / 3) / κ + 1 / 2 ≤ heightScale θ κ₀ (xp k) := by
    intro k
    have hpos : 0 < xp k := lt_of_lt_of_le (ha k).1 (ha k).2.1
    have h0 : 0 < xp 0 := lt_of_lt_of_le (ha 0).1 (ha 0).2.1
    have hlog : (X₀ : ℝ) ^ 2 ≤ Real.log (xp k) :=
      hxp0.trans (Real.log_le_log h0 (xp_ge_zero hsp k))
    exact size_of_log_ge hX0 hX hθ2 hκ hκ1 hκ₀1 hpos hlog
  set T := Real.exp ((X₀ : ℝ) ^ 2 / 3) / κ with hT
  have hκT : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T := by
    rw [hT, mul_div_cancel₀ _ hκp.ne']
  refine ⟨X₀, κ, T, κ₀, η, xp, a, D, Dlt, A, u, hX, hθ1, hθ2, hκp, hκ1, hκT, hκ₀1, hκ₀2,
    fun k => (hsize k).1, fun k => (hsize k).2.1, fun k => (hsize k).2.2, fun k => ?_, hDd,
    hpieces, hsp, hη0, hη, ha, hD, hA, hempty, hbound, hdec⟩
  have := (hsize k).2.2
  calc Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * T := hκT
    _ ≤ κ * heightScale θ κ₀ (xp k) := by
      apply mul_le_mul_of_nonneg_left _ hκp.le; linarith


end
