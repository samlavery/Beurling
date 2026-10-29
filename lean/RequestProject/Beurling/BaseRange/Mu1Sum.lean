module

public import RequestProject.Beurling.BaseRange.Blin
public import RequestProject.BSCert.Consts.MarginCert

/-!
# Lemma 7.3(c): from the pointwise bounds to the dyadic sum (87) (`eq:mu1sum`)

Lemma 7.3(c) bounds the Huxley-error part `μ₁` pointwise, with `Λ = log X₀`, `v = log x/Λ` and
`U = 1 + 2 log v`:

  `|μ₁(x)| ≤ 2Λ⁻³ (log v + 1.01)` for `x ≥ X₀`, and for `v ≥ 4`
  `|μ₁(x)| ≤ 2 [(U/log x)³ (log U + 1.01) + 2e^γ e^{Ein(2)} (v/U) v⁻⁴ Λ⁻³]`,

and concludes (87): `∑_{u dyadic ≥ X₀} log(2u) sup_{[u,2u]} |μ₁| ≤ 690/log X₀ ≤ 7·10⁻⁶`.

`Mu1Pointwise X₀ μ₁` is the pair of pointwise bounds (for an arbitrary function `μ₁`), and
`mu1sum` derives (87) from it, as the paper does: summing over the dyadic `u = 2ʲX₀`, with
`log(2u) ≤ 1.01 log u`, gives `(2.02/log 2) Λ⁻¹ (I₁ + I₂ + I₃)`, where `I₁, I₂, I₃` are the
certified integrals of `BSCert.Consts` (m2–m4). The comparison of the dyadic sums with the
integrals is done explicitly: the blocks `[u, 2u]` correspond to the cells
`[v_j, v_j + δ]`, `v_j = 1 + jδ`, `δ = log 2/Λ`, and

* for `v_j < 4` (first bound):
  `δ v_j (log(v_j + δ) + 1.01) ≤ ∫_{v_j}^{v_j+δ} (t(log t + 1.01) + δ)`;
* for `v_j ≥ 4` (second bound): the block supremum is at most `(1 + δ)⁶` times the integral of
  `f₂ + c₃ f₃` over the cell, because `U³(log U + 1.01)` is increasing and moves by a factor
  `≤ (1 + δ)⁴` across a cell.

The errors are `O(δ) = O(Λ⁻¹)` and fit in the slack of m5 (`688.99 ≤ 690`).
-/

@[expose] public section

open Real MeasureTheory Set Filter BSCert.Consts BSCert.EiFn

namespace BaseRange

/-- `c₃ = 2 e^γ e^{Ein(2)}`, the constant of the second bound of Lemma 7.3(c). -/
lemma c3_eq : c3 = 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) := rfl

/-- **The pointwise bounds of Lemma 7.3(c)** for a function `μ₁`, with `Λ = log X₀`,
`v = log x/Λ`, `U = Uf v = 1 + 2 log v`. -/
def Mu1Pointwise (X0 : ℝ) (μ1 : ℝ → ℝ) : Prop :=
  (∀ x, X0 ≤ x →
      |μ1 x| ≤ 2 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 1.01)) ∧
  (∀ x, X0 ≤ x → 4 ≤ Real.log x / Real.log X0 →
      |μ1 x| ≤ 2 * ((Uf (Real.log x / Real.log X0) / Real.log x) ^ 3 *
          (Real.log (Uf (Real.log x / Real.log X0)) + 1.01) +
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) *
          ((Real.log x / Real.log X0) / Uf (Real.log x / Real.log X0)) /
          (Real.log x / Real.log X0) ^ 4 / Real.log X0 ^ 3))

/-- The dyadic block suprema `sup_{[u, 2u]} |μ₁|`, `u = 2ʲ X₀`. -/
noncomputable def blockSup (X0 : ℝ) (μ1 : ℝ → ℝ) (j : ℕ) : ℝ :=
  sSup ((fun x => |μ1 x|) '' Icc (2 ^ j * X0) (2 * (2 ^ j * X0)))

/-- The dyadic term `log(2u) sup_{[u,2u]} |μ₁|`, `u = 2ʲ X₀`. -/
noncomputable def dyTerm (X0 : ℝ) (μ1 : ℝ → ℝ) (j : ℕ) : ℝ :=
  Real.log (2 * (2 ^ j * X0)) * blockSup X0 μ1 j

/-- `A(v) = U³ (log U + 1.01)`, the numerator of `f₂`. -/
noncomputable def Anum (v : ℝ) : ℝ := Uf v ^ 3 * (Real.log (Uf v) + 1.01)

/-- The integrand used for the cells below `4`: `t (log t + 1.01) + δ`. -/
noncomputable def GA (δ t : ℝ) : ℝ := t * (Real.log t + 1.01) + δ

/-- The integrand used for the cells above `4`: `f₂ + c₃ f₃`. -/
noncomputable def GB (t : ℝ) : ℝ := f2 t + c3 * f3 t

/-! ### Elementary facts -/

lemma Uf_ge_one {v : ℝ} (hv : 1 ≤ v) : 1 ≤ Uf v := by
  unfold Uf; have := Real.log_nonneg hv; linarith

lemma log_Uf_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ Real.log (Uf v) :=
  Real.log_nonneg (Uf_ge_one hv)

lemma Anum_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ Anum v := by
  have := Uf_ge_one hv; have := log_Uf_nonneg hv
  unfold Anum; positivity

lemma Anum_mono {v w : ℝ} (hv : 1 ≤ v) (hvw : v ≤ w) : Anum v ≤ Anum w := by
  have h1 := Uf_ge_one hv
  have h2 := Uf_mono (by linarith) hvw
  have h3 := log_Uf_nonneg hv
  have h4 : Real.log (Uf v) ≤ Real.log (Uf w) := Real.log_le_log (by linarith) h2
  unfold Anum
  apply mul_le_mul (pow_le_pow_left₀ (by linarith) h2 3) (by linarith) (by linarith)
    (pow_nonneg (by linarith) 3)

lemma c3_pos : 0 < c3 := by
  unfold c3; positivity

/-- Across a cell `[v, v + δ]`, `v ≥ 1`, `0 ≤ δ`, `A` moves by a factor at most `(1 + δ)⁴`. -/
lemma Uf_shift {v δ : ℝ} (hv : 2 ≤ v) (hδ : 0 ≤ δ) : Uf (v + δ) ≤ Uf v * (1 + δ) := by
  unfold Uf
  have h1 : Real.log (v + δ) ≤ Real.log v + δ / v := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < (v + δ) / v)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : (v + δ) / v - 1 = δ / v := by field_simp; ring
    linarith
  have h2 : δ / v ≤ δ / 2 := div_le_div_of_nonneg_left hδ (by norm_num) hv
  have h3 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  nlinarith

lemma Anum_shift {v δ : ℝ} (hv2 : 2 ≤ v) (hδ : 0 ≤ δ) :
    Anum (v + δ) ≤ (1 + δ) ^ 4 * Anum v := by
  have hv : 1 ≤ v := by linarith
  have hU := Uf_ge_one hv
  have hl := log_Uf_nonneg hv
  have hUs : Uf (v + δ) ≤ Uf v * (1 + δ) := Uf_shift hv2 hδ
  have hU1 := Uf_ge_one (by linarith : 1 ≤ v + δ)
  have hlog : Real.log (Uf (v + δ)) ≤ Real.log (Uf v) + δ := by
    have := Real.log_le_log (by linarith) hUs
    rw [Real.log_mul (by linarith) (by linarith)] at this
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + δ)
    linarith
  have hl1 := log_Uf_nonneg (by linarith : 1 ≤ v + δ)
  unfold Anum
  have hp3 : Uf (v + δ) ^ 3 ≤ (Uf v * (1 + δ)) ^ 3 := pow_le_pow_left₀ (by linarith) hUs 3
  have hlg : Real.log (Uf (v + δ)) + 1.01 ≤ (1 + δ) * (Real.log (Uf v) + 1.01) := by nlinarith
  calc Uf (v + δ) ^ 3 * (Real.log (Uf (v + δ)) + 1.01)
      ≤ (Uf v * (1 + δ)) ^ 3 * ((1 + δ) * (Real.log (Uf v) + 1.01)) :=
        mul_le_mul hp3 hlg (by linarith) (by positivity)
    _ = (1 + δ) ^ 4 * (Uf v ^ 3 * (Real.log (Uf v) + 1.01)) := by ring

lemma f2_eq (v : ℝ) : f2 v = Anum v / v ^ 2 := rfl

/-! ### The cell comparisons -/

lemma continuousOn_GA (δ : ℝ) : ContinuousOn (GA δ) (Ici 1) := by
  have : ContinuousOn Real.log (Ici (1 : ℝ)) :=
    Real.continuousOn_log.mono fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]; have : (1 : ℝ) ≤ t := ht; linarith
  unfold GA; fun_prop

lemma intervalIntegrable_GA (δ : ℝ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (GA δ) volume a b :=
  ((continuousOn_GA δ).mono (Icc_subset_Ici_iff hab |>.mpr ha)).intervalIntegrable_of_Icc hab

lemma continuousOn_GB : ContinuousOn GB (Ici 1) := by
  unfold GB
  exact continuousOn_f2.add (continuousOn_const.mul continuousOn_f3)

lemma intervalIntegrable_GB {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable GB volume a b :=
  (continuousOn_GB.mono (Icc_subset_Ici_iff hab |>.mpr ha)).intervalIntegrable_of_Icc hab

lemma GB_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ GB t := by
  have := f2_nonneg ht; have := f3_nonneg ht; have := c3_pos
  unfold GB; positivity

/-- Cells below `4`: `δ v (log(v + δ) + 1.01) ≤ ∫_v^{v+δ} GA δ`. -/
lemma cellA {v δ : ℝ} (hv : 1 ≤ v) (hδ : 0 < δ) :
    δ * (v * (Real.log (v + δ) + 1.01)) ≤ ∫ t in v..v + δ, GA δ t := by
  have hc : δ * (v * (Real.log (v + δ) + 1.01)) =
      ∫ _ in v..v + δ, v * (Real.log (v + δ) + 1.01) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hc]
  apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    (intervalIntegrable_GA δ hv (by linarith))
  intro t ht
  have ht1 : 1 ≤ t := hv.trans ht.1
  have ht0 : 0 < t := by linarith
  have h1 : Real.log (v + δ) ≤ Real.log (t + δ) :=
    Real.log_le_log (by linarith) (by linarith [ht.1])
  have h2 : Real.log (t + δ) ≤ Real.log t + δ / t := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < (t + δ) / t)
    rw [Real.log_div (by positivity) ht0.ne'] at this
    have e : (t + δ) / t - 1 = δ / t := by field_simp; ring
    linarith
  have h3 : 0 ≤ Real.log (v + δ) + 1.01 := by
    have := Real.log_nonneg (by linarith : 1 ≤ v + δ); linarith
  unfold GA
  have e : t * (Real.log t + δ / t + 1.01) = t * (Real.log t + 1.01) + δ := by field_simp; ring
  calc v * (Real.log (v + δ) + 1.01) ≤ t * (Real.log (v + δ) + 1.01) :=
        mul_le_mul_of_nonneg_right ht.1 h3
    _ ≤ t * (Real.log t + δ / t + 1.01) := by
        apply mul_le_mul_of_nonneg_left _ ht0.le; linarith
    _ = _ := e

/-- Cells above `4`: `δ (A(v + δ)/v² + c₃ f₃(v)) ≤ (1 + δ)⁶ ∫_v^{v+δ} (f₂ + c₃ f₃)`. -/
lemma cellB {v δ : ℝ} (hv2 : 2 ≤ v) (hδ : 0 < δ) :
    δ * (Anum (v + δ) / v ^ 2 + c3 * f3 v) ≤ (1 + δ) ^ 6 * ∫ t in v..v + δ, GB t := by
  have hv : 1 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hA := Anum_shift hv2 hδ.le
  have hA0 := Anum_nonneg hv
  have hU := Uf_ge_one hv
  have hc3 := c3_pos
  -- the lower bound of `GB` on the cell
  set m := Anum v / (v ^ 2 * (1 + δ) ^ 2) + c3 * f3 v / (1 + δ) ^ 3 with hm
  have hlow : ∀ t ∈ Icc v (v + δ), m ≤ GB t := by
    intro t ht
    have ht1 : 1 ≤ t := hv.trans ht.1
    have ht0 : 0 < t := by linarith
    have hsq : t ^ 2 ≤ v ^ 2 * (1 + δ) ^ 2 := by
      have : t ≤ v * (1 + δ) := by nlinarith [ht.2]
      calc t ^ 2 ≤ (v * (1 + δ)) ^ 2 := pow_le_pow_left₀ ht0.le this 2
        _ = v ^ 2 * (1 + δ) ^ 2 := by ring
    have h1 : Anum v / (v ^ 2 * (1 + δ) ^ 2) ≤ f2 t := by
      rw [f2_eq]
      calc Anum v / (v ^ 2 * (1 + δ) ^ 2) ≤ Anum v / t ^ 2 :=
            div_le_div_of_nonneg_left hA0 (by positivity) hsq
        _ ≤ Anum t / t ^ 2 := div_le_div_of_nonneg_right (Anum_mono hv ht.1) (by positivity)
    have hUt : Uf t ≤ Uf v * (1 + δ) := by
      have h := Uf_mono ht0 ht.2
      have := Uf_shift hv2 hδ.le
      linarith
    have h2 : f3 v / (1 + δ) ^ 3 ≤ f3 t := by
      unfold f3
      rw [div_div, one_div_le_one_div (by positivity) (by have := Uf_pos ht1; positivity)]
      have hUt0 : 0 < Uf t := Uf_pos ht1
      calc Uf t * t ^ 2 ≤ (Uf v * (1 + δ)) * (v ^ 2 * (1 + δ) ^ 2) :=
            mul_le_mul hUt hsq (by positivity) (by positivity)
        _ = Uf v * v ^ 2 * (1 + δ) ^ 3 := by ring
    unfold GB
    have : c3 * f3 v / (1 + δ) ^ 3 ≤ c3 * f3 t := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 hc3.le
    linarith
  have hint : δ * m ≤ ∫ t in v..v + δ, GB t := by
    have hc : δ * m = ∫ _ in v..v + δ, m := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hc]
    exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegrable_GB hv (by linarith)) hlow
  have hpos : (0 : ℝ) < (1 + δ) := by linarith
  have h1d : 1 ≤ 1 + δ := by linarith
  have hf3 : 0 ≤ f3 v := f3_nonneg hv
  -- `δ (A(v+δ)/v² + c₃ f₃ v) ≤ (1+δ)⁶ δ m`
  have key : Anum (v + δ) / v ^ 2 + c3 * f3 v ≤ (1 + δ) ^ 6 * m := by
    rw [hm, mul_add]
    have e1 : (1 + δ) ^ 6 * (Anum v / (v ^ 2 * (1 + δ) ^ 2)) = (1 + δ) ^ 4 * Anum v / v ^ 2 := by
      field_simp
    have e2 : (1 + δ) ^ 6 * (c3 * f3 v / (1 + δ) ^ 3) = (1 + δ) ^ 3 * (c3 * f3 v) := by
      field_simp
    rw [e1, e2]
    have h1 : Anum (v + δ) / v ^ 2 ≤ (1 + δ) ^ 4 * Anum v / v ^ 2 :=
      div_le_div_of_nonneg_right hA (by positivity)
    have h2 : c3 * f3 v ≤ (1 + δ) ^ 3 * (c3 * f3 v) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ h1d)
    linarith
  calc δ * (Anum (v + δ) / v ^ 2 + c3 * f3 v) ≤ δ * ((1 + δ) ^ 6 * m) :=
        mul_le_mul_of_nonneg_left key hδ.le
    _ = (1 + δ) ^ 6 * (δ * m) := by ring
    _ ≤ (1 + δ) ^ 6 * ∫ t in v..v + δ, GB t :=
        mul_le_mul_of_nonneg_left hint (by positivity)

/-! ### The blocks -/

section Blocks

variable {X0 : ℝ} {μ1 : ℝ → ℝ}

/-- `log(2ʲ X₀) = Λ v_j` with `v_j = 1 + jδ`, `δ = log 2/Λ`. -/
lemma log_block {j : ℕ} (hX0 : 0 < X0) (hΛ : 0 < Real.log X0) :
    Real.log (2 ^ j * X0) = Real.log X0 * (1 + j * (Real.log 2 / Real.log X0)) := by
  rw [Real.log_mul (by positivity) hX0.ne', Real.log_pow]
  field_simp
  ring

lemma blockSup_nonneg (j : ℕ) : 0 ≤ blockSup X0 μ1 j :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

lemma blockSup_le {j : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ x, 2 ^ j * X0 ≤ x → x ≤ 2 * (2 ^ j * X0) → |μ1 x| ≤ B) : blockSup X0 μ1 j ≤ B :=
  Real.sSup_le (fun _ ⟨x, hx, hx'⟩ => hx' ▸ h x hx.1 hx.2) hB0

/-- The position `v = log x/Λ` of a point of the block `j` lies in `[v_j, v_j + δ]`. -/
lemma v_mem_block {j : ℕ} (hX0 : 0 < X0) (hΛ : 0 < Real.log X0) {x : ℝ}
    (hx1 : 2 ^ j * X0 ≤ x) (hx2 : x ≤ 2 * (2 ^ j * X0)) :
    1 + j * (Real.log 2 / Real.log X0) ≤ Real.log x / Real.log X0 ∧
      Real.log x / Real.log X0 ≤
        1 + j * (Real.log 2 / Real.log X0) + Real.log 2 / Real.log X0 := by
  have hu : 0 < 2 ^ j * X0 := by positivity
  have h1 := Real.log_le_log hu hx1
  have h2 := Real.log_le_log (by linarith) hx2
  rw [Real.log_mul (by norm_num) hu.ne', log_block hX0 hΛ] at h2
  rw [log_block hX0 hΛ] at h1
  constructor
  · rw [le_div_iff₀ hΛ]; linarith
  · rw [div_le_iff₀ hΛ]
    have : (1 + j * (Real.log 2 / Real.log X0) + Real.log 2 / Real.log X0) * Real.log X0 =
        Real.log 2 + Real.log X0 * (1 + j * (Real.log 2 / Real.log X0)) := by
      field_simp; ring
    linarith

/-- `log(2u_j) ≤ 1.01 Λ v_j`. -/
lemma log_two_block_le {j : ℕ} (hX0 : 0 < X0) (hΛ : 10 ^ 8 ≤ Real.log X0) :
    Real.log (2 * (2 ^ j * X0)) ≤
      1.01 * Real.log X0 * (1 + j * (Real.log 2 / Real.log X0)) := by
  have hΛ0 : 0 < Real.log X0 := by linarith
  rw [Real.log_mul (by norm_num) (by positivity), log_block hX0 hΛ0]
  have hl2 := Real.log_two_lt_d9
  have hj : 0 ≤ (j : ℝ) * (Real.log 2 / Real.log X0) := by
    have := (Real.log_pos one_lt_two); positivity
  nlinarith

/-- Blocks with `v_j < 4`: `log(2u) sup |μ₁| ≤ (2.02/(Λ log 2)) δ v_j (log(v_j + δ) + 1.01)`. -/
lemma dyTerm_le_A (h : Mu1Pointwise X0 μ1) (hX0 : 0 < X0) (hΛ : 10 ^ 8 ≤ Real.log X0)
    (j : ℕ) :
    dyTerm X0 μ1 j ≤ 2.02 / (Real.log X0 * Real.log 2) * (Real.log 2 / Real.log X0) *
      ((1 + j * (Real.log 2 / Real.log X0)) *
        (Real.log (1 + j * (Real.log 2 / Real.log X0) + Real.log 2 / Real.log X0) + 1.01)) := by
  have hΛ0 : 0 < Real.log X0 := by linarith
  set δ := Real.log 2 / Real.log X0 with hδ
  have hδ0 : 0 < δ := div_pos (Real.log_pos one_lt_two) hΛ0
  set vj := 1 + j * δ with hvj
  have hvj1 : 1 ≤ vj := by have : 0 ≤ (j : ℝ) * δ := by positivity
                           linarith
  set B := 2 / Real.log X0 ^ 3 * (Real.log (vj + δ) + 1.01)
  have hB0 : 0 ≤ B := by
    have := Real.log_nonneg (by linarith : 1 ≤ vj + δ); positivity
  have hsup : blockSup X0 μ1 j ≤ B := by
    apply blockSup_le hB0
    intro x hx1 hx2
    have hxX : X0 ≤ x := by
      have : X0 ≤ 2 ^ j * X0 := le_mul_of_one_le_left hX0.le (one_le_pow₀ (by norm_num))
      linarith
    obtain ⟨hv1, hv2⟩ := v_mem_block hX0 hΛ0 hx1 hx2
    refine (h.1 x hxX).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := Real.log_le_log (by linarith) hv2
    linarith
  have hl := log_two_block_le (j := j) hX0 hΛ
  have hl0 : 0 ≤ Real.log (2 * (2 ^ j * X0)) := by
    apply Real.log_nonneg
    have : 1 ≤ X0 := by
      by_contra hc; push_neg at hc
      have := Real.log_nonpos hX0.le hc.le; linarith
    have : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  unfold dyTerm
  calc Real.log (2 * (2 ^ j * X0)) * blockSup X0 μ1 j
      ≤ Real.log (2 * (2 ^ j * X0)) * B := mul_le_mul_of_nonneg_left hsup hl0
    _ ≤ (1.01 * Real.log X0 * vj) * B := mul_le_mul_of_nonneg_right hl hB0
    _ = 2.02 / (Real.log X0 * Real.log 2) * δ * (vj * (Real.log (vj + δ) + 1.01)) := by
        simp only [B, hδ]
        have := (Real.log_pos one_lt_two)
        field_simp
        ring

/-- Blocks with `v_j ≥ 4`:
`log(2u) sup |μ₁| ≤ (2.02/(Λ log 2)) δ (A(v_j + δ)/v_j² + c₃ f₃(v_j))`. -/
lemma dyTerm_le_B (h : Mu1Pointwise X0 μ1) (hX0 : 0 < X0) (hΛ : 10 ^ 8 ≤ Real.log X0)
    (j : ℕ) (hj : 4 ≤ 1 + j * (Real.log 2 / Real.log X0)) :
    dyTerm X0 μ1 j ≤ 2.02 / (Real.log X0 * Real.log 2) * (Real.log 2 / Real.log X0) *
      (Anum (1 + j * (Real.log 2 / Real.log X0) + Real.log 2 / Real.log X0) /
          (1 + j * (Real.log 2 / Real.log X0)) ^ 2 +
        c3 * f3 (1 + j * (Real.log 2 / Real.log X0))) := by
  have hΛ0 : 0 < Real.log X0 := by linarith
  set Λ := Real.log X0 with hΛdef
  set δ := Real.log 2 / Λ with hδ
  have hδ0 : 0 < δ := div_pos (Real.log_pos one_lt_two) hΛ0
  set vj := 1 + j * δ with hvj
  have hvj0 : 0 < vj := by linarith
  have hUj := Uf_ge_one (by linarith : 1 ≤ vj)
  set B := 2 / Λ ^ 3 * (Anum (vj + δ) / vj ^ 3 + c3 / (Uf vj * vj ^ 3)) with hBdef
  have hB0 : 0 ≤ B := by
    have := Anum_nonneg (by linarith : 1 ≤ vj + δ); have := c3_pos; positivity
  have hsup : blockSup X0 μ1 j ≤ B := by
    apply blockSup_le hB0
    intro x hx1 hx2
    have hxX : X0 ≤ x := by
      have : X0 ≤ 2 ^ j * X0 := le_mul_of_one_le_left hX0.le (one_le_pow₀ (by norm_num))
      linarith
    obtain ⟨hv1, hv2⟩ := v_mem_block hX0 hΛ0 hx1 hx2
    set v := Real.log x / Λ with hv
    have hv4 : 4 ≤ v := hj.trans hv1
    have hv0 : 0 < v := by linarith
    have hlx : Real.log x = Λ * v := by rw [hv]; field_simp
    have key : |μ1 x| ≤ 2 * ((Uf v / Real.log x) ^ 3 * (Real.log (Uf v) + 1.01) +
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / Uf v) / v ^ 4 /
          Λ ^ 3) := h.2 x hxX hv4
    refine key.trans ?_
    rw [hlx]
    have hU := Uf_ge_one (by linarith : 1 ≤ v)
    have e : 2 * ((Uf v / (Λ * v)) ^ 3 * (Real.log (Uf v) + 1.01) +
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / Uf v) / v ^ 4 /
          Λ ^ 3) = 2 / Λ ^ 3 * (Anum v / v ^ 3 + c3 / (Uf v * v ^ 3)) := by
      rw [c3_eq]; unfold Anum; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : Anum v / v ^ 3 ≤ Anum (vj + δ) / vj ^ 3 := by
      calc Anum v / v ^ 3 ≤ Anum (vj + δ) / v ^ 3 :=
            div_le_div_of_nonneg_right (Anum_mono (by linarith) hv2) (by positivity)
        _ ≤ Anum (vj + δ) / vj ^ 3 :=
            div_le_div_of_nonneg_left (Anum_nonneg (by linarith)) (by positivity)
              (pow_le_pow_left₀ hvj0.le hv1 3)
    have h2 : c3 / (Uf v * v ^ 3) ≤ c3 / (Uf vj * vj ^ 3) := by
      apply div_le_div_of_nonneg_left c3_pos.le (by positivity)
      exact mul_le_mul (Uf_mono hvj0 hv1) (pow_le_pow_left₀ hvj0.le hv1 3) (by positivity)
        (by linarith)
    linarith
  have hl := log_two_block_le (j := j) hX0 hΛ
  have hl0 : 0 ≤ Real.log (2 * (2 ^ j * X0)) := by
    apply Real.log_nonneg
    have : 1 ≤ X0 := by
      by_contra hc; push_neg at hc
      have := Real.log_nonpos hX0.le hc.le; linarith
    have : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  unfold dyTerm
  calc Real.log (2 * (2 ^ j * X0)) * blockSup X0 μ1 j
      ≤ Real.log (2 * (2 ^ j * X0)) * B := mul_le_mul_of_nonneg_left hsup hl0
    _ ≤ (1.01 * Λ * vj) * B := mul_le_mul_of_nonneg_right hl hB0
    _ = 2.02 / (Λ * Real.log 2) * δ * (Anum (vj + δ) / vj ^ 2 + c3 * f3 vj) := by
        simp only [hBdef, hδ, f3]
        have := (Real.log_pos one_lt_two)
        field_simp
        ring

end Blocks

/-! ### The sum -/

lemma integral_GA_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10) :
    ∫ t in (1 : ℝ)..4 + δ, GA δ t ≤ I1 + 20 * δ := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_GA δ (a := 1) (b := 4) le_rfl (by norm_num))
    (intervalIntegrable_GA δ (a := 4) (b := 4 + δ) (by norm_num) (by linarith))
  rw [← hsplit]
  have h1 : ∫ t in (1 : ℝ)..4, GA δ t = I1 + 3 * δ := by
    unfold GA I1
    rw [intervalIntegral.integral_add _ intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    · ring
    · have : ContinuousOn (fun t : ℝ => t * (Real.log t + 1.01)) (Icc 1 4) := by
        have hl : ContinuousOn Real.log (Icc (1 : ℝ) 4) :=
          Real.continuousOn_log.mono fun t ht => by
            simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
        fun_prop
      exact this.intervalIntegrable_of_Icc (by norm_num)
  have h2 : ∫ t in (4 : ℝ)..4 + δ, GA δ t ≤ 17 * δ := by
    have hc : 17 * δ = ∫ _ in (4 : ℝ)..4 + δ, (17 : ℝ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hc]
    apply intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_GA δ (by norm_num) (by linarith)) intervalIntegrable_const
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
    have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
    unfold GA
    nlinarith [ht.2]
  linarith

theorem integral_GB_le (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, GB t ≤ I2 + I3 := by
  have hi2 := I2_le.1
  have hi3 := I3_le.1
  have hint : IntegrableOn GB (Ioi 4) := hi2.add (hi3.const_mul c3)
  rw [intervalIntegral.integral_of_le hab]
  have hsub : Ioc a b ⊆ Ioi 4 := fun t ht => lt_of_le_of_lt ha ht.1
  have h1 : ∫ t in Ioc a b, GB t ≤ ∫ t in Ioi 4, GB t := by
    apply setIntegral_mono_set hint
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      exact GB_nonneg (by have : (4 : ℝ) < t := ht; linarith)
    · exact Eventually.of_forall hsub
  refine h1.trans (le_of_eq ?_)
  unfold GB I2 I3
  rw [integral_add hi2 (hi3.const_mul c3), integral_const_mul]

/-- **(87)** (`eq:mu1sum`), finite form: under the pointwise bounds of Lemma 7.3(c), every
partial sum of `∑_{u = 2ʲX₀} log(2u) sup_{[u,2u]} |μ₁|` is at most `690/log X₀`. -/
theorem mu1sum_partial {X0 : ℝ} {μ1 : ℝ → ℝ} (h : Mu1Pointwise X0 μ1) (hX0 : 0 < X0)
    (hΛ : 10 ^ 8 ≤ Real.log X0) (J : ℕ) :
    ∑ j ∈ Finset.range J, dyTerm X0 μ1 j ≤ 690 / Real.log X0 := by
  have hΛ0 : 0 < Real.log X0 := by linarith
  set Λ := Real.log X0 with hΛdef
  set δ := Real.log 2 / Λ with hδ
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hδ0 : 0 < δ := div_pos (Real.log_pos one_lt_two) hΛ0
  have hδs : δ ≤ 1 / 10 ^ 8 := by
    rw [hδ, div_le_iff₀ hΛ0]
    have : (1 : ℝ) ≤ 1 / 10 ^ 8 * Λ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by norm_num)]; linarith
    linarith
  set v : ℕ → ℝ := fun j => 1 + j * δ with hv
  have hvs : ∀ j, v (j + 1) = v j + δ := fun j => by simp only [hv]; push_cast; ring
  have hv1 : ∀ j, 1 ≤ v j := fun j => by
    simp only [hv]; have : 0 ≤ (j : ℝ) * δ := by positivity
    linarith
  set C := 2.02 / (Λ * Real.log 2) with hC
  have hC0 : 0 < C := by positivity
  set K := ⌈3 / δ⌉₊ with hK
  set N := max J K with hN
  have hterm0 : ∀ j, 0 ≤ dyTerm X0 μ1 j := fun j => by
    unfold dyTerm
    apply mul_nonneg _ (blockSup_nonneg j)
    apply Real.log_nonneg
    have : 1 ≤ X0 := by
      by_contra hc; push_neg at hc
      have := Real.log_nonpos hX0.le hc.le; linarith
    have : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  -- reduce to `range N = range K ∪ Ico K N`
  have hJN : ∑ j ∈ Finset.range J, dyTerm X0 μ1 j ≤ ∑ j ∈ Finset.range N, dyTerm X0 μ1 j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (le_max_left _ _))
      fun j _ _ => hterm0 j
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right J K)] at hJN
  -- the cells below `4`
  have hA : ∑ j ∈ Finset.range K, dyTerm X0 μ1 j ≤ C * (I1 + 20 * δ) := by
    have h1 : ∀ j ∈ Finset.range K, dyTerm X0 μ1 j ≤ C * ∫ t in v j..v (j + 1), GA δ t := by
      intro j _
      refine (dyTerm_le_A h hX0 hΛ j).trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC0.le
      rw [hvs]
      exact cellA (hv1 j) hδ0
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => intervalIntegrable_GA δ (hv1 j) (by rw [hvs]; linarith))]
    have hvK : v K ≤ 4 + δ := by
      simp only [hv]
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 3 / δ)
      rw [← hK] at this
      have e : (3 / δ + 1) * δ = 3 + δ := by field_simp
      nlinarith
    have hv0 : v 0 = 1 := by simp [hv]
    rw [hv0]
    refine le_trans ?_ (integral_GA_le hδ0 (by linarith))
    apply intervalIntegral.integral_mono_interval le_rfl (hv1 K) hvK
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht1 : 1 ≤ t := le_of_lt ht.1
      have := Real.log_nonneg ht1
      unfold GA; positivity
    · exact intervalIntegrable_GA δ le_rfl (by linarith)
  -- the cells above `4`
  have hB : ∑ j ∈ Finset.Ico K N, dyTerm X0 μ1 j ≤ C * ((1 + δ) ^ 6 * (I2 + I3)) := by
    have h4 : ∀ j, K ≤ j → 4 ≤ v j := by
      intro j hj
      simp only [hv]
      have : 3 / δ ≤ (j : ℝ) := by
        have := Nat.ceil_le.mp (hK ▸ hj : ⌈3 / δ⌉₊ ≤ j); exact this
      have : 3 ≤ (j : ℝ) * δ := by rwa [div_le_iff₀ hδ0] at this
      linarith
    have h1 : ∀ j ∈ Finset.Ico K N,
        dyTerm X0 μ1 j ≤ C * ((1 + δ) ^ 6 * ∫ t in v j..v (j + 1), GB t) := by
      intro j hj
      refine (dyTerm_le_B h hX0 hΛ j (h4 j (Finset.mem_Ico.mp hj).1)).trans ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC0.le
      rw [hvs]
      exact cellB (by linarith [h4 j (Finset.mem_Ico.mp hj).1]) hδ0
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (le_max_right J K)
      (fun j _ => intervalIntegrable_GB (hv1 j) (by rw [hvs]; linarith))]
    apply integral_GB_le _ _ (h4 K le_rfl)
    simp only [hv]
    have : (K : ℝ) ≤ N := by exact_mod_cast le_max_right J K
    nlinarith
  -- the numerics
  have hI1 := I1_le
  have hI2 := I2_le.2
  have hI3 := I3_le.2
  have hpow : (1 + δ) ^ 6 ≤ 1 + 1 / 10 ^ 7 := by
    have h1 : (1 + δ) ^ 6 ≤ (1 + 1 / 10 ^ 8) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    refine h1.trans ?_
    norm_num
  have htot : C * (I1 + 20 * δ) + C * ((1 + δ) ^ 6 * (I2 + I3)) ≤ 690 / Λ := by
    rw [← mul_add, hC]
    have hb : I1 + 20 * δ + (1 + δ) ^ 6 * (I2 + I3) ≤ 236.4202 := by
      have : (1 + δ) ^ 6 * (I2 + I3) ≤ (1 + δ) ^ 6 * 221.5 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : (1 + δ) ^ 6 * 221.5 ≤ (1 + 1 / 10 ^ 7) * 221.5 := by nlinarith
      norm_num at *
      linarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hΛ0]
    have hl0 : 0 < Real.log 2 := (Real.log_pos one_lt_two)
    have : 2.02 * (I1 + 20 * δ + (1 + δ) ^ 6 * (I2 + I3)) ≤ 2.02 * 236.4202 := by linarith
    have : 2.02 * 236.4202 ≤ 690 * Real.log 2 := by norm_num at hl2' ⊢; linarith
    nlinarith
  linarith

/-- **(87)** (`eq:mu1sum`): under the pointwise bounds of Lemma 7.3(c), the dyadic series
`∑_{u = 2ʲX₀} log(2u) sup_{[u,2u]} |μ₁|` converges, and its sum is at most
`690/log X₀ ≤ 7·10⁻⁶` (m5, m6). -/
theorem mu1sum {X0 : ℝ} {μ1 : ℝ → ℝ} (h : Mu1Pointwise X0 μ1) (hX0 : 0 < X0)
    (hΛ : 10 ^ 8 ≤ Real.log X0) :
    Summable (dyTerm X0 μ1) ∧ ∑' j, dyTerm X0 μ1 j ≤ 690 / Real.log X0 ∧
      690 / Real.log X0 ≤ 7e-6 := by
  have hterm0 : ∀ j, 0 ≤ dyTerm X0 μ1 j := fun j => by
    unfold dyTerm
    apply mul_nonneg _ (blockSup_nonneg j)
    apply Real.log_nonneg
    have : 1 ≤ X0 := by
      by_contra hc; push_neg at hc
      have := Real.log_nonpos hX0.le hc.le; linarith
    have : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hs : Summable (dyTerm X0 μ1) :=
    summable_of_sum_range_le hterm0 (mu1sum_partial h hX0 hΛ)
  exact ⟨hs, hs.tsum_le_of_sum_range_le (mu1sum_partial h hX0 hΛ), m6 hΛ⟩

end BaseRange
