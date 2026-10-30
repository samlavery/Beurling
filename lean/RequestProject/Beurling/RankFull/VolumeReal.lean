module

public import Mathlib

/-!
# Theorem A.10(i): the stage change of variables (real exponents, Schur complements)

In the Staged Volume Lemma, stage `t` integrates the pivots `q_{P_t}` by the change of variables
`q_{P_t} ↦ (n_y)_{y ∈ C_t}`. Once the earlier pivots are expressed through the earlier stage
variables, `log n_y = S_t x_{P_t} + (terms not involving x_{P_t})` with `x = log q` and `S_t` the
Schur complement of `E_{R<t,P<t}` in `E_{R≤t,P≤t}` — a **real** (rational) invertible matrix.
So the stage map is `q ↦ (a_y ∏_j q_j^{(S_t)_{yj}})_y` with real exponents (`rmap`), and:

* `RankFull.rmap_injOn` : it is injective on the positive orthant;
* `RankFull.hasFDerivAt_rmap`, `RankFull.det_jacR` : its Jacobian is
  `det(S_t) ∏_y n_y/∏_j q_j`;
* `RankFull.volume_identity_real` : the change of variables
  `∫_{q ∈ s} |det S_t| ∏ n_y(q)/∏ q_j dq = vol(n(s))` for measurable `s` in the orthant;
* `RankFull.volume_bound_real` : if the Jacobian factor is `≥ κ > 0` on `s` and `n(s) ⊆ B`, then
  `vol(s) ≤ vol(B)/κ`;
* `RankFull.stage_det` : the cumulative determinant is the product of the Schur complements,
  `det E_{R≤t,P≤t} = det E_{R<t,P<t} · det S_t` (Mathlib's `Matrix.det_fromBlocks₁₁`), so
  `|det E_{R≤T,P≤T}| = ∏_t |det S_t|`.

This generalizes `Volume.lean` (natural exponents, one stage).
-/

@[expose] public section

open Finset MeasureTheory

namespace RankFull

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The stage map `q ↦ (a_i ∏_j q_j^{S_ij})_i` with real exponents. -/
noncomputable def rmap (a : ι → ℝ) (S : Matrix ι ι ℝ) (q : ι → ℝ) : ι → ℝ :=
  fun i => a i * ∏ j, q j ^ S i j

/-- The positive orthant. -/
def posOrth (ι : Type*) : Set (ι → ℝ) := {q | ∀ j, 0 < q j}

/-- The Jacobian matrix `S_ij n_i/q_j`. -/
noncomputable def jacR (a : ι → ℝ) (S : Matrix ι ι ℝ) (q : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => S i j * rmap a S q i / q j

lemma rmap_pos {a : ι → ℝ} (ha : ∀ i, 0 < a i) (S : Matrix ι ι ℝ) {q : ι → ℝ}
    (hq : q ∈ posOrth ι) (i : ι) : 0 < rmap a S q i :=
  mul_pos (ha i) (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hq j) _)

lemma log_rmap {a : ι → ℝ} (ha : ∀ i, 0 < a i) (S : Matrix ι ι ℝ) {q : ι → ℝ}
    (hq : q ∈ posOrth ι) (i : ι) :
    Real.log (rmap a S q i) = Real.log (a i) + (Matrix.mulVec S (fun j => Real.log (q j))) i := by
  unfold rmap
  rw [Real.log_mul (ha i).ne' (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hq j) _).ne',
    Real.log_prod (fun j _ => (Real.rpow_pos_of_pos (hq j) _).ne')]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => Real.log_rpow (hq j) _

/-- The stage map is injective on the positive orthant when `S` is invertible. -/
theorem rmap_injOn {a : ι → ℝ} (ha : ∀ i, 0 < a i) {S : Matrix ι ι ℝ} (hS : S.det ≠ 0) :
    Set.InjOn (rmap a S) (posOrth ι) := by
  intro q hq q' hq' h
  have hlog : Matrix.mulVec S (fun j => Real.log (q j)) =
      Matrix.mulVec S (fun j => Real.log (q' j)) := by
    funext i
    have := congrArg Real.log (congrFun h i)
    rw [log_rmap ha S hq, log_rmap ha S hq'] at this
    linarith
  have hinj := (Matrix.mulVec_injective_iff_isUnit (A := S)).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hS))
  have := hinj hlog
  funext j
  exact Real.log_injOn_pos (hq j) (hq' j) (congrFun this j)

lemma jacR_eq (a : ι → ℝ) (S : Matrix ι ι ℝ) (q : ι → ℝ) :
    jacR a S q = Matrix.diagonal (rmap a S q) * S * Matrix.diagonal (fun j => (q j)⁻¹) := by
  ext i j
  simp only [jacR, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
  ring

/-- `det(∂n/∂q) = det(S) ∏_i n_i/∏_j q_j`. -/
theorem det_jacR (a : ι → ℝ) (S : Matrix ι ι ℝ) (q : ι → ℝ) :
    (jacR a S q).det = S.det * (∏ i, rmap a S q i) / ∏ j, q j := by
  rw [jacR_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  ring

/-- The derivative of the stage map on the positive orthant. -/
theorem hasFDerivAt_rmap (a : ι → ℝ) (S : Matrix ι ι ℝ) {q : ι → ℝ} (hq : q ∈ posOrth ι) :
    HasFDerivAt (rmap a S) (Matrix.toLin' (jacR a S q)).toContinuousLinearMap q := by
  rw [hasFDerivAt_pi']
  intro i
  have hfac : ∀ j ∈ (univ : Finset ι), HasFDerivAt (fun q : ι → ℝ => q j ^ S i j)
      ((S i j * q j ^ (S i j - 1)) • ContinuousLinearMap.proj j) q :=
    fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j q).rpow_const (Or.inl (hq j).ne')
  have hprod := (HasFDerivAt.finset_prod hfac).const_mul (a i)
  convert! hprod using 1
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [jacR, rmap]
  have hqj := (hq j).ne'
  rw [← Finset.mul_prod_erase univ (fun j' => q j' ^ S i j') (Finset.mem_univ j)]
  have : q j ^ S i j = q j ^ (S i j - 1) * q j := by
    rw [Real.rpow_sub_one hqj]; field_simp
  rw [this]
  field_simp

/-- **The stage change of variables** (Theorem A.10(i)): for measurable `s ⊆ (0,∞)^ι`,
`∫_{q ∈ s} |det S| ∏ n_i(q)/∏ q_j dq = vol(n(s))`. -/
theorem volume_identity_real {a : ι → ℝ} (ha : ∀ i, 0 < a i) {S : Matrix ι ι ℝ}
    (hS : S.det ≠ 0) {s : Set (ι → ℝ)} (hs : MeasurableSet s) (hsp : s ⊆ posOrth ι) :
    ∫⁻ q in s, ENNReal.ofReal (|S.det| * (∏ i, rmap a S q i) / ∏ j, q j) =
      volume (rmap a S '' s) := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun q hq => (hasFDerivAt_rmap a S (hsp hq)).hasFDerivWithinAt)
    ((rmap_injOn ha hS).mono hsp)]
  refine setLIntegral_congr_fun hs fun q hq => ?_
  congr 1
  rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    det_jacR]
  have hq := hsp hq
  have hn : 0 < ∏ i, rmap a S q i := Finset.prod_pos fun i _ => rmap_pos ha S hq i
  have hp : 0 < ∏ j, q j := Finset.prod_pos fun j _ => hq j
  rw [abs_div, abs_mul, abs_of_pos hn, abs_of_pos hp]

/-- **The stage volume bound**: if `|det S| ∏ n_i/∏ q_j ≥ κ > 0` on `s` and `n(s) ⊆ B`, then
`vol(s) ≤ vol(B)/κ`. -/
theorem volume_bound_real {a : ι → ℝ} (ha : ∀ i, 0 < a i) {S : Matrix ι ι ℝ} (hS : S.det ≠ 0)
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (hsp : s ⊆ posOrth ι) {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ q ∈ s, κ ≤ |S.det| * (∏ i, rmap a S q i) / ∏ j, q j) {B : Set (ι → ℝ)}
    (hB : rmap a S '' s ⊆ B) :
    volume s ≤ volume B / ENNReal.ofReal κ := by
  have h1 : ENNReal.ofReal κ * volume s ≤ volume B := by
    calc ENNReal.ofReal κ * volume s = ∫⁻ _q in s, ENNReal.ofReal κ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ q in s, ENNReal.ofReal (|S.det| * (∏ i, rmap a S q i) / ∏ j, q j) :=
          setLIntegral_mono' hs fun q hq => ENNReal.ofReal_le_ofReal (hlow q hq)
      _ = volume (rmap a S '' s) := volume_identity_real ha hS hs hsp
      _ ≤ volume B := measure_mono hB
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hκ).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h1

/-- **The cumulative determinant** (proof of Theorem A.10(i)): with the earlier block `A`
(`E_{R<t,P<t}`, invertible) and the Schur complement `D - C A⁻¹ B` (`S_t`),
`det E_{R≤t,P≤t} = det E_{R<t,P<t} · det S_t`. -/
theorem stage_det {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    [Invertible A] :
    |(Matrix.fromBlocks A B C D).det| = |A.det| * |(D - C * ⅟A * B).det| := by
  rw [Matrix.det_fromBlocks₁₁, abs_mul]

end RankFull
