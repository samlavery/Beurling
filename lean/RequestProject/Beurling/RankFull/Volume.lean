module

public import Mathlib

/-!
# Lemma A.2 (Volume Lemma)

Lemma A.2 of Appendix A. Fix cofactors `c_i > 0` and an invertible exponent pattern
`E_P ∈ ℕ^{k×k}`. The map `q ↦ n`, `n_i = c_i ∏_j q_j^{E_ij}` (`nmap`):
* is injective on `ℝ_+^k` (`nmap_injOn`);
* has Jacobian matrix `∂n_i/∂q_j = E_ij n_i/q_j` (`hasFDerivAt_nmap`), with determinant
  `det(E_P) ∏_i n_i/∏_j q_j` (`det_jac`);
* satisfies `∏_j q_j^{s_j} = ∏_i (n_i/c_i)`, `s_j = ∑_i E_ij` (`prod_pow_colSum`).

The change of variables `q_P ↦ n` then gives the volume identity (A.vol) in the form
`∫_{q ∈ s} |det E_P| ∏_i n_i(q)/∏_j q_j dq = vol(n(s))` for every measurable `s ⊆ ℝ_+^k`
(`volume_identity`), and the bound of the lemma: if all `q_j ≥ Xm ≥ 1` on `s` and `n(s) ⊆ J^k`,
then `vol(s) ≤ vol(J)^k / (|det E_P| ∏_i c_i Xm^{M-k})`, `M = ∑_{ij} E_ij`
(`volume_bound`). (The paper's form `∫_{J^k} ∏q/(|det E_P| ∏n) dn` is the same identity written
on the `n` side.)
-/

@[expose] public section

open Finset MeasureTheory

namespace RankFull

variable {k : ℕ}

/-- The map `q ↦ (c_i ∏_j q_j^{E_ij})_i`. -/
noncomputable def nmap (c : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) (q : Fin k → ℝ) :
    Fin k → ℝ :=
  fun i => c i * ∏ j, q j ^ E i j

/-- The positive orthant `ℝ_+^k`. -/
def posOrthant (k : ℕ) : Set (Fin k → ℝ) := {q | ∀ j, 0 < q j}

/-- The real matrix of `E`. -/
noncomputable def Ereal (E : Matrix (Fin k) (Fin k) ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  E.map (Nat.cast : ℕ → ℝ)

/-- The Jacobian matrix `E_ij n_i/q_j`. -/
noncomputable def jac (c : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) (q : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (E i j : ℝ) * nmap c E q i / q j

lemma nmap_pos {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) (E : Matrix (Fin k) (Fin k) ℕ)
    {q : Fin k → ℝ} (hq : q ∈ posOrthant k) (i : Fin k) : 0 < nmap c E q i :=
  mul_pos (hc i) (Finset.prod_pos fun j _ => pow_pos (hq j) _)

/-- In logarithmic coordinates, `log n_i = log c_i + ∑_j E_ij log q_j`. -/
lemma log_nmap {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) (E : Matrix (Fin k) (Fin k) ℕ)
    {q : Fin k → ℝ} (hq : q ∈ posOrthant k) (i : Fin k) :
    Real.log (nmap c E q i) =
      Real.log (c i) + (Matrix.mulVec (Ereal E) (fun j => Real.log (q j))) i := by
  unfold nmap
  rw [Real.log_mul (hc i).ne' (Finset.prod_pos fun j _ => pow_pos (hq j) _).ne',
    Real.log_prod (fun j _ => (pow_pos (hq j) _).ne')]
  congr 1
  simp [Matrix.mulVec, dotProduct, Ereal, Real.log_pow]

/-- **Lemma A.2**: the map `q ↦ n` is injective on `ℝ_+^k` when `E_P` is invertible. -/
theorem nmap_injOn {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) {E : Matrix (Fin k) (Fin k) ℕ}
    (hE : (Ereal E).det ≠ 0) : Set.InjOn (nmap c E) (posOrthant k) := by
  intro q hq q' hq' h
  have hlog : Matrix.mulVec (Ereal E) (fun j => Real.log (q j)) =
      Matrix.mulVec (Ereal E) (fun j => Real.log (q' j)) := by
    funext i
    have := congrArg Real.log (congrFun h i)
    rw [log_nmap hc E hq, log_nmap hc E hq'] at this
    linarith
  have hinj := (Matrix.mulVec_injective_iff_isUnit (A := Ereal E)).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hE))
  have := hinj hlog
  funext j
  have hj := congrFun this j
  exact Real.log_injOn_pos (hq j) (hq' j) hj

/-- `∏_j q_j^{s_j} = ∏_i (n_i/c_i)` with `s_j = ∑_i E_ij` (proof of Lemma A.2). -/
theorem prod_pow_colSum {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) (E : Matrix (Fin k) (Fin k) ℕ)
    (q : Fin k → ℝ) : ∏ j, q j ^ (∑ i, E i j) = ∏ i, (nmap c E q i / c i) := by
  unfold nmap
  simp_rw [mul_div_cancel_left₀ _ (hc _).ne']
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun j _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm

/-- The Jacobian matrix is `diag(n) E_P diag(q)⁻¹`. -/
lemma jac_eq (c : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) (q : Fin k → ℝ) :
    jac c E q = Matrix.diagonal (nmap c E q) * Ereal E * Matrix.diagonal (fun j => (q j)⁻¹) := by
  ext i j
  simp only [jac, Ereal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
    div_eq_mul_inv]
  ring

/-- **The Jacobian determinant** `det(∂n/∂q) = det(E_P) ∏_i n_i/∏_j q_j`. -/
theorem det_jac (c : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) (q : Fin k → ℝ) :
    (jac c E q).det = (Ereal E).det * (∏ i, nmap c E q i) / ∏ j, q j := by
  rw [jac_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  ring

/-- The derivative of `q ↦ n` on `ℝ_+^k`. -/
theorem hasFDerivAt_nmap (c : Fin k → ℝ) (E : Matrix (Fin k) (Fin k) ℕ) {q : Fin k → ℝ}
    (hq : q ∈ posOrthant k) :
    HasFDerivAt (nmap c E) (Matrix.toLin' (jac c E q)).toContinuousLinearMap q := by
  classical
  rw [hasFDerivAt_pi']
  intro i
  have hfac : ∀ j ∈ (univ : Finset (Fin k)), HasFDerivAt (fun q : Fin k → ℝ => q j ^ E i j)
      (((E i j : ℕ) • q j ^ (E i j - 1)) • ContinuousLinearMap.proj j) q :=
    fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j q).pow (E i j)
  have hprod := (HasFDerivAt.finset_prod hfac).const_mul (c i)
  convert! hprod using 1
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, nsmul_eq_mul]
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [jac, nmap]
  have hqj := (hq j).ne'
  rcases Nat.eq_zero_or_pos (E i j) with h0 | hpos
  · simp [h0]
  · rw [← Finset.mul_prod_erase univ (fun j' => q j' ^ E i j') (Finset.mem_univ j)]
    have : q j ^ E i j = q j ^ (E i j - 1) * q j := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    rw [this]
    field_simp

/-- **Lemma A.2, the volume identity** (A.vol), on the `q` side: for every measurable
`s ⊆ ℝ_+^k`, `∫_{q ∈ s} |det E_P| ∏_i n_i(q)/∏_j q_j dq = vol(n(s))`. -/
theorem volume_identity {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) {E : Matrix (Fin k) (Fin k) ℕ}
    (hE : (Ereal E).det ≠ 0) {s : Set (Fin k → ℝ)} (hs : MeasurableSet s)
    (hsp : s ⊆ posOrthant k) :
    ∫⁻ q in s, ENNReal.ofReal (|(Ereal E).det| * (∏ i, nmap c E q i) / ∏ j, q j) =
      volume (nmap c E '' s) := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun q hq => (hasFDerivAt_nmap c E (hsp hq)).hasFDerivWithinAt)
    ((nmap_injOn hc hE).mono hsp)]
  refine setLIntegral_congr_fun hs fun q hq => ?_
  congr 1
  rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    det_jac]
  have hq := hsp hq
  have hn : 0 < ∏ i, nmap c E q i := Finset.prod_pos fun i _ => nmap_pos hc E hq i
  have hp : 0 < ∏ j, q j := Finset.prod_pos fun j _ => hq j
  rw [abs_div, abs_mul, abs_of_pos hn, abs_of_pos hp]

/-- **Lemma A.2, the bound**: if every `q ∈ s` has all `q_j ≥ Xm ≥ 1`, and `n(s) ⊆ J^k`, then
`vol(s) ≤ vol(J)^k / (|det E_P| ∏_i c_i Xm^{M-k})`, `M = ∑_{ij} E_ij`. -/
theorem volume_bound {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) {E : Matrix (Fin k) (Fin k) ℕ}
    (hE : (Ereal E).det ≠ 0) {s : Set (Fin k → ℝ)} (hs : MeasurableSet s) {Xm : ℝ}
    (hXm : 1 ≤ Xm) (hsX : ∀ q ∈ s, ∀ j, Xm ≤ q j) (J : Set ℝ)
    (hsJ : ∀ q ∈ s, ∀ i, nmap c E q i ∈ J) :
    volume s ≤ volume (Set.univ.pi fun _ : Fin k => J) /
      ENNReal.ofReal (|(Ereal E).det| * (∏ i, c i) * Xm ^ ((∑ i, ∑ j, E i j) - k)) := by
  have hsp : s ⊆ posOrthant k := fun q hq j => lt_of_lt_of_le (by linarith) (hsX q hq j)
  set C := |(Ereal E).det| * (∏ i, c i) * Xm ^ ((∑ i, ∑ j, E i j) - k) with hC
  have hdet : 0 < |(Ereal E).det| := abs_pos.mpr hE
  have hC0 : 0 < C := by
    have : 0 < ∏ i, c i := Finset.prod_pos fun i _ => hc i
    positivity
  -- every column of an invertible `E_P` is non-zero, so `s_j ≥ 1`
  have hcol : ∀ j, 1 ≤ ∑ i, E i j := by
    intro j
    by_contra h
    push_neg at h
    have h0 : ∀ i, E i j = 0 := fun i => by
      have := Finset.single_le_sum (f := fun i => E i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      try simp only at this
      omega
    apply hE
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i; simp [Ereal, h0 i]
  -- the integrand is at least `C`
  have hpt : ∀ q ∈ s, C ≤ |(Ereal E).det| * (∏ i, nmap c E q i) / ∏ j, q j := by
    intro q hq
    have hqp := hsp hq
    have hp : 0 < ∏ j, q j := Finset.prod_pos fun j _ => hqp j
    rw [le_div_iff₀ hp]
    have hnc : ∏ i, nmap c E q i = (∏ i, c i) * ∏ j, q j ^ (∑ i, E i j) := by
      rw [prod_pow_colSum hc E q, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by field_simp [(hc i).ne']
    rw [hnc]
    -- `∏_j q_j^{s_j} ≥ Xm^{M-k} ∏_j q_j`
    have hpow : Xm ^ ((∑ i, ∑ j, E i j) - k) * ∏ j, q j ≤ ∏ j, q j ^ (∑ i, E i j) := by
      have hM : (∑ i, ∑ j, E i j) - k = ∑ j, ((∑ i, E i j) - 1) := by
        rw [show (∑ i, ∑ j, E i j) = ∑ j, ∑ i, E i j from Finset.sum_comm]
        have h2 : ∑ j : Fin k, ((∑ i, E i j) - 1 + 1) = ∑ j, ∑ i, E i j :=
          Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hcol j)
        have h3 : ∑ j : Fin k, ((∑ i, E i j) - 1 + 1) = ∑ j : Fin k, ((∑ i, E i j) - 1) + k := by
          rw [Finset.sum_add_distrib]; simp
        omega
      rw [hM, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro j _; exact mul_nonneg (pow_nonneg (by linarith) _) (hqp j).le
      · intro j _
        have : q j ^ (∑ i, E i j) = q j ^ ((∑ i, E i j) - 1) * q j := by
          rw [← pow_succ, Nat.sub_add_cancel (hcol j)]
        rw [this]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (hsX q hq j) _)
          (hqp j).le
    have hcp : 0 < ∏ i, c i := Finset.prod_pos fun i _ => hc i
    calc C * ∏ j, q j = |(Ereal E).det| * (∏ i, c i) * (Xm ^ ((∑ i, ∑ j, E i j) - k) *
          ∏ j, q j) := by rw [hC]; ring
      _ ≤ |(Ereal E).det| * (∏ i, c i) * ∏ j, q j ^ (∑ i, E i j) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = |(Ereal E).det| * ((∏ i, c i) * ∏ j, q j ^ (∑ i, E i j)) := by ring
  have hid := volume_identity hc hE hs hsp
  have himg : nmap c E '' s ⊆ Set.univ.pi fun _ : Fin k => J := by
    rintro _ ⟨q, hq, rfl⟩ i _; exact hsJ q hq i
  have h1 : ENNReal.ofReal C * volume s ≤ volume (Set.univ.pi fun _ : Fin k => J) := by
    calc ENNReal.ofReal C * volume s = ∫⁻ _q in s, ENNReal.ofReal C := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ q in s, ENNReal.ofReal (|(Ereal E).det| * (∏ i, nmap c E q i) / ∏ j, q j) :=
          setLIntegral_mono' hs fun q hq => ENNReal.ofReal_le_ofReal (hpt q hq)
      _ = volume (nmap c E '' s) := hid
      _ ≤ _ := measure_mono himg
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hC0).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h1

end RankFull
