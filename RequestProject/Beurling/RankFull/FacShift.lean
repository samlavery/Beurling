module

public import RequestProject.Beurling.RankFull.LogVolume
public import RequestProject.BSCert.StageRows

/-!
# Lemma A.6 (FAC) in log coordinates: the stage weight, and the stage rows

In log coordinates `x = log q` of the pivots, row `y` of a configuration has the value
`n_y = c_y e^{⟨E_y, x⟩}`. The pending integrand of Lemma A.5 is
`L(x, c) = ∏_y e^{⟨E_y, x⟩} 1(c_y e^{⟨E_y, x⟩} ∈ J)` (the measure `∏ dq_j/q_j` times
`∏_y n_y/c_y`, which is `∏_j q_j^{s_j-1}`; Lemma A.2).

* `RankFull.Lcore_shift` : **(FAC)**: if every free column `g` of a block lies in the span of the
  pivot columns, `w_{·g} = E v_g` (Theorem A.10(ii)), then shifting the pivots by
  `ψ = ∑_g log q_g · v_g` removes the block from every row, and produces the weight
  `∏_g q_g^{-a_g}`, `a_g = ∑_y w_{yg}`: `L(x - ψ, c) = ∏_g q_g^{-a_g} L(x, c^{noF})`.
* `RankFull.lintegral_Lcore_shift` : the same for the integral over the processed pivots (the
  shift is a translation of the integration variables, Lebesgue measure being invariant).
* `RankFull.exists_rows_inj` : (Lemma A.8 (2)) a matrix with independent columns has a set `R` of
  `#columns` rows on which it is injective; so a column in the span of the stage pivots is
  determined by its entries in the stage rows `R≤t`, and is non-zero there if non-zero.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace RankFull

variable {K N : ℕ}

/-- The log-value `⟨E_y, x⟩` of row `y` without its cofactor. -/
noncomputable def rowLog (E : Matrix (Fin K) (Fin K) ℕ) (x : Fin K → ℝ) (y : Fin K) : ℝ :=
  ∑ j, (E y j : ℝ) * x j

/-- The pending integrand `L(x, c) = ∏_y e^{⟨E_y,x⟩} 1(c_y e^{⟨E_y,x⟩} ∈ J)`. -/
noncomputable def Lcore (E : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (cv : Fin K → ℝ)
    (x : Fin K → ℝ) : ℝ≥0∞ :=
  ∏ y, ENNReal.ofReal (Real.exp (rowLog E x y)) *
    Jw.indicator 1 (cv y * Real.exp (rowLog E x y))

lemma measurable_Lcore (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ} (hJw : MeasurableSet Jw)
    (cv : Fin K → ℝ) : Measurable (Lcore E Jw cv) := by
  unfold Lcore
  refine Finset.measurable_prod _ fun y _ => ?_
  have hr : Measurable fun x : Fin K → ℝ => rowLog E x y :=
    Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hr)).mul
    ((measurable_one.indicator hJw).comp (measurable_const.mul (Real.measurable_exp.comp hr)))

/-- The FAC shift vector `ψ = ∑_{g ∈ S} log q_g · v_g`. -/
noncomputable def facShift (S : Finset (Fin N)) (Q : Fin N → ℝ) (v : Fin N → Fin K → ℝ) :
    Fin K → ℝ :=
  fun j => ∑ g ∈ S, Real.log (Q g) * v g j

lemma rowLog_sub_facShift (E : Matrix (Fin K) (Fin K) ℕ) (S : Finset (Fin N)) (Q : Fin N → ℝ)
    (v : Fin N → Fin K → ℝ) (W : Fin K → Fin N → ℕ)
    (hv : ∀ g ∈ S, ∀ y, (W y g : ℝ) = ∑ j, (E y j : ℝ) * v g j) (x : Fin K → ℝ) (y : Fin K) :
    rowLog E (x - facShift S Q v) y = rowLog E x y - ∑ g ∈ S, (W y g : ℝ) * Real.log (Q g) := by
  unfold rowLog facShift
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hv g hg y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **(FAC) in log coordinates.** -/
theorem Lcore_shift (E : Matrix (Fin K) (Fin K) ℕ) (Jw : Set ℝ) (S : Finset (Fin N))
    (Q : Fin N → ℝ) (hQ : ∀ g ∈ S, 0 < Q g) (v : Fin N → Fin K → ℝ) (W : Fin K → Fin N → ℕ)
    (hv : ∀ g ∈ S, ∀ y, (W y g : ℝ) = ∑ j, (E y j : ℝ) * v g j) (cv' : Fin K → ℝ)
    (x : Fin K → ℝ) :
    Lcore E Jw (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g) (x - facShift S Q v) =
      ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y, W y g)) * Lcore E Jw cv' x := by
  have hexp : ∀ y, Real.exp (rowLog E (x - facShift S Q v) y) =
      Real.exp (rowLog E x y) * ∏ g ∈ S, ((Q g)⁻¹) ^ W y g := by
    intro y
    rw [rowLog_sub_facShift E S Q v W hv, Real.exp_sub, Real.exp_sum, div_eq_mul_inv,
      ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun g hg => ?_
    rw [mul_comm, Real.exp_mul, Real.exp_log (hQ g hg), Real.rpow_natCast, inv_pow]
  have hcv : ∀ y, (cv' y * ∏ g ∈ S, Q g ^ W y g) * Real.exp (rowLog E (x - facShift S Q v) y) =
      cv' y * Real.exp (rowLog E x y) := by
    intro y
    rw [hexp y]
    have : (∏ g ∈ S, Q g ^ W y g) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun g hg => ?_
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (hQ g hg).ne')]
    calc (cv' y * ∏ g ∈ S, Q g ^ W y g) * (Real.exp (rowLog E x y) *
          ∏ g ∈ S, (Q g)⁻¹ ^ W y g)
        = cv' y * Real.exp (rowLog E x y) *
            ((∏ g ∈ S, Q g ^ W y g) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g) := by ring
      _ = _ := by rw [this, mul_one]
  have hnn : ∀ y, 0 ≤ ∏ g ∈ S, (Q g)⁻¹ ^ W y g := fun y =>
    Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (hQ g hg).le) _
  unfold Lcore
  simp_rw [hcv, hexp]
  have hsplit : ∀ y, ENNReal.ofReal (Real.exp (rowLog E x y) * ∏ g ∈ S, (Q g)⁻¹ ^ W y g) =
      ENNReal.ofReal (Real.exp (rowLog E x y)) *
        ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ W y g) := fun y =>
    ENNReal.ofReal_mul (Real.exp_pos _).le
  simp_rw [hsplit]
  have hprod : ∏ g ∈ S, (Q g)⁻¹ ^ (∑ y, W y g) = ∏ y, ∏ g ∈ S, (Q g)⁻¹ ^ W y g := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hprod, ENNReal.ofReal_prod_of_nonneg (fun y _ => hnn y), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  ring

/-- The full log-vector at level `i`: the `i` processed (latest) pivots from the dummy variables
`z`, the others from `u`. -/
noncomputable def mergeL (i : ℕ) (z : Fin i → ℝ) (u : Fin K → ℝ) : Fin K → ℝ :=
  fun j => if h : K - i ≤ (j : ℕ) then z ⟨(j : ℕ) - (K - i), by omega⟩ else u j

lemma measurable_mergeL (i : ℕ) (u : Fin K → ℝ) :
    Measurable fun z : Fin i → ℝ => mergeL i z u := by
  rw [measurable_pi_iff]
  intro j
  unfold mergeL
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The shift of the processed pivots. -/
lemma mergeL_sub {i : ℕ} (hi : i ≤ K) (z : Fin i → ℝ) (u ψ : Fin K → ℝ)
    (hψ : ∀ j : Fin K, (j : ℕ) < K - i → ψ j = 0) :
    mergeL i z u - ψ =
      mergeL i (z - fun a : Fin i => ψ ⟨K - i + (a : ℕ), by have := a.isLt; omega⟩) u := by
  funext j
  simp only [Pi.sub_apply, mergeL]
  split_ifs with h
  · congr 2; exact Fin.ext (by simp; omega)
  · rw [hψ j (by omega), sub_zero]

/-- **(FAC) for the integral over the processed pivots.** -/
theorem lintegral_Lcore_shift (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) {i : ℕ} (hi : i ≤ K) (u : Fin K → ℝ) (S : Finset (Fin N))
    (Q : Fin N → ℝ) (hQ : ∀ g ∈ S, 0 < Q g) (v : Fin N → Fin K → ℝ) (W : Fin K → Fin N → ℕ)
    (hv : ∀ g ∈ S, ∀ y, (W y g : ℝ) = ∑ j, (E y j : ℝ) * v g j)
    (hsupp : ∀ g ∈ S, ∀ j : Fin K, (j : ℕ) < K - i → v g j = 0) (cv' : Fin K → ℝ) :
    ∫⁻ z : Fin i → ℝ, Lcore E Jw (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g) (mergeL i z u) =
      ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y, W y g)) *
        ∫⁻ z : Fin i → ℝ, Lcore E Jw cv' (mergeL i z u) := by
  set ψ := facShift S Q v with hψ
  have hψ0 : ∀ j : Fin K, (j : ℕ) < K - i → ψ j = 0 := by
    intro j hj
    simp only [hψ, facShift]
    exact Finset.sum_eq_zero fun g hg => by rw [hsupp g hg j hj, mul_zero]
  set ψ' : Fin i → ℝ := fun a : Fin i => ψ ⟨K - i + (a : ℕ), by have := a.isLt; omega⟩
    with hψ'
  rw [← lintegral_sub_right_eq_self _ ψ']
  have : ∀ z : Fin i → ℝ, Lcore E Jw (fun y => cv' y * ∏ g ∈ S, Q g ^ W y g)
      (mergeL i (z - ψ') u) = ENNReal.ofReal (∏ g ∈ S, (Q g)⁻¹ ^ (∑ y, W y g)) *
        Lcore E Jw cv' (mergeL i z u) := by
    intro z
    rw [← mergeL_sub hi z u ψ hψ0]
    exact Lcore_shift E Jw S Q hQ v W hv cv' _
  simp_rw [this]
  exact lintegral_const_mul _ ((measurable_Lcore E hJw cv').comp (measurable_mergeL i u))

/-- **Stage rows** (Lemma A.8 (2)): a matrix with linearly independent columns has a set `R` of
`#columns` rows on which only the zero combination of the columns vanishes. -/
theorem exists_rows_inj {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix (Fin K) ι ℝ)
    (hM : LinearIndependent ℝ M.col) :
    ∃ R : Finset (Fin K), R.card = Fintype.card ι ∧
      ∀ β : ι → ℝ, (∀ y ∈ R, ∑ j, M y j * β j = 0) → β = 0 := by
  classical
  set v : Fin K → (ι → ℝ) := M.row with hv
  set R := BSCert.StageRows.lexBasis (K := ℝ) v (fun y : Fin K => (y : ℕ)) with hR
  refine ⟨R, ?_, ?_⟩
  · rw [hR, BSCert.StageRows.card_lexBasis _ _ Fin.val_injective]
    have h1 : Module.finrank ℝ (Submodule.span ℝ (range v)) = M.rank := by
      rw [Matrix.rank_eq_finrank_span_row]
    rw [h1, Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hM]
  · intro β hβ
    -- the functional `w ↦ ∑ w_j β_j` vanishes on the span of the rows
    set φ : (ι → ℝ) →ₗ[ℝ] ℝ := Fintype.linearCombination ℝ β with hφ
    have hφv : ∀ w, φ w = ∑ j, w j * β j := by
      intro w
      simp only [hφ, Fintype.linearCombination_apply, smul_eq_mul]
    have hspan : ∀ w ∈ Submodule.span ℝ (range v), φ w = 0 := by
      intro w hw
      rw [← BSCert.StageRows.span_lexBasis (K := ℝ) v (fun y : Fin K => (y : ℕ))] at hw
      refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by
        rw [map_add, ha, hb, add_zero]) (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hw
      rintro _ ⟨y, hy, rfl⟩
      rw [hφv]
      exact hβ y hy
    have hrows : ∀ y, ∑ j, M y j * β j = 0 := fun y => by
      have := hspan (v y) (Submodule.subset_span ⟨y, rfl⟩)
      rwa [hφv] at this
    rw [Fintype.linearIndependent_iff] at hM
    refine funext fun j => hM β ?_ j
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hrows y]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end RankFull
