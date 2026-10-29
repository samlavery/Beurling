module

public import RequestProject.Beurling.RankFull.TypeUnionSum
public import RequestProject.Beurling.RankFull.CapLw
public import RequestProject.Beurling.RowWeights

/-!
# Lemma 6.21(ii) (type union): `TypeUnionBound` from the Cover Bound

The skeleton of a configuration of rank `r` (Section 6.7) records
* (s1) the set `C ⊆ Fin r` of the indices of the rows of the cover (rows are indexed by their
  pivots), with `κ = |C| ≥ 1` and `|R| = r - κ ≥ 1 + j` (`CSet r j`);
* (s2) the labels of the `r` pivots, an `r`-subset of the `π = κ D` labels (`labSet`);
* (s3) the exponents of the pivots in the rows of `C` (`ExOK`, summed by `sum_s3_le`);
* (s4) for each row `y ∈ R` its monomial and tail, an element of a finite set `adm` of admissible
  pairs with `#adm ≤ z w` (Lemma 6.22 at the degree class of the row: `#adm = z w_y ≤ z w`)
  (`s4Set`).

`RankFull.type_union_sum` is the deterministic part of the proof of Lemma 6.21(ii): with
`Σ̄_𝔰` of (6.19) (with `s_R ≤ |R|`), `(2z/δ + 1) ∑_𝔰 (θδ)^r Σ̄_𝔰 ≤ 13 L^{5.1} z w^{1+j}`.

`RankFull.typeUnionBound_of_cover` then derives `TypeUnionBound` (the hypothesis of
`theorem_6_23a`) from
* `ConfigSkeletonReduction` (pathwise: every configuration counted by `configCount` has a skeleton
  with `|R| ≥ 1 + j`, so `configCount ≤ ∑_𝔰 X_𝔰`), and
* `CoverSkeletonBound` for every skeleton (Lemma A.5 + Theorem A.10 with the cover, proof of
  Proposition 6.19), with a join list `l` with `∑ l = κ` and `#{t : j_t = 0} ≤ |R|`.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal Classical

namespace RankFull

/-- (s1): the cover index sets with `κ ≥ 1` and `|R| ≥ 1 + j`. -/
noncomputable def CSet (r j : ℕ) : Finset (Finset (Fin r)) :=
  (univ : Finset (Fin r)).powerset.filter fun C => C.Nonempty ∧ j + 1 ≤ r - C.card

/-- (s2): the `r`-subsets of the `κ D` labels. -/
noncomputable def labSet (r κ Dn : ℕ) : Finset (Finset (Fin (κ * Dn))) :=
  (univ : Finset (Fin (κ * Dn))).powersetCard r

/-- (s4): the data of the rows of `R` (the rows of `C` carry the dummy value `b₀`). -/
noncomputable def s4Set {r : ℕ} {β : Type*} (C : Finset (Fin r)) (adm : Finset β) (b₀ : β) :
    Finset (Fin r → β) :=
  Fintype.piFinset fun y => if y ∈ C then {b₀} else adm

lemma card_s4Set {r : ℕ} {β : Type*} (C : Finset (Fin r)) (adm : Finset β) (b₀ : β) :
    (s4Set C adm b₀).card = adm.card ^ (r - C.card) := by
  unfold s4Set
  rw [Fintype.card_piFinset]
  have : ∀ y, (if y ∈ C then ({b₀} : Finset β) else adm).card =
      if y ∈ C then 1 else adm.card := fun y => by split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    Finset.card_univ, Fintype.card_fin, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The pivot excess `e_i = (column sum over C) - 1`. -/
def exExcess {r : ℕ} (ex : Fin r → Fin r → ℕ) : Fin r → ℕ := fun i => (∑ y, ex y i) - 1

/-- The real part of the per-cover bound: the factors of `Σ̄_𝔰` and of the (s2)–(s4) counts,
distributed over the rows. -/
lemma perC_real {L Λ Dn Ch B lam z w : ℝ} {r κ nR : ℕ} (hr : r = κ + nR) (hκ : 1 ≤ κ)
    (hL : 60 ≤ L) (hΛ : 10 ^ 8 ≤ Λ) (hDn0 : 0 ≤ Dn) (hDn : Dn ≤ L) (hCh0 : 0 ≤ Ch)
    (hB1 : 1 ≤ B) (hlam0 : 0 ≤ lam) (hκL : (κ : ℝ) ≤ L) (hκlam : 1 + κ * lam ≤ L)
    (hz : 0 < z) (hw0 : 0 ≤ w) :
    (Real.exp 1 * Dn) ^ r * (z * w) ^ nR *
        (((1 + 1 / Λ) * (4 * L ^ (-6 : ℝ))) ^ r * (1 + κ * lam) ^ nR *
          ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * z⁻¹ ^ nR) * ((κ : ℝ) ^ nR * B ^ (κ + 1)) ≤
      (1 / 2) ^ r * ((1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) *
        (2 * (Real.exp 1 * Dn) * Real.exp 1 * Ch * B ^ 2)) ^ κ * w ^ nR := by
  set θδ := (1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) with hθδ
  have hL0 : 0 < L := by linarith
  have hθδ0 : 0 ≤ θδ := by
    have : 0 ≤ 1 / Λ := by positivity
    rw [hθδ]; positivity
  have hkk : (κ : ℝ) ^ κ / κ.factorial ≤ Real.exp 1 ^ κ := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp (x := (κ : ℝ)) (Nat.cast_nonneg κ) κ
  have hB : B ^ (κ + 1) ≤ (B ^ 2) ^ κ := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hB1 (by omega)
  have hRrow := TypeUnion.R_row_cost_le hL hΛ hDn0 hDn (Nat.cast_nonneg κ) hκL
    (by have : (0 : ℝ) ≤ κ * lam := by positivity
        linarith) hκlam
  rw [← hθδ] at hRrow
  have hzz : z ^ nR * z⁻¹ ^ nR = 1 := by rw [← mul_pow, mul_inv_cancel₀ hz.ne', one_pow]
  have hcore : (Real.exp 1 * Dn) ^ r * (z * w) ^ nR *
        (θδ ^ r * (1 + κ * lam) ^ nR * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * z⁻¹ ^ nR) *
        ((κ : ℝ) ^ nR * B ^ (κ + 1)) =
      (θδ * (Real.exp 1 * Dn)) ^ κ * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * B ^ (κ + 1) *
        (θδ * (Real.exp 1 * Dn) * κ * (1 + κ * lam) * w) ^ nR := by
    rw [hr]
    simp only [mul_pow, pow_add]
    have : z ^ nR * z⁻¹ ^ nR = 1 := hzz
    calc _ = (θδ ^ κ * (Real.exp 1 * Dn) ^ κ) * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ *
            B ^ (κ + 1) * (θδ ^ nR * (Real.exp 1 * Dn) ^ nR * (κ : ℝ) ^ nR *
            (1 + κ * lam) ^ nR * w ^ nR) * (z ^ nR * z⁻¹ ^ nR) := by ring
      _ = _ := by rw [this]; ring
  rw [hcore]
  have hA0 : 0 ≤ (θδ * (Real.exp 1 * Dn)) ^ κ := by positivity
  have h1 : (θδ * (Real.exp 1 * Dn)) ^ κ * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * B ^ (κ + 1) ≤
      (θδ * (Real.exp 1 * Dn)) ^ κ * Real.exp 1 ^ κ * Ch ^ κ * (B ^ 2) ^ κ := by
    have hC0 : 0 ≤ Ch ^ κ := pow_nonneg hCh0 _
    have hBk : 0 ≤ B ^ (κ + 1) := pow_nonneg (by linarith) _
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkk hA0) hC0) hB hBk
      (by positivity)
  have h2 : (θδ * (Real.exp 1 * Dn) * κ * (1 + κ * lam) * w) ^ nR ≤ ((1 / 2) * w) ^ nR := by
    apply pow_le_pow_left₀ (by positivity)
    have : θδ * (Real.exp 1 * Dn) * κ * (1 + κ * lam) ≤ 1 / 2 := by
      have e : θδ * 2 * (Real.exp 1 * Dn) * κ * (1 + κ * lam) =
          2 * (θδ * (Real.exp 1 * Dn) * κ * (1 + κ * lam)) := by ring
      linarith
    exact mul_le_mul_of_nonneg_right this hw0
  calc (θδ * (Real.exp 1 * Dn)) ^ κ * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * B ^ (κ + 1) *
        (θδ * (Real.exp 1 * Dn) * κ * (1 + κ * lam) * w) ^ nR
      ≤ (θδ * (Real.exp 1 * Dn)) ^ κ * Real.exp 1 ^ κ * Ch ^ κ * (B ^ 2) ^ κ *
          ((1 / 2) * w) ^ nR := by
        apply mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (1 / 2) ^ (κ + nR) * (θδ * (2 * (Real.exp 1 * Dn) * Real.exp 1 * Ch * B ^ 2)) ^ κ *
          w ^ nR := by
        simp only [mul_pow, pow_add]
        rw [show (2 : ℝ) ^ κ = ((1 / 2) ^ κ)⁻¹ by rw [one_div, inv_pow, inv_inv]]
        field_simp
    _ = _ := by rw [hr]

/-- `C(κD, r) ≤ (eD)^r` for `1 ≤ κ ≤ r`. -/
lemma choose_labels_le {κ r Dn : ℕ} (hr : 1 ≤ r) (hκr : κ ≤ r) :
    ((κ * Dn).choose r : ℝ) ≤ (Real.exp 1 * Dn) ^ r := by
  refine (RowWeights.choose_le_exp_mul_div_pow (κ * Dn) r hr).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  rw [div_le_iff₀ (by exact_mod_cast hr)]
  push_cast
  have : (κ : ℝ) ≤ r := by exact_mod_cast hκr
  have he := Real.exp_pos 1
  have hD : (0 : ℝ) ≤ Dn := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg he.le hD)]

/-- The skeleton weight `(θδ)^r Σ̄_𝔰` with `s_R = |R|` (`Σ̄` of (6.19)). -/
noncomputable def skelWeight (r : ℕ) (θδ lam Ch z : ℝ) (τ : Fin r → ℝ) (C : Finset (Fin r))
    (ex : Fin r → Fin r → ℕ) : ℝ :=
  θδ ^ r * sigmaBar C.card (r - C.card) (r - C.card) lam Ch z τ (exExcess ex)

/-- **Lemma 6.21(ii), the sum over skeletons** (deterministic): for one rank `r ≥ 1`,
`(2z/δ + 1) ∑_{(s1)–(s4)} (θδ)^r Σ̄_𝔰 ≤ 13 L^{5.1} z w^{1+j}`, with `z = e^L`, `L ≥ 60`,
`Λ ≥ 10⁸`, `θ = 1 + 1/Λ`, `δ = 4L^{-6}`, `D ≤ L`, `r ≤ L`, `1 + rλ ≤ L`, `0 ≤ Ch ≤ 2L`,
`∏_i (1 - 1/τ_i)^{-1} ≤ B ≤ 2.1 L^{1.02}`, `0 < w ≤ 1` and `#adm ≤ z w`. -/
theorem type_union_sum {L Λ Ch B lam w : ℝ} {r j Dn : ℕ} (hr1 : 1 ≤ r) {β : Type*}
    (adm : Finset β) (b₀ : β) (τ : Fin r → ℝ) (hτ : ∀ i, 1 < τ i) (hL : 60 ≤ L)
    (hΛ : 10 ^ 8 ≤ Λ) (hDn : (Dn : ℝ) ≤ L) (hrL : (r : ℝ) ≤ L) (hlam0 : 0 ≤ lam)
    (hrlam : 1 + r * lam ≤ L) (hCh0 : 0 ≤ Ch) (hCh : Ch ≤ 2 * L)
    (hBτ : ∏ i, (1 - (τ i)⁻¹)⁻¹ ≤ B) (hB : B ≤ 2.1 * L ^ (1.02 : ℝ)) (hw0 : 0 < w)
    (hw1 : w ≤ 1) (hadm : (adm.card : ℝ) ≤ Real.exp L * w) :
    ENNReal.ofReal (2 * Real.exp L / (4 * L ^ (-6 : ℝ)) + 1) *
      ∑ C ∈ CSet r j, ∑ _lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
        (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀, ENNReal.ofReal
          (skelWeight r ((1 + 1 / Λ) * (4 * L ^ (-6 : ℝ))) lam Ch (Real.exp L) τ C ex)
        else 0) ≤
      ENNReal.ofReal (13 * L ^ (5.1 : ℝ) * Real.exp L * w ^ (1 + j)) := by
  set z := Real.exp L with hzdef
  set θδ := (1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) with hθδ
  have hL0 : 0 < L := by linarith
  have hz : 0 < z := Real.exp_pos L
  have hθδ0 : 0 ≤ θδ := by
    have : 0 ≤ 1 / Λ := by positivity
    rw [hθδ]; positivity
  have hτ0 : ∀ i, 0 < (τ i)⁻¹ := fun i => inv_pos.mpr (by linarith [hτ i])
  have hu1 : ∀ i, 1 ≤ (1 - (τ i)⁻¹)⁻¹ := fun i =>
    one_le_inv₀ (by linarith [inv_lt_one_of_one_lt₀ (hτ i)]) |>.mpr (by linarith [hτ0 i])
  have hB1 : 1 ≤ B := by
    have := Finset.prod_le_prod (s := univ) (fun _ _ => zero_le_one) (fun i _ => hu1 i)
    simp only [Finset.prod_const_one] at this
    exact this.trans hBτ
  set C' := 2 * (Real.exp 1 * (Dn : ℝ)) * Real.exp 1 * Ch * B ^ 2 with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hC'le := TypeUnion.cover_row_const_le hL hDn hCh0 hCh (by linarith) hB
  set N := 2 * z / (4 * L ^ (-6 : ℝ)) + 1 with hN
  have hN0 : 0 ≤ N := by positivity
  -- one cover set
  have hper : ∀ C ∈ CSet r j,
      ∑ _lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
        (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀,
          ENNReal.ofReal (skelWeight r θδ lam Ch z τ C ex) else 0) ≤
      ENNReal.ofReal ((1 / 2) ^ r * (θδ * C') ^ C.card * w ^ (1 + j)) := by
    intro C hC
    obtain ⟨hCne, hRj⟩ := (Finset.mem_filter.mp hC).2
    set κ := C.card with hκdef
    set nR := r - κ with hnR
    have hκ1 : 1 ≤ κ := Finset.card_pos.mpr hCne
    have hκr : κ ≤ r := by
      have := Finset.card_le_univ C; simpa using this
    have hrsplit : r = κ + nR := by omega
    set K := θδ ^ r * (1 + κ * lam) ^ nR * ((κ : ℝ) ^ κ / κ.factorial) * Ch ^ κ * z⁻¹ ^ nR
      with hK
    have hK0 : 0 ≤ K := by
      have a1 : 0 ≤ θδ ^ r := pow_nonneg hθδ0 _
      have a2 : 0 ≤ (1 + (κ : ℝ) * lam) ^ nR := pow_nonneg (by
        have := mul_nonneg (Nat.cast_nonneg (α := ℝ) κ) hlam0; linarith) _
      have a3 : 0 ≤ (κ : ℝ) ^ κ / κ.factorial :=
        div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
      have a4 : 0 ≤ Ch ^ κ := pow_nonneg hCh0 _
      have a5 : 0 ≤ z⁻¹ ^ nR := pow_nonneg (inv_nonneg.mpr hz.le) _
      rw [hK]; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg a1 a2) a3) a4) a5
    have hw_eq : ∀ ex, skelWeight r θδ lam Ch z τ C ex =
        K * ∏ i, (τ i)⁻¹ ^ exExcess ex i := by
      intro ex
      unfold skelWeight sigmaBar
      rw [hK]; ring
    have hinner : ∀ ex : Fin r → Fin r → ℕ, (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀,
        ENNReal.ofReal (skelWeight r θδ lam Ch z τ C ex) else 0) =
        ENNReal.ofReal (adm.card ^ nR * K) * (if ExOK C ex then
          ∏ i, ENNReal.ofReal ((τ i)⁻¹ ^ ((∑ y, ex y i) - 1)) else 0) := by
      intro ex
      split_ifs with h
      · rw [Finset.sum_const, card_s4Set, nsmul_eq_mul, hw_eq, ENNReal.ofReal_mul hK0,
          ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hτ0 i).le _),
          ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← hκdef, ← hnR]
        simp only [exExcess]
        push_cast
        ring
      · simp
    have hs3 := sum_s3_le C τ hτ
    have hprodB : ∏ i, (1 - (τ i)⁻¹)⁻¹ ^ (κ + 1) ≤ B ^ (κ + 1) := by
      rw [Finset.prod_pow]
      exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => by linarith [hu1 i]) hBτ _
    calc ∑ _lab ∈ labSet r κ Dn, ∑' ex : Fin r → Fin r → ℕ,
          (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀,
            ENNReal.ofReal (skelWeight r θδ lam Ch z τ C ex) else 0)
        = ((κ * Dn).choose r : ℝ≥0∞) * (ENNReal.ofReal (adm.card ^ nR * K) *
            ∑' ex : Fin r → Fin r → ℕ, (if ExOK C ex then
              ∏ i, ENNReal.ofReal ((τ i)⁻¹ ^ ((∑ y, ex y i) - 1)) else 0)) := by
          rw [Finset.sum_const, labSet, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          congr 1
          rw [tsum_congr hinner, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal ((Real.exp 1 * Dn) ^ r) * (ENNReal.ofReal (adm.card ^ nR * K) *
            ENNReal.ofReal ((κ : ℝ) ^ nR * B ^ (κ + 1))) := by
          gcongr
          · rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (choose_labels_le hr1 hκr)
          · refine hs3.trans (ENNReal.ofReal_le_ofReal ?_)
            exact mul_le_mul_of_nonneg_left hprodB (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ENNReal.ofReal ((Real.exp 1 * Dn) ^ r * (adm.card ^ nR * K) *
            ((κ : ℝ) ^ nR * B ^ (κ + 1))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (mul_nonneg (Real.exp_pos 1).le
            (Nat.cast_nonneg _)) _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hK0)),
            ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (Real.exp_pos 1).le
            (Nat.cast_nonneg _)) _), mul_assoc]
      _ ≤ ENNReal.ofReal ((1 / 2) ^ r * (θδ * C') ^ κ * w ^ (1 + j)) := by
          apply ENNReal.ofReal_le_ofReal
          have hadm' : (adm.card : ℝ) ^ nR ≤ (z * w) ^ nR :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hadm nR
          have hκL : (κ : ℝ) ≤ L := le_trans (by exact_mod_cast hκr) hrL
          have hκlam : 1 + κ * lam ≤ L := by
            have : (κ : ℝ) * lam ≤ r * lam :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hκr) hlam0
            linarith
          have hreal := perC_real (z := z) (w := w) (Ch := Ch) (B := B) (lam := lam)
            (Dn := (Dn : ℝ)) hrsplit hκ1 hL hΛ (Nat.cast_nonneg _) hDn hCh0 hB1 hlam0 hκL
            hκlam hz hw0.le
          rw [← hθδ] at hreal
          have hwR : w ^ nR ≤ w ^ (1 + j) := pow_le_pow_of_le_one hw0.le hw1 (by omega)
          calc (Real.exp 1 * Dn) ^ r * (adm.card ^ nR * K) * ((κ : ℝ) ^ nR * B ^ (κ + 1))
              ≤ (Real.exp 1 * Dn) ^ r * ((z * w) ^ nR * K) * ((κ : ℝ) ^ nR * B ^ (κ + 1)) := by
                apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
                  (pow_nonneg (by linarith) _))
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hadm' hK0)
                  (pow_nonneg (mul_nonneg (Real.exp_pos 1).le (Nat.cast_nonneg _)) _)
            _ = (Real.exp 1 * Dn) ^ r * (z * w) ^ nR * K * ((κ : ℝ) ^ nR * B ^ (κ + 1)) := by
                ring
            _ ≤ (1 / 2) ^ r * (θδ * C') ^ κ * w ^ nR := hreal
            _ ≤ (1 / 2) ^ r * (θδ * C') ^ κ * w ^ (1 + j) :=
                mul_le_mul_of_nonneg_left hwR (by positivity)
  -- the number of cover sets and the window count
  have hcard : ((CSet r j).card : ℝ) ≤ 2 ^ r := by
    have : (CSet r j).card ≤ 2 ^ r := by
      unfold CSet
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast this
  have hterm : ∀ C ∈ CSet r j, N * ((1 / 2) ^ r * (θδ * C') ^ C.card * w ^ (1 + j)) ≤
      (1 / 2) ^ r * (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j)) := by
    intro C hC
    have hκ1 : 1 ≤ C.card := Finset.card_pos.mpr (Finset.mem_filter.mp hC).2.1
    have := TypeUnion.type_union_bound hL hΛ hC'0 hC'le hκ1 (pow_nonneg hw0.le (1 + j))
    rw [← hzdef, ← hθδ, ← hN] at this
    calc N * ((1 / 2) ^ r * (θδ * C') ^ C.card * w ^ (1 + j))
        = (1 / 2) ^ r * (N * (θδ * C') ^ C.card * w ^ (1 + j)) := by ring
      _ ≤ (1 / 2) ^ r * (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
  calc ENNReal.ofReal N * ∑ C ∈ CSet r j, ∑ _lab ∈ labSet r C.card Dn,
        ∑' ex : Fin r → Fin r → ℕ, (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀,
          ENNReal.ofReal (skelWeight r θδ lam Ch z τ C ex) else 0)
      ≤ ENNReal.ofReal N * ∑ C ∈ CSet r j,
          ENNReal.ofReal ((1 / 2) ^ r * (θδ * C') ^ C.card * w ^ (1 + j)) := by
        gcongr with C hC; exact hper C hC
    _ = ENNReal.ofReal (∑ C ∈ CSet r j,
          N * ((1 / 2) ^ r * (θδ * C') ^ C.card * w ^ (1 + j))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun C _ => by positivity),
          ← ENNReal.ofReal_mul hN0, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (∑ _C ∈ CSet r j,
          (1 / 2) ^ r * (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j))) :=
        ENNReal.ofReal_le_ofReal (Finset.sum_le_sum hterm)
    _ ≤ ENNReal.ofReal (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_const, nsmul_eq_mul]
        have h0 : 0 ≤ 13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j) := by positivity
        calc ((CSet r j).card : ℝ) * ((1 / 2) ^ r * (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j)))
            ≤ 2 ^ r * ((1 / 2) ^ r * (13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j))) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j) := by
              rw [← mul_assoc, ← mul_pow]; norm_num

/-! ## `TypeUnionBound` from the Cover Bound -/

lemma CSet_zero (j : ℕ) : CSet 0 j = ∅ := by
  ext C
  simp only [CSet, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ hC
  obtain ⟨y, _⟩ := hC
  exact y.elim0

/-- **Reduction of configurations to skeletons** (Lemma 6.21(ii), pathwise counting): every
configuration counted by `configCount` (rank `r < r₀`, `|R| ≥ 1 + j`) has a skeleton
(s1)–(s4), and `X J r C lab ex s4` counts the configurations in the window `J` with that
skeleton. -/
def ConfigSkeletonReduction {Ω ι β : Type*} {m : ℕ} (W : Finset ι)
    (S : ι → Ω → Finset (Fin m → ℕ)) (r₀ j k Dn : ℕ) (adm : Finset β) (b₀ : β)
    (X : ι → (r : ℕ) → (C : Finset (Fin r)) → Finset (Fin (C.card * Dn)) →
      (Fin r → Fin r → ℕ) → (Fin r → β) → Ω → ℝ≥0∞) : Prop :=
  ∀ J ∈ W, ∀ ω, (configCount r₀ j k (S J ω) : ℝ≥0∞) ≤
    ∑ r ∈ range r₀, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
      (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0)

/-- **Lemma 6.21(ii) (type union)**: `TypeUnionBound` (the input of `theorem_6_23a`) follows from
the reduction to skeletons and the Cover Bound inputs `CoverSkeletonBound` for every skeleton
(each with a join list `l`, `∑ l = κ`, `#{t : j_t = 0} ≤ |R|`), at most `2z/δ + 1` windows, and
the parameter bounds of `type_union_sum` for every rank `r < r₀`. -/
theorem typeUnionBound_of_cover {Ω ι β : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Good : Set Ω) (W : Finset ι) {m : ℕ} (S : ι → Ω → Finset (Fin m → ℕ)) {r₀ j k Dn : ℕ}
    (adm : Finset β) (b₀ : β) {L Λ Ch B lam w A Eu : ℝ} (τ : (r : ℕ) → Fin r → ℝ)
    (hτ : ∀ r, ∀ i, 1 < τ r i) (hL : 60 ≤ L) (hΛ : 10 ^ 8 ≤ Λ) (hDn : (Dn : ℝ) ≤ L)
    (hr₀L : (r₀ : ℝ) ≤ L) (hlam0 : 0 ≤ lam) (hrlam : 1 + r₀ * lam ≤ L) (hCh : Ch ≤ 2 * L)
    (hBτ : ∀ r < r₀, ∏ i, (1 - (τ r i)⁻¹)⁻¹ ≤ B) (hB : B ≤ 2.1 * L ^ (1.02 : ℝ))
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hadm : (adm.card : ℝ) ≤ Real.exp L * w)
    (hEu : 0 < Eu) (hEuA : Eu ≤ A) (hACh : A ≤ Ch) (hlam : Real.log (A / Eu) ≤ lam)
    (hW : (W.card : ℝ) ≤ 2 * Real.exp L / (4 * L ^ (-6 : ℝ)) + 1)
    (X : ι → (r : ℕ) → (C : Finset (Fin r)) → Finset (Fin (C.card * Dn)) →
      (Fin r → Fin r → ℕ) → (Fin r → β) → Ω → ℝ≥0∞)
    (hXm : ∀ J r C lab ex s4, Measurable (X J r C lab ex s4))
    (hred : ConfigSkeletonReduction W S r₀ j k Dn adm b₀ X)
    (hcov : ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r (1 + 1 / Λ) (4 * L ^ (-6 : ℝ)) A Eu (Real.exp L) (τ r)
          (exExcess ex) (r - C.card) l (X J r C lab ex s4)) :
    TypeUnionBound P Good W S r₀ j k L (Real.exp L) w := by
  set z := Real.exp L with hzdef
  set θδ := (1 + 1 / Λ) * (4 * L ^ (-6 : ℝ)) with hθδ
  set N := 2 * z / (4 * L ^ (-6 : ℝ)) + 1 with hN
  set T := 13 * L ^ (5.1 : ℝ) * z * w ^ (1 + j) with hT
  have hL0 : 0 < L := by linarith
  have hz : 0 < z := Real.exp_pos L
  have hN1 : 1 ≤ N := by
    have : 0 ≤ 2 * z / (4 * L ^ (-6 : ℝ)) := by positivity
    linarith
  have hT0 : 0 ≤ T := by positivity
  have hCh0 : 0 ≤ Ch := by
    have := hEu.trans_le hEuA; linarith
  have hθ0 : 0 ≤ 1 + 1 / Λ := by
    have : 0 ≤ 1 / Λ := by positivity
    linarith
  -- each skeleton
  have hskel : ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∫⁻ ω in Good, X J r C lab ex s4 ω ∂P ≤
        ENNReal.ofReal (skelWeight r θδ lam Ch z (τ r) C ex) := by
    intro J hJ r hr C hC lab ex s4 hex
    obtain ⟨l, hl, hl0, hb⟩ := hcov J hJ r hr C hC lab ex s4 hex
    have hκ1 : 1 ≤ l.sum := by
      rw [hl]; exact Finset.card_pos.mpr (Finset.mem_filter.mp hC).2.1
    have := cover_bound P Good hθ0 (by positivity) hz hEu hEuA hACh hlam (τ r)
      (fun i => by linarith [hτ r i]) (exExcess ex) (r - C.card) l hκ1 _ hb
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold skelWeight sigmaBar
    rw [hl, mul_pow]
    have h1 : 1 ≤ 1 + (C.card : ℝ) * lam := by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) C.card) hlam0; linarith
    have hp : (1 + (C.card : ℝ) * lam) ^ l.count 0 ≤ (1 + (C.card : ℝ) * lam) ^ (r - C.card) :=
      pow_le_pow_right₀ h1 hl0
    have hτp : 0 ≤ ∏ i, (τ r i)⁻¹ ^ exExcess ex i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (by linarith [hτ r i])) _
    have hrest : 0 ≤ ((C.card : ℝ) ^ C.card / (C.card).factorial) * Ch ^ C.card *
        (∏ i, (τ r i)⁻¹ ^ exExcess ex i) * z⁻¹ ^ (r - C.card) := by positivity
    have hθδr : 0 ≤ (1 + 1 / Λ) ^ r * (4 * L ^ (-6 : ℝ)) ^ r := by positivity
    calc (1 + 1 / Λ) ^ r * (4 * L ^ (-6 : ℝ)) ^ r * ((1 + (C.card : ℝ) * lam) ^ l.count 0 *
          ((C.card : ℝ) ^ C.card / (C.card).factorial) * Ch ^ C.card *
          (∏ i, (τ r i)⁻¹ ^ exExcess ex i) * z⁻¹ ^ (r - C.card))
        = (1 + 1 / Λ) ^ r * (4 * L ^ (-6 : ℝ)) ^ r * ((1 + (C.card : ℝ) * lam) ^ l.count 0 *
          (((C.card : ℝ) ^ C.card / (C.card).factorial) * Ch ^ C.card *
          (∏ i, (τ r i)⁻¹ ^ exExcess ex i) * z⁻¹ ^ (r - C.card))) := by ring
      _ ≤ (1 + 1 / Λ) ^ r * (4 * L ^ (-6 : ℝ)) ^ r * ((1 + (C.card : ℝ) * lam) ^ (r - C.card) *
          (((C.card : ℝ) ^ C.card / (C.card).factorial) * Ch ^ C.card *
          (∏ i, (τ r i)⁻¹ ^ exExcess ex i) * z⁻¹ ^ (r - C.card))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hrest) hθδr
      _ = _ := by ring
  -- the sum for one window and one rank
  have hrank : ∀ J ∈ W, ∀ r < r₀,
      ∫⁻ ω in Good, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
        (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0) ∂P ≤
      ENNReal.ofReal (T / N) := by
    intro J hJ r hr
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · subst hr0; simp [CSet_zero]
    have hmeas_ex : ∀ C lab (ex : Fin r → Fin r → ℕ), Measurable fun ω =>
        (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0) := by
      intro C lab ex
      split_ifs
      · exact Finset.measurable_sum _ fun s4 _ => hXm J r C lab ex s4
      · exact measurable_const
    rw [lintegral_finset_sum' _ fun C _ => (Finset.measurable_sum _ fun lab _ =>
      Measurable.ennreal_tsum fun ex => hmeas_ex C lab ex).aemeasurable]
    have hstep : ∀ C ∈ CSet r j, ∫⁻ ω in Good, ∑ lab ∈ labSet r C.card Dn,
        ∑' ex : Fin r → Fin r → ℕ,
          (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0) ∂P ≤
        ∑ _lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ, (if ExOK C ex then
          ∑ _s4 ∈ s4Set C adm b₀, ENNReal.ofReal (skelWeight r θδ lam Ch z (τ r) C ex)
          else 0) := by
      intro C hC
      rw [lintegral_finset_sum' _ fun lab _ =>
        (Measurable.ennreal_tsum fun ex => hmeas_ex C lab ex).aemeasurable]
      refine Finset.sum_le_sum fun lab _ => ?_
      rw [lintegral_tsum fun ex => (hmeas_ex C lab ex).aemeasurable]
      refine ENNReal.tsum_le_tsum fun ex => ?_
      split_ifs with hex
      · rw [lintegral_finset_sum' _ fun s4 _ => (hXm J r C lab ex s4).aemeasurable]
        exact Finset.sum_le_sum fun s4 _ => hskel J hJ r hr C hC lab ex s4 hex
      · simp
    have hsum := type_union_sum hr1 adm b₀ (τ r) (hτ r) hL hΛ hDn
      (le_trans (by exact_mod_cast hr.le) hr₀L) hlam0
      (by have : (r : ℝ) * lam ≤ r₀ * lam :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) hlam0
          linarith) hCh0 hCh (hBτ r hr) hB hw0 hw1 hadm (j := j)
    rw [← hzdef, ← hθδ, ← hN, ← hT] at hsum
    have hN0 : (0 : ℝ) < N := by linarith
    calc ∑ C ∈ CSet r j, ∫⁻ ω in Good, ∑ lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
          (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0) ∂P
        ≤ ∑ C ∈ CSet r j, ∑ _lab ∈ labSet r C.card Dn, ∑' ex : Fin r → Fin r → ℕ,
          (if ExOK C ex then ∑ _s4 ∈ s4Set C adm b₀,
            ENNReal.ofReal (skelWeight r θδ lam Ch z (τ r) C ex) else 0) :=
          Finset.sum_le_sum hstep
      _ ≤ ENNReal.ofReal T / ENNReal.ofReal N := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hN0).ne')
            (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hsum
      _ = ENNReal.ofReal (T / N) := (ENNReal.ofReal_div_of_pos hN0).symm
  -- assemble
  unfold TypeUnionBound
  have hN0 : (0 : ℝ) < N := by linarith
  calc ∑ J ∈ W, ∫⁻ ω in Good, (configCount r₀ j k (S J ω) : ℝ≥0∞) ∂P
      ≤ ∑ J ∈ W, ∑ r ∈ range r₀, ∫⁻ ω in Good, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card Dn,
          ∑' ex : Fin r → Fin r → ℕ,
            (if ExOK C ex then ∑ s4 ∈ s4Set C adm b₀, X J r C lab ex s4 ω else 0) ∂P := by
        refine Finset.sum_le_sum fun J hJ => ?_
        refine (lintegral_mono fun ω => hred J hJ ω).trans_eq ?_
        rw [lintegral_finset_sum']
        intro r _
        refine (Finset.measurable_sum _ fun C _ => Finset.measurable_sum _ fun lab _ =>
          Measurable.ennreal_tsum fun ex => ?_).aemeasurable
        split_ifs
        · exact Finset.measurable_sum _ fun s4 _ => hXm J r C lab ex s4
        · exact measurable_const
    _ ≤ ∑ _J ∈ W, ∑ _r ∈ range r₀, ENNReal.ofReal (T / N) :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun r hr =>
          hrank J hJ r (Finset.mem_range.mp hr)
    _ = ENNReal.ofReal (W.card * (r₀ * (T / N))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (r₀ * (13 * L ^ (5.1 : ℝ) * z) * w ^ (1 + j)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (W.card : ℝ) * (r₀ * (T / N)) ≤ N * (r₀ * (T / N)) :=
          mul_le_mul_of_nonneg_right hW (by positivity)
        have h2 : N * (r₀ * (T / N)) = r₀ * T := by field_simp
        calc (W.card : ℝ) * (r₀ * (T / N)) ≤ N * (r₀ * (T / N)) := h1
          _ = r₀ * T := h2
          _ = r₀ * (13 * L ^ (5.1 : ℝ) * z) * w ^ (1 + j) := by rw [hT]; ring

end RankFull
