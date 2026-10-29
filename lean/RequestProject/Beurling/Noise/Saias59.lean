module

public import RequestProject.Beurling.Noise.BSDefs
public import RequestProject.Beurling.LemmaM
public import RequestProject.BSCert.Finite.SmallCert

/-!
# Corollary 5.9 (Saias weights at every start)

For a start `y ≥ X₀⁻` and `X₀⁻/2 ≤ v ≤ y`,

  `W^sh_y(v) = ∑_{e ∈ 𝒩 : y/e ∈ [v, 2v)} |c_e(y)|/e ≤ C_S log(2v)/log y`,
  `C_S = max(2.01 C_BS, 1.4)`, `C_BS = Φ_∞(10⁸)`.

The sharp coefficients `c_e(y)` are those of Lemma 5.5 (`LemmaM.coeff`), which is stated for
the free monoid on the rational primes with an arbitrary value map. We transport a Beurling
system `P` to that setting by labelling its `j`-th prime with the `j`-th rational prime
(`labelVal`, `iota`), so the element `e` of `P` is the integer `iota e`, of value `P.val e`
(`valN_iota`).

The proof is the paper's. If `c_e(y) ≠ 0` then, by Lemma M, `χ^t_y(e) = 1`; the density
statement after Lemma M (`LemmaM.dense_of_chi`, with `p ≤ 2t(p)`) makes `e` squarefree and
`4v`-dense (`isDense_of_chi`). For `v ≤ √y/4`, Theorem 5.6 with `t = 4v`, `Y = y/(2v)` gives the
bound with `2.01 C_BS`. For `v > √y/4` the weight is at most the dyadic harmonic sum of `P`,
which is at most `1` (`harmBlock_le_one`); since `log(2v)/log y ≥ 1/2 - log 2/log y` and
`2.01 C_BS ≥ 76`, this is far below `C_S log(2v)/log y` (the paper uses the finer constant `1.4`
here; the statement is the same).

Theorem 5.6 enters as the hypothesis `P.Thm56 Z` (its statement, read on `[1, Z]`).
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- **Theorem 5.6 (Beurling–Saias, upper bound)** for `P`, read on `[1, Z]`: for `t > 0`,
`log t ≥ 10⁸`,
`t ≤ Y` and `2Y ≤ Z`, `W_t(Y) ≤ C_BS(log t) log t/log Y` with `C_BS(τ) = Φ_∞(τ)`. -/
def Thm56 (Z : ℝ) : Prop :=
  ∀ t Y : ℝ, 0 < t → 100000000 ≤ Real.log t → t ≤ Y → 2 * Y ≤ Z →
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y

/-! ## Transport to the setting of Lemma M -/

/-- The value of the rational-prime label `r`: `p_j` for `r = qp j`. -/
noncomputable def labelVal (r : ℕ) : ℝ := P.p (Nat.count Nat.Prime r)

lemma labelVal_qp (j : ℕ) : P.labelVal (qp j) = P.p j := by
  simp [labelVal, Nat.count_nth_of_infinite Nat.infinite_setOf_prime]

lemma one_le_labelVal (r : ℕ) : 1 ≤ P.labelVal r := (P.one_lt _).le

lemma factorization_iota_qp (e : ℕ →₀ ℕ) (j : ℕ) : (iota e).factorization (qp j) = e j := by
  rw [factorization_iota, Finsupp.mapDomain_apply qp_injective]

lemma primeFactors_iota (e : ℕ →₀ ℕ) : (iota e).primeFactors = e.support.image qp := by
  rw [← Nat.support_factorization, factorization_iota,
    Finsupp.mapDomain_support_of_injective qp_injective]

lemma valN_iota (e : ℕ →₀ ℕ) : LemmaM.valN P.labelVal (iota e) = P.val e := by
  unfold LemmaM.valN
  rw [factorization_iota, Finsupp.prod_mapDomain_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  unfold val
  simp only [labelVal_qp]

lemma squarefree_iota {e : ℕ →₀ ℕ} (h : Squarefree (iota e)) (j : ℕ) : e j ≤ 1 := by
  have := (Nat.squarefree_iff_factorization_le_one (iota_pos e).ne').mp h (qp j)
  rwa [factorization_iota_qp] at this

lemma p_le_val {e : ℕ →₀ ℕ} {j : ℕ} (hj : j ∈ e.support) : P.p j ≤ P.val e := by
  have h1 : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  calc P.p j = P.p j ^ 1 := (pow_one _).symm
    _ ≤ P.p j ^ e j := pow_le_pow_right₀ (P.one_lt j).le h1
    _ ≤ P.val e := P.pow_le_val e j

/-- **Density** (after Lemma 5.5): if `χ^t_y(e) = 1`, `y/e < 2v`, and `p ≤ 2t(p)` for every
prime, then `e` is squarefree and `4v`-dense. -/
lemma isDense_of_chi {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) {y v : ℝ} {e : ℕ →₀ ℕ}
    (hchi : LemmaM.chi tw P.labelVal y (iota e)) (hv : y < 2 * v * P.val e) :
    P.IsDense (4 * v) e := by
  have hval : ∀ r, r.Prime → 1 ≤ P.labelVal r := fun r _ => P.one_le_labelVal r
  refine ⟨squarefree_iota hchi.1, fun j hj => ?_⟩
  have hq : qp j ∈ (iota e).primeFactors := by
    rw [primeFactors_iota]; exact Finset.mem_image_of_mem _ hj
  have hv' : y < 2 * v * LemmaM.valN P.labelVal (iota e) := by rwa [valN_iota]
  have hd := LemmaM.dense_of_chi tw P.labelVal ht hval htv hchi hv' hq
  rw [labelVal_qp] at hd
  have hS : LemmaM.valS P.labelVal ((iota e).primeFactors.filter
      fun r => P.labelVal r < P.p j) =
      ∏ i ∈ e.support.filter (fun i => P.p i < P.p j), P.p i := by
    unfold LemmaM.valS
    rw [primeFactors_iota, Finset.filter_image, Finset.prod_image
      (fun a _ b _ h => qp_injective h)]
    simp only [labelVal_qp]
  rw [hS] at hd
  have hsub : e.support.filter (fun i => P.p i < P.p j) ⊆ e.support.filter (· < j) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    by_contra hij
    push_neg at hij
    exact absurd (P.mono hij) (not_le.mpr hi.2)
  have hle : ∏ i ∈ e.support.filter (fun i => P.p i < P.p j), P.p i ≤
      ∏ i ∈ e.support.filter (· < j), P.p i :=
    by
      rw [← Finset.prod_sdiff hsub]
      have h1 : 1 ≤ ∏ i ∈ e.support.filter (· < j) \ e.support.filter (fun i => P.p i < P.p j),
          P.p i := LemmaM.one_le_prod_real (fun i _ => (P.one_lt i).le)
      have h2 : 0 ≤ ∏ i ∈ e.support.filter (fun i => P.p i < P.p j), P.p i :=
        Finset.prod_nonneg (fun i _ => (P.p_pos i).le)
      nlinarith
  have hv0 : 0 ≤ 4 * v := by
    have he := P.val_pos e
    have hc := hchi.2 (qp j) hq
    have hpos : 0 < tw (qp j) * LemmaM.valS P.labelVal ((iota e).primeFactors.filter
        fun q => LemmaM.rk tw (qp j) ≤ LemmaM.rk tw q) :=
      mul_pos (ht _ (qp_prime j)) (lt_of_lt_of_le one_pos (LemmaM.one_le_prod_real
        (fun r _ => P.one_le_labelVal r)))
    nlinarith
  calc P.p j ≤ 4 * v * ∏ i ∈ e.support.filter (fun i => P.p i < P.p j), P.p i := hd
    _ ≤ 4 * v * ∏ i ∈ e.support.filter (· < j), P.p i := mul_le_mul_of_nonneg_left hle hv0

/-! ## The sharp Saias weight -/

/-- `W^sh_y(v) = ∑_{e ∈ 𝒩 : y/e ∈ [v, 2v)} |c_e(y)|/e`, with the sharp coefficients of
Lemma 5.5 for the decision order `tw` (on the labels) and the cut-off `X₀⁻`. -/
noncomputable def Wsh (tw : ℕ → ℝ) (X0m y v : ℝ) : ℝ :=
  ∑ e ∈ (P.elems (y / v)).filter (fun e => v ≤ y / P.val e ∧ y / P.val e < 2 * v),
    |((LemmaM.coeff tw P.labelVal X0m y (iota e) : ℤ) : ℝ)| / P.val e

lemma window_iff {y v : ℝ} (hv : 0 < v) (e : ℕ →₀ ℕ) :
    (v ≤ y / P.val e ∧ y / P.val e < 2 * v) ↔ (y / (2 * v) < P.val e ∧ P.val e ≤ y / v) := by
  have he := P.val_pos e
  rw [le_div_iff₀ he, div_lt_iff₀ he, div_lt_iff₀ (by positivity), le_div_iff₀ hv]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `W^sh_y(v) ≤ W_{4v}(y/(2v))`: the non-zero sharp coefficients live on `4v`-dense
elements and have modulus `1` (Lemma 5.5). -/
lemma Wsh_le_Wt {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) {X0m y v : ℝ} (hX0 : 0 ≤ X0m)
    (hy : X0m ≤ y) (hv : 0 < v) (hY : 1 ≤ y / (2 * v)) :
    P.Wsh tw X0m y v ≤ P.Wt (4 * v) (y / (2 * v)) := by
  classical
  have hval : ∀ r, r.Prime → 1 ≤ P.labelVal r := fun r _ => P.one_le_labelVal r
  set s := (P.elems (y / v)).filter (fun e => v ≤ y / P.val e ∧ y / P.val e < 2 * v)
  have hterm : ∀ e ∈ s, |((LemmaM.coeff tw P.labelVal X0m y (iota e) : ℤ) : ℝ)| / P.val e ≤
      if P.IsDense (4 * v) e then 1 / P.val e else 0 := by
    intro e he
    have hwin := (Finset.mem_filter.mp he).2
    rw [LemmaM.lemma_M tw P.labelVal ht hval hX0 hy (iota_pos e)]
    by_cases hchi : LemmaM.chi tw P.labelVal y (iota e)
    · have hd : P.IsDense (4 * v) e := by
        refine P.isDense_of_chi ht htv hchi ?_
        have := hwin.2
        rwa [div_lt_iff₀ (P.val_pos e)] at this
      rw [if_pos hd]
      apply div_le_div_of_nonneg_right _ (P.val_pos e).le
      have hmu : |(μ (iota e) : ℝ)| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or (iota e) with h | h | h <;> simp [h]
      push_cast
      split_ifs <;> simp [hmu]
    · simp only [hchi, if_false, mul_zero, zero_mul, Int.cast_zero, abs_zero, zero_div]
      split_ifs
      · exact (one_div_pos.mpr (P.val_pos e)).le
      · exact le_rfl
  calc P.Wsh tw X0m y v ≤ ∑ e ∈ s, (if P.IsDense (4 * v) e then 1 / P.val e else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ e ∈ s.filter (fun e => P.IsDense (4 * v) e), 1 / P.val e :=
        (Finset.sum_filter _ _).symm
    _ ≤ P.Wt (4 * v) (y / (2 * v)) := by
        unfold Wt Wsm
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          simp only [s, Finset.mem_filter, mem_elems] at he ⊢
          obtain ⟨⟨-, hw⟩, hd⟩ := he
          rw [P.window_iff hv] at hw
          refine ⟨?_, hw.1, hd, fun j _ => ?_⟩
          · have : 2 * (y / (2 * v)) = y / v := by field_simp
            rw [this]; exact hw.2
          · simp only [zero_mul]; exact Real.log_nonneg hY
        · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

/-- `W^sh_y(v)` is at most the dyadic harmonic sum of `P` at `y/(2v)`. -/
lemma Wsh_le_harmBlock {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r) {X0m y v : ℝ}
    (hX0 : 0 ≤ X0m) (hy : X0m ≤ y) (hv : 0 < v) :
    P.Wsh tw X0m y v ≤ P.harmBlock (y / (2 * v)) := by
  have hval : ∀ r, r.Prime → 1 ≤ P.labelVal r := fun r _ => P.one_le_labelVal r
  unfold Wsh harmBlock
  have e2 : 2 * (y / (2 * v)) = y / v := by field_simp
  rw [e2]
  calc ∑ e ∈ (P.elems (y / v)).filter (fun e => v ≤ y / P.val e ∧ y / P.val e < 2 * v),
        |((LemmaM.coeff tw P.labelVal X0m y (iota e) : ℤ) : ℝ)| / P.val e
      ≤ ∑ e ∈ (P.elems (y / v)).filter (fun e => v ≤ y / P.val e ∧ y / P.val e < 2 * v),
        1 / P.val e := by
        apply Finset.sum_le_sum
        intro e _
        apply div_le_div_of_nonneg_right _ (P.val_pos e).le
        exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht hval hX0 hy (iota_pos e)
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          simp only [Finset.mem_filter, mem_elems] at he ⊢
          exact ⟨he.1, ((P.window_iff hv e).mp he.2).1⟩
        · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le


namespace Cor59

/-! ## The constant -/

lemma PhiInf_ge {τ : ℝ} (hτ : 0 < τ) : 0.7 * Real.exp 4 ≤ BSaias.PhiInf τ := by
  unfold BSaias.PhiInf BSaias.C0 BSaias.kappa
  have h : (4 : ℝ) ≤ (4 * τ + 1500) / τ := by
    rw [le_div_iff₀ hτ]; linarith
  have := Real.exp_le_exp.mpr h
  have h2 := le_max_left (Real.exp ((4 * τ + 1500) / τ))
    (30 * Real.exp ((4 * τ + 1500) / (30 * τ)))
  nlinarith

lemma PhiInf_antitone {τ τ' : ℝ} (hτ : 0 < τ) (hττ' : τ ≤ τ') :
    BSaias.PhiInf τ' ≤ BSaias.PhiInf τ := by
  unfold BSaias.PhiInf BSaias.C0 BSaias.kappa
  have hτ' : 0 < τ' := lt_of_lt_of_le hτ hττ'
  have e1 : (4 * τ' + 1500) / τ' ≤ (4 * τ + 1500) / τ := by
    rw [div_le_div_iff₀ hτ' hτ]; nlinarith
  have e2 : (4 * τ' + 1500) / (30 * τ') ≤ (4 * τ + 1500) / (30 * τ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le_max (Real.exp_le_exp.mpr e1)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr e2) (by norm_num))

lemma exp4_ge : (50 : ℝ) ≤ Real.exp 4 := by
  have := Real.add_one_le_exp (1 : ℝ)
  have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h2 4]

/-! ## The dyadic harmonic sum of `P` -/

/-- Below `X₀⁻` the elements of `P` are rational integers: the harmonic sum of `P` over
`(A, 2A]` is at most that of `ℕ`. -/
lemma harmBlock_le_harmWin {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {A : ℝ} (hA : 2 * A < X0m) (hAZ : 2 * A ≤ Z) :
    P.harmBlock A ≤ BSCert.FiniteN.harmWin A := by
  unfold harmBlock BSCert.FiniteN.harmWin
  set s := (P.elems (2 * A)).filter (fun e => A < P.val e)
  have hid : ∀ e ∈ s, P.val e = (iota e : ℝ) := by
    intro e he
    have hv := (Finset.mem_filter.mp he)
    rw [mem_elems] at hv
    apply P.val_eq_iota
    intro i hi
    exact h.ident (x := 2 * A) hA hAZ i (Or.inl ((P.p_le_val hi).trans hv.1))
  calc ∑ e ∈ s, 1 / P.val e = ∑ e ∈ s, (1 : ℝ) / (iota e : ℕ) :=
        Finset.sum_congr rfl fun e he => by rw [hid e he]
    _ = ∑ n ∈ s.image iota, (1 : ℝ) / n :=
        (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / n)
          fun a _ b _ hab => iota_injective hab).symm
    _ ≤ ∑ n ∈ (Finset.range (⌊2 * A⌋₊ + 1)).filter (fun n : ℕ => A < n), (1 : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
          have hv := Finset.mem_filter.mp he
          rw [mem_elems, hid e he] at hv
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_of_le (Nat.le_floor hv.1), hv.2⟩
        · intro n _ _; positivity

/-- `∑_{n ∈ 𝒩 ∩ (A, 2A]} 1/n ≤ 1` for `A ≥ 1/2`. -/
lemma harmBlock_le_one {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hsm : P.SmallHeights Z) {A : ℝ} (hA : 1 / 2 ≤ A) (hAZ : 2 * A ≤ Z) :
    P.harmBlock A ≤ 1 := by
  rcases le_or_gt 72 A with h72 | h72
  · exact (hsm A h72 hAZ).trans (by unfold BSaias.C0; norm_num)
  have hX := h.X0m_ge
  refine (harmBlock_le_harmWin P h (by linarith) hAZ).trans ?_
  rcases le_or_gt 1 A with h1 | h1
  · exact (BSCert.FiniteN.harmWin_le_five_sixths h1 h72).trans (by norm_num)
  · rw [BSCert.FiniteN.harmWin_eq (by linarith)]
    have hf : ⌊2 * A⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]; norm_num; constructor <;> linarith
    rw [hf]
    simp

end Cor59

open Cor59 in
/-- **Corollary 5.9 (Saias weights at every start).** Let `P` satisfy (HBS) on `[1, Z]` with
`log X₀⁻ ≥ 10⁸`, and Theorem 5.6 on `[1, Z]` (`P.Thm56 Z`) and the small-height bound
`P.SmallHeights Z` (proof of Lemma 5.3). Let the decision order `tw > 0` satisfy
`p ≤ 2 t(p)` (in the paper `|t(p) - p| ≤ H(p) ≤ p/10¹⁰`). Then for every start `y ≥ X₀⁻` and
`X₀⁻/2 ≤ v ≤ y` with `2y/X₀⁻ ≤ Z`,
`W^sh_y(v) ≤ C_S log(2v)/log y`, `C_S = max(2.01 C_BS, 1.4)`, `C_BS = Φ_∞(10⁸)`. -/
theorem cor_5_9 {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (h56 : P.Thm56 Z) (hsm : P.SmallHeights Z)
    {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y := by
  have hX := h.X0m_pos
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hlogXm : 100000000 ≤ Real.log X0m := hXm
  have hlogy : 100000000 ≤ Real.log y := hlogXm.trans (Real.log_le_log hX hy)
  have hly : 0 < Real.log y := by linarith
  have h2v : X0m ≤ 2 * v := by linarith
  have hl2v : 100000000 ≤ Real.log (2 * v) := hlogXm.trans (Real.log_le_log hX h2v)
  have hYZ : y / v ≤ Z := by
    refine le_trans ?_ hZ
    rw [div_le_div_iff₀ hv0 hX]; nlinarith
  set CS := max (2.01 * BSaias.PhiInf 100000000) 1.4
  have hCS : 2.01 * BSaias.PhiInf 100000000 ≤ CS := le_max_left _ _
  have hPhi0 : 0.7 * Real.exp 4 ≤ BSaias.PhiInf 100000000 := PhiInf_ge (by norm_num)
  have he4 := exp4_ge
  have hXm7 := h.X0m_ge
  rcases le_or_gt v (√y / 4) with hsmall | hlarge
  · -- `v ≤ √y/4`: Theorem 5.6 with `t = 4v`, `Y = y/(2v)`.
    have hsq : 0 < √y := Real.sqrt_pos.mpr hy0
    have hsy : √y * √y = y := Real.mul_self_sqrt hy0.le
    have hY : 2 * √y ≤ y / (2 * v) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hYge : 4 * v ≤ y / (2 * v) := by nlinarith
    have hY1 : 1 ≤ y / (2 * v) := by
      have : (1 : ℝ) ≤ 4 * v := by norm_num at hXm7; linarith
      linarith
    have hlt : 100000000 ≤ Real.log (4 * v) :=
      hl2v.trans (Real.log_le_log (by positivity) (by linarith))
    have h2Y : 2 * (y / (2 * v)) ≤ Z := by
      have : 2 * (y / (2 * v)) = y / v := by field_simp
      rw [this]; exact hYZ
    have hW := h56 (4 * v) (y / (2 * v)) (by linarith) hlt hYge h2Y
    have hA := P.Wsh_le_Wt ht htv hX.le hy hv0 hY1
    -- `log(y/(2v)) ≥ (1/2) log y`
    have hlogY : Real.log y / 2 ≤ Real.log (y / (2 * v)) := by
      have h1 : Real.log y / 2 = Real.log √y := by rw [Real.log_sqrt hy0.le]
      rw [h1]; exact Real.log_le_log hsq (by linarith)
    have hlY : 0 < Real.log (y / (2 * v)) := by linarith
    -- `log(4v) ≤ (1 + log 2/10⁸) log(2v)`
    have hl4 : Real.log (4 * v) ≤ (1 + Real.log 2 / 100000000) * Real.log (2 * v) := by
      have : Real.log (4 * v) = Real.log 2 + Real.log (2 * v) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
      rw [this]
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have : Real.log 2 ≤ Real.log 2 / 100000000 * Real.log (2 * v) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; nlinarith
      linarith
    have hPhi := PhiInf_antitone (by norm_num : (0 : ℝ) < 100000000) hlt
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hPos : 0 ≤ BSaias.PhiInf (Real.log (4 * v)) := by
      have := PhiInf_ge (τ := Real.log (4 * v)) (by linarith); nlinarith
    calc P.Wsh tw X0m y v ≤ BSaias.PhiInf (Real.log (4 * v)) * Real.log (4 * v) /
          Real.log (y / (2 * v)) := hA.trans hW
      _ ≤ BSaias.PhiInf 100000000 * ((1 + Real.log 2 / 100000000) * Real.log (2 * v)) /
          (Real.log y / 2) := by
        have hP8 : 0 ≤ BSaias.PhiInf 100000000 := by linarith
        have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        apply div_le_div₀ (mul_nonneg hP8 (mul_nonneg (by positivity) (by linarith))) _
          (by linarith) hlogY
        exact mul_le_mul hPhi hl4 (by linarith) (by linarith)
      _ = 2 * (1 + Real.log 2 / 100000000) * BSaias.PhiInf 100000000 * Real.log (2 * v) /
          Real.log y := by field_simp
      _ ≤ CS * Real.log (2 * v) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hly.le
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have : 2 * (1 + Real.log 2 / 100000000) ≤ 2.01 := by
          have : Real.log 2 / 100000000 ≤ 1 / 100000000 := by
            apply div_le_div_of_nonneg_right hl2.le (by norm_num)
          linarith
        nlinarith
  · -- `v > √y/4`: the harmonic sum.
    have hA := P.Wsh_le_harmBlock ht hX.le hy hv0
    have hA2 : 1 / 2 ≤ y / (2 * v) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2Y : 2 * (y / (2 * v)) ≤ Z := by
      have : 2 * (y / (2 * v)) = y / v := by field_simp
      rw [this]; exact hYZ
    have hB := harmBlock_le_one P h hsm hA2 h2Y
    -- `log(2v) ≥ (1/2) log y - log 2`
    have hsq : 0 < √y := Real.sqrt_pos.mpr hy0
    have h2v' : √y / 2 ≤ 2 * v := by linarith
    have hl : Real.log y / 2 - Real.log 2 ≤ Real.log (2 * v) := by
      have : Real.log (√y / 2) = Real.log y / 2 - Real.log 2 := by
        rw [Real.log_div hsq.ne' (by norm_num), Real.log_sqrt hy0.le]
      rw [← this]; exact Real.log_le_log (by positivity) h2v'
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    rw [le_div_iff₀ hly]
    calc P.Wsh tw X0m y v * Real.log y ≤ 1 * Real.log y :=
          mul_le_mul_of_nonneg_right (hA.trans hB) hly.le
      _ ≤ CS * Real.log (2 * v) := by
        have h35 : (35 : ℝ) ≤ BSaias.PhiInf 100000000 :=
          le_trans (by linarith only [he4]) hPhi0
        have h70 : (70 : ℝ) ≤ CS := le_trans (by linarith only [h35]) hCS
        have h2 : 70 * Real.log (2 * v) ≤ CS * Real.log (2 * v) :=
          mul_le_mul_of_nonneg_right h70 (by linarith only [hl2, hl, hlogy])
        linarith only [h2, hl, hl2, hlogy]

end BeurlingSystem

end
