module

public import RequestProject.Beurling.Noise.RML6PredOps
public import RequestProject.Beurling.Noise.LemSMain

/-!
# Lemma 5.34, second bullet (correction #110): the pointwise block bound for `G = K_pt F`

`abs_Kpt_le` : for `F` bounded by `M_j` on the dyadic blocks `[v_j, 2v_j)`, `v_j = X₀⁻ 2^j`,

  `|(K_pt F)(y)| ≤ ∑_j ω_y(v_j) M_j`,

the first display of the regrouped proof of Lemma 5.34 (04f-bridge.tex, `lem:predictable`,
second bullet): the cofactors `w` with `y/w ∈ [v, 2v)` passing the filter `τ_w < y/w` are
exactly those counted by the filtered cofactor weight `ω_y(v)` of Lemma 5.21 (`omegaW`, for the
decision times `j ↦ t(p_j)` read on the labels).
-/

@[expose] public section

open Finset Real BeurlingSystem KR.Sharp

namespace KR.RML7G

variable (P : BeurlingSystem)

/-- The cofactors `w ≥ 2` landing in `[v, 2v)` and passing the filter carry at most the filtered
cofactor weight `ω_y(v)` of Lemma 5.21. -/
lemma sum_block_le (tw : ℕ → ℝ) {X0m y v : ℝ} (hv : 0 < v) :
    ∑ n ∈ ((NAll P y X0m).filter (2 ≤ ·)).filter (fun n =>
        (∀ p ∈ n.primeFactors, tw p * Vl P n < y) ∧ v ≤ y / Vl P n ∧ y / Vl P n < 2 * v),
      1 / Vl P n ≤ P.omegaW (fun j => tw (qp j)) y v := by
  classical
  unfold NAll
  rw [Finset.filter_image, Finset.filter_image,
    Finset.sum_image (fun a _ b _ h => iota_injective h)]
  unfold omegaW
  have hval : ∀ e : ℕ →₀ ℕ, Vl P (iota e) = P.val e := fun e => P.valN_iota e
  simp_rw [hval]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter, mem_elems] at he ⊢
    obtain ⟨⟨-, -⟩, hf, hv1, hv2⟩ := he
    have he0 := P.val_pos e
    refine ⟨?_, hv1, hv2, fun j hj => ?_⟩
    · rw [le_div_iff₀ hv, mul_comm]; rw [le_div_iff₀ he0] at hv1; linarith
    · have := hf (qp j) (by
        rw [BeurlingSystem.primeFactors_iota]; exact Finset.mem_image_of_mem _ hj)
      rw [lt_div_iff₀ he0]; exact this
  · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

/-- The dyadic block of a point `s ∈ [X₀⁻, X₀⁻ 2^J)`. -/
lemma exists_block {X0m s : ℝ} (hX : 0 < X0m) (hs : X0m ≤ s) {J : ℕ} (hJ : s < X0m * 2 ^ J) :
    ∃ j < J, X0m * 2 ^ j ≤ s ∧ s < 2 * (X0m * 2 ^ j) := by
  classical
  have hex : ∃ k : ℕ, s < X0m * 2 ^ (k + 1) := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s / X0m) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hX] at hk
    have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
    nlinarith
  set j := Nat.find hex with hj
  have hjs : s < X0m * 2 ^ (j + 1) := Nat.find_spec hex
  refine ⟨j, ?_, ?_, by rw [pow_succ] at hjs; linarith⟩
  · by_contra hc; push_neg at hc
    obtain ⟨k, hk⟩ : ∃ k, J = k + 1 := ⟨J - 1, by
      rcases Nat.eq_zero_or_pos J with h0 | h0
      · subst h0; simp at hJ; linarith
      · omega⟩
    have := Nat.find_min' hex (show s < X0m * 2 ^ (k + 1) by rw [← hk]; exact hJ)
    omega
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; simpa using hs
    · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have := Nat.find_min hex (show k < j by omega)
      push_neg at this
      rw [hk]; exact this

/-- **The pointwise block bound** (Lemma 5.34, second bullet, regrouped by block, correction
#110): `|(K_pt F)(y)| ≤ ∑_{j<J} ω_y(X₀⁻ 2^j) M_j`, if `|F| ≤ M_j` on `[X₀⁻2^j, X₀⁻2^{j+1})`
(only points `≤ y/2` are read). -/
theorem abs_Kpt_le (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) (hp2 : ∀ j, 2 ≤ P.p j)
    (F : ℝ → ℝ) {y : ℝ} {J : ℕ} (hJ : y ≤ X0m * 2 ^ J) (M : ℕ → ℝ) (hM0 : ∀ j, 0 ≤ M j)
    (hF : ∀ j < J, ∀ s, X0m * 2 ^ j ≤ s → s < 2 * (X0m * 2 ^ j) → s ≤ y / 2 → |F s| ≤ M j) :
    |Kpt P tw X0m F y| ≤
      ∑ j ∈ range J, P.omegaW (fun i => tw (qp i)) y (X0m * 2 ^ j) * M j := by
  classical
  set S := (NAll P y X0m).filter (2 ≤ ·)
  set c : ℕ → ℕ → Prop := fun j n =>
    (∀ p ∈ n.primeFactors, tw p * Vl P n < y) ∧ X0m * 2 ^ j ≤ y / Vl P n ∧
      y / Vl P n < 2 * (X0m * 2 ^ j)
  have hterm : ∀ n ∈ S, |(if ∀ p ∈ n.primeFactors, tw p * Vl P n < y then
      F (y / Vl P n) / Vl P n else 0)| ≤
      ∑ j ∈ range J, (if c j n then M j / Vl P n else 0) := by
    intro n hn
    have hnn : ∀ j ∈ range J, 0 ≤ (if c j n then M j / Vl P n else 0) := fun j _ => by
      split_ifs
      · exact div_nonneg (hM0 j) (Vl_pos P n).le
      · exact le_rfl
    split_ifs with hf
    · obtain ⟨hnN, hn2⟩ := Finset.mem_filter.mp hn
      have hV := Vl_pos P n
      have hV2 := KR.Ops.Vl_ge_two (P := P) hp2 hn2
      have hVle := ((mem_NAll_iff P hX).mp hnN).2
      have hy0 : 0 < y := by
        have h1 : (1 : ℝ) ≤ Vl P n := LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)
        have : (1 : ℝ) ≤ y / X0m := h1.trans hVle
        rw [le_div_iff₀ hX] at this; linarith
      set s := y / Vl P n
      have hsX : X0m ≤ s := by
        rw [le_div_iff₀ hX] at hVle; rw [le_div_iff₀ hV]; linarith
      have hs2 : s ≤ y / 2 := div_le_div_of_nonneg_left hy0.le (by norm_num) hV2
      have hsJ : s < X0m * 2 ^ J := by linarith
      obtain ⟨j, hjJ, hj1, hj2⟩ := exists_block hX hsX hsJ
      have hcj : c j n := ⟨hf, hj1, hj2⟩
      have hle : |F s / Vl P n| ≤ (if c j n then M j / Vl P n else 0) := by
        rw [if_pos hcj, abs_div, abs_of_pos hV]
        exact div_le_div_of_nonneg_right (hF j hjJ s hj1 hj2 hs2) hV.le
      exact hle.trans (Finset.single_le_sum hnn (Finset.mem_range.mpr hjJ))
    · rw [abs_zero]; exact Finset.sum_nonneg hnn
  calc |Kpt P tw X0m F y| ≤ ∑ n ∈ S, |(if ∀ p ∈ n.primeFactors, tw p * Vl P n < y then
        F (y / Vl P n) / Vl P n else 0)| := by
        unfold Kpt; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, ∑ j ∈ range J, (if c j n then M j / Vl P n else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ j ∈ range J, ∑ n ∈ S, (if c j n then M j / Vl P n else 0) := Finset.sum_comm
    _ ≤ ∑ j ∈ range J, P.omegaW (fun i => tw (qp i)) y (X0m * 2 ^ j) * M j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_filter]
        have e : ∑ n ∈ S.filter (c j), M j / Vl P n =
            M j * ∑ n ∈ S.filter (c j), 1 / Vl P n := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
        rw [e, mul_comm]
        exact mul_le_mul_of_nonneg_right (sum_block_le P tw (by positivity)) (hM0 j)

end KR.RML7G

end
