module

public import RequestProject.Beurling.RankFull.Volume

/-!
# Lemma A.2 (Volume Lemma) with per-pivot caps

`RankFull.volume_bound_caps` : if every `q ∈ s` has `q_j ≥ τ_j ≥ 1` and `n(s) ⊆ J^k`, then
`vol(s) ≤ vol(J)^k / (|det E_P| ∏_i c_i ∏_j τ_j^{s_j - 1})`, `s_j = ∑_i E_ij` (the form used in the
proof of Theorem A.12, with the caps `τ_j` of (A.tau)).
-/

@[expose] public section

open Finset MeasureTheory

namespace RankFull

variable {k : ℕ}

/-- Every column of an invertible pattern is non-zero. -/
lemma one_le_colSum {E : Matrix (Fin k) (Fin k) ℕ} (hE : (Ereal E).det ≠ 0) (j : Fin k) :
    1 ≤ ∑ i, E i j := by
  by_contra h
  push_neg at h
  have h0 : ∀ i, E i j = 0 := fun i => by
    have := Finset.single_le_sum (f := fun i => E i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    simp only at this
    omega
  apply hE
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i; simp [Ereal, h0 i]

/-- **Lemma A.2 with per-pivot caps.** -/
theorem volume_bound_caps {c : Fin k → ℝ} (hc : ∀ i, 0 < c i) {E : Matrix (Fin k) (Fin k) ℕ}
    (hE : (Ereal E).det ≠ 0) {s : Set (Fin k → ℝ)} (hs : MeasurableSet s) {τ : Fin k → ℝ}
    (hτ : ∀ j, 1 ≤ τ j) (hsX : ∀ q ∈ s, ∀ j, τ j ≤ q j) (J : Set ℝ)
    (hsJ : ∀ q ∈ s, ∀ i, nmap c E q i ∈ J) :
    volume s ≤ volume (Set.univ.pi fun _ : Fin k => J) /
      ENNReal.ofReal (|(Ereal E).det| * (∏ i, c i) * ∏ j, τ j ^ ((∑ i, E i j) - 1)) := by
  have hsp : s ⊆ posOrthant k := fun q hq j =>
    lt_of_lt_of_le (by linarith [hτ j]) (hsX q hq j)
  set C := |(Ereal E).det| * (∏ i, c i) * ∏ j, τ j ^ ((∑ i, E i j) - 1) with hC
  have hdet : 0 < |(Ereal E).det| := abs_pos.mpr hE
  have hC0 : 0 < C := by
    have : 0 < ∏ i, c i := Finset.prod_pos fun i _ => hc i
    have : 0 < ∏ j, τ j ^ ((∑ i, E i j) - 1) :=
      Finset.prod_pos fun j _ => pow_pos (by linarith [hτ j]) _
    positivity
  have hpt : ∀ q ∈ s, C ≤ |(Ereal E).det| * (∏ i, nmap c E q i) / ∏ j, q j := by
    intro q hq
    have hqp := hsp hq
    have hp : 0 < ∏ j, q j := Finset.prod_pos fun j _ => hqp j
    rw [le_div_iff₀ hp]
    have hnc : ∏ i, nmap c E q i = (∏ i, c i) * ∏ j, q j ^ (∑ i, E i j) := by
      rw [prod_pow_colSum hc E q, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by field_simp [(hc i).ne']
    rw [hnc]
    have hpow : (∏ j, τ j ^ ((∑ i, E i j) - 1)) * ∏ j, q j ≤ ∏ j, q j ^ (∑ i, E i j) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro j _; exact mul_nonneg (pow_nonneg (by linarith [hτ j]) _) (hqp j).le
      · intro j _
        have : q j ^ (∑ i, E i j) = q j ^ ((∑ i, E i j) - 1) * q j := by
          rw [← pow_succ, Nat.sub_add_cancel (one_le_colSum hE j)]
        rw [this]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith [hτ j]) (hsX q hq j) _) (hqp j).le
    have hcp : 0 < ∏ i, c i := Finset.prod_pos fun i _ => hc i
    calc C * ∏ j, q j = |(Ereal E).det| * (∏ i, c i) * ((∏ j, τ j ^ ((∑ i, E i j) - 1)) *
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
