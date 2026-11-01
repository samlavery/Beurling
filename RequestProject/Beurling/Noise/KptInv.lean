module

public import RequestProject.Beurling.Noise.KptDefs
public import RequestProject.Beurling.Noise.KptFirst

/-!
# The resolvent identity `(1 + K_pt) R_sh = id` (§5.5)

`KptDefs.lean` proves `R_sh ((1 + K_pt) g) = g` (the last-step recursion of Lemma 5.5). Here we
prove the other composition,

  `(R_sh g)(y) + (K_pt (R_sh g))(y) = g(y)`   for every start `y ≥ X₀⁻ > 0` and every `g`
  (`one_add_Kpt_Rsh`),

from the first-step recursion of the coefficients (`LemmaM.coeff_first`, `KptFirst.lean`):
`K_pt (R_sh g)(y) = ∑_{w ≥ 2} w⁻¹ 1[τ_w < y/w] ∑_m c_m(y/w) g(y/(wm))/m` is reindexed by
`N = wm` (`Kpt_Rsh_eq`), and the coefficient of `g(y/N)/N` is
`∑_{w ∣ N, w ≥ 2} 1[τ_w w < y] c_{N/w}(y/w) = -c_N(y)`. No support condition on `g` is needed:
both sides read `g` only at the points `y/N ≥ X₀⁻`.
-/

@[expose] public section

open Finset BeurlingSystem

namespace KR.Sharp

variable (P : BeurlingSystem)

/-- `K_pt (R_sh g)(y)`, reindexed by the level `N = w m`. -/
lemma Kpt_Rsh_eq (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {y : ℝ} (g : ℝ → ℝ) :
    Kpt P tw X0m (Rsh P tw X0m g) y =
      ∑ N ∈ (NAll P y X0m).filter (2 ≤ ·), (∑ w ∈ N.divisors.filter (2 ≤ ·),
        (open scoped Classical in if LemmaM.ffilt tw P.labelVal y w then
          (LemmaM.coeff tw P.labelVal X0m (y / Vl P w) (N / w) : ℝ) else 0)) *
          (g (y / Vl P N) / Vl P N) := by
  classical
  unfold Kpt Rsh
  simp only [Finset.sum_mul]
  have hif : ∀ w, (if ∀ p ∈ w.primeFactors, tw p * Vl P w < y then
      (∑ m ∈ NAll P (y / Vl P w) X0m, (LemmaM.coeff tw P.labelVal X0m (y / Vl P w) m : ℝ) *
        g (y / Vl P w / Vl P m) / Vl P m) / Vl P w else 0) =
      ∑ m ∈ NAll P (y / Vl P w) X0m, (if LemmaM.ffilt tw P.labelVal y w then
        (LemmaM.coeff tw P.labelVal X0m (y / Vl P w) m : ℝ) *
          g (y / Vl P w / Vl P m) / Vl P m / Vl P w else 0) := by
    intro w
    by_cases h : ∀ p ∈ w.primeFactors, tw p * Vl P w < y
    · have h' : LemmaM.ffilt tw P.labelVal y w := h
      rw [if_pos h, Finset.sum_div]
      exact Finset.sum_congr rfl fun m _ => by rw [if_pos h']
    · have h' : ¬ LemmaM.ffilt tw P.labelVal y w := h
      rw [if_neg h]
      exact (Finset.sum_eq_zero fun m _ => by rw [if_neg h']).symm
  simp_rw [hif]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.1 * p.2, p.1⟩) (fun q => ⟨q.2, q.1 / q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨w, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    obtain ⟨⟨hw, h2⟩, hm⟩ := hp
    rw [mem_NAll_iff P hX] at hw hm
    have hw0 : w ≠ 0 := by omega
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm.1
    refine ⟨⟨(mem_NAll_iff P hX).mpr ⟨Nat.mul_ne_zero hw0 hm.1, ?_⟩, by nlinarith⟩, ?_, h2⟩
    · rw [Vl_mul P hw0 hm.1]
      have := hm.2
      rw [div_div, le_div_iff₀ (by have := Vl_pos P w; positivity)] at this
      rw [le_div_iff₀ hX]; linarith
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_right w m, Nat.mul_ne_zero hw0 hm.1⟩
  · rintro ⟨N, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨hN, -⟩, ⟨hwN, -⟩, hw2⟩ := hq
    rw [mem_NAll_iff P hX] at hN
    have hw0 : w ≠ 0 := by omega
    have hk := div_mul_cancel_dvd hwN
    have hk0 : N / w ≠ 0 := by intro h; rw [h, mul_zero] at hk; exact hN.1 hk.symm
    refine ⟨⟨(mem_NAll_iff P hX).mpr ⟨hw0, le_trans
      (LemmaM.valN_le_of_dvd _ (fun r _ => P.one_le_labelVal r) hwN hN.1) hN.2⟩, hw2⟩,
      (mem_NAll_iff P hX).mpr ⟨hk0, ?_⟩⟩
    have := hN.2
    rw [← hk, Vl_mul P hw0 hk0] at this
    rw [div_div, le_div_iff₀ (by have := Vl_pos P w; positivity)]
    rw [le_div_iff₀ hX] at this; linarith
  · rintro ⟨w, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    have hw0 : w ≠ 0 := by omega
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hw0)
  · rintro ⟨N, w⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hq
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact div_mul_cancel_dvd hq.2.1.1
  · rintro ⟨w, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨⟨hw, h2⟩, hm⟩ := hp
    have hw0 : w ≠ 0 := by omega
    have hm0 := ((mem_NAll_iff P hX).mp hm).1
    have hdiv : w * m / w = m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hw0)
    simp only
    rw [hdiv, Vl_mul P hw0 hm0, div_div]
    by_cases hF : LemmaM.ffilt tw P.labelVal y w
    · rw [if_pos hF, if_pos hF]; ring
    · rw [if_neg hF, if_neg hF, zero_mul]

/-- **The resolvent identity** `(1 + K_pt) R_sh = id`: for every start `y ≥ X₀⁻ > 0` and every
`g`, `(R_sh g)(y) + (K_pt (R_sh g))(y) = g(y)`. With `Rsh_one_add_Kpt` this shows that `R_sh`
is the two-sided inverse of `1 + K_pt`. -/
theorem one_add_Kpt_Rsh (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {y : ℝ} (hy : X0m ≤ y)
    (g : ℝ → ℝ) :
    Rsh P tw X0m g y + Kpt P tw X0m (Rsh P tw X0m g) y = g y := by
  classical
  rw [Kpt_Rsh_eq P tw hX g]
  have h1 : (1 : ℕ) ∈ NAll P y X0m := by
    rw [mem_NAll_iff P hX, Vl_one, le_div_iff₀ hX]; exact ⟨one_ne_zero, by linarith⟩
  have hsplit : NAll P y X0m = insert 1 ((NAll P y X0m).filter (2 ≤ ·)) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hn
      have hn0 := ((mem_NAll_iff P hX).mp hn).1
      rcases Nat.lt_or_ge n 2 with h | h
      · left; omega
      · right; exact ⟨hn, h⟩
    · rintro (rfl | ⟨hn, -⟩)
      · exact h1
      · exact hn
  have hnot : (1 : ℕ) ∉ (NAll P y X0m).filter (2 ≤ ·) := by simp
  unfold Rsh
  rw [hsplit, Finset.sum_insert hnot, LemmaM.coeff_one_eq, Vl_one, div_one, div_one]
  have hfl : ((NAll P y X0m).filter (2 ≤ ·)).filter (2 ≤ ·) = (NAll P y X0m).filter (2 ≤ ·) :=
    Finset.filter_filter _ _ _ |>.trans (by simp)
  rw [Finset.filter_insert, if_neg (by norm_num), hfl]
  push_cast
  rw [one_mul, add_assoc, ← Finset.sum_add_distrib]
  have hzero : ∀ N ∈ (NAll P y X0m).filter (2 ≤ ·),
      (LemmaM.coeff tw P.labelVal X0m y N : ℝ) * g (y / Vl P N) / Vl P N +
      (∑ w ∈ N.divisors.filter (2 ≤ ·), (if LemmaM.ffilt tw P.labelVal y w then
        (LemmaM.coeff tw P.labelVal X0m (y / Vl P w) (N / w) : ℝ) else 0)) *
          (g (y / Vl P N) / Vl P N) = 0 := by
    intro N hN
    obtain ⟨hNA, hN2⟩ := Finset.mem_filter.mp hN
    have hcut : X0m ≤ y / LemmaM.valN P.labelVal N :=
      (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hNA).2
    have hrec := LemmaM.coeff_first (t := tw) (fun r _ => P.one_le_labelVal r) hX.le N hN2 y
    have hc : (LemmaM.coeff tw P.labelVal X0m y N : ℝ) =
        -∑ w ∈ N.divisors.filter (2 ≤ ·), (if LemmaM.ffilt tw P.labelVal y w then
          (LemmaM.coeff tw P.labelVal X0m (y / Vl P w) (N / w) : ℝ) else 0) := by
      rw [hrec]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hf : LemmaM.ffilt tw P.labelVal y w
      · rw [if_pos ⟨hf, hcut⟩, if_pos hf]
      · rw [if_neg (fun h => hf h.1), if_neg hf]
    rw [hc]; ring
  rw [Finset.sum_eq_zero hzero, add_zero]

end KR.Sharp

end
