module

public import RequestProject.Beurling.Noise.BridgeBR

/-!
# The realised latest-prime operator `K_pt` and the sharp resolvent (§5.1, §5.5)

For a Beurling system `P` (elements written as integers `n = iota e`, values
`V n = LemmaM.valN P.labelVal n`, as in `KRWeights.lean`), a decision order `tw` on the prime
labels and the cut-off `X₀⁻`:

* `Kpt P tw X0m g y = (K_pt g)(y) = ∑_{w ≥ 2} w⁻¹ 1[τ_w < y/w] 1[y/w ≥ X₀⁻] g(y/w)`
  (04a-setup.tex lines 47–50; `τ_w < y/w` is written `t(p)·w < y` for every prime `p ∣ w`);
* `Rsh P tw X0m g y = ((1 + K_pt)⁻¹ g)(y) = ∑_n c_n(y) g(y/n)/n` with the sharp coefficients
  `c_n(y)` of Lemma 5.5 (`LemmaM.coeff`), summed over the levels `y/n ≥ X₀⁻`.

Main results:

* `Rsh_one_add_Kpt` : the resolvent identity `R_sh ((1 + K_pt) g) = g` at every start
  `y ≥ X₀⁻ > 0`, for every `g` (no support condition is needed): this is the last-step
  recursion of `c_n` (Lemma 5.5's definition);
* `Rsh_eq_rhoSh` : `R_sh g = rhoSh` of Proposition 5.26 (`BridgeBR.lean`), so the sharp
  reference there is this resolvent;
* `Rsh_eq_moebius` : by Lemma M, `R_sh g(y) = ∑_n μ(n) χ^t_y(n) g(y/n)/n`.
-/

@[expose] public section

open Finset BeurlingSystem
open scoped ArithmeticFunction.Moebius

namespace KR.Sharp

/-- `(K_pt g)(y) = ∑_{w ≥ 2, y/w ≥ X₀⁻} w⁻¹ 1[τ_w < y/w] g(y/w)`. -/
noncomputable def Kpt (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  open scoped Classical in
  ∑ w ∈ (NAll P y X0m).filter (2 ≤ ·),
    if ∀ p ∈ w.primeFactors, tw p * Vl P w < y then g (y / Vl P w) / Vl P w else 0

/-- The sharp resolvent `((1 + K_pt)⁻¹ g)(y) = ∑_n c_n(y) g(y/n)/n`. -/
noncomputable def Rsh (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ NAll P y X0m, (LemmaM.coeff tw P.labelVal X0m y n : ℝ) * g (y / Vl P n) / Vl P n

variable (P : BeurlingSystem)

lemma Vl_pos (n : ℕ) : 0 < Vl P n := KR.valN_labelVal_pos P n

lemma Vl_one : Vl P 1 = 1 := LemmaM.valN_one _

lemma Vl_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : Vl P (a * b) = Vl P a * Vl P b :=
  LemmaM.valN_mul _ ha hb

lemma mem_NAll_iff {y X0m : ℝ} (_hX : 0 < X0m) {n : ℕ} :
    n ∈ NAll P y X0m ↔ n ≠ 0 ∧ Vl P n ≤ y / X0m := by
  constructor
  · intro hn
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
    rw [mem_elems] at he
    refine ⟨(iota_pos e).ne', ?_⟩
    unfold Vl; rw [P.valN_iota]; exact he
  · rintro ⟨hn, hV⟩
    exact KR.mem_image_iota P hn hV

lemma le_div_iff_cut {y X0m : ℝ} (hX : 0 < X0m) {n : ℕ} :
    Vl P n ≤ y / X0m ↔ X0m ≤ y / Vl P n := by
  rw [le_div_iff₀ hX, le_div_iff₀ (Vl_pos P n), mul_comm]

lemma div_mul_cancel_dvd {d m : ℕ} (hd : d ∣ m) : d * (m / d) = m :=
  Nat.mul_div_cancel' hd

/-- The double sum of `R_sh (K_pt g)`, reindexed by `m = n w`. -/
lemma double_sum (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {y : ℝ} (c : ℕ → ℝ) (g : ℝ → ℝ) :
    ∑ n ∈ NAll P y X0m, c n * Kpt P tw X0m g (y / Vl P n) / Vl P n =
      ∑ m ∈ (NAll P y X0m).filter (2 ≤ ·), (∑ d ∈ m.properDivisors,
        (open scoped Classical in if LemmaM.filt tw P.labelVal y m d then c d else 0)) *
          (g (y / Vl P m) / Vl P m) := by
  classical
  unfold Kpt
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.1 * p.2, p.1⟩) (fun q => ⟨q.2, q.1 / q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, w⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    obtain ⟨hn, hw, h2⟩ := hp
    rw [mem_NAll_iff P hX] at hn hw
    rw [mem_NAll_iff P hX]
    have hw0 : w ≠ 0 := by omega
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.1
    refine ⟨⟨⟨Nat.mul_ne_zero hn.1 hw0, ?_⟩, by nlinarith⟩, ?_⟩
    · rw [Vl_mul P hn.1 hw0]
      have := hw.2
      rw [div_div, le_div_iff₀ (by have := Vl_pos P n; positivity)] at this
      rw [le_div_iff₀ hX]; linarith
    · rw [Nat.mem_properDivisors]
      exact ⟨dvd_mul_right n w, by nlinarith⟩
  · rintro ⟨m, d⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter,
      Nat.mem_properDivisors] at hq ⊢
    obtain ⟨⟨hm, h2⟩, hdm, hlt⟩ := hq
    rw [mem_NAll_iff P hX] at hm
    have hd0 : d ≠ 0 := by rintro rfl; exact hm.1 (Nat.eq_zero_of_zero_dvd hdm)
    have hk := div_mul_cancel_dvd hdm
    set q := m / d with hq
    have hk0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hk; exact hm.1 hk.symm
    have hk2 : 2 ≤ q := by
      by_contra hc; push_neg at hc
      have h1 : q = 1 := le_antisymm (Nat.lt_succ_iff.mp hc) (Nat.one_le_iff_ne_zero.mpr hk0)
      rw [h1, mul_one] at hk; omega
    refine ⟨(mem_NAll_iff P hX).mpr ⟨hd0, le_trans
      (LemmaM.valN_le_of_dvd _ (fun r _ => P.one_le_labelVal r) hdm hm.1) hm.2⟩,
      (mem_NAll_iff P hX).mpr ⟨hk0, ?_⟩, hk2⟩
    have := hm.2
    rw [← hk, Vl_mul P hd0 hk0] at this
    rw [div_div, le_div_iff₀ (by have := Vl_pos P d; positivity)]
    rw [le_div_iff₀ hX] at this; linarith
  · rintro ⟨n, w⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    have hn0 := ((mem_NAll_iff P hX).mp hp.1).1
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Nat.mul_div_cancel_left w (Nat.pos_of_ne_zero hn0)
  · rintro ⟨m, d⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter,
      Nat.mem_properDivisors] at hq
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    have hd0 : d ≠ 0 := by rintro rfl; simp at hq; omega
    exact div_mul_cancel_dvd hq.2.1
  · rintro ⟨n, w⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨hn, hw, h2⟩ := hp
    have hn0 := ((mem_NAll_iff P hX).mp hn).1
    have hw0 : w ≠ 0 := by omega
    have hdiv : n * w / n = w := Nat.mul_div_cancel_left w (Nat.pos_of_ne_zero hn0)
    have hVn := Vl_pos P n
    have hVw := Vl_pos P w
    simp only
    have hfilt : (∀ p ∈ w.primeFactors, tw p * Vl P w < y / Vl P n) ↔
        LemmaM.filt tw P.labelVal y (n * w) n := by
      unfold LemmaM.filt
      rw [hdiv]
      have e : LemmaM.valN P.labelVal (n * w) = Vl P n * Vl P w := Vl_mul P hn0 hw0
      rw [e]
      refine forall₂_congr fun p _ => ?_
      rw [lt_div_iff₀ hVn]
      constructor <;> intro h <;> linarith
    by_cases hF : ∀ p ∈ w.primeFactors, tw p * Vl P w < y / Vl P n
    · rw [if_pos hF, if_pos (hfilt.mp hF), Vl_mul P hn0 hw0, div_div]
      ring
    · rw [if_neg hF, if_neg (fun h => hF (hfilt.mpr h))]
      ring

/-- **The resolvent identity** `R_sh ((1 + K_pt) g) = g` at a start `y ≥ X₀⁻ > 0`: this is
the recursion `c_m = -∑_{d ∣ m, d < m} 1[τ_{m/d} < y/m] 1[y/m ≥ X₀⁻] c_d` of Lemma 5.5. -/
theorem Rsh_one_add_Kpt (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {y : ℝ} (hy : X0m ≤ y)
    (g : ℝ → ℝ) :
    Rsh P tw X0m (fun z => g z + Kpt P tw X0m g z) y = g y := by
  classical
  have h1 : (1 : ℕ) ∈ NAll P y X0m := by
    rw [mem_NAll_iff P hX, Vl_one, le_div_iff₀ hX]; exact ⟨one_ne_zero, by linarith⟩
  unfold Rsh
  simp only [mul_add, add_div, Finset.sum_add_distrib]
  rw [double_sum P tw hX (fun n => (LemmaM.coeff tw P.labelVal X0m y n : ℝ)) g]
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
  have hc1 : (LemmaM.coeff tw P.labelVal X0m y 1 : ℝ) = 1 := by
    rw [LemmaM.coeff]; simp
  have hzero : ∀ m ∈ (NAll P y X0m).filter (2 ≤ ·),
      (LemmaM.coeff tw P.labelVal X0m y m : ℝ) * g (y / Vl P m) / Vl P m +
      (∑ d ∈ m.properDivisors, (if LemmaM.filt tw P.labelVal y m d then
        (LemmaM.coeff tw P.labelVal X0m y d : ℝ) else 0)) * (g (y / Vl P m) / Vl P m) = 0 := by
    intro m hm
    obtain ⟨hmA, hm2⟩ := Finset.mem_filter.mp hm
    have hcut : X0m ≤ y / LemmaM.valN P.labelVal m :=
      (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hmA).2
    have hrec : (LemmaM.coeff tw P.labelVal X0m y m : ℝ) = -∑ d ∈ m.properDivisors,
        (if LemmaM.filt tw P.labelVal y m d then
          (LemmaM.coeff tw P.labelVal X0m y d : ℝ) else 0) := by
      rw [LemmaM.coeff, if_neg (by omega)]
      push_cast
      rw [Finset.sum_attach m.properDivisors (fun d => (if LemmaM.filt tw P.labelVal y m d ∧
        X0m ≤ y / LemmaM.valN P.labelVal m then (LemmaM.coeff tw P.labelVal X0m y d : ℝ)
          else 0))]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hf : LemmaM.filt tw P.labelVal y m d
      · rw [if_pos ⟨hf, hcut⟩, if_pos hf]
      · rw [if_neg (fun h => hf h.1), if_neg hf]
    rw [hrec]; ring
  have hfl : ((NAll P y X0m).filter (2 ≤ ·)).filter (2 ≤ ·) = (NAll P y X0m).filter (2 ≤ ·) :=
    Finset.filter_filter _ _ _ |>.trans (by simp)
  conv_lhs => rw [hsplit]
  rw [Finset.sum_insert hnot, Finset.filter_insert, if_neg (by norm_num), hfl, hc1, Vl_one,
    div_one, div_one, one_mul, add_assoc, ← Finset.sum_add_distrib,
    Finset.sum_eq_zero hzero, add_zero]

/-- The sharp resolvent is the sharp reference `rhoSh` of Proposition 5.26 (`BridgeBR.lean`):
the masses there are the coefficients of Lemma 5.5 (`KR.mass_eq_coeff`). -/
theorem Rsh_eq_rhoSh (tw : ℕ → ℝ) (X0m y : ℝ) (g : ℝ → ℝ) :
    Rsh P tw X0m g y = rhoSh P tw X0m y g := by
  unfold Rsh rhoSh
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold cN posn
  rw [KR.mass_eq_coeff]

/-- **Lemma 5.5 in the resolvent**: `R_sh g(y) = ∑_n μ(n) χ^t_y(n) g(y/n)/n`. -/
theorem Rsh_eq_moebius {tw : ℕ → ℝ} (ht : ∀ p, p.Prime → 0 < tw p) {X0m : ℝ}
    (hX : 0 < X0m) {y : ℝ} (hy : X0m ≤ y) (g : ℝ → ℝ) :
    Rsh P tw X0m g y = ∑ n ∈ NAll P y X0m, open scoped Classical in
      (μ n : ℝ) * (if LemmaM.chi tw P.labelVal y n then 1 else 0) * g (y / Vl P n) / Vl P n := by
  classical
  unfold Rsh
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 := ((mem_NAll_iff P hX).mp hn).1
  have hcut := (le_div_iff_cut P hX).mp ((mem_NAll_iff P hX).mp hn).2
  rw [LemmaM.lemma_M tw P.labelVal ht (fun r _ => P.one_le_labelVal r) hX.le hy
    (Nat.one_le_iff_ne_zero.mpr hn0)]
  unfold Vl at hcut ⊢
  rw [if_pos hcut]
  push_cast
  split_ifs <;> ring

end KR.Sharp

end
