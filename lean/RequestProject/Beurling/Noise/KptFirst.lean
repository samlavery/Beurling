module

public import RequestProject.Beurling.LemmaM

/-!
# The first-step recursion of the sharp coefficients (§5.5)

The sharp coefficients `c_n(y)` of Lemma 5.5 (`LemmaM.coeff`) are defined by the *last-step*
recursion `c_n(y) = -∑_{d ∣ n, d < n} 1[τ_{n/d} · n < y] 1[y/n ≥ X₀⁻] c_d(y)`. Expanding it,
`c_n(y)` is the signed sum over the ordered factorisations `n = w₁ ⋯ w_k` whose cumulative
filters pass. Splitting off the *first* factor instead of the last one gives the first-step
recursion

  `c_n(y) = -∑_{w ∣ n, w ≥ 2} 1[τ_w · w < y] 1[y/n ≥ X₀⁻] c_{n/w}(y/w)`   (`coeff_first`),

where the chain of the cofactor `n/w` starts at `y/w`: its cumulative filters
`τ_{w_i} w₂ ⋯ w_i < y/w` are those of the original chain, and its cut-off is again `y/n ≥ X₀⁻`.
The proof is by strong induction on `n`, comparing the two double sums over the pairs
`(d, w)`, `w ∣ d ∣ n` (first and last factor), reindexed by `d = w e`.
-/

@[expose] public section

open Finset

namespace LemmaM

variable (t val : ℕ → ℝ)

open scoped Classical

/-- The first-step filter `τ_w · w < y` (`t(p) · w < y` for every prime `p ∣ w`). -/
def ffilt (y : ℝ) (w : ℕ) : Prop := ∀ p ∈ w.primeFactors, t p * valN val w < y

lemma coeff_one_eq (X0 y : ℝ) : coeff t val X0 y 1 = 1 := by rw [coeff]; simp

lemma coeff_rec (X0 y : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    coeff t val X0 y n = -∑ d ∈ n.properDivisors,
      (if filt t val y n d ∧ X0 ≤ y / valN val n then coeff t val X0 y d else 0) := by
  rw [coeff, if_neg (by omega)]
  congr 1
  exact Finset.sum_attach n.properDivisors
    (fun d => if filt t val y n d ∧ X0 ≤ y / valN val n then coeff t val X0 y d else 0)

variable {t val}

lemma valN_div_mul' {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) :
    valN val n = valN val d * valN val (n / d) := by
  obtain ⟨k, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hn
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hn
  rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0), valN_mul val hd0 hk0]

/-- The last-step filter of `w e → n` from `y` is the last-step filter of `e → n/w` from
`y/w`. -/
lemma filt_shift (hval : ∀ p, p.Prime → 1 ≤ val p) {y : ℝ} {n w e : ℕ} (hw : w ∣ n)
    (hn : n ≠ 0) :
    filt t val y n (w * e) ↔ filt t val (y / valN val w) (n / w) e := by
  unfold filt
  rw [Nat.div_div_eq_div_mul]
  have hV := valN_div_mul' (val := val) hw hn
  have hw0 := valN_pos val hval (n := w)
  refine forall₂_congr fun p _ => ?_
  rw [lt_div_iff₀ hw0, hV]
  constructor <;> intro h <;> nlinarith

/-- The cut-off of the cofactor chain is the original one: `(y/w)/(n/w) = y/n`. -/
lemma cut_shift (hval : ∀ p, p.Prime → 1 ≤ val p) {X0 y : ℝ} {n w : ℕ} (hw : w ∣ n)
    (hn : n ≠ 0) :
    X0 ≤ y / valN val w / valN val (n / w) ↔ X0 ≤ y / valN val n := by
  rw [valN_div_mul' (val := val) hw hn, div_div]

/-- **The first-step recursion** of the sharp coefficients:
`c_n(y) = -∑_{w ∣ n, w ≥ 2} 1[τ_w w < y] 1[y/n ≥ X₀⁻] c_{n/w}(y/w)` for `n ≥ 2`. -/
theorem coeff_first (hval : ∀ p, p.Prime → 1 ≤ val p) {X0 : ℝ} (hX0 : 0 ≤ X0) :
    ∀ (n : ℕ), 2 ≤ n → ∀ y : ℝ, coeff t val X0 y n = -∑ w ∈ n.divisors.filter (2 ≤ ·),
      (if ffilt t val y w ∧ X0 ≤ y / valN val n then
        coeff t val X0 (y / valN val w) (n / w) else 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn y
  have hn0 : n ≠ 0 := by omega
  set cut := X0 ≤ y / valN val n with hcut
  -- the LHS: last step, then the first step for `d`
  rw [coeff_rec t val X0 y hn]
  have hpd : n.properDivisors = insert 1 (n.properDivisors.filter (2 ≤ ·)) := by
    ext d
    simp only [Finset.mem_insert, Finset.mem_filter, Nat.mem_properDivisors]
    constructor
    · rintro ⟨hdn, hdlt⟩
      rcases Nat.lt_or_ge d 2 with h | h
      · left
        have : d ≠ 0 := by rintro rfl; exact hn0 (Nat.eq_zero_of_zero_dvd hdn)
        omega
      · right; exact ⟨⟨hdn, hdlt⟩, h⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact ⟨one_dvd n, by omega⟩
      · exact h
  have h1n : (1 : ℕ) ∉ n.properDivisors.filter (2 ≤ ·) := by simp
  rw [hpd, Finset.sum_insert h1n, coeff_one_eq]
  -- the RHS: split off `w = n`, expand the other cofactors by the last step
  have hdv : n.divisors.filter (2 ≤ ·) =
      insert n ((n.divisors.filter (2 ≤ ·)).filter (· < n)) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hwn, -⟩, h2⟩
      rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hwn) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨⟨hwn, hn0⟩, h2⟩, h⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact ⟨⟨dvd_refl _, hn0⟩, hn⟩
      · exact h
  have hnn : n ∉ (n.divisors.filter (2 ≤ ·)).filter (· < n) := by simp
  rw [hdv, Finset.sum_insert hnn, Nat.div_self (by omega), coeff_one_eq]
  have hf1 : filt t val y n 1 ↔ ffilt t val y n := by
    unfold filt ffilt; rw [Nat.div_one]
  -- the two double sums
  have hL : ∀ d ∈ n.properDivisors.filter (2 ≤ ·),
      (if filt t val y n d ∧ cut then coeff t val X0 y d else 0) =
        -∑ w ∈ d.divisors.filter (2 ≤ ·),
          (if filt t val y n d ∧ cut ∧ ffilt t val y w then
            coeff t val X0 (y / valN val w) (d / w) else 0) := by
    intro d hd
    obtain ⟨hdp, hd2⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hdp
    have hcd : cut → X0 ≤ y / valN val d := by
      intro hc
      refine le_trans hc (div_le_div_of_nonneg_left ?_ (valN_pos val hval)
        (valN_le_of_dvd val hval hdn hn0))
      by_contra hy; push_neg at hy
      have := valN_pos val hval (n := n)
      have : y / valN val n < 0 := div_neg_of_neg_of_pos hy this
      have hc' : X0 ≤ y / valN val n := hc
      linarith
    rw [ih d hdlt hd2 y]
    by_cases hC : filt t val y n d ∧ cut
    · rw [if_pos hC]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hw : ffilt t val y w
      · rw [if_pos ⟨hw, hcd hC.2⟩, if_pos ⟨hC.1, hC.2, hw⟩]
      · rw [if_neg (fun h => hw h.1), if_neg (fun h => hw h.2.2)]
    · rw [if_neg hC, Finset.sum_eq_zero, neg_zero]
      intro w _
      rw [if_neg (fun h => hC ⟨h.1, h.2.1⟩)]
  have hR : ∀ w ∈ (n.divisors.filter (2 ≤ ·)).filter (· < n),
      (if ffilt t val y w ∧ cut then coeff t val X0 (y / valN val w) (n / w) else 0) =
        -∑ e ∈ (n / w).properDivisors,
          (if filt t val y n (w * e) ∧ cut ∧ ffilt t val y w then
            coeff t val X0 (y / valN val w) e else 0) := by
    intro w hw
    simp only [Finset.mem_filter, Nat.mem_divisors] at hw
    obtain ⟨⟨⟨hwn, -⟩, hw2⟩, hwlt⟩ := hw
    have hk2 : 2 ≤ n / w := by
      obtain ⟨k, hk⟩ := hwn
      rw [hk, Nat.mul_div_cancel_left k (by omega)]
      by_contra hc; push_neg at hc
      have : w * k ≤ w * 1 := Nat.mul_le_mul_left w (by omega)
      omega
    rw [coeff_rec t val X0 (y / valN val w) hk2]
    by_cases hC : ffilt t val y w ∧ cut
    · rw [if_pos hC]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      have h1 := filt_shift (t := t) hval (y := y) (e := e) hwn hn0
      have h2 := cut_shift hval (X0 := X0) (y := y) hwn hn0
      by_cases he : filt t val y n (w * e)
      · rw [if_pos ⟨h1.mp he, h2.mpr hC.2⟩, if_pos ⟨he, hC.2, hC.1⟩]
      · rw [if_neg (fun h => he (h1.mpr h.1)), if_neg (fun h => he h.1)]
    · rw [if_neg hC, Finset.sum_eq_zero, neg_zero]
      intro e _
      rw [if_neg (fun h => hC ⟨h.2.2, h.2.1⟩)]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  simp only [Finset.sum_neg_distrib]
  -- reindex `(d, w) ↦ (w, d/w)`
  have hsw : ∑ d ∈ n.properDivisors.filter (2 ≤ ·), ∑ w ∈ d.divisors.filter (2 ≤ ·),
      (if filt t val y n d ∧ cut ∧ ffilt t val y w then
        coeff t val X0 (y / valN val w) (d / w) else 0) =
      ∑ w ∈ (n.divisors.filter (2 ≤ ·)).filter (· < n), ∑ e ∈ (n / w).properDivisors,
        (if filt t val y n (w * e) ∧ cut ∧ ffilt t val y w then
          coeff t val X0 (y / valN val w) e else 0) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 / p.2⟩) (fun q => ⟨q.1 * q.2, q.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨d, w⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_properDivisors,
        Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨⟨hdn, hdlt⟩, hd2⟩, ⟨hwd, hd0⟩, hw2⟩ := hp
      obtain ⟨e, rfl⟩ := hwd
      have hw0 : 0 < w := by omega
      rw [Nat.mul_div_cancel_left e hw0]
      obtain ⟨k, hk⟩ := hdn
      refine ⟨⟨⟨⟨dvd_trans (dvd_mul_right w e) ⟨k, hk⟩, hn0⟩, hw2⟩, ?_⟩, ?_, ?_⟩
      · have he0 : e ≠ 0 := by rintro rfl; simp at hd0
        exact lt_of_le_of_lt (Nat.le_mul_of_pos_right w (Nat.pos_of_ne_zero he0)) hdlt
      · rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hw0]; exact dvd_mul_right e k
      · rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hw0]
        have he0 : e ≠ 0 := by rintro rfl; simp at hd0
        have : w * e < w * e * k := by rw [← hk]; exact hdlt
        have hk1 : 1 < k := by
          by_contra hc; push_neg at hc
          have : w * e * k ≤ w * e * 1 := Nat.mul_le_mul_left _ hc
          omega
        nlinarith
    · rintro ⟨w, e⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_properDivisors,
        Nat.mem_divisors] at hq ⊢
      obtain ⟨⟨⟨⟨hwn, -⟩, hw2⟩, hwlt⟩, hen, helt⟩ := hq
      obtain ⟨k, rfl⟩ := hwn
      have hw0 : 0 < w := by omega
      rw [Nat.mul_div_cancel_left k hw0] at hen helt
      have he0 : e ≠ 0 := by rintro rfl; simp at hen; omega
      refine ⟨⟨⟨Nat.mul_dvd_mul_left w hen, (Nat.mul_lt_mul_left hw0).mpr helt⟩, ?_⟩,
        ⟨dvd_mul_right w e, Nat.mul_ne_zero (by omega) he0⟩, hw2⟩
      have : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
      nlinarith
    · rintro ⟨d, w⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp
      simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      exact Nat.mul_div_cancel' hp.2.1.1
    · rintro ⟨w, e⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_filter] at hq
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Nat.mul_div_cancel_left e (by omega)
    · rintro ⟨d, w⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp
      simp only
      rw [Nat.mul_div_cancel' hp.2.1.1]
  rw [hsw]
  have hfn : (if filt t val y n 1 ∧ cut then (1 : ℤ) else 0) =
      (if ffilt t val y n ∧ cut then 1 else 0) := by
    by_cases h : ffilt t val y n ∧ cut
    · rw [if_pos ⟨hf1.mpr h.1, h.2⟩, if_pos h]
    · rw [if_neg (fun h' => h ⟨hf1.mp h'.1, h'.2⟩), if_neg h]
  rw [hfn]

end LemmaM

end
