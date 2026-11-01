module

public import Mathlib

/-!
# The jump at `X₀`, small range (`x0band_exact.py`, Appendix B.3)

Proposition 5.31(i) of the paper uses, for `2 ≤ n ≤ 10⁶`,
```
B(n) = (1/n) [ μ²(n)/2 + (1/2) ∑_{d | n, 1 < d < n} (2 μ²(d) + (1/2) λ X(d)/d) ],
X(d) = ∑_{e | d, 1 < e < d} μ²(e) e H_ord(d/e),       λ = 1.0001,
```
where `H_ord(1) = 1` and `H_ord(m) = ∑_{d | m, d < m} H_ord(d)` (ordered factorisations).
The claim is `B(n) ≤ 5/12`, with equality only at `n = 6`.

This file defines `B` exactly (`Bx`, a rational number), and a fast exact integer evaluation:
* `fdivs` computes the divisors from the factorisation (`fdivs_eq : fdivs n = n.divisors`);
* `hArr`, `xArr` tabulate `H_ord` and `X` (`hArr_spec`, `xArr_spec`);
* `x0Check n` compares `12 (20000 n μ²(n) + T(n))` with `200000 n²`, where
  `T(n) = 20000 n ∑_d (2 μ²(d) + λ X(d)/(2d))` is an integer (`Bx_eq`). So the comparison is
  exact, with no rounding at all.
-/

@[expose] public section

namespace BSCert.X0Band

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## The definitions of the paper -/

/-- Ordered factorisations: `H_ord(1) = 1`, `H_ord(m) = ∑_{d | m, d < m} H_ord(d)`
(and `H_ord(0) = 0`). -/
def Hord (n : ℕ) : ℕ :=
  if n ≤ 1 then n else ∑ d ∈ n.properDivisors.attach, Hord d.1
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

lemma Hord_eq (n : ℕ) :
    Hord n = if n ≤ 1 then n else ∑ d ∈ n.properDivisors, Hord d := by
  rw [Hord]
  split_ifs
  · rfl
  · exact Finset.sum_attach n.properDivisors Hord

/-- `μ²(n)` as a rational number. -/
def musq (n : ℕ) : ℚ := ((μ n : ℤ) : ℚ) ^ 2

/-- `X(d) = ∑_{e | d, 1 < e < d} μ²(e) e H_ord(d/e)`. -/
def X (d : ℕ) : ℚ := ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d), musq e * e * Hord (d / e)

/-- `λ = 1.0001`. -/
def lam : ℚ := 10001 / 10000

/-- `B(n)` of Proposition 5.31(i). -/
def Bx (n : ℕ) : ℚ :=
  1 / n * (musq n / 2 + 1 / 2 * ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n),
    (2 * musq d + 1 / 2 * lam * X d / d))

/-! ## Fast divisors -/

/-- The divisors of `n`, computed from the smallest prime factor. -/
def fdivs (n : ℕ) : Finset ℕ :=
  if h : n ≤ 1 then (if n = 1 then {1} else ∅) else
    let D := fdivs (n / n.minFac)
    D ∪ D.image (fun d => n.minFac * d)
decreasing_by exact Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt

lemma divisors_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    (p * m).divisors = m.divisors ∪ m.divisors.image (fun d => p * d) := by
  ext d
  simp only [Nat.mem_divisors, mem_union, mem_image]
  constructor
  · rintro ⟨hd, -⟩
    obtain ⟨k1, k2, hk1, hk2, rfl⟩ := Nat.dvd_mul.mp hd
    rcases (Nat.dvd_prime hp).mp hk1 with rfl | rfl
    · left; simpa using ⟨hk2, hm⟩
    · right; exact ⟨k2, ⟨hk2, hm⟩, rfl⟩
  · rintro (⟨hd, -⟩ | ⟨k, ⟨hk, -⟩, rfl⟩)
    · exact ⟨Dvd.dvd.mul_left hd p, mul_ne_zero hp.ne_zero hm⟩
    · exact ⟨mul_dvd_mul_left p hk, mul_ne_zero hp.ne_zero hm⟩

theorem fdivs_eq (n : ℕ) : fdivs n = n.divisors := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fdivs]
    split_ifs with h1 h2
    · subst h2; simp
    · have : n = 0 := by omega
      subst this; simp
    · simp only
      have hp := Nat.minFac_prime (show n ≠ 1 by omega)
      have hlt : n / n.minFac < n := Nat.div_lt_self (by omega) hp.one_lt
      rw [ih _ hlt]
      have hm : n / n.minFac ≠ 0 := by
        have := Nat.div_pos (Nat.minFac_le (by omega)) hp.pos
        omega
      conv_rhs => rw [← Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [divisors_prime_mul hp hm]

/-! ## Tables of `H_ord` and `X` -/

/-- Squarefree indicator. -/
def sq (n : ℕ) : ℕ := if Squarefree n then 1 else 0

lemma musq_eq (n : ℕ) : musq n = (sq n : ℚ) := by
  unfold musq sq
  have := congrArg (fun z : ℤ => (z : ℚ)) (moebius_sq (n := n))
  push_cast at this
  rw [this]; split_ifs <;> simp

/-- The next value of `H_ord`, given the table of the previous values. -/
def nextH (a : Array ℕ) : ℕ :=
  let m := a.size
  if m ≤ 1 then m else ∑ d ∈ (fdivs m).filter (· < m), a.getD d 0

/-- Extend a table of `H_ord` by `f` entries. -/
def buildH : ℕ → Array ℕ → Array ℕ
  | 0, a => a
  | f + 1, a => buildH f (a.push (nextH a))

lemma buildH_spec : ∀ f (a : Array ℕ), (∀ i < a.size, a.getD i 0 = Hord i) →
    (buildH f a).size = a.size + f ∧ ∀ i < (buildH f a).size, (buildH f a).getD i 0 = Hord i := by
  intro f
  induction f with
  | zero => intro a ha; exact ⟨rfl, ha⟩
  | succ f ih =>
    intro a ha
    have hpush : ∀ i < (a.push (nextH a)).size, (a.push (nextH a)).getD i 0 = Hord i := by
      intro i hi
      rw [Array.size_push] at hi
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      split_ifs with heq
      · subst heq
        simp only [Option.getD_some]
        unfold nextH
        simp only
        rw [Hord_eq]
        split_ifs with h1
        · rfl
        · rw [fdivs_eq]
          have : (a.size.divisors.filter (· < a.size)) = a.size.properDivisors := by
            ext d
            simp only [mem_filter, Nat.mem_divisors, Nat.mem_properDivisors]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
          rw [this]
          apply sum_congr rfl
          intro d hd
          exact ha d (Nat.mem_properDivisors.mp hd).2
      · have hi' : i < a.size := by omega
        have := ha i hi'
        rw [Array.getD_eq_getD_getElem?] at this
        exact this
    obtain ⟨h1, h2⟩ := ih _ hpush
    refine ⟨?_, h2⟩
    show (buildH f (a.push (nextH a))).size = _
    rw [h1, Array.size_push]; ring

/-- Range of the `H_ord` table. -/
def HL : ℕ := 250000

/-- The table of `H_ord(m)`, `m ≤ HL`. -/
def hArr : Array ℕ := buildH (HL + 1) #[]

lemma hArr_spec {i : ℕ} (hi : i ≤ HL) : hArr.getD i 0 = Hord i := by
  have := buildH_spec (HL + 1) #[] (by simp)
  unfold hArr
  exact this.2 i (by rw [this.1]; simp; omega)

/-- Fast `X(d)`, reading `H_ord` from the table. -/
def xFast (d : ℕ) : ℕ :=
  ∑ e ∈ (fdivs d).filter (fun e => 1 < e ∧ e < d), sq e * e * hArr.getD (d / e) 0

/-- Range of the `X` table. -/
def XL : ℕ := 500000

/-- The table of `X(d)`, `d ≤ XL`. -/
def xArr : Array ℕ := Array.ofFn (n := XL + 1) fun i => xFast i

lemma xFast_eq {d : ℕ} (hd : d ≤ XL) : (xFast d : ℚ) = X d := by
  unfold xFast X
  rw [fdivs_eq]
  push_cast
  apply sum_congr rfl
  intro e he
  simp only [mem_filter, Nat.mem_divisors] at he
  rw [musq_eq, hArr_spec]
  have : d / e ≤ d / 2 := Nat.div_le_div_left he.2.1 (by norm_num)
  unfold HL; unfold XL at hd; omega

lemma xArr_spec {d : ℕ} (hd : d ≤ XL) : (xArr.getD d 0 : ℚ) = X d := by
  unfold xArr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show d < XL + 1 by omega, dite_true, Option.getD_some]
  exact xFast_eq hd

/-! ## The exact check -/

/-- `T(n) = ∑_{d | n, 1 < d < n} (40000 n μ²(d) + 10001 X(d) (n/d))`. -/
def Tn (n : ℕ) : ℕ :=
  ∑ d ∈ (fdivs n).filter (fun d => 1 < d ∧ d < n),
    (40000 * n * sq d + 10001 * xArr.getD d 0 * (n / d))

/-- The check: `12 (20000 n μ²(n) + T(n)) ≤ 200000 n²`, strictly unless `n = 6`. -/
def x0Check (n : ℕ) : Bool :=
  let L := 12 * (20000 * n * sq n + Tn n)
  let R := 200000 * n * n
  if n = 6 then decide (L = R) else decide (L < R)

lemma two_mul_le_of_dvd_of_lt {d n : ℕ} (h : d ∣ n) (hlt : d < n) : 2 * d ≤ n := by
  obtain ⟨k, rfl⟩ := h
  have hk : 2 ≤ k := by
    by_contra hc
    interval_cases k <;> simp_all
  nlinarith

lemma Tn_eq {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 2 * XL) :
    (Tn n : ℚ) = 20000 * n * ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n),
      (2 * musq d + 1 / 2 * lam * X d / d) := by
  unfold Tn
  rw [fdivs_eq, mul_sum]
  push_cast
  apply sum_congr rfl
  intro d hd
  simp only [mem_filter, Nat.mem_divisors] at hd
  have hdXL : d ≤ XL := by
    have := two_mul_le_of_dvd_of_lt hd.1.1 hd.2.2
    omega
  have hd0 : d ≠ 0 := by omega
  rw [Nat.cast_div hd.1.1 (by exact_mod_cast hd0), xArr_spec hdXL, musq_eq]
  unfold lam
  have : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  field_simp
  ring

/-- `B(n) = (20000 n μ²(n) + T(n)) / (40000 n²)`. -/
lemma Bx_eq {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 2 * XL) :
    Bx n = (20000 * n * (sq n : ℚ) + (Tn n : ℚ)) / (40000 * n * n) := by
  rw [Tn_eq hn hn', Bx, musq_eq]
  have : (n : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem Bx_of_check {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 2 * XL) (h : x0Check n = true) :
    Bx n ≤ 5 / 12 ∧ (n ≠ 6 → Bx n < 5 / 12) ∧ (n = 6 → Bx n = 5 / 12) := by
  rw [Bx_eq hn hn']
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : (0 : ℚ) < 40000 * n * n := by positivity
  unfold x0Check at h
  simp only at h
  split_ifs at h with h6
  · simp only [decide_eq_true_eq] at h
    have h' : (12 : ℚ) * (20000 * n * sq n + Tn n) = 200000 * n * n := by exact_mod_cast h
    have heq : (20000 * n * (sq n : ℚ) + (Tn n : ℚ)) / (40000 * n * n) = 5 / 12 := by
      rw [div_eq_iff hden.ne']; linarith
    exact ⟨heq.le, fun h => absurd h6 h, fun _ => heq⟩
  · simp only [decide_eq_true_eq] at h
    have h' : (12 : ℚ) * (20000 * n * sq n + Tn n) < 200000 * n * n := by exact_mod_cast h
    have hlt : (20000 * n * (sq n : ℚ) + (Tn n : ℚ)) / (40000 * n * n) < 5 / 12 := by
      rw [div_lt_iff₀ hden]; linarith
    exact ⟨hlt.le, fun _ => hlt, fun h => absurd h h6⟩

/-- The check over a range of `n`. -/
def checkAll : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, n => x0Check n && checkAll f (n + 1)

lemma checkAll_spec : ∀ f n, checkAll f n = true → ∀ k, n ≤ k → k < n + f → x0Check k = true := by
  intro f
  induction f with
  | zero => intro n _ k h1 h2; omega
  | succ f ih =>
    intro n h k hk1 hk2
    simp only [checkAll, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt
    · exact h.1
    · exact ih (n + 1) h.2 k hlt (by omega)

end BSCert.X0Band

namespace BSCert.X0Band

/-- The analytic tail of the proof of Proposition 5.31(i), printed by `x0band_exact.py` at
`n = 10⁶` (value `0.137383`): for every real `n ≥ 10⁶`,
`(1/2 + 1.64 √n)/n + (1/4) · 7.4915 · 2^{0.2} n^{-0.2} ≤ 0.1375 < 0.14`. -/
theorem x0_tail_bound {n : ℝ} (hn : 10 ^ 6 ≤ n) :
    (1 / 2 + 1.64 * Real.sqrt n) / n + 1 / 4 * 7.4915 * (2 : ℝ) ^ (0.2 : ℝ) * n ^ (-0.2 : ℝ)
      ≤ 0.1375 := by
  have hn0 : 0 < n := by linarith
  -- first term
  have hs : 1000 ≤ Real.sqrt n := by
    rw [show (1000 : ℝ) = Real.sqrt (10 ^ 6) by
      rw [show (10 : ℝ) ^ 6 = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hn
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have h1 : (1 / 2 + 1.64 * Real.sqrt n) / n ≤ 0.0016405 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  -- second term: `2^{0.2} n^{-0.2} = (2/n)^{0.2} ≤ 0.0725`
  have e : (2 : ℝ) ^ (0.2 : ℝ) * n ^ (-0.2 : ℝ) = (2 / n) ^ (0.2 : ℝ) := by
    rw [Real.rpow_neg hn0.le, Real.div_rpow (by norm_num) hn0.le, div_eq_mul_inv]
  set t := (2 / n) ^ (0.2 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht5 : t ^ 5 = 2 / n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h2n : 2 / n ≤ 2 / 10 ^ 6 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have htle : t ≤ 0.0725 := by
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (by norm_num) (show (5 : ℕ) ≠ 0 by norm_num)
    rw [ht5] at this
    norm_num at this h2n
    linarith
  have h2 : 1 / 4 * 7.4915 * (2 : ℝ) ^ (0.2 : ℝ) * n ^ (-0.2 : ℝ) ≤ 1 / 4 * 7.4915 * 0.0725 := by
    rw [mul_assoc (1 / 4 * 7.4915), e]
    exact mul_le_mul_of_nonneg_left htle (by norm_num)
  norm_num at h2 ⊢
  linarith

end BSCert.X0Band
