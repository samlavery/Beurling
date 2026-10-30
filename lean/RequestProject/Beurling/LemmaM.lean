module

public import Mathlib

/-!
# Lemma 5.5 (Lemma M): the sharp coefficients

For a start `y`, the sharp resolvent has coefficients `c_n(y)` given by `c_1 = 1` and

  `c_n = - ∑_{d ∣ n, d < n} 1[τ_{n/d} · n < y] · 1[y/n ≥ X₀⁻] · c_d`,

where `τ_w = max_{p ∣ w} t(p)` for a weight `t` on the primes. Lemma M says

  `c_n(y) = μ(n) χ(n) 1[y/n ≥ X₀⁻]`,

where `χ(n) = 1` iff `n` is squarefree and `t(p) · ∏_{q ∣ n, q ⪰ p} q < y` for every prime
`p ∣ n`; here `⪰` is the order by `t`, with ties broken by a fixed order.

## Setting

The combinatorics only involves the free commutative monoid on the primes, so we label the
Beurling primes by the rational primes: an element of the system is a positive integer `n`, and
its *value* is `valN val n = ∏ p^k ∥ n, val(p)^k`, for an arbitrary value map `val ≥ 1` on the
labels. The weight `t > 0` is arbitrary; ties are broken by the label, through the rank
`rk t p = (t p, p)` in lexicographic order. The condition `τ_{n/d} · n < y` is written as
`∀ p ∣ n/d, t(p) · n < y` (the same thing, since `n/d > 1`).
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace LemmaM

variable (t val : ℕ → ℝ)

/-- The decision rank: order by `t`, ties broken by the label. -/
def rk (p : ℕ) : Lex (ℝ × ℕ) := toLex (t p, p)

/-- The value of a squarefree element given by its set of prime labels. -/
noncomputable def valS (A : Finset ℕ) : ℝ := ∏ p ∈ A, val p

/-- The value of an element `n` of the system. -/
noncomputable def valN (n : ℕ) : ℝ := n.factorization.prod fun p k => val p ^ k

/-- The stripping condition on a set of primes `D`: `t(p) · ∏_{q ∈ D, q ⪰ p} q < y` for all
`p ∈ D`. -/
def chiS (y : ℝ) (D : Finset ℕ) : Prop :=
  ∀ p ∈ D, t p * valS val (D.filter fun q => rk t p ≤ rk t q) < y

/-- `χ_y^t(n)`. -/
def chi (y : ℝ) (n : ℕ) : Prop := Squarefree n ∧ chiS t val y n.primeFactors

/-- The landing filter of the last step `d → n`: `τ_{n/d} · n < y`. -/
def filt (y : ℝ) (n d : ℕ) : Prop := ∀ p ∈ (n / d).primeFactors, t p * valN val n < y

/-- The sharp coefficients `c_n(y)`. -/
noncomputable def coeff (X0 y : ℝ) (n : ℕ) : ℤ :=
  if n ≤ 1 then (if n = 1 then 1 else 0) else
    - ∑ d ∈ n.properDivisors.attach,
        (open scoped Classical in
          if filt t val y n d ∧ X0 ≤ y / valN val n then coeff X0 y d else 0)
termination_by n
decreasing_by exact Nat.mem_properDivisors.mp d.2 |>.2

open scoped Classical


/-! ### Values -/

lemma moebius_eq_card {d : ℕ} (hd : Squarefree d) : μ d = (-1) ^ d.primeFactors.card := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hd.ne_zero).mpr hd]
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

lemma one_le_prod_real {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ s, f i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

lemma valN_one : valN val 1 = 1 := by simp [valN]

lemma valN_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    valN val (a * b) = valN val a * valN val b := by
  unfold valN
  rw [Nat.factorization_mul ha hb, Finsupp.prod_add_index']
  · intro p; simp
  · intro p k l; rw [pow_add]

lemma one_le_valN (hval : ∀ p, p.Prime → 1 ≤ val p) {n : ℕ} :
    1 ≤ valN val n := by
  unfold valN Finsupp.prod
  apply one_le_prod_real
  intro p hp
  rw [Nat.support_factorization] at hp
  exact one_le_pow₀ (hval p (Nat.prime_of_mem_primeFactors hp))

lemma valN_pos (hval : ∀ p, p.Prime → 1 ≤ val p) {n : ℕ} : 0 < valN val n :=
  lt_of_lt_of_le one_pos (one_le_valN val hval)

lemma valN_le_of_dvd (hval : ∀ p, p.Prime → 1 ≤ val p) {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) :
    valN val d ≤ valN val n := by
  obtain ⟨e, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hn
  have he0 : e ≠ 0 := right_ne_zero_of_mul hn
  rw [valN_mul val hd0 he0]
  have h1 := one_le_valN val hval (n := e)
  have h2 := valN_pos val hval (n := d)
  nlinarith

lemma valN_of_squarefree {n : ℕ} (hn : Squarefree n) : valN val n = valS val n.primeFactors := by
  unfold valN valS Finsupp.prod
  rw [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have h1 := hn.natFactorization_le_one p
  have h2 : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization]))
  simp only [show n.factorization p = 1 by omega, pow_one]

lemma valS_nonneg {A : Finset ℕ} (hA : ∀ p ∈ A, 1 ≤ val p) : 0 ≤ valS val A :=
  Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hA p hp))

lemma valS_mono {A B : Finset ℕ} (hB : ∀ p ∈ B, 1 ≤ val p) (hAB : A ⊆ B) :
    valS val A ≤ valS val B := by
  unfold valS
  rw [← Finset.prod_sdiff hAB]
  have h1 : 1 ≤ ∏ p ∈ B \ A, val p :=
    one_le_prod_real (fun p hp => hB p (Finset.mem_sdiff.mp hp).1)
  have h2 : 0 ≤ ∏ p ∈ A, val p :=
    Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hB p (hAB hp)))
  nlinarith

/-! ### The squarefree cancellation -/

lemma rk_le_iff {p q : ℕ} : rk t p ≤ rk t q ↔ t p < t q ∨ (t p = t q ∧ p ≤ q) := by
  unfold rk; exact Prod.Lex.toLex_le_toLex

lemma rk_injective : Function.Injective (rk t) := by
  intro p q h; unfold rk at h; have := congrArg (fun x => (ofLex x).2) h; simpa using this

lemma t_le_of_rk_le {p q : ℕ} (h : rk t p ≤ rk t q) : t p ≤ t q := by
  rcases (rk_le_iff t).mp h with h | h
  · exact h.le
  · exact h.1.le

lemma chiS_insert {q : ℕ} {D : Finset ℕ} (hq : q ∉ D) (hmax : ∀ x ∈ D, rk t x ≤ rk t q)
    (hvq : 0 < val q) (y : ℝ) :
    chiS t val y (insert q D) ↔ t q * val q < y ∧ chiS t val (y / val q) D := by
  have hfq : (insert q D).filter (fun x => rk t q ≤ rk t x) = {q} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hle⟩
      · exact hx
      · exact absurd (rk_injective t (le_antisymm (hmax x hx) hle) ▸ hx) hq
    · rintro rfl; exact ⟨Or.inl rfl, le_rfl⟩
  have hfp : ∀ p ∈ D, (insert q D).filter (fun x => rk t p ≤ rk t x) =
      insert q (D.filter (fun x => rk t p ≤ rk t x)) := by
    intro p hp
    rw [Finset.filter_insert, if_pos (hmax p hp)]
  unfold chiS
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h q (Finset.mem_insert_self q D)
      rw [hfq] at this; simpa [valS] using this
    · intro p hp
      have := h p (Finset.mem_insert_of_mem hp)
      rw [hfp p hp] at this
      unfold valS at this ⊢
      rw [Finset.prod_insert (fun h' => hq (Finset.mem_filter.mp h').1)] at this
      rw [lt_div_iff₀ hvq]
      linarith
  · rintro ⟨h1, h2⟩ p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rw [hfq]; simpa [valS] using h1
    · have := h2 p hp
      rw [hfp p hp]
      unfold valS at this ⊢
      rw [Finset.prod_insert (fun h' => hq (Finset.mem_filter.mp h').1)]
      rw [lt_div_iff₀ hvq] at this
      linarith

/-- The finite-set form of the cancellation, for a squarefree element with prime set `A`. -/
lemma keyS (A : Finset ℕ) (ht : ∀ p ∈ A, 0 < t p) (hval : ∀ p ∈ A, 1 ≤ val p)
    (hA : A.Nonempty) (y : ℝ) :
    ∑ D ∈ A.powerset, ((-1 : ℤ) ^ D.card * (if chiS t val y D then 1 else 0) *
      (if D = A ∨ ∀ p ∈ A \ D, t p * valS val A < y then 1 else 0)) = 0 := by
  classical
  revert ht hval hA y
  refine Finset.induction_on_max_value (rk t) A ?_ ?_
  · intro _ _ hA _; exact absurd hA Finset.not_nonempty_empty
  intro q s hq hmax ih ht hval _ y
  have hvq : 0 < val q := lt_of_lt_of_le one_pos (hval q (Finset.mem_insert_self q s))
  have htq : 0 < t q := ht q (Finset.mem_insert_self q s)
  have hvals : ∀ p ∈ s, 1 ≤ val p := fun p hp => hval p (Finset.mem_insert_of_mem hp)
  have hV : valS val (insert q s) = val q * valS val s := by
    unfold valS; rw [Finset.prod_insert hq]
  rw [Finset.sum_powerset_insert hq]
  -- the first sum
  have hfirst : ∀ D ∈ s.powerset, ((-1 : ℤ) ^ D.card * (if chiS t val y D then 1 else 0) *
      (if D = insert q s ∨ ∀ p ∈ insert q s \ D, t p * valS val (insert q s) < y then 1 else 0))
      = (if t q * valS val (insert q s) < y then 1 else 0) * (-1 : ℤ) ^ D.card := by
    intro D hD
    rw [Finset.mem_powerset] at hD
    have hqD : q ∉ D := fun h => hq (hD h)
    have hne : D ≠ insert q s := fun h => hqD (h ▸ Finset.mem_insert_self q s)
    have hbr : (D = insert q s ∨ ∀ p ∈ insert q s \ D, t p * valS val (insert q s) < y) ↔
        t q * valS val (insert q s) < y := by
      constructor
      · rintro (h | h)
        · exact absurd h hne
        · exact h q (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self q s, hqD⟩)
      · intro h
        right
        intro p hp
        obtain ⟨hpA, -⟩ := Finset.mem_sdiff.mp hp
        have htp : t p ≤ t q := by
          rcases Finset.mem_insert.mp hpA with rfl | hps
          · exact le_rfl
          · exact t_le_of_rk_le t (hmax p hps)
        have := valS_nonneg val hval
        nlinarith
    by_cases hc : t q * valS val (insert q s) < y
    · have hchi : chiS t val y D := by
        intro p hp
        have htp : t p ≤ t q := t_le_of_rk_le t (hmax p (hD hp))
        have hsub : D.filter (fun x => rk t p ≤ rk t x) ⊆ insert q s :=
          (Finset.filter_subset _ _).trans (hD.trans (Finset.subset_insert q s))
        have h1 := valS_mono val hval hsub
        have h2 := valS_nonneg val (A := D.filter (fun x => rk t p ≤ rk t x))
          (fun x hx => hval x (hsub hx))
        calc t p * valS val (D.filter (fun x => rk t p ≤ rk t x))
            ≤ t q * valS val (D.filter (fun x => rk t p ≤ rk t x)) :=
              mul_le_mul_of_nonneg_right htp h2
          _ ≤ t q * valS val (insert q s) := mul_le_mul_of_nonneg_left h1 htq.le
          _ < y := hc
      rw [if_pos hchi, if_pos (hbr.mpr hc), if_pos hc]; ring
    · rw [if_neg (fun h => hc (hbr.mp h)), if_neg hc]; ring
  -- the second sum
  have hsecond : ∀ D ∈ s.powerset, ((-1 : ℤ) ^ (insert q D).card *
      (if chiS t val y (insert q D) then 1 else 0) *
      (if insert q D = insert q s ∨ ∀ p ∈ insert q s \ insert q D,
        t p * valS val (insert q s) < y then 1 else 0))
      = - ((if t q * val q < y then 1 else 0) * ((-1 : ℤ) ^ D.card *
          (if chiS t val (y / val q) D then 1 else 0) *
          (if D = s ∨ ∀ p ∈ s \ D, t p * valS val s < y / val q then 1 else 0))) := by
    intro D hD
    rw [Finset.mem_powerset] at hD
    have hqD : q ∉ D := fun h => hq (hD h)
    rw [Finset.card_insert_of_notMem hqD]
    have hchi := chiS_insert t val hqD (fun x hx => hmax x (hD hx)) hvq y
    have hbr : (insert q D = insert q s ∨ ∀ p ∈ insert q s \ insert q D,
        t p * valS val (insert q s) < y) ↔
        (D = s ∨ ∀ p ∈ s \ D, t p * valS val s < y / val q) := by
      have e1 : insert q D = insert q s ↔ D = s := by
        constructor
        · intro h
          rw [← Finset.erase_insert hqD, h, Finset.erase_insert hq]
        · rintro rfl; rfl
      have e2 : insert q s \ insert q D = s \ D := by
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hq]
      rw [e1, e2, hV]
      apply or_congr Iff.rfl
      apply forall₂_congr
      intro p _
      rw [lt_div_iff₀ hvq]
      constructor <;> intro h <;> linarith
    by_cases h1 : t q * val q < y
    · by_cases h2 : chiS t val (y / val q) D
      · have : chiS t val y (insert q D) := hchi.mpr ⟨h1, h2⟩
        rw [if_pos this, if_pos h1, if_pos h2]
        by_cases h3 : D = s ∨ ∀ p ∈ s \ D, t p * valS val s < y / val q
        · rw [if_pos (hbr.mpr h3), if_pos h3]; ring
        · rw [if_neg (fun h => h3 (hbr.mp h)), if_neg h3]; ring
      · have : ¬ chiS t val y (insert q D) := fun h => h2 (hchi.mp h).2
        rw [if_neg this, if_neg h2]; ring
    · have : ¬ chiS t val y (insert q D) := fun h => h1 (hchi.mp h).1
      rw [if_neg this, if_neg h1]; ring
  rw [Finset.sum_congr rfl hfirst, Finset.sum_congr rfl hsecond, ← Finset.mul_sum,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [chiS, valS]
  · rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hsne,
      ih (fun p hp => ht p (Finset.mem_insert_of_mem hp)) hvals hsne (y / val q)]
    ring

/-- Lemma M, squarefree case of the recursion. -/
lemma key_sqfree (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p)
    (y : ℝ) {n : ℕ} (hn : 1 < n) (hsq : Squarefree n) :
    ∑ d ∈ n.properDivisors, ((if filt t val y n d then 1 else 0) * μ d *
      (if chi t val y d then 1 else 0)) = - (μ n * (if chi t val y n then 1 else 0)) := by
  have hn0 : n ≠ 0 := by omega
  have hAprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hAne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  have hkey := keyS t val n.primeFactors (fun p hp => ht p (hAprime p hp))
    (fun p hp => hval p (hAprime p hp)) hAne y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self n.primeFactors)] at hkey
  have hterm : (-1 : ℤ) ^ n.primeFactors.card * (if chiS t val y n.primeFactors then 1 else 0) *
      (if n.primeFactors = n.primeFactors ∨ ∀ p ∈ n.primeFactors \ n.primeFactors,
        t p * valS val n.primeFactors < y then 1 else 0) =
      μ n * (if chi t val y n then 1 else 0) := by
    rw [moebius_eq_card hsq, if_pos (Or.inl rfl)]
    simp [chi, hsq]
  have hbij : ∑ d ∈ n.properDivisors, ((if filt t val y n d then 1 else 0) * μ d *
      (if chi t val y d then 1 else 0)) =
      ∑ D ∈ n.primeFactors.powerset.erase n.primeFactors, ((-1 : ℤ) ^ D.card *
        (if chiS t val y D then 1 else 0) *
        (if D = n.primeFactors ∨ ∀ p ∈ n.primeFactors \ D,
          t p * valS val n.primeFactors < y then 1 else 0)) := by
    apply Finset.sum_nbij' (fun d => d.primeFactors) (fun D => ∏ p ∈ D, p)
    · intro d hd
      obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
      have hdsq := hsq.squarefree_of_dvd hdn
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr (Nat.primeFactors_mono hdn hn0)⟩
      intro h
      have := Nat.prod_primeFactors_of_squarefree hdsq
      rw [h, Nat.prod_primeFactors_of_squarefree hsq] at this
      omega
    · intro D hD
      obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hD
      rw [Finset.mem_powerset] at hsub
      rw [Nat.mem_properDivisors]
      have hdvd : ∏ p ∈ D, p ∣ n := by
        conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
      refine ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) ?_⟩
      intro h; apply hne
      rw [← Nat.primeFactors_prod (fun p hp => hAprime p (hsub hp)), h]
    · intro d hd
      exact Nat.prod_primeFactors_of_squarefree
        (hsq.squarefree_of_dvd (Nat.mem_properDivisors.mp hd).1)
    · intro D hD
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2
      exact Nat.primeFactors_prod (fun p hp => hAprime p (hsub hp))
    · intro d hd
      obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
      have hdsq := hsq.squarefree_of_dvd hdn
      have hne : d.primeFactors ≠ n.primeFactors := by
        intro h
        have := Nat.prod_primeFactors_of_squarefree hdsq
        rw [h, Nat.prod_primeFactors_of_squarefree hsq] at this
        omega
      have hdiv : (n / d).primeFactors = n.primeFactors \ d.primeFactors := by
        have he : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
        have hd0 : d ≠ 0 := by rintro rfl; simp at hdn; omega
        have he0 : n / d ≠ 0 := by
          intro h; rw [h, mul_zero] at he; omega
        have hsq' : Squarefree (d * (n / d)) := he ▸ hsq
        have hcop := Nat.coprime_of_squarefree_mul hsq'
        conv_rhs => rw [he, Nat.primeFactors_mul hd0 he0]
        exact (Finset.union_sdiff_cancel_left hcop.disjoint_primeFactors).symm
      have hfilt : filt t val y n d ↔ (d.primeFactors = n.primeFactors ∨
          ∀ p ∈ n.primeFactors \ d.primeFactors, t p * valS val n.primeFactors < y) := by
        unfold filt
        rw [hdiv, valN_of_squarefree val hsq]
        constructor
        · exact fun h => Or.inr h
        · rintro (h | h)
          · exact absurd h hne
          · exact h
      have hchi : chi t val y d ↔ chiS t val y d.primeFactors := by
        unfold chi; exact ⟨fun h => h.2, fun h => ⟨hdsq, h⟩⟩
      rw [moebius_eq_card hdsq]
      by_cases h1 : filt t val y n d
      · rw [if_pos h1, if_pos (hfilt.mp h1)]
        by_cases h2 : chi t val y d
        · rw [if_pos h2, if_pos (hchi.mp h2)]; ring
        · rw [if_neg h2, if_neg (fun h => h2 (hchi.mpr h))]; ring
      · rw [if_neg h1, if_neg (fun h => h1 (hfilt.mpr h))]; ring
  rw [hbij]
  linarith

/-! ### The non-squarefree cancellation -/

lemma chiS_toggle (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p) {y : ℝ}
    {D D' : Finset ℕ} {s : ℕ} (hs : s.Prime) (hD' : ∀ p ∈ D', p.Prime)
    (hsame : ∀ p, p ≠ s → (p ∈ D' ↔ p ∈ D)) (hbound : t s * valS val D' < y)
    (hD : chiS t val y D) : chiS t val y D' := by
  intro p hp
  by_cases hps : rk t s < rk t p
  · have hpne : p ≠ s := fun h => by rw [h] at hps; exact lt_irrefl _ hps
    have hfil : D'.filter (fun x => rk t p ≤ rk t x) = D.filter (fun x => rk t p ≤ rk t x) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hle⟩
        have hxs : x ≠ s := fun h => by rw [h] at hle; exact absurd hps (not_lt.mpr hle)
        exact ⟨(hsame x hxs).mp hx, hle⟩
      · rintro ⟨hx, hle⟩
        have hxs : x ≠ s := fun h => by rw [h] at hle; exact absurd hps (not_lt.mpr hle)
        exact ⟨(hsame x hxs).mpr hx, hle⟩
    rw [hfil]
    exact hD p ((hsame p hpne).mp hp)
  · push_neg at hps
    have htp : t p ≤ t s := t_le_of_rk_le t hps
    have hvalD' : ∀ x ∈ D', 1 ≤ val x := fun x hx => hval x (hD' x hx)
    have h1 := valS_mono val hvalD' (Finset.filter_subset (fun x => rk t p ≤ rk t x) D')
    have h2 := valS_nonneg val (A := D'.filter (fun x => rk t p ≤ rk t x))
      (fun x hx => hvalD' x (Finset.mem_filter.mp hx).1)
    have hts := ht s hs
    calc t p * valS val (D'.filter (fun x => rk t p ≤ rk t x))
        ≤ t s * valS val (D'.filter (fun x => rk t p ≤ rk t x)) :=
          mul_le_mul_of_nonneg_right htp h2
      _ ≤ t s * valS val D' := mul_le_mul_of_nonneg_left h1 hts.le
      _ < y := hbound

/-- Toggling the prime `s` (with `s² ∣ n`) into a squarefree divisor `e` with `s ∤ e`. -/
lemma toggleA {n e s : ℕ} (hs : s.Prime) (hss : s * s ∣ n) (hn0 : n ≠ 0) (hen : e ∣ n)
    (hesq : Squarefree e) (hse : ¬ s ∣ e) :
    e * s ∣ n ∧ Squarefree (e * s) ∧ μ (e * s) = - μ e ∧
      (n / (e * s)).primeFactors = (n / e).primeFactors ∧ s ∈ (n / e).primeFactors ∧
      (e * s).primeFactors = insert s e.primeFactors := by
  have hcop : Nat.Coprime s e := (Nat.Prime.coprime_iff_not_dvd hs).mpr hse
  have he0 : e ≠ 0 := by rintro rfl; exact hse (dvd_zero s)
  have hsn : s ∣ n := (Dvd.intro s rfl).trans hss
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hen hsn
  · exact Nat.squarefree_mul_iff.mpr ⟨hcop.symm, hesq, hs.prime.squarefree⟩
  · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm,
      ArithmeticFunction.moebius_apply_prime hs]
    ring
  · -- `m = n / e` is divisible by `s²`
    obtain ⟨m, rfl⟩ := hen
    have hm0 : m ≠ 0 := right_ne_zero_of_mul hn0
    have hssm : s * s ∣ m := by
      have hc2 : Nat.Coprime (s * s) e := Nat.Coprime.mul_left hcop hcop
      exact hc2.dvd_of_dvd_mul_left hss
    rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero he0),
      Nat.mul_div_mul_left m s (Nat.pos_of_ne_zero he0)]
    obtain ⟨k, hk⟩ := hssm
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
    rw [hk, show s * s * k = s * (s * k) by ring, Nat.mul_div_cancel_left _ hs.pos]
    simp [Nat.primeFactors_mul, hs.ne_zero, hk0, hs.primeFactors]
  · obtain ⟨m, rfl⟩ := hen
    have hm0 : m ≠ 0 := right_ne_zero_of_mul hn0
    rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero he0)]
    have hc2 : Nat.Coprime (s * s) e := Nat.Coprime.mul_left hcop hcop
    have hssm : s * s ∣ m := hc2.dvd_of_dvd_mul_left hss
    exact Nat.mem_primeFactors.mpr ⟨hs, (Dvd.intro s rfl).trans hssm, hm0⟩
  · rw [Nat.primeFactors_mul he0 hs.ne_zero, hs.primeFactors]
    ext x; simp

lemma pair_cancel (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p) (y : ℝ)
    {n e s : ℕ} (hs : s.Prime) (hss : s * s ∣ n) (hn0 : n ≠ 0) (hen : e ∣ n)
    (hesq : Squarefree e) (hse : ¬ s ∣ e) :
    (if filt t val y n e then (1 : ℤ) else 0) * μ e * (if chi t val y e then 1 else 0) +
      (if filt t val y n (e * s) then (1 : ℤ) else 0) * μ (e * s) *
        (if chi t val y (e * s) then 1 else 0) = 0 := by
  obtain ⟨hdvd, hsq', hmu, hpf, hsmem, hpfs⟩ := toggleA hs hss hn0 hen hesq hse
  have hfilt : filt t val y n (e * s) ↔ filt t val y n e := by unfold filt; rw [hpf]
  have hpr : ∀ m : ℕ, ∀ p ∈ m.primeFactors, p.Prime := fun m p hp => Nat.prime_of_mem_primeFactors hp
  by_cases hf : filt t val y n e
  · have hbound : t s * valN val n < y := hf s hsmem
    have hts := ht s hs
    have hchi : chi t val y (e * s) ↔ chi t val y e := by
      constructor
      · rintro ⟨_, h⟩
        refine ⟨hesq, chiS_toggle t val ht hval hs (hpr e) ?_ ?_ h⟩
        · intro p hp; rw [hpfs]; simp [hp]
        · rw [← valN_of_squarefree val hesq]
          have := valN_le_of_dvd val hval hen hn0
          nlinarith
      · rintro ⟨_, h⟩
        refine ⟨hsq', chiS_toggle t val ht hval hs (hpr (e * s)) ?_ ?_ h⟩
        · intro p hp; rw [hpfs]; simp [hp]
        · rw [← valN_of_squarefree val hsq']
          have := valN_le_of_dvd val hval hdvd hn0
          nlinarith
    rw [if_pos hf, if_pos (hfilt.mpr hf), hmu]
    by_cases hc : chi t val y e
    · rw [if_pos hc, if_pos (hchi.mpr hc)]; ring
    · rw [if_neg hc, if_neg (fun h => hc (hchi.mp h))]; ring
  · rw [if_neg hf, if_neg (fun h => hf (hfilt.mp h))]; ring

/-- Lemma M, non-squarefree case of the recursion. -/
lemma key_not_sqfree (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p)
    (y : ℝ) {n : ℕ} (hn : 1 ≤ n) (hsq : ¬ Squarefree n) :
    ∑ d ∈ n.properDivisors, ((if filt t val y n d then 1 else 0) * μ d *
      (if chi t val y d then 1 else 0)) = 0 := by
  have hn0 : n ≠ 0 := by omega
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push_neg at hsq
  obtain ⟨s, hs, hss⟩ := hsq
  set f : ℕ → ℤ := fun d =>
    (if filt t val y n d then (1 : ℤ) else 0) * μ d * (if chi t val y d then 1 else 0) with hf
  have hnsq : ¬ Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]; push_neg; exact ⟨s, hs, hss⟩
  let g : ℕ → ℕ := fun d => if Squarefree d then (if s ∣ d then d / s else d * s) else d
  have hdiv_case : ∀ d, Squarefree d → s ∣ d → ¬ s ∣ d / s ∧ d / s * s = d := by
    intro d hdsq hsd
    obtain ⟨k, rfl⟩ := hsd
    rw [Nat.mul_div_cancel_left k hs.pos]
    refine ⟨?_, mul_comm k s⟩
    intro hk
    obtain ⟨j, rfl⟩ := hk
    have := hdsq s ⟨j, by ring⟩
    exact hs.not_isUnit this
  apply Finset.sum_involution (fun d _ => g d)
  · intro d hd
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
    show f d + f (g d) = 0
    by_cases hdsq : Squarefree d
    · by_cases hsd : s ∣ d
      · obtain ⟨hse, hes⟩ := hdiv_case d hdsq hsd
        have hen : d / s ∣ n := (Nat.div_dvd_of_dvd hsd).trans hdn
        have hesq : Squarefree (d / s) := hdsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hsd)
        have := pair_cancel t val ht hval y hs hss hn0 hen hesq hse
        simp only [g, if_pos hdsq, if_pos hsd, hf]
        rw [hes] at this
        linarith
      · have := pair_cancel t val ht hval y hs hss hn0 hdn hdsq hsd
        simp only [g, if_pos hdsq, if_neg hsd, hf]
        exact this
    · simp only [g, if_neg hdsq, hf, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdsq]
      ring
  · intro d hd hfd
    have hdsq : Squarefree d := by
      by_contra h
      apply hfd
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    have hd0 : d ≠ 0 := hdsq.ne_zero
    simp only [g, if_pos hdsq]
    split_ifs with hsd
    · intro h
      have := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hs.one_lt
      omega
    · intro h
      have h1 := hs.one_lt
      have h2 : 0 < d := Nat.pos_of_ne_zero hd0
      nlinarith
  · intro d hd
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
    show g d ∈ n.properDivisors
    by_cases hdsq : Squarefree d
    · simp only [g, if_pos hdsq]
      split_ifs with hsd
      · rw [Nat.mem_properDivisors]
        refine ⟨(Nat.div_dvd_of_dvd hsd).trans hdn, lt_of_le_of_lt (Nat.div_le_self d s) hdlt⟩
      · obtain ⟨hdvd, hsq', -⟩ := toggleA hs hss hn0 hdn hdsq hsd
        rw [Nat.mem_properDivisors]
        refine ⟨hdvd, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) ?_⟩
        intro h; rw [h] at hsq'; exact hnsq hsq'
    · simp only [g, if_neg hdsq]; exact hd
  · intro d hd
    show g (g d) = d
    by_cases hdsq : Squarefree d
    · by_cases hsd : s ∣ d
      · obtain ⟨hse, hes⟩ := hdiv_case d hdsq hsd
        have hesq : Squarefree (d / s) := hdsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hsd)
        simp only [g, if_pos hdsq, if_pos hsd, if_pos hesq, if_neg hse]
        exact hes
      · obtain ⟨hdvd, hsq', -⟩ := toggleA hs hss hn0 (Nat.mem_properDivisors.mp hd).1 hdsq hsd
        simp only [g, if_pos hdsq, if_neg hsd, if_pos hsq', if_pos (Dvd.intro_left d rfl)]
        exact Nat.mul_div_cancel d hs.pos
    · simp only [g, if_neg hdsq]

/-- **Lemma 5.5 (Lemma M).** For a start `y ≥ X₀⁻ ≥ 0`,
`c_n(y) = μ(n) χ_y^t(n) 1[y/n ≥ X₀⁻]`. -/
theorem lemma_M (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p)
    {X0 : ℝ} (hX0 : 0 ≤ X0) {y : ℝ} (hy : X0 ≤ y) {n : ℕ} (hn : 1 ≤ n) :
    coeff t val X0 y n = μ n * (if chi t val y n then 1 else 0) *
      (if X0 ≤ y / valN val n then 1 else 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [coeff, if_neg (by omega)]
    rw [Finset.sum_attach n.properDivisors (fun d =>
      if filt t val y n d ∧ X0 ≤ y / valN val n then coeff t val X0 y d else 0)]
    by_cases hcut : X0 ≤ y / valN val n
    · have hsum : ∑ d ∈ n.properDivisors,
          (if filt t val y n d ∧ X0 ≤ y / valN val n then coeff t val X0 y d else 0) =
          ∑ d ∈ n.properDivisors, ((if filt t val y n d then 1 else 0) * μ d *
            (if chi t val y d then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
        have hcutd : X0 ≤ y / valN val d := by
          refine le_trans hcut (div_le_div_of_nonneg_left (by linarith) (valN_pos val hval)
            (valN_le_of_dvd val hval hdn (by omega)))
        rw [ih d hdlt hd1, if_pos hcutd]
        by_cases hf : filt t val y n d <;> simp [hf, hcut]
      rw [hsum, if_pos hcut]
      by_cases hsq : Squarefree n
      · rw [key_sqfree t val ht hval y h1 hsq]; ring
      · rw [key_not_sqfree t val ht hval y (by omega) hsq]
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    · simp [hcut]
  · obtain rfl : n = 1 := by omega
    simp [coeff, valN_one, chi, chiS, hy]

/-- First consequence of Lemma M: `|c_n(y)| ≤ 1`. -/
theorem abs_coeff_le_one (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p)
    {X0 : ℝ} (hX0 : 0 ≤ X0) {y : ℝ} (hy : X0 ≤ y) {n : ℕ} (hn : 1 ≤ n) :
    |coeff t val X0 y n| ≤ 1 := by
  rw [lemma_M t val ht hval hX0 hy hn]
  have hmu : |μ n| ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
  split_ifs <;> simp [hmu]

/-- Second consequence of Lemma M (density): if `χ_y^t(n) = 1` and `y/n < 2v`, and every prime
satisfies `p ≤ 2 t(p)` (in the paper, `p ≤ (1 - 10⁻¹⁰)⁻¹ t(p)`), then `n` is `4v`-dense: every
prime `q ∣ n` satisfies `q ≤ 4v ∏_{p ∣ n, p < q} p`. -/
theorem dense_of_chi (ht : ∀ p, p.Prime → 0 < t p) (hval : ∀ p, p.Prime → 1 ≤ val p)
    (htv : ∀ p, p.Prime → val p ≤ 2 * t p) {y v : ℝ} {n : ℕ} (hchi : chi t val y n)
    (hv : y < 2 * v * valN val n) {q : ℕ} (hq : q ∈ n.primeFactors) :
    val q ≤ 4 * v * valS val (n.primeFactors.filter fun p => val p < val q) := by
  obtain ⟨hsq, hchiS⟩ := hchi
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  set T := n.primeFactors.filter fun p => ¬ val p < val q with hT
  set S := n.primeFactors.filter fun p => val p < val q with hS
  have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hq, lt_irrefl _⟩
  obtain ⟨ps, hpsT, hpsmin⟩ := T.exists_min_image (rk t) ⟨q, hqT⟩
  obtain ⟨hps, hpsq⟩ := Finset.mem_filter.mp hpsT
  push_neg at hpsq
  have hF : T ⊆ n.primeFactors.filter (fun x => rk t ps ≤ rk t x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hpsmin x hx⟩
  have hvalF : ∀ x ∈ n.primeFactors.filter (fun x => rk t ps ≤ rk t x), 1 ≤ val x :=
    fun x hx => hval x (hpr x (Finset.mem_filter.mp hx).1)
  have h1 := hchiS ps hps
  have h2 := valS_mono val hvalF hF
  have htps := ht ps (hpr ps hps)
  have hsplit : valN val n = valS val S * valS val T := by
    rw [valN_of_squarefree val hsq]
    unfold valS
    rw [hS, hT, Finset.prod_filter_mul_prod_filter_not]
  have hTpos : 0 < valS val T := by
    unfold valS
    exact Finset.prod_pos (fun x hx => lt_of_lt_of_le one_pos
      (hval x (hpr x (Finset.mem_filter.mp hx).1)))
  have hkey : t ps * valS val T < 2 * v * valS val S * valS val T := by
    calc t ps * valS val T ≤ t ps * valS val (n.primeFactors.filter (fun x => rk t ps ≤ rk t x)) :=
          mul_le_mul_of_nonneg_left h2 htps.le
      _ < y := h1
      _ < 2 * v * valN val n := hv
      _ = 2 * v * valS val S * valS val T := by rw [hsplit]; ring
  have hlt : t ps < 2 * v * valS val S := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have := htv ps (hpr ps hps)
  linarith

end LemmaM
