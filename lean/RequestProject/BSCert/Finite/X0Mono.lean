module

public import RequestProject.BSCert.Finite.X0Band

/-!
# The jump at `X₀`: monotone reduction to representatives

For `n ≥ 1` let `p₁ < … < p_k` be the prime factors of `n`, and let `φ` replace `p_i` by the
`i`-th prime: `φ(d) = ∏_{p | n} σ(p)^{v_p(d)}` with `σ(p_i) = nth_prime (i - 1)`.
Then `φ` is a multiplicative, injective, divisibility-preserving map from the divisors of `n`
into the divisors of `φ(n)`, with `φ(d) ≤ d`, `μ²(d) ≤ μ²(φ d)`, `H_ord(d) ≤ H_ord(φ d)` and
`X(d)/d ≤ X(φ d)/φ d`. Hence (`Bx_le_φ`) `B(n) ≤ B(φ n)`, strictly if `φ n < n`.
-/

@[expose] public section

open Finset

namespace BSCert.X0Mono

variable (n : ℕ)

/-- The rank of `p` among the prime factors of `n`. -/
def rk (p : ℕ) : ℕ := (n.primeFactors.filter (· < p)).card

/-- The prime that replaces `p`: the `rk p`-th prime. -/
noncomputable def σ (p : ℕ) : ℕ := Nat.nth Nat.Prime (rk n p)

/-- `φ(d) = ∏_{p | n} σ(p)^{v_p(d)}`. -/
noncomputable def φ (d : ℕ) : ℕ := ∏ p ∈ n.primeFactors, σ n p ^ d.factorization p

variable {n}

lemma σ_prime (p : ℕ) : (σ n p).Prime := Nat.prime_nth_prime _

lemma rk_lt {p q : ℕ} (hp : p ∈ n.primeFactors) (hpq : p < q) : rk n p < rk n q := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, by simp [hp, hpq], by simp⟩
  · intro x hx; simp at hx ⊢; exact ⟨hx.1, by omega⟩

lemma σ_strictMono {p q : ℕ} (hp : p ∈ n.primeFactors) (hpq : p < q) : σ n p < σ n q :=
  Nat.nth_strictMono Nat.infinite_setOf_prime (rk_lt hp hpq)

lemma σ_injOn : Set.InjOn (σ n) n.primeFactors := by
  intro p hp q hq h
  rcases lt_trichotomy p q with hl | rfl | hl
  · exact absurd h (σ_strictMono hp hl).ne
  · rfl
  · exact absurd h (σ_strictMono hq hl).ne'

lemma σ_le {p : ℕ} (hp : p ∈ n.primeFactors) : σ n p ≤ p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hc : rk n p ≤ Nat.count Nat.Prime p := by
    unfold rk
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.2, Nat.prime_of_mem_primeFactors hx.1⟩
  calc σ n p = Nat.nth Nat.Prime (rk n p) := rfl
    _ ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime p) := Nat.nth_monotone Nat.infinite_setOf_prime hc
    _ = p := Nat.nth_count hpp

lemma φ_pos (d : ℕ) : 0 < φ n d :=
  Finset.prod_pos fun p _ => pow_pos (σ_prime p).pos _

lemma φ_ne_zero (d : ℕ) : φ n d ≠ 0 := (φ_pos d).ne'

/-- The factorization of `φ(d)`. -/
lemma fac_φ (d q : ℕ) :
    (φ n d).factorization q = ∑ p ∈ n.primeFactors, if σ n p = q then d.factorization p else 0 := by
  unfold φ
  rw [Nat.factorization_prod (fun p _ => (pow_pos (σ_prime p).pos _).ne')]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow,
    (σ_prime _).factorization, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finsupp.single_apply]

lemma fac_φ_σ (d : ℕ) {p : ℕ} (hp : p ∈ n.primeFactors) :
    (φ n d).factorization (σ n p) = d.factorization p := by
  rw [fac_φ, Finset.sum_eq_single p]
  · simp
  · intro b hb hbp
    rw [if_neg]
    intro h; exact hbp (σ_injOn hb hp h)
  · intro h; exact absurd hp h

lemma fac_φ_le {d e : ℕ} (h : ∀ p, d.factorization p ≤ e.factorization p) (q : ℕ) :
    (φ n d).factorization q ≤ (φ n e).factorization q := by
  rw [fac_φ, fac_φ]
  exact Finset.sum_le_sum fun p _ => by split_ifs <;> simp [h p]

lemma φ_one : φ n 1 = 1 := by simp [φ]

lemma φ_mul {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) : φ n (d * e) = φ n d * φ n e := by
  unfold φ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hd he, Finsupp.add_apply, pow_add]

lemma support_sub {d : ℕ} (hd : d ∣ n) (hn : n ≠ 0) : d.primeFactors ⊆ n.primeFactors :=
  Nat.primeFactors_mono hd hn

lemma φ_inj {d e : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (he : e ∣ n) (h : φ n d = φ n e) : d = e := by
  have hd0 : d ≠ 0 := fun h0 => hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))
  have he0 : e ≠ 0 := fun h0 => hn (Nat.eq_zero_of_zero_dvd (h0 ▸ he))
  apply Nat.eq_of_factorization_eq hd0 he0
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have := congrArg (fun m => m.factorization (σ n p)) h
    simpa [fac_φ_σ _ hp] using this
  · have hz : ∀ m : ℕ, m ∣ n → m.factorization p = 0 := by
      intro m hm
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact fun h => hp (Nat.primeFactors_mono hm hn h)
    rw [hz d hd, hz e he]

lemma fac_zero_of_not_mem {m p : ℕ} (hn : n ≠ 0) (hm : m ∣ n) (hp : p ∉ n.primeFactors) :
    m.factorization p = 0 := by
  rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
  exact fun h => hp (Nat.primeFactors_mono hm hn h)

lemma ne_zero_of_dvd {d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : d ≠ 0 :=
  fun h0 => hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))

/-- Divisibility is preserved. -/
lemma φ_dvd {d e : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hde : d ∣ e) : φ n d ∣ φ n e := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd hn (hde.trans he)
  have he0 : e ≠ 0 := ne_zero_of_dvd hn he
  rw [← Nat.factorization_le_iff_dvd (φ_ne_zero d) (φ_ne_zero e)]
  intro q
  exact fac_φ_le (fun p => (Nat.factorization_le_iff_dvd hd0 he0).mpr hde p) q

/-- `φ` decreases: `φ(d) ≤ d`. -/
lemma φ_le {d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : φ n d ≤ d := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd hn hd
  have e : d = ∏ p ∈ n.primeFactors, p ^ d.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hd0]
    rw [Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_subset (Nat.primeFactors_mono hd hn)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]
  conv_rhs => rw [e]
  unfold φ
  exact Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_left (σ_le hp) _

/-- Squarefreeness is preserved. -/
lemma φ_squarefree {d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hsq : Squarefree d) : Squarefree (φ n d) := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd hn hd
  rw [Nat.squarefree_iff_factorization_le_one hd0] at hsq
  rw [Nat.squarefree_iff_factorization_le_one (φ_ne_zero d)]
  intro q
  rw [fac_φ]
  by_cases hq : ∃ p ∈ n.primeFactors, σ n p = q
  · obtain ⟨p, hp, rfl⟩ := hq
    rw [Finset.sum_eq_single p]
    · simpa using hsq p
    · intro b hb hbp; rw [if_neg]; intro h; exact hbp (σ_injOn hb hp h)
    · intro h; exact absurd hp h
  · push_neg at hq
    rw [Finset.sum_eq_zero]
    · omega
    · intro p hp; rw [if_neg (hq p hp)]

lemma φ_div {d e : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hed : e ∣ d) : φ n (d / e) * φ n e = φ n d := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd hn hd
  have he0 : e ≠ 0 := ne_zero_of_dvd hn (hed.trans hd)
  have hq0 : d / e ≠ 0 := by
    intro h; rw [Nat.div_eq_zero_iff] at h; rcases h with h | h
    · exact he0 h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed) (by omega)
  rw [← φ_mul hq0 he0, Nat.div_mul_cancel hed]


open BSCert.X0Band in
lemma musq_le_φ {e : ℕ} (hn : n ≠ 0) (he : e ∣ n) : musq e ≤ musq (φ n e) := by
  rw [musq_eq, musq_eq]
  unfold BSCert.X0Band.sq
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (φ_squarefree hn he h1) h2
  · norm_num
  · exact le_rfl

lemma musq_nonneg' (e : ℕ) : 0 ≤ BSCert.X0Band.musq e := by
  unfold BSCert.X0Band.musq; positivity

open BSCert.X0Band in
lemma one_lt_φ {d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (h1 : 1 < d) : 1 < φ n d := by
  have hne : φ n d ≠ 1 := by
    intro h
    have := φ_inj hn hd (one_dvd n) (h.trans φ_one.symm)
    omega
  have := φ_pos (n := n) d
  omega

lemma φ_lt {d e : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hde : d ∣ e) (hlt : d < e) : φ n d < φ n e := by
  have h1 := Nat.le_of_dvd (φ_pos e) (φ_dvd hn he hde)
  have h2 : φ n d ≠ φ n e := fun h => by
    have := φ_inj hn (hde.trans he) he h; omega
  omega

open BSCert.X0Band in
/-- `H_ord` does not decrease. -/
lemma Hord_le_φ (hn : n ≠ 0) : ∀ m, m ∣ n → Hord m ≤ Hord (φ n m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm0 : m ≠ 0 := ne_zero_of_dvd hn hm
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this; rw [φ_one]
    · have h1 := one_lt_φ hn hm (by omega)
      rw [Hord_eq, if_neg (by omega), Hord_eq (φ n m), if_neg (by omega)]
      calc ∑ d ∈ m.properDivisors, Hord d ≤ ∑ d ∈ m.properDivisors, Hord (φ n d) :=
            Finset.sum_le_sum fun d hd => ih d (Nat.mem_properDivisors.mp hd).2
              ((Nat.mem_properDivisors.mp hd).1.trans hm)
        _ = ∑ d' ∈ m.properDivisors.image (φ n), Hord d' := by
            rw [Finset.sum_image]
            intro a ha b hb hab
            exact φ_inj hn ((Nat.mem_properDivisors.mp ha).1.trans hm)
              ((Nat.mem_properDivisors.mp hb).1.trans hm) hab
        _ ≤ ∑ d' ∈ (φ n m).properDivisors, Hord d' := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
              obtain ⟨hdm, hdlt⟩ := Nat.mem_properDivisors.mp hd
              exact Nat.mem_properDivisors.mpr ⟨φ_dvd hn hm hdm, φ_lt hn hm hdm hdlt⟩
            · intro _ _ _; exact Nat.zero_le _


open BSCert.X0Band in
/-- `X(d)/d = ∑_{e | d, 1<e<d} μ²(e) H(d/e)/(d/e)`. -/
lemma X_div_eq {d : ℕ} (hd : d ≠ 0) :
    X d / d = ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      musq e * (Hord (d / e) : ℚ) / ((d / e : ℕ) : ℚ) := by
  unfold X
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_filter, Nat.mem_divisors] at he
  have hed := he.1.1
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hq : ((d / e : ℕ) : ℚ) = (d : ℚ) / e := by rw [Nat.cast_div hed he0]
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [hq]
  field_simp

open BSCert.X0Band in
lemma X_div_le_φ {d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : X d / d ≤ X (φ n d) / φ n d := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd hn hd
  rw [X_div_eq hd0, X_div_eq (φ_ne_zero d)]
  set E := d.divisors.filter (fun e => 1 < e ∧ e < d)
  have hE : ∀ e ∈ E, e ∣ d ∧ 1 < e ∧ e < d := by
    intro e he; simp only [E, Finset.mem_filter, Nat.mem_divisors] at he; exact ⟨he.1.1, he.2⟩
  calc ∑ e ∈ E, musq e * (Hord (d / e) : ℚ) / ((d / e : ℕ) : ℚ)
      ≤ ∑ e ∈ E, musq (φ n e) * (Hord (φ n d / φ n e) : ℚ) / ((φ n d / φ n e : ℕ) : ℚ) := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨hed, h1, h2⟩ := hE e he
        have hen : e ∣ n := hed.trans hd
        have hqd : d / e ∣ n := (Nat.div_dvd_of_dvd hed).trans hd
        have hφq : φ n d / φ n e = φ n (d / e) := by
          rw [← φ_div hn hd hed, Nat.mul_div_cancel _ (φ_pos e)]
        rw [hφq]
        have hq0 : (0 : ℚ) < ((φ n (d / e) : ℕ) : ℚ) := by exact_mod_cast φ_pos _
        have hq1 : ((φ n (d / e) : ℕ) : ℚ) ≤ ((d / e : ℕ) : ℚ) := by exact_mod_cast φ_le hn hqd
        have hH : (Hord (d / e) : ℚ) ≤ (Hord (φ n (d / e)) : ℚ) := by
          exact_mod_cast Hord_le_φ hn _ hqd
        have hm := musq_le_φ hn hen
        have hm0 := musq_nonneg' e
        have hH0 : (0 : ℚ) ≤ (Hord (d / e) : ℚ) := by positivity
        calc musq e * (Hord (d / e) : ℚ) / ((d / e : ℕ) : ℚ)
            ≤ musq e * (Hord (d / e) : ℚ) / ((φ n (d / e) : ℕ) : ℚ) :=
              div_le_div_of_nonneg_left (by positivity) hq0 hq1
          _ ≤ musq (φ n e) * (Hord (φ n (d / e)) : ℚ) / ((φ n (d / e) : ℕ) : ℚ) := by
              apply div_le_div_of_nonneg_right _ hq0.le
              exact mul_le_mul hm hH hH0 (hm0.trans hm)
    _ = ∑ e' ∈ E.image (φ n), musq e' * (Hord (φ n d / e') : ℚ) / ((φ n d / e' : ℕ) : ℚ) := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact φ_inj hn ((hE a ha).1.trans hd) ((hE b hb).1.trans hd) hab
    _ ≤ ∑ e' ∈ (φ n d).divisors.filter (fun e => 1 < e ∧ e < φ n d),
          musq e' * (Hord (φ n d / e') : ℚ) / ((φ n d / e' : ℕ) : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨hed, h1, h2⟩ := hE e he
          simp only [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨φ_dvd hn hd hed, φ_ne_zero d⟩, one_lt_φ hn (hed.trans hd) h1, φ_lt hn hd hed h2⟩
        · intro x _ _
          have := musq_nonneg' x
          positivity


open BSCert.X0Band in
/-- The bracket of `B(n)`. -/
noncomputable def brk (m : ℕ) : ℚ :=
  musq m / 2 + 1 / 2 * ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m),
    (2 * musq d + 1 / 2 * lam * X d / d)

open BSCert.X0Band in
lemma Bx_eq_brk (m : ℕ) : Bx m = 1 / m * brk m := rfl

open BSCert.X0Band in
lemma X_nonneg (d : ℕ) : 0 ≤ X d := by
  unfold X
  apply Finset.sum_nonneg
  intro e _
  have := musq_nonneg' e
  positivity

open BSCert.X0Band in
lemma term_nonneg (d : ℕ) : 0 ≤ 2 * musq d + 1 / 2 * lam * X d / d := by
  have := musq_nonneg' d
  have := X_nonneg d
  unfold lam
  positivity

open BSCert.X0Band in
lemma brk_nonneg (m : ℕ) : 0 ≤ brk m := by
  unfold brk
  have := musq_nonneg' m
  have : 0 ≤ ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), (2 * musq d + 1 / 2 * lam * X d / d) :=
    Finset.sum_nonneg fun d _ => term_nonneg d
  positivity

open BSCert.X0Band in
lemma brk_pos {m : ℕ} (hm : 2 ≤ m) : 0 < brk m := by
  unfold brk
  have hS : 0 ≤ ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), (2 * musq d + 1 / 2 * lam * X d / d) :=
    Finset.sum_nonneg fun d _ => term_nonneg d
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  by_cases hpm : m.minFac = m
  · -- `m` is prime, hence squarefree
    have hsq : musq m = 1 := by
      rw [musq_eq]; unfold BSCert.X0Band.sq
      rw [if_pos (hpm ▸ hp).squarefree]; norm_num
    rw [hsq]; positivity
  · have hlt : m.minFac < m := lt_of_le_of_ne (Nat.minFac_le (by omega)) hpm
    have hmem : m.minFac ∈ m.divisors.filter (fun d => 1 < d ∧ d < m) := by
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.minFac_dvd m, by omega⟩, hp.one_lt, hlt⟩
    have hsq : musq m.minFac = 1 := by
      rw [musq_eq]; unfold BSCert.X0Band.sq
      rw [if_pos hp.squarefree]; norm_num
    have h1 : 2 ≤ ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), (2 * musq d + 1 / 2 * lam * X d / d) := by
      have := Finset.single_le_sum (fun d _ => term_nonneg d) hmem
      have h2 := X_nonneg m.minFac
      have h3 : (0 : ℚ) ≤ 1 / 2 * lam * X m.minFac / m.minFac := by unfold lam; positivity
      rw [hsq] at this
      linarith
    have := musq_nonneg' m
    linarith

open BSCert.X0Band in
lemma brk_le_φ (hn : n ≠ 0) : brk n ≤ brk (φ n n) := by
  unfold brk
  have hm := musq_le_φ hn (dvd_refl n)
  have hsum : ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n), (2 * musq d + 1 / 2 * lam * X d / d)
      ≤ ∑ d ∈ (φ n n).divisors.filter (fun d => 1 < d ∧ d < φ n n),
          (2 * musq d + 1 / 2 * lam * X d / d) := by
    set E := n.divisors.filter (fun d => 1 < d ∧ d < n)
    have hE : ∀ d ∈ E, d ∣ n ∧ 1 < d ∧ d < n := by
      intro d hd; simp only [E, Finset.mem_filter, Nat.mem_divisors] at hd; exact ⟨hd.1.1, hd.2⟩
    calc ∑ d ∈ E, (2 * musq d + 1 / 2 * lam * X d / d)
        ≤ ∑ d ∈ E, (2 * musq (φ n d) + 1 / 2 * lam * X (φ n d) / (φ n d)) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hdn, -, -⟩ := hE d hd
          have h1 := musq_le_φ hn hdn
          have h2 := X_div_le_φ hn hdn
          have e1 : 1 / 2 * lam * X d / d = 1 / 2 * lam * (X d / d) := by ring
          have e2 : 1 / 2 * lam * X (φ n d) / (φ n d) = 1 / 2 * lam * (X (φ n d) / φ n d) := by ring
          rw [e1, e2]
          have : (0 : ℚ) ≤ 1 / 2 * lam := by unfold lam; norm_num
          nlinarith
      _ = ∑ d' ∈ E.image (φ n), (2 * musq d' + 1 / 2 * lam * X d' / d') := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          exact φ_inj hn (hE a ha).1 (hE b hb).1 hab
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
            obtain ⟨hdn, h1, h2⟩ := hE d hd
            simp only [Finset.mem_filter, Nat.mem_divisors]
            exact ⟨⟨φ_dvd hn (dvd_refl n) hdn, φ_ne_zero n⟩, one_lt_φ hn hdn h1,
              φ_lt hn (dvd_refl n) hdn h2⟩
          · intro x _ _; exact term_nonneg x
  linarith

open BSCert.X0Band in
/-- **Monotone reduction.** `B(n) ≤ B(φ(n))`, strictly if `φ(n) < n`. -/
theorem Bx_le_φ {n : ℕ} (hn : 2 ≤ n) :
    Bx n ≤ Bx (φ n n) ∧ (φ n n < n → Bx n < Bx (φ n n)) := by
  have hn0 : n ≠ 0 := by omega
  have hφ2 : 2 ≤ φ n n := one_lt_φ hn0 (dvd_refl n) (by omega)
  have hle : φ n n ≤ n := φ_le hn0 (dvd_refl n)
  have hb := brk_le_φ hn0
  have hb0 := brk_nonneg n
  have hbφ := brk_pos hφ2
  rw [Bx_eq_brk, Bx_eq_brk]
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hφq : (0 : ℚ) < (φ n n : ℕ) := by exact_mod_cast (φ_pos n)
  have hle' : ((φ n n : ℕ) : ℚ) ≤ n := by exact_mod_cast hle
  have h1 : 1 / (n : ℚ) ≤ 1 / ((φ n n : ℕ) : ℚ) := one_div_le_one_div_of_le hφq hle'
  constructor
  · calc 1 / (n : ℚ) * brk n ≤ 1 / (n : ℚ) * brk (φ n n) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 1 / ((φ n n : ℕ) : ℚ) * brk (φ n n) := mul_le_mul_of_nonneg_right h1 hbφ.le
  · intro hlt
    have hlt' : ((φ n n : ℕ) : ℚ) < n := by exact_mod_cast hlt
    have h2 : 1 / (n : ℚ) < 1 / ((φ n n : ℕ) : ℚ) := one_div_lt_one_div_of_lt hφq hlt'
    calc 1 / (n : ℚ) * brk n ≤ 1 / (n : ℚ) * brk (φ n n) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ < 1 / ((φ n n : ℕ) : ℚ) * brk (φ n n) := mul_lt_mul_of_pos_right h2 hbφ

end BSCert.X0Mono
