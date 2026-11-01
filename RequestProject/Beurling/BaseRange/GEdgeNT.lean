module

public import RequestProject.Beurling.BaseRange.EdgeRes

/-!
# Lemma 7.3(d)(iii): the coefficient of a window prime in `g`

For `N ≥ 2` and a prime `p`, split `N = N_≤ N_>`, where `N_>` collects the prime factors of `N`
larger than `p` (`Nbig`, `Nsm`). For a proper divisor `d ∣ N`, the cofactor `N/d` has all its
primes `≤ p` iff `N_> ∣ d` (`Nbig_dvd_iff`). If `p N < 2x`, the stripping condition `χ_x(d)` of
Lemma M (rational system, `t(q) = q`) for squarefree `d = N_> s` depends only on `N_>`
(`chi_mul_iff`). Hence (`coeff_window_le`)

  `|∑_{d ∣ N, d < N, P⁺(N/d) ≤ p} μ(d) χ_x(d)| = |χ_x(N_>) μ(N_>) ∑_{s ∣ N_≤, s < N_≤} μ(s)| ≤ 1`,

the coefficient of `p` in the `N`-term of `g` (proof of (d)(iii)).
-/

@[expose] public section

open Real Finset BeurlingSystem
open scoped ArithmeticFunction.Moebius

namespace BaseRange

/-- The part of `N` composed of the primes `> p`. -/
noncomputable def Nbig (N p : ℕ) : ℕ := (N.factorization.filter (p < ·)).prod (· ^ ·)

/-- The part of `N` composed of the primes `≤ p`. -/
noncomputable def Nsm (N p : ℕ) : ℕ := (N.factorization.filter (fun q => ¬ p < q)).prod (· ^ ·)

lemma Nbig_mul_Nsm {N : ℕ} (hN : N ≠ 0) (p : ℕ) : Nbig N p * Nsm N p = N := by
  unfold Nbig Nsm
  rw [Finsupp.prod_filter_mul_prod_filter_not, Nat.prod_factorization_pow_eq_self hN]

lemma factorization_Nbig (N p : ℕ) :
    (Nbig N p).factorization = N.factorization.filter (p < ·) := by
  unfold Nbig
  apply Nat.prod_pow_factorization_eq_self
  intro q hq
  rw [Finsupp.support_filter, Finset.mem_filter] at hq
  exact Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hq.1)

lemma factorization_Nsm (N p : ℕ) :
    (Nsm N p).factorization = N.factorization.filter (fun q => ¬ p < q) := by
  unfold Nsm
  apply Nat.prod_pow_factorization_eq_self
  intro q hq
  rw [Finsupp.support_filter, Finset.mem_filter] at hq
  exact Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hq.1)

lemma Nbig_ne_zero (N p : ℕ) : Nbig N p ≠ 0 := by
  unfold Nbig Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun q hq => by
    rw [Finsupp.support_filter, Finset.mem_filter] at hq
    have : q.Prime :=
      Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hq.1)
    exact pow_ne_zero _ this.ne_zero

lemma Nsm_ne_zero (N p : ℕ) : Nsm N p ≠ 0 := by
  unfold Nsm Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun q hq => by
    rw [Finsupp.support_filter, Finset.mem_filter] at hq
    have : q.Prime :=
      Nat.prime_of_mem_primeFactors (by rw [← Nat.support_factorization]; exact hq.1)
    exact pow_ne_zero _ this.ne_zero

lemma lt_of_prime_dvd_Nbig {N p q : ℕ} (hq : q.Prime) (h : q ∣ Nbig N p) : p < q := by
  have h1 : (Nbig N p).factorization q ≠ 0 := by
    have := (Nat.Prime.dvd_iff_one_le_factorization hq (Nbig_ne_zero N p)).mp h; omega
  rw [factorization_Nbig, Finsupp.filter_apply] at h1
  by_contra hc; exact h1 (if_neg hc)

lemma le_of_prime_dvd_Nsm {N p q : ℕ} (hq : q.Prime) (h : q ∣ Nsm N p) : q ≤ p := by
  have h1 : (Nsm N p).factorization q ≠ 0 := by
    have := (Nat.Prime.dvd_iff_one_le_factorization hq (Nsm_ne_zero N p)).mp h; omega
  rw [factorization_Nsm, Finsupp.filter_apply] at h1
  by_contra hc; push_neg at hc; exact h1 (if_neg (not_not.mpr hc))

lemma coprime_Nbig_Nsm (N p : ℕ) : Nat.Coprime (Nbig N p) (Nsm N p) :=
  Nat.coprime_of_dvd fun q hq h1 h2 => by
    have := lt_of_prime_dvd_Nbig hq h1
    have := le_of_prime_dvd_Nsm hq h2
    omega

/-- `P⁺(N/d) ≤ p` iff `N_> ∣ d`, for `d ∣ N`. -/
lemma Nbig_dvd_iff {N p d : ℕ} (hN : N ≠ 0) (hd : d ∣ N) :
    Nbig N p ∣ d ↔ ∀ q ∈ (N / d).primeFactors, q ≤ p := by
  have hd0 : d ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hNd : d * (N / d) = N := Nat.mul_div_cancel' hd
  have hNd0 : N / d ≠ 0 := fun h => hN (by rw [← hNd, h, mul_zero])
  constructor
  · rintro ⟨s, rfl⟩ q hq
    have hq' := Nat.prime_of_mem_primeFactors hq
    have hqdvd := Nat.dvd_of_mem_primeFactors hq
    have hs0 : s ≠ 0 := right_ne_zero_of_mul hd0
    -- `N/(N_> s) ∣ N_≤`
    have h1 : Nbig N p * s * (N / (Nbig N p * s)) = Nbig N p * Nsm N p := by
      rw [hNd, Nbig_mul_Nsm hN]
    have h2 : s * (N / (Nbig N p * s)) = Nsm N p := by
      rw [mul_assoc] at h1
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Nbig_ne_zero N p)) h1
    exact le_of_prime_dvd_Nsm hq' (h2 ▸ Dvd.dvd.mul_left hqdvd s)
  · intro h
    rw [← Nat.factorization_le_iff_dvd (Nbig_ne_zero N p) hd0, factorization_Nbig]
    intro q
    rw [Finsupp.filter_apply]
    split_ifs with hpq
    · have h1 : N.factorization q = d.factorization q + (N / d).factorization q := by
        conv_lhs => rw [← hNd]
        rw [Nat.factorization_mul hd0 hNd0, Finsupp.add_apply]
      have h2 : (N / d).factorization q = 0 := by
        by_contra hc
        have hmem : q ∈ (N / d).primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hc
        have := h q hmem
        omega
      omega
    · exact Nat.zero_le _

/-! ### The stripping condition in the rational system -/

/-- The labels of the rational system: `lv q = q` on the primes. -/
noncomputable abbrev lv : ℕ → ℝ := ratSys.labelVal

lemma lv_prime {q : ℕ} (hq : q.Prime) : lv q = q := by
  unfold lv labelVal
  rw [ratSys_p, exists_qp_eq hq]

lemma rk_tQ_le_iff {q r : ℕ} : LemmaM.rk tQ q ≤ LemmaM.rk tQ r ↔ q ≤ r := by
  rw [LemmaM.rk_le_iff]
  unfold tQ
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact_mod_cast h.le
    · exact h
  · intro h
    rcases h.lt_or_eq with h | h
    · left; exact_mod_cast h
    · right; exact ⟨by rw [h], h.le⟩

lemma valS_primeFactors {n : ℕ} (hn : Squarefree n) : LemmaM.valS lv n.primeFactors = n := by
  unfold LemmaM.valS
  rw [Finset.prod_congr rfl (fun q hq => lv_prime (Nat.prime_of_mem_primeFactors hq))]
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]

/-- **`χ_x(N_> s) = χ_x(N_>)`** for squarefree `N_> s`, `s ∣ N_≤`, `p N_> s < x`. -/
lemma chi_mul_iff {N p s : ℕ} (hs : s ∣ Nsm N p)
    (hsq : Squarefree (Nbig N p * s)) {x : ℝ} (hb : (p : ℝ) * (Nbig N p * s : ℕ) < x) :
    LemmaM.chi tQ lv x (Nbig N p * s) ↔ LemmaM.chi tQ lv x (Nbig N p) := by
  classical
  have hs0 : s ≠ 0 := fun h => Nsm_ne_zero N p (Nat.eq_zero_of_zero_dvd (h ▸ hs))
  have hB0 := Nbig_ne_zero N p
  have hsqB : Squarefree (Nbig N p) := hsq.of_mul_left
  have hD : (Nbig N p * s).primeFactors = (Nbig N p).primeFactors ∪ s.primeFactors :=
    Nat.primeFactors_mul hB0 hs0
  have hsmall : ∀ r ∈ s.primeFactors, r ≤ p := fun r hr =>
    le_of_prime_dvd_Nsm (Nat.prime_of_mem_primeFactors hr)
      ((Nat.dvd_of_mem_primeFactors hr).trans hs)
  have hbig : ∀ q ∈ (Nbig N p).primeFactors, p < q := fun q hq =>
    lt_of_prime_dvd_Nbig (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have key : ∀ q ∈ (Nbig N p).primeFactors,
      (Nbig N p * s).primeFactors.filter (fun r => LemmaM.rk tQ q ≤ LemmaM.rk tQ r) =
        (Nbig N p).primeFactors.filter (fun r => LemmaM.rk tQ q ≤ LemmaM.rk tQ r) := by
    intro q hq
    ext r
    simp only [Finset.mem_filter, hD, Finset.mem_union, rk_tQ_le_iff]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, h2⟩
      · have := hsmall r h1; have := hbig q hq; omega
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
  unfold LemmaM.chi LemmaM.chiS
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hsqB, fun q hq => ?_⟩
    have := h q (by rw [hD]; exact Finset.mem_union_left _ hq)
    rwa [key q hq] at this
  · rintro ⟨-, h⟩
    refine ⟨hsq, fun q hq => ?_⟩
    rw [hD, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rw [key q hq]; exact h q hq
    · have hqp : (q : ℝ) ≤ p := by exact_mod_cast hsmall q hq
      have hv1 : ∀ r ∈ (Nbig N p * s).primeFactors, 1 ≤ lv r := fun r _ =>
        ratSys.one_le_labelVal r
      have hmono := LemmaM.valS_mono lv hv1
        (Finset.filter_subset (fun r => LemmaM.rk tQ q ≤ LemmaM.rk tQ r)
          (Nbig N p * s).primeFactors)
      rw [valS_primeFactors hsq] at hmono
      have h0 : 0 ≤ LemmaM.valS lv ((Nbig N p * s).primeFactors.filter
          (fun r => LemmaM.rk tQ q ≤ LemmaM.rk tQ r)) :=
        LemmaM.valS_nonneg lv (fun r hr => hv1 r (Finset.mem_filter.mp hr).1)
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      unfold tQ
      calc (q : ℝ) * LemmaM.valS lv ((Nbig N p * s).primeFactors.filter
            (fun r => LemmaM.rk tQ q ≤ LemmaM.rk tQ r))
          ≤ p * ((Nbig N p * s : ℕ) : ℝ) := mul_le_mul hqp hmono h0 (Nat.cast_nonneg _)
        _ < x := hb

lemma abs_sum_properDivisors_moebius_le (n : ℕ) (hn : n ≠ 0) :
    |∑ s ∈ n.properDivisors, (μ s : ℝ)| ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this; simp
  · rw [sum_properDivisors_moebius h, abs_neg]
    rcases ArithmeticFunction.moebius_eq_or n with h' | h' | h' <;> simp [h']

open Classical in
/-- **The coefficient of a window prime**, exactly: for `N ≥ 2` and `p N < 2x`,
`∑_{d ∣ N, d < N, P⁺(N/d) ≤ p} μ(d) χ_x(d) = μ(N_>) χ_x(N_>) ∑_{s ∣ N_≤, s < N_≤} μ(s)`. -/
theorem coeff_window_eq {N p : ℕ} (hN : 2 ≤ N) {x : ℝ} (hpx : (p : ℝ) * N < 2 * x) :
    ∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
      (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0) =
    (μ (Nbig N p) : ℝ) * (if LemmaM.chi tQ lv x (Nbig N p) then 1 else 0) *
      ∑ s ∈ (Nsm N p).properDivisors, (μ s : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  set B := Nbig N p
  set S := Nsm N p
  have hBS : B * S = N := Nbig_mul_Nsm hN0 p
  have hB0 : 0 < B := Nat.pos_of_ne_zero (Nbig_ne_zero N p)
  have hfilt : N.properDivisors.filter (fun d => Pplus (N / d) ≤ p) =
      S.properDivisors.image (B * ·) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_properDivisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, hdN⟩, hP⟩
      have hall : ∀ q ∈ (N / d).primeFactors, q ≤ p := fun q hq =>
        (le_Pplus hq).trans hP
      obtain ⟨s, rfl⟩ := (Nbig_dvd_iff hN0 hd).mpr hall
      refine ⟨s, ⟨?_, ?_⟩, rfl⟩
      · have hd' : B * s ∣ B * S := by rw [hBS]; exact hd
        exact Nat.dvd_of_mul_dvd_mul_left hB0 hd'
      · have hd' : B * s < B * S := by rw [hBS]; exact hdN
        exact Nat.lt_of_mul_lt_mul_left hd'
    · rintro ⟨s, ⟨hs, hsS⟩, rfl⟩
      have hd : B * s ∣ N := hBS ▸ Nat.mul_dvd_mul_left B hs
      refine ⟨⟨hd, ?_⟩, ?_⟩
      · rw [← hBS]; exact Nat.mul_lt_mul_of_pos_left hsS hB0
      · have := (Nbig_dvd_iff hN0 hd).mp (Dvd.intro s rfl)
        unfold Pplus
        exact Finset.sup_le fun q hq => this q hq
  rw [hfilt, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hB0 h)]
  have hterm : ∀ s ∈ S.properDivisors,
      (μ (B * s) : ℝ) * (if LemmaM.chi tQ lv x (B * s) then 1 else 0) =
        (μ B : ℝ) * (if LemmaM.chi tQ lv x B then 1 else 0) * (μ s : ℝ) := by
    intro s hs
    obtain ⟨hsS, hslt⟩ := Nat.mem_properDivisors.mp hs
    have hcop : Nat.Coprime B s := (coprime_Nbig_Nsm N p).coprime_dvd_right hsS
    have hmul : (μ (B * s) : ℝ) = (μ B : ℝ) * (μ s : ℝ) := by
      have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      exact_mod_cast this
    by_cases hsq : Squarefree (B * s)
    · have hd : B * s ∣ N := hBS ▸ Nat.mul_dvd_mul_left B hsS
      have h2 : 2 * (B * s) ≤ N := by
        obtain ⟨k, hk⟩ := hd
        have hk2 : 2 ≤ k := by
          by_contra hc; push_neg at hc
          have hdlt : B * s < N := by rw [← hBS]; exact Nat.mul_lt_mul_of_pos_left hslt hB0
          interval_cases k <;> omega
        calc 2 * (B * s) ≤ k * (B * s) := Nat.mul_le_mul_right _ hk2
          _ = N := by rw [hk]; ring
      have hb : (p : ℝ) * (B * s : ℕ) < x := by
        have h2' : (2 : ℝ) * (B * s : ℕ) ≤ N := by exact_mod_cast h2
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        nlinarith
      rw [chi_mul_iff hsS hsq hb, hmul]; ring
    · have h0 : (μ (B * s) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
      have e : (μ B : ℝ) * (μ s : ℝ) = 0 := by rw [← hmul]; exact h0
      rw [h0, zero_mul, mul_right_comm, e, zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

open Classical in
/-- **The coefficient of a window prime**: for `N ≥ 2` and `p N < 2x`,
`|∑_{d ∣ N, d < N, P⁺(N/d) ≤ p} μ(d) χ_x(d)| ≤ 1`. -/
theorem coeff_window_le {N p : ℕ} (hN : 2 ≤ N) {x : ℝ} (hpx : (p : ℝ) * N < 2 * x) :
    |∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
      (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0)| ≤ 1 := by
  rw [coeff_window_eq hN hpx, abs_mul, abs_mul]
  have h1 : |(μ (Nbig N p) : ℝ)| ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or (Nbig N p) with h' | h' | h' <;> simp [h']
  have h2 : |(if LemmaM.chi tQ lv x (Nbig N p) then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> simp
  have h3 := abs_sum_properDivisors_moebius_le (Nsm N p) (Nsm_ne_zero N p)
  calc _ ≤ (1 : ℝ) * 1 * 1 := by gcongr
    _ = 1 := by ring

end BaseRange
