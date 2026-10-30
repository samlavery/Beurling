module

public import RequestProject.BSCert.Finite.X0Mono
public import RequestProject.BSCert.Finite.X0Vec

/-!
# The jump at `X₀`: the representatives up to `10⁶`

`rep_of`: for `2 ≤ n ≤ 10⁶`, `φ(n) = nOf PL v` with `v` of length 7 and nonzero entries forming
a prefix (`φ(n)` is built on the first `ω(n) ≤ 7` primes). `mem_gen`: all such `v` with
`nOf PL v ≤ 10⁶` are listed by `gen PL (10⁶)` (785 vectors, including `0`).
`chkL` is the check run on slices of that list.
-/

@[expose] public section

open Finset

namespace BSCert.X0Rep

open BSCert.X0Mono BSCert.X0Vec

lemma nth5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by norm_num : Nat.Prime 13)
lemma nth6 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (by norm_num : Nat.Prime 17)
lemma nth7 : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (by norm_num : Nat.Prime 19)

lemma PL_eq : PL = (List.range 7).map (Nat.nth Nat.Prime) := by
  simp [PL, List.range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven, nth5, nth6]

/-- Vectors whose nonzero entries form a prefix. -/
def PS : List ℕ → Prop
  | [] => True
  | 0 :: v => ∀ x ∈ v, x = 0
  | (_ + 1) :: v => PS v

lemma PS_of : ∀ (v : List ℕ) (k : ℕ), (∀ i (h : i < v.length), (v[i] ≠ 0 ↔ i < k)) → PS v := by
  intro v
  induction v with
  | nil => intro _ _; trivial
  | cons a v ih =>
    intro k h
    rcases a with _ | a
    · have hk : k = 0 := by
        have := h 0 (by simp); simp at this; omega
      subst hk
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := h (i + 1) (by simp; omega)
      simp at this; exact this
    · have hk : 0 < k := by have := h 0 (by simp); simpa using this
      refine ih (k - 1) fun i hi => ?_
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; omega

lemma nOf_map : ∀ (ps : List ℕ) (f : ℕ → ℕ), nOf ps (ps.map f) = (ps.map fun p => p ^ f p).prod := by
  intro ps f
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [nOf, ih]

lemma nOf_map_fac (ps : List ℕ) (hnd : ps.Nodup) {M : ℕ} (hM : M ≠ 0)
    (hsub : M.primeFactors ⊆ ps.toFinset) : nOf ps (ps.map M.factorization) = M := by
  rw [nOf_map, ← List.prod_toFinset _ hnd]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hM]
  rw [Finsupp.prod, Nat.support_factorization]
  symm
  apply Finset.prod_subset hsub
  intro p _ hp
  rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]

variable {n : ℕ}

lemma rk_lt_card {p : ℕ} (hp : p ∈ n.primeFactors) : rk n p < n.primeFactors.card := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨p, hp, by simp⟩

lemma rk_surj {r : ℕ} (hr : r < n.primeFactors.card) :
    ∃ p ∈ n.primeFactors, rk n p = r := by
  have := Finset.surj_on_of_inj_on_of_card_le (s := n.primeFactors) (t := Finset.range n.primeFactors.card)
    (fun p hp => rk n p) (fun p hp => Finset.mem_range.mpr (rk_lt_card hp))
    (fun p q hp hq h => by
      rcases lt_trichotomy p q with hl | rfl | hl
      · exact absurd h (rk_lt hp hl).ne
      · rfl
      · exact absurd h (rk_lt hq hl).ne')
    (by simp) r (Finset.mem_range.mpr hr)
  obtain ⟨p, hp, h⟩ := this
  exact ⟨p, hp, h.symm⟩

lemma mem_pf_φ (hn : n ≠ 0) (q : ℕ) :
    q ∈ (φ n n).primeFactors ↔ ∃ r < n.primeFactors.card, q = Nat.nth Nat.Prime r := by
  constructor
  · intro hq
    have h0 : (φ n n).factorization q ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hq
    rw [fac_φ] at h0
    obtain ⟨p, hp, hpq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hσ : σ n p = q := by by_contra h; simp [h] at hpq
    exact ⟨rk n p, rk_lt_card hp, hσ.symm⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨p, hp, rfl⟩ := rk_surj hr
    have h1 : (φ n n).factorization (σ n p) = n.factorization p := fac_φ_σ n hp
    have h2 : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact h1 ▸ h2

lemma card_le_seven (hn : n ≠ 0) (hle : n ≤ 10 ^ 6) : n.primeFactors.card ≤ 7 := by
  by_contra hk
  push_neg at hk
  have hsub : (Finset.range 8).image (Nat.nth Nat.Prime) ⊆ (φ n n).primeFactors := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact (mem_pf_φ hn _).mpr ⟨r, by simp at hr; omega, rfl⟩
  have h1 : ∏ q ∈ (Finset.range 8).image (Nat.nth Nat.Prime), q ≤ ∏ q ∈ (φ n n).primeFactors, q :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub
      (fun q hq _ => (Nat.prime_of_mem_primeFactors hq).one_lt.le)
  have h2 : ∏ q ∈ (φ n n).primeFactors, q ≤ φ n n :=
    Nat.le_of_dvd (φ_pos n) (Nat.prod_primeFactors_dvd _)
  have h3 := φ_le hn (dvd_refl n)
  rw [Finset.prod_image (fun a _ b _ h => Nat.nth_injective Nat.infinite_setOf_prime h)] at h1
  simp [Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven,
    nth5, nth6, nth7] at h1
  omega

/-- The representative `φ(n)` is `nOf PL v` for a prefix-shaped `v`. -/
theorem rep_of (hn : 2 ≤ n) (hle : n ≤ 10 ^ 6) :
    ∃ v : List ℕ, v.length = 7 ∧ PS v ∧ nOf PL v = φ n n := by
  have hn0 : n ≠ 0 := by omega
  have hk := card_le_seven hn0 hle
  refine ⟨PL.map (φ n n).factorization, by simp [PL], ?_, ?_⟩
  · refine PS_of _ n.primeFactors.card fun i hi => ?_
    simp only [List.length_map] at hi
    have hi7 : i < 7 := by simpa [PL] using hi
    simp only [List.getElem_map]
    have hPL : PL[i] = Nat.nth Nat.Prime i := by simp [PL_eq]
    rw [hPL, ← Finsupp.mem_support_iff, Nat.support_factorization, mem_pf_φ hn0]
    constructor
    · rintro ⟨r, hr, h⟩
      rw [Nat.nth_injective Nat.infinite_setOf_prime h]; exact hr
    · intro h; exact ⟨i, h, rfl⟩
  · apply nOf_map_fac PL (by decide) (φ_ne_zero n)
    intro q hq
    obtain ⟨r, hr, rfl⟩ := (mem_pf_φ hn0 q).mp hq
    rw [PL_eq]
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    exact ⟨r, by omega, rfl⟩


/-! ## Enumerating the prefix-shaped vectors -/

/-- The prefix-shaped `v` with `nOf ps v ≤ B` (exponents below 20). -/
def gen : List ℕ → ℕ → List (List ℕ)
  | [], _ => [[]]
  | p :: ps, B => (0 :: List.replicate ps.length 0) ::
      ((List.range 20).filter fun a => 1 ≤ a ∧ p ^ a ≤ B).flatMap
        fun a => (gen ps (B / p ^ a)).map (a :: ·)

lemma mem_gen : ∀ (ps : List ℕ) (B : ℕ) (v : List ℕ), (∀ p ∈ ps, p.Prime) → B ≤ 10 ^ 6 →
    v.length = ps.length → PS v → nOf ps v ≤ B → v ∈ gen ps B := by
  intro ps
  induction ps with
  | nil => intro B v _ _ hl _ _; cases v <;> simp_all [gen]
  | cons p ps ih =>
    intro B v hp hB hl hps hle
    cases v with
    | nil => simp at hl
    | cons a v =>
      have hpp : p.Prime := hp p (by simp)
      have hpr' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (by simp [hq])
      have hl' : v.length = ps.length := by simpa using hl
      rcases a with _ | a
      · simp only [PS] at hps
        simp only [gen, List.mem_cons]
        left
        rw [List.cons.injEq]
        exact ⟨rfl, List.eq_replicate_iff.mpr ⟨hl', hps⟩⟩
      · simp only [PS] at hps
        simp only [nOf] at hle
        have hM := nOf_pos ps v hpr'
        have hpa : p ^ (a + 1) ≤ B := le_trans (Nat.le_mul_of_pos_right _ hM) hle
        have ha : a + 1 < 20 := by
          by_contra h
          have : 2 ^ 20 ≤ p ^ (a + 1) :=
            le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
              (Nat.pow_le_pow_left hpp.two_le _)
          omega
        simp only [gen, List.mem_cons, List.mem_flatMap, List.mem_filter, List.mem_range,
          List.mem_map]
        right
        refine ⟨a + 1, ⟨ha, by simp [hpa]⟩, v, ih _ v hpr' (le_trans (Nat.div_le_self _ _) hB) hl' hps ?_, rfl⟩
        rw [Nat.le_div_iff_mul_le (pow_pos hpp.pos _)]
        linarith [hle]

/-- The vector of `6 = 2 · 3`. -/
def v6 : List ℕ := [1, 1, 0, 0, 0, 0, 0]

/-- The check for one vector: `0`, or `B < 5/12`, or (only for `6`) `B = 5/12`. -/
def chk (v hs : List ℕ) : Bool := isZ v || okV v hs || (v == v6 && eqV v hs)

/-- The check for a slice of vectors with their certificates. -/
def chkL : List (List ℕ) → List (List ℕ) → Bool
  | v :: vs, hs :: hss => chk v hs && chkL vs hss
  | [], _ => true
  | _ :: _, [] => false

lemma chkL_sound : ∀ (vs hss : List (List ℕ)), chkL vs hss = true → ∀ v ∈ vs,
    v.length = PL.length → isZ v = true ∨ BSCert.X0Band.Bx (nOf PL v) < 5 / 12 ∨
      (v = v6 ∧ BSCert.X0Band.Bx (nOf PL v) = 5 / 12) := by
  intro vs
  induction vs with
  | nil => intro _ _ v hv; simp at hv
  | cons a vs ih =>
    intro hss h v hv hl
    cases hss with
    | nil => simp [chkL] at h
    | cons hs hss =>
      simp only [chkL, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hv with rfl | hv
      · simp only [chk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rcases h.1 with (h1 | h1) | ⟨rfl, h1⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl (okV_sound hl h1))
        · exact Or.inr (Or.inr ⟨rfl, eqV_sound hl h1⟩)
      · exact ih hss h.2 v hv hl

end BSCert.X0Rep
