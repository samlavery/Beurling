module

public import Mathlib

/-!
# Lemma A.6 (S3)(c) for one run: the Euler chain of the early block and the tails

For one run (`T = 1`, every row a chain row starting at `P_1`), the end step of Lemma A.5 sums,
over the contents `c` of the early block and the tails (row `i`: a free exponent vector `w_i`
on the decided slots and a tail `d_i`), the weight `∏_i 1/c_i`, `c_i = d_i ∏_n q_n^{w_i n}`, times
`χ = 1(u ≤ s_max) 1(G_{<u})`, where `u = u_c` is the first slot after the latest free slot.

* `RankFull.Config.rowSum_le` : the sum over the contents of one row with free slots before `M`
  is at most `R_D ∏_{decided n < M} (1 - 1/q_n)^{-1}` (`R_D = ∑ 1/d` over the tails);
* `RankFull.Config.euler_oneRun` : **(S3)(c) for one run**: with nested `G` and the sure top
  bound (S3)(d) `R_D ∏_{decided n < u} (1 - 1/q_n)^{-1} ≤ A` on `G_{<u}` for `u ≤ s_max`,
  `∑_c χ_c ∏_i 1/c_i ≤ A^k`. (The paper's `Fin = G_1(Eu) + Eu^k = A^k` for the run structure
  `[k]`.)
-/

@[expose] public section

open Finset
open scoped Classical

namespace RankFull.Config

variable {N : ℕ}

/-- The contents of one row: an exponent vector (entries `≤ D`) and an `X₀`-smooth tail
`≤ Dmax`. -/
noncomputable def rowSet (N D Dmax X₀ : ℕ) : Finset ((Fin N → ℕ) × ℕ) :=
  (Fintype.piFinset fun _ : Fin N => range (D + 1)) ×ˢ Nat.smoothNumbersUpTo Dmax X₀

/-- The value `d ∏_n q_n^{w_n}` of a row content. -/
noncomputable def cval (q : Fin N → ℝ) (x : (Fin N → ℕ) × ℕ) : ℝ := (x.2 : ℝ) * ∏ n, q n ^ x.1 n

/-- The first slot after the latest free slot of a content (`0` if there is none). -/
noncomputable def uOf {k : ℕ} (c : Fin k → (Fin N → ℕ) × ℕ) : ℕ :=
  (univ.filter fun n : Fin N => ∃ i, (c i).1 n ≠ 0).sup fun n => (n : ℕ) + 1

/-- The tail sum `R_D = ∑_{d ≤ Dmax, X₀-smooth} 1/d`. -/
noncomputable def tailSum (Dmax X₀ : ℕ) : ℝ := ∑ d ∈ Nat.smoothNumbersUpTo Dmax X₀, (d : ℝ)⁻¹

lemma uOf_le_iff {k : ℕ} (c : Fin k → (Fin N → ℕ) × ℕ) (M : ℕ) :
    uOf c ≤ M ↔ ∀ i n, (c i).1 n ≠ 0 → (n : ℕ) < M := by
  unfold uOf
  rw [Finset.sup_le_iff]
  constructor
  · intro h i n hn
    have := h n (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hn⟩); omega
  · intro h n hn
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hn).2
    have := h i n hi; omega

lemma uOf_le_N {k : ℕ} (c : Fin k → (Fin N → ℕ) × ℕ) : uOf c ≤ N :=
  (uOf_le_iff c N).mpr fun _ n _ => n.isLt

lemma smooth_pos {Dmax X₀ d : ℕ} (hd : d ∈ Nat.smoothNumbersUpTo Dmax X₀) : 0 < d := by
  rw [Nat.mem_smoothNumbersUpTo] at hd
  exact Nat.pos_of_ne_zero hd.2.1

lemma cval_pos {q : Fin N → ℝ} {D Dmax X₀ : ℕ} {x : (Fin N → ℕ) × ℕ}
    (hx : x ∈ rowSet N D Dmax X₀) (hq : ∀ n, x.1 n ≠ 0 → 0 < q n) : 0 < cval q x := by
  unfold cval
  have hd : (0 : ℝ) < x.2 := by
    exact_mod_cast smooth_pos (Finset.mem_product.mp hx).2
  refine mul_pos hd (Finset.prod_pos fun n _ => ?_)
  by_cases h : x.1 n = 0
  · simp [h]
  · exact pow_pos (hq n h) _

lemma geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (D : ℕ) :
    ∑ e ∈ range (D + 1), x ^ e ≤ (1 - x)⁻¹ := by
  have h := geom_sum_mul_neg x (D + 1)
  have h1 : 0 < 1 - x := by linarith
  calc ∑ e ∈ range (D + 1), x ^ e = (∑ e ∈ range (D + 1), x ^ e) * (1 - x) / (1 - x) := by
        field_simp
    _ = (1 - x ^ (D + 1)) / (1 - x) := by rw [h]
    _ ≤ 1 / (1 - x) := div_le_div_of_nonneg_right (by linarith [pow_nonneg hx0 (D + 1)]) h1.le
    _ = (1 - x)⁻¹ := one_div _

lemma tailSum_nonneg (Dmax X₀ : ℕ) : 0 ≤ tailSum Dmax X₀ :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **One row**: the contents with free slots in `allowed` sum to at most
`R_D ∏_{n allowed} (1 - 1/q_n)^{-1}`. -/
lemma rowSum_le {q : Fin N → ℝ} (allowed : Fin N → Prop) (hq : ∀ n, allowed n → 1 < q n)
    (D Dmax X₀ : ℕ) :
    ∑ x ∈ rowSet N D Dmax X₀, (if ∀ n, x.1 n ≠ 0 → allowed n then (cval q x)⁻¹ else 0) ≤
      tailSum Dmax X₀ * ∏ n ∈ univ.filter allowed, (1 - (q n)⁻¹)⁻¹ := by
  set f : Fin N → ℕ → ℝ := fun n e => if e = 0 ∨ allowed n then (q n)⁻¹ ^ e else 0 with hf
  have hterm : ∀ x : (Fin N → ℕ) × ℕ,
      (if ∀ n, x.1 n ≠ 0 → allowed n then (cval q x)⁻¹ else 0) =
        (x.2 : ℝ)⁻¹ * ∏ n, f n (x.1 n) := by
    intro x
    by_cases hc : ∀ n, x.1 n ≠ 0 → allowed n
    · rw [if_pos hc, cval, mul_inv, ← Finset.prod_inv_distrib]
      congr 1
      refine Finset.prod_congr rfl fun n _ => ?_
      have : x.1 n = 0 ∨ allowed n := by
        by_cases h : x.1 n = 0
        · exact Or.inl h
        · exact Or.inr (hc n h)
      rw [hf]; simp only [if_pos this, inv_pow]
    · rw [if_neg hc]
      push_neg at hc
      obtain ⟨n, hn0, hna⟩ := hc
      have h0 : f n (x.1 n) = 0 := by
        simp only [hf]; rw [if_neg]; push_neg; exact ⟨hn0, hna⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ n) h0, mul_zero]
  simp_rw [hterm]
  rw [rowSet, Finset.sum_product, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change tailSum Dmax X₀ * _ ≤ _
  refine mul_le_mul_of_nonneg_left ?_ (tailSum_nonneg _ _)
  rw [← Finset.prod_univ_sum (fun _ => range (D + 1)) f]
  rw [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro n _
    refine Finset.sum_nonneg fun e _ => ?_
    simp only [hf]
    split_ifs with h
    · rcases h with h | h
      · subst h; simp
      · exact pow_nonneg (inv_nonneg.mpr (by linarith [hq n h])) _
    · exact le_rfl
  · intro n _
    by_cases ha : allowed n
    · rw [if_pos ha]
      have hq1 := hq n ha
      have : ∑ e ∈ range (D + 1), f n e = ∑ e ∈ range (D + 1), (q n)⁻¹ ^ e :=
        Finset.sum_congr rfl fun e _ => by simp [hf, ha]
      rw [this]
      exact geom_le (inv_nonneg.mpr (by linarith)) (inv_lt_one_of_one_lt₀ hq1) D
    · rw [if_neg ha]
      have : ∑ e ∈ range (D + 1), f n e = ∑ e ∈ range (D + 1), if e = 0 then 1 else 0 :=
        Finset.sum_congr rfl fun e _ => by
          by_cases he : e = 0
          · simp [hf, he]
          · simp [hf, he, ha]
      rw [this, Finset.sum_ite_eq' (range (D + 1)) 0]
      simp

/-- The contents of the `k` rows. -/
noncomputable def contents (k N D Dmax X₀ : ℕ) : Finset (Fin k → (Fin N → ℕ) × ℕ) :=
  Fintype.piFinset fun _ : Fin k => rowSet N D Dmax X₀

/-- Every free slot of the content is decided. -/
def DecOK {k : ℕ} (ok : Fin N → Prop) (c : Fin k → (Fin N → ℕ) × ℕ) : Prop :=
  ∀ i n, (c i).1 n ≠ 0 → ok n

lemma prod_inv_cval_nonneg {k : ℕ} {q : Fin N → ℝ} {ok : Fin N → Prop}
    (hq : ∀ n, ok n → 1 < q n) {D Dmax X₀ : ℕ} {c : Fin k → (Fin N → ℕ) × ℕ}
    (hc : c ∈ contents k N D Dmax X₀) (hok : DecOK ok c) : 0 ≤ ∏ i, (cval q (c i))⁻¹ :=
  Finset.prod_nonneg fun i _ => (inv_pos.mpr (cval_pos (Fintype.mem_piFinset.mp hc i)
    fun n hn => by linarith [hq n (hok i n hn)])).le

/-- **The contents with free slots before `M`**: at most `(R_D ∏_{decided n < M}
(1 - 1/q_n)^{-1})^k`. -/
lemma contentSum_le {k : ℕ} {q : Fin N → ℝ} (ok : Fin N → Prop) (hq : ∀ n, ok n → 1 < q n)
    (D Dmax X₀ M : ℕ) :
    ∑ c ∈ contents k N D Dmax X₀,
      (if DecOK ok c ∧ uOf c ≤ M then ∏ i, (cval q (c i))⁻¹ else 0) ≤
      (tailSum Dmax X₀ * ∏ n ∈ univ.filter (fun n => ok n ∧ (n : ℕ) < M),
        (1 - (q n)⁻¹)⁻¹) ^ k := by
  set g : (Fin N → ℕ) × ℕ → ℝ := fun x =>
    if ∀ n, x.1 n ≠ 0 → ok n ∧ (n : ℕ) < M then (cval q x)⁻¹ else 0 with hg
  have hterm : ∀ c : Fin k → (Fin N → ℕ) × ℕ,
      (if DecOK ok c ∧ uOf c ≤ M then ∏ i, (cval q (c i))⁻¹ else 0) = ∏ i, g (c i) := by
    intro c
    have hiff : (DecOK ok c ∧ uOf c ≤ M) ↔
        ∀ i, ∀ n, (c i).1 n ≠ 0 → ok n ∧ (n : ℕ) < M := by
      rw [uOf_le_iff]
      constructor
      · rintro ⟨h1, h2⟩ i n hn; exact ⟨h1 i n hn, h2 i n hn⟩
      · intro h; exact ⟨fun i n hn => (h i n hn).1, fun i n hn => (h i n hn).2⟩
    by_cases h : DecOK ok c ∧ uOf c ≤ M
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hg]; simp only; rw [if_pos (hiff.mp h i)]
    · rw [if_neg h]
      rw [hiff] at h
      push_neg at h
      obtain ⟨i, n, hn, hfail⟩ := h
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hg]; simp only
      rw [if_neg]
      push_neg
      exact ⟨n, hn, fun h => hfail h⟩
  simp_rw [hterm]
  rw [contents, Finset.sum_prod_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hrow := rowSum_le (q := q) (fun n => ok n ∧ (n : ℕ) < M) (fun n h => hq n h.1) D Dmax X₀
  have hnn : 0 ≤ ∑ j ∈ rowSet N D Dmax X₀, g j := by
    refine Finset.sum_nonneg fun x hx => ?_
    rw [hg]; simp only
    split_ifs with h
    · exact (inv_pos.mpr (cval_pos hx fun n hn => by linarith [hq n (h n hn).1])).le
    · exact le_rfl
  have hrow' : ∑ j ∈ rowSet N D Dmax X₀, g j ≤
      tailSum Dmax X₀ * ∏ n ∈ univ.filter (fun n => ok n ∧ (n : ℕ) < M), (1 - (q n)⁻¹)⁻¹ := by
    rw [hg]; convert hrow
  exact pow_le_pow_left₀ hnn hrow' k

/-- **Lemma A.6 (S3)(c) for one run** (Euler chain of the early block and the tails). -/
theorem euler_oneRun {k : ℕ} {q : Fin N → ℝ} (ok : Fin N → Prop) (hq : ∀ n, ok n → 1 < q n)
    (D Dmax X₀ smax : ℕ) (G : ℕ → Prop) {A : ℝ} (hA : 0 ≤ A)
    (hS3 : ∀ u ≤ smax, G u → tailSum Dmax X₀ *
      ∏ n ∈ univ.filter (fun n => ok n ∧ (n : ℕ) < u), (1 - (q n)⁻¹)⁻¹ ≤ A) :
    ∑ c ∈ contents k N D Dmax X₀,
      (if DecOK ok c ∧ uOf c ≤ smax ∧ G (uOf c) then ∏ i, (cval q (c i))⁻¹ else 0) ≤ A ^ k := by
  set U := (range (N + 1)).filter fun u => u ≤ smax ∧ G u with hU
  by_cases hUe : U.Nonempty
  · set M := U.max' hUe with hM
    have hMU : M ∈ U := Finset.max'_mem U hUe
    obtain ⟨-, hMs, hGM⟩ := Finset.mem_filter.mp hMU
    have hle : ∀ c ∈ contents k N D Dmax X₀,
        (if DecOK ok c ∧ uOf c ≤ smax ∧ G (uOf c) then ∏ i, (cval q (c i))⁻¹ else 0) ≤
          (if DecOK ok c ∧ uOf c ≤ M then ∏ i, (cval q (c i))⁻¹ else 0) := by
      intro c hc
      by_cases h : DecOK ok c ∧ uOf c ≤ smax ∧ G (uOf c)
      · have hmem : uOf c ∈ U := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (uOf_le_N c)), h.2⟩
        rw [if_pos h, if_pos ⟨h.1, Finset.le_max' U _ hmem⟩]
      · rw [if_neg h]
        split_ifs with h'
        · exact prod_inv_cval_nonneg hq hc h'.1
        · exact le_rfl
    refine (Finset.sum_le_sum hle).trans ((contentSum_le ok hq D Dmax X₀ M).trans ?_)
    refine pow_le_pow_left₀ ?_ (hS3 M hMs hGM) k
    refine mul_nonneg (tailSum_nonneg _ _) (Finset.prod_nonneg fun n hn => ?_)
    have := hq n (Finset.mem_filter.mp hn).2.1
    have : (q n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    exact (inv_pos.mpr (by linarith)).le
  · have hzero : ∀ c ∈ contents k N D Dmax X₀,
        (if DecOK ok c ∧ uOf c ≤ smax ∧ G (uOf c) then ∏ i, (cval q (c i))⁻¹ else 0) = 0 := by
      intro c _
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact hUe ⟨uOf c, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (uOf_le_N c)), h1, h2⟩⟩
    rw [Finset.sum_eq_zero hzero]
    exact pow_nonneg hA k

end RankFull.Config
