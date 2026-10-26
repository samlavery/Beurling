module

public import Mathlib

/-!
# Theorem A.12 (Theorem R): the sum over run structures

In the proof of Theorem A.12 the polynomials `H_K` on `[0,1]` are defined by `H₀ := 1` and
(eq. (A.HK))
`H_K(E) := K ∑_{j=1}^{K} ∫_E^1 x^{j-1} H_{K-j}(x) dx`  (`K ≥ 1`),
and the paper shows (via the tree function) that `H_K(0) = K^K/K!`, that the sum of the chain
recursion `g_T` over all compositions of `K` is `H_K`, and that
`F_k(ρ) := H_k(ρ) + ∑_{j=1}^{k} ρ^j H_{k-j}(ρ)` is non-increasing on `[0,1]`, so
`F_k(ρ) ≤ F_k(0) = k^k/k!`.

Here we give an explicit closed form and prove all of this without power series:
`H_K(E) = ∑_{n ≤ K} a_{n,K}(E) - E ∑_{n ≤ K-1} a_{n,K-1}(E)`, with
`a_{n,i}(E) = n^n/n! · (-nE)^{i-n}/(i-n)!` (`hPoly`, `aCoef`). This is the coefficient of `z^K`
in the
paper's `P(E,z) = (1 - Ez)/(1 - ζ)`, `1/(1-ζ) = ∑_n n^n z^n e^{-nEz}/n!`. The boundary value
`H_K(1) = 0` is the identity `∑_n (-1)^{K-n} C(K,n) n^K = K!` (`fwdDiff_iter_eq_factorial`).

Main results:
* `RankFull.hPoly_rec` : the recursion (A.HK);
* `RankFull.hPoly_zero` : `H_K(0) = K^K/K!`;
* `RankFull.sum_comps_gRun` : the sum of `g_T` over the compositions of `K` is `H_K`;
* `RankFull.Fk_le` : `F_k(ρ) ≤ k^k/k!` for `ρ ∈ [0,1]`;
* `RankFull.sum_comps_fin_le` : the sum over run structures of
  `Fin(s) = G_T(Eu) + Eu^{j_T} G_{T-1}(Eu)` (with the cut-off at `A`) is at most `A^k k^k/k!`.

Conventions: a run structure `(j_1, …, j_T)` (latest run first, as in Lemma A.5) is stored as the
list `[j_T, …, j_1]`, i.e. **earliest run first**, because the recursion (A.Grec) builds `G_T`
from `G_{T-1}`: `gRun (j :: l) E = (j + l.sum) ∫_E^1 x^{j-1} gRun l x dx`, and `j + l.sum = K_T`.
-/

@[expose] public section

open Finset Real intervalIntegral

namespace RankFull

/-! ## The closed form -/

/-- `a_{n,i}(E) = n^n/n! · (-nE)^{i-n}/(i-n)!` for `n ≤ i`, and `0` for `n > i`. -/
noncomputable def aCoef (n i : ℕ) (E : ℝ) : ℝ :=
  if n ≤ i then (n : ℝ) ^ n / n.factorial * ((-(n : ℝ) * E) ^ (i - n) / (i - n).factorial)
  else 0

/-- The closed form of the polynomial `H_K` of the proof of Theorem A.12. -/
noncomputable def hPoly (K : ℕ) (E : ℝ) : ℝ :=
  ∑ n ∈ range (K + 1), aCoef n K E - E * ∑ n ∈ range K, aCoef n (K - 1) E

lemma aCoef_of_lt {n i : ℕ} (h : i < n) (E : ℝ) : aCoef n i E = 0 := by
  simp [aCoef, not_le.mpr h]

lemma continuous_aCoef (n i : ℕ) : Continuous (aCoef n i) := by
  unfold aCoef; split_ifs <;> fun_prop

lemma continuous_hPoly (K : ℕ) : Continuous (hPoly K) := by
  unfold hPoly
  exact (continuous_finset_sum _ fun n _ => continuous_aCoef n K).sub
    (continuous_id.mul (continuous_finset_sum _ fun n _ => continuous_aCoef n (K - 1)))

/-- Sums of `a_{n,i}` over `n` may be taken over any range containing `[0, i]`. -/
lemma sum_aCoef_eq {i N : ℕ} (hN : i + 1 ≤ N) (E : ℝ) :
    ∑ n ∈ range N, aCoef n i E = ∑ n ∈ range (i + 1), aCoef n i E := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro n hn hn'
  exact aCoef_of_lt (by simp at hn'; omega) E

lemma aCoef_zero_zero (E : ℝ) : aCoef 0 0 E = 1 := by simp [aCoef]

lemma sum_aCoef_zero (E : ℝ) : ∑ n ∈ range 1, aCoef n 0 E = 1 := by
  simp [aCoef_zero_zero]

lemma hasDerivAt_aCoef_zero (n : ℕ) (E : ℝ) : HasDerivAt (aCoef n 0) 0 E := by
  have : aCoef n 0 = fun _ => aCoef n 0 0 := by
    funext E'
    unfold aCoef
    split_ifs with h
    · have : n = 0 := by omega
      subst this; simp
    · rfl
  rw [this]; exact hasDerivAt_const _ _

lemma hasDerivAt_aCoef_succ (n i : ℕ) (E : ℝ) :
    HasDerivAt (aCoef n (i + 1)) (-(n : ℝ) * aCoef n i E) E := by
  rcases lt_trichotomy n (i + 1) with h | h | h
  · -- `n ≤ i`
    have hni : n ≤ i := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hni
    have hf : aCoef n (n + m + 1) =
        fun E => (n : ℝ) ^ n / n.factorial * ((-(n : ℝ) * E) ^ (m + 1) / (m + 1).factorial) := by
      funext E; unfold aCoef; rw [if_pos (by omega), show n + m + 1 - n = m + 1 by omega]
    have hg : aCoef n (n + m) E =
        (n : ℝ) ^ n / n.factorial * ((-(n : ℝ) * E) ^ m / m.factorial) := by
      simp [aCoef]
    rw [hf, hg]
    have h1 : HasDerivAt (fun E : ℝ => (-(n : ℝ) * E) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (-(n : ℝ) * E) ^ m * (-(n : ℝ))) E := by
      have := ((hasDerivAt_id E).const_mul (-(n : ℝ))).pow (m + 1)
      simpa using this
    have h2 := (h1.div_const ((m + 1).factorial : ℝ)).const_mul ((n : ℝ) ^ n / n.factorial)
    convert h2 using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  · -- `n = i + 1`: `a_{n,n}` is constant
    subst h
    have hf : aCoef (i + 1) (i + 1) = fun _ => aCoef (i + 1) (i + 1) 0 := by
      funext E; simp [aCoef]
    rw [hf, aCoef_of_lt (by omega : i < i + 1)]
    simpa using hasDerivAt_const E (aCoef (i + 1) (i + 1) 0)
  · have hf : aCoef n (i + 1) = fun _ => 0 := by funext E; exact aCoef_of_lt h E
    rw [hf, aCoef_of_lt (by omega : i < n)]
    simpa using hasDerivAt_const E (0 : ℝ)

/-- The key identity `n E a_{n,i} = (n - (i+1)) a_{n,i+1}`. -/
lemma aCoef_key (n i : ℕ) (E : ℝ) :
    (n : ℝ) * E * aCoef n i E = ((n : ℝ) - (i + 1)) * aCoef n (i + 1) E := by
  rcases lt_trichotomy n (i + 1) with h | h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ i)
    simp only [aCoef, show n ≤ n + m from by omega, show n ≤ n + m + 1 from by omega, if_true,
      show n + m + 1 - n = m + 1 by omega, show n + m - n = m by omega]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · subst h
    rw [aCoef_of_lt (by omega : i < i + 1)]
    push_cast; ring
  · rw [aCoef_of_lt (by omega : i < n), aCoef_of_lt (by omega : i + 1 < n)]; ring

/-- `hPoly (K+1)` in the form used for derivatives. -/
lemma hPoly_succ (K : ℕ) (E : ℝ) :
    hPoly (K + 1) E = ∑ n ∈ range (K + 2), (aCoef n (K + 1) E - E * aCoef n K E) := by
  unfold hPoly
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.add_sub_cancel,
    sum_aCoef_eq (by omega : K + 1 ≤ K + 2) E, sum_aCoef_eq (by omega : K + 1 ≤ K + 1) E]

/-- The telescoping identity `∑_{j=0}^{K} E^j H_{K-j}(E) = ∑_{n ≤ K} a_{n,K}(E)`. -/
lemma sum_pow_hPoly (K : ℕ) (E : ℝ) :
    ∑ j ∈ range (K + 1), E ^ j * hPoly (K - j) E = ∑ n ∈ range (K + 1), aCoef n K E := by
  induction K with
  | zero => simp [hPoly, aCoef_zero_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ', pow_zero, one_mul, Nat.sub_zero]
    have : ∑ j ∈ range (K + 1), E ^ (j + 1) * hPoly (K + 1 - (j + 1)) E =
        E * ∑ j ∈ range (K + 1), E ^ j * hPoly (K - j) E := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show K + 1 - (j + 1) = K - j by omega]; ring
    rw [this, ih, hPoly_succ, ← sum_aCoef_eq (by omega : K + 1 ≤ K + 2) E, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring

/-- The derivative of `H_{K+1}`: `H_{K+1}' = -(K+1) ∑_{j=0}^{K} E^j H_{K-j}(E)`. -/
lemma hasDerivAt_hPoly_succ (K : ℕ) (E : ℝ) :
    HasDerivAt (hPoly (K + 1))
      (-((K : ℝ) + 1) * ∑ j ∈ range (K + 1), E ^ j * hPoly (K - j) E) E := by
  rw [sum_pow_hPoly]
  have hfun : hPoly (K + 1) = fun E => ∑ n ∈ range (K + 2), (aCoef n (K + 1) E - E * aCoef n K E) :=
    funext (hPoly_succ K)
  rw [hfun]
  have hd : ∀ n ∈ range (K + 2), HasDerivAt (fun E => aCoef n (K + 1) E - E * aCoef n K E)
      (-((K : ℝ) + 1) * aCoef n K E) E := by
    intro n _
    rcases K with _ | K
    · have h1 := hasDerivAt_aCoef_succ n 0 E
      have h2 := (hasDerivAt_id E).mul (hasDerivAt_aCoef_zero n E)
      convert h1.sub h2 using 1
      simp only [id, mul_zero, add_zero, one_mul]
      unfold aCoef
      split_ifs with h
      · have : n = 0 := by omega
        subst this; simp
      · simp
    · have h1 := hasDerivAt_aCoef_succ n (K + 1) E
      have h2 := (hasDerivAt_id E).mul (hasDerivAt_aCoef_succ n K E)
      convert h1.sub h2 using 1
      simp only [id, one_mul]
      have hk := aCoef_key n K E
      push_cast at hk ⊢
      linear_combination (-1 : ℝ) * hk
  have := HasDerivAt.fun_sum hd
  rw [← Finset.mul_sum, sum_aCoef_eq (by omega : K + 1 ≤ K + 2) E] at this
  exact this

/-- `∑_{n ≤ K} n^n (-n)^{K-n}/(n!(K-n)!) = 1`: the `K`-th forward difference of `x^K` is `K!`. -/
lemma sum_aCoef_one (K : ℕ) : ∑ n ∈ range (K + 1), aCoef n K 1 = 1 := by
  have hfd := congr_fun (fwdDiff_iter_eq_factorial (R := ℝ) (n := K)) 0
  rw [fwdDiff_iter_eq_sum_shift] at hfd
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Pi.natCast_apply] at hfd
  have hK : (K.factorial : ℝ) ≠ 0 := by positivity
  have : ∑ n ∈ range (K + 1), aCoef n K 1 =
      (∑ k ∈ range (K + 1), (((-1 : ℤ) ^ (K - k) * K.choose k : ℤ) : ℝ) * (k : ℝ) ^ K) /
        K.factorial := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnK : n ≤ K := by simp at hn; omega
    simp only [aCoef, hnK, if_true, mul_one]
    push_cast
    rw [Nat.cast_choose ℝ hnK]
    have hnk : (n : ℝ) ^ K = (n : ℝ) ^ n * (n : ℝ) ^ (K - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hnK]
    rw [hnk, neg_pow]
    have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((K - n).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [this, hfd]
  field_simp

/-- **`H_K(1) = 0` for `K ≥ 1`.** -/
lemma hPoly_succ_one (K : ℕ) : hPoly (K + 1) 1 = 0 := by
  unfold hPoly
  rw [Nat.add_sub_cancel, sum_aCoef_one, sum_aCoef_eq (by omega : K + 1 ≤ K + 1), sum_aCoef_one]
  ring

/-- **`H_K(0) = K^K/K!`** (proof of Theorem A.12). -/
theorem hPoly_zero (K : ℕ) : hPoly K 0 = (K : ℝ) ^ K / K.factorial := by
  unfold hPoly
  simp only [zero_mul, sub_zero]
  rw [Finset.sum_eq_single K]
  · simp [aCoef]
  · intro n hn hnK
    have : n < K := by simp at hn; omega
    simp [aCoef, this.le, Nat.sub_ne_zero_of_lt this]
  · simp

lemma hPoly_zero_left (E : ℝ) : hPoly 0 E = 1 := by simp [hPoly, aCoef_zero_zero]

/-- **The recursion (A.HK)**: `H_{K+1}(E) = (K+1) ∑_{j=0}^{K} ∫_E^1 x^j H_{K-j}(x) dx`
(the paper's `j` is our `j + 1`). -/
theorem hPoly_rec (K : ℕ) (E : ℝ) :
    hPoly (K + 1) E =
      ((K : ℝ) + 1) * ∑ j ∈ range (K + 1), ∫ x in E..1, x ^ j * hPoly (K - j) x := by
  have hcont :
      Continuous fun x => -((K : ℝ) + 1) * ∑ j ∈ range (K + 1), x ^ j * hPoly (K - j) x := by
    exact continuous_const.mul (continuous_finset_sum _ fun j _ =>
      (continuous_pow j).mul (continuous_hPoly (K - j)))
  have hftc := integral_eq_sub_of_hasDerivAt (a := E) (b := 1)
    (fun x _ => hasDerivAt_hPoly_succ K x) (hcont.intervalIntegrable _ _)
  rw [hPoly_succ_one, intervalIntegral.integral_const_mul] at hftc
  rw [← intervalIntegral.integral_finset_sum]
  · linarith
  · intro j _
    exact ((continuous_pow j).mul (continuous_hPoly (K - j))).intervalIntegrable _ _

/-- `H_K ≥ 0` on `[0,1]`. -/
theorem hPoly_nonneg (K : ℕ) : ∀ E ∈ Set.Icc (0 : ℝ) 1, 0 ≤ hPoly K E := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro E hE
    rcases K with _ | K
    · rw [hPoly_zero_left]; norm_num
    · rw [hPoly_rec]
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j hj => ?_)
      refine intervalIntegral.integral_nonneg hE.2 fun x hx => ?_
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hE.1.trans hx.1, hx.2⟩
      exact mul_nonneg (pow_nonneg hx'.1 j) (ih (K - j) (by omega) x hx')

/-- The derivative of `H_K` (for every `K`, with `H_0' = 0`). -/
noncomputable def hPolyDeriv (K : ℕ) (E : ℝ) : ℝ :=
  -(K : ℝ) * ∑ j ∈ range K, E ^ j * hPoly (K - 1 - j) E

lemma hasDerivAt_hPoly (K : ℕ) (E : ℝ) : HasDerivAt (hPoly K) (hPolyDeriv K E) E := by
  rcases K with _ | K
  · have : hPoly 0 = fun _ => 1 := funext hPoly_zero_left
    rw [this]; simpa [hPolyDeriv] using hasDerivAt_const E (1 : ℝ)
  · have := hasDerivAt_hPoly_succ K E
    unfold hPolyDeriv
    push_cast
    simpa [Nat.add_sub_cancel] using this

lemma hPolyDeriv_nonpos (K : ℕ) {E : ℝ} (hE : E ∈ Set.Icc (0 : ℝ) 1) : hPolyDeriv K E ≤ 0 := by
  unfold hPolyDeriv
  have : 0 ≤ ∑ j ∈ range K, E ^ j * hPoly (K - 1 - j) E :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hE.1 j) (hPoly_nonneg _ E hE)
  have : (0 : ℝ) ≤ K := by positivity
  nlinarith

/-! ## `F_k` -/

/-- `F_k(ρ) := H_k(ρ) + ∑_{j=1}^{k} ρ^j H_{k-j}(ρ)` (proof of Theorem A.12). -/
noncomputable def Fk (k : ℕ) (ρ : ℝ) : ℝ :=
  hPoly k ρ + ∑ j ∈ range k, ρ ^ (j + 1) * hPoly (k - 1 - j) ρ

lemma hasDerivAt_Fk (k : ℕ) (ρ : ℝ) :
    HasDerivAt (Fk k) (hPolyDeriv k ρ + ∑ j ∈ range k,
      (((j : ℝ) + 1) * ρ ^ j * hPoly (k - 1 - j) ρ +
        ρ ^ (j + 1) * hPolyDeriv (k - 1 - j) ρ)) ρ := by
  unfold Fk
  refine (hasDerivAt_hPoly k ρ).add (HasDerivAt.fun_sum fun j _ => ?_)
  have h1 := (hasDerivAt_pow (j + 1) ρ).mul (hasDerivAt_hPoly (k - 1 - j) ρ)
  convert h1 using 1
  push_cast; ring

lemma Fk_deriv_nonpos (k : ℕ) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    hPolyDeriv k ρ + ∑ j ∈ range k,
      (((j : ℝ) + 1) * ρ ^ j * hPoly (k - 1 - j) ρ +
        ρ ^ (j + 1) * hPolyDeriv (k - 1 - j) ρ) ≤ 0 := by
  unfold hPolyDeriv
  rw [Finset.sum_add_distrib, Finset.mul_sum, ← add_assoc, ← Finset.sum_add_distrib]
  apply add_nonpos
  · apply Finset.sum_nonpos
    intro j hj
    have hjk : (j : ℝ) + 1 ≤ k := by
      have : j + 1 ≤ k := by simp at hj; omega
      exact_mod_cast this
    have h0 := hPoly_nonneg (k - 1 - j) ρ hρ
    have h1 : 0 ≤ ρ ^ j := pow_nonneg hρ.1 j
    nlinarith [mul_nonneg h1 h0]
  · apply Finset.sum_nonpos
    intro j _
    have := hPolyDeriv_nonpos (k - 1 - j) hρ
    unfold hPolyDeriv at this
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hρ.1 _) this

/-- **`F_k(ρ) ≤ F_k(0) = k^k/k!`** for `ρ ∈ [0,1]` (proof of Theorem A.12). -/
theorem Fk_le (k : ℕ) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    Fk k ρ ≤ (k : ℝ) ^ k / k.factorial := by
  have hanti : AntitoneOn (Fk k) (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun x _ => (hasDerivAt_Fk k x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_Fk k x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_Fk k x).deriv]
      exact Fk_deriv_nonpos k (interior_subset hx)
  have h0 : Fk k 0 = (k : ℝ) ^ k / k.factorial := by
    simp [Fk, hPoly_zero]
  rw [← h0]
  exact hanti ⟨le_rfl, zero_le_one⟩ hρ hρ.1

lemma Fk_one (k : ℕ) (hk : 1 ≤ k) : Fk k 1 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold Fk
  rw [add_comm 1 k, hPoly_succ_one, zero_add]
  have := sum_pow_hPoly k 1
  simp only [one_pow, one_mul] at this ⊢
  rw [Nat.add_sub_cancel]
  rw [this, sum_aCoef_one]

/-! ## Run structures and the chain recursion -/

/-- The compositions of `K` (the run structures of Theorem A.12), stored **earliest run first**. -/
def comps : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | K + 1 => (range (K + 1)).biUnion fun i => (comps (K - i)).image (List.cons (i + 1))

/-- `comps K` is exactly the set of lists of positive integers with sum `K`. -/
theorem mem_comps : ∀ (K : ℕ) (l : List ℕ), l ∈ comps K ↔ (∀ j ∈ l, 1 ≤ j) ∧ l.sum = K
  | 0, l => by
    simp only [comps, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨hpos, hsum⟩
      cases l with
      | nil => rfl
      | cons j l =>
        have := hpos j (by simp)
        simp at hsum; omega
  | K + 1, l => by
    simp only [comps, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, l', hl', rfl⟩
      rw [mem_comps] at hl'
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact hl'.1 j hj
      · simp [hl'.2]; omega
    · rintro ⟨hpos, hsum⟩
      cases l with
      | nil => simp at hsum
      | cons j l =>
        have hj := hpos j (by simp)
        simp only [List.sum_cons] at hsum
        refine ⟨j - 1, by omega, l, (mem_comps _ _).mpr ⟨fun j' hj' => hpos j' (by simp [hj']), ?_⟩,
          by congr 1; omega⟩
        omega

/-- The chain recursion (A.Grec) with `A = 1`, for a run structure `l` (earliest run first):
`g_T(E) = K_T ∫_E^1 x^{j_T - 1} g_{T-1}(x) dx`, `K_T = j_T + (j_{T-1} + ⋯ + j_1)`. -/
noncomputable def gRun : List ℕ → ℝ → ℝ
  | [] => fun _ => 1
  | j :: l => fun E => ((j + l.sum : ℕ) : ℝ) * ∫ x in E..1, x ^ (j - 1) * gRun l x

lemma continuous_gRun : ∀ l : List ℕ, Continuous (gRun l)
  | [] => continuous_const
  | j :: l => by
    have hf : Continuous fun x : ℝ => x ^ (j - 1) * gRun l x :=
      (continuous_pow _).mul (continuous_gRun l)
    have : (fun E => ∫ x in E..1, x ^ (j - 1) * gRun l x) =
        fun E => -∫ x in (1 : ℝ)..E, x ^ (j - 1) * gRun l x := by
      funext E; exact intervalIntegral.integral_symm _ _
    have hprim : Continuous fun E => ∫ x in E..1, x ^ (j - 1) * gRun l x := by
      rw [this]
      exact (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 1).neg
    exact continuous_const.mul hprim

/-- **Splitting off the last run** (proof of Theorem A.12): the sum of `g_T` over all
compositions of `K` is `H_K`. -/
theorem sum_comps_gRun (K : ℕ) (E : ℝ) : ∑ l ∈ comps K, gRun l E = hPoly K E := by
  induction K using Nat.strong_induction_on generalizing E with
  | _ K ih =>
    rcases K with _ | K
    · simp [comps, gRun, hPoly_zero_left]
    · rw [comps, Finset.sum_biUnion]
      · rw [hPoly_rec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ K := by simp at hi; omega
        rw [Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
        have hterm : ∀ l ∈ comps (K - i), gRun ((i + 1) :: l) E =
            ((K : ℝ) + 1) * ∫ x in E..1, x ^ i * gRun l x := by
          intro l hl
          have hs := ((mem_comps _ _).mp hl).2
          simp only [gRun, Nat.add_sub_cancel, hs]
          congr 1
          push_cast [Nat.cast_sub hi']; ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← intervalIntegral.integral_finset_sum]
        · congr 1
          refine intervalIntegral.integral_congr fun x _ => ?_
          rw [← Finset.mul_sum, ih (K - i) (by omega)]
        · intro l _
          exact ((continuous_pow i).mul (continuous_gRun l)).intervalIntegrable _ _
      · intro i _ i' _ hii'
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro l hl hl'
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hl'
        have := (List.cons_eq_cons.mp hb).1
        exact hii' (by omega)

/-- `Fin(s) = g_T(ρ) + ρ^{j_T} g_{T-1}(ρ)` for a run structure `j_T :: l` (with `A = 1`). -/
noncomputable def finRun : List ℕ → ℝ → ℝ
  | [] => fun _ => 1
  | j :: l => fun ρ => gRun (j :: l) ρ + ρ ^ j * gRun l ρ

/-- The sum of `Fin(s)` over the run structures of `k ≥ 1` is `F_k(ρ)`. -/
theorem sum_comps_finRun (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) :
    ∑ l ∈ comps k, finRun l ρ = Fk k ρ := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm 1 K]
  have hsplit : ∀ l ∈ comps (K + 1), finRun l ρ =
      gRun l ρ + ρ ^ l.headI * gRun l.tail ρ := by
    intro l hl
    cases l with
    | nil => simp [comps] at hl
    | cons j l => rfl
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, sum_comps_gRun, Fk]
  congr 1
  rw [comps, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp only [List.headI_cons, List.tail_cons]
    rw [← Finset.mul_sum, sum_comps_gRun, show K + 1 - 1 - i = K - i by omega]
  · intro i _ i' _ hii'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hl'
    have := (List.cons_eq_cons.mp hb).1
    exact hii' (by omega)

/-- **The sum over run structures in Theorem A.12**: `∑_{run structures} Fin(s) ≤ k^k/k!`
for `ρ = Eu_rat/A ∈ [0,1]` (with `A = 1`; see `sum_comps_finG_le` for general `A`). -/
theorem sum_comps_finRun_le (k : ℕ) (hk : 1 ≤ k) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ∑ l ∈ comps k, finRun l ρ ≤ (k : ℝ) ^ k / k.factorial := by
  rw [sum_comps_finRun k hk]; exact Fk_le k hρ

/-! ## The recursion (A.Grec) with top `A` -/

/-- **The chain recursion (A.Grec)** of Lemma A.6 (S3), for a list of run increments
`j_T :: ⋯ :: j_1` (earliest run first; `j_t = 0` is allowed):
`G_0 ≡ 1`, `G_t(E) = ∫_E^A K_t x^{j_t - 1} G_{t-1}(x) dx` for `E < A`, `G_t(E) = 0` for `E ≥ A`,
with `K_t = j_1 + ⋯ + j_t`. -/
noncomputable def GRun (A : ℝ) : List ℕ → ℝ → ℝ
  | [] => fun _ => 1
  | j :: l => fun E =>
      if E < A then ∫ x in E..A, ((j + l.sum : ℕ) : ℝ) * x ^ ((j : ℤ) - 1) * GRun A l x else 0

/-- `Fin = G_T(Eu) + Eu^{j_T} G_{T-1}(Eu)` (Lemma A.6 (S3)(c)). -/
noncomputable def finG (A : ℝ) : List ℕ → ℝ → ℝ
  | [] => fun _ => 1
  | j :: l => fun E => GRun A (j :: l) E + E ^ j * GRun A l E

/-- Scaling: for a composition (all `j_t ≥ 1`), `G_T(E) = A^{K_T} g_T(E/A)` on `E ≤ A`. -/
theorem GRun_eq_scale {A : ℝ} (hA : 0 < A) :
    ∀ l : List ℕ, (∀ j ∈ l, 1 ≤ j) → ∀ E ≤ A, GRun A l E = A ^ l.sum * gRun l (E / A)
  | [] => by intros; simp [GRun, gRun]
  | j :: l => by
    intro hpos E hE
    have hj := hpos j (by simp)
    have ihl := GRun_eq_scale hA l (fun j' hj' => hpos j' (by simp [hj']))
    simp only [GRun, gRun, List.sum_cons]
    rcases hE.lt_or_eq with hlt | rfl
    · rw [if_pos hlt]
      have hcongr : ∫ x in E..A, ((j + l.sum : ℕ) : ℝ) * x ^ ((j : ℤ) - 1) * GRun A l x =
          ∫ x in E..A, ((j + l.sum : ℕ) : ℝ) * x ^ (j - 1) * (A ^ l.sum * gRun l (x / A)) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        have hx : x ≤ A := by
          rw [Set.uIcc_of_le hlt.le] at hx; exact hx.2
        rw [ihl x hx, show ((j : ℤ) - 1) = ((j - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      rw [hcongr]
      have hsub := intervalIntegral.integral_comp_mul_left
        (fun x => ((j + l.sum : ℕ) : ℝ) * x ^ (j - 1) * (A ^ l.sum * gRun l (x / A)))
        (a := E / A) (b := 1) hA.ne'
      simp only [smul_eq_mul] at hsub
      rw [show A * (E / A) = E by field_simp, mul_one] at hsub
      have hEA : (∫ x in E..A, ((j + l.sum : ℕ) : ℝ) * x ^ (j - 1) * (A ^ l.sum * gRun l (x / A)))
          = A * ∫ x in E / A..1, ((j + l.sum : ℕ) : ℝ) * (A * x) ^ (j - 1) *
              (A ^ l.sum * gRun l (A * x / A)) := by
        rw [hsub, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
      rw [hEA]
      have hc : ∀ x : ℝ,
          ((j + l.sum : ℕ) : ℝ) * (A * x) ^ (j - 1) * (A ^ l.sum * gRun l (A * x / A))
          = (A ^ (j - 1) * A ^ l.sum * ((j + l.sum : ℕ) : ℝ)) * (x ^ (j - 1) * gRun l x) := by
        intro x
        rw [show A * x / A = x by field_simp, mul_pow]; ring
      simp_rw [hc]
      rw [intervalIntegral.integral_const_mul]
      have : A ^ (j + l.sum) = A * (A ^ (j - 1) * A ^ l.sum) := by
        rw [← mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
      rw [this]; ring
    · rw [if_neg (lt_irrefl _), div_self hA.ne', intervalIntegral.integral_same, mul_zero, mul_zero]

/-- **The sum over run structures in Theorem A.12**, with top `A > 0` and `0 ≤ Eu ≤ A`:
`∑_{(j_1,…,j_T)} [G_T(Eu) + Eu^{j_T} G_{T-1}(Eu)] = A^k F_k(Eu/A) ≤ A^k k^k/k!`. -/
theorem sum_comps_finG_le (k : ℕ) (hk : 1 ≤ k) {A Eu : ℝ} (hA : 0 < A) (hEu0 : 0 ≤ Eu)
    (hEu : Eu ≤ A) :
    ∑ l ∈ comps k, finG A l Eu ≤ A ^ k * ((k : ℝ) ^ k / k.factorial) := by
  have hρ : Eu / A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hEu0 hA.le, (div_le_one hA).mpr hEu⟩
  have heq : ∀ l ∈ comps k, finG A l Eu = A ^ k * finRun l (Eu / A) := by
    intro l hl
    obtain ⟨hpos, hsum⟩ := (mem_comps _ _).mp hl
    cases l with
    | nil => simp at hsum; omega
    | cons j l =>
      have hpos' : ∀ j' ∈ l, 1 ≤ j' := fun j' hj' => hpos j' (by simp [hj'])
      simp only [finG, finRun]
      rw [GRun_eq_scale hA _ hpos Eu hEu, GRun_eq_scale hA l hpos' Eu hEu, hsum]
      simp only [List.sum_cons] at hsum
      have : Eu ^ j = A ^ j * (Eu / A) ^ j := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hA.ne')]
      rw [this, ← hsum, pow_add]; ring
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, sum_comps_finRun k hk]
  exact mul_le_mul_of_nonneg_left (Fk_le k hρ) (pow_nonneg hA.le k)

end RankFull
