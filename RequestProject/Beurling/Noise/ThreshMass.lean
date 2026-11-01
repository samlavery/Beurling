module

public import RequestProject.Beurling.Noise.ThreshMassPrime

/-!
# Lemma 5.23 (threshold mass)

For `x ≥ X₀³` and `6H(x)x^{-1/3} ≤ δ ≤ 1/4` (04e-lp.tex, Lemma 5.23):

  `∑_{n : τ(n) ∈ [x(1-δ), x)} 1/n ≤ 55 δ log x (log H(x) + log(1/δ) + 2)
      + 14 (K_loc(√x) + 2) log x √(H(x)/(δx))`.

The proof is the paper's: the decomposition `n = k m` (`threshSum_le_split`), the bounds
`∑_k 1/k ≤ 2 log x` and `1/m ≤ t(p)/(x(1-δ))`, and the two cases (i) `p ≤ √(δx/(2H))` and
(ii) `p > √(δx/(2H))`. In case (ii) the jitter bound `|t(p) - p| ≤ δp/20`, the fact `m' = 1`, the
`p`-interval `[a_*, b_*)` and its length `≤ 0.6 δ √x` are proved here from the jitter hypotheses.

## Inputs (structure `ThreshHyp`)

The construction enters only through the following hypotheses, each a statement the paper's
proof uses:

* (HBS) on `[1, Z]` with `√x ≤ Z` (for `∑_{p ≤ √x} 1/p`, Lemma 5.1(iv));
* decision times `t ≥ 1` with the centred jitter `|t(p) - p| ≤ H(t(p))/2` (§5.1; `t(p) = p` for
  rational primes), `H(z) ≤ z/100` and `H` non-decreasing on `[1, ∞)`, `H(2z) ≤ 1.000003 H(z)`
  ((RH) with `w = 2`), `H(x) ≥ 1` and `log H(x) ≥ 16 log log x` (`H ≥ H_std`);
* `kSum` : `∑_k 1/k ≤ 2 log x` for each `p` that occurs (lines 31-45: the Euler product over the
  primes `t`-below `p`, bounded by Rosser–Schoenfeld and Lemma 5.1(iv); `sum_Kset_le_prod`
  reduces it to the Euler product);
* `countI` : case (i), `#{m'} ≤ 4δx/p²` (lines 56-77; uses the lag `|N - T| ≤ D`, Lemma P and
  the slot structure of the construction);
* `localCount` : the prime count `≤ 13.5 ℓ + K_loc(√x) + 2` on the `p`-interval of case (ii)
  (lines 85-91; Corollary localcount(i) applied to windows of length `≤ 6H(P₁)`).
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The endpoints of the `p`-interval of case (ii). -/
noncomputable def aStar (x δ : ℝ) : ℝ := √(x * (1 - δ) / (1 + δ / 20))
noncomputable def bStar (x δ : ℝ) : ℝ := √(x / (1 - δ / 20))

/-- The hypotheses of Lemma 5.23 (see the module docstring). -/
structure ThreshHyp (t : ℕ → ℝ) (Hf : ℝ → ℝ) (x δ Kloc X0m Z η1 η2 : ℝ) (ε1 : ℝ → ℝ) :
    Prop where
  hbs : P.HBS X0m Z η1 η2 ε1
  sqrt_le : √x ≤ Z
  x_ge : 16 ≤ x
  loglog : 0 ≤ Real.log (Real.log x)
  t_ge : ∀ j, 1 ≤ t j
  jit : ∀ j, |t j - P.p j| ≤ Hf (t j) / 2
  /-- `|t(p) - p| ≤ t(p)/200` (from `jit` and `H(z) ≤ z/100` at the decision times) -/
  jit_small : ∀ j, |t j - P.p j| ≤ t j / 200
  H_mono : MonotoneOn Hf (Set.Ici 1)
  H_two : ∀ z, 1 ≤ z → Hf (2 * z) ≤ 1.000003 * Hf z
  Hx_ge : 1 ≤ Hf x
  logH : 16 * Real.log (Real.log x) ≤ Real.log (Hf x)
  δ_ge : 6 * Hf x / x ^ ((1 : ℝ) / 3) ≤ δ
  δ_le : δ ≤ 1 / 4
  Kloc_nonneg : 0 ≤ Kloc
  kSum : ∀ j ∈ P.primesLe x, (P.Mset t x δ j).Nonempty →
    ∑ k ∈ P.Kset t x j, 1 / P.val k ≤ 2 * Real.log x
  countI : ∀ j ∈ P.primesLe x, P.p j ≤ √(δ * x / (2 * Hf x)) →
    ((P.Mset t x δ j).card : ℝ) ≤ 4 * δ * x / P.p j ^ 2
  localCount : (((P.primesLe x).filter
      (fun j => aStar x δ ≤ P.p j ∧ P.p j < bStar x δ)).card : ℝ) ≤
    13.5 * (bStar x δ - aStar x δ) + Kloc + 2

namespace ThreshHyp

variable {P} {t : ℕ → ℝ} {Hf : ℝ → ℝ} {x δ Kloc X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma δ_pos (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) : 0 < δ := by
  have h1 := h.δ_ge
  have hx : 0 < x := by linarith [h.x_ge]
  have : 0 < 6 * Hf x / x ^ ((1 : ℝ) / 3) :=
    div_pos (by linarith [h.Hx_ge]) (Real.rpow_pos_of_pos hx _)
  linarith

/-- `t(p) ≤ (200/199) p` and `p ≤ (201/200) t(p)`. -/
lemma t_le (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) (j : ℕ) :
    t j ≤ 200 / 199 * P.p j ∧ P.p j ≤ 201 / 200 * t j := by
  have h1 := h.jit_small j
  have h0 := h.t_ge j
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

/-- Case (ii): `|t(p) - p| ≤ δp/20`, `m' = 1`, and `p ∈ [a_*, b_*)`. -/
lemma caseII (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) {j : ℕ}
    (hj : √(δ * x / (2 * Hf x)) < P.p j) {m : ℕ →₀ ℕ} (hm : m ∈ P.Mset t x δ j) :
    m = Finsupp.single j 1 ∧ aStar x δ ≤ P.p j ∧ P.p j < bStar x δ ∧
      t j ≤ (1 + δ / 20) * P.p j := by
  obtain ⟨hmx, hs, hjm, hge, h1, h2⟩ := Finset.mem_filter.mp hm
  rw [mem_elems] at hmx
  have hx : 0 < x := by linarith [h.x_ge]
  have hH : 1 ≤ Hf x := h.Hx_ge
  have hδ := h.δ_pos
  set p := P.p j
  have hp0 : 0 < p := P.p_pos j
  have htj := h.t_ge j
  -- `p ≤ m ≤ x`
  have hpm : p ≤ P.val m := by
    rw [P.val_eq_prod_support hs, ← Finset.mul_prod_erase _ _ hjm]
    have := P.one_le_prod_p (m.support.erase j); nlinarith
  have hpx : p ≤ x := hpm.trans hmx
  -- `c = x^{1/3}`
  set c := x ^ ((1 : ℝ) / 3)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hx _
  have hc3 : c ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hδc : 6 * Hf x ≤ δ * c := by
    have := h.δ_ge; rwa [div_le_iff₀ hc0] at this
  -- `p² > 3c²`
  have hp2 : 3 * c ^ 2 < p ^ 2 := by
    have hs0 : 0 ≤ δ * x / (2 * Hf x) := by positivity
    have := (Real.sqrt_lt' hp0).mp hj
    have e : 3 * c ^ 2 ≤ δ * x / (2 * Hf x) := by
      rw [le_div_iff₀ (by linarith)]
      have ex : δ * x = c ^ 2 * (δ * c) := by rw [← hc3]; ring
      rw [ex]
      nlinarith [sq_nonneg c]
    linarith
  have hpc : 1.73 * c < p := by
    by_contra hcon
    push_neg at hcon
    have := pow_le_pow_left₀ hp0.le hcon 2
    nlinarith
  -- `p³ > 5x`
  have hp3 : 5 * x < p ^ 3 := by
    have h27 : 27 * x ^ 2 < (p ^ 3) ^ 2 := by
      have hlt : (3 * c ^ 2) ^ 3 < (p ^ 2) ^ 3 :=
        pow_lt_pow_left₀ hp2 (by positivity) (by norm_num)
      have e1 : (p ^ 3) ^ 2 = (p ^ 2) ^ 3 := by ring
      have e2 : 27 * x ^ 2 = (3 * c ^ 2) ^ 3 := by rw [← hc3]; ring
      rw [e1, e2]; exact hlt
    nlinarith [pow_pos hp0 3]
  -- the jitter: `|t - p| ≤ δp/20`
  obtain ⟨ht1, ht2⟩ := h.t_le j
  have hHp : Hf p ≤ Hf x := h.H_mono (Set.mem_Ici.mpr (by linarith [P.one_lt j]))
    (Set.mem_Ici.mpr (by linarith [h.x_ge])) hpx
  have hHt : Hf (t j) ≤ 1.000003 * Hf p := by
    have hp1 : 1 ≤ p := (P.one_lt j).le
    calc Hf (t j) ≤ Hf (2 * p) := h.H_mono (Set.mem_Ici.mpr htj)
          (Set.mem_Ici.mpr (by linarith)) (by linarith)
      _ ≤ 1.000003 * Hf p := h.H_two p hp1
  have hjit : |t j - p| ≤ δ * p / 20 := by
    refine (h.jit j).trans ?_
    have : Hf x ≤ δ * c / 6 := by linarith
    have : Hf p * 1.73 * c ≤ δ * c / 6 * p := by nlinarith
    have : Hf p ≤ δ * p / (6 * 1.73) := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    have : Hf (t j) / 2 ≤ 1.000003 * (δ * p / (6 * 1.73)) / 2 := by nlinarith
    have : 1.000003 * (δ * p / (6 * 1.73)) / 2 ≤ δ * p / 20 := by
      have e6 : δ * p / (6 * 1.73) = δ * p / 10.38 := by norm_num
      rw [e6]
      have hdp := mul_pos hδ hp0
      have key : 1.000003 * (δ * p / 10.38) / 2 = 1.000003 / 20.76 * (δ * p) := by ring
      have key2 : δ * p / 20 = 1 / 20 * (δ * p) := by ring
      rw [key, key2]
      apply mul_le_mul_of_nonneg_right (by norm_num) hdp.le
    linarith
  rw [abs_le] at hjit
  -- `m' = 1`
  have hsupp : m.support = {j} := by
    ext i
    rw [Finset.mem_singleton]
    refine ⟨fun hi => ?_, fun hi => hi ▸ hjm⟩
    by_contra hij
    have hti := (Finset.mem_filter.mp hm).2.2.2.1 i hi
    obtain ⟨hti1, -⟩ := h.t_le i
    have hpi : 0.99 * p ≤ P.p i := by
      have := h.jit_small i
      have hti0 := h.t_ge i
      rw [abs_le] at this
      linarith [this.1, hti, ht2]
    have hval : p * P.p i ≤ P.val m := by
      rw [P.val_eq_prod_support hs, ← Finset.mul_prod_erase _ _ hjm,
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij, hi⟩)]
      rw [show P.p j = p from rfl]
      have h1' := P.one_le_prod_p ((m.support.erase j).erase i)
      have hpi' := P.p_pos i
      calc p * P.p i = p * P.p i * 1 := by ring
        _ ≤ p * P.p i * ∏ x ∈ (m.support.erase j).erase i, P.p x :=
            mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = p * (P.p i * ∏ x ∈ (m.support.erase j).erase i, P.p x) := by ring
    have : t j * P.val m ≥ (200 / 201 * p) * (0.99 * p * p) := by
      have ht0 : 200 / 201 * p ≤ t j := by linarith
      have hpi0 : 0 ≤ 0.99 * p * p := by positivity
      calc t j * P.val m ≥ t j * (p * P.p i) := mul_le_mul_of_nonneg_left hval (by linarith)
        _ ≥ (200 / 201 * p) * (0.99 * p * p) := by
            apply mul_le_mul ht0 (by nlinarith) hpi0 (by linarith)
    have e : (200 / 201 * p) * (0.99 * p * p) = 198 / 201 * p ^ 3 := by ring
    linarith
  have hm1 : m = Finsupp.single j 1 := by
    ext i
    by_cases hi : i = j
    · rw [hi, Finsupp.single_eq_same]
      exact le_antisymm (hs j) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjm))
    · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
      exact Finsupp.notMem_support_iff.mp (by rw [hsupp, Finset.mem_singleton]; exact hi)
  have hvm : P.val m = p := by rw [hm1]; simp [val_single, p]
  rw [hvm] at h1 h2
  refine ⟨hm1, ?_, ?_, by linarith⟩
  · unfold aStar
    refine (Real.sqrt_le_left hp0.le).mpr ?_
    rw [div_le_iff₀ (by linarith)]
    have ht' : t j ≤ (1 + δ / 20) * p := by linarith [hjit.2]
    have hq : t j * p ≤ (1 + δ / 20) * p * p := mul_le_mul_of_nonneg_right ht' hp0.le
    have hδ20 : 0 < 1 + δ / 20 := by linarith
    calc x * (1 - δ) ≤ t j * p := h1
      _ ≤ (1 + δ / 20) * p * p := hq
      _ = p ^ 2 * (1 + δ / 20) := by ring
  · unfold bStar
    rw [Real.lt_sqrt hp0.le, lt_div_iff₀ (by linarith [h.δ_le])]
    have ht' : (1 - δ / 20) * p ≤ t j := by linarith [hjit.1]
    have hq : (1 - δ / 20) * p * p ≤ t j * p := mul_le_mul_of_nonneg_right ht' hp0.le
    calc p ^ 2 * (1 - δ / 20) = (1 - δ / 20) * p * p := by ring
      _ ≤ t j * p := hq
      _ < x := h2

/-- `b_* ≤ (1 + 0.026δ)√x` and `a_* ≥ (1 - 0.574δ)√x`, so `b_* - a_* ≤ 0.6δ√x`
(the paper: `f(δ) ≤ 0.58259 δ` by convexity). -/
lemma ab_bounds (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) :
    bStar x δ ≤ (1 + 0.026 * δ) * √x ∧ (1 - 0.574 * δ) * √x ≤ aStar x δ := by
  have hδ := h.δ_pos
  have hδ4 := h.δ_le
  have hx : 0 < x := by linarith [h.x_ge]
  have hsx := Real.sq_sqrt hx.le
  have hs0 := Real.sqrt_nonneg x
  constructor
  · unfold bStar
    refine (Real.sqrt_le_left (by positivity)).mpr ?_
    rw [div_le_iff₀ (by linarith), mul_pow, hsx]
    have : 1 ≤ (1 + 0.026 * δ) ^ 2 * (1 - δ / 20) := by
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ4),
        mul_nonneg (mul_nonneg hδ.le hδ.le) (sub_nonneg.mpr hδ4),
        mul_nonneg (mul_nonneg hδ.le hδ.le) hδ.le, hδ]
    nlinarith
  · unfold aStar
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ (by linarith), mul_pow, hsx]
    have : (1 - 0.574 * δ) ^ 2 * (1 + δ / 20) ≤ 1 - δ := by
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ4),
        mul_nonneg (mul_nonneg hδ.le hδ.le) (sub_nonneg.mpr hδ4),
        mul_nonneg (mul_nonneg hδ.le hδ.le) hδ.le, hδ]
    nlinarith

lemma sum_Mset_le (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) (j : ℕ) :
    ∑ m ∈ P.Mset t x δ j, 1 / P.val m ≤ (P.Mset t x δ j).card * (t j / (x * (1 - δ))) := by
  have hx : 0 < x := by linarith [h.x_ge]
  have hd : 0 < x * (1 - δ) := mul_pos hx (by linarith [h.δ_le])
  rw [← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro m hm
  obtain ⟨-, -, -, -, h1, -⟩ := Finset.mem_filter.mp hm
  have hv := P.val_pos m
  have ht := h.t_ge j
  rw [div_le_div_iff₀ hv hd]
  nlinarith

/-- The term of `p_j`: `(∑_m 1/m)(∑_k 1/k) ≤ 2 log x · #Mset_j · t(p_j)/(x(1-δ))`. -/
lemma term_le (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) {j : ℕ} (hj : j ∈ P.primesLe x) :
    (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k ≤
      2 * Real.log x * ((P.Mset t x δ j).card * (t j / (x * (1 - δ)))) := by
  have hx : 0 < x := by linarith [h.x_ge]
  have hd : 0 < x * (1 - δ) := mul_pos hx (by linarith [h.δ_le])
  have hK0 : 0 ≤ ∑ k ∈ P.Kset t x j, 1 / P.val k :=
    Finset.sum_nonneg fun k _ => (one_div_pos.mpr (P.val_pos k)).le
  have hM0 : 0 ≤ ∑ m ∈ P.Mset t x δ j, 1 / P.val m :=
    Finset.sum_nonneg fun m _ => (one_div_pos.mpr (P.val_pos m)).le
  have ht := h.t_ge j
  rcases (P.Mset t x δ j).eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  have hk := h.kSum j hj hne
  have hm := h.sum_Mset_le j
  have hL : 0 ≤ 2 * Real.log x := by
    have := Real.log_nonneg (by linarith [h.x_ge] : (1 : ℝ) ≤ x); linarith
  calc (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k
      ≤ ((P.Mset t x δ j).card * (t j / (x * (1 - δ)))) * (2 * Real.log x) :=
        mul_le_mul hm hk hK0 (by positivity)
    _ = _ := by ring

/-- Case (i): the term of `p_j ≤ √(δx/(2H))` is `≤ 10.73 δ log x / p_j`. -/
lemma term_caseI (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) {j : ℕ}
    (hj : j ∈ P.primesLe x) (hjs : P.p j ≤ √(δ * x / (2 * Hf x))) :
    (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k ≤
      10.73 * δ * Real.log x / P.p j := by
  have hx : 0 < x := by linarith [h.x_ge]
  have hδ := h.δ_pos
  have hδ4 := h.δ_le
  have hp := P.p_pos j
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith [h.x_ge])
  refine (h.term_le hj).trans ?_
  have hc := h.countI j hj hjs
  have ht := (h.t_le j).1
  have hd : 0 < x * (1 - δ) := mul_pos hx (by linarith)
  have h1 : ((P.Mset t x δ j).card : ℝ) * (t j / (x * (1 - δ))) ≤
      4 * δ * x / P.p j ^ 2 * (200 / 199 * P.p j / (x * (1 - δ))) := by
    apply mul_le_mul hc (div_le_div_of_nonneg_right ht hd.le)
      (div_nonneg (by linarith [h.t_ge j]) hd.le) (by positivity)
  have e : 4 * δ * x / P.p j ^ 2 * (200 / 199 * P.p j / (x * (1 - δ))) =
      800 / 199 * δ / ((1 - δ) * P.p j) := by
    field_simp; ring
  rw [e] at h1
  have h2 : 800 / 199 * δ / ((1 - δ) * P.p j) ≤ 800 / 199 * δ / (3 / 4 * P.p j) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith) hp.le)
  calc 2 * Real.log x * (((P.Mset t x δ j).card : ℝ) * (t j / (x * (1 - δ))))
      ≤ 2 * Real.log x * (800 / 199 * δ / (3 / 4 * P.p j)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)
    _ = 6400 / 597 * δ * Real.log x / P.p j := by field_simp; ring
    _ ≤ 10.73 * δ * Real.log x / P.p j := by
        apply div_le_div_of_nonneg_right _ hp.le
        have := mul_nonneg hδ.le hL
        nlinarith

/-- Case (ii): the term of `p_j > √(δx/(2H))` is `≤ 2.72 log x/√x`, and vanishes unless
`p_j ∈ [a_*, b_*)`. -/
lemma term_caseII (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) {j : ℕ}
    (hj : j ∈ P.primesLe x) (hjs : √(δ * x / (2 * Hf x)) < P.p j) :
    (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k ≤
      if aStar x δ ≤ P.p j ∧ P.p j < bStar x δ then 2.72 * Real.log x / √x else 0 := by
  have hx : 0 < x := by linarith [h.x_ge]
  have hδ := h.δ_pos
  have hδ4 := h.δ_le
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith [h.x_ge])
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  rcases (P.Mset t x δ j).eq_empty_or_nonempty with he | ⟨m, hm⟩
  · rw [he]; simp only [Finset.sum_empty, zero_mul]; split_ifs <;> positivity
  obtain ⟨hm1, ha, hb, ht⟩ := h.caseII hjs hm
  rw [if_pos ⟨ha, hb⟩]
  have hcard : ((P.Mset t x δ j).card : ℝ) ≤ 1 := by
    have : P.Mset t x δ j ⊆ {Finsupp.single j 1} := by
      intro m' hm'
      rw [Finset.mem_singleton]
      exact (h.caseII hjs hm').1
    exact_mod_cast (Finset.card_le_card this).trans (by simp)
  obtain ⟨hbx, -⟩ := h.ab_bounds
  have htx : t j ≤ 1.0192 * √x := by
    have : (1 + δ / 20) * P.p j ≤ (1 + 1 / 80) * ((1 + 0.026 / 4) * √x) := by
      apply mul_le_mul (by linarith) _ (P.p_pos j).le (by norm_num)
      refine hb.le.trans (hbx.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith) hsx.le
    nlinarith
  have hd : 0 < x * (1 - δ) := mul_pos hx (by linarith)
  refine (h.term_le hj).trans ?_
  have h1 : ((P.Mset t x δ j).card : ℝ) * (t j / (x * (1 - δ))) ≤
      1 * (1.0192 * √x / (x * (3 / 4))) := by
    apply mul_le_mul hcard _ (div_nonneg (by linarith [h.t_ge j]) hd.le) zero_le_one
    calc t j / (x * (1 - δ)) ≤ 1.0192 * √x / (x * (1 - δ)) :=
          div_le_div_of_nonneg_right htx hd.le
      _ ≤ 1.0192 * √x / (x * (3 / 4)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hx.le)
  calc 2 * Real.log x * (((P.Mset t x δ j).card : ℝ) * (t j / (x * (1 - δ))))
      ≤ 2 * Real.log x * (1 * (1.0192 * √x / (x * (3 / 4)))) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = 2 * 1.0192 / (3 / 4) * Real.log x / √x := by
        have e : x * (3 / 4) = √x * (√x * (3 / 4)) := by
          rw [← mul_assoc, Real.mul_self_sqrt hx.le]
        rw [e]; field_simp
    _ ≤ 2.72 * Real.log x / √x := by
        apply div_le_div_of_nonneg_right _ hsx.le
        nlinarith

/-- **Lemma 5.23 (threshold mass).** Under the hypotheses `ThreshHyp` (see the module
docstring), for `6H(x)x^{-1/3} ≤ δ ≤ 1/4`,
`∑_{n : τ(n) ∈ [x(1-δ), x)} 1/n ≤ 55 δ log x (log H(x) + log(1/δ) + 2)
  + 14 (K_loc + 2) log x √(H(x)/(δx))`. -/
theorem threshold_mass (h : P.ThreshHyp t Hf x δ Kloc X0m Z η1 η2 ε1) :
    P.threshSum t x δ ≤
      55 * δ * Real.log x * (Real.log (Hf x) + Real.log (1 / δ) + 2) +
        14 * (Kloc + 2) * Real.log x * √(Hf x / (δ * x)) := by
  have hx : 0 < x := by linarith [h.x_ge]
  have hδ := h.δ_pos
  have hδ4 := h.δ_le
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith [h.x_ge])
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  have hH := h.Hx_ge
  have hK := h.Kloc_nonneg
  set s0 := √(δ * x / (2 * Hf x))
  set A := (P.primesLe x).filter (fun j => aStar x δ ≤ P.p j ∧ P.p j < bStar x δ)
  -- split the sum over `j`
  have hsplit := P.threshSum_le_split t x δ
  have hterm : ∀ j ∈ P.primesLe x,
      (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k ≤
        (if P.p j ≤ s0 then 10.73 * δ * Real.log x / P.p j else 0) +
          (if j ∈ A then 2.72 * Real.log x / √x else 0) := by
    intro j hj
    by_cases hjs : P.p j ≤ s0
    · rw [if_pos hjs]
      have := h.term_caseI hj hjs
      have : 0 ≤ (if j ∈ A then 2.72 * Real.log x / √x else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [if_neg hjs, zero_add]
      push_neg at hjs
      have h2 := h.term_caseII hj hjs
      have hmem : (j ∈ A) ↔ (aStar x δ ≤ P.p j ∧ P.p j < bStar x δ) := by
        simp [A, Finset.mem_filter, hj]
      by_cases hc : aStar x δ ≤ P.p j ∧ P.p j < bStar x δ
      · rw [if_pos hc] at h2; rw [if_pos (hmem.mpr hc)]; exact h2
      · rw [if_neg hc] at h2; rw [if_neg (fun h' => hc (hmem.mp h'))]; exact h2
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  -- the case (i) sum
  have hs0 : s0 ≤ √x := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hI : ∑ j ∈ P.primesLe x, (if P.p j ≤ s0 then 10.73 * δ * Real.log x / P.p j else 0) ≤
      10.73 * δ * Real.log x * (Real.log (Real.log x) + 3.41) := by
    rw [← Finset.sum_filter]
    have hsub : (P.primesLe x).filter (fun j => P.p j ≤ s0) ⊆ P.primesLe √x := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [mem_primesLe]; exact hj.2.trans hs0
    have hx4 : 4 ≤ √x := by
      rw [Real.le_sqrt (by norm_num) hx.le]; linarith [h.x_ge]
    have hps := h.hbs.sum_inv_primesLe_le hx4 h.sqrt_le
    have hlog : Real.log (Real.log √x) ≤ Real.log (Real.log x) - 0.69 := by
      rw [Real.log_sqrt hx.le]
      have hl : 0 < Real.log x := Real.log_pos (by linarith [h.x_ge])
      rw [Real.log_div hl.ne' (by norm_num)]
      have := Real.log_two_gt_d9
      linarith
    calc ∑ j ∈ (P.primesLe x).filter (fun j => P.p j ≤ s0), 10.73 * δ * Real.log x / P.p j
        = 10.73 * δ * Real.log x *
            ∑ j ∈ (P.primesLe x).filter (fun j => P.p j ≤ s0), 1 / P.p j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 10.73 * δ * Real.log x * ∑ j ∈ P.primesLe √x, 1 / P.p j := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => (one_div_pos.mpr (P.p_pos j)).le)
      _ ≤ 10.73 * δ * Real.log x * (Real.log (Real.log x) + 3.41) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  -- the case (ii) sum
  have hII : ∑ j ∈ P.primesLe x, (if j ∈ A then 2.72 * Real.log x / √x else 0) ≤
      2.72 * Real.log x / √x * (8.1 * δ * √x + Kloc + 2) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hA : (P.primesLe x).filter (fun j => j ∈ A) = A := by
      ext j; simp only [Finset.mem_filter, A]; tauto
    rw [hA, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hc := h.localCount
    obtain ⟨hb, ha⟩ := h.ab_bounds
    have : bStar x δ - aStar x δ ≤ 0.6 * δ * √x := by nlinarith
    linarith
  -- assembly
  have hll := h.loglog
  have hlogH := h.logH
  have hlδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hsq : 1 / √x ≤ √(Hf x / (δ * x)) := by
    rw [one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    rw [inv_eq_one_div, div_le_div_iff₀ hx (by positivity)]
    nlinarith
  have hfin1 : 10.73 * δ * Real.log x * (Real.log (Real.log x) + 3.41) +
      2.72 * Real.log x / √x * (8.1 * δ * √x) ≤
      55 * δ * Real.log x * (Real.log (Hf x) + Real.log (1 / δ) + 2) := by
    have e : 2.72 * Real.log x / √x * (8.1 * δ * √x) = 22.032 * δ * Real.log x := by
      field_simp; ring
    rw [e]
    have hdl := mul_nonneg hδ.le hL
    nlinarith
  have hfin2 : 2.72 * Real.log x / √x * (Kloc + 2) ≤
      14 * (Kloc + 2) * Real.log x * √(Hf x / (δ * x)) := by
    have e : 2.72 * Real.log x / √x * (Kloc + 2) = 2.72 * (Kloc + 2) * Real.log x * (1 / √x) := by
      ring
    rw [e]
    have h0 : 0 ≤ (Kloc + 2) * Real.log x := mul_nonneg (by linarith) hL
    have h1 : 0 ≤ 1 / √x := by positivity
    nlinarith
  calc P.threshSum t x δ ≤ _ := hsplit
    _ ≤ _ := hsum
    _ ≤ 10.73 * δ * Real.log x * (Real.log (Real.log x) + 3.41) +
          2.72 * Real.log x / √x * (8.1 * δ * √x + Kloc + 2) := add_le_add hI hII
    _ ≤ _ := by nlinarith

end ThreshHyp

end BeurlingSystem

end
