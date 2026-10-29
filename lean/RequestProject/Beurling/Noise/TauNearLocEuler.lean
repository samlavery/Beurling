module

public import RequestProject.Beurling.Noise.TauNearProofBlk
public import RequestProject.Beurling.Noise.TauNearProofEuler

/-!
# Lemma 5.20 at the cofactor horizon: the smooth harmonic sums

`TauNearProofEuler.lean` bounds `∑_{m ∈ S} 1/m` for `z`-smooth `S` through the Euler product,
using `∑_{p ≤ z} log p/p² ≤ 2.2`, which it takes from `S(z²)` (Lemma 5.1(ii) at `z²`), so it
reads `𝒩` up to `z²`. Here the same bound (`1810 log z`) is proved reading `𝒩` only up to `z`
(and `2500 ≤ Z`):

* `HBS.sum_log_div_sq_tail` : `∑_{b < p ≤ z} log p/p² ≤ 2.84/b` for `1 ≤ b`, `z ≤ Z` (dyadic
  blocks `(2ᵏb, 2ᵏ⁺¹b]` and Lemma 5.1(i), `ψ(m) - ψ(m/2) ≤ 0.71 m`);
* `HBS.sum_log_div_sq_loc` : `∑_{p ≤ z} log p/p² ≤ 2.2568` for `1 ≤ z ≤ Z`, `2500 ≤ Z` (the head
  `p ≤ √Z` by `S(Z)`, the tail by the dyadic bound);
* `smooth_harm_le_loc`, `smooth_mult_le_loc`, `smooth_logharm_le_loc` : the bounds of
  `TauNearProofEuler.lean` with `z ≤ Z` in place of `z² ≤ Z`;
* `U_horizon_loc`, `U_harm_loc`, `U_logharm_loc` : the block sums of `TauNearProofBlk.lean` with
  the horizon `18 v ≤ Z²` (i.e. `3√(2v) ≤ Z`, the largest prime read) in place of `18 v ≤ Z`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} {ε θ : ℝ}

/-- `∑_{b < p ≤ z} log p/p² ≤ 2.84/b` (dyadic blocks and Lemma 5.1(i)); reads `𝒩` up to `z`. -/
theorem sum_log_div_sq_tail (h : P.HBS X0m Z η1 η2 ε1) {z b : ℝ} (hb : 1 ≤ b) (hzZ : z ≤ Z) :
    ∑ j ∈ (P.primesLe z).filter (fun j => b < P.p j), Real.log (P.p j) / P.p j ^ 2 ≤
      2.84 / b := by
  classical
  have hb0 : 0 < b := by linarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (z / b) (by norm_num : (1 : ℝ) < 2)
  set I := (P.primesLe z).filter (fun j => b < P.p j)
  -- the block index
  have hblk : ∀ j ∈ I, ∃ k ∈ range K, 2 ^ k * b < P.p j ∧ P.p j ≤ 2 ^ (k + 1) * b := by
    intro j hj
    obtain ⟨hjz, hjb⟩ := Finset.mem_filter.mp hj
    rw [mem_primesLe] at hjz
    have hex : ∃ n : ℕ, P.p j ≤ 2 ^ n * b := ⟨K, by
      rw [div_lt_iff₀ hb0] at hK; linarith⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, ¬ P.p j ≤ 2 ^ m * b := fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = n at hspec hmin
    cases n with
    | zero => simp at hspec; linarith
    | succ k =>
    have hlt : ¬ P.p j ≤ 2 ^ k * b := hmin k (by omega)
    refine ⟨k, ?_, not_le.mp hlt, hspec⟩
    rw [Finset.mem_range]
    by_contra hkK; push_neg at hkK
    have h1 : (2 : ℝ) ^ K ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hkK
    rw [div_lt_iff₀ hb0] at hK
    have : z < 2 ^ k * b := by nlinarith
    exact hlt (by linarith)
  -- the blocks
  set blkS : ℕ → Finset ℕ := fun k =>
    I.filter (fun j => 2 ^ k * b < P.p j ∧ P.p j ≤ 2 ^ (k + 1) * b)
  have hcover : I ⊆ (range K).biUnion blkS := by
    intro j hj
    obtain ⟨k, hk, h1, h2⟩ := hblk j hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, h1, h2⟩⟩
  have hnn : ∀ j, 0 ≤ Real.log (P.p j) / P.p j ^ 2 := fun j =>
    div_nonneg (P.log_p_nonneg j) (pow_pos (P.p_pos j) 2).le
  have hblock : ∀ k, ∑ j ∈ blkS k, Real.log (P.p j) / P.p j ^ 2 ≤ 1.42 / (2 ^ k * b) := by
    intro k
    have hA : 0 < 2 ^ k * b := by positivity
    -- each term `≤ log p/(2ᵏb)²`
    have h1 : ∑ j ∈ blkS k, Real.log (P.p j) / P.p j ^ 2 ≤
        (∑ j ∈ blkS k, Real.log (P.p j)) / (2 ^ k * b) ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk := (Finset.mem_filter.mp hj).2
      apply div_le_div_of_nonneg_left (P.log_p_nonneg j) (by positivity)
      exact pow_le_pow_left₀ hA.le hjk.1.le 2
    -- the block sum of `log p` by `ψ`
    rcases (blkS k).eq_empty_or_nonempty with he | ⟨j0, hj0⟩
    · rw [he, Finset.sum_empty]; positivity
    set m := min (2 ^ (k + 1) * b) z
    have hj0' := Finset.mem_filter.mp hj0
    have hj0z : P.p j0 ≤ z := by
      have := (Finset.mem_filter.mp hj0'.1).1; rwa [mem_primesLe] at this
    have hm1 : 1 ≤ m := by
      have := hj0'.2.1
      have h2k : (1 : ℝ) ≤ 2 ^ k * b := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      exact le_min (by rw [pow_succ]; nlinarith) (by linarith)
    have hmZ : m ≤ Z := (min_le_right _ _).trans hzZ
    have hsum : ∑ j ∈ blkS k, Real.log (P.p j) ≤ P.psi m - P.psi (2 ^ k * b) := by
      have hsub := HBS.sum_le_psi_sub (P := P) (a := 2 ^ k * b) (b := m)
        (by
          have : 2 ^ k * b < P.p j0 := hj0'.2.1
          exact this.le.trans (le_min hj0'.2.2 hj0z))
        ((blkS k).image (fun j => (j, 0)))
        (by
          intro jk hjk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
          have hj' := Finset.mem_filter.mp hj
          have hjz : P.p j ≤ z := by
            have := (Finset.mem_filter.mp hj'.1).1; rwa [mem_primesLe] at this
          simp only [zero_add, pow_one]
          exact ⟨hj'.2.1, le_min hj'.2.2 hjz⟩)
      rwa [Finset.sum_image (fun a _ b _ hab => by simpa using hab)] at hsub
    have hpsi := (P.lemma_5_1 h hm1 hmZ).1.1
    have hmono : P.psi (m / 2) ≤ P.psi (2 ^ k * b) := P.psi_mono (by
      have : m ≤ 2 ^ (k + 1) * b := min_le_left _ _
      rw [pow_succ] at this; linarith)
    have hmle : m ≤ 2 * (2 ^ k * b) := by
      have : m ≤ 2 ^ (k + 1) * b := min_le_left _ _
      rw [pow_succ] at this; linarith
    have hS : ∑ j ∈ blkS k, Real.log (P.p j) ≤ 1.42 * (2 ^ k * b) := by linarith
    calc ∑ j ∈ blkS k, Real.log (P.p j) / P.p j ^ 2
        ≤ (∑ j ∈ blkS k, Real.log (P.p j)) / (2 ^ k * b) ^ 2 := h1
      _ ≤ 1.42 * (2 ^ k * b) / (2 ^ k * b) ^ 2 :=
          div_le_div_of_nonneg_right hS (by positivity)
      _ = 1.42 / (2 ^ k * b) := by field_simp
  calc ∑ j ∈ I, Real.log (P.p j) / P.p j ^ 2
      ≤ ∑ j ∈ (range K).biUnion blkS, Real.log (P.p j) / P.p j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun j _ _ => hnn j
    _ = ∑ k ∈ range K, ∑ j ∈ blkS k, Real.log (P.p j) / P.p j ^ 2 := by
        apply Finset.sum_biUnion
        intro k1 _ k2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro j hj1 hj2
        have a1 := (Finset.mem_filter.mp hj1).2
        have a2 := (Finset.mem_filter.mp hj2).2
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have : (2 : ℝ) ^ (k1 + 1) ≤ 2 ^ k2 := pow_le_pow_right₀ (by norm_num) hlt
          nlinarith
        · have : (2 : ℝ) ^ (k2 + 1) ≤ 2 ^ k1 := pow_le_pow_right₀ (by norm_num) hlt
          nlinarith
    _ ≤ ∑ k ∈ range K, 1.42 / (2 ^ k * b) := Finset.sum_le_sum fun k _ => hblock k
    _ ≤ 2.84 / b := by
        have hgeo : ∀ n : ℕ, ∑ k ∈ range n, (1 / 2 : ℝ) ^ k ≤ 2 := by
          intro n
          have := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num) n
          rw [this]
          have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
          rw [div_le_iff_of_neg (by norm_num)]; nlinarith
        have e : ∑ k ∈ range K, 1.42 / (2 ^ k * b) =
            1.42 / b * ∑ k ∈ range K, (1 / 2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [one_div_pow]; field_simp
        rw [e]
        have := hgeo K
        have hb1 : 0 ≤ 1.42 / b := by positivity
        calc 1.42 / b * ∑ k ∈ range K, (1 / 2 : ℝ) ^ k ≤ 1.42 / b * 2 :=
              mul_le_mul_of_nonneg_left this hb1
          _ = 2.84 / b := by ring

/-- `∑_{p ≤ z} log p/p² ≤ 2.2568` for `1 ≤ z ≤ Z`, `2500 ≤ Z`; reads `𝒩` up to `z` only. -/
theorem sum_log_div_sq_loc (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 1 ≤ z) (hzZ : z ≤ Z)
    (hZ : 2500 ≤ Z) : ∑ j ∈ P.primesLe z, Real.log (P.p j) / P.p j ^ 2 ≤ 2.2568 := by
  classical
  rcases le_or_gt (z ^ 2) Z with hz2 | hz2
  · have := h.sum_log_div_sq_le_lemS hz hz2; linarith
  set b := √Z
  have hb50 : 50 ≤ b := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hbsq : b ^ 2 = Z := Real.sq_sqrt (by linarith)
  have hnn : ∀ j, 0 ≤ Real.log (P.p j) / P.p j ^ 2 := fun j =>
    div_nonneg (P.log_p_nonneg j) (pow_pos (P.p_pos j) 2).le
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe z) (fun j => b < P.p j)]
  have htail := sum_log_div_sq_tail h (by linarith : (1 : ℝ) ≤ b) hzZ
  have hhead : ∑ j ∈ (P.primesLe z).filter (fun j => ¬ b < P.p j),
      Real.log (P.p j) / P.p j ^ 2 ≤ 2.2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := P.primesLe b) ?_
      (fun j _ _ => hnn j)).trans (h.sum_log_div_sq_le_lemS (by linarith) (by rw [hbsq]))
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [mem_primesLe]; exact not_lt.mp hj.2
  have : 2.84 / b ≤ 0.0568 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- **The Euler-product bound at the cofactor horizon**: `∑_{m ∈ S} 1/m ≤ 1810 log z` for
`z`-smooth `S`, with `z ≤ Z` (in place of `z² ≤ Z`) and `2500 ≤ Z`. -/
theorem smooth_harm_le_loc (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ' : z ≤ Z)
    (hZ : 2500 ≤ Z) (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) :
    ∑ e ∈ S, 1 / P.val e ≤ 1810 * Real.log z := by
  set J := P.primesLe z
  have hsupp : ∀ e ∈ S, e.support ⊆ J := fun e he i hi => by
    rw [mem_primesLe]; exact hS e he i hi
  have hE := P.sum_rpow_le_euler one_pos J S hsupp
  have hp2 : ∀ j ∈ J, 2 ≤ P.p j := fun j hj => h.p_ge_two ((P.mem_primesLe.mp hj).trans hzZ')
  have hx : ∀ j ∈ J, 0 ≤ P.p j ^ (-(1 : ℝ)) ∧ P.p j ^ (-(1 : ℝ)) < 1 := fun j hj => by
    rw [Real.rpow_neg_one]
    have := hp2 j hj
    exact ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith)⟩
  have hprod := LemS.prod_inv_le_exp J (fun j => P.p j ^ (-(1 : ℝ))) hx
  have hS1 : ∑ e ∈ S, 1 / P.val e = ∑ e ∈ S, P.val e ^ (-(1 : ℝ)) :=
    Finset.sum_congr rfl fun e _ => by rw [Real.rpow_neg_one, one_div]
  have hsum1 := h.sum_inv_p_le hz hzZ'
  have hsum2 := sum_log_div_sq_loc h (by linarith) hzZ' hZ
  have hterm : ∀ j ∈ J, P.p j ^ (-(1 : ℝ)) + (P.p j ^ (-(1 : ℝ))) ^ 2 /
      (2 * (1 - P.p j ^ (-(1 : ℝ)))) ≤ 1 / P.p j + Real.log (P.p j) / P.p j ^ 2 / 0.6931 := by
    intro j hj
    have hp := hp2 j hj
    rw [Real.rpow_neg_one]
    have hx0 : 0 < (P.p j)⁻¹ := by positivity
    have hx1 : (P.p j)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hl2 : 0.6931 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlp : Real.log 2 ≤ Real.log (P.p j) := Real.log_le_log (by norm_num) hp
    have h1 : (P.p j)⁻¹ ^ 2 / (2 * (1 - (P.p j)⁻¹)) ≤ (P.p j)⁻¹ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (P.p j)⁻¹]
    have h2 : (P.p j)⁻¹ ^ 2 ≤ Real.log (P.p j) / P.p j ^ 2 / 0.6931 := by
      rw [inv_pow, div_div, le_div_iff₀ (by positivity)]
      have : 0 < P.p j ^ 2 := by positivity
      field_simp
      linarith
    rw [one_div]; linarith
  have hexp : ∑ j ∈ J, (P.p j ^ (-(1 : ℝ)) + (P.p j ^ (-(1 : ℝ))) ^ 2 /
      (2 * (1 - P.p j ^ (-(1 : ℝ))))) ≤ Real.log (Real.log z) + 7.4 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    have : (∑ j ∈ J, Real.log (P.p j) / P.p j ^ 2) / 0.6931 ≤ 2.2568 / 0.6931 :=
      div_le_div_of_nonneg_right hsum2 (by norm_num)
    have : (2.2568 : ℝ) / 0.6931 ≤ 3.27 := by norm_num
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  calc ∑ e ∈ S, 1 / P.val e ≤ Real.exp (Real.log (Real.log z) + 7.4) := by
        rw [hS1]; exact hE.trans (hprod.trans (Real.exp_le_exp.mpr hexp))
    _ = Real.exp 7.4 * Real.log z := by rw [Real.exp_add, Real.exp_log hlz]; ring
    _ ≤ 1810 * Real.log z := by
        have : Real.exp 7.4 ≤ Real.exp 7.5 := Real.exp_le_exp.mpr (by norm_num)
        nlinarith [exp_75_le]

/-- `∑_{e ∈ S} e_j/e ≤ (2/p_j)·1810 log z` for a finite set of `z`-smooth elements
(cofactor horizon `z ≤ Z`). -/
theorem smooth_mult_le_loc (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ' : z ≤ Z)
    (hZ : 2500 ≤ Z)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) (j : ℕ) (hj : P.p j ≤ z) :
    ∑ e ∈ S, (e j : ℝ) / P.val e ≤ 2 / P.p j * (1810 * Real.log z) := by
  classical
  have hp2 : 2 ≤ P.p j := h.p_ge_two (hj.trans hzZ')
  set N := S.sup (fun e => e j)
  -- `e_j/e = ∑_{k < e_j} 1/e`
  have h1 : ∑ e ∈ S, (e j : ℝ) / P.val e =
      ∑ k ∈ range N, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e := by
    symm
    rw [Finset.sum_comm' (t' := S) (s' := fun e => (range N).filter (fun k => k + 1 ≤ e j))]
    · refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (range N).filter (fun k => k + 1 ≤ e j) = range (e j) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨-, h⟩; omega
        · intro hk
          exact ⟨lt_of_lt_of_le hk (Finset.le_sup (f := fun e => e j) he), by omega⟩
      rw [this, Finset.card_range]; ring
    · intro k e
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
  -- each layer
  have h2 : ∀ k, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e ≤
      (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) := by
    intro k
    set S' := S.filter (fun e => k + 1 ≤ e j)
    have hinj : Set.InjOn (fun e => e - Finsupp.single j (k + 1)) S' := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hla : Finsupp.single j (k + 1) ≤ a := Finsupp.single_le_iff.mpr ha'
      have hlb : Finsupp.single j (k + 1) ≤ b := Finsupp.single_le_iff.mpr hb'
      have := congrArg (· + Finsupp.single j (k + 1)) hab
      simp only [tsub_add_cancel_of_le hla, tsub_add_cancel_of_le hlb] at this
      exact this
    have hsm : ∀ e ∈ S'.image (fun e => e - Finsupp.single j (k + 1)),
        ∀ i ∈ e.support, P.p i ≤ z := by
      intro e he i hi
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
      apply hS e0 (Finset.mem_filter.mp he0).1 i
      rw [Finsupp.mem_support_iff] at hi ⊢
      intro h0; apply hi; simp [Finsupp.tsub_apply, h0]
    have hb := smooth_harm_le_loc h hz hzZ' hZ _ hsm
    rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)] at hb
    calc ∑ e ∈ S', 1 / P.val e =
          ∑ e ∈ S', (P.p j)⁻¹ ^ (k + 1) * (1 / P.val (e - Finsupp.single j (k + 1))) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [P.val_sub_single (Finset.mem_filter.mp he).2, one_div, one_div, mul_inv, inv_pow]
          ring
      _ ≤ (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hb (by have := P.p_pos j; positivity)
  rw [h1]
  calc ∑ k ∈ range N, ∑ e ∈ S.filter (fun e => k + 1 ≤ e j), 1 / P.val e
      ≤ ∑ k ∈ range N, (P.p j)⁻¹ ^ (k + 1) * (1810 * Real.log z) :=
        Finset.sum_le_sum fun k _ => h2 k
    _ = (∑ k ∈ range N, (P.p j)⁻¹ ^ (k + 1)) * (1810 * Real.log z) := by rw [Finset.sum_mul]
    _ ≤ 2 / P.p j * (1810 * Real.log z) := by
        have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        -- geometric sum `∑_{k<N} x^{k+1} ≤ x/(1-x) ≤ 2x`
        set x := (P.p j)⁻¹
        have hx0 : 0 ≤ x := by positivity
        have hx1 : x ≤ 1 / 2 := by
          simp only [x]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have hcl : ∀ n : ℕ, (∑ k ∈ range n, x ^ (k + 1)) * (1 - x) = x - x ^ (n + 1) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
        have hgeo : ∀ n : ℕ, ∑ k ∈ range n, x ^ (k + 1) ≤ 2 * x := by
          intro n
          have h := hcl n
          have hpos : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
          have hS0 : 0 ≤ ∑ k ∈ range n, x ^ (k + 1) :=
            Finset.sum_nonneg fun k _ => pow_nonneg hx0 _
          nlinarith
        calc ∑ k ∈ range N, x ^ (k + 1) ≤ 2 * x := hgeo N
          _ = 2 / P.p j := by simp only [x]; rw [div_eq_mul_inv]

/-- `∑_{m ∈ S} log m/m ≤ 3620 log z (log z + 0.43)` for a finite set of `z`-smooth elements
(cofactor horizon `z ≤ Z`). -/
theorem smooth_logharm_le_loc (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 2 ≤ z) (hzZ' : z ≤ Z)
    (hZ : 2500 ≤ Z)
    (S : Finset (ℕ →₀ ℕ)) (hS : ∀ e ∈ S, ∀ i ∈ e.support, P.p i ≤ z) :
    ∑ e ∈ S, Real.log (P.val e) / P.val e ≤
      3620 * Real.log z * (Real.log z + 0.43) := by
  classical
  set J := P.primesLe z
  have hlog : ∀ e ∈ S, Real.log (P.val e) = ∑ j ∈ J, (e j : ℝ) * Real.log (P.p j) := by
    intro e he
    rw [P.log_val]
    apply Finsupp.sum_of_support_subset
    · intro i hi; rw [P.mem_primesLe]; exact hS e he i hi
    · intro i _; simp
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  calc ∑ e ∈ S, Real.log (P.val e) / P.val e
      = ∑ j ∈ J, Real.log (P.p j) * ∑ e ∈ S, (e j : ℝ) / P.val e := by
        rw [Finset.sum_congr rfl fun e he => by rw [hlog e he, Finset.sum_div]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ j ∈ J, Real.log (P.p j) * (2 / P.p j * (1810 * Real.log z)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_left
          (smooth_mult_le_loc h hz hzZ' hZ S hS j (P.mem_primesLe.mp hj)) (P.log_p_nonneg j)
    _ = 3620 * Real.log z * P.Sp z := by
        unfold BeurlingSystem.Sp
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 3620 * Real.log z * (Real.log z + 0.43) := by
        have := (P.lemma_5_1 h (by linarith) hzZ').2.2.1.2
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

lemma U_horizon_loc (hX : 0 < X0m) {Sc : Finset ℝ} (hZ0 : 2500 ≤ Z)
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (k : ℕ)
    (hne : (Sc.biUnion (SmB P X0m k)).Nonempty) : 3 * Pk X0m k ≤ Z := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv, hev⟩ := Finset.mem_biUnion.mp he
  simp only [SmB, Finset.mem_filter, mem_elems] at hev
  have hk := Pk_pos hX k
  have h1 := (P.one_le_val e).trans hev.1
  rw [le_div_iff₀ (by positivity)] at h1
  have := hZ v hv
  have hsq : (3 * Pk X0m k) ^ 2 ≤ Z ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).mp hsq

/-- `∑_{m ∈ U_k} 1/m ≤ 1810 log(3P_k)`. -/
theorem U_harm_loc (h : P.HBS X0m Z η1 η2 ε1) (hP : PaperWidth H X0m ε θ) {Sc : Finset ℝ}
    (hZ0 : 2500 ≤ Z) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (k : ℕ) (hk1 : 1 ≤ Pk X0m k) :
    ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e ≤ 1810 * Real.log (3 * Pk X0m k) := by
  have hX := hP.X0m_pos
  rcases (Sc.biUnion (SmB P X0m k)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
  · exact smooth_harm_le_loc h (by linarith) (U_horizon_loc hX hZ0 hZ k hne) hZ0 _
      (U_smooth hX k)

/-- `∑_{m ∈ U_k} log m/m ≤ 3620 log(3P_k)(log(3P_k) + 0.43)`. -/
theorem U_logharm_loc (h : P.HBS X0m Z η1 η2 ε1) (hP : PaperWidth H X0m ε θ) {Sc : Finset ℝ}
    (hZ0 : 2500 ≤ Z) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z ^ 2) (k : ℕ) (hk1 : 1 ≤ Pk X0m k) :
    ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) / P.val e ≤
      3620 * Real.log (3 * Pk X0m k) * (Real.log (3 * Pk X0m k) + 0.43) := by
  have hX := hP.X0m_pos
  rcases (Sc.biUnion (SmB P X0m k)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
  · exact smooth_logharm_le_loc h (by linarith) (U_horizon_loc hX hZ0 hZ k hne) hZ0 _
      (U_smooth hX k)

end KR.TNP

end
