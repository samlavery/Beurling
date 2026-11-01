module

public import RequestProject.Beurling.Model.S3d

/-!
# The Euler-factor sums of (F3′) with the Mertens bound read up to a horizon

The second group of the proof of (F3′) (§5) uses the sure local Mertens bound of Lemma 5.1(iv)
for the realised primes up to the horizon of `Good(< s)` only ("That bound reads `NN` only on
`[1, s - H]` and holds on `Good(< s)`"). Here Lemma 5.1(iv) is assumed up to a height `Z`
(`MertensUpTo P Z`), and the bounds of `Model/S3dMertens.lean` and `euler_top_le` are rerun with
every height `≤ Z`:

* `sum_inv_sq_le_loc` : `∑_{y₀ < p ≤ V} 1/p² ≤ 5.8/(y₀ log y₀)` for `V ≤ Z`;
* `sum_wE_le_loc` : `∑_{y₀ < p ≤ V} w(p) ≤ log(log V/log y₀) + 2.20/log y₀ + 11.6/(y₀ log y₀)`;
* `euler_top_le_loc` : `tailSum · ∏_{k ∈ κ} (1 - 1/p_k)⁻¹ ≤ 1.8 log V · e^{2.21/Λ}` for decided
  primes `k ∈ κ` with values `≤ V ≤ Z`.
-/

@[expose] public section

open Finset Real Construction CaplLink SlotModel BModel

namespace Queue6

/-- **Lemma 5.1(iv), upper half, up to the height `Z`.** -/
def MertensUpTo (P : BeurlingSystem) (Z : ℝ) : Prop :=
  ∀ y x : ℝ, 2 ≤ y → y ≤ x → x ≤ Z →
    ∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j ≤
      Real.log (Real.log x / Real.log y) + 2.20 / Real.log y

/-- One dyadic block, cut at `Z`: `∑_{y < p ≤ min(2y, Z)} 1/p² ≤ 2.9/(y log y)`. -/
lemma block_inv_sq_le_loc {P : BeurlingSystem} {Z : ℝ} (hM : MertensUpTo P Z) {y : ℝ}
    (hy : 3 ≤ y) (hyZ : y ≤ Z) :
    ∑ j ∈ (P.primesLe (min (2 * y) Z)).filter (fun j => y < P.p j), 1 / P.p j ^ 2 ≤
      2.9 / (y * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hL : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  set x := min (2 * y) Z with hx
  have hyx : y ≤ x := le_min (by linarith) hyZ
  have hx2 : x ≤ 2 * y := min_le_left _ _
  have h1 : ∀ j ∈ (P.primesLe x).filter (fun j => y < P.p j),
      1 / P.p j ^ 2 ≤ y⁻¹ * (1 / P.p j) := by
    intro j hj
    rw [mem_filter] at hj
    have hp : 0 < P.p j := by linarith [hj.2]
    have e : y⁻¹ * (1 / P.p j) = 1 / (y * P.p j) := by field_simp
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_right hj.2.le hp.le
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h2 := hM y x (by linarith) hyx (min_le_right _ _)
  have hLy0 : 0 < Real.log y := by linarith
  have hLx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
  have hmono : Real.log (Real.log x / Real.log y) ≤ Real.log (Real.log (2 * y) / Real.log y) := by
    apply Real.log_le_log (div_pos (by linarith) hLy0)
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hx2) hLy0.le
  have hl2 : Real.log (Real.log (2 * y) / Real.log y) ≤ 0.7 / Real.log y := by
    rw [Real.log_mul (by norm_num) hy0.ne']
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (Real.log 2 + Real.log y) / Real.log y by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    have e : (Real.log 2 + Real.log y) / Real.log y - 1 = Real.log 2 / Real.log y := by
      field_simp; ring
    rw [e] at h
    have := Real.log_two_lt_d9
    have : Real.log 2 / Real.log y ≤ 0.7 / Real.log y :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  have h3 : ∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j ≤
      2.9 / Real.log y := by
    have : 2.9 / Real.log y = 0.7 / Real.log y + 2.20 / Real.log y := by ring
    linarith
  calc y⁻¹ * ∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j
      ≤ y⁻¹ * (2.9 / Real.log y) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2.9 / (y * Real.log y) := by field_simp

/-- **The second-order terms up to `Z`**: `∑_{y₀ < p ≤ V} 1/p² ≤ 5.8/(y₀ log y₀)`, `V ≤ Z`. -/
theorem sum_inv_sq_le_loc {P : BeurlingSystem} {Z : ℝ} (hM : MertensUpTo P Z) {y₀ : ℝ}
    (hy : 3 ≤ y₀) {V : ℝ} (hVZ : V ≤ Z) :
    ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2 ≤
      5.8 / (y₀ * Real.log y₀) := by
  have hy0 : 0 < y₀ := by linarith
  have hL : 0 < Real.log y₀ := Real.log_pos (by linarith)
  set c := 5.8 / (y₀ * Real.log y₀) with hc
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ K : ℕ, ∑ j ∈ (P.primesLe (min (y₀ * 2 ^ K) Z)).filter (fun j => y₀ < P.p j),
      1 / P.p j ^ 2 ≤ c * (1 - (1 / 2) ^ K) := by
    intro K
    induction K with
    | zero =>
      simp only [pow_zero, mul_one, sub_self, mul_zero]
      rw [Finset.sum_eq_zero]
      intro j hj
      rw [mem_filter, BeurlingSystem.mem_primesLe] at hj
      linarith [hj.1, hj.2, min_le_left y₀ Z]
    | succ K ih =>
      set y := y₀ * 2 ^ K with hydef
      have hyy : y₀ ≤ y := by
        rw [hydef]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := K)]
      have e2y : y₀ * 2 ^ (K + 1) = 2 * y := by rw [hydef, pow_succ]; ring
      rw [e2y, ← sum_filter_add_sum_filter_not _ (fun j => P.p j ≤ y)]
      have hA : ∑ j ∈ ((P.primesLe (min (2 * y) Z)).filter (fun j => y₀ < P.p j)).filter
          (fun j => P.p j ≤ y), 1 / P.p j ^ 2 ≤
          ∑ j ∈ (P.primesLe (min y Z)).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe] at hj ⊢
          exact ⟨le_min hj.2 ((hj.1.1).trans (min_le_right _ _)), hj.1.2⟩
        · intro j _ _; positivity
      have hB : ∑ j ∈ ((P.primesLe (min (2 * y) Z)).filter (fun j => y₀ < P.p j)).filter
          (fun j => ¬ P.p j ≤ y), 1 / P.p j ^ 2 ≤ c * (1 / 2) ^ K / 2 := by
        rcases le_or_gt y Z with hyZ | hyZ
        · have hsub : ∑ j ∈ ((P.primesLe (min (2 * y) Z)).filter (fun j => y₀ < P.p j)).filter
              (fun j => ¬ P.p j ≤ y), 1 / P.p j ^ 2 ≤
              ∑ j ∈ (P.primesLe (min (2 * y) Z)).filter (fun j => y < P.p j),
                1 / P.p j ^ 2 := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro j hj
              simp only [mem_filter, BeurlingSystem.mem_primesLe, not_le] at hj ⊢
              exact ⟨hj.1.1, hj.2⟩
            · intro j _ _; positivity
          have hb := block_inv_sq_le_loc hM (y := y) (by linarith) hyZ
          have hlog : Real.log y₀ ≤ Real.log y := Real.log_le_log hy0 hyy
          have hb2 : 2.9 / (y * Real.log y) ≤ 2.9 / (y * Real.log y₀) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_left hlog (by linarith))
          have e : 2.9 / (y * Real.log y₀) = c * (1 / 2) ^ K / 2 := by
            have h2K : (1 / 2 : ℝ) ^ K * 2 ^ K = 1 := by
              rw [← mul_pow]; norm_num
            rw [hc, hydef]; field_simp; linear_combination (-(29 / 5) : ℝ) * h2K
          linarith
        · rw [Finset.sum_eq_zero]
          · positivity
          intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe, not_le] at hj
          linarith [hj.1.1, hj.2, min_le_right (2 * y) Z]
      have hmin : min y Z = min (y₀ * 2 ^ K) Z := rfl
      have ih' := ih
      rw [← hmin] at ih'
      have e2 : c * (1 - (1 / 2) ^ (K + 1)) = c * (1 - (1 / 2) ^ K) + c * (1 / 2) ^ K / 2 := by
        ring
      linarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (V / y₀) (by norm_num : (1 : ℝ) < 2)
  have hVK : V ≤ y₀ * 2 ^ K := by
    rw [div_lt_iff₀ hy0] at hK; linarith
  calc ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), 1 / P.p j ^ 2
      ≤ ∑ j ∈ (P.primesLe (min (y₀ * 2 ^ K) Z)).filter (fun j => y₀ < P.p j),
          1 / P.p j ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [mem_filter, BeurlingSystem.mem_primesLe] at hj ⊢
          exact ⟨le_min (hj.1.trans hVK) (hj.1.trans hVZ), hj.2⟩
        · intro j _ _; positivity
    _ ≤ c * (1 - (1 / 2) ^ K) := key K
    _ ≤ c := by
        have : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
        nlinarith

/-- **The realised Euler factors above `y₀`, up to `Z`** (`sum_wE_le` with the horizon). -/
theorem sum_wE_le_loc {P : BeurlingSystem} {Z : ℝ} (hM : MertensUpTo P Z) {y₀ V : ℝ}
    (hy : 3 ≤ y₀) (hyV : y₀ ≤ V) (hVZ : V ≤ Z) :
    ∑ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j), wE (P.p j) ≤
      Real.log (Real.log V / Real.log y₀) + 2.20 / Real.log y₀ +
        11.6 / (y₀ * Real.log y₀) := by
  have h1 : ∀ j ∈ (P.primesLe V).filter (fun j => y₀ < P.p j),
      wE (P.p j) ≤ 1 / P.p j + 2 * (1 / P.p j ^ 2) := by
    intro j hj
    rw [mem_filter] at hj
    have := wE_le (v := P.p j) (by linarith [hj.2])
    simp only [one_div, inv_pow] at this ⊢
    exact this
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h2 := hM y₀ V (by linarith) hyV hVZ
  have h3 := sum_inv_sq_le_loc hM hy hVZ
  have e : 11.6 / (y₀ * Real.log y₀) = 2 * (5.8 / (y₀ * Real.log y₀)) := by ring
  linarith

section Top

variable {X₀ : ℕ} {M : SlotModel X₀} {U : ℕ → ℝ}

/-- **The sure top bound with the Mertens bound up to `Z`** ((F3′), second case, the first two
groups; Lemma A.6 (S3)(d)): for decided primes `k ∈ κ` with values `≤ V ≤ Z`,
`tailSum · exp ∑_{k ∈ κ} w(p_k) ≤ 1.8 log V · e^{2.21/Λ}`. -/
theorem euler_top_le_loc (h : RealisedOK M (capH X₀) U) (hU : ∀ j, U j ∈ Set.Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) (hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊) {Z : ℝ}
    (hM : MertensUpTo (realisedSystem M (capH X₀) U) Z) {V : ℝ}
    (hV : (X₀ : ℝ) ≤ V) (hVZ : V ≤ Z) (κ : Finset ℕ) (hκ : ∀ k ∈ κ, placedAt M k)
    (hκV : ∀ k ∈ κ, primeValueOf M (capH X₀) U k ≤ V) (Dmax : ℕ) :
    RankFull.Config.tailSum Dmax X₀ * Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) ≤
      1.8 * Real.log V * Real.exp (2.21 / Real.log X₀) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXb : 10 ^ 8 ≤ (X₀ : ℝ) := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  set y₀ : ℝ := (X₀ : ℝ) / 2 with hy₀
  have hy3 : 286 ≤ y₀ := by rw [hy₀]; linarith
  have hyV : y₀ ≤ V := by rw [hy₀]; linarith
  have hy78 : y₀ < 7 / 8 * X₀ := by rw [hy₀]; linarith
  have hLy4 : 10 ^ 4 ≤ Real.log y₀ := by
    rw [hy₀, Real.log_div (by linarith) (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  have hlow := rat_low_le X₀ (by linarith) hLy4
  have hyL : 1 / (y₀ * Real.log y₀) ≤ 1 / (2 * Real.log y₀ ^ 2) := by
    have hl0 : 0 < Real.log y₀ := by linarith
    have hly : 2 * Real.log y₀ ≤ y₀ := by
      have h := Real.log_le_sub_one_of_pos (show 0 < y₀ / 2 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h
      have := Real.log_two_lt_d9; linarith
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hly hl0.le
  have hreal := realised_sum_le h hU hX hTlow hy78 hV κ hκ hκV
  have hhigh := sum_wE_le_loc hM (by linarith : (3 : ℝ) ≤ y₀) hyV hVZ
  have hsplit := sum_filter_add_sum_filter_not X₀.primesBelow (fun p : ℕ => y₀ < (p : ℝ))
    (fun p : ℕ => wE p)
  have hT := tailSum_le_exp Dmax X₀
  have hLy : 0 < Real.log y₀ := Real.log_pos (by linarith)
  have hLV : 0 < Real.log V := Real.log_pos (by linarith)
  have hdiv : Real.log (Real.log V / Real.log y₀) =
      Real.log (Real.log V) - Real.log (Real.log y₀) := Real.log_div hLV.ne' hLy.ne'
  have hnum := top_numeric hX0 hX
  rw [← hy₀] at hnum
  have hE : ∑ p ∈ X₀.primesBelow, wE p + ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k) ≤
      Real.log 1.8 + Real.log (Real.log V) + 2.21 / Real.log X₀ := by
    linarith
  calc RankFull.Config.tailSum Dmax X₀ *
        Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k))
      ≤ Real.exp (∑ p ∈ X₀.primesBelow, wE p) *
          Real.exp (∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) :=
        mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ = Real.exp (∑ p ∈ X₀.primesBelow, wE p + ∑ k ∈ κ, wE (primeValueOf M (capH X₀) U k)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log 1.8 + Real.log (Real.log V) + 2.21 / Real.log X₀) :=
        Real.exp_le_exp.mpr hE
    _ = 1.8 * Real.log V * Real.exp (2.21 / Real.log X₀) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hLV, Real.exp_log (by norm_num)]

end Top

/-- **The rational top bound** (the case `u = X₀` of (S3)(d)): `Eu_rat = tailSum ≤
1.8 log X₀ · e^{1/(X₀ log X₀)}`. -/
theorem tailSum_le_rat {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (Dmax : ℕ) :
    RankFull.Config.tailSum Dmax X₀ ≤
      1.8 * Real.log X₀ * Real.exp (1 / (X₀ * Real.log X₀)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hlow := rat_low_le X₀ (y₀ := (X₀ : ℝ)) (by linarith) (by linarith)
  have hall : X₀.primesBelow.filter (fun p : ℕ => ¬ (X₀ : ℝ) < (p : ℝ)) = X₀.primesBelow := by
    refine Finset.filter_true_of_mem fun p hp => ?_
    have : p < X₀ := (Nat.mem_primesBelow.mp hp).1
    rw [not_lt]; exact_mod_cast this.le
  rw [hall] at hlow
  have hT := tailSum_le_exp Dmax X₀
  have hL : 0 < Real.log X₀ := by linarith
  calc RankFull.Config.tailSum Dmax X₀ ≤ Real.exp (∑ p ∈ X₀.primesBelow, wE p) := hT
    _ ≤ Real.exp (Real.log 1.8 + Real.log (Real.log X₀) + 1 / (X₀ * Real.log X₀)) :=
        Real.exp_le_exp.mpr hlow
    _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hL, Real.exp_log (by norm_num)]

end Queue6

end
