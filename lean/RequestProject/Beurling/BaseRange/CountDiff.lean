module

public import RequestProject.Beurling.BaseRange.StepAbel

/-!
# Counting differences of two prime sets from their `θ`-difference

For two finite sets of "primes" `X`, `Y` (values `> a ≥ e`) with
`|θ_X(s) - θ_Y(s)| ≤ B s (log s + 1)²` on `[a, s_max]`:

* `count_diff_le` : `|#{x : v_x ≤ s} - #{y : v_y ≤ s}| ≤ B s (log s + 7)` (Abel summation with
  the weight `1/log`);
* `count_down_le` : the same for any down-closed set of values in `(a, s_max]`;
* `count_convex_le` : `≤ 2 B s_max (log s_max + 7)` for `D ∩ U`, `D` down-closed with
  `D ∩ (a, ∞) ⊆ (a, s_max]`, `U` up-closed.

These are the counting inputs of the one-replacement step with the non-smooth `g` in the proof
of Lemma 7.3(d)(iii).
-/

@[expose] public section

open Real Finset

namespace BaseRange

lemma hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s => 1 / Real.log s) (-(1 / (t * Real.log t ^ 2))) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (Real.hasDerivAt_log (by linarith : t ≠ 0)).inv hl
  simp only [one_div] at h ⊢
  convert h using 1
  field_simp

lemma continuousOn_inv_log_deriv {a s : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t => -(1 / (t * Real.log t ^ 2))) (Set.Icc a s) := by
  apply ContinuousOn.neg
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_id.mul ((Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])).pow 2)
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have : 0 < t := by linarith [ht.1]
    positivity

/-- **The counting difference at a point.** -/
theorem count_diff_le {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι) (Y : Finset κ')
    {a s B : ℝ} (ha : Real.exp 1 ≤ a) (has : a ≤ s) (hXa : ∀ x ∈ X, a < vX x)
    (hYa : ∀ y ∈ Y, a < vY y) (hB : 0 ≤ B)
    (hD : ∀ t ∈ Set.Icc a s, |thetaF vX X t - thetaF vY Y t| ≤ B * t * (Real.log t + 1) ^ 2) :
    |((X.filter (fun x => vX x ≤ s)).card : ℝ) - (Y.filter (fun y => vY y ≤ s)).card| ≤
      B * s * (Real.log s + 7) := by
  have he : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha1 : 1 < a := by linarith
  have hlog : ∀ t, a ≤ t → 1 ≤ Real.log t := fun t ht => by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hA := abel_diff vX vY X Y ha1.le has hXa hYa (fun t => 1 / Real.log t)
    (fun t => -(1 / (t * Real.log t ^ 2))) (fun t ht => hasDerivAt_inv_log (by linarith [ht.1]))
    (continuousOn_inv_log_deriv ha1)
  have hcX : ∑ z ∈ X.filter (fun z => vX z ≤ s), Real.log (vX z) * (1 / Real.log (vX z)) =
      ((X.filter (fun z => vX z ≤ s)).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun z hz => ?_
    have := hlog (vX z) (hXa z (Finset.mem_filter.mp hz).1).le
    field_simp
  have hcY : ∑ z ∈ Y.filter (fun z => vY z ≤ s), Real.log (vY z) * (1 / Real.log (vY z)) =
      ((Y.filter (fun z => vY z ≤ s)).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun z hz => ?_
    have := hlog (vY z) (hYa z (Finset.mem_filter.mp hz).1).le
    field_simp
  simp only at hA
  rw [hcX, hcY] at hA
  rw [hA]
  have hs1 := hlog s has
  have hs0 : 0 < s := by linarith
  -- the boundary term
  have h1 : |(thetaF vX X s - thetaF vY Y s) * (1 / Real.log s)| ≤ B * s * (Real.log s + 3) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.log s)]
    have hDs := hD s ⟨has, le_rfl⟩
    calc |thetaF vX X s - thetaF vY Y s| * (1 / Real.log s)
        ≤ B * s * (Real.log s + 1) ^ 2 * (1 / Real.log s) :=
          mul_le_mul_of_nonneg_right hDs (by positivity)
      _ ≤ B * s * (Real.log s + 3) := by
          rw [mul_one_div, div_le_iff₀ (by linarith)]
          have : 0 ≤ B * s := by positivity
          nlinarith
  -- the integral
  have h2 : |∫ t in a..s, (thetaF vX X t - thetaF vY Y t) * -(1 / (t * Real.log t ^ 2))| ≤
      4 * B * s := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := s) (C := 4 * B)
      (f := fun t => (thetaF vX X t - thetaF vY Y t) * -(1 / (t * Real.log t ^ 2))) (by
        intro t ht
        rw [Set.uIoc_of_le has] at ht
        have ht1 := hlog t ht.1.le
        have ht0 : 0 < t := by linarith [ht.1]
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity :
          (0 : ℝ) < 1 / (t * Real.log t ^ 2))]
        have hDt := hD t ⟨ht.1.le, ht.2⟩
        calc |thetaF vX X t - thetaF vY Y t| * (1 / (t * Real.log t ^ 2))
            ≤ B * t * (Real.log t + 1) ^ 2 * (1 / (t * Real.log t ^ 2)) :=
              mul_le_mul_of_nonneg_right hDt (by positivity)
          _ = B * ((Real.log t + 1) ^ 2 / Real.log t ^ 2) := by field_simp
          _ ≤ B * 4 := by
              apply mul_le_mul_of_nonneg_left _ hB
              rw [div_le_iff₀ (by positivity)]; nlinarith
          _ = 4 * B := by ring)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - a)] at hb
    have ha0 : 0 < a := by linarith
    calc _ ≤ 4 * B * (s - a) := hb
      _ ≤ 4 * B * s := by nlinarith
  calc |(thetaF vX X s - thetaF vY Y s) * (1 / Real.log s) -
        ∫ t in a..s, (thetaF vX X t - thetaF vY Y t) * -(1 / (t * Real.log t ^ 2))|
      ≤ |(thetaF vX X s - thetaF vY Y s) * (1 / Real.log s)| +
        |∫ t in a..s, (thetaF vX X t - thetaF vY Y t) * -(1 / (t * Real.log t ^ 2))| :=
        abs_sub _ _
    _ ≤ B * s * (Real.log s + 3) + 4 * B * s := add_le_add h1 h2
    _ = B * s * (Real.log s + 7) := by ring

/-- **The counting difference on a down-closed set.** -/
theorem count_down_le {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι) (Y : Finset κ')
    {a smax B : ℝ} (ha : Real.exp 1 ≤ a) (has : a ≤ smax) (hXa : ∀ x ∈ X, a < vX x)
    (hYa : ∀ y ∈ Y, a < vY y) (hB : 0 ≤ B)
    (hD : ∀ t ∈ Set.Icc a smax, |thetaF vX X t - thetaF vY Y t| ≤ B * t * (Real.log t + 1) ^ 2)
    (S : ℝ → Prop) [DecidablePred S] (hS : ∀ t t', t' ≤ t → S t → S t')
    (hsmax : ∀ t, a < t → S t → t ≤ smax) :
    |((X.filter (fun x => S (vX x))).card : ℝ) - (Y.filter (fun y => S (vY y))).card| ≤
      B * smax * (Real.log smax + 7) := by
  classical
  have he : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hs1 : 1 ≤ Real.log smax := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hR0 : 0 ≤ B * smax * (Real.log smax + 7) := by
    have : 0 ≤ smax := by linarith
    positivity
  set A := (X.filter (fun x => S (vX x))).image vX ∪ (Y.filter (fun y => S (vY y))).image vY
  rcases A.eq_empty_or_nonempty with hA | hA
  · have h1 : X.filter (fun x => S (vX x)) = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : vX x ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
      rw [hA] at this; simp at this
    have h2 : Y.filter (fun y => S (vY y)) = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : vY y ∈ A := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)
      rw [hA] at this; simp at this
    rw [h1, h2]; simpa using hR0
  set s := A.max' hA
  have hsA : s ∈ A := A.max'_mem hA
  have hsS : S s ∧ a < s := by
    rcases Finset.mem_union.mp hsA with h | h
    · obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp h
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      rw [← hxs]; exact ⟨hx2, hXa x hx1⟩
    · obtain ⟨y, hy, hys⟩ := Finset.mem_image.mp h
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      rw [← hys]; exact ⟨hy2, hYa y hy1⟩
  have hsm : s ≤ smax := hsmax s hsS.2 hsS.1
  have eX : X.filter (fun x => S (vX x)) = X.filter (fun x => vX x ≤ s) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, A.le_max' _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨h1, h2⟩)))⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, hS s _ h2 hsS.1⟩
  have eY : Y.filter (fun y => S (vY y)) = Y.filter (fun y => vY y ≤ s) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, A.le_max' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨h1, h2⟩)))⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, hS s _ h2 hsS.1⟩
  rw [eX, eY]
  refine (count_diff_le vX vY X Y ha hsS.2.le hXa hYa hB
    (fun t ht => hD t ⟨ht.1, ht.2.trans hsm⟩)).trans ?_
  have hs0 : 0 < s := by linarith [hsS.2]
  have hl : Real.log s ≤ Real.log smax := Real.log_le_log hs0 hsm
  have hl0 : 0 ≤ Real.log s + 7 := by
    have : 0 ≤ Real.log s := Real.log_nonneg (by linarith [hsS.2]); linarith
  calc B * s * (Real.log s + 7) ≤ B * smax * (Real.log s + 7) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsm hB) hl0
    _ ≤ B * smax * (Real.log smax + 7) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        have : 0 ≤ smax := by linarith
        positivity

/-- **The counting difference on a convex set** `D ∩ U`. -/
theorem count_convex_le {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι)
    (Y : Finset κ') {a smax B : ℝ} (ha : Real.exp 1 ≤ a) (has : a ≤ smax)
    (hXa : ∀ x ∈ X, a < vX x) (hYa : ∀ y ∈ Y, a < vY y) (hB : 0 ≤ B)
    (hD : ∀ t ∈ Set.Icc a smax, |thetaF vX X t - thetaF vY Y t| ≤ B * t * (Real.log t + 1) ^ 2)
    (Dn Up : ℝ → Prop) [DecidablePred Dn] [DecidablePred Up]
    (hDn : ∀ t t', t' ≤ t → Dn t → Dn t') (hUp : ∀ t t', t ≤ t' → Up t → Up t')
    (hsmax : ∀ t, a < t → Dn t → t ≤ smax) :
    |((X.filter (fun x => Dn (vX x) ∧ Up (vX x))).card : ℝ) -
        (Y.filter (fun y => Dn (vY y) ∧ Up (vY y))).card| ≤
      2 * (B * smax * (Real.log smax + 7)) := by
  classical
  have hsplitX : ((X.filter (fun x => Dn (vX x) ∧ Up (vX x))).card : ℝ) =
      (X.filter (fun x => Dn (vX x))).card -
        (X.filter (fun x => Dn (vX x) ∧ ¬ Up (vX x))).card := by
    have := Finset.card_filter_add_card_filter_not (s := X.filter (fun x => Dn (vX x)))
      (fun x => Up (vX x))
    rw [Finset.filter_filter, Finset.filter_filter] at this
    rw [← this]; push_cast; ring
  have hsplitY : ((Y.filter (fun y => Dn (vY y) ∧ Up (vY y))).card : ℝ) =
      (Y.filter (fun y => Dn (vY y))).card -
        (Y.filter (fun y => Dn (vY y) ∧ ¬ Up (vY y))).card := by
    have := Finset.card_filter_add_card_filter_not (s := Y.filter (fun y => Dn (vY y)))
      (fun y => Up (vY y))
    rw [Finset.filter_filter, Finset.filter_filter] at this
    rw [← this]; push_cast; ring
  have h1 := count_down_le vX vY X Y ha has hXa hYa hB hD Dn hDn hsmax
  have h2 := count_down_le vX vY X Y ha has hXa hYa hB hD (fun t => Dn t ∧ ¬ Up t)
    (fun t t' htt h => ⟨hDn t t' htt h.1, fun hu => h.2 (hUp t' t htt hu)⟩)
    (fun t ht h => hsmax t ht h.1)
  rw [hsplitX, hsplitY]
  calc _ = |(((X.filter (fun x => Dn (vX x))).card : ℝ) - (Y.filter (fun y => Dn (vY y))).card) -
        (((X.filter (fun x => Dn (vX x) ∧ ¬ Up (vX x))).card : ℝ) -
          (Y.filter (fun y => Dn (vY y) ∧ ¬ Up (vY y))).card)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

end BaseRange
