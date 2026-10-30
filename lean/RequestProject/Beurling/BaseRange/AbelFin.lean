module

public import RequestProject.Beurling.Noise.KRNormHarm

/-!
# Abel summation over finitely many real points, and the realised cofactor sums of Lemma 7.3(c)

* `abel_fin` : for points `t_i ∈ (a, b]` with weights `c_i` and a `C¹` function `g` on `[a, b]`,
  `∑ c_i g(t_i) = C(b) g(b) - ∫_a^b C(s) g'(s) ds`, `C(s) = ∑_{t_i ≤ s} c_i`;
* `HBS.harm_ge` : the lower harmonic bound under (HBS),
  `∑_{n ∈ 𝒩, n ≤ X} 1/n ≥ log X - η₁(1 + log 2)` (with `HBS.harm_le`, `B₁ = 1`, this is the
  two-sided bound `|e(t)| ≤ 1.002` used in the proof of Lemma 7.3(c));
* `HBS.cofactor_sum_le` : for `1 ≤ b ≤ Z` and `x > b`,
  `∑_{n ∈ 𝒩, 1 < n ≤ b} 1/(n log(x/n)) ≤ log(log x/log(x/b)) + 1.01/log(x/b)`
  (the first bullet of the proof of Lemma 7.3(c), for the realised system).
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral Set

namespace BaseRange

/-- **Abel summation over finitely many points.** -/
theorem abel_fin {ι : Type*} (I : Finset ι) (t c : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (ht : ∀ i ∈ I, a < t i ∧ t i ≤ b) (g g' : ℝ → ℝ)
    (hg : ∀ s ∈ Icc a b, HasDerivAt g (g' s) s) (hgc : ContinuousOn g' (Icc a b)) :
    ∑ i ∈ I, c i * g (t i) =
      (∑ i ∈ I, c i) * g b - ∫ s in a..b, (∑ i ∈ I, if t i ≤ s then c i else 0) * g' s := by
  classical
  have hint : IntegrableOn g' (Icc a b) := hgc.integrableOn_Icc
  -- for each point, `g(t_i) = g(b) - ∫_a^b 1[t_i ≤ s] g'(s) ds`
  have hpt : ∀ i ∈ I, g (t i) = g b - ∫ s in a..b, (if t i ≤ s then g' s else 0) := by
    intro i hi
    obtain ⟨h1, h2⟩ := ht i hi
    have hftc : ∫ s in t i..b, g' s = g b - g (t i) := by
      apply integral_eq_sub_of_hasDerivAt
      · intro s hs
        rw [Set.uIcc_of_le h2] at hs
        exact hg s ⟨by linarith [hs.1], hs.2⟩
      · exact (hgc.mono (by
          intro s hs; rw [Set.uIcc_of_le h2] at hs
          exact ⟨by linarith [hs.1], hs.2⟩)).intervalIntegrable
    have hind : ∫ s in a..b, (if t i ≤ s then g' s else 0) = ∫ s in t i..b, g' s := by
      rw [integral_of_le hab, integral_of_le h2]
      have e : (fun s => if t i ≤ s then g' s else 0) = (Ici (t i)).indicator g' := by
        funext s; simp [Set.indicator, Set.mem_Ici]
      rw [e, setIntegral_indicator measurableSet_Ici]
      have hset : Ioc a b ∩ Ici (t i) = Icc (t i) b := by
        ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
        · rintro ⟨h', h⟩; exact ⟨⟨by linarith, h⟩, h'⟩
      rw [hset, integral_Icc_eq_integral_Ioc]
    rw [hind]; linarith
  rw [Finset.sum_congr rfl fun i hi => by rw [hpt i hi], Finset.sum_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  have hsw : ∀ i ∈ I, c i * ∫ s in a..b, (if t i ≤ s then g' s else 0) =
      ∫ s in a..b, c i * (if t i ≤ s then g' s else 0) :=
    fun i _ => (intervalIntegral.integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl hsw, ← intervalIntegral.integral_finset_sum]
  · refine integral_congr fun s _ => ?_
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  · intro i _
    have : IntervalIntegrable (fun s => if t i ≤ s then g' s else 0) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      have e : (fun s => if t i ≤ s then g' s else 0) = (Ici (t i)).indicator g' := by
        funext s; simp [Set.indicator, Set.mem_Ici]
      rw [e]
      exact (hint.mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici
    exact this.const_mul (c i)

end BaseRange

namespace BeurlingSystem

namespace HBS

variable {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- On a block, `-E₁(t)/t² ≤ M_k/t`. -/
lemma negE_div_sq_le (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hXZ : X ≤ Z) {k : ℕ} {t : ℝ}
    (ht1 : X / 2 ^ (k + 1) ≤ t) (ht2 : t ≤ X / 2 ^ k) (ht0 : 0 < t) :
    ((⌊t⌋₊ : ℝ) - P.N t) / t ^ 2 ≤ bsup P X X0m k / t := by
  have htX : t ≤ X := by
    have hX0 : 0 ≤ X := by
      by_contra hc; push_neg at hc
      have : X / 2 ^ k < 0 := div_neg_of_neg_of_pos hc (by positivity)
      linarith
    exact ht2.trans (div_le_self hX0 (one_le_pow₀ (by norm_num)))
  rcases lt_or_ge t X0m with hlt | hge
  · have := h.E_zero ht0.le hlt (htX.trans hXZ)
    rw [show (⌊t⌋₊ : ℝ) - P.N t = -(P.N t - ⌊t⌋₊) by ring, this, neg_zero, zero_div]
    exact div_nonneg (h.bsup_nonneg hXZ k) ht0.le
  · have hb := h.le_bsup hXZ (k := k) (t := t) ⟨ht1, ht2, hge⟩
    unfold phiE at hb
    rw [div_le_iff₀ ht0] at hb
    rw [div_le_div_iff₀ (by positivity) ht0]
    have := neg_abs_le (P.N t - (⌊t⌋₊ : ℝ))
    nlinarith

/-- **The integral term, lower bound**: `∫_{1/2}^X E₁(t) dt/t² ≥ -η₁ log 2`. -/
lemma integral_E_ge (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) :
    -(η1 * Real.log 2) ≤ ∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, X / 2 ^ K ≤ 1 / 2 := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * X) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, ?_⟩
    rw [div_le_iff₀ (by positivity)]; linarith
  set F : ℝ → ℝ := fun t => ((⌊t⌋₊ : ℝ) - P.N t) / t ^ 2 with hF
  have hFi : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable F volume a b := by
    intro a b ha hab
    have := (intervalIntegrable_E_div_sq P ha hab).neg
    refine this.congr (fun t _ => ?_)
    simp only [hF, Pi.neg_apply]; ring
  set a : ℕ → ℝ := fun k => X / 2 ^ (K - k)
  have hX0 : 0 < X := by linarith
  have ha0 : ∀ k, 0 < a k := fun k => by simp only [a]; positivity
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    simp only [a]
    apply div_le_div_of_nonneg_left hX0.le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hint : ∀ k < K, IntervalIntegrable F volume (a k) (a (k + 1)) :=
    fun k _ => hFi _ _ (ha0 k) (hmono k)
  have haK : a K = X := by simp [a]
  have ha0' : a 0 = X / 2 ^ K := by simp [a]
  have hlow : ∫ t in a 0..(1 / 2 : ℝ), F t = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le (by rw [ha0']; exact hK)] at ht
      simp only [hF]
      have ht0 : 0 < t := lt_of_lt_of_le (ha0 0) ht.1
      have htX : t < X0m := by
        have := h.X0m_ge; norm_num at this; linarith [ht.2]
      have := h.E_zero ht0.le htX (by linarith [ht.2])
      rw [show (⌊t⌋₊ : ℝ) - P.N t = -(P.N t - ⌊t⌋₊) by ring, this, neg_zero, zero_div]
  have hsplit : ∫ t in (1 / 2 : ℝ)..X, F t = ∑ k ∈ range K, ∫ t in a k..a (k + 1), F t := by
    rw [sum_integral_adjacent_intervals hint, haK]
    rw [← integral_add_adjacent_intervals (b := (1 / 2 : ℝ))
      (hFi _ _ (ha0 0) (by rw [ha0']; exact hK)) (hFi _ _ (by norm_num) (by linarith)), hlow,
      zero_add]
  have hblock : ∀ k ∈ range K, ∫ t in a k..a (k + 1), F t ≤
      bsup P X X0m (K - 1 - k) * Real.log 2 := by
    intro k hk
    have hkK := mem_range.mp hk
    have e1 : a (k + 1) = X / 2 ^ (K - 1 - k) := by
      simp only [a]; congr 2; omega
    have e2 : a k = X / 2 ^ (K - 1 - k + 1) := by
      simp only [a]; congr 2; omega
    calc ∫ t in a k..a (k + 1), F t
        ≤ ∫ t in a k..a (k + 1), bsup P X X0m (K - 1 - k) / t := by
          apply integral_mono_on (hmono k) (hint k hkK)
          · apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.div continuousOn_const continuousOn_id
            intro t ht
            rw [Set.uIcc_of_le (hmono k)] at ht
            exact (lt_of_lt_of_le (ha0 k) ht.1).ne'
          · intro t ht
            have ht0 : 0 < t := lt_of_lt_of_le (ha0 k) ht.1
            exact h.negE_div_sq_le hXZ (by rw [← e2]; exact ht.1) (by rw [← e1]; exact ht.2) ht0
      _ = bsup P X X0m (K - 1 - k) * Real.log 2 := by
          rw [show (fun t : ℝ => bsup P X X0m (K - 1 - k) / t) =
              fun t => bsup P X X0m (K - 1 - k) * t⁻¹ by funext t; ring,
            intervalIntegral.integral_const_mul, integral_inv_of_pos (ha0 k) (ha0 (k + 1))]
          congr 2
          rw [e1, e2, pow_succ]
          field_simp
  have hF' : ∫ t in (1 / 2 : ℝ)..X, F t ≤ η1 * Real.log 2 := by
    rw [hsplit]
    calc ∑ k ∈ range K, ∫ t in a k..a (k + 1), F t
        ≤ ∑ k ∈ range K, bsup P X X0m (K - 1 - k) * Real.log 2 := Finset.sum_le_sum hblock
      _ = (∑ k ∈ range K, bsup P X X0m k) * Real.log 2 := by
          rw [← Finset.sum_mul]
          congr 1
          exact Finset.sum_range_reflect (bsup P X X0m) K
      _ ≤ η1 * Real.log 2 :=
          mul_le_mul_of_nonneg_right (h.sum_blockSup_le hXZ K) (Real.log_nonneg (by norm_num))
  have hneg : ∫ t in (1 / 2 : ℝ)..X, F t =
      -∫ t in (1 / 2 : ℝ)..X, (P.N t - (⌊t⌋₊ : ℝ)) / t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t; simp only [hF]; ring
  linarith

/-- **The lower harmonic bound** under (HBS): `∑_{n ∈ 𝒩, n ≤ X} 1/n ≥ log X - η₁(1 + log 2)`
for `1 ≤ X ≤ Z`. -/
theorem harm_ge (h : P.HBS X0m Z η1 η2 ε1) {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z) :
    Real.log X - η1 * (1 + Real.log 2) ≤ ∑ e ∈ P.elems X, 1 / P.val e := by
  have hd := harm_sub_natHarm P hX
  have h1 : Real.log X ≤ ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n := by
    rw [sum_Icc_inv_eq_harmonic]
    refine le_trans ?_ (log_add_one_le_harmonic _)
    apply Real.log_le_log (by linarith)
    push_cast; linarith [Nat.lt_floor_add_one X]
  have h2 : -η1 ≤ (P.N X - ⌊X⌋₊) / X := by
    rw [le_div_iff₀ (by linarith)]
    have := h.abs_E_le (by linarith) hXZ
    linarith [neg_abs_le (P.N X - (⌊X⌋₊ : ℝ))]
  have h3 := h.integral_E_ge hX hXZ
  linarith

/-- The sum of `1/val` over the elements of value at most `s`, other than `1`. -/
noncomputable def harm1 (P : BeurlingSystem) (s : ℝ) : ℝ :=
  ∑ e ∈ (P.elems s).filter (· ≠ 0), 1 / P.val e

lemma val_zero (P : BeurlingSystem) : P.val 0 = 1 := by simp [BeurlingSystem.val]

lemma one_lt_val {P : BeurlingSystem} {e : ℕ →₀ ℕ} (he : e ≠ 0) : 1 < P.val e := by
  unfold BeurlingSystem.val Finsupp.prod
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp he
  have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr (by simpa using hj)
  rw [← Finset.mul_prod_erase _ _ hjs]
  have h1 : 1 < P.p j ^ e j := one_lt_pow₀ (P.one_lt j) (by simpa using hj)
  have h2 : 1 ≤ ∏ x ∈ e.support.erase j, P.p x ^ e x :=
    calc (1 : ℝ) = ∏ x ∈ e.support.erase j, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun i _ => one_le_pow₀ (P.one_lt i).le)
  nlinarith

lemma harm1_eq (P : BeurlingSystem) {s : ℝ} (hs : 1 ≤ s) :
    harm1 P s = ∑ e ∈ P.elems s, 1 / P.val e - 1 := by
  unfold harm1
  have h0 : (0 : ℕ →₀ ℕ) ∈ P.elems s := by rw [P.mem_elems, val_zero]; exact hs
  rw [← Finset.sum_filter_add_sum_filter_not (P.elems s) (· ≠ 0)]
  have : (P.elems s).filter (fun e => ¬ e ≠ 0) = {0} := by
    ext e; simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro rfl; exact ⟨h0, rfl⟩
  rw [this, Finset.sum_singleton, val_zero]
  ring

/-- **The realised cofactor sum** (first bullet of the proof of Lemma 7.3(c)): under (HBS) on
`[1, Z]`, for `1 ≤ b ≤ Z` and `b < x`,
`∑_{n ∈ 𝒩, 1 < n ≤ b} 1/(n log(x/n)) ≤ log(log x/log(x/b)) + 1.01/log(x/b)`. -/
theorem cofactor_sum_le (h : P.HBS X0m Z η1 η2 ε1) {b x : ℝ} (hb : 1 ≤ b) (hbZ : b ≤ Z)
    (hbx : b < x) :
    ∑ e ∈ (P.elems b).filter (· ≠ 0), 1 / (P.val e * Real.log (x / P.val e)) ≤
      Real.log (Real.log x / Real.log (x / b)) + 1.01 / Real.log (x / b) := by
  classical
  have hx0 : 0 < x := by linarith
  have hlogxs : ∀ s ∈ Icc (1 : ℝ) b, 0 < Real.log (x / s) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    apply Real.log_pos; rw [lt_div_iff₀ hs0, one_mul]; linarith [hs.2]
  set g : ℝ → ℝ := fun s => 1 / Real.log (x / s) with hg
  set g' : ℝ → ℝ := fun s => 1 / (s * Real.log (x / s) ^ 2) with hg'
  have hder : ∀ s ∈ Icc (1 : ℝ) b, HasDerivAt g (g' s) s := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hl := hlogxs s hs
    have h1 := (hasDerivAt_inv hs0.ne').const_mul x
    have h1' : HasDerivAt (fun t => x / t) (x * -(s ^ 2)⁻¹) s := by
      simpa [div_eq_mul_inv] using h1
    have h2 := (h1'.log (div_pos hx0 hs0).ne').inv hl.ne'
    simp only [hg, hg', one_div]
    convert! h2 using 1
    field_simp
  have hcont : ContinuousOn g' (Icc 1 b) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hl := hlogxs s hs
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div (continuousAt_id.mul (((continuousAt_const.div continuousAt_id
      hs0.ne').log (div_pos hx0 hs0).ne').pow 2)) (by positivity)
  set I := (P.elems b).filter (· ≠ 0)
  have hI : ∀ e ∈ I, (1 : ℝ) < P.val e ∧ P.val e ≤ b := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    exact ⟨one_lt_val he2, P.mem_elems.mp he1⟩
  have habel := BaseRange.abel_fin I P.val (fun e => 1 / P.val e) hb hI g g' hder hcont
  have e1 : ∑ e ∈ I, 1 / (P.val e * Real.log (x / P.val e)) =
      ∑ e ∈ I, 1 / P.val e * g (P.val e) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hg]; rw [one_div_mul_one_div]
  rw [e1, habel]
  -- `C(s) = harm1 P s` on `[1, b]`
  have hC : ∀ s ∈ Icc (1 : ℝ) b,
      (∑ e ∈ I, if P.val e ≤ s then 1 / P.val e else 0) = harm1 P s := by
    intro s hs
    unfold harm1
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [I, Finset.mem_filter, P.mem_elems]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨h3.trans hs.2, h2⟩, h3⟩
  have hCb : ∑ e ∈ I, 1 / P.val e = harm1 P b := by
    have := hC b ⟨hb, le_rfl⟩
    rw [← this]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [if_pos (hI e he).2]
  rw [hCb]
  -- bounds on `harm1`
  have hup : harm1 P b ≤ Real.log b := by
    rw [harm1_eq P hb]; have := h.harm_le hb hbZ; linarith
  have hlow : ∀ s ∈ Icc (1 : ℝ) b, Real.log s - 1.01 ≤ harm1 P s := by
    intro s hs
    rw [harm1_eq P hs.1]
    have := h.harm_ge hs.1 (hs.2.trans hbZ)
    have hη := h.eta1_le
    have hl2 := Real.log_two_lt_d9
    have hη0 := h.eta1_nonneg
    nlinarith
  have hg'0 : ∀ s ∈ Icc (1 : ℝ) b, 0 ≤ g' s := by
    intro s hs
    have := hlogxs s hs
    have : 0 < s := by linarith [hs.1]
    simp only [hg']; positivity
  -- `∫_1^b C g' ≥ ∫_1^b (log s - 1.01) g' = F(b) - F(1)`
  have hint1 : IntervalIntegrable (fun s => (∑ e ∈ I, if P.val e ≤ s then 1 / P.val e else 0) *
      g' s) volume 1 b := by
    have hsum : IntervalIntegrable (fun s => ∑ e ∈ I, if P.val e ≤ s then 1 / P.val e else 0)
        volume 1 b := by
      apply Monotone.intervalIntegrable
      intro s1 s2 hs
      apply Finset.sum_le_sum
      intro e _
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (h1.trans hs) h2
      · have := P.val_pos e; positivity
      · exact le_rfl
    exact hsum.mul_continuousOn (by rw [Set.uIcc_of_le hb]; exact hcont)
  have hint2 : IntervalIntegrable (fun s => (Real.log s - 1.01) * g' s) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    apply ContinuousOn.mul _ hcont
    exact (Real.continuousOn_log.mono fun s hs => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hs.1]).sub continuousOn_const
  have hmono : ∫ s in (1 : ℝ)..b, (Real.log s - 1.01) * g' s ≤
      ∫ s in (1 : ℝ)..b, (∑ e ∈ I, if P.val e ≤ s then 1 / P.val e else 0) * g' s := by
    apply integral_mono_on hb hint2 hint1
    intro s hs
    rw [hC s hs]
    exact mul_le_mul_of_nonneg_right (hlow s hs) (hg'0 s hs)
  -- the primitive `F(s) = (log s - 1.01) g(s) + log log(x/s)`
  have hF : ∫ s in (1 : ℝ)..b, (Real.log s - 1.01) * g' s =
      ((Real.log b - 1.01) * g b + Real.log (Real.log (x / b))) -
        ((Real.log 1 - 1.01) * g 1 + Real.log (Real.log (x / 1))) := by
    apply integral_eq_sub_of_hasDerivAt
    · intro s hs
      rw [Set.uIcc_of_le hb] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have hl := hlogxs s hs
      have h1 := (hasDerivAt_inv hs0.ne').const_mul x
      have h1' : HasDerivAt (fun t => x / t) (x * -(s ^ 2)⁻¹) s := by
        simpa [div_eq_mul_inv] using h1
      have hL := h1'.log (div_pos hx0 hs0).ne'
      have hLL := hL.log hl.ne'
      have hlog := (Real.hasDerivAt_log hs0.ne').sub_const 1.01
      have hprod := hlog.mul (hder s hs)
      convert! hprod.add hLL using 1
      simp only [hg, hg']
      field_simp
      ring
    · exact hint2
  rw [hF] at hmono
  have hg1 : 0 ≤ g 1 := by
    simp only [hg, div_one]
    have := hlogxs 1 ⟨le_rfl, hb⟩; simp only [div_one] at this; positivity
  have hgb : 0 ≤ g b := by have := hlogxs b ⟨hb, le_rfl⟩; simp only [hg]; positivity
  have hlb : Real.log (Real.log x / Real.log (x / b)) =
      Real.log (Real.log x) - Real.log (Real.log (x / b)) := by
    have hlx : 0 < Real.log x := by
      have := hlogxs 1 ⟨le_rfl, hb⟩; simpa using this
    exact Real.log_div hlx.ne' (hlogxs b ⟨hb, le_rfl⟩).ne'
  rw [hlb]
  simp only [Real.log_one, div_one] at hmono
  have hgbe : g b = 1 / Real.log (x / b) := rfl
  have : harm1 P b * g b ≤ Real.log b * g b := mul_le_mul_of_nonneg_right hup hgb
  have h101 : 1.01 / Real.log (x / b) = 1.01 * g b := by rw [hgbe]; ring
  rw [h101]
  nlinarith

end HBS

end BeurlingSystem
