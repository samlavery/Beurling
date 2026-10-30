module

public import Mathlib

/-!
# Partial summation for the induction step of Theorem 5.6 (Step 5, (bs-D1))

An abstract form of the partial summation of Step 5 of the proof of Theorem 5.6, written in the
variable `w` (so that the left end `a = w_lo` corresponds to the top prime `σ_a`).

* `ps_identity`: for points `w_i ∈ [a, b)` with weights `c_i`, and `H` continuous on `[a, b]`,
  differentiable off a countable set with integrable derivative,
  `∑ c_i H(w_i) = H(b) R(b) - ∫_a^b H' R`, where `R(x) = ∑_{w_i < x} c_i`.
* `ps_bound`: if moreover `|R(x) - log((1+x)/(1+a))| ≤ K(1+x)/ℓ` on `[a, b]` (this is
  Lemma 5.1(iv) in the variable `w`, `σ = ℓ/(1+w)`), `H ≥ 0`, and `|H'| ≤ -H' + 2Hη` off the
  countable set (this holds for `H = H₁H₂` with `H₁` non-increasing and `|H₂'| ≤ η H₂`), then
  `∑ c_i H(w_i) ≤ ∫ H/(1+x) + K H(a)(1+a)/ℓ + (K/ℓ)∫ H + (2K/ℓ) ∫ H η (1+x)`.

In the variable `σ = ℓ/(1+w)` this is (bs-D1) with `K f(σ_a)/σ_a` in place of `2K' f(σ_a)/σ_a`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace BSaias

/-- The counting function `R(x) = ∑_{i ∈ s, w_i < x} c_i`. -/
noncomputable def cnt {ι : Type*} (s : Finset ι) (w c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, (Ioi (w i)).indicator (fun _ => c i) x

lemma intervalIntegrable_mul_cnt {ι : Type*} (s : Finset ι) (w c : ι → ℝ) {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => f x * cnt s w c x) volume a b := by
  have : (fun x => f x * cnt s w c x) =
      fun x => ∑ i ∈ s, (Ioi (w i)).indicator (fun x => c i * f x) x := by
    funext x
    unfold cnt
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ Ioi (w i) <;> simp [hx, mul_comm]
  rw [this, intervalIntegrable_iff]
  rw [intervalIntegrable_iff] at hf
  exact integrable_finset_sum s fun i _ => (hf.const_mul (c i)).indicator measurableSet_Ioi

/-- **Partial summation, identity form.** -/
theorem ps_identity {ι : Type*} (s : Finset ι) (w c : ι → ℝ) {a b : ℝ}
    (hw : ∀ i ∈ s, a ≤ w i ∧ w i < b) (H H' : ℝ → ℝ) {C : Set ℝ} (hC : C.Countable)
    (Hc : ContinuousOn H (Icc a b)) (Hd : ∀ x ∈ Ioo a b \ C, HasDerivAt H (H' x) x)
    (Hi : IntervalIntegrable H' volume a b) :
    ∑ i ∈ s, c i * H (w i) = H b * cnt s w c b - ∫ x in a..b, H' x * cnt s w c x := by
  have hone : ∀ i ∈ s, H (w i) = H b - ∫ x in a..b, (Ioi (w i)).indicator H' x := by
    intro i hi
    obtain ⟨h1, h2⟩ := hw i hi
    have hab : a ≤ b := h1.trans h2.le
    have hsub : Icc (w i) b ⊆ Icc a b := Icc_subset_Icc h1 le_rfl
    have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le H H' h2.le hC (Hc.mono hsub)
      (fun x hx => Hd x ⟨⟨h1.trans_lt hx.1.1, hx.1.2⟩, hx.2⟩)
      (Hi.mono_set (by rw [uIcc_of_le h2.le, uIcc_of_le hab]; exact hsub))
    have hsplit : ∫ x in a..b, (Ioi (w i)).indicator H' x =
        (∫ x in a..w i, (Ioi (w i)).indicator H' x) +
          ∫ x in w i..b, (Ioi (w i)).indicator H' x := by
      rw [integral_add_adjacent_intervals]
      · rw [intervalIntegrable_iff] at Hi ⊢
        refine (Hi.mono_set ?_).indicator measurableSet_Ioi
        rw [uIoc_of_le h1, uIoc_of_le hab]; exact Ioc_subset_Ioc le_rfl h2.le
      · rw [intervalIntegrable_iff] at Hi ⊢
        refine (Hi.mono_set ?_).indicator measurableSet_Ioi
        rw [uIoc_of_le h2.le, uIoc_of_le hab]; exact Ioc_subset_Ioc h1 le_rfl
    have hz : ∫ x in a..w i, (Ioi (w i)).indicator H' x = 0 := by
      rw [integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro x hx
        rw [uIcc_of_le h1] at hx
        simp [indicator_of_notMem (show x ∉ Ioi (w i) from fun h => absurd hx.2 (not_le.mpr h))]
    have hb : ∫ x in w i..b, (Ioi (w i)).indicator H' x = ∫ x in w i..b, H' x := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [uIoc_of_le h2.le] at hx
      exact indicator_of_mem (show x ∈ Ioi (w i) from hx.1) _
    rw [hsplit, hz, hb, hFTC]; ring
  have hint : ∀ i ∈ s, IntervalIntegrable (fun x => (Ioi (w i)).indicator H' x) volume a b := by
    intro i _
    rw [intervalIntegrable_iff] at Hi ⊢
    exact Hi.indicator measurableSet_Ioi
  have hR : ∀ x, H' x * cnt s w c x = ∑ i ∈ s, c i * (Ioi (w i)).indicator H' x := by
    intro x
    unfold cnt
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ Ioi (w i) <;> simp [hx, mul_comm]
  simp_rw [hR]
  rw [integral_finset_sum (fun i hi => (hint i hi).const_mul (c i))]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl fun i hi => by rw [hone i hi]]
  have hcb : cnt s w c b = ∑ i ∈ s, c i := by
    unfold cnt
    exact Finset.sum_congr rfl fun i hi => indicator_of_mem (show b ∈ Ioi (w i) from (hw i hi).2) _
  rw [hcb, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma ae_restrict_off_countable {C : Set ℝ} (hC : C.Countable) {a b : ℝ} {p : ℝ → Prop}
    (h : ∀ x ∈ Ioo a b \ C, p x) : ∀ᵐ x ∂(volume.restrict (Icc a b)), p x := by
  have hD : (C ∪ {a, b}).Countable := hC.union (by simp)
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hD.ae_notMem volume] with x hx hxI
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hx
  exact h x ⟨⟨lt_of_le_of_ne hxI.1 (Ne.symm hx.2.1), lt_of_le_of_ne hxI.2 hx.2.2⟩, hx.1⟩

/-- **Partial summation, bound form** ((bs-D1) in the variable `w`). -/
theorem ps_bound {ι : Type*} (s : Finset ι) (w c : ι → ℝ) {a b ℓ K : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (hw : ∀ i ∈ s, a ≤ w i ∧ w i < b)
    (hR : ∀ x ∈ Icc a b, |cnt s w c x - Real.log ((1 + x) / (1 + a))| ≤ K * (1 + x) / ℓ)
    (H H' η : ℝ → ℝ) {C : Set ℝ} (hC : C.Countable)
    (Hc : ContinuousOn H (Icc a b)) (Hd : ∀ x ∈ Ioo a b \ C, HasDerivAt H (H' x) x)
    (Hi : IntervalIntegrable H' volume a b) (Hnn : ∀ x ∈ Icc a b, 0 ≤ H x)
    (hη : ContinuousOn η (Icc a b))
    (hHη : ∀ x ∈ Ioo a b \ C, |H' x| ≤ -H' x + 2 * H x * η x) :
    ∑ i ∈ s, c i * H (w i) ≤ (∫ x in a..b, H x / (1 + x)) + K * H a * (1 + a) / ℓ
      + K / ℓ * (∫ x in a..b, H x) + 2 * K / ℓ * ∫ x in a..b, H x * η x * (1 + x) := by
  have hid := ps_identity s w c hw H H' hC Hc Hd Hi
  set L : ℝ → ℝ := fun x => Real.log ((1 + x) / (1 + a)) with hL
  set R := cnt s w c with hRdef
  have hUI : uIcc a b = Icc a b := uIcc_of_le hab
  have hpos : ∀ x ∈ Icc a b, 0 < 1 + x := fun x hx => by linarith [hx.1]
  have hLc : ContinuousOn L (Icc a b) := by
    refine ContinuousOn.log ?_ ?_
    · exact (continuousOn_const.add continuousOn_id).div continuousOn_const
        (fun _ _ => by linarith)
    · intro x hx; exact (div_pos (hpos x hx) (by linarith)).ne'
  have hinvc : ContinuousOn (fun x => 1 / (1 + x)) (Icc a b) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) fun x hx => (hpos x hx).ne'
  have hlinc : ContinuousOn (fun x : ℝ => 1 + x) (Icc a b) :=
    continuousOn_const.add continuousOn_id
  -- integrabilities
  have iHL : IntervalIntegrable (fun x => H' x * L x) volume a b :=
    Hi.mul_continuousOn (by rw [hUI]; exact hLc)
  have iHR : IntervalIntegrable (fun x => H' x * R x) volume a b :=
    intervalIntegrable_mul_cnt s w c Hi
  have iHinv : IntervalIntegrable (fun x => H x * (1 / (1 + x))) volume a b :=
    (Hc.mul hinvc).intervalIntegrable_of_Icc hab
  have iH : IntervalIntegrable H volume a b := Hc.intervalIntegrable_of_Icc hab
  have iHlin : IntervalIntegrable (fun x => H' x * (1 + x)) volume a b :=
    Hi.mul_continuousOn (by rw [hUI]; exact hlinc)
  -- FTC for H L
  have hHL : ∫ x in a..b, (H' x * L x + H x * (1 / (1 + x))) = H b * L b - H a * L a := by
    apply integral_eq_of_hasDerivAt_off_countable_of_le (fun x => H x * L x) _ hab hC
      (Hc.mul hLc)
    · intro x hx
      have hx1 : 0 < 1 + x := by linarith [hx.1.1]
      have hdL : HasDerivAt L (1 / (1 + x)) x := by
        have h1 : HasDerivAt (fun x => (1 + x) / (1 + a)) (1 / (1 + a)) x := by
          simpa using ((hasDerivAt_id x).const_add 1).div_const (1 + a)
        have h2 := h1.log (div_pos hx1 (by linarith)).ne'
        convert! h2 using 1
        field_simp
      exact (Hd x hx).mul hdL
    · exact iHL.add iHinv
  have hLa : L a = 0 := by simp [hL]
  -- FTC for H (1 + x)
  have hHlin : ∫ x in a..b, (H' x * (1 + x) + H x * 1) = H b * (1 + b) - H a * (1 + a) := by
    apply integral_eq_of_hasDerivAt_off_countable_of_le (fun x => H x * (1 + x)) _ hab hC
      (Hc.mul hlinc)
    · intro x hx
      exact (Hd x hx).mul ((hasDerivAt_id x).const_add 1)
    · exact iHlin.add (by simpa using iH)
  rw [integral_add iHL iHinv] at hHL
  rw [integral_add iHlin (by simpa using iH)] at hHlin
  simp only [mul_one] at hHlin
  -- e = R - L
  have iHe : IntervalIntegrable (fun x => H' x * (R x - L x)) volume a b := by
    have := iHR.sub iHL
    convert! this using 1
    funext x; ring
  have hsplitRL : ∫ x in a..b, H' x * R x =
      (∫ x in a..b, H' x * L x) + ∫ x in a..b, H' x * (R x - L x) := by
    rw [← integral_add iHL iHe]
    congr 1; funext x; ring
  -- bound for the e-term
  have iabs : IntervalIntegrable (fun x => |H' x| * (K * (1 + x) / ℓ)) volume a b := by
    refine Hi.abs.mul_continuousOn ?_
    rw [hUI]
    exact (continuousOn_const.mul hlinc).div continuousOn_const fun _ _ => hℓ.ne'
  have he1 : -(∫ x in a..b, H' x * (R x - L x)) ≤ ∫ x in a..b, |H' x| * (K * (1 + x) / ℓ) := by
    rw [← intervalIntegral.integral_neg]
    apply integral_mono_on hab iHe.neg iabs
    intro x hx
    have h1 := hR x hx
    have h2 : -(H' x * (R x - L x)) ≤ |H' x| * |R x - L x| := by
      rw [← abs_mul]; exact neg_le_abs _
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  have iη : IntervalIntegrable (fun x => H x * η x * (1 + x)) volume a b :=
    ((Hc.mul hη).mul hlinc).intervalIntegrable_of_Icc hab
  have iright : IntervalIntegrable
      (fun x => (-H' x + 2 * H x * η x) * (K * (1 + x) / ℓ)) volume a b := by
    have i2 : IntervalIntegrable (fun x => 2 * H x * η x) volume a b := by
      have := ((Hc.mul hη).intervalIntegrable_of_Icc (μ := volume) hab).const_mul 2
      convert! this using 1
      funext x; simp only [Pi.mul_apply]; ring
    refine (Hi.neg.add i2).mul_continuousOn ?_
    rw [hUI]
    exact (continuousOn_const.mul hlinc).div continuousOn_const fun _ _ => hℓ.ne'
  have he2 : ∫ x in a..b, |H' x| * (K * (1 + x) / ℓ) ≤
      ∫ x in a..b, (-H' x + 2 * H x * η x) * (K * (1 + x) / ℓ) := by
    apply integral_mono_ae_restrict hab iabs iright
    refine ae_restrict_off_countable hC fun x hx => ?_
    have hx1 : 0 ≤ K * (1 + x) / ℓ := div_nonneg (mul_nonneg hK (by linarith [hx.1.1])) hℓ.le
    exact mul_le_mul_of_nonneg_right (hHη x hx) hx1
  have he3 : ∫ x in a..b, (-H' x + 2 * H x * η x) * (K * (1 + x) / ℓ) =
      -(K / ℓ) * (∫ x in a..b, H' x * (1 + x)) +
        2 * K / ℓ * ∫ x in a..b, H x * η x * (1 + x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← integral_add (iHlin.const_mul _) (iη.const_mul _)]
    congr 1; funext x; ring
  have hb1 : H b * (R b - L b) ≤ K * H b * (1 + b) / ℓ := by
    have h1 := hR b ⟨hab, le_rfl⟩
    have h2 : R b - L b ≤ K * (1 + b) / ℓ := (le_abs_self _).trans h1
    have := mul_le_mul_of_nonneg_left h2 (Hnn b ⟨hab, le_rfl⟩)
    calc H b * (R b - L b) ≤ H b * (K * (1 + b) / ℓ) := this
      _ = K * H b * (1 + b) / ℓ := by ring
  have hdivH : ∫ x in a..b, H x / (1 + x) = ∫ x in a..b, H x * (1 / (1 + x)) := by
    congr 1; funext x; ring
  rw [hid, hsplitRL, hdivH]
  have e1 : K * H a * (1 + a) / ℓ = K / ℓ * (H a * (1 + a)) := by ring
  have e2 : K * H b * (1 + b) / ℓ = K / ℓ * (H b * (1 + b)) := by ring
  rw [e1]; rw [e2] at hb1
  have hHlin' : ∫ x in a..b, H' x * (1 + x) =
      H b * (1 + b) - H a * (1 + a) - ∫ x in a..b, H x := by linarith
  have h5 : K / ℓ * ∫ x in a..b, H' x * (1 + x) =
      K / ℓ * (H b * (1 + b)) - K / ℓ * (H a * (1 + a)) - K / ℓ * ∫ x in a..b, H x := by
    rw [hHlin']; ring
  rw [hLa, mul_zero, sub_zero] at hHL
  have h6 : H b * R b - H b * L b = H b * (R b - L b) := by ring
  linarith [he1, he2, he3, hb1, hHL, h5, h6]

end BSaias

end
