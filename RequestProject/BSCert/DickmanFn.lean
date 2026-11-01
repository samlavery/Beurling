module

public import Mathlib

/-!
# Dickman's function

Dickman's function `ρ` is the continuous function with `ρ(u) = 1` for `u ≤ 1` and
`u ρ'(u) = -ρ(u - 1)` for `u > 1`. It is not in Mathlib; here it is constructed, interval by
interval, as the solution of the integral equation

  `ρ(u) = 1 - ∫_1^u ρ(t - 1)/t dt`   (`u ≥ 1`).

Main results:

* `Dickman.rho_eq` : the integral equation, `Dickman.continuous_rho`, `Dickman.hasDerivAt_rho`;
* `Dickman.mul_rho_eq_integral` : (R1) `u ρ(u) = ∫_{u-1}^u ρ` for `u ≥ 1`;
* `Dickman.rho_pos` : `ρ > 0`; `Dickman.rho_antitone`;
* `Dickman.rho_one_two` : `ρ(u) = 1 - log u` on `[1, 2]`;
* `Dickman.tendsto_integral_shift_div` : (R1) `∫_a^∞ ρ(w-1) dw/w = ρ(a)` for `a ≥ 1`;
* `Dickman.integral_shift_mul_div` : (R1) `∫_{u-1}^u ρ(w-1)(u-w) dw/w = ρ(u-1) - u ρ(u)`
  for `u ≥ 2`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace Dickman

/-- One step of the construction: `f ↦ (u ↦ 1 - ∫_1^{max u 1} f(t-1)/max t 1 dt)`. -/
noncomputable def step (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  1 - ∫ t in (1 : ℝ)..(max u 1), f (t - 1) / max t 1

/-- The iterates; `seq n` is Dickman's function on `(-∞, n + 1]`. -/
noncomputable def seq : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => step (seq n)

/-- **Dickman's function** `ρ`. -/
noncomputable def rho (u : ℝ) : ℝ := seq ⌈u⌉₊ u

lemma continuous_integrand {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t : ℝ => f (t - 1) / max t 1) := by
  apply Continuous.div (hf.comp (continuous_id.sub continuous_const))
    (continuous_id.max continuous_const)
  intro t; exact (lt_of_lt_of_le one_pos (le_max_right t 1)).ne'

lemma hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in (1 : ℝ)..x, f (t - 1) / max t 1) (f (x - 1) / max x 1) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_integrand hf).intervalIntegrable _ _)
    ((continuous_integrand hf).stronglyMeasurableAtFilter _ _)
    (continuous_integrand hf).continuousAt

lemma continuous_step {f : ℝ → ℝ} (hf : Continuous f) : Continuous (step f) := by
  have hF : Continuous (fun x => ∫ t in (1 : ℝ)..x, f (t - 1) / max t 1) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_primitive hf x).continuousAt
  exact continuous_const.sub (hF.comp (continuous_id.max continuous_const))

lemma continuous_seq (n : ℕ) : Continuous (seq n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_step ih

lemma step_congr {f g : ℝ → ℝ} {c : ℝ} (h : ∀ w ≤ c, f w = g w) {u : ℝ} (hu : u ≤ c + 1) :
    step f u = step g u := by
  unfold step
  rcases le_total u 1 with h1 | h1
  · rw [max_eq_right h1]; simp
  rw [max_eq_left h1]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h1] at ht
  simp only
  rw [h]
  linarith [ht.2]

lemma seq_succ_eq (n : ℕ) : ∀ u ≤ (n : ℝ) + 1, seq (n + 1) u = seq n u := by
  induction n with
  | zero =>
    intro u hu
    simp only [seq, step]
    rw [max_eq_right (by simpa using hu)]
    simp
  | succ n ih =>
    intro u hu
    show step (seq (n + 1)) u = step (seq n) u
    exact step_congr (c := (n : ℝ) + 1) ih (by push_cast at hu; linarith)

lemma seq_stable {n : ℕ} {u : ℝ} (hu : u ≤ (n : ℝ) + 1) : ∀ m, n ≤ m → seq m u = seq n u := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    rw [seq_succ_eq m u (by linarith), ih]

lemma rho_eq_seq {n : ℕ} {u : ℝ} (hu : u ≤ n) : rho u = seq n u := by
  unfold rho
  have hc : ⌈u⌉₊ ≤ n := Nat.ceil_le.mpr hu
  rw [seq_stable (n := ⌈u⌉₊) (by linarith [Nat.le_ceil u]) n hc]

lemma continuous_rho : Continuous rho := by
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have : seq n =ᶠ[nhds u] rho := by
    filter_upwards [Iio_mem_nhds hn] with w hw
    exact (rho_eq_seq (le_of_lt hw)).symm
  exact ((continuous_seq n).continuousAt).congr this

/-- The integral equation of Dickman's function, for every `u`:
`ρ(u) = 1 - ∫_1^{max u 1} ρ(t-1)/max t 1 dt`. -/
lemma rho_eq_step (u : ℝ) : rho u = step rho u := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  rw [rho_eq_seq (n := n + 1) (by push_cast; linarith)]
  show step (seq n) u = step rho u
  apply step_congr (c := (n : ℝ)) (fun w hw => (rho_eq_seq hw).symm) (by linarith)

lemma rho_of_le_one {u : ℝ} (hu : u ≤ 1) : rho u = 1 := by
  rw [rho_eq_step, step, max_eq_right hu]; simp

/-- **The integral equation**: `ρ(u) = 1 - ∫_1^u ρ(t-1)/t dt` for `u ≥ 1`. -/
theorem rho_eq {u : ℝ} (hu : 1 ≤ u) : rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  rw [rho_eq_step, step, max_eq_left hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu] at ht
  simp only [max_eq_left ht.1]

/-- `ρ'(u) = -ρ(u-1)/u` for `u > 1`. -/
theorem hasDerivAt_rho {u : ℝ} (hu : 1 < u) : HasDerivAt rho (-(rho (u - 1) / u)) u := by
  have hF := hasDerivAt_primitive continuous_rho u
  rw [max_eq_left hu.le] at hF
  have h := (hasDerivAt_const u (1 : ℝ)).sub hF
  rw [zero_sub] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with w hw
  rw [rho_eq_step, step, max_eq_left (le_of_lt hw)]
  rfl

/-- `ρ'(u) = 0` for `u < 1`. -/
theorem hasDerivAt_rho_of_lt {u : ℝ} (hu : u < 1) : HasDerivAt rho 0 u := by
  apply (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hu] with w hw
  exact rho_of_le_one hw.le

/-- The right derivative at every `u ≥ 1`: `ρ'(u+) = -ρ(u-1)/u`. -/
theorem hasDerivWithinAt_rho {u : ℝ} (hu : 1 ≤ u) :
    HasDerivWithinAt rho (-(rho (u - 1) / u)) (Ici u) u := by
  have hF := hasDerivAt_primitive continuous_rho u
  rw [max_eq_left hu] at hF
  have h := ((hasDerivAt_const u (1 : ℝ)).sub hF).hasDerivWithinAt (s := Ici u)
  rw [zero_sub] at h
  apply h.congr_of_mem (fun w hw => ?_) self_mem_Ici
  rw [rho_eq_step, step, max_eq_left (hu.trans hw)]
  rfl

lemma hasDerivAt_integral_window (u : ℝ) :
    HasDerivAt (fun u => ∫ t in (u - 1)..u, rho t) (rho u - rho (u - 1)) u := by
  have hP : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, rho t) (rho x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (continuous_rho.intervalIntegrable _ _)
      (continuous_rho.stronglyMeasurableAtFilter _ _) continuous_rho.continuousAt
  have h1 := hP u
  have h2 := (hP (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  simp only [mul_one, Function.comp_def] at h2
  have := h1.sub h2
  apply this.congr_of_eventuallyEq
  filter_upwards with w
  simp only [Pi.sub_apply, id]
  rw [intervalIntegral.integral_interval_sub_left (continuous_rho.intervalIntegrable _ _)
    (continuous_rho.intervalIntegrable _ _)]

/-- **(R1)**: `u ρ(u) = ∫_{u-1}^u ρ` for `u ≥ 1`. -/
theorem mul_rho_eq_integral {u : ℝ} (hu : 1 ≤ u) : u * rho u = ∫ t in (u - 1)..u, rho t := by
  set G : ℝ → ℝ := fun u => u * rho u - ∫ t in (u - 1)..u, rho t
  have hG : ∀ x ∈ Ico (1 : ℝ) u, HasDerivWithinAt G 0 (Ici x) x := by
    intro x hx
    have h1 := (hasDerivWithinAt_id x (Ici x)).mul (hasDerivWithinAt_rho hx.1)
    have h2 := (hasDerivAt_integral_window x).hasDerivWithinAt (s := Ici x)
    have h := h1.sub h2
    have hx0 : x ≠ 0 := by linarith [hx.1]
    convert! h using 1
    simp only [id]
    field_simp
    ring
  have hc : ContinuousOn G (Icc 1 u) := by
    apply Continuous.continuousOn
    exact (continuous_id.mul continuous_rho).sub
      (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_integral_window x).continuousAt)
  have := constant_of_has_deriv_right_zero hc hG u ⟨hu, le_rfl⟩
  have h1 : G 1 = 0 := by
    simp only [G, sub_self, rho_of_le_one le_rfl, one_mul]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact rho_of_le_one ht.2)]
    simp
  have : G u = 0 := this.trans h1
  simp only [G] at this
  linarith

/-- `ρ(u) > 0` for every `u`. -/
theorem rho_pos (u : ℝ) : 0 < rho u := by
  by_contra hneg
  push_neg at hneg
  set S : Set ℝ := {w | rho w ≤ 0}
  have hS : S.Nonempty := ⟨u, hneg⟩
  have hbdd : BddBelow S := ⟨1, fun w hw => by
    by_contra h; push_neg at h
    have := rho_of_le_one h.le
    simp only [S, mem_setOf_eq] at hw; linarith⟩
  have hclosed : IsClosed S := isClosed_le continuous_rho continuous_const
  set w := sInf S
  have hw : w ∈ S := hclosed.csInf_mem hS hbdd
  have hlow : ∀ t < w, 0 < rho t := fun t ht => by
    by_contra h; push_neg at h
    exact absurd (csInf_le hbdd h) (not_le.mpr ht)
  have hw1 : 1 < w := by
    by_contra h; push_neg at h
    have := rho_of_le_one h
    simp only [S, mem_setOf_eq] at hw; linarith
  have hint : 0 < ∫ t in (w - 1)..w, rho t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_rho.intervalIntegrable _ _)
      (fun t ht => hlow t ht.2) (by linarith)
  rw [← mul_rho_eq_integral hw1.le] at hint
  have : rho w ≤ 0 := hw
  nlinarith

/-- `ρ` is non-increasing. -/
theorem rho_antitone : Antitone rho := by
  have h1 : AntitoneOn rho (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1) continuous_rho.continuousOn
    · intro x hx
      rw [interior_Ici] at hx
      exact (hasDerivAt_rho hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_rho hx).deriv]
      have := rho_pos (x - 1)
      have : 0 < x := by linarith [mem_Ioi.mp hx]
      have : 0 ≤ rho (x - 1) / x := by positivity
      linarith
  intro a b hab
  rcases le_total b 1 with hb | hb
  · rw [rho_of_le_one hb, rho_of_le_one (hab.trans hb)]
  rcases le_total a 1 with ha | ha
  · rw [rho_of_le_one ha]
    have := h1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb) hb
    rwa [rho_of_le_one le_rfl] at this
  · exact h1 (mem_Ici.mpr ha) (mem_Ici.mpr hb) hab

/-- `ρ(u) = 1 - log u` on `[1, 2]`. -/
theorem rho_one_two {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : rho u = 1 - Real.log u := by
  rw [rho_eq hu1]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun t => 1 / t) (fun t ht => by
    rw [uIcc_of_le hu1] at ht
    simp only
    rw [rho_of_le_one (by linarith [ht.2])])]
  rw [integral_one_div_of_pos one_pos (by linarith), div_one]

lemma intervalIntegrable_shift_div {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun t => rho (t - 1) / t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuous_rho.comp (continuous_id.sub continuous_const)).continuousOn
    continuousOn_id
  intro t ht
  have : 1 ≤ t := by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at ht; linarith [ht.1]
    · rw [uIcc_of_ge h] at ht; linarith [ht.1]
  simp only [id]; linarith

/-- `∫_a^b ρ(w-1)/w dw = ρ(a) - ρ(b)` for `a, b ≥ 1`. -/
theorem integral_shift_div {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ w in a..b, rho (w - 1) / w = rho a - rho b := by
  have e := intervalIntegral.integral_interval_sub_left (intervalIntegrable_shift_div le_rfl hb)
    (intervalIntegrable_shift_div le_rfl ha)
  rw [rho_eq ha, rho_eq hb]
  linarith

/-- `u ρ(u) ≤ ρ(u-1)` for `u ≥ 1`. -/
theorem mul_rho_le {u : ℝ} (hu : 1 ≤ u) : u * rho u ≤ rho (u - 1) := by
  rw [mul_rho_eq_integral hu]
  have h : ∫ t in (u - 1)..u, rho t ≤ ∫ t in (u - 1)..u, rho (u - 1) :=
    intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
      (continuous_rho.intervalIntegrable _ _) intervalIntegrable_const
      (fun t ht => rho_antitone ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  simpa using h

lemma rho_le_one (u : ℝ) : rho u ≤ 1 := by
  rcases le_total u 1 with h | h
  · rw [rho_of_le_one h]
  · have := rho_antitone h; rwa [rho_of_le_one le_rfl] at this

/-- `ρ(u) ≤ 1/u` for `u ≥ 1`, hence `ρ(u) → 0`. -/
theorem rho_le_inv {u : ℝ} (hu : 1 ≤ u) : rho u ≤ 1 / u := by
  rw [le_div_iff₀ (by linarith), mul_comm]
  exact (mul_rho_le hu).trans (rho_le_one _)

theorem tendsto_rho_atTop : Filter.Tendsto rho Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop Filter.tendsto_id) (Filter.Eventually.of_forall
      fun u => (rho_pos u).le)
  filter_upwards [Filter.eventually_ge_atTop 1] with u hu
  exact rho_le_inv hu

/-- **(R1)**, second identity: `∫_a^∞ ρ(w-1) dw/w = ρ(a)` for `a ≥ 1` (as a limit). -/
theorem tendsto_integral_shift_div {a : ℝ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b => ∫ w in a..b, rho (w - 1) / w) Filter.atTop (nhds (rho a)) := by
  have h : Filter.Tendsto (fun b => rho a - rho b) Filter.atTop (nhds (rho a - 0)) :=
    tendsto_const_nhds.sub tendsto_rho_atTop
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with b hb
  exact (integral_shift_div ha hb).symm

/-- **(R1)**, third identity: for `u ≥ 2`,
`∫_{u-1}^u ρ(w-1)(u-w) dw/w = ρ(u-1) - u ρ(u)`. -/
theorem integral_shift_mul_div {u : ℝ} (hu : 2 ≤ u) :
    ∫ w in (u - 1)..u, rho (w - 1) * (u - w) / w = rho (u - 1) - u * rho u := by
  have hcongr : ∫ w in (u - 1)..u, rho (w - 1) * (u - w) / w =
      ∫ w in (u - 1)..u, (u * (rho (w - 1) / w) - rho (w - 1)) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le (by linarith)] at hw
    have : w ≠ 0 := by linarith [hw.1]
    simp only
    field_simp
  have hi : IntervalIntegrable (fun w => rho (w - 1)) volume (u - 1) u :=
    (continuous_rho.comp (continuous_sub_right (1 : ℝ))).intervalIntegrable _ _
  rw [hcongr, intervalIntegral.integral_sub
    ((intervalIntegrable_shift_div (by linarith) (by linarith)).const_mul u) hi,
    intervalIntegral.integral_const_mul, integral_shift_div (by linarith) (by linarith),
    intervalIntegral.integral_comp_sub_right (fun t => rho t) 1]
  have h := mul_rho_eq_integral (u := u - 1) (by linarith)
  rw [← h]
  ring

end Dickman
