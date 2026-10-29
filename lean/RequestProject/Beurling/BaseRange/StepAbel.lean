module

public import RequestProject.Beurling.BaseRange.Split
public import RequestProject.Beurling.BaseRange.AbelFin

/-!
# Step 3 of the proof of Lemma 7.3(b): one replacement

One replacement in the symmetric telescoping compares, for fixed other variables (cofactor
value `m`), the sums of `F(m p) = f₀(u/(m p))/(m p)` over the large primes `p ≤ β` of the two
systems. With `θ_X(s) = ∑_{x ∈ X, v(x) ≤ s} log v(x)`, Abel summation against `θ_X - θ_Y` gives
(`one_replacement`)

  `|∑_{x ∈ X, v(x) ≤ β} F(m v(x)) - ∑_{y ∈ Y, v(y) ≤ β} F(m v(y))| ≤ 12 B log² β/(Λ m)`

whenever `|θ_X - θ_Y| ≤ B s (log s + 1)²` on `[a, β]`, all points lie in `(a, ∞)`, `log a ≥ 1`,
and `β ≤ u/(X₀ m)` (so that `f₀` is evaluated on `[X₀, ∞)`). The paper's bound is
`4κ log² b/(m_j Λ)` with `B ≈ 5κ`; the constant is immaterial (the final bound has a factor `Λ`
to spare).

* `f0s` : `f₀(q) = (G((1+κ)q) - G(q))/(κq)`, `G(x) = ∫₂^x dt/log t`, a `C¹` form of `f₀`;
  `f0s_eq` (it is `f₀` on `[X₀, ∞)`), `f0s_le`, `abs_mul_deriv_f0s_le` (`|q f₀'(q)| ≤ 2/log q`);
* `abel_diff` : the Abel identity for the difference of two prime sums.
-/

@[expose] public section

open Real Finset MeasureTheory intervalIntegral

namespace BaseRange

/-- `G(x) = ∫₂^x dt/log t`. -/
noncomputable def Gli (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

lemma continuousOn_inv_log_Ioi : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; have : (1 : ℝ) < t := ht; linarith
  · intro t ht; exact (Real.log_pos ht).ne'

lemma hasDerivAt_Gli {x : ℝ} (hx : 1 < x) : HasDerivAt Gli (1 / Real.log x) x := by
  unfold Gli
  have hc := continuousOn_inv_log_Ioi
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    simp only [Set.mem_Ioi]
    rcases ht with h | h <;> linarith [h.1]
  · exact hc.stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact hc.continuousAt (isOpen_Ioi.mem_nhds hx)

lemma Gli_sub {a b : ℝ} (ha : 1 < a) (hb : 1 < b) : Gli b - Gli a = liI a b := by
  unfold Gli liI
  have hc := continuousOn_inv_log_Ioi
  have hi : ∀ x y : ℝ, 1 < x → 1 < y →
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume x y :=
    by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    simp only [Set.mem_Ioi]
    rcases ht with h | h <;> linarith [h.1]
  rw [intervalIntegral.integral_interval_sub_left (hi 2 b (by norm_num) hb)
    (hi 2 a (by norm_num) ha)]

/-- A `C¹` form of `f₀`: `f0s(q) = (G((1+κ)q) - G(q))/(κq)`. -/
noncomputable def f0s (κ q : ℝ) : ℝ := (Gli ((1 + κ) * q) - Gli q) / (κ * q)

lemma f0s_eq {X0 : ℕ} {κ q : ℝ} (hX : 1 < (X0 : ℝ)) (hκ : 0 < κ) (hq : (X0 : ℝ) ≤ q) :
    f0s κ q = f0 X0 κ q := by
  have hq1 : 1 < q := by linarith
  rw [f0_eq hκ.le hq, f0s, Gli_sub hq1 (by nlinarith)]

/-- The derivative of `f0s`. -/
noncomputable def f0s' (κ q : ℝ) : ℝ :=
  (((1 + κ) / Real.log ((1 + κ) * q) - 1 / Real.log q) * (κ * q) -
    (Gli ((1 + κ) * q) - Gli q) * κ) / (κ * q) ^ 2

lemma hasDerivAt_f0s {κ q : ℝ} (hκ : 0 < κ) (hq : 1 < q) :
    HasDerivAt (f0s κ) (f0s' κ q) q := by
  have hq1 : 1 < (1 + κ) * q := by nlinarith
  have h1 := (hasDerivAt_Gli hq1).comp q ((hasDerivAt_id' q).const_mul (1 + κ))
  have h2 := h1.sub (hasDerivAt_Gli hq)
  have h3 := (hasDerivAt_id' q).const_mul κ
  have h4 := h2.div h3 (by positivity)
  unfold f0s f0s'
  refine h4.congr_deriv ?_
  simp only [Function.comp, Pi.sub_apply, mul_one]
  ring

/-- `0 ≤ f0s ≤ 1/log q` and `|q f0s'(q)| ≤ 2/log q` for `q ≥ e`. -/
lemma f0s_bounds {κ q : ℝ} (hκ : 0 < κ) (hq : Real.exp 1 ≤ q) :
    0 ≤ f0s κ q ∧ f0s κ q ≤ 1 / Real.log q ∧ |q * f0s' κ q| ≤ 2 / Real.log q := by
  have he := Real.add_one_le_exp (1 : ℝ)
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hL : 1 ≤ Real.log q := by rw [Real.le_log_iff_exp_le hq0]; exact hq
  have hb : q < (1 + κ) * q := by nlinarith
  have hli := liI_pos hq1 hb
  have hle := liI_le hq1 hb.le
  have hκq := mul_pos hκ hq0
  rw [show (1 + κ) * q - q = κ * q by ring] at hle
  have hG : Gli ((1 + κ) * q) - Gli q = liI q ((1 + κ) * q) := Gli_sub hq1 (by linarith)
  have hf0 : 0 ≤ f0s κ q := by unfold f0s; rw [hG]; positivity
  have hf1 : f0s κ q ≤ 1 / Real.log q := by
    unfold f0s; rw [hG, div_le_iff₀ hκq]
    calc liI q ((1 + κ) * q) ≤ κ * q / Real.log q := hle
      _ = 1 / Real.log q * (κ * q) := by ring
  refine ⟨hf0, hf1, ?_⟩
  -- `q f0s' = L'/κ - f0s` with `0 ≤ L' ≤ κ/log q`
  set L' := (1 + κ) / Real.log ((1 + κ) * q) - 1 / Real.log q
  have hLq : Real.log q ≤ Real.log ((1 + κ) * q) := Real.log_le_log hq0 hb.le
  have hLq2 : Real.log ((1 + κ) * q) ≤ Real.log q + κ := by
    rw [Real.log_mul (by linarith) hq0.ne']
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + κ); linarith
  have hL'0 : 0 ≤ L' := by
    simp only [L']
    rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hL'1 : L' ≤ κ / Real.log q := by
    simp only [L']
    have : (1 + κ) / Real.log ((1 + κ) * q) ≤ (1 + κ) / Real.log q :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hLq
    have e : (1 + κ) / Real.log q - 1 / Real.log q = κ / Real.log q := by ring
    linarith
  have hq' : q * f0s' κ q = L' / κ - f0s κ q := by
    unfold f0s' f0s; simp only [L']; field_simp
  rw [hq']
  have hL'κ : L' / κ ≤ 1 / Real.log q := by
    rw [div_le_iff₀ hκ]; calc L' ≤ κ / Real.log q := hL'1
      _ = 1 / Real.log q * κ := by ring
  have hL'κ0 : 0 ≤ L' / κ := div_nonneg hL'0 hκ.le
  have e2 : 2 / Real.log q = 2 * (1 / Real.log q) := by ring
  rw [abs_le, e2]
  constructor <;> linarith

/-! ### The Abel identity for two prime sums -/

/-- `θ_X(s) = ∑_{x ∈ X, v(x) ≤ s} log v(x)`. -/
noncomputable def thetaF {ι : Type*} (v : ι → ℝ) (X : Finset ι) (s : ℝ) : ℝ :=
  ∑ x ∈ X.filter (fun x => v x ≤ s), Real.log (v x)

/-- **Abel summation for the difference of two prime sums**. -/
theorem abel_diff {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι) (Y : Finset κ')
    {a β : ℝ} (ha1 : 1 ≤ a)
    (haβ : a ≤ β) (hX : ∀ x ∈ X, a < vX x) (hY : ∀ y ∈ Y, a < vY y) (w w' : ℝ → ℝ)
    (hw : ∀ s ∈ Set.Icc a β, HasDerivAt w (w' s) s) (hwc : ContinuousOn w' (Set.Icc a β)) :
    ∑ x ∈ X.filter (fun x => vX x ≤ β), Real.log (vX x) * w (vX x) -
        ∑ y ∈ Y.filter (fun y => vY y ≤ β), Real.log (vY y) * w (vY y) =
      (thetaF vX X β - thetaF vY Y β) * w β -
        ∫ s in a..β, (thetaF vX X s - thetaF vY Y s) * w' s := by
  classical
  have hA := abel_fin (X.filter (fun x => vX x ≤ β)) vX (fun x => Real.log (vX x)) haβ
    (fun x hx => ⟨hX x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩) w w' hw hwc
  have hB := abel_fin (Y.filter (fun y => vY y ≤ β)) vY (fun y => Real.log (vY y)) haβ
    (fun y hy => ⟨hY y (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩) w w' hw hwc
  have hC : ∀ (Z : Finset ι), ∀ s ∈ Set.uIcc a β,
      (∑ z ∈ Z.filter (fun z => vX z ≤ β), if vX z ≤ s then Real.log (vX z) else 0) * w' s =
        thetaF vX Z s * w' s := by
    intro Z s hs
    rw [Set.uIcc_of_le haβ] at hs
    congr 1
    unfold thetaF
    rw [← Finset.sum_filter, Finset.filter_filter]
    congr 1
    ext z; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3.trans hs.2, h3⟩
  have hC' : ∀ (Z : Finset κ'), ∀ s ∈ Set.uIcc a β,
      (∑ z ∈ Z.filter (fun z => vY z ≤ β), if vY z ≤ s then Real.log (vY z) else 0) * w' s =
        thetaF vY Z s * w' s := by
    intro Z s hs
    rw [Set.uIcc_of_le haβ] at hs
    congr 1
    unfold thetaF
    rw [← Finset.sum_filter, Finset.filter_filter]
    congr 1
    ext z; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, h3.trans hs.2, h3⟩
  rw [intervalIntegral.integral_congr (hC X)] at hA
  rw [intervalIntegral.integral_congr (hC' Y)] at hB
  have hthX : ∑ x ∈ X.filter (fun x => vX x ≤ β), Real.log (vX x) = thetaF vX X β := rfl
  have hthY : ∑ y ∈ Y.filter (fun y => vY y ≤ β), Real.log (vY y) = thetaF vY Y β := rfl
  rw [hthX] at hA; rw [hthY] at hB
  have hmono : ∀ (Z : Finset ι), (∀ z ∈ Z, a < vX z) →
      IntervalIntegrable (fun s => thetaF vX Z s * w' s) volume a β := by
    intro Z h1
    have hm : Monotone (thetaF vX Z) := by
      intro s1 s2 hs
      unfold thetaF
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hs⟩
      · intro z hz _
        exact Real.log_nonneg (by linarith [h1 z (Finset.mem_filter.mp hz).1])
    exact hm.intervalIntegrable.mul_continuousOn (by rw [Set.uIcc_of_le haβ]; exact hwc)
  have hmonoY : ∀ (Z : Finset κ'), (∀ z ∈ Z, a < vY z) →
      IntervalIntegrable (fun s => thetaF vY Z s * w' s) volume a β := by
    intro Z h1
    have hm : Monotone (thetaF vY Z) := by
      intro s1 s2 hs
      unfold thetaF
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hs⟩
      · intro z hz _
        exact Real.log_nonneg (by linarith [h1 z (Finset.mem_filter.mp hz).1])
    exact hm.intervalIntegrable.mul_continuousOn (by rw [Set.uIcc_of_le haβ]; exact hwc)
  have hint : ∫ s in a..β, (thetaF vX X s - thetaF vY Y s) * w' s =
      (∫ s in a..β, thetaF vX X s * w' s) - ∫ s in a..β, thetaF vY Y s * w' s := by
    rw [← intervalIntegral.integral_sub (hmono X hX) (hmonoY Y hY)]
    congr 1; funext s; ring
  rw [hA, hB, hint]
  ring

/-- **One replacement** in the symmetric telescoping (Step 3 of the proof of Lemma 7.3(b)). -/
theorem one_replacement {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι)
    (Y : Finset κ') {X0 : ℝ} (hX0 : Real.exp 1 ≤ X0)
    {κ u m a β B : ℝ} (hκ : 0 < κ) (_hκ1 : κ ≤ 1) (hm : 0 < m) (hu : 0 < u)
    (ha : Real.exp 1 ≤ a) (haβ : a ≤ β) (hβ : β ≤ u / (X0 * m)) (hB : 0 ≤ B)
    (hXa : ∀ x ∈ X, a < vX x) (hYa : ∀ y ∈ Y, a < vY y)
    (hΔ : ∀ s ∈ Set.Icc a β, |thetaF vX X s - thetaF vY Y s| ≤ B * s * (Real.log s + 1) ^ 2) :
    |∑ x ∈ X.filter (fun x => vX x ≤ β), f0s κ (u / (m * vX x)) / (m * vX x) -
        ∑ y ∈ Y.filter (fun y => vY y ≤ β), f0s κ (u / (m * vY y)) / (m * vY y)| ≤
      12 * B * Real.log β ^ 2 / (Real.log X0 * m) := by
  have he := Real.add_one_le_exp (1 : ℝ)
  have ha0 : 0 < a := by linarith
  have hX00 : 0 < X0 := by linarith
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  have hΛ0 : 0 < Real.log X0 := by linarith
  -- on `[a, β]`: `log s ≥ 1`, `q = u/(m s) ≥ X₀`
  have hs1 : ∀ s ∈ Set.Icc a β, 0 < s ∧ 1 ≤ Real.log s ∧ X0 ≤ u / (m * s) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    refine ⟨hs0, ?_, ?_⟩
    · rw [Real.le_log_iff_exp_le hs0]; linarith [hs.1]
    · rw [le_div_iff₀ (by positivity)]
      have := hs.2.trans hβ
      rw [le_div_iff₀ (by positivity)] at this; linarith
  set w : ℝ → ℝ := fun s => f0s κ (u / (m * s)) * (1 / (m * s * Real.log s)) with hw
  set w' : ℝ → ℝ := fun s =>
    f0s' κ (u / (m * s)) * (-(u / (m * s ^ 2))) * (1 / (m * s * Real.log s))
    + f0s κ (u / (m * s)) * (-(m * (Real.log s + 1)) / (m * s * Real.log s) ^ 2) with hw'
  have hq1 : ∀ s ∈ Set.Icc a β, 1 < u / (m * s) := fun s hs => by
    have := (hs1 s hs).2.2; linarith
  have hder : ∀ s ∈ Set.Icc a β, HasDerivAt w (w' s) s := by
    intro s hs
    obtain ⟨hs0, hls, -⟩ := hs1 s hs
    have hne : m * s ≠ 0 := by positivity
    have hqd : HasDerivAt (fun s => u / (m * s)) (-(u / (m * s ^ 2))) s := by
      have h := (((hasDerivAt_id' s).const_mul m).inv hne).const_mul u
      simp only [Pi.inv_apply] at h
      have e : (fun x => u * (m * x)⁻¹) = fun s => u / (m * s) := by
        funext t; rw [div_eq_mul_inv]
      rw [e] at h
      refine h.congr_deriv ?_
      field_simp
    have hf := (hasDerivAt_f0s hκ (hq1 s hs)).comp s hqd
    have hl : HasDerivAt (fun s => m * s * Real.log s) (m * (Real.log s + 1)) s := by
      have h := ((hasDerivAt_id' s).const_mul m).mul (Real.hasDerivAt_log hs0.ne')
      refine h.congr_deriv ?_
      field_simp
    have hne2 : m * s * Real.log s ≠ 0 := by
      have : 0 < Real.log s := by linarith
      positivity
    have hinv : HasDerivAt (fun y => 1 / (m * y * Real.log y))
        (-(m * (Real.log s + 1)) / (m * s * Real.log s) ^ 2) s := by
      have e : (fun y => 1 / (m * y * Real.log y)) = fun y => (m * y * Real.log y)⁻¹ := by
        funext y; rw [one_div]
      rw [e]; exact hl.inv hne2
    exact hf.mul hinv
  have hcont : ContinuousOn w' (Set.Icc a β) := by
    intro s hs
    obtain ⟨hs0, hls, -⟩ := hs1 s hs
    have hls0 : 0 < Real.log s := by linarith
    apply ContinuousAt.continuousWithinAt
    have hq := hq1 s hs
    have hqc : ContinuousAt (fun s => u / (m * s)) s :=
      continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
    have hlog : ContinuousAt Real.log s := Real.continuousAt_log hs0.ne'
    have hG : ∀ y, 1 < y → ContinuousAt Gli y := fun y hy => (hasDerivAt_Gli hy).continuousAt
    have hf0 : ContinuousAt (fun s => f0s κ (u / (m * s))) s :=
      ContinuousAt.comp (f := fun s => u / (m * s)) (hasDerivAt_f0s hκ hq).continuousAt hqc
    have hf0' : ContinuousAt (fun s => f0s' κ (u / (m * s))) s := by
      have hq' : 1 < (1 + κ) * (u / (m * s)) := by nlinarith
      unfold f0s'
      apply ContinuousAt.div _ _ (by positivity)
      · apply ContinuousAt.sub
        · apply ContinuousAt.mul _ (continuousAt_const.mul hqc)
          apply ContinuousAt.sub
          · exact continuousAt_const.div (ContinuousAt.comp (f := fun s => (1 + κ) * (u / (m * s)))
              (Real.continuousAt_log (by positivity)) (continuousAt_const.mul hqc))
              (Real.log_pos hq').ne'
          · exact continuousAt_const.div (ContinuousAt.comp (f := fun s => u / (m * s))
              (Real.continuousAt_log (by positivity)) hqc) (Real.log_pos hq).ne'
        · exact ((ContinuousAt.comp (f := fun s => (1 + κ) * (u / (m * s))) (hG _ hq')
            (continuousAt_const.mul hqc)).sub
            (ContinuousAt.comp (f := fun s => u / (m * s)) (hG _ hq) hqc)).mul continuousAt_const
      · exact (continuousAt_const.mul hqc).pow 2
    simp only [hw']
    apply ContinuousAt.add
    · apply ContinuousAt.mul (hf0'.mul (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.pow 2)) (show m * s ^ 2 ≠ 0 by positivity)).neg)
      exact continuousAt_const.div ((continuousAt_const.mul continuousAt_id).mul hlog)
        (by have : 0 < Real.log s := by linarith
            positivity)
    · apply hf0.mul
      apply ContinuousAt.div (continuousAt_const.mul (hlog.add continuousAt_const)).neg
        (((continuousAt_const.mul continuousAt_id).mul hlog).pow 2)
      exact (show (m * s * Real.log s) ^ 2 ≠ 0 by positivity)
  -- the sums as Abel sums
  have hsum : ∀ (Z : Finset ι), (∀ z ∈ Z, a < vX z) →
      ∑ z ∈ Z.filter (fun z => vX z ≤ β), f0s κ (u / (m * vX z)) / (m * vX z) =
        ∑ z ∈ Z.filter (fun z => vX z ≤ β), Real.log (vX z) * w (vX z) := by
    intro Z hZ
    refine Finset.sum_congr rfl fun z hz => ?_
    have hza := hZ z (Finset.mem_filter.mp hz).1
    have hz0 : 0 < vX z := by linarith
    have hlz : 0 < Real.log (vX z) := Real.log_pos (by linarith)
    simp only [hw]
    field_simp
  have hsum' : ∀ (Z : Finset κ'), (∀ z ∈ Z, a < vY z) →
      ∑ z ∈ Z.filter (fun z => vY z ≤ β), f0s κ (u / (m * vY z)) / (m * vY z) =
        ∑ z ∈ Z.filter (fun z => vY z ≤ β), Real.log (vY z) * w (vY z) := by
    intro Z hZ
    refine Finset.sum_congr rfl fun z hz => ?_
    have hza := hZ z (Finset.mem_filter.mp hz).1
    have hz0 : 0 < vY z := by linarith
    have hlz : 0 < Real.log (vY z) := Real.log_pos (by linarith)
    simp only [hw]
    field_simp
  rw [hsum X hXa, hsum' Y hYa, abel_diff vX vY X Y (by linarith) haβ hXa hYa w w' hder hcont]
  -- the bounds on `w` and `w'`
  have hwb : ∀ s ∈ Set.Icc a β, |w s| ≤ 1 / (Real.log X0 * m * s * Real.log s) := by
    intro s hs
    obtain ⟨hs0, hls, hqX⟩ := hs1 s hs
    obtain ⟨h0, h1, -⟩ := f0s_bounds hκ (hX0.trans hqX) (q := u / (m * s))
    have hlq : Real.log X0 ≤ Real.log (u / (m * s)) := Real.log_le_log hX00 hqX
    simp only [hw]
    rw [abs_mul, abs_of_nonneg h0, abs_of_pos (by positivity)]
    have : f0s κ (u / (m * s)) ≤ 1 / Real.log X0 :=
      h1.trans (one_div_le_one_div_of_le hΛ0 hlq)
    calc f0s κ (u / (m * s)) * (1 / (m * s * Real.log s)) ≤
          1 / Real.log X0 * (1 / (m * s * Real.log s)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 / (Real.log X0 * m * s * Real.log s) := by field_simp
  have hw'b : ∀ s ∈ Set.Icc a β, |w' s| ≤ 4 / (Real.log X0 * m * s ^ 2 * Real.log s) := by
    intro s hs
    obtain ⟨hs0, hls, hqX⟩ := hs1 s hs
    set q := u / (m * s) with hqdef
    obtain ⟨h0, h1, h2⟩ := f0s_bounds hκ (hX0.trans hqX) (q := q)
    have hlq : Real.log X0 ≤ Real.log q := Real.log_le_log hX00 hqX
    have hf1 : f0s κ q ≤ 1 / Real.log X0 := h1.trans (one_div_le_one_div_of_le hΛ0 hlq)
    have hf2 : |q * f0s' κ q| ≤ 2 / Real.log X0 :=
      h2.trans (div_le_div_of_nonneg_left (by norm_num) hΛ0 hlq)
    have e1 : f0s' κ q * (-(u / (m * s ^ 2))) * (1 / (m * s * Real.log s)) =
        -(q * f0s' κ q) * (1 / (m * s ^ 2 * Real.log s)) := by
      rw [hqdef]; field_simp
    have e2 : f0s κ q * (-(m * (Real.log s + 1)) / (m * s * Real.log s) ^ 2) =
        -(f0s κ q) * ((Real.log s + 1) / (m * s ^ 2 * Real.log s ^ 2)) := by
      field_simp
    have hls0 : 0 < Real.log s := by linarith
    simp only [hw']
    rw [← hqdef, e1, e2]
    have hA : |-(q * f0s' κ q) * (1 / (m * s ^ 2 * Real.log s))| ≤
        2 / (Real.log X0 * m * s ^ 2 * Real.log s) := by
      rw [abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 1 / (m * s ^ 2 * Real.log s) by positivity)]
      calc |q * f0s' κ q| * (1 / (m * s ^ 2 * Real.log s)) ≤
            2 / Real.log X0 * (1 / (m * s ^ 2 * Real.log s)) :=
            mul_le_mul_of_nonneg_right hf2 (by positivity)
        _ = 2 / (Real.log X0 * m * s ^ 2 * Real.log s) := by field_simp
    have hB' : |-(f0s κ q) * ((Real.log s + 1) / (m * s ^ 2 * Real.log s ^ 2))| ≤
        2 / (Real.log X0 * m * s ^ 2 * Real.log s) := by
      rw [abs_mul, abs_neg, abs_of_nonneg h0,
        abs_of_pos (show (0 : ℝ) < (Real.log s + 1) / (m * s ^ 2 * Real.log s ^ 2) by positivity)]
      have hl2 :
          (Real.log s + 1) / (m * s ^ 2 * Real.log s ^ 2) ≤ 2 / (m * s ^ 2 * Real.log s) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hK : 0 < m * s ^ 2 * Real.log s := by positivity
        have h1 : (Real.log s + 1) * (m * s ^ 2 * Real.log s) ≤
            (2 * Real.log s) * (m * s ^ 2 * Real.log s) :=
          mul_le_mul_of_nonneg_right (by linarith) hK.le
        have e :
            2 * (m * s ^ 2 * Real.log s ^ 2) = (2 * Real.log s) * (m * s ^ 2 * Real.log s) := by
          ring
        rw [e]; exact h1
      calc f0s κ q * ((Real.log s + 1) / (m * s ^ 2 * Real.log s ^ 2)) ≤
            1 / Real.log X0 * (2 / (m * s ^ 2 * Real.log s)) :=
            mul_le_mul hf1 hl2 (by positivity) (by positivity)
        _ = 2 / (Real.log X0 * m * s ^ 2 * Real.log s) := by field_simp
    calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ 2 / (Real.log X0 * m * s ^ 2 * Real.log s) + 2 / (Real.log X0 * m * s ^ 2 * Real.log s) :=
          add_le_add hA hB'
      _ = 4 / (Real.log X0 * m * s ^ 2 * Real.log s) := by ring
  obtain ⟨hβ0, hlβ, -⟩ := hs1 β ⟨haβ, le_rfl⟩
  -- the boundary term
  have hbd : |(thetaF vX X β - thetaF vY Y β) * w β| ≤ 4 * B * Real.log β / (Real.log X0 * m) := by
    rw [abs_mul]
    have h1 := hΔ β ⟨haβ, le_rfl⟩
    have h2 := hwb β ⟨haβ, le_rfl⟩
    calc |thetaF vX X β - thetaF vY Y β| * |w β| ≤
          (B * β * (Real.log β + 1) ^ 2) * (1 / (Real.log X0 * m * β * Real.log β)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = B * (Real.log β + 1) ^ 2 / (Real.log β * (Real.log X0 * m)) := by field_simp
      _ ≤ 4 * B * Real.log β / (Real.log X0 * m) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : (Real.log β + 1) ^ 2 ≤ 4 * Real.log β ^ 2 := by nlinarith
          have hBm : 0 ≤ B * (Real.log X0 * m) := by positivity
          nlinarith
  -- the integral
  have hint : |∫ s in a..β, (thetaF vX X s - thetaF vY Y s) * w' s| ≤
      8 * B * Real.log β ^ 2 / (Real.log X0 * m) := by
    have hg : ∀ s ∈ Set.Icc a β, |(thetaF vX X s - thetaF vY Y s) * w' s| ≤
        16 * B / (Real.log X0 * m) * (Real.log s / s) := by
      intro s hs
      obtain ⟨hs0, hls, -⟩ := hs1 s hs
      rw [abs_mul]
      calc |thetaF vX X s - thetaF vY Y s| * |w' s| ≤
            (B * s * (Real.log s + 1) ^ 2) * (4 / (Real.log X0 * m * s ^ 2 * Real.log s)) :=
            mul_le_mul (hΔ s hs) (hw'b s hs) (abs_nonneg _) (by positivity)
        _ = 4 * B / (Real.log X0 * m) * ((Real.log s + 1) ^ 2 / (s * Real.log s)) := by
            field_simp
        _ ≤ 4 * B / (Real.log X0 * m) * (4 * (Real.log s / s)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ (by positivity)]
            have : (Real.log s + 1) ^ 2 ≤ 4 * Real.log s ^ 2 := by nlinarith
            have e : 4 * (Real.log s / s) * (s * Real.log s) = 4 * Real.log s ^ 2 := by
              field_simp
            rw [e]; exact this
        _ = 16 * B / (Real.log X0 * m) * (Real.log s / s) := by ring
    have hlc : ContinuousOn (fun s => Real.log s / s) (Set.Icc a β) := by
      apply ContinuousOn.div (Real.continuousOn_log.mono fun s hs => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hs.1]) continuousOn_id
      intro s hs; exact (show (0 : ℝ) < s by linarith [hs.1]).ne'
    have hFTC : ∫ s in a..β, Real.log s / s = Real.log β ^ 2 / 2 - Real.log a ^ 2 / 2 := by
      apply integral_eq_sub_of_hasDerivAt
      · intro s hs
        rw [Set.uIcc_of_le haβ] at hs
        have hs0 : 0 < s := by linarith [hs.1]
        have := ((Real.hasDerivAt_log hs0.ne').pow 2).div_const 2
        convert this using 1
        field_simp
        push_cast
        ring
      · exact (hlc.mono (by rw [Set.uIcc_of_le haβ])).intervalIntegrable
    have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    refine (intervalIntegral.abs_integral_le_integral_abs haβ).trans ?_
    calc ∫ s in a..β, |(thetaF vX X s - thetaF vY Y s) * w' s| ≤
          ∫ s in a..β, 16 * B / (Real.log X0 * m) * (Real.log s / s) := by
          apply intervalIntegral.integral_mono_on haβ
          · -- integrability of the absolute value
            have hmono : ∀ (Z : Finset ι), (∀ z ∈ Z, a < vX z) →
                IntervalIntegrable (fun s => thetaF vX Z s * w' s) volume a β := by
              intro Z h1
              have hm : Monotone (thetaF vX Z) := by
                intro s1 s2 hs
                unfold thetaF
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hs⟩
                · intro z hz _
                  exact Real.log_nonneg (by linarith [h1 z (Finset.mem_filter.mp hz).1])
              exact hm.intervalIntegrable.mul_continuousOn (by rw [Set.uIcc_of_le haβ]; exact hcont)
            have hmonoY : ∀ (Z : Finset κ'), (∀ z ∈ Z, a < vY z) →
                IntervalIntegrable (fun s => thetaF vY Z s * w' s) volume a β := by
              intro Z h1
              have hm : Monotone (thetaF vY Z) := by
                intro s1 s2 hs
                unfold thetaF
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hs⟩
                · intro z hz _
                  exact Real.log_nonneg (by linarith [h1 z (Finset.mem_filter.mp hz).1])
              exact hm.intervalIntegrable.mul_continuousOn (by rw [Set.uIcc_of_le haβ]; exact hcont)
            have := (hmono X hXa).sub (hmonoY Y hYa)
            refine (this.congr (fun s _ => by ring)).abs
          · exact (hlc.mono (by rw [Set.uIcc_of_le haβ])).intervalIntegrable.const_mul _
          · exact hg
      _ = 16 * B / (Real.log X0 * m) * (Real.log β ^ 2 / 2 - Real.log a ^ 2 / 2) := by
          rw [intervalIntegral.integral_const_mul, hFTC]
      _ ≤ 8 * B * Real.log β ^ 2 / (Real.log X0 * m) := by
          have : 0 ≤ 16 * B / (Real.log X0 * m) := by positivity
          have : 16 * B / (Real.log X0 * m) * (Real.log β ^ 2 / 2 - Real.log a ^ 2 / 2) ≤
              16 * B / (Real.log X0 * m) * (Real.log β ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith) this
          refine this.trans (le_of_eq ?_)
          ring
  calc |(thetaF vX X β - thetaF vY Y β) * w β - ∫ s in a..β, (thetaF vX X s - thetaF vY Y s) * w' s|
      ≤ |(thetaF vX X β - thetaF vY Y β) * w β| +
        |∫ s in a..β, (thetaF vX X s - thetaF vY Y s) * w' s| := abs_sub _ _
    _ ≤ 4 * B * Real.log β / (Real.log X0 * m) + 8 * B * Real.log β ^ 2 / (Real.log X0 * m) :=
        add_le_add hbd hint
    _ ≤ 12 * B * Real.log β ^ 2 / (Real.log X0 * m) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : B * Real.log β ≤ B * Real.log β ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) hB
        linarith

end BaseRange
