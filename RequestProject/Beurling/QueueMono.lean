module

public import RequestProject.Beurling.QueueBound75
public import RequestProject.BSCert.CaplMono

/-!
# `M̄₁` and the queue bound `B` are non-decreasing; the bound frozen per dyadic scale

Theorem 6.23(c): `M̄₁(x)` is non-decreasing in the height `x`. Consequently the explicit queue
bound `B(x)` of (75) (`queueB`) is non-decreasing on `[X₀, ∞)`.

Theorem 6.6 and Definition 6.8 use the bound **frozen per dyadic scale**:
`B(s) := B(u)` for `s ∈ [u, 2u)`, `u = 2^m X₀`. Here

* `dyadicScale X₀ s = X₀ · 2^⌊log₂(s/X₀)⌋`, so that `dyadicScale X₀ s ∈ (s/2, s]` for `s ≥ X₀`;
* `queueBScale X₀ s = queueB X₀ (dyadicScale X₀ (max X₀ s))`, the frozen bound (for `s ≥ X₀` it
  is `B(u)` with `u` the dyadic scale of `s`);
* `queueBScale_monotone` : the frozen bound is non-decreasing ("`B` is non-decreasing across
  scales, because `M₁` and `H` are non-decreasing in `x`");
* `queueBScale_le` : for `s ≤ x`, `x ≥ X₀`, `B(s) ≤ B(x)` — the step
  `max_{s_j ≤ x} Q_j ≤ max_{s_j ≤ x} B(s_j) ≤ B(x)` of Remark 6.9(ii).
-/

@[expose] public section

open Real CaplLink QueueBound BSCert.Capl

namespace QueueMono

lemma sHroot_le_six : sHroot ≤ 6 := by linarith [sHroot_mem.2]

lemma gstar_sHroot_le : gstar sHroot ≤ 7.5 := by
  rw [gstar_sHroot]; unfold gTarget; norm_num

lemma one_lt_of_logX {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) : 1 < X₀ := by
  by_contra h; push_neg at h
  rcases hX0.lt_or_eq with h' | h'
  · have := Real.log_nonpos hX0 h; linarith
  · rw [← h', Real.log_zero] at hX; norm_num at hX

/-- **Theorem 6.23(c): `M̄₁` is non-decreasing in the height** on `[X₀, ∞)`, `log X₀ ≥ 10⁸`. -/
theorem capM1_mono {X₀ x y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxy : x ≤ y) : capM1 X₀ x ≤ capM1 X₀ y := by
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  have hll : 1 ≤ 2 * Real.log (Real.log X₀) + capS X₀ x := by
    rw [ell_eq]
    have := log_ge_18 (Λ := Real.log x) (by linarith)
    linarith
  have hS : capS X₀ x ≤ capS X₀ y := by
    unfold capS
    have hlx : 0 < Real.log x := by linarith
    have := Real.log_le_log hlx (Real.log_le_log (by linarith) hxy)
    linarith
  exact Mbar1_mono sHroot_le_six gstar_sHroot_le (by linarith) hll hS

/-- The queue bound (75) is non-decreasing in `M₁` and `L` (for `M₁, L ≥ 0`, `Λ > 0`). -/
lemma queueBound75_mono {M1 M1' L L' Λ : ℝ} (hM : 0 ≤ M1) (hMM : M1 ≤ M1') (hL : 0 ≤ L)
    (hLL : L ≤ L') (hΛ : 0 < Λ) :
    queueBound75 M1 L Λ 0.15 3 ≤ queueBound75 M1' L' Λ 0.15 3 := by
  unfold queueBound75
  have hM' : 0 ≤ M1' := hM.trans hMM
  have hL' : 0 ≤ L' := hL.trans hLL
  have hML : M1 * L ≤ M1' * L' := mul_le_mul hMM hLL hL hM'
  have hML2 : M1 * L ^ 2 ≤ M1' * L' ^ 2 :=
    mul_le_mul hMM (pow_le_pow_left₀ hL hLL 2) (by positivity) hM'
  have hsq : Real.sqrt (M1 * L * (3 + 4)) ≤ Real.sqrt (M1' * L' * (3 + 4)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hd : L / Λ + 1 ≤ L' / Λ + 1 := by
    have := div_le_div_of_nonneg_right hLL hΛ.le; linarith
  have h4 : 8 * M1 * L * (L / Λ + 1) ≤ 8 * M1' * L' * (L' / Λ + 1) := by
    have : 0 ≤ L / Λ + 1 := by positivity
    have : 0 ≤ M1 * L := by positivity
    nlinarith
  have : 4 * M1 * L ^ 2 / 0.15 ≤ 4 * M1' * L' ^ 2 / 0.15 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  have h2 : 16 * M1 * L / 3 ≤ 16 * M1' * L' / 3 := by nlinarith
  have h5 := add_le_add (add_le_add (add_le_add this h2)
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 4))) h4
  exact add_le_add (add_le_add h5 le_rfl) le_rfl

/-- **The queue bound `B(x)` of (75) is non-decreasing** on `[X₀, ∞)`. -/
theorem queueB_mono {X₀ x y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxy : x ≤ y) : queueB X₀ x ≤ queueB X₀ y := by
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  have hx0 : 0 < x := by linarith
  have hLx : 0 ≤ Real.log x := by linarith
  have hLy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  unfold queueB
  apply queueBound75_mono (le_of_lt (capM1_pos hX0 hX hx)) (capM1_mono hX0 hX hx hxy)
    (Real.log_nonneg (by linarith)) _ (by linarith)
  exact Real.log_le_log (by linarith) (by linarith)

lemma queueB_nonneg {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    0 ≤ queueB X₀ x := by
  obtain ⟨h1, -, -⟩ := logs_of_ge hX0 hX hx
  have hX1 := one_lt_of_logX hX0 hX
  have hM := (capM1_pos hX0 hX hx).le
  have hL : 0 ≤ Real.log (2 * x + 12 * Real.log x + 2) := Real.log_nonneg (by linarith)
  unfold queueB queueBound75
  have : 0 ≤ Real.log X₀ := by linarith
  positivity

/-- The dyadic scale `X₀ · 2^⌊log₂(s/X₀)⌋` of a height `s` (Definition 6.8). -/
noncomputable def dyadicScale (X₀ s : ℝ) : ℝ := X₀ * (2 : ℝ) ^ Int.log 2 (s / X₀)

lemma dyadicScale_le {X₀ s : ℝ} (hX0 : 0 < X₀) (hs : 0 < s) : dyadicScale X₀ s ≤ s := by
  unfold dyadicScale
  have := Int.zpow_log_le_self (b := 2) (by norm_num) (div_pos hs hX0)
  push_cast at this
  rw [le_div_iff₀ hX0] at this
  linarith

lemma lt_two_mul_dyadicScale {X₀ s : ℝ} (hX0 : 0 < X₀) : s < 2 * dyadicScale X₀ s := by
  unfold dyadicScale
  have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (s / X₀)
  push_cast at this
  rw [zpow_add_one₀ (by norm_num), div_lt_iff₀ hX0] at this
  linarith

lemma le_dyadicScale {X₀ s : ℝ} (hX0 : 0 < X₀) (hs : X₀ ≤ s) : X₀ ≤ dyadicScale X₀ s := by
  unfold dyadicScale
  have h1 : (1 : ℝ) ≤ s / X₀ := by rw [le_div_iff₀ hX0]; linarith
  have h0 : 0 ≤ Int.log 2 (s / X₀) := by rw [Int.log_of_one_le_right _ h1]; positivity
  have : (1 : ℝ) ≤ (2 : ℝ) ^ Int.log 2 (s / X₀) := one_le_zpow₀ (by norm_num) h0
  nlinarith

lemma dyadicScale_mono {X₀ s t : ℝ} (hX0 : 0 < X₀) (hs : 0 < s) (hst : s ≤ t) :
    dyadicScale X₀ s ≤ dyadicScale X₀ t := by
  unfold dyadicScale
  have := Int.log_mono_right (b := 2) (div_pos hs hX0)
    (div_le_div_of_nonneg_right hst hX0.le)
  have : (2 : ℝ) ^ Int.log 2 (s / X₀) ≤ (2 : ℝ) ^ Int.log 2 (t / X₀) :=
    zpow_le_zpow_right₀ (by norm_num) this
  exact mul_le_mul_of_nonneg_left this hX0.le

/-- **The queue bound frozen per dyadic scale** (Definition 6.8): `B(s) := B(u)` for
`s ∈ [u, 2u)`, `u = 2^m X₀` (heights below `X₀` are assigned the first scale `X₀`). -/
noncomputable def queueBScale (X₀ s : ℝ) : ℝ := queueB X₀ (dyadicScale X₀ (max X₀ s))

/-- For `s ≥ X₀`, the frozen bound is `B(u)` at the dyadic scale `u ∈ (s/2, s]` of `s`. -/
lemma queueBScale_eq {X₀ s : ℝ} (hs : X₀ ≤ s) :
    queueBScale X₀ s = queueB X₀ (dyadicScale X₀ s) := by
  unfold queueBScale; rw [max_eq_right hs]

/-- **`B` is non-decreasing across scales** (proof of Theorem 6.6(ii), via Theorem 6.23(c)). -/
theorem queueBScale_monotone {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    Monotone (queueBScale X₀) := by
  intro s t hst
  have hX1 := one_lt_of_logX hX0 hX
  unfold queueBScale
  have hm : max X₀ s ≤ max X₀ t := max_le_max le_rfl hst
  have hpos : 0 < max X₀ s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  exact queueB_mono hX0 hX (le_dyadicScale (by linarith) (le_max_left _ _))
    (dyadicScale_mono (by linarith) hpos hm)

/-- **Remark 6.9(ii)**: for a slot start `s ≤ x` with `x ≥ X₀`, the frozen bound satisfies
`B(s) ≤ B(x)`. -/
theorem queueBScale_le {X₀ s x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hsx : s ≤ x) : queueBScale X₀ s ≤ queueB X₀ x := by
  have hX1 := one_lt_of_logX hX0 hX
  unfold queueBScale
  have hpos : 0 < max X₀ s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  exact queueB_mono hX0 hX (le_dyadicScale (by linarith) (le_max_left _ _))
    ((dyadicScale_le (by linarith) hpos).trans (max_le hx hsx))

end QueueMono

end
