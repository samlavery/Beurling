module

public import RequestProject.Beurling.Lemmas

/-!
# The oscillations `R` of the target (Section 3.2, (1)) and `|R(x)| ≤ 2 x^θ log* x`

With `ϕ` the smooth step (`Real.smoothTransition`), the switch-on points `x⁺_k`, amplitudes
`α_k` and frequencies `γ_k`, the paper puts

  `R_k(x) := α_k x^θ cos(γ_k log x) ϕ(log(x / x⁺_k))`,   `R := ∑_k R_k`.

* `oscTerm_eq_zero_of_le` : `R_k ≡ 0` on `(0, x⁺_k]`;
* the **design index** `θ ∈ [0, 1/2 - 10⁻⁴]`: for `θ ≠ 0` the oscillations are the `oscTerm θ` of
  Theorem A; for `θ = 0` (Theorem A′, §8) the `k`-th oscillation has the per-zero exponent
  `thK 0 x⁺_k = 9 ℓ_k²/L_k` (`L_k = log x⁺_k`, `ℓ_k = log L_k`) and is switched off at `(x⁺_k)²`
  (`oscTermS`, `oscK`); `osc θ` sums the `oscK θ`;
* `card_switched_on_le_logStar` : with spacing `x⁺_{k+1} ≥ exp(x⁺_k)` and `x⁺_0 ≥ 1`, the number of
  `k` with `x⁺_k < x` is at most `log* x`;
* `abs_osc_le_of` : the oscillation bound of Lemma 3.4, `|R(x)| ≤ 2 x^t log* x` when every
  per-zero exponent is `≤ t` (for `|α_k| ≤ 2`); `abs_osc_le` is the case `t = θ ≠ 0`.
-/

@[expose] public section

open Filter Topology Finset

namespace Oscillation

/-- One oscillation `R_k(x) = α x^θ cos(γ log x) ϕ(log(x / x⁺))` of (1). -/
noncomputable def oscTerm (θ α γ xp x : ℝ) : ℝ :=
  α * x ^ θ * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xp))

/-- An oscillation switched on at `x⁺` and **switched off at `y = (x⁺)²`** (eq. (Rkflat) of §8),
written as the difference of the oscillations switched on at `x⁺` and at `y`:
`α x^t cos(γ log x) (ϕ(log(x/x⁺)) - ϕ(log(x/(x⁺)²)))` for `x⁺ ≥ 1`. The switch-off point is
written `x⁺ max(x⁺, 1)`, so that the term vanishes identically for `x⁺ < 1`. -/
noncomputable def oscTermS (t α γ xp x : ℝ) : ℝ :=
  oscTerm t α γ xp x - oscTerm t α γ (xp * max xp 1) x

lemma offPt_eq {xp : ℝ} (h : 1 ≤ xp) : xp * max xp 1 = xp ^ 2 := by
  rw [max_eq_left h]; ring

lemma oscTermS_eq {t α γ xp x : ℝ} (h : 1 ≤ xp) : oscTermS t α γ xp x =
    α * x ^ t * Real.cos (γ * Real.log x) *
      (Real.smoothTransition (Real.log (x / xp)) -
        Real.smoothTransition (Real.log (x / xp ^ 2))) := by
  unfold oscTermS oscTerm; rw [offPt_eq h]; ring

/-- The `k`-th oscillation of the design `θ`: `oscTerm θ` for `θ ≠ 0`, and the switched-off
oscillation with the per-zero exponent `thK 0 x⁺` for `θ = 0`. -/
noncomputable def oscK (θ α γ xp x : ℝ) : ℝ :=
  if θ = 0 then oscTermS (thK 0 xp) α γ xp x else oscTerm θ α γ xp x

lemma oscK_of_ne {θ : ℝ} (hθ : θ ≠ 0) (α γ xp x : ℝ) : oscK θ α γ xp x = oscTerm θ α γ xp x := by
  simp [oscK, hθ]

lemma oscK_zero (α γ xp x : ℝ) : oscK 0 α γ xp x = oscTermS (thK 0 xp) α γ xp x := by
  simp [oscK]

/-- The oscillation `R(x) = ∑_k R_k(x)` of (1) (of (Rkflat) for the design `θ = 0`). -/
noncomputable def osc (θ : ℝ) (α γ xp : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k, oscK θ (α k) (γ k) (xp k) x

lemma osc_of_ne {θ : ℝ} (hθ : θ ≠ 0) (α γ xp : ℕ → ℝ) (x : ℝ) :
    osc θ α γ xp x = ∑' k, oscTerm θ (α k) (γ k) (xp k) x := by
  simp [osc, oscK_of_ne hθ]

/-- Standing assumptions on the switch-on points: `x⁺_0 ≥ 1` and `x⁺_{k+1} ≥ exp(x⁺_k)`. -/
structure Spacing (xp : ℕ → ℝ) : Prop where
  one_le : 1 ≤ xp 0
  exp_le : ∀ k, Real.exp (xp k) ≤ xp (k + 1)

lemma oscTerm_eq_zero_of_le {θ α γ xp x : ℝ} (hx : 0 < x) (hxp : x ≤ xp) :
    oscTerm θ α γ xp x = 0 := by
  have hxp0 : 0 < xp := lt_of_lt_of_le hx hxp
  have : Real.log (x / xp) ≤ 0 :=
    Real.log_nonpos (div_pos hx hxp0).le ((div_le_one hxp0).mpr hxp)
  simp [oscTerm, Real.smoothTransition.zero_of_nonpos this]

lemma oscTermS_eq_zero_of_le {t α γ xp x : ℝ} (hx : 0 < x) (hxp : x ≤ xp) :
    oscTermS t α γ xp x = 0 := by
  rcases le_or_gt 1 xp with hxp1 | hxp1
  · have hxp0 : 0 < xp := by linarith
    have h1 : Real.log (x / xp) ≤ 0 :=
      Real.log_nonpos (div_pos hx hxp0).le ((div_le_one hxp0).mpr hxp)
    have h2 : Real.log (x / xp ^ 2) ≤ 0 := by
      have : xp ≤ xp ^ 2 := by nlinarith
      exact Real.log_nonpos (div_pos hx (by positivity)).le
        ((div_le_one (by positivity)).mpr (hxp.trans this))
    simp [oscTermS_eq hxp1, Real.smoothTransition.zero_of_nonpos h1,
      Real.smoothTransition.zero_of_nonpos h2]
  · simp [oscTermS, max_eq_right hxp1.le]

lemma oscK_eq_zero_of_le {θ α γ xp x : ℝ} (hx : 0 < x) (hxp : x ≤ xp) :
    oscK θ α γ xp x = 0 := by
  unfold oscK
  split_ifs
  · exact oscTermS_eq_zero_of_le hx hxp
  · exact oscTerm_eq_zero_of_le hx hxp

lemma Spacing.strictMono {xp : ℕ → ℝ} (h : Spacing xp) : StrictMono xp :=
  strictMono_nat_of_lt_succ fun k =>
    lt_of_lt_of_le (by linarith [Real.add_one_le_exp (xp k)]) (h.exp_le k)

lemma Spacing.one_le_all {xp : ℕ → ℝ} (h : Spacing xp) (k : ℕ) : 1 ≤ xp k :=
  h.one_le.trans (h.strictMono.monotone (Nat.zero_le k))

lemma logStar_set_nonempty (x : ℝ) : {n : ℕ | Real.log^[n] x ≤ 1}.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have := iterate_log_gt_aux n x fun k _ => by
    by_contra hk
    push_neg at hk
    have : k ∈ {n : ℕ | Real.log^[n] x ≤ 1} := hk
    rw [h] at this
    exact this
  linarith

/-- If `x⁺_{m-1} < x` then `log^[j] x > 1` for all `j < m`, hence `m ≤ log* x`. -/
lemma le_logStar_of_lt {xp : ℕ → ℝ} (h : Spacing xp) {x : ℝ} {m : ℕ} (hm : xp m < x) :
    m + 1 ≤ logStar x := by
  have key : ∀ j ≤ m, xp (m - j) < Real.log^[j] x := by
    intro j
    induction j with
    | zero => intro _; simpa using hm
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := h.exp_le (m - (j + 1))
      rw [show m - (j + 1) + 1 = m - j by omega] at h2
      have h3 : 0 < xp (m - (j + 1)) := by linarith [h.one_le_all (m - (j + 1))]
      rw [Function.iterate_succ_apply']
      have h4 : xp (m - (j + 1)) < Real.log (Real.log^[j] x) := by
        rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (xp (m - (j + 1)))])]
        linarith
      exact h4
  by_contra hlt
  push_neg at hlt
  have hmem := Nat.sInf_mem (logStar_set_nonempty x)
  change Real.log^[logStar x] x ≤ 1 at hmem
  have := key (logStar x) (by omega)
  linarith [h.one_le_all (m - logStar x)]

/-- Only the terms with `x⁺_k < x` are nonzero, and there are at most `log* x` of them. -/
lemma osc_eq_sum {θ : ℝ} {α γ xp : ℕ → ℝ} (h : Spacing xp) {x : ℝ} (hx : 1 ≤ x) :
    osc θ α γ xp x = ∑ k ∈ range (logStar x), oscK θ (α k) (γ k) (xp k) x := by
  unfold osc
  apply tsum_eq_sum
  intro k hk
  rw [mem_range, not_lt] at hk
  apply oscK_eq_zero_of_le (by linarith)
  by_contra hlt
  push_neg at hlt
  have := le_logStar_of_lt h hlt
  omega

/-- The switch-off factor `ψ = ϕ(log(x/x⁺)) - ϕ(log(x/(x⁺)²))` lies in `[0, 1]` (for `x⁺ ≥ 1`). -/
lemma switch_mem {xp x : ℝ} (hxp : 1 ≤ xp) (hx : 0 < x) :
    0 ≤ Real.smoothTransition (Real.log (x / xp)) -
        Real.smoothTransition (Real.log (x / xp ^ 2)) ∧
      Real.smoothTransition (Real.log (x / xp)) -
        Real.smoothTransition (Real.log (x / xp ^ 2)) ≤ 1 := by
  have hxp0 : 0 < xp := by linarith
  have hle : Real.log (x / xp ^ 2) ≤ Real.log (x / xp) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left hx.le hxp0 (by nlinarith)
  have h1 := Real.smoothTransition.monotone hle
  have h2 := Real.smoothTransition.le_one (Real.log (x / xp))
  have h3 := Real.smoothTransition.nonneg (Real.log (x / xp ^ 2))
  constructor <;> linarith

/-- `|R_k(x)| ≤ |α_k| x^{θ_k}` for the oscillations of every design. -/
lemma abs_oscK_le {θ α γ xp x : ℝ} (hxp : 1 ≤ xp) (hx : 0 < x) :
    |oscK θ α γ xp x| ≤ |α| * x ^ thK θ xp := by
  have hxθ : ∀ t : ℝ, 0 ≤ x ^ t := fun t => Real.rpow_nonneg hx.le t
  unfold oscK
  split_ifs with hθ
  · subst hθ
    rw [oscTermS_eq hxp]
    obtain ⟨h0, h1⟩ := switch_mem hxp hx
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hxθ _), abs_of_nonneg h0]
    have hc := Real.abs_cos_le_one (γ * Real.log x)
    calc |α| * x ^ thK 0 xp * |Real.cos (γ * Real.log x)| * _
        ≤ |α| * x ^ thK 0 xp * 1 * 1 := by gcongr
      _ = _ := by ring
  · rw [thK_of_ne hθ]
    unfold oscTerm
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hxθ _),
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have h1 := Real.abs_cos_le_one (γ * Real.log x)
    have h2 := Real.smoothTransition.le_one (Real.log (x / xp))
    have h3 := Real.smoothTransition.nonneg (Real.log (x / xp))
    calc |α| * x ^ θ * |Real.cos (γ * Real.log x)| * Real.smoothTransition (Real.log (x / xp))
        ≤ |α| * x ^ θ * 1 * 1 := by gcongr
      _ = _ := by ring

/-- **The oscillation bound**: `|R(x)| ≤ 2 x^t log* x` for `x ≥ 1`, when every per-zero
exponent is `≤ t`. -/
theorem abs_osc_le_of {θ t : ℝ} {α γ xp : ℕ → ℝ} (h : Spacing xp) (hα : ∀ k, |α k| ≤ 2)
    (ht : ∀ k, thK θ (xp k) ≤ t) {x : ℝ} (hx : 1 ≤ x) :
    |osc θ α γ xp x| ≤ 2 * x ^ t * (logStar x : ℝ) := by
  rw [osc_eq_sum h hx]
  have hterm : ∀ k, |oscK θ (α k) (γ k) (xp k) x| ≤ 2 * x ^ t := by
    intro k
    refine (abs_oscK_le (h.one_le_all k) (by linarith)).trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hx (ht k)
    have := hα k
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) (thK θ (xp k))
    nlinarith
  calc |∑ k ∈ range (logStar x), oscK θ (α k) (γ k) (xp k) x|
      ≤ ∑ k ∈ range (logStar x), |oscK θ (α k) (γ k) (xp k) x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range (logStar x), 2 * x ^ t := sum_le_sum fun k _ => hterm k
    _ = 2 * x ^ t * (logStar x : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **The oscillation bound of Lemma 3.4**: `|R(x)| ≤ 2 x^θ log* x` for `x ≥ 1` (`θ ≠ 0`). -/
theorem abs_osc_le {θ : ℝ} (hθ : θ ≠ 0) {α γ xp : ℕ → ℝ} (h : Spacing xp)
    (hα : ∀ k, |α k| ≤ 2) {x : ℝ} (hx : 1 ≤ x) :
    |osc θ α γ xp x| ≤ 2 * x ^ θ * (logStar x : ℝ) :=
  abs_osc_le_of h hα (fun k => (thK_of_ne hθ _).le) hx

end Oscillation

end
