module

public import RequestProject.Beurling.Lemmas

/-!
# The oscillations `R` of the target (Section 3.2, (1)) and `|R(x)| ≤ 2 x^θ log* x`

With `ϕ` the smooth step (`Real.smoothTransition`), the switch-on points `x⁺_k`, amplitudes
`α_k` and frequencies `γ_k`, the paper puts

  `R_k(x) := α_k x^θ cos(γ_k log x) ϕ(log(x / x⁺_k))`,   `R := ∑_k R_k`.

* `oscTerm_eq_zero_of_le` : `R_k ≡ 0` on `(0, x⁺_k]`;
* `card_switched_on_le_logStar` : with spacing `x⁺_{k+1} ≥ exp(x⁺_k)` and `x⁺_0 ≥ 1`, the number of
  `k` with `x⁺_k < x` is at most `log* x`;
* `abs_osc_le` : the oscillation bound of Lemma 3.4, `|R(x)| ≤ 2 x^θ log* x` (for `|α_k| ≤ 2`).
-/

@[expose] public section

open Filter Topology Finset

namespace Oscillation

/-- One oscillation `R_k(x) = α x^θ cos(γ log x) ϕ(log(x / x⁺))` of (1). -/
noncomputable def oscTerm (θ α γ xp x : ℝ) : ℝ :=
  α * x ^ θ * Real.cos (γ * Real.log x) * Real.smoothTransition (Real.log (x / xp))

/-- The oscillation `R(x) = ∑_k R_k(x)` of (1). -/
noncomputable def osc (θ : ℝ) (α γ xp : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k, oscTerm θ (α k) (γ k) (xp k) x

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
    osc θ α γ xp x = ∑ k ∈ range (logStar x), oscTerm θ (α k) (γ k) (xp k) x := by
  unfold osc
  apply tsum_eq_sum
  intro k hk
  rw [mem_range, not_lt] at hk
  apply oscTerm_eq_zero_of_le (by linarith)
  by_contra hlt
  push_neg at hlt
  have := le_logStar_of_lt h hlt
  omega

/-- **The oscillation bound of Lemma 3.4**: `|R(x)| ≤ 2 x^θ log* x` for `x ≥ 1`. -/
theorem abs_osc_le {θ : ℝ} {α γ xp : ℕ → ℝ} (h : Spacing xp) (hα : ∀ k, |α k| ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    |osc θ α γ xp x| ≤ 2 * x ^ θ * (logStar x : ℝ) := by
  rw [osc_eq_sum h hx]
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) θ
  have hterm : ∀ k, |oscTerm θ (α k) (γ k) (xp k) x| ≤ 2 * x ^ θ := by
    intro k
    unfold oscTerm
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hxθ,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have h1 := Real.abs_cos_le_one (γ k * Real.log x)
    have h2 := Real.smoothTransition.le_one (Real.log (x / xp k))
    have h3 := Real.smoothTransition.nonneg (Real.log (x / xp k))
    have h4 := hα k
    calc |α k| * x ^ θ * |Real.cos (γ k * Real.log x)| *
          Real.smoothTransition (Real.log (x / xp k))
        ≤ 2 * x ^ θ * 1 * 1 := by gcongr
      _ = 2 * x ^ θ := by ring
  calc |∑ k ∈ range (logStar x), oscTerm θ (α k) (γ k) (xp k) x|
      ≤ ∑ k ∈ range (logStar x), |oscTerm θ (α k) (γ k) (xp k) x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range (logStar x), 2 * x ^ θ := sum_le_sum fun k _ => hterm k
    _ = 2 * x ^ θ * (logStar x : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

end Oscillation

end
