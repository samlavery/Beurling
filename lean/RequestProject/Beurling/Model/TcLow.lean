module

public import RequestProject.Beurling.Model.Wire

/-!
# `T_c = 0` on `(-∞, X₀]` (§5.1, "The jump at `X₀`")

`T' = 0` below `X₀` (there `T = ⌊·⌋`), and `T_c(X₀) = T'(X₀⁺) - j₀ = 0`:

* `absSet_large` : an absorbed height `n` has `(log X₀)² < log n` (its latest prime is jittered,
  `≥ X₀⁻`, and below `y(n)`, while `y(n) < X₀⁻` for `log n ≤ (log X₀)²`, Theorem 6.23(b));
* `rhoCap_X0` : `ρ̄_𝒜(X₀) = 0`;
* `deriv_osc_X0` : `R'(X₀) = 0` (`R` vanishes below `x₁ ≥ e^{X₀²}`);
* `KAbsR_eq_zero_low` : `K_𝒜 g = 0` on `(-∞, X₀]`;
* `TcR_low` : `T_c = 0` on `(-∞, X₀]` (the input `TcLow` of the bridge).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section

variable (hc : Cond θ X₀)
include hc

/-- `y(n) > X₀⁻` forces `(log X₀)² < log x`, `x` the scale of `n`, and `X₀ < x ≤ n`. -/
lemma absorbY_gt_Xm {n : ℝ} (h : Xm X₀ < absorbY X₀ n) :
    Real.log X₀ ^ 2 < Real.log n ∧ (X₀ : ℝ) < n := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  set x := dyadicScale (X₀ : ℝ) (max (X₀ : ℝ) n) with hxdef
  have hxX : (X₀ : ℝ) ≤ x := le_dyadicScale (by linarith) (le_max_left _ _)
  have hxt : x ≤ max (X₀ : ℝ) n := dyadicScale_le (by linarith) (by positivity)
  have hbig : Real.log X₀ ^ 2 < Real.log x := by
    by_contra hlow; push_neg at hlow
    have := absorbYAt_lt hX0 hX hxX hlow
    have e : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
    have e2 : absorbY X₀ n = absorbYAt X₀ x := rfl
    linarith
  have hlogX : Real.log X₀ < Real.log x := by
    have : Real.log X₀ < Real.log X₀ ^ 2 := by nlinarith
    linarith
  have hxX' : (X₀ : ℝ) < x := by
    by_contra h; push_neg at h
    have := Real.log_le_log (by linarith) h; linarith
  have hxn : x ≤ n := by
    rcases le_total (X₀ : ℝ) n with h | h
    · rwa [max_eq_right h] at hxt
    · rw [max_eq_left h] at hxt; linarith
  exact ⟨lt_of_lt_of_le hbig (Real.log_le_log (by linarith) hxn), by linarith⟩

/-- **Absorbed heights are large**: `n ∈ 𝒜` has `(log X₀)² < log n` and `X₀ < n`. -/
lemma absSet_large (ω : JitterΩ) {n : ℝ} (hn : n ∈ absSet X₀ (DF θ X₀ ω)) :
    Real.log X₀ ^ 2 < Real.log n ∧ (X₀ : ℝ) < n := by
  obtain ⟨-, e, -, -, -, k, -, -, hk⟩ := hn
  have h1 : Xm X₀ ≤ valF θ X₀ k ω := valF_ge_Xm hc k ω
  exact absorbY_gt_Xm hc (lt_of_le_of_lt h1 hk)

/-- **`ρ̄_𝒜(X₀) = 0`**. -/
lemma rhoCap_X0 (ω : JitterΩ) :
    absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) X₀ = 0 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hb : 0 < thetaB θ := thetaB_pos (by linarith [hc.hθ.1])
  have hb1 : thetaB θ ≤ 1 := (thetaB_le_quarter (by linarith [hc.hθ.2])).trans (by norm_num)
  have hρ : absorbedDensity (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) X₀ = 0 := by
    unfold absorbedDensity
    refine (tsum_congr fun a => ?_).trans tsum_zero
    unfold absorbedBump
    split_ifs with ha
    · obtain ⟨hla, hXa⟩ := absSet_large hc ω ha
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨h1, h2⟩
      have ha0 : 0 ≤ a := by linarith
      obtain ⟨hu0, hu⟩ := solveU_spec hb ha0
      have hU : uA θ a = solveU (thetaB θ) a := rfl
      rw [hU] at h1
      -- `a ≤ 2u` (as `u^b ≤ max(u, 1)`), so `u ≥ a/2 > X₀`
      have hbig : 4 * (X₀ : ℝ) < a := by
        have : (X₀ : ℝ) ^ 2 < a := by
          have hlog : Real.log ((X₀ : ℝ) ^ 2) < Real.log a := by
            rw [Real.log_pow]; push_cast
            have : 2 * Real.log X₀ < Real.log X₀ ^ 2 := by nlinarith [hc.hX]
            linarith
          exact (Real.log_lt_log_iff (by positivity) (by linarith)).mp hlog
        nlinarith [X₀_ge_two_pow hc.hX]
      rcases le_or_gt 1 (solveU (thetaB θ) a) with hu1 | hu1
      · have : solveU (thetaB θ) a ^ (thetaB θ) ≤ solveU (thetaB θ) a :=
          Real.rpow_le_self_of_one_le hu1 hb1
        linarith
      · have : solveU (thetaB θ) a ^ (thetaB θ) ≤ 1 :=
          Real.rpow_le_one hu0 hu1.le hb.le
        linarith
    · rfl
  unfold absorbedDensityCap
  rw [hρ]
  have : 0 ≤ 0.1 / Real.log X₀ := div_nonneg (by norm_num) (by linarith [hc.hX])
  exact min_eq_left this

omit hc in
/-- **`R'(X₀) = 0`**: the oscillation vanishes on `(0, x₀⁺]`, `x₀⁺ = e^{X₀²} > X₀`. -/
lemma deriv_osc_X0 (hX1 : 1 < (X₀ : ℝ)) (α γ : ℕ → ℝ) :
    deriv (Oscillation.osc θ α γ (switchOn X₀)) X₀ = 0 := by
  have hlt : (X₀ : ℝ) < switchOn X₀ 0 := by
    show (X₀ : ℝ) < Real.exp ((X₀ : ℝ) ^ 2)
    have := Real.add_one_le_exp ((X₀ : ℝ) ^ 2)
    nlinarith
  have hev : Oscillation.osc θ α γ (switchOn X₀) =ᶠ[nhds (X₀ : ℝ)] fun _ => 0 := by
    have hmem : Ioo (0 : ℝ) (switchOn X₀ 0) ∈ nhds (X₀ : ℝ) :=
      Ioo_mem_nhds (by linarith) hlt
    filter_upwards [hmem] with x hx
    exact Target.osc_eq_zero_of_le (switchOn_spacing _) hx.1 hx.2.le
  rw [hev.deriv_eq]
  exact deriv_const _ _

/-- **`K_𝒜 g = 0` on `(-∞, X₀]`** (absorbed landings need `y(t) > X₀⁻`). -/
lemma KAbsR_eq_zero_low (ω : JitterΩ) (g : ℝ → ℝ) {t : ℝ} (ht : t ≤ X₀) :
    KAbsR θ X₀ ω g t = 0 := by
  classical
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  unfold KAbsR
  refine Finset.sum_eq_zero fun w hw => ?_
  rw [if_neg]
  rintro ⟨-, -, habs⟩
  have hw' := (KR.Sharp.mem_NAll_iff (PR θ X₀ ω) hXm0).mp (Finset.mem_filter.mp hw).1
  have hcut : Xm X₀ ≤ t / Vl (PR θ X₀ ω) w :=
    (KR.Sharp.le_div_iff_cut (PR θ X₀ ω) hXm0).mp hw'.2
  have := (absorbY_gt_Xm hc (lt_of_le_of_lt hcut habs)).2
  linarith

/-- **`T_c = 0` on `(-∞, X₀]`** (§5.1; `T_c(X₀) = T'(X₀⁺) - j₀ = 0`), the input `TcLow` of the
bridge. -/
theorem TcR_low (ω : JitterΩ) {t : ℝ} (ht : t ≤ X₀) : TcR θ X₀ ω (jzX X₀) t = 0 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  unfold TcR
  rw [KAbsR_eq_zero_low hc ω _ ht]
  rcases ht.lt_or_eq with hlt | heq
  · have hT0 : TpCont θ X₀ ω t = 0 := by unfold TpCont; rw [if_neg (not_le.mpr hlt)]
    have hi : KR.Chain.ind X₀ t = 0 := by
      unfold KR.Chain.ind; exact Set.indicator_of_notMem (by simpa using hlt) _
    rw [hT0, hi]; ring
  · subst heq
    have hi : KR.Chain.ind X₀ (X₀ : ℝ) = 1 := by
      unfold KR.Chain.ind; exact Set.indicator_of_mem (by simp) _
    have hT : TpCont θ X₀ ω X₀ = 1 - Target.rhoDet X₀ (kappaParam X₀) X₀ := by
      unfold TpCont
      rw [if_pos le_rfl, rhoCap_X0 hc ω, deriv_osc_X0 hX1]
      ring
    rw [hT, hi]; unfold jzX; ring

end

end BModel
