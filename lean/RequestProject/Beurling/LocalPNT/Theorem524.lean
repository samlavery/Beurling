module

public import RequestProject.Beurling.LocalPNT.Step9
public import RequestProject.Beurling.LocalPNT.Num9
public import RequestProject.Beurling.LocalPNT.PartialSum
public import RequestProject.Beurling.LocalPNT.LPa

/-!
# Theorem 5.24 (local prime number theorem)

* `LPHyp.lp_i` : (i) with `K = e^{97} Λ²` (Step 9, applied at the height `v`, where (LP-a)
  still holds by `LPHyp.mono`);
* `LPHyp.theorem_5_24` : `Theorem524Concl P X₀ y`, i.e. (i) and (ii) with `K = e^{98} Λ^{5.9}`
  (the latter by partial summation, `lp_ii_of_i8'`) and (iii) (Step 10, `lp_iii`);
* `theorem_5_24_of_lag` : the same from the queue-lag bound up to the horizon `ž`
  (`lpHyp_of_lag`), the form used on `Good(<z)`.
-/

@[expose] public section

open Set Real Oscillation Construction DesignedZero

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma X0_le_XLP : (X₀ : ℝ) ≤ XLP (Real.log X₀) := by
  have hX := h.logX
  have hl := Num10.eighteen_le_log hX
  rw [XLP, ← Real.exp_log h.X0_pos]
  apply Real.exp_le_exp.2
  rw [Real.log_exp]
  have h1 : Real.log X₀ ≤ Real.log X₀ ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ 10 ^ 5 * Real.log (Real.log X₀) ^ 2 := by nlinarith
  nlinarith

/-- **Theorem 5.24(i)** with `K = e^{97} Λ²`, `c_LP = c_zf/5`, `c_zf = 0.088/Λ`, for
`X_LP ≤ v ≤ y`. -/
theorem lp_i {v : ℝ} (hv : XLP (Real.log X₀) ≤ v) (hvy : v ≤ y) :
    |piRecip P v - pi0Recip v| ≤
      Real.exp 97 * Real.log X₀ ^ 2 *
        Real.exp (-(cLP (Real.log X₀) * Real.sqrt (Real.log v))) := by
  have hX := h.logX
  have h' := h.mono (h.X0_le_XLP.trans hv) hvy
  have hL : 10 ^ 5 * Real.log X₀ ^ 2 * Real.log (Real.log X₀) ^ 2 ≤ Real.log v := by
    have := Real.log_le_log (Real.exp_pos (10 ^ 5 * Real.log X₀ ^ 2 *
      Real.log (Real.log X₀) ^ 2)) hv
    rwa [Real.log_exp] at this
  exact h'.lp_i_top_of hL (Num9.yrange9 hX hL) (Num9.hTy9 hX hL)
    (fun a θ' ha hθ' => Num9.num9_main hX hL ha hθ')

/-- **Theorem 5.24** (local prime number theorem): (i), (ii) and (iii) with the explicit
constants, under (LP-a) (and the target data of `LPHyp`). -/
theorem theorem_5_24 : Theorem524Concl P X₀ y := by
  have hX := h.logX
  refine ⟨fun v hv hvy => ?_, fun v η hP hη1 hη2 hy => ?_⟩
  · have hXy := hv.trans hvy
    have hrec := (h.mono h.X0_le_XLP hXy).piRecip_le
    exact lp_ii_of_i8' P hX (fun v hv hvy => h.lp_i hv hvy)
      (fun u _ hu2 => ((monotone_piRecip P) hu2).trans hrec) v hv hvy
  · have hΛ3 : 0 < 76 * Real.log X₀ ^ 3 := by positivity
    have hη0 : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hη1
    by_cases hv0 : 0 < v
    · have hv1 : 1 < v := by
        by_contra hc; push_neg at hc
        have := Real.log_nonpos hv0.le hc; linarith
      have hlv : 1 ≤ Real.log v := by
        have : (1 : ℝ) ≤ Real.log X₀ ^ 3 := one_le_pow₀ (by linarith)
        linarith
      exact ⟨lpWindow_bounds hv1 hlv hη0 hη2, fun u hu => lpWindow_eq_one hv1 hlv hη0 hη2 hu,
        fun u hu => lpWindow_support hv1 hlv hη0 hη2 hu, h.lp_iii hv1 hP hη1 hη2 hy⟩
    · -- for `v ≤ 0` the window vanishes (and `log v ≥ 76 Λ³` forces `v < 0`)
      have hz : ∀ u, lpWindow v η u = 0 := fun u => by simp [lpWindow, hv0]
      have hvneg : v < 0 := by
        rcases (not_lt.1 hv0).lt_or_eq with h1 | h1
        · exact h1
        · rw [h1, Real.log_zero] at hP; linarith
      refine ⟨fun u => by simp [hz], fun u hu => ?_, fun u hu => absurd (hz u) hu, ?_⟩
      · exfalso; have := hu.1.trans hu.2; nlinarith
      · simp only [piInt, pi0Int, hz, zero_div, zero_mul, finsum_zero,
          MeasureTheory.integral_zero, mul_zero, le_refl]

end LPHyp

/-- **Theorem 5.24 on `Good(<z)`**: from the queue-lag bound up to the horizon `ž` (Theorem 5.2,
Corollary 5.4, (eq:T1), Remark 5.3) — the form of (LP-a) of the paper — for every height
`X₀ ≤ y ≤ ž`. The positivity margin (Lemma 3.3) enters as `hmono`. -/
theorem theorem_5_24_of_lag {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ}
    {Xm zc y : ℝ}
    (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀) (hev : Even X₀)
    (hα : ∀ k, |α k| ≤ 2) (h0 : Real.exp ((X₀ : ℝ) ^ 2) ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) (hmono : MonotoneOn (T0 θ X₀ α γ xp) (Ici (X₀ : ℝ)))
    (cntA rhoA : ℝ → ℝ) (hXm : (X₀ : ℝ) - (X₀ : ℝ) ^ (1 / 40 : ℝ) ≤ Xm) (hXmX : Xm ≤ X₀)
    (hfl : ∀ u, u < Xm → P.N u = ⌊u⌋₊)
    (hlag : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc →
      |P.N u - Target.target X₀ (kap X₀) cntA rhoA (osc θ α γ xp) u| ≤ u ^ lagExponent θ)
    (hA : ∀ u, (X₀ : ℝ) ≤ u → u ≤ zc → |cntA u - ∫ v in (X₀ : ℝ)..u, rhoA v| ≤ 2 * u ^ (thetaB θ))
    (hy : (X₀ : ℝ) ≤ y) (hyz : y ≤ zc) :
    Theorem524Concl P X₀ y :=
  (lpHyp_of_lag hθ hX hev hα h0 hsp hmono cntA rhoA hXm hXmX hfl hlag hA hy hyz).theorem_5_24

end LocalPNT

end
