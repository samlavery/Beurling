module

public import RequestProject.Beurling.Noise.RML10Rest

/-!
# The field `hsmall` of `RestMargin`, with the `a_K`, `G` and `Φ₂` inputs reduced

`hsmall_11` is `BModel.RML10.hsmall_10` with

* `Φ₂(X₀⁻/2) ≤ e^{-200}` proved (`KR.WidthReal.Phi_tiny` with `Hc_Xm_half_le`, from `TNP.Hyp`);
* the `a_K`-term bounded by `1612 S_b` from `S_K(t) ≤ S_b` (`aK_le`: `C_N ≤ 158` and
  `log t/log(t - H(t)/2) ≤ 2`);
* the `G`-term bounded by `56564 G_b` from `0 ≤ G_s(t) ≤ G_b` (`C_N ≤ 158`).

The remaining inputs are the bound `j_{X₀} ≤ a₄` on `[X₀^{1.01}, b]`, the Step 4 size
`6.5 E_S + V_{X₀} ≤ a₅`, the sizes `S_b`, `G_b` of the Model's `S_K`, `∑ (log 3v)² (o_G + F̄_r)`,
and `1612 S_b + 56564 G_b + a₄ + a₅ ≤ 0.0099`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML11

open KR.TNP KR.Chain

variable {θ : ℝ} {X₀ : ℕ}

/-- `a_K(C_N, S, H, t) ≤ 1612 S_b` for `0 ≤ S ≤ S_b`, `C_N ≤ 158`, `t ≥ X₀⁻ ≥ 10⁷` and
`H(t) ≤ t/10`. -/
lemma aK_le {CN S Sb t : ℝ} {H : ℝ → ℝ} (hCN : CN ≤ 158) (hS0 : 0 ≤ S)
    (hSb : S ≤ Sb) (ht : 10000000 ≤ t) (hH : H t ≤ t / 10) :
    KR.RML6K.aK CN S H t ≤ 1612 * Sb := by
  unfold KR.RML6K.aK
  have ht0 : 0 < t := by linarith
  have hu : 0.95 * t ≤ t - H t / 2 := by linarith
  have hu0 : 0 < t - H t / 2 := by linarith
  have hlt : Real.log t ≤ 2 * Real.log (t - H t / 2) := by
    have h1 : Real.log (0.95 * t) ≤ Real.log (t - H t / 2) := Real.log_le_log (by positivity) hu
    have h2 : Real.log (0.95 * t) = Real.log 0.95 + Real.log t :=
      Real.log_mul (by norm_num) ht0.ne'
    have h3 : Real.log 0.95 ≥ -1 := by
      have := Real.add_one_le_exp (-1 : ℝ)
      have h := Real.log_le_log (Real.exp_pos (-1)) (by
        have : Real.exp (-1) ≤ 0.95 := by
          have := Real.exp_one_gt_d9
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
        exact this)
      rw [Real.log_exp] at h; linarith
    have h4 : (16 : ℝ) ≤ Real.log t := by
      have : Real.log 10000000 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      have h7 : (16 : ℝ) ≤ Real.log 10000000 := by
        have := Real.add_one_le_exp (16 : ℝ)
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have e : Real.exp 16 ≤ 10000000 := by
          have := Real.exp_one_lt_d9
          have h : Real.exp 16 = Real.exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h]
          calc Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
                pow_le_pow_left₀ (Real.exp_pos 1).le this.le 16
            _ ≤ 10000000 := by norm_num
        exact e
      linarith
    linarith
  have hlu : 0 < Real.log (t - H t / 2) := by
    have : (1 : ℝ) < t - H t / 2 := by linarith
    exact Real.log_pos this
  have hr : Real.log t / Real.log (t - H t / 2) ≤ 2 := by
    rw [div_le_iff₀ hlu]; linarith
  have hr0 : 0 ≤ Real.log t / Real.log (t - H t / 2) :=
    div_nonneg (Real.log_nonneg (by linarith)) hlu.le
  have hb : 5.1 * CN * S ≤ 5.1 * 158 * Sb := by
    have := mul_le_mul hCN hSb hS0 (by norm_num : (0 : ℝ) ≤ 158); nlinarith
  calc 5.1 * CN * S * (Real.log t / Real.log (t - H t / 2)) ≤ 5.1 * 158 * Sb * 2 :=
        mul_le_mul hb hr hr0 (by nlinarith)
    _ ≤ 1612 * Sb := by nlinarith

/-- **The field `hsmall`** of `RestMargin`, with `Φ₂`, `a_K` and `G` reduced. -/
theorem hsmall_11 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) (nb : ℕ → ℝ) (ES jP b a4 a5 Sb Gb : ℝ)
    {Z η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) (hXmX : Xm X₀ ≤ X₀)
    (hj : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      0 ≤ jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ∧
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ≤ a4) (ha4 : a4 ≤ 1 / 2)
    (hS : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → 0 ≤ SK θ X₀ ω nb t ∧ SK θ X₀ ω nb t ≤ Sb)
    (hG : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      0 ≤ ∑ i ∈ Finset.range (Jc X₀ t + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 *
        (obG X₀ i + FrBv θ X₀ ω nb i) ∧
      ∑ i ∈ Finset.range (Jc X₀ t + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 *
        (obG X₀ i + FrBv θ X₀ ω nb i) ≤ Gb)
    (hEV : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      6.5 * (RML7.canonP X₀ epsH ES jP).ES + VX (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t ≤ a5)
    (hsum : 1612 * Sb + 56564 * Gb + a4 + a5 ≤ 0.0099) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    oTot (Queue6.Hc X₀ t) t ((fun _ => EBRc) t) ((fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀)
      (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t) +
      ((fun x => KR.RML6K.aK (CNt X₀) (SK θ X₀ ω nb x) (Queue6.Hc X₀) x) t +
        (fun x => 35.8 * CNt X₀ * 10 * ∑ i ∈ Finset.range (Jc X₀ x + 1), Real.log (3 *
          (Xm X₀ * 2 ^ i)) ^ 2 *
            (obG X₀ i + FrBv θ X₀ ω nb i)) t + 6 * Real.log t / Queue6.Hc X₀ t) +
              (fun _ => EBRc) t + (fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω)
                (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t +
      54 * (sηB X₀) + 6 * Real.log t / Queue6.Hc X₀ t + 6.5 * (RML7.canonP X₀ epsH ES jP).ES + VX
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t ≤ 0.01 := by
  have hPhi := KR.WidthReal.Phi_tiny htnp (KR.WidthReal.Hc_Xm_half_le hX) (a := 2) (by norm_num)
  obtain ⟨hCN0, hCN⟩ := CNt_bounds (X0 := (X₀ : ℝ)) (htnp.hXm.trans
    (Real.log_le_log htnp.width.X0m_pos hXmX))
  have hX1 := RML10.X0_le_X1 hX
  have hXm7 : (10 : ℝ) ^ 7 ≤ Xm X₀ := htnp.hbs.X0m_ge
  refine RML10.hsmall_10 hX ω nb ES jP b (1612 * Sb) (56564 * Gb) a4 a5 hj ha4 ?_ ?_ hEV hPhi
    hsum
  · intro t ht htb
    obtain ⟨h0, h1⟩ := hS t ht htb
    have htX : (X₀ : ℝ) ≤ t := hX1.trans ht
    have hXt : Xm X₀ ≤ t := hXmX.trans htX
    exact aK_le hCN h0 h1 (by norm_num at hXm7; linarith)
      (hO.small t (by linarith [htnp.width.X0m_pos]))
  · intro t ht htb
    obtain ⟨h0, h1⟩ := hG t ht htb
    have := mul_le_mul hCN h1 h0 (by norm_num : (0 : ℝ) ≤ 158)
    nlinarith

end BModel.RML11

end
