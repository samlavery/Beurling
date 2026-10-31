module

public import RequestProject.Beurling.Model.R27

/-!
# Step 4 of Proposition 5.38: the oscillation `o_V` of `T_c` (the field `ho` of `RestMarginR`)

`ho_c` : on `Good(< t)`, at every `X₀/4 ≤ t' ≤ b`, `log t' · o_V(t') ≤ 10⁻²⁰`, where
`o_V(t') = sup_{|h| ≤ 1.01 H(t')} |T_c(t'+h) - T_c(t')|` (`oVc`). Both points are clamped to
`[X₀, ∞)` (`T_c = 0` on `(-∞, X₀]` and continuous at `X₀`), and `Tc_pair_le` (the three parts of
eq. (osc): `ρ_det`, `R'`, `σ_𝒜`) with `nonA_le` at the scale `u = ` the lower point gives
`log t' · |T_c(t'+h) - T_c(t')| ≤ u^{-1/10} + 4 (log u)^{-3}`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Queue6 KR KR.TNP

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `sup_W F ≤ C` if `F ≤ C` on the window. -/
lemma supW_le' {F : ℝ → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hb : ∀ h, |h| ≤ c → F h ≤ C) :
    Margin.RML6.supW F c ≤ C := by
  unfold Margin.RML6.supW
  haveI : Nonempty {h : ℝ // |h| ≤ c} := ⟨⟨0, by simpa using hc⟩⟩
  exact ciSup_le fun h => hb h.1 h.2

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 4000000 in
/-- **The field `ho`** (Step 4 of Proposition 5.38: the oscillation of `T_c` on the windows of
length `1.01 H`): `log t' · o_V(t') ≤ 10⁻²⁰` at `X₀/4 ≤ t' ≤ b`, on `Good(< t)`, `b ≤ t`. -/
theorem ho_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {t' : ℝ} (ht1 : (X₀ : ℝ) / 4 ≤ t') (htb : t' ≤ b) :
    Real.log t' * oVc θ X₀ ω t' ≤ 1 / 10 ^ 20 := by
  have hX := hc.hX
  have hX1' := one_lt_X0 hc
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hXge := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have ht0 : 0 < t' := by linarith
  have hHt0 := (KR.WidthReal.Hc_pos hX (X₀ := X₀) t').le
  have hHt : Queue6.Hc X₀ t' ≤ max t' X₀ / 40 := by
    unfold Queue6.Hc; exact KR.WidthReal.capH_le_tenth hX (le_max_right _ _)
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  have hlt : 0 ≤ Real.log t' := Real.log_nonneg (by linarith)
  have hHb40 : Queue6.Hc X₀ t' ≤ b / 40 :=
    hHt.trans (div_le_div_of_nonneg_right (max_le htb hb) (by norm_num))
  have hHt1 : (X₀ : ℝ) ≤ t' → Queue6.Hc X₀ t' ≤ t' / 40 := fun h1 => by
    rw [max_eq_left h1] at hHt; exact hHt
  -- the pointwise bound
  have key : ∀ h, |h| ≤ 1.01 * Queue6.Hc X₀ t' →
      |TcR θ X₀ ω (jzX X₀) (t' + h) - TcR θ X₀ ω (jzX X₀) t'| ≤
        1 / 10 ^ 20 / Real.log t' := by
    intro h hh
    have hh' := abs_le.mp hh
    rw [TcR_eq_max hc ω (t' + h), TcR_eq_max hc ω t']
    set a := max (t' + h) (X₀ : ℝ)
    set c := max t' (X₀ : ℝ)
    have hac : |a - c| ≤ 1.01 * Queue6.Hc X₀ t' :=
      (abs_max_sub_max_le_abs _ _ _).trans (by simpa using hh)
    -- a single bound for `lo ≤ hi`
    have pair : ∀ lo hi : ℝ, (X₀ : ℝ) ≤ lo → lo ≤ hi → hi - lo ≤ 1.01 * Queue6.Hc X₀ t' →
        t' / 2 ≤ lo → hi ≤ 2 * (b + Queue6.Hc X₀ b) →
        |TcR θ X₀ ω (jzX X₀) lo - TcR θ X₀ ω (jzX X₀) hi| ≤ 1 / 10 ^ 20 / Real.log t' := by
      intro lo hi hlo hlh hd hlo2 hhi
      have hP := Tc_pair_le hc hev hb hbt hQC hE1 hN hT hlo hlh hhi
      have hlo0 : 0 < lo := by linarith
      have hu4 : (X₀ : ℝ) ≤ 4 * lo := by linarith
      have hn := nonA_le hX hu4
      have hκ := (kappa_facts hX).1
      -- `H(t') ≤ H(2 lo)`
      have hH2 : Queue6.Hc X₀ t' ≤ Queue6.Hc X₀ (2 * lo) := KR.WidthReal.Hc_mono hX (by linarith)
      have hd2 : hi - lo ≤ 2.04 * Queue6.Hc X₀ (2 * lo) := by linarith
      have hd0 : 0 ≤ hi - lo := by linarith
      have t1 : (5 * (hi - lo) + 3) / (kappaParam X₀ * lo) ≤
          (10 * (2.04 * Queue6.Hc X₀ (2 * lo)) + 6) / (kappaParam X₀ * lo) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have t2 : (hi - lo) * lo ^ (-(1 / 20 : ℝ)) ≤
          2.04 * Queue6.Hc X₀ (2 * lo) * (lo / 2) ^ (-(1 / 20 : ℝ)) :=
        mul_le_mul hd2 (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num))
          (Real.rpow_nonneg hlo0.le _) (by
            have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) (2 * lo)).le; positivity)
      have hLlo : 10 ^ 8 ≤ Real.log lo := hX.trans (Real.log_le_log hXp hlo)
      have hl2 : Real.log t' ≤ Real.log (2 * lo) := Real.log_le_log ht0 (by linarith)
      have hl2' : Real.log (2 * lo) ≤ 2 * Real.log lo := by
        rw [Real.log_mul (by norm_num) hlo0.ne']
        have := Real.log_two_lt_d9; linarith
      have t3 : (if Lstar X₀ < Real.log hi then (Real.log lo ^ 4)⁻¹ else 0) ≤
          (Real.log lo ^ 4)⁻¹ := by
        split_ifs
        · exact le_rfl
        · positivity
      -- `lo^{-1/40} ≤ 10⁻⁴³`
      have hr : lo ^ (-(1 / 40 : ℝ)) ≤ 1 / 10 ^ 43 :=
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)).trans
          (X0_quarter_rpow_le hX)
      have hA : Real.log (2 * lo) * (2 * (Real.log lo ^ 4)⁻¹) ≤ 4 / 10 ^ 24 := by
        have hL0 : 0 < Real.log lo := by linarith
        rw [mul_comm, mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc,
          div_le_div_iff₀ (by positivity) (by norm_num)]
        have h3 : (10 : ℝ) ^ 24 ≤ Real.log lo ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num) hLlo 3; norm_num at this ⊢; linarith
        nlinarith [pow_pos hL0 3]
      rw [le_div_iff₀' (by
        rcases eq_or_lt_of_le hlt with h0 | h0
        · exfalso
          have hq : Real.log t' ≥ Real.log (X₀ / 4) := Real.log_le_log (by positivity) ht1
          rw [Real.log_div hXp.ne' (by norm_num),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hq
          have h2 := Real.log_two_lt_d9; push_cast at hq; linarith
        · exact h0)]
      have hS : |TcR θ X₀ ω (jzX X₀) lo - TcR θ X₀ ω (jzX X₀) hi| ≤
          ((10 * (2.04 * Queue6.Hc X₀ (2 * lo)) + 6) / (kappaParam X₀ * lo) +
            2.04 * Queue6.Hc X₀ (2 * lo) * (lo / 2) ^ (-(1 / 20 : ℝ))) +
          2 * (Real.log lo ^ 4)⁻¹ := by linarith
      have hpos : 0 ≤ ((10 * (2.04 * Queue6.Hc X₀ (2 * lo)) + 6) / (kappaParam X₀ * lo) +
            2.04 * Queue6.Hc X₀ (2 * lo) * (lo / 2) ^ (-(1 / 20 : ℝ))) := by
        have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) (2 * lo)).le
        have : 0 ≤ (lo / 2) ^ (-(1 / 20 : ℝ)) := Real.rpow_nonneg (by linarith) _
        positivity
      calc Real.log t' * |TcR θ X₀ ω (jzX X₀) lo - TcR θ X₀ ω (jzX X₀) hi|
          ≤ Real.log (2 * lo) * (((10 * (2.04 * Queue6.Hc X₀ (2 * lo)) + 6) /
              (kappaParam X₀ * lo) + 2.04 * Queue6.Hc X₀ (2 * lo) * (lo / 2) ^ (-(1 / 20 : ℝ))) +
              2 * (Real.log lo ^ 4)⁻¹) :=
            mul_le_mul hl2 hS (abs_nonneg _) (by linarith)
        _ = Real.log (2 * lo) * ((10 * (2.04 * Queue6.Hc X₀ (2 * lo)) + 6) /
              (kappaParam X₀ * lo) + 2.04 * Queue6.Hc X₀ (2 * lo) * (lo / 2) ^ (-(1 / 20 : ℝ))) +
            Real.log (2 * lo) * (2 * (Real.log lo ^ 4)⁻¹) := by ring
        _ ≤ 1 / 10 ^ 43 + 4 / 10 ^ 24 := by linarith
        _ ≤ 1 / 10 ^ 20 := by norm_num
    -- ranges of the clamped points
    have hcX : (X₀ : ℝ) ≤ c := le_max_right _ _
    have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
    have hlo_a : t' / 2 ≤ a := by
      rcases le_or_gt (X₀ : ℝ) t' with h1 | h1
      · have := hHt1 h1; exact le_trans (by linarith) (le_max_left _ _)
      · exact le_trans (by linarith) haX
    have hlo_c : t' / 2 ≤ c := le_trans (by linarith) (le_max_left _ _)
    have hhi : ∀ z, z ≤ t' + 1.01 * Queue6.Hc X₀ t' → max z (X₀ : ℝ) ≤ 2 * (b + Queue6.Hc X₀ b) :=
      fun z hz => max_le (by linarith) (by linarith)
    have ha2 := hhi (t' + h) (by linarith)
    have hc2 := hhi t' (by linarith)
    rcases le_total a c with h1 | h1
    · exact pair a c haX h1 (by linarith [(abs_le.mp hac).1]) hlo_a hc2
    · rw [abs_sub_comm]
      exact pair c a hcX h1 (by linarith [(abs_le.mp hac).2]) hlo_c ha2
  have hW0 : 0 ≤ 1.01 * Queue6.Hc X₀ t' := by linarith
  have hs := supW_le' (F := fun h => |TcR θ X₀ ω (jzX X₀) (t' + h) - TcR θ X₀ ω (jzX X₀) t'|)
    hW0 key
  unfold oVc
  rcases eq_or_lt_of_le hlt with h0 | h0
  · rw [← h0, zero_mul]; norm_num
  · calc Real.log t' * Margin.RML6.supW (fun h => |TcR θ X₀ ω (jzX X₀) (t' + h) -
          TcR θ X₀ ω (jzX X₀) t'|) (1.01 * Queue6.Hc X₀ t')
        ≤ Real.log t' * (1 / 10 ^ 20 / Real.log t') := mul_le_mul_of_nonneg_left hs hlt
      _ = 1 / 10 ^ 20 := by field_simp

end BModel

end
