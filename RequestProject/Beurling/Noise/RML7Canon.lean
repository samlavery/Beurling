module

public import RequestProject.Beurling.Noise.MarginRealLoc

/-!
# The canonical recursion parameters of Proposition 5.38 for the realised system

`BModel.RML7.canonP X₀ εH ES j` is the parameter record `Margin.Rec.CP` that §5 uses for the
realised system (`H = Hc X₀`, `X₀⁻ = Xm X₀`):

* `ε = εH` (the exponent of `CapHSlope`/(R_H)), `ε' = 0.045`, `θ = 0.01`, `θ₀ = 0.21`;
* `c_∞ = 1.21 X₀⁻/2`, `K_c = 5 H(2X₀)`, `R₀ = X₀ - 1.21 X₀⁻/2`, `K_r = 5 H(3X₀)`;
* `E_S` and `j` are the free size parameters (`E_S ≥ 0`, `j ≥ 0`).

Proved: `canonP_eps` (`εH ≤ p.ε`, for `RML6Var.hgeom_of`), `canonP_Kc_nonneg`, `canonP_cinf`
(`p.Xm/2 ≤ p.cinf`), `canonP_ES_nonneg` (for `Margin.Rec.htail_loc`), `canonP_epsle`
(`p.ε ≤ 0.01`, the field `hpε`), `canonP_eps'` (`p.ε' ≤ 0.045`, the field `hpε'`), and
`canonP_chain`: all of `Margin.Rec.ChainHyp (PR θ X₀ ω) p (Hc X₀)` (the field `chain`), from
`PaperWidth (Hc X₀) (Xm X₀) εH θH`, `log X₀ ≥ 10⁸` and prime values `≥ 2`.
-/

@[expose] public section

open Real Set

namespace BModel.RML7

/-- **The canonical recursion parameters** for the realised system. -/
noncomputable def canonP (X₀ : ℕ) (εH ES j : ℝ) : Margin.Rec.CP where
  Xm := Xm X₀
  X0 := X₀
  ES := ES
  j := j
  ε := εH
  ε' := 0.045
  θ := 0.01
  θ0 := 0.21
  Kc := 5 * Queue6.Hc X₀ (2 * X₀)
  Kr := 5 * Queue6.Hc X₀ (3 * X₀)
  R0 := X₀ - 1.21 * (Xm X₀ / 2)
  cinf := 1.21 * (Xm X₀ / 2)

variable {X₀ : ℕ} {εH ES j : ℝ}

theorem canonP_eps : εH ≤ (canonP X₀ εH ES j).ε := le_rfl

theorem canonP_Xm : (canonP X₀ εH ES j).Xm = Xm X₀ := rfl

theorem canonP_eps' : (canonP X₀ εH ES j).ε' ≤ 0.045 := le_rfl

theorem canonP_ES_nonneg (hES : 0 ≤ ES) : 0 ≤ (canonP X₀ εH ES j).ES := hES

theorem canonP_epsle (hε : εH ≤ 4 / 1000000) : (canonP X₀ εH ES j).ε ≤ 0.01 := by
  show εH ≤ 0.01; linarith

theorem canonP_Kc_nonneg (hX : 10 ^ 8 ≤ Real.log X₀) : 0 ≤ (canonP X₀ εH ES j).Kc := by
  show 0 ≤ 5 * Queue6.Hc X₀ (2 * X₀)
  have := KR.WidthReal.Hc_pos hX (2 * X₀); linarith

theorem canonP_cinf (hX : 10 ^ 8 ≤ Real.log X₀) :
    (canonP X₀ εH ES j).Xm / 2 ≤ (canonP X₀ εH ES j).cinf := by
  show Xm X₀ / 2 ≤ 1.21 * (Xm X₀ / 2)
  have h1 := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have h2 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  linarith

lemma Xm_le_X0 (hX : 10 ^ 8 ≤ Real.log X₀) : Xm X₀ ≤ X₀ := by
  have e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
    unfold Xm Queue6.Hc; rw [max_self]
  have := KR.WidthReal.Hc_pos hX (X₀ : ℝ)
  linarith

lemma two_rpow_sub_one_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 4 / 1000000) :
    (2 : ℝ) ^ (ε - 1) ≤ 0.5005 := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have := KR.two_rpow_le h0 h1
  linarith

lemma two_rpow_weight_le {ε : ℝ} (h1 : ε ≤ 4 / 1000000) :
    (2 : ℝ) ^ (ε - 0.045) ≤ 0.9705 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  set c := (0.045 - ε) * Real.log 2
  have hl2 := Real.log_two_gt_d9
  have hc : 0.0305 ≤ c := by
    have : (0.0449 : ℝ) ≤ 0.045 - ε := by linarith
    have := mul_le_mul this hl2.le (by norm_num) (by linarith)
    simp only [c]; nlinarith
  have e : Real.log 2 * (ε - 0.045) = -c := by simp only [c]; ring
  rw [e, Real.exp_neg]
  have h := Real.add_one_le_exp c
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos c)]
  nlinarith

/-- **The field `chain`**: the canonical parameters satisfy `ChainHyp` for `H = Hc X₀`. -/
theorem canonP_chain {θ : ℝ} {ω : Construction.JitterΩ} (hX : 10 ^ 8 ≤ Real.log X₀)
    {θH : ℝ} (hP : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) εH θH) (hES : 0 ≤ ES) (hj : 0 ≤ j)
    (hp2 : ∀ i, 2 ≤ (PR θ X₀ ω).p i) :
    Margin.Rec.ChainHyp (PR θ X₀ ω) (canonP X₀ εH ES j) (Queue6.Hc X₀) := by
  have hXm := KR.WidthReal.Xm_ge hX (X₀ := X₀)
  have hX0 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hXmX := Xm_le_X0 hX
  have hε0 := hP.eps_nonneg
  have hε1 := hP.eps_le
  have hpos := KR.WidthReal.Hc_pos hX
  have hmono := KR.WidthReal.Hc_mono hX
  have hsmall2 : Queue6.Hc X₀ (2 * X₀) ≤ 2 * X₀ / 10 := hP.small _ (by linarith)
  have hw := two_rpow_sub_one_le hε0 hε1
  refine
    { hXm := by show 2 < Xm X₀; linarith
      hε0 := hε0
      hε1 := by show εH < 1; linarith
      hεε := by show εH ≤ 0.045; linarith
      hES := hES
      hj := hj
      hθ := by show (0 : ℝ) ≤ 0.01; norm_num
      hθ0 := by show (0 : ℝ) ≤ 0.21; norm_num
      hθ01 := by show (0.21 : ℝ) < 1; norm_num
      hKc := by show 0 ≤ 5 * Queue6.Hc X₀ (2 * X₀); linarith [hpos (2 * X₀)]
      hKr := by show 0 ≤ 5 * Queue6.Hc X₀ (3 * X₀); linarith [hpos (3 * X₀)]
      hrel := fun y hy => by
        show 2.1 * Queue6.Hc X₀ y ≤ 0.21 * y
        have := hP.small y hy; linarith
      hH0 := fun y => (hpos y).le
      hmono := hmono.monotoneOn _
      hRH := fun z hz a ha => by
        show Queue6.Hc X₀ (a * z) ≤ a ^ εH * Queue6.Hc X₀ z
        rw [mul_comm]; exact hP.RH z a hz ha
      hcinf := by show (1 + 0.21) * (Xm X₀ / 2) ≤ 1.21 * (Xm X₀ / 2); norm_num
      hXR := by
        show (1 + 0.21) * (Xm X₀ / 2) ≤ (X₀ : ℝ) - ((X₀ : ℝ) - 1.21 * (Xm X₀ / 2))
        linarith
      hR0 := by show (0 : ℝ) ≤ X₀ - 1.21 * (Xm X₀ / 2); linarith
      hlog := by
        show (1 + 0.01) * (-Real.log (1 - 0.21)) ≤ 0.01 * Real.log (1.21 * (Xm X₀ / 2))
        have h1 : -Real.log (1 - 0.21) ≤ 0.266 := by
          have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - 0.21 by norm_num)
          norm_num at this ⊢; linarith
        have hX4 : (X₀ : ℝ) / 4 ≤ 1.21 * (Xm X₀ / 2) := by linarith
        have h2 : Real.log X₀ - Real.log 4 ≤ Real.log (1.21 * (Xm X₀ / 2)) := by
          rw [← Real.log_div (by linarith) (by norm_num)]
          exact Real.log_le_log (by linarith) (by linarith)
        have h4 : Real.log 4 ≤ 2 := by
          have := Real.log_two_lt_d9
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
        nlinarith
      hKcH := by
        show 2.1 * Queue6.Hc X₀ (1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀)) ≤
          5 * Queue6.Hc X₀ (2 * X₀) * (1 - 2 ^ (εH - 1))
        have hle : Queue6.Hc X₀ (1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀)) ≤
            Queue6.Hc X₀ (2 * X₀) := hmono (by linarith)
        have := hpos (2 * X₀)
        nlinarith
      hKrH := by
        show 2.1 * Queue6.Hc X₀ ((X₀ + (X₀ - 1.21 * (Xm X₀ / 2))) / (1 - 0.21)) ≤
          5 * Queue6.Hc X₀ (3 * X₀) * (1 - 2 ^ (εH - 1))
        have harg : ((X₀ : ℝ) + (X₀ - 1.21 * (Xm X₀ / 2))) / (1 - 0.21) ≤ 3 * X₀ := by
          rw [div_le_iff₀ (by norm_num)]; linarith
        have hle := hmono harg
        have := hpos (3 * X₀)
        nlinarith
      hweight := by
        show 1.0101 * (1 + 0.01) * 2 ^ (εH - 0.045) ≤ 1
        have := two_rpow_weight_le hε1
        nlinarith
      hp2 := hp2 }

end BModel.RML7

end
