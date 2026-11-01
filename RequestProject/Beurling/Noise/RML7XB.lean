module

public import RequestProject.Beurling.Noise.RML7XBTail
public import RequestProject.Beurling.Noise.RML6Bridge
public import RequestProject.Beurling.Noise.RML6Var2Misc

/-!
# Proposition 5.31(i) (the small range) and the field `hjb`

* `xbB_le_five_twelfths` : **Proposition 5.31(i), the level reduction**: for a start `y` with
  `8 y H(X₀) ≤ X₀²` and `2y ≤ X₀⁻ X₀`, `0 ≤ 𝔅(y) ≤ 5/12` (one level `n₀` carries `𝔅(y)`,
  `RML7XBNear`; its term is at most `Br(n₀)`, `RML7XBLevel`; and `Br(n) ≤ 5/12` by the
  certificate `x0band_exact.py` for `n ≤ 10⁶` and the analytic tail beyond, `RML7XBTail`);
* `lam_eps_le` : `λ₀ (10⁶)^ε ≤ 1.0001` for `λ₀ ≤ 1.00003`, `ε ≤ 4·10⁻⁶`;
* `hjb_of` : **the field `hjb` of `BModel.RealMarginLoc`** for `jb := jXdef … j₀ NK` (eq. (jX0),
  `j_{X₀}(t) = sup_{y ∈ W_t} j₀ (𝔅(y) + 4.3 C_N E_θ/log y) log y`): `j_{X₀}(t) ≤ 0.4209` for
  `2X₀ ≤ t ≤ X₀^{1.01}` (Proposition 5.31(i), 04x-x0band.tex; Proposition 5.33).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- If `1.15 ≤ a^{2500}` and `x^{250000} = 10⁶` (`x, a ≥ 0`), then `x ≤ a`. -/
lemma root_le_of_pow {x a : ℝ} (hx0 : 0 ≤ x) (ha0 : 0 ≤ a) (hb : (1.15 : ℝ) ≤ a ^ (2500 : ℕ))
    (hxp : x ^ (250000 : ℕ) = 10 ^ 6) : x ≤ a := by
  have hb4 : (4 : ℝ) ≤ (1.15 : ℝ) ^ (10 : ℕ) := by norm_num
  have hc : (10 : ℝ) ^ 6 ≤ ((1.15 : ℝ) ^ (10 : ℕ)) ^ (10 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hb4 10
    have h4 : (10 : ℝ) ^ 6 ≤ 4 ^ (10 : ℕ) := by norm_num
    exact h4.trans this
  have hd : ((1.15 : ℝ) ^ (10 : ℕ)) ^ (10 : ℕ) ≤ (a ^ (2500 : ℕ)) ^ (100 : ℕ) := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hb 100
  have he : x ^ (250000 : ℕ) ≤ a ^ (250000 : ℕ) := by
    rw [hxp, show (250000 : ℕ) = 2500 * 100 by norm_num, pow_mul]
    exact hc.trans hd
  exact (pow_le_pow_iff_left₀ hx0 ha0 (by norm_num)).mp he

/-- `λ₀ (10⁶)^ε ≤ 1.0001` for `0 ≤ λ₀ ≤ 1.00003` and `0 ≤ ε ≤ 4·10⁻⁶`. -/
lemma lam_eps_le {ε lam0 : ℝ} (_hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (_hlam0 : 0 ≤ lam0)
    (hlam : lam0 ≤ 1.00003) : lam0 * ((10 : ℝ) ^ 6) ^ ε ≤ 1.0001 := by
  have h1 : ((10 : ℝ) ^ 6) ^ ε ≤ ((10 : ℝ) ^ 6) ^ (4 / 1000000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hε
  -- `(10⁶)^{4·10⁻⁶} ≤ 1.00006`, as `1.00006^{250000} ≥ 1.15^{100} ≥ 10⁶`
  have hb : (1.15 : ℝ) ≤ (1.00006 : ℝ) ^ (2500 : ℕ) := by
    have h0 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 0.00006 by norm_num) 2500
    have e1 : (1 : ℝ) + (2500 : ℕ) * 0.00006 = 1.15 := by norm_num
    have e2 : (1 : ℝ) + 0.00006 = 1.00006 := by norm_num
    rw [e1, e2] at h0; exact h0
  have hxp : (((10 : ℝ) ^ 6) ^ (4 / 1000000 : ℝ)) ^ (250000 : ℕ) = 10 ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : ((10 : ℝ) ^ 6) ^ (4 / 1000000 : ℝ) ≤ 1.00006 :=
    root_le_of_pow (Real.rpow_nonneg (by norm_num) _) (by norm_num) hb hxp
  have h3 : ((10 : ℝ) ^ 6) ^ ε ≤ 1.00006 := h1.trans h2
  have h4 : 0 ≤ ((10 : ℝ) ^ 6) ^ ε := Real.rpow_nonneg (by norm_num) _
  have := mul_le_mul hlam h3 h4 (by norm_num)
  linarith only [this]

lemma xbBstep_nonneg {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hlam0 : 0 ≤ lam0)
    (d n : ℕ) : 0 ≤ xbBstep P H tw X0m y X0 θ lam0 d n := by
  have hT : 0 ≤ TVD P H tw X0m y d := by unfold TVD; positivity
  have hK : 0 ≤ KRD P H tw X0m y d := ENNReal.toReal_nonneg
  have hw := KR.valN_labelVal_pos P (n / d)
  have hH := hP.reg.pos (posn P.labelVal y n)
  unfold xbBstep
  split_ifs <;> positivity

lemma xbTerm_nonneg {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hlam0 : 0 ≤ lam0)
    (n : ℕ) : 0 ≤ xbTerm P H tw X0m y X0 θ lam0 n := by
  unfold xbTerm
  have hV := KR.valN_labelVal_pos P n
  have h1 : 0 ≤ ∑ d ∈ n.properDivisors, xbBstep P H tw X0m y X0 θ lam0 d n :=
    Finset.sum_nonneg fun d _ => xbBstep_nonneg hP hlam0 d n
  have h2 : 0 ≤ (if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
      then |cN P tw X0m y n| / 2 else 0) := by split_ifs <;> positivity
  positivity

/-- **Proposition 5.31(i), the level reduction**: `0 ≤ 𝔅(y) ≤ 5/12` in the small range. -/
theorem xbB_le_five_twelfths {Z η1 η2 ε θ X0 lam0 : ℝ} {ε1 : ℝ → ℝ}
    (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (hXZ : X0m ≤ Z) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hlamS : lam0 ≤ 1.00003) (hy : X0m ≤ y) (hδ : 8 * y * H X0 ≤ X0 ^ 2)
    (hyN : 2 * y ≤ X0m * X0) :
    0 ≤ xbB P H tw X0m y X0 θ lam0 ∧ xbB P H tw X0m y X0 θ lam0 ≤ 5 / 12 := by
  have hP := h.width
  have hbs := h.hbs
  have hX := hP.X0m_pos
  have hy0 : 0 < y := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hlε := lam_eps_le hP.eps_nonneg hP.eps_le hlam0 hlamS
  have hX0pos : 0 < X0 := by
    have := hP.reg.pos X0; nlinarith
  constructor
  · rw [xbB_eq]; exact Finset.sum_nonneg fun n _ => xbTerm_nonneg hP hlam0 n
  refine xbB_le_of_near hP hbs hXZ hX0e hp2 hy0 hδ hyN (by norm_num) fun n hn hnear => ?_
  obtain ⟨hVn, hclose⟩ := val_near hP hbs hXZ hX0e hy0 hδ hyN hn hnear
  obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
  have hn0 : n ≠ 0 := by omega
  have hnlt : (n : ℝ) < X0m := by
    have h1 : y / X0 ≤ X0m / 2 := by rw [div_le_iff₀ hX0pos]; linarith
    have := (abs_le.mp hclose).2
    have h7 : (10 : ℝ) ^ 7 ≤ X0m := hbs.X0m_ge
    linarith
  have hrat : ∀ m, m ∣ n → LemmaM.valN P.labelVal m = m := by
    intro m hm
    have hm0 : m ≠ 0 := fun h0 => by subst h0; simp at hm; omega
    have hle := KR.valN_dvd_le P hm hn0
    rw [hVn] at hle
    exact valN_eq_self P hbs hm0 (lt_of_le_of_lt hle hnlt) (by linarith)
  have hlam1 : lam0 ≤ 1.001 := by linarith
  exact (xbTerm_le_Br hP hp2 ht hlam hlam1 hy hn hrat).trans
    (BrN_le hP.eps_nonneg hP.eps_le hlam0 hlam1 hlε hn2)

end KR.XB7

end
