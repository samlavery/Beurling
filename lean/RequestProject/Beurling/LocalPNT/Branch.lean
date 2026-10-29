module

public import RequestProject.Beurling.LocalPNT.ZeroFree
public import RequestProject.Beurling.LocalPNT.RectLog

/-!
# Step 8 of the proof of Theorem 5.24: the function `𝔊₁ = log(ζ^♯(s)(s-1)/s)`

* `gfun = (s - 1) ζ^♯(s)/s`, extended by `1` at `s = 1`, is holomorphic near `1`
  (removable singularity, `|(s-1)ζ^♯(s) - 1| ≤ 4|s - 1|`);
* on `σ > 1 + 8 log log y/log y` it has the explicit logarithm
  `Gright = ∑_{p_j ≤ y} -log(1 - p_j^{-s}) + log(1 + g) + log((s-1)/s)` (principal logarithms);
  this is the branch "real on `(1, ∞)`" of the paper.
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology

namespace LocalPNT

/-- `gfun(s) = (s - 1) ζ^♯(s)/s`, with the value `1` at `s = 1`. -/
noncomputable def gfun (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ) :
    ℂ → ℂ :=
  Function.update (fun s => (s - 1) * zetaSharp P θ X₀ α γ xp y s / s) 1 1

/-- `log ζ_J(s) = ∑_{p_j ≤ y} -log(1 - p_j^{-s})`. -/
noncomputable def LJ (P : BeurlingSystem) (y : ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ P.primesLe y, -Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s))

/-- The branch of `log gfun` on the right: `log ζ_J + log(1 + g) + log((s-1)/s)`. -/
noncomputable def Gright (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ)
    (s : ℂ) : ℂ :=
  LJ P y s + Complex.log (1 + gJ P θ X₀ α γ xp y s) + Complex.log ((s - 1) / s)

lemma one_sub_cpow_re_pos (P : BeurlingSystem) (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 < (1 - ((P.p j : ℝ) : ℂ) ^ (-s)).re := by
  have h1 := Complex.re_le_norm (((P.p j : ℝ) : ℂ) ^ (-s))
  have h2 := norm_p_cpow_neg_lt_one P j hs
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma exp_LJ (P : BeurlingSystem) (y : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (LJ P y s) = zetaF P (P.primesLe y) s := by
  unfold LJ zetaF
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.exp_neg, Complex.exp_log (one_sub_p_cpow_ne_zero P j hs)]

lemma differentiableAt_LJ (P : BeurlingSystem) (y : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (LJ P y) s := by
  unfold LJ
  refine DifferentiableAt.fun_sum fun j _ => ?_
  refine (DifferentiableAt.clog ?_ ?_).neg
  · exact (hasDerivAt_factor P j s).differentiableAt
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_cpow_re_pos P j hs))

/-- `Re((s - 1)/s) > 0` for `Re s > 1`. -/
lemma re_sub_one_div_pos {s : ℂ} (hs : 1 < s.re) : 0 < ((s - 1) / s).re := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at hs; simp at hs; linarith
  rw [Complex.div_re]
  have hn : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs0
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [← add_div]
  apply div_pos _ hn
  have : Complex.normSq s = s.re * s.re + s.im * s.im := Complex.normSq_apply s
  nlinarith [sq_nonneg s.im]

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma one_le_re_of_ball {s : ℂ} (hs : s ∈ ball (1 : ℂ) (1 / Real.log X₀)) :
    1 - 8 / Real.log X₀ ≤ s.re ∧ 15 / 16 < s.re ∧ ‖s - 1‖ < 1 / 16 := by
  have hX := h.logX
  rw [mem_ball, dist_eq_norm] at hs
  have := Complex.abs_re_le_norm (s - 1)
  simp only [Complex.sub_re, Complex.one_re] at this
  have h1 : 1 / Real.log X₀ ≤ 1 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
    (by norm_num) hX
  have h2 : 1 / Real.log X₀ ≤ 8 / Real.log X₀ :=
    div_le_div_of_nonneg_right (by norm_num) (by linarith)
  refine ⟨?_, ?_, by linarith⟩
  · linarith [(abs_lt.mp (lt_of_le_of_lt this hs)).1]
  · linarith [(abs_lt.mp (lt_of_le_of_lt this hs)).1]

/-- **`gfun` is holomorphic near `1`** (removable singularity). -/
theorem differentiableOn_gfun_ball :
    DifferentiableOn ℂ (gfun P θ X₀ α γ xp y) (ball (1 : ℂ) (1 / Real.log X₀)) := by
  set f : ℂ → ℂ := fun s => (s - 1) * zetaSharp P θ X₀ α γ xp y s / s
  have hX := h.logX
  have h8 : 8 / Real.log X₀ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
    (by norm_num) hX
  have hd : DifferentiableOn ℂ f (ball (1 : ℂ) (1 / Real.log X₀) \ {1}) := by
    intro s hs
    obtain ⟨-, h1, -⟩ := h.one_le_re_of_ball hs.1
    have hs1 : s ≠ 1 := hs.2
    have hs0 : s ≠ 0 := by intro e; rw [e] at h1; simp at h1; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_id.sub_const 1).mul (h.differentiableAt_zetaSharp
      (by linarith [h.theta_mem.2]) hs1)).div differentiableAt_id hs0
  have hbound : ∀ s ∈ ball (1 : ℂ) (1 / Real.log X₀) \ {1}, ‖f s - 1‖ ≤ 1 := by
    intro s hs
    obtain ⟨h0, h1, h2⟩ := h.one_le_re_of_ball hs.1
    have hs0 : s ≠ 0 := by intro e; rw [e] at h1; simp at h1; linarith
    have hnp := h.near_pole' (s := s) h0 (by linarith) hs.2
    have hsn : 15 / 16 ≤ ‖s‖ := by
      have := Complex.re_le_norm s; linarith
    simp only [f]
    have e : (s - 1) * zetaSharp P θ X₀ α γ xp y s / s - 1 =
        ((s - 1) * zetaSharp P θ X₀ α γ xp y s - 1) / s + (1 - s) / s := by
      field_simp; ring
    rw [e]
    calc _ ≤ ‖((s - 1) * zetaSharp P θ X₀ α γ xp y s - 1) / s‖ + ‖(1 - s) / s‖ :=
          norm_add_le _ _
      _ = ‖(s - 1) * zetaSharp P θ X₀ α γ xp y s - 1‖ / ‖s‖ + ‖s - 1‖ / ‖s‖ := by
          rw [norm_div, norm_div, norm_sub_rev 1 s]
      _ ≤ (4 * (1 / 16)) / (15 / 16) + (1 / 16) / (15 / 16) := by
          gcongr <;> linarith
      _ ≤ 1 := by norm_num
  have hb : BddAbove (norm ∘ f '' (ball (1 : ℂ) (1 / Real.log X₀) \ {1})) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := hbound s hs
    have := norm_sub_norm_le (f s) 1
    simp only [Function.comp_apply, norm_one] at *
    linarith
  have hD := differentiableOn_update_limUnder_of_bddAbove
    (ball_mem_nhds 1 (by have : 0 < Real.log X₀ := by linarith
                         positivity)) hd hb
  -- the limit is `1`
  have htend : Tendsto f (𝓝[≠] 1) (𝓝 1) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hΛ0 : 0 < Real.log X₀ := by linarith
    refine ⟨min (1 / Real.log X₀) (ε / 6), by positivity, fun s hs hds => ?_⟩
    have hsb : s ∈ ball (1 : ℂ) (1 / Real.log X₀) := by
      rw [mem_ball]; exact lt_of_lt_of_le hds (min_le_left _ _)
    obtain ⟨h0, h1, h2⟩ := h.one_le_re_of_ball hsb
    have hs0 : s ≠ 0 := by intro e; rw [e] at h1; simp at h1; linarith
    have hnp := h.near_pole' (s := s) h0 (by linarith) hs
    have hsn : 15 / 16 ≤ ‖s‖ := by
      have := Complex.re_le_norm s; linarith
    have hd' : ‖s - 1‖ < ε / 6 := by
      rw [dist_eq_norm] at hds; exact lt_of_lt_of_le hds (min_le_right _ _)
    rw [dist_eq_norm]
    simp only [f]
    have e : (s - 1) * zetaSharp P θ X₀ α γ xp y s / s - 1 =
        ((s - 1) * zetaSharp P θ X₀ α γ xp y s - 1) / s + (1 - s) / s := by
      field_simp; ring
    rw [e]
    calc _ ≤ ‖((s - 1) * zetaSharp P θ X₀ α γ xp y s - 1) / s‖ + ‖(1 - s) / s‖ :=
          norm_add_le _ _
      _ = ‖(s - 1) * zetaSharp P θ X₀ α γ xp y s - 1‖ / ‖s‖ + ‖s - 1‖ / ‖s‖ := by
          rw [norm_div, norm_div, norm_sub_rev 1 s]
      _ ≤ (4 * ‖s - 1‖) / (15 / 16) + ‖s - 1‖ / (15 / 16) := by gcongr <;> linarith
      _ = 16 / 3 * ‖s - 1‖ := by ring
      _ < ε := by nlinarith [norm_nonneg (s - 1)]
  rw [htend.limUnder_eq] at hD
  exact hD

/-- `gfun` is holomorphic at `s ≠ 1` with `σ > θ + 2/5`. -/
theorem differentiableAt_gfun {s : ℂ} (hs : θ + 2 / 5 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (gfun P θ X₀ α γ xp y) s := by
  have hs0 : s ≠ 0 := by
    intro e; rw [e] at hs; simp at hs; linarith [h.theta_mem.1]
  have hf : DifferentiableAt ℂ (fun s => (s - 1) * zetaSharp P θ X₀ α γ xp y s / s) s :=
    ((differentiableAt_id.sub_const 1).mul (h.differentiableAt_zetaSharp hs hs1)).div
      differentiableAt_id hs0
  refine hf.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
  simp only [gfun, Function.update_of_ne hz]

/-- `exp(Gright) = gfun` on `1 + 8 log log y/log y ≤ σ ≤ 2`. -/
theorem exp_Gright {s : ℂ} (hs1 : 1 + 8 * Real.log (Real.log y) / Real.log y ≤ s.re)
    (hs2 : s.re ≤ 2) :
    Complex.exp (Gright P θ X₀ α γ xp y s) = gfun P θ X₀ α γ xp y s := by
  have hL := h.logy_ge
  have hσ : 1 < s.re := by
    have : 0 < 8 * Real.log (Real.log y) / Real.log y :=
      div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
    linarith
  have hs0 : s ≠ 0 := by intro e; rw [e] at hσ; simp at hσ; linarith
  have hs1' : s ≠ 1 := by intro e; rw [e] at hσ; simp at hσ
  have hg := h.norm_g_le hs1 hs2
  have hL4 : (10 : ℝ) ^ 32 ≤ Real.log y ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg1 : ‖gJ P θ X₀ α γ xp y s‖ < 1 := by
    by_contra hc; push_neg at hc
    nlinarith
  have hne : 1 + gJ P θ X₀ α γ xp y s ≠ 0 := by
    intro e
    have : gJ P θ X₀ α γ xp y s = -1 := by linear_combination e
    rw [this, norm_neg, norm_one] at hg1; exact lt_irrefl _ hg1
  have hw : (s - 1) / s ≠ 0 := div_ne_zero (sub_ne_zero.mpr hs1') hs0
  unfold Gright
  rw [Complex.exp_add, Complex.exp_add, exp_LJ P y (by linarith), Complex.exp_log hne,
    Complex.exp_log hw, gfun, Function.update_of_ne hs1', ← h.zetaSharp_eq_mul (by linarith)]
  field_simp

/-- `Gright` is holomorphic on `1 + 8 log log y/log y < σ < 2`. -/
theorem differentiableAt_Gright {s : ℂ}
    (hs1 : 1 + 8 * Real.log (Real.log y) / Real.log y < s.re) (hs2 : s.re < 2) :
    DifferentiableAt ℂ (Gright P θ X₀ α γ xp y) s := by
  have hL := h.logy_ge
  have hσ : 1 < s.re := by
    have : 0 < 8 * Real.log (Real.log y) / Real.log y :=
      div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
    linarith
  have hs0 : s ≠ 0 := by intro e; rw [e] at hσ; simp at hσ; linarith
  have hg := h.norm_g_le hs1.le hs2.le
  have hL4 : (10 : ℝ) ^ 32 ≤ Real.log y ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg1 : ‖gJ P θ X₀ α γ xp y s‖ < 1 := by
    by_contra hc; push_neg at hc
    nlinarith
  have hre : 0 < (1 + gJ P θ X₀ α γ xp y s).re := by
    have := Complex.abs_re_le_norm (gJ P θ X₀ α γ xp y s)
    simp only [Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp this).1]
  unfold Gright
  refine ((differentiableAt_LJ P y (by linarith)).add ?_).add ?_
  · exact ((differentiableAt_const 1).add (h.differentiableAt_gJ hσ)).clog
      (Complex.mem_slitPlane_iff.mpr (Or.inl hre))
  · exact ((differentiableAt_id.sub_const 1).div differentiableAt_id hs0).clog
      (Complex.mem_slitPlane_iff.mpr (Or.inl (re_sub_one_div_pos hσ)))

end LPHyp

end LocalPNT

end
