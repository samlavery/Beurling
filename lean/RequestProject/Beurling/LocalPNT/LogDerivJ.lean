module

public import RequestProject.Beurling.LocalPNT.Pole

/-!
# Step 3 of the proof of Theorem 5.24: the logarithmic derivative of `ζ^♯`

* `threeFour`: `∑_{k=0}^4 a_k Re(-ζ_J'/ζ_J)(σ + ikt) ≥ 0`, `(a_k) = (35, 56, 28, 8, 1)`, since
  `∑_k a_k cos kφ = 8 (1 + cos φ)^4` and `-ζ_J'/ζ_J` has non-negative Dirichlet coefficients;
* `logDeriv_zetaSharp`: `ζ^♯'/ζ^♯ = ζ_J'/ζ_J + (1+g)'/(1+g)` on `σ > 1`;
* `norm_logDeriv_g_le`: `|(1+g)'/(1+g)(s)| ≤ 4/(η log⁴ y)` for `σ = 1 + η`,
  `16 log log y/log y ≤ η ≤ 1/2` (Cauchy's estimate on the circle of radius `η/2`).
-/

@[expose] public section

open Set Real Complex Metric Construction

namespace LocalPNT

/-- `35 + 56 cos φ + 28 cos 2φ + 8 cos 3φ + cos 4φ = 8 (1 + cos φ)^4`. -/
lemma cos_poly (φ : ℝ) :
    35 + 56 * Real.cos φ + 28 * Real.cos (2 * φ) + 8 * Real.cos (3 * φ) + Real.cos (4 * φ) =
      8 * (1 + Real.cos φ) ^ 4 := by
  have h2 := Real.cos_two_mul φ
  have h3 := Real.cos_three_mul φ
  have h4 : Real.cos (4 * φ) = 2 * Real.cos (2 * φ) ^ 2 - 1 := by
    rw [show 4 * φ = 2 * (2 * φ) by ring, Real.cos_two_mul]
  rw [h4, h2, h3]; ring

/-- `Re(x^{-s}) = x^{-σ} cos(t log x)` for `x > 0`. -/
lemma re_cpow_neg {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (((x : ℝ) : ℂ) ^ (-s)).re = x ^ (-s.re) * Real.cos (s.im * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.exp_re,
    ← Complex.ofReal_log hx.le]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, zero_mul, sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hx, show Real.log x * -s.im = -(s.im * Real.log x) by ring,
    Real.cos_neg, mul_comm (Real.log x) (-s.re)]

/-- The weights `(35, 56, 28, 8, 1)`. -/
def aw : ℕ → ℝ
  | 0 => 35
  | 1 => 56
  | 2 => 28
  | 3 => 8
  | 4 => 1
  | _ => 0

lemma aw_sum : ∑ k ∈ Finset.range 5, aw k = 128 := by
  simp [Finset.sum_range_succ, aw]; norm_num

lemma aw_nonneg (k : ℕ) : 0 ≤ aw k := by
  match k with
  | 0 => norm_num [aw]
  | 1 => norm_num [aw]
  | 2 => norm_num [aw]
  | 3 => norm_num [aw]
  | 4 => norm_num [aw]
  | n + 5 => simp [aw]

lemma aw_cos (φ : ℝ) :
    ∑ k ∈ Finset.range 5, aw k * Real.cos (k * φ) = 8 * (1 + Real.cos φ) ^ 4 := by
  rw [← cos_poly]
  simp [Finset.sum_range_succ, aw]

/-- **The 3-4 inequality for `ζ_J`**: `∑_k a_k Re(-ζ_J'/ζ_J)(σ + ikt) ≥ 0`. -/
theorem threeFour (P : BeurlingSystem) (J : Finset ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    0 ≤ ∑ k ∈ Finset.range 5, aw k *
      (-(deriv (zetaF P J) (σ + k * t * I) / zetaF P J (σ + k * t * I))).re := by
  have hsk : ∀ k : ℕ, 0 < ((σ : ℂ) + k * t * I).re := by intro k; simpa using hσ
  -- each fiber
  have hfib : ∀ k : ℕ, ∀ j ∈ J, HasSum (fun m : ℕ => Real.log (P.p j) *
      ((P.p j ^ (m + 1)) ^ (-σ) * Real.cos ((k * t) * Real.log (P.p j ^ (m + 1)))))
      ((Real.log (P.p j) : ℂ) * ((P.p j : ℝ) : ℂ) ^ (-((σ : ℂ) + k * t * I)) /
        (1 - ((P.p j : ℝ) : ℂ) ^ (-((σ : ℂ) + k * t * I)))).re := by
    intro k j _
    have h := ((hasSum_logFactor P j (hsk k)).mul_left (Real.log (P.p j) : ℂ))
    have hre := Complex.reCLM.hasSum h
    convert! hre using 1
    · funext m
      simp only [Complex.reCLM_apply]
      rw [Complex.re_ofReal_mul, re_cpow_neg (pow_pos (P.p_pos j) _)]
      simp
    · simp only [Complex.reCLM_apply]; ring_nf
  have hk : ∀ k : ℕ, (-(deriv (zetaF P J) (σ + k * t * I) / zetaF P J (σ + k * t * I))).re =
      ∑ j ∈ J, ∑' m : ℕ, Real.log (P.p j) *
        ((P.p j ^ (m + 1)) ^ (-σ) * Real.cos ((k * t) * Real.log (P.p j ^ (m + 1)))) := by
    intro k
    rw [logDeriv_zetaF P J (hsk k), neg_neg, Complex.re_sum]
    exact Finset.sum_congr rfl fun j hj => ((hfib k j hj).tsum_eq).symm
  simp_rw [hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun j hj => ?_
  have hsum : HasSum (fun m : ℕ => ∑ k ∈ Finset.range 5, aw k * (Real.log (P.p j) *
      ((P.p j ^ (m + 1)) ^ (-σ) * Real.cos ((k * t) * Real.log (P.p j ^ (m + 1))))))
      (∑ k ∈ Finset.range 5, aw k * ∑' m : ℕ, Real.log (P.p j) *
        ((P.p j ^ (m + 1)) ^ (-σ) * Real.cos ((k * t) * Real.log (P.p j ^ (m + 1))))) := by
    apply hasSum_sum
    intro k _
    exact ((hfib k j hj).summable.hasSum).mul_left _
  refine hsum.nonneg fun m => ?_
  have e : ∑ k ∈ Finset.range 5, aw k * (Real.log (P.p j) *
      ((P.p j ^ (m + 1)) ^ (-σ) * Real.cos ((k * t) * Real.log (P.p j ^ (m + 1))))) =
      Real.log (P.p j) * (P.p j ^ (m + 1)) ^ (-σ) *
        ∑ k ∈ Finset.range 5, aw k * Real.cos (k * (t * Real.log (P.p j ^ (m + 1)))) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring_nf
  rw [e, aw_cos]
  have := P.log_p_nonneg j
  have := Real.rpow_nonneg (pow_pos (P.p_pos j) (m + 1)).le (-σ)
  positivity

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

lemma differentiableAt_gJ {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (gJ P θ X₀ α γ xp y) s := by
  have hs1 : s ≠ 1 := by intro e; rw [e] at hs; simp at hs
  have h1 := h.differentiableAt_zetaSharp (s := s) (by linarith [h.theta_mem.2]) hs1
  have hO : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 := (differentiableOn_zetaF P (P.primesLe y)).differentiableAt
    (hO.mem_nhds (show 0 < s.re by linarith))
  exact (h1.sub h2).div h2 (zetaF_ne_zero P _ (by linarith))

lemma zetaSharp_eq_mul {s : ℂ} (hs : 0 < s.re) :
    zetaSharp P θ X₀ α γ xp y s = zetaF P (P.primesLe y) s * (1 + gJ P θ X₀ α γ xp y s) := by
  unfold gJ
  have := zetaF_ne_zero P (P.primesLe y) hs
  field_simp
  ring

/-- `ζ^♯'/ζ^♯ = ζ_J'/ζ_J + (1+g)'/(1+g)` where `1 + g ≠ 0`. -/
theorem logDeriv_zetaSharp {s : ℂ} (hs : 1 < s.re) (hg : 1 + gJ P θ X₀ α γ xp y s ≠ 0) :
    logDeriv (zetaSharp P θ X₀ α γ xp y) s =
      logDeriv (zetaF P (P.primesLe y)) s + logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s := by
  have hO : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : zetaSharp P θ X₀ α γ xp y =ᶠ[nhds s]
      fun z => zetaF P (P.primesLe y) z * (1 + gJ P θ X₀ α γ xp y z) := by
    filter_upwards [hO.mem_nhds hs] with z hz
    exact h.zetaSharp_eq_mul (by have : 1 < z.re := hz; linarith)
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply]
  have hO0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact logDeriv_mul s (zetaF_ne_zero P _ (by linarith)) hg
    ((differentiableOn_zetaF P (P.primesLe y)).differentiableAt
      (hO0.mem_nhds (show 0 < s.re by linarith)))
    ((differentiableAt_const _).add (h.differentiableAt_gJ hs))

/-- **The derivative of `log(1 + g)`**: `|(1+g)'/(1+g)(s)| ≤ 4/(η log⁴ y)` for `σ = 1 + η`,
`16 log log y/log y ≤ η ≤ 1/2`. -/
theorem norm_logDeriv_g_le {s : ℂ}
    (hs1 : 1 + 16 * Real.log (Real.log y) / Real.log y ≤ s.re) (hs2 : s.re ≤ 3 / 2) :
    1 + gJ P θ X₀ α γ xp y s ≠ 0 ∧
    ‖logDeriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s‖ * ((s.re - 1) * Real.log y ^ 4) ≤ 4 := by
  set L := Real.log y
  have hL := h.logy_ge
  have hL0 : 0 < L := by linarith
  have hLL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set η := s.re - 1
  have hη0 : 0 < η := by
    have : 0 ≤ 16 * Real.log L / L := by positivity
    have : 0 < 16 * Real.log L / L := by
      apply div_pos _ hL0
      have : 0 < Real.log L := Real.log_pos (by linarith)
      linarith
    linarith
  -- on the circle `|z - s| = η/2`: `8 log log y/log y ≤ re z - 1` and `re z ≤ 2`
  have hcirc : ∀ z ∈ closedBall s (η / 2), 1 + 8 * Real.log L / L ≤ z.re ∧ z.re ≤ 2 := by
    intro z hz
    have hre : |z.re - s.re| ≤ η / 2 := by
      have := Complex.abs_re_le_norm (z - s)
      rw [mem_closedBall, dist_eq_norm] at hz
      simp only [Complex.sub_re] at this
      linarith
    have hh : 8 * Real.log L / L ≤ η / 2 := by
      have : 16 * Real.log L / L ≤ η := by linarith
      have e : 8 * Real.log L / L = (16 * Real.log L / L) / 2 := by ring
      linarith
    constructor <;> linarith [abs_le.mp hre]
  have hgbound : ∀ z ∈ closedBall s (η / 2), ‖gJ P θ X₀ α γ xp y z‖ ≤ 1 / L ^ 4 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hcirc z hz
    have := h.norm_g_le h1 h2
    rw [le_div_iff₀ (by positivity)]; exact this
  have hL4 : 1 / L ^ 4 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pow_le_pow_left₀ (by norm_num)
      (show (2 : ℝ) ≤ L by linarith) 4]
  have hsmem : s ∈ closedBall s (η / 2) := mem_closedBall_self (by linarith)
  have hgs := hgbound s hsmem
  have hne : 1 + gJ P θ X₀ α γ xp y s ≠ 0 := by
    intro e
    have : gJ P θ X₀ α γ xp y s = -1 := by linear_combination e
    rw [this, norm_neg, norm_one] at hgs; linarith
  refine ⟨hne, ?_⟩
  -- Cauchy's estimate for `g` on the circle of radius `η/2`
  have hdiff : DiffContOnCl ℂ (gJ P θ X₀ α γ xp y) (ball s (η / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    intro z hz
    rw [closure_ball _ (show (0 : ℝ) < η / 2 by linarith).ne'] at hz
    have := (hcirc z hz).1
    have : 1 < z.re := by
      have : 0 < 8 * Real.log L / L := by
        have := Real.log_pos (show (1 : ℝ) < L by linarith); positivity
      linarith
    exact (h.differentiableAt_gJ this).differentiableWithinAt
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hdiff
    (fun z hz => hgbound z (sphere_subset_closedBall hz))
  have hderiv : deriv (fun z => 1 + gJ P θ X₀ α γ xp y z) s = deriv (gJ P θ X₀ α γ xp y) s := by
    simp
  rw [logDeriv_apply, hderiv, norm_div]
  have hden : 1 / 2 ≤ ‖1 + gJ P θ X₀ α γ xp y s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-gJ P θ X₀ α γ xp y s)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hL4' : 0 < L ^ 4 := by positivity
  calc ‖deriv (gJ P θ X₀ α γ xp y) s‖ / ‖1 + gJ P θ X₀ α γ xp y s‖ * (η * L ^ 4)
      ≤ (1 / L ^ 4 / (η / 2)) / (1 / 2) * (η * L ^ 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div₀ (by positivity) hcauchy (by norm_num) hden
    _ = 4 := by field_simp; norm_num

end LPHyp

end LocalPNT

end
