module

public import RequestProject.Beurling.DirichletSumBound
public import RequestProject.Beurling.Lemma48ZB
public import RequestProject.Beurling.AbsorbedL2

/-!
# Lemma 4.8(ii): the `L²` bound from the decomposition of `D̂_{<a_k}`

In the proof of Lemma 4.8(ii), `f = D̂_{<a_k}` is written (by (6)) as the Dirichlet sum `S` over the
residual elements `B ∩ [X₀⁻, a_k)` (counted with multiplicity) plus the integrals of `1`, `ρ_det`,
`R'` and `ρ̄_A`. The bound for `S` is now proved (`dirichlet_sum_box`); here it is combined with the
other pieces by Minkowski's inequality:

* `box_pointwise` : a pointwise bound `|h| ≤ M` on `Q` gives `∬_Q |h|² ≤ (1/2)(Γ + 1/2) M²`
  (this is how the paper bounds the `1`, `ρ_det` and `R'` parts);
* `box_add` : Minkowski's inequality for two functions;
* `lemma_4_8_ii_L2` : the `L²` bound `∬_Q |f|² ≤ 144 X₀^{-3/8} Γ` of Lemma 4.8(ii) from the
  decomposition `f = S + h` on `Q` with the counting hypotheses on the residual elements and an
  `L²` bound `∬_Q |h|² ≤ H²` for the rest;
* `lemma_4_8_ZB_of_decomposition` : Lemma 4.8 for the concrete base factor from these inputs;
* `lemma_4_8_ii_L2_of_pieces`, `lemma_4_8_ZB_of_pieces` : the same with the rest `h` split as in the
  paper into a pointwise bounded part (the `1`, `ρ_det` and `R'` parts, `|p| ≤ M` on `Q`) and the
  `ρ̄_A` part `∫_α^β w(u) e^{(1-s)u} du` with `|w| ≤ c` (bounded by `box_fourier_part`).
-/

@[expose] public section

open Complex MeasureTheory Set Finset GoodHeights Metric

namespace GoodHeights

/-- A pointwise bound `|h| ≤ M` on `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]` (with `Γ ≥ 0`) gives
`∬_Q |h|² ≤ (1/2)(Γ + 1/2) M²`. -/
theorem box_pointwise {h : ℂ → ℂ} {Γ M : ℝ} (hΓ : 0 ≤ Γ)
    (hM : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), ‖h z‖ ≤ M) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖h z‖ ^ 2) ≤
      ENNReal.ofReal (1 / 2 * (Γ + 1 / 2) * M ^ 2) := by
  have hvol : volume (box (Γ - 1 / 4) (2 * Γ + 1 / 4)) = ENNReal.ofReal (1 / 2 * (Γ + 1 / 2)) := by
    have := lintegral_box_eq (F := fun _ => (1 : ENNReal)) measurable_const (Γ - 1 / 4)
      (2 * Γ + 1 / 4)
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc, one_mul] at this
    rw [this, ← ENNReal.ofReal_mul (by linarith)]
    congr 1; ring
  calc ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖h z‖ ^ 2)
      ≤ ∫⁻ _z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (M ^ 2) := by
        apply setLIntegral_mono' (measurableSet_box _ _)
        intro z hz
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM z hz) 2)
    _ = ENNReal.ofReal (1 / 2 * (Γ + 1 / 2) * M ^ 2) := by
        rw [setLIntegral_const, hvol, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

/-- Minkowski's inequality for two functions on a set `Q`. -/
theorem box_add {a b : ℂ → ℂ} (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) (Q : Set ℂ)
    (hQa : ∫⁻ z in Q, ENNReal.ofReal (‖a z‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (hQb : ∫⁻ z in Q, ENNReal.ofReal (‖b z‖ ^ 2) ≤ ENNReal.ofReal (B ^ 2)) :
    ∫⁻ z in Q, ENNReal.ofReal (‖a z + b z‖ ^ 2) ≤ ENNReal.ofReal ((A + B) ^ 2) := by
  have := box_minkowski (ι := Bool) Finset.univ (g := fun j => if j then a else b)
    (fun j => by cases j <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption)
    (c := fun j => if j then A else B)
    (fun j _ => by cases j <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption) Q
    (fun j _ => by cases j <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption)
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at this
  exact this

/-- **The `L²` bound of Lemma 4.8(ii) from the decomposition.** Let `f` be a function with
`f = S + h` on `Q = [3/4, 5/4] × [Γ - 1/4, 2Γ + 1/4]`, where `S(s) = ∑_i n_i^{-s}` is the Dirichlet
sum over a list `n_0 ≤ … ≤ n_{m-1}` of reals in `[X, 2^J X]`, `X ≥ 2`, such that each window
`[n_i, n_i + 2]` contains at most `2 (n_i + 2)^η + 5` of them and each dyadic interval `(N, 2N]`
(`N ≥ 1`) at most `1.02 N`; and where `∬_Q |h|² ≤ H²`, `H > 0`. If
`25 √(Γ + 1/2) X^{η/2-1/4} + 40 (2^J X)^{η/2+1/4} + H ≤ C X₀^{-3/16} √Γ`, then
`∬_Q |f|² ≤ C² X₀^{-3/8} Γ` (the paper has `C = 12`). -/
theorem lemma_4_8_ii_L2 {f h : ℂ → ℂ} (hh : Measurable h) {m J : ℕ} {X η Γ H X₀ C : ℝ}
    (hX : 2 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hΓ : 0 ≤ Γ) (hX₀ : 0 < X₀)
    {n : Fin m → ℝ} (hmono : Monotone n)
    (hrange : ∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X)
    (hwin : ∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5)
    (hcount : ∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
      1.02 * N)
    (hdec : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) + h z)
    (hH : 0 < H)
    (hhb : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖h z‖ ^ 2) ≤
      ENNReal.ofReal (H ^ 2))
    (hnum : 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      H ≤ C * X₀ ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * X₀ ^ (-(3 / 8 : ℝ)) * Γ) := by
  have hn0 : ∀ i, 0 < n i := fun i => by linarith [(hrange i).1]
  set S : ℂ → ℂ := fun z => ∑ i, ((n i : ℝ) : ℂ) ^ (-z)
  have hSm : Measurable S := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (Continuous.measurable (continuous_const.cpow continuous_neg (fun _ => Or.inl (by
        simp only [Complex.ofReal_re]; exact hn0 i))))
  set A := 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4)
  have hX0 : 0 < X := by linarith
  have hA : 0 < A := by
    have : 0 < (2 ^ J * X) ^ (η / 2 + 1 / 4) := by positivity
    have : 0 ≤ 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) := by positivity
    simp only [A]; linarith
  have hS := dirichlet_sum_box hX hη0 hη hΓ hmono hrange hwin hcount
  have hsum := box_add hSm hh hA hH _ hS hhb
  calc ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2)
      = ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖S z + h z‖ ^ 2) :=
        setLIntegral_congr_fun (measurableSet_box _ _) (fun z hz => by rw [hdec z hz])
    _ ≤ ENNReal.ofReal ((A + H) ^ 2) := hsum
    _ ≤ ENNReal.ofReal (C ^ 2 * X₀ ^ (-(3 / 8 : ℝ)) * Γ) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (A + H) ^ 2 ≤ (C * X₀ ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hnum 2
        have h2 : (C * X₀ ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) ^ 2 =
            C ^ 2 * X₀ ^ (-(3 / 8 : ℝ)) * Γ := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hΓ, ← Real.rpow_mul_natCast hX₀.le]
          norm_num
        linarith

/-- **Lemma 4.8 for the concrete base factor with a weaker `L²` bound.** As `lemma_4_8_ZB`, but
with `∬_Q |f|² ≤ 10⁴ X₀^{-3/8} Γ` (i.e. `‖f‖ ≤ 100 X₀^{-3/16}`) in place of `144 X₀^{-3/8} Γ`, at the
cost of `X₀ ≥ e^{100}` in place of `X₀ ≥ e^{50}` (the paper has `X₀ ≥ e^{10^8}`). -/
theorem lemma_4_8_ZB_C {X₀ : ℕ} (hX : Real.exp 100 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hii : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (10 ^ 4 * (X₀ : ℝ) ^ (-(3 / 8 : ℝ)) * Γ)) :
    ENNReal.ofReal (0.018 * Γ) ≤ volume {γ ∈ Icc Γ (2 * Γ) |
      0.6 ≤ ‖BaseFactor.ZBcont X₀ κ (1 + γ * I)‖ ∧
        ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  have hX50 : Real.exp 50 ≤ (X₀ : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hX
  have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (Real.exp_pos _) hX
  set Y : ℝ := (X₀ : ℝ) / Real.exp 12
  have hY : Real.exp 50 ≤ Y := by
    simp only [Y]
    rw [le_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
    exact le_trans (Real.exp_le_exp.mpr (by norm_num)) hX
  have hYp : Y ^ (-(3 / 8 : ℝ)) = (X₀ : ℝ) ^ (-(3 / 8 : ℝ)) * Real.exp (9 / 2) := by
    simp only [Y]
    rw [Real.div_rpow hX0.le (Real.exp_pos _).le, ← Real.exp_mul, div_eq_mul_inv,
      ← Real.exp_neg]
    congr 2; norm_num
  have he : (70 : ℝ) ≤ Real.exp (9 / 2) := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp (9 / 2) = Real.exp 1 ^ 4 * Real.exp (1 / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h3 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
      have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
    rw [h2]
    have h4 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    nlinarith
  refine lemma_4_8 hf hΓ0 hY
    (ZMoments.lemma_4_8_i (twentyfour_le_of_exp_le hX50) hκ hκ1 hΓ) (hii.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [hYp]
  have : 0 ≤ (X₀ : ℝ) ^ (-(3 / 8 : ℝ)) * Γ := by positivity
  nlinarith

/-- **Lemma 4.8 for the concrete base factor, from the decomposition of `f = D̂_{<a_k}`.**
Under the hypotheses of `lemma_4_8_ii_L2` with `C = 100` (with `f` entire, `X₀ ≥ e^{100}` natural,
`0 < κ ≤ 1` and `κΓ ≥ e^{X₀²/3}`), the set `S_k` of `γ ∈ [Γ, 2Γ]` with `|Z_B(1+iγ)| ≥ 0.6` and
`|f| ≤ 1/16` on `|s - (1+iγ)| ≤ 1/8` has measure at least `0.018 Γ`. -/
theorem lemma_4_8_ZB_of_decomposition {X₀ : ℕ} (hX₀ : Real.exp 100 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hh : Measurable h) {m J : ℕ} {X η H : ℝ}
    (hX : 2 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    {n : Fin m → ℝ} (hmono : Monotone n)
    (hrange : ∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X)
    (hwin : ∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5)
    (hcount : ∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
      1.02 * N)
    (hdec : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) + h z)
    (hH : 0 < H)
    (hhb : ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖h z‖ ^ 2) ≤
      ENNReal.ofReal (H ^ 2))
    (hnum : 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      H ≤ 100 * (X₀ : ℝ) ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) :
    ENNReal.ofReal (0.018 * Γ) ≤ volume {γ ∈ Icc Γ (2 * Γ) |
      0.6 ≤ ‖BaseFactor.ZBcont X₀ κ (1 + γ * I)‖ ∧
        ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  have hX₀0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (Real.exp_pos _) hX₀
  refine lemma_4_8_ZB_C hX₀ hκ hκ1 hΓ hf ?_
  have := lemma_4_8_ii_L2 hh hX hη0 hη hΓ0.le hX₀0 hmono hrange hwin hcount hdec hH hhb hnum
  norm_num at this ⊢; exact this

/-- **The `L²` bound of Lemma 4.8(ii) from the five pieces.** As `lemma_4_8_ii_L2`, with the rest
split as `h = p + A` on `Q`, where `|p| ≤ M` on `Q` (the `1`, `ρ_det` and `R'` parts) and
`A(s) = ∫_α^β w(u) e^{(1-s)u} du` with `|w| ≤ c` on `[α, β]`, `0 ≤ α ≤ β` (the `ρ̄_A` part in the
variable `u = log x`). The numerical condition is
`25 √(Γ+1/2) X^{η/2-1/4} + 40 (2^J X)^{η/2+1/4} + √((Γ+1/2)/2) M
  + 2 √(1 + log((β-α)(Γ+1/2))) c e^{β/4} ≤ C X₀^{-3/16} √Γ`, and the conclusion
`∬_Q |f|² ≤ C² X₀^{-3/8} Γ`. -/
theorem lemma_4_8_ii_L2_of_pieces {f p : ℂ → ℂ} (hp : Measurable p) {w : ℝ → ℝ}
    (hw : Measurable w) {m J : ℕ} {X η Γ X₀ M c α β C : ℝ}
    (hX : 2 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hΓ : 0 ≤ Γ) (hX₀ : 0 < X₀)
    {n : Fin m → ℝ} (hmono : Monotone n)
    (hrange : ∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X)
    (hwin : ∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5)
    (hcount : ∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
      1.02 * N)
    (hM : 0 < M) (hpM : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), ‖p z‖ ≤ M)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hc : 0 < c) (hwc : ∀ u ∈ Icc α β, |w u| ≤ c)
    (hL : 1 ≤ (β - α) * (Γ + 1 / 2))
    (hdec : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) +
      (p z + ∫ u in Icc α β, (w u : ℂ) * cexp ((1 - z) * u)))
    (hnum : 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      (Real.sqrt ((Γ + 1 / 2) / 2) * M +
        2 * Real.sqrt (1 + Real.log ((β - α) * (Γ + 1 / 2))) * c * Real.exp (β / 4)) ≤
      C * X₀ ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) :
    ∫⁻ z in box (Γ - 1 / 4) (2 * Γ + 1 / 4), ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * X₀ ^ (-(3 / 8 : ℝ)) * Γ) := by
  set Q := box (Γ - 1 / 4) (2 * Γ + 1 / 4)
  set A : ℂ → ℂ := fun z => ∫ u in Icc α β, (w u : ℂ) * cexp ((1 - z) * u)
  have hAm : Measurable A := measurable_fourier_part hw α β
  set lg := 1 + Real.log ((β - α) * (Γ + 1 / 2))
  have hlg : 1 ≤ lg := by
    have := Real.log_nonneg hL; simp only [lg]; linarith
  set P1 := Real.sqrt ((Γ + 1 / 2) / 2) * M
  set P2 := 2 * Real.sqrt lg * c * Real.exp (β / 4)
  have hP1 : 0 < P1 := by simp only [P1]; positivity
  have hP2 : 0 < P2 := by
    have : 0 < Real.sqrt lg := Real.sqrt_pos.mpr (by linarith)
    simp only [P2]; positivity
  have hpb : ∫⁻ z in Q, ENNReal.ofReal (‖p z‖ ^ 2) ≤ ENNReal.ofReal (P1 ^ 2) := by
    refine (box_pointwise hΓ hpM).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [P1]
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hAb : ∫⁻ z in Q, ENNReal.ofReal (‖A z‖ ^ 2) ≤ ENNReal.ofReal (P2 ^ 2) := by
    refine (box_fourier_part hw hα hαβ hwc hΓ hL).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [P2]
    rw [show (2 * Real.sqrt lg * c * Real.exp (β / 4)) ^ 2 =
      4 * Real.sqrt lg ^ 2 * c ^ 2 * Real.exp (β / 4) ^ 2 by ring,
      Real.sq_sqrt (by linarith), ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hh := box_add hp hAm hP1 hP2 Q hpb hAb
  have hhm : Measurable fun z => p z + A z := hp.add hAm
  exact lemma_4_8_ii_L2 hhm hX hη0 hη hΓ hX₀ hmono hrange hwin hcount hdec (by positivity) hh hnum

/-- **Lemma 4.8 for the concrete base factor, from the five pieces of `D̂_{<a_k}`.** Under the
hypotheses of `lemma_4_8_ii_L2_of_pieces` with `C = 100` (with `f` entire, `X₀ ≥ e^{100}` natural,
`0 < κ ≤ 1` and
`κΓ ≥ e^{X₀²/3}`), the set `S_k` has measure at least `0.018 Γ`. -/
theorem lemma_4_8_ZB_of_pieces {X₀ : ℕ} (hX₀ : Real.exp 100 ≤ X₀) {κ Γ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hΓ : Real.exp ((X₀ : ℝ) ^ 2 / 3) ≤ κ * Γ) {f p : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hp : Measurable p) {w : ℝ → ℝ}
    (hw : Measurable w) {m J : ℕ} {X η M c α β : ℝ}
    (hX : 2 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8)
    {n : Fin m → ℝ} (hmono : Monotone n)
    (hrange : ∀ i, X ≤ n i ∧ n i ≤ 2 ^ J * X)
    (hwin : ∀ i, ((univ.filter (fun k => n i ≤ n k ∧ n k ≤ n i + 2)).card : ℝ) ≤
      2 * (n i + 2) ^ η + 5)
    (hcount : ∀ N : ℝ, 1 ≤ N → ((univ.filter (fun k => N < n k ∧ n k ≤ 2 * N)).card : ℝ) ≤
      1.02 * N)
    (hM : 0 < M) (hpM : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), ‖p z‖ ≤ M)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hc : 0 < c) (hwc : ∀ u ∈ Icc α β, |w u| ≤ c)
    (hL : 1 ≤ (β - α) * (Γ + 1 / 2))
    (hdec : ∀ z ∈ box (Γ - 1 / 4) (2 * Γ + 1 / 4), f z = ∑ i, ((n i : ℝ) : ℂ) ^ (-z) +
      (p z + ∫ u in Icc α β, (w u : ℂ) * cexp ((1 - z) * u)))
    (hnum : 25 * Real.sqrt (Γ + 1 / 2) * X ^ (η / 2 - 1 / 4) + 40 * (2 ^ J * X) ^ (η / 2 + 1 / 4) +
      (Real.sqrt ((Γ + 1 / 2) / 2) * M +
        2 * Real.sqrt (1 + Real.log ((β - α) * (Γ + 1 / 2))) * c * Real.exp (β / 4)) ≤
      100 * (X₀ : ℝ) ^ (-(3 / 16 : ℝ)) * Real.sqrt Γ) :
    ENNReal.ofReal (0.018 * Γ) ≤ volume {γ ∈ Icc Γ (2 * Γ) |
      0.6 ≤ ‖BaseFactor.ZBcont X₀ κ (1 + γ * I)‖ ∧
        ∀ s ∈ closedBall (1 + γ * I) (1 / 8), ‖f s‖ ≤ 1 / 16} := by
  have hΓ0 : 0 < Γ := by
    have := lt_of_lt_of_le (Real.exp_pos _) hΓ
    exact pos_of_mul_pos_right this hκ.le
  have hX₀0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (Real.exp_pos _) hX₀
  refine lemma_4_8_ZB_C hX₀ hκ hκ1 hΓ hf ?_
  have := lemma_4_8_ii_L2_of_pieces hp hw hX hη0 hη hΓ0.le hX₀0
    hmono hrange hwin hcount hM hpM hα hαβ hc hwc hL hdec hnum
  norm_num at this ⊢; exact this

end GoodHeights

end
