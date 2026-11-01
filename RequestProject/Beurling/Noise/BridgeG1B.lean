module

public import RequestProject.Beurling.LocalPNT.Theorem524
public import RequestProject.BSCert.Dickman

/-!
# Proposition 5.35 (positivity of the sharp reference), range (B)

Range (B) is `x ≥ X_sw`, `log X_sw = X₀^{1/100}`. Proved here:

* `G1B.range_fit` : the ranges fit (the paper's Remark after Proposition 5.35 and the start of
  the proof): `X₀^{1.01} ≤ X_sw` and `log X_LP = 10⁵Λ² log²Λ ≤ log X_sw`, for `Λ = log X₀ ≥ 10⁸`;
* `G1B.pi0Dens_antitone` : the density `π₀(u) = (1 - 1/u)/log u` decreases on `(1, ∞)`;
* `G1B.step1_window` : **Step 1, second bullet**, from Theorem 5.24(ii) (`LocalPNT`):
  for `J = [x(1-2δ), x(1-δ)]` above `X_LP` and below the certified height `y`,
  `Π(J) ≥ δ x π₀(x) - 2K x e^{-c_LP √(log x(1-2δ))}`; and the resulting lower bound for the
  `J`-average of `ρ̃` (`step1_avg`), given the local-count comparison of the first bullet;
* `G1B.step5` : **Step 5**: Steps 1–4 combine to `ρ^sh(x) log x ≥ 1 - 1/x - ε_N - E_BR - j - o`,
  and `≥ 0.97` with the paper's sizes (`ε_N ≤ 10⁻¹³`, Lemma 5.34; `E_BR ≤ e^{-76}`, (osc);
  `j_{X₀} ≤ e^{-59}`, Proposition 5.33; `o ≤ Λ⁻³`).

The inputs of Steps 2–4 (the bridge terms on `J`, the threshold changes via Lemma 5.23, the jump
at `X₀`, the smooth changes of `ρ_det` and of the resolvable `R'_j`, the current oscillation)
enter `step5` as the three averaged inequalities `h1`, `h2`, `h3`, each the conclusion of the
corresponding step of the paper.
-/

@[expose] public section

open Real Set MeasureTheory

namespace KR.G1B

/-! ## The ranges -/

/-- `X₀^{1.01} ≤ X_sw` and `log X_LP ≤ log X_sw`, `log X_sw = X₀^{1/100} = e^{Λ/100}`. -/
theorem range_fit {Λ : ℝ} (hΛ : 100000000 ≤ Λ) :
    1.01 * Λ ≤ Real.exp (Λ / 100) ∧ 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ Real.exp (Λ / 100) := by
  have hΛ0 : 0 < Λ := by linarith
  have h6 := Real.pow_div_factorial_le_exp (x := Λ / 100) (by positivity) 10
  have hlog : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
  have hlog0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hl2 : Real.log Λ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  norm_num [Nat.factorial] at h6
  have hΛ6 : (100000000 : ℝ) ^ 6 ≤ Λ ^ 6 := pow_le_pow_left₀ (by norm_num) hΛ 6
  have key : 10 ^ 5 * Λ ^ 4 ≤ Λ ^ 10 / 362880000000000000000000000 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 10 ^ 5 * 362880000000000000000000000 * Λ ^ 4 ≤ Λ ^ 6 * Λ ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
    nlinarith
  have e6 : (Λ / 100) ^ 10 / 3628800 = Λ ^ 10 / 362880000000000000000000000 := by ring
  constructor
  · nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 100000000) hΛ 2]
  · calc 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ 10 ^ 5 * Λ ^ 2 * Λ ^ 2 := by gcongr
      _ = 10 ^ 5 * Λ ^ 4 := by ring
      _ ≤ _ := key.trans (by rw [← e6]; exact h6)

/-! ## The density `π₀` -/

lemma pi0Dens_eq {u : ℝ} (hu : 1 < u) :
    LocalPNT.pi0Dens u = (1 - Real.exp (-Real.log u)) / Real.log u := by
  unfold LocalPNT.pi0Dens
  rw [Real.exp_neg, Real.exp_log (by linarith), one_div]

/-- `π₀(u) = (1 - 1/u)/log u` is non-increasing on `(1, ∞)`. -/
lemma pi0Dens_antitone {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    LocalPNT.pi0Dens v ≤ LocalPNT.pi0Dens u := by
  have hv : 1 < v := lt_of_lt_of_le hu huv
  rw [pi0Dens_eq hu, pi0Dens_eq hv]
  have ha := Real.log_pos hu
  have hab : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  have hm := BSCert.div_one_sub_exp_neg_mono ha hab
  have hb := lt_of_lt_of_le ha hab
  have hea : 0 < 1 - Real.exp (-Real.log u) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha); linarith
  have heb : 0 < 1 - Real.exp (-Real.log v) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb); linarith
  rw [div_le_div_iff₀ hea heb] at hm
  rw [div_le_div_iff₀ hb ha]
  linarith

lemma pi0Dens_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ LocalPNT.pi0Dens u := by
  unfold LocalPNT.pi0Dens
  apply div_nonneg _ (Real.log_nonneg hu)
  have : 1 / u ≤ 1 := by rw [div_le_one (by linarith)]; exact hu
  linarith

lemma pi0Dens_le_one {u : ℝ} (hu : 1 ≤ u) : LocalPNT.pi0Dens u ≤ 1 := by
  unfold LocalPNT.pi0Dens
  rcases eq_or_lt_of_le hu with h | h
  · subst h; simp
  have hl := Real.log_pos h
  rw [div_le_one hl]
  have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < u)
  rw [one_div]; linarith

lemma intervalIntegrable_pi0Dens {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable LocalPNT.pi0Dens volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ ?_
  · unfold LocalPNT.pi0Dens
    exact ((measurable_const.sub (measurable_const.div measurable_id)).div
      Real.measurable_log).aestronglyMeasurable
  · rw [Set.uIoc_of_le hab]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu1 : 1 ≤ u := le_trans ha hu.1.le
    simp only [Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (pi0Dens_nonneg hu1)]
    exact pi0Dens_le_one hu1

/-- `Π₀(b) - Π₀(a) ≥ (b - a) π₀(b)` for `1 < a ≤ b`. -/
lemma pi0_sub_ge {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) * LocalPNT.pi0Dens b ≤ LocalPNT.pi0 b - LocalPNT.pi0 a := by
  unfold LocalPNT.pi0
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_pi0Dens le_rfl (by linarith)) (intervalIntegrable_pi0Dens le_rfl ha.le)]
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_pi0Dens ha.le hab) (fun u hu => pi0Dens_antitone (by linarith [hu.1]) hu.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

/-! ## Step 1 -/

/-- **Step 1, second bullet** (Theorem 5.24(ii)): for `J = [x(1-2δ), x(1-δ)]` with
`X_LP ≤ x(1-2δ)` and `x(1-δ) ≤ y` (`y` the certified height of Theorem 5.24),
`Π(J) ≥ δ x π₀(x) - 2K x exp(-c_LP √(log(x(1-2δ))))`. -/
theorem step1_window {P : BeurlingSystem} {X₀ : ℕ} {y x δ : ℝ}
    (hT : LocalPNT.Theorem524Concl P X₀ y) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hXLP : LocalPNT.XLP (Real.log X₀) ≤ x * (1 - 2 * δ)) (hy : x * (1 - δ) ≤ y)
    (hXLP1 : 1 < LocalPNT.XLP (Real.log X₀)) :
    δ * x * LocalPNT.pi0Dens x -
        2 * LocalPNT.KLP (Real.log X₀) * x *
          Real.exp (-(LocalPNT.cLP (Real.log X₀) * √(Real.log (x * (1 - 2 * δ))))) ≤
      LocalPNT.piCount P (x * (1 - δ)) - LocalPNT.piCount P (x * (1 - 2 * δ)) := by
  set a := x * (1 - 2 * δ)
  set b := x * (1 - δ)
  set K := LocalPNT.KLP (Real.log X₀)
  set c := LocalPNT.cLP (Real.log X₀)
  have ha1 : 1 < a := lt_of_lt_of_le hXLP1 hXLP
  have hx0 : 0 < x := by
    by_contra hc; push_neg at hc
    have : a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hab : a ≤ b := by simp only [a, b]; nlinarith
  have hbx : b ≤ x := by simp only [b]; nlinarith
  have hK : 0 ≤ K := by simp only [K, LocalPNT.KLP]; positivity
  have hiA := (hT.1 a hXLP (hab.trans hy)).2
  have hiB := (hT.1 b (hXLP.trans hab) hy).2
  rw [abs_le] at hiA hiB
  have hpi := pi0_sub_ge ha1 hab
  have hdens : LocalPNT.pi0Dens x ≤ LocalPNT.pi0Dens b := pi0Dens_antitone (by linarith) hbx
  have hba : b - a = δ * x := by simp only [a, b]; ring
  have hd0 := pi0Dens_nonneg (show (1 : ℝ) ≤ x by linarith)
  -- the error terms
  have hla : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hla0 : 0 ≤ Real.log a := Real.log_nonneg ha1.le
  have hc0 : 0 ≤ c := by simp only [c, LocalPNT.cLP, LocalPNT.cZF]; positivity
  have heb : Real.exp (-(c * √(Real.log b))) ≤ Real.exp (-(c * √(Real.log a))) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_le_sqrt hla
    nlinarith
  have hE1 : K * b * Real.exp (-(c * √(Real.log b))) ≤ K * x * Real.exp (-(c * √(Real.log a))) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hbx hK) heb (Real.exp_pos _).le
    positivity
  have hE2 : K * a * Real.exp (-(c * √(Real.log a))) ≤ K * x * Real.exp (-(c * √(Real.log a))) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab.trans hbx) hK)
      (Real.exp_pos _).le
  have hmain : δ * x * LocalPNT.pi0Dens x ≤ LocalPNT.pi0 b - LocalPNT.pi0 a := by
    rw [← hba]
    exact (mul_le_mul_of_nonneg_left hdens (by linarith)).trans hpi
  linarith [hiA.1, hiA.2, hiB.1, hiB.2]

/-- **Step 1**, the average: if the integral `I_J = ∫_J ρ̃` satisfies the first bullet's
comparison `I_J ≥ Π(J) - E_loc` (the partial boxes, the local count and the prime powers,
`E_loc = 27H(x) + 2K_loc + 6 + 2√x`), then
`I_J/(δx) ≥ π₀(x) - (2Kx e^{-c_LP √(log x(1-2δ))} + E_loc)/(δx)`. -/
theorem step1_avg {P : BeurlingSystem} {X₀ : ℕ} {y x δ IJ Eloc : ℝ}
    (hT : LocalPNT.Theorem524Concl P X₀ y) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hXLP : LocalPNT.XLP (Real.log X₀) ≤ x * (1 - 2 * δ)) (hy : x * (1 - δ) ≤ y)
    (hXLP1 : 1 < LocalPNT.XLP (Real.log X₀))
    (hcount : LocalPNT.piCount P (x * (1 - δ)) - LocalPNT.piCount P (x * (1 - 2 * δ)) - Eloc ≤
      IJ) :
    LocalPNT.pi0Dens x - (2 * LocalPNT.KLP (Real.log X₀) * x *
        Real.exp (-(LocalPNT.cLP (Real.log X₀) * √(Real.log (x * (1 - 2 * δ))))) + Eloc) /
        (δ * x) ≤ IJ / (δ * x) := by
  have h := step1_window hT hδ0 hδ hXLP hy hXLP1
  have hx0 : 0 < x := by
    by_contra hc; push_neg at hc
    have : x * (1 - 2 * δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hd : 0 < δ * x := mul_pos hδ0 hx0
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hd]
  have : LocalPNT.pi0Dens x * (δ * x) = δ * x * LocalPNT.pi0Dens x := by ring
  linarith

/-! ## Step 5 -/

/-- **Step 5 of the proof (range (B))**: Steps 1–4 give, with `L = log x`,
* (Step 1) `avg_J ρ̃ ≥ π₀(x) - o₁/L`;
* (Step 2) `avg_J ρ^sh ≥ avg_J ρ̃ - (ε_N + E_BR + j + o₂)/L` (Lemma 5.34, Proposition 5.26,
  `j = j_{X₀}`);
* (Steps 3–4) `ρ^sh(x) ≥ avg_J ρ^sh - o₃/L`;
so `ρ^sh(x) L ≥ 1 - 1/x - ε_N - E_BR - j - (o₁ + o₂ + o₃)`. -/
theorem step5 {x L avgR avgS ρx εN EBR j o1 o2 o3 : ℝ} (hx : 1 < x) (hL : L = Real.log x)
    (h1 : LocalPNT.pi0Dens x - o1 / L ≤ avgR)
    (h2 : avgR - (εN + EBR + j + o2) / L ≤ avgS) (h3 : avgS - o3 / L ≤ ρx) :
    1 - 1 / x - εN - EBR - j - (o1 + o2 + o3) ≤ ρx * L := by
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos hx
  have hπ : LocalPNT.pi0Dens x * L = 1 - 1 / x := by
    unfold LocalPNT.pi0Dens; rw [hL, div_mul_cancel₀ _ (Real.log_pos hx).ne']
  have : LocalPNT.pi0Dens x - o1 / L - (εN + EBR + j + o2) / L - o3 / L ≤ ρx := by linarith
  have e : (LocalPNT.pi0Dens x - o1 / L - (εN + EBR + j + o2) / L - o3 / L) * L =
      1 - 1 / x - εN - EBR - j - (o1 + o2 + o3) := by
    rw [← hπ]; field_simp; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right this hL0.le

/-- **Proposition 5.35, range (B)**, with the paper's sizes: `ε_N ≤ 10⁻¹³` (Lemma 5.34),
`E_BR ≤ e^{-76}` ((osc)), `j_{X₀} ≤ e^{-59}` (Proposition 5.33), `o₁ + o₂ + o₃ ≤ 10⁻²⁴`
(`o(1) ≤ Λ⁻³`), and `x ≥ 10¹⁰`: `ρ^sh(x) log x ≥ 0.97`. -/
theorem prop_5_35_B {x avgR avgS ρx εN EBR j o1 o2 o3 : ℝ} (hx : 10 ^ 10 ≤ x)
    (h1 : LocalPNT.pi0Dens x - o1 / Real.log x ≤ avgR)
    (h2 : avgR - (εN + EBR + j + o2) / Real.log x ≤ avgS)
    (h3 : avgS - o3 / Real.log x ≤ ρx) (hεN : εN ≤ 1 / 10 ^ 13)
    (hEBR : EBR ≤ Real.exp (-76)) (hj : j ≤ Real.exp (-59))
    (ho : o1 + o2 + o3 ≤ 1 / 10 ^ 24) : 0.97 ≤ ρx * Real.log x := by
  have h := step5 (by linarith) rfl h1 h2 h3
  have he76 : Real.exp (-76) ≤ 1 / 10 ^ 10 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have := Real.pow_div_factorial_le_exp (x := (76 : ℝ)) (by norm_num) 10
    norm_num [Nat.factorial] at this ⊢; linarith
  have he59 : Real.exp (-59) ≤ 1 / 10 ^ 10 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have := Real.pow_div_factorial_le_exp (x := (59 : ℝ)) (by norm_num) 10
    norm_num [Nat.factorial] at this ⊢; linarith
  have hx1 : 1 / x ≤ 1 / 10 ^ 10 := one_div_le_one_div_of_le (by norm_num) hx
  linarith

end KR.G1B

end
