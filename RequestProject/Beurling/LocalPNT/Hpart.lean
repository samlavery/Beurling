module

public import RequestProject.Beurling.LocalPNT.Contour

/-!
# Steps 9–10 of the proof of Theorem 5.24: `log ζ^♯` minus the prime powers `≤ y`

`Gright = Ly + Hp + log((s-1)/s)`, where `Ly(s) = ∑_{p^n ≤ y} p^{-ns}/n` (the transform of
`Π|_{[1,y]}`) and `Hp = (log ζ_J - Ly) + log(1 + g)`. The part `Hp` is the transform of a measure on
`(y, ∞)` (paper: `Π^♯ = Π` on `[1, y]`); we only use that it is holomorphic on
`σ > 1 + 8 log log y/log y` and `O(y^{1-σ}(1 + σ))` there (`norm_Hp_le`).
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology MeasureTheory

namespace LocalPNT

/-- A cut-off `M` with `2^M > y`. -/
noncomputable def Mcut (y : ℝ) : ℕ := ⌈Real.log y / Real.log 2⌉₊ + 1

/-- `Ly(s) = ∑_{p_j ≤ y} ∑_{1 ≤ n, p_j^n ≤ y} (p_j^n)^{-s}/n`. -/
noncomputable def Ly (P : BeurlingSystem) (y : ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ P.primesLe y, ∑ n ∈ Finset.range (Mcut y),
    if 1 ≤ n ∧ P.p j ^ n ≤ y then ((P.p j ^ n : ℝ) : ℂ) ^ (-s) / n else 0

/-- `Hp = (log ζ_J - Ly) + log(1 + g)`. -/
noncomputable def Hp (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ)
    (s : ℂ) : ℂ :=
  (LJ P y s - Ly P y s) + Complex.log (1 + gJ P θ X₀ α γ xp y s)

lemma Gright_eq (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ) (s : ℂ) :
    Gright P θ X₀ α γ xp y s =
      Ly P y s + Hp P θ X₀ α γ xp y s + Complex.log ((s - 1) / s) := by
  unfold Gright Hp; ring

lemma two_pow_Mcut_gt {y : ℝ} (hy : 1 ≤ y) : y < 2 ^ Mcut y := by
  unfold Mcut
  have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h1 : Real.log y / Real.log 2 < (⌈Real.log y / Real.log 2⌉₊ + 1 : ℕ) := by
    push_cast; linarith [Nat.le_ceil (Real.log y / Real.log 2)]
  have h2 : Real.log y < Real.log ((2 : ℝ) ^ (⌈Real.log y / Real.log 2⌉₊ + 1)) := by
    rw [Real.log_pow]; rw [div_lt_iff₀ hl2] at h1; linarith
  exact (Real.log_lt_log_iff (by linarith) (by positivity)).mp h2

lemma cpow_neg_pow {p : ℝ} (hp : 0 < p) (n : ℕ) (s : ℂ) :
    (((p : ℝ) : ℂ) ^ (-s)) ^ n = ((p ^ n : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos hp n).ne'),
    ← Complex.exp_nat_mul, ← Complex.ofReal_log hp.le, ← Complex.ofReal_log (pow_pos hp n).le,
    Real.log_pow]
  push_cast; ring_nf

/-- The tail of `-log(1 - p^{-s})` beyond `y`: `‖-log(1 - p^{-s}) - ∑_{p^n ≤ y} p^{-ns}/n‖ ≤
2 y^{1-σ}` for `p ≥ 2`, `σ > 1`. -/
lemma norm_log_tail_le {p y : ℝ} (hp : 2 ≤ p) (hy : 1 ≤ y) {s : ℂ} (hs : 1 < s.re) :
    ‖-Complex.log (1 - ((p : ℝ) : ℂ) ^ (-s)) - ∑ n ∈ Finset.range (Mcut y),
      (if 1 ≤ n ∧ p ^ n ≤ y then ((p ^ n : ℝ) : ℂ) ^ (-s) / n else 0)‖ ≤ 2 * y ^ (1 - s.re) := by
  classical
  have hp0 : 0 < p := by linarith
  have hy0 : 0 < y := by linarith
  set z : ℂ := ((p : ℝ) : ℂ) ^ (-s)
  have hz : ‖z‖ = p ^ (-s.re) := by
    simp only [z]; rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  have hz1 : ‖z‖ < 1 := by
    rw [hz]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hS := hasSum_taylorSeries_neg_log hz1
  have hzn : ∀ n : ℕ, z ^ n = ((p ^ n : ℝ) : ℂ) ^ (-s) := fun n => cpow_neg_pow hp0 n s
  set A : ℕ → Prop := fun n => 1 ≤ n ∧ p ^ n ≤ y
  -- `A n → n < M`
  have hAM : ∀ n, A n → n < Mcut y := by
    intro n hn
    by_contra hc; push_neg at hc
    have h2 : (2 : ℝ) ^ Mcut y ≤ p ^ n :=
      (pow_le_pow_right₀ (by norm_num) hc).trans (pow_le_pow_left₀ (by norm_num) hp n)
    linarith [two_pow_Mcut_gt hy, hn.2]
  have hfin : ∑ n ∈ Finset.range (Mcut y),
      (if A n then ((p ^ n : ℝ) : ℂ) ^ (-s) / n else 0) =
      ∑' n, (if A n then z ^ n / n else 0) := by
    rw [tsum_eq_sum (s := Finset.range (Mcut y))]
    · exact Finset.sum_congr rfl fun n _ => by rw [hzn]
    · intro n hn
      rw [if_neg]; intro hA; exact hn (Finset.mem_range.mpr (hAM n hA))
  have hsA : Summable (fun n => if A n then z ^ n / n else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (Mcut y)) fun n hn => ?_
    rw [if_neg]; intro hA; exact hn (Finset.mem_range.mpr (hAM n hA))
  have hsB : Summable (fun n => if A n then 0 else z ^ n / n) :=
    (hS.summable.sub hsA).congr fun n => by split_ifs <;> simp
  have htail : -Complex.log (1 - z) - ∑' n, (if A n then z ^ n / n else 0) =
      ∑' n, (if A n then 0 else z ^ n / n) := by
    rw [← hS.tsum_eq, ← hS.summable.tsum_sub hsA]
    exact tsum_congr fun n => by split_ifs <;> simp
  rw [hfin, htail]
  -- bound the tail by `y^{1-σ} ∑_{n ≥ 1} p^{-n}`
  have hq0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo := hasSum_geometric_of_lt_one hq0 hq1
  have hmaj : ∀ n : ℕ, ‖(if A n then 0 else z ^ n / n)‖ ≤ y ^ (1 - s.re) * p⁻¹ ^ n := by
    intro n
    split_ifs with hA
    · rw [norm_zero]; positivity
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
      positivity
    have hgt : y < p ^ n := by
      by_contra hc; push_neg at hc; exact hA ⟨hn, hc⟩
    rw [norm_div, norm_pow, hz, Complex.norm_natCast]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpn : 0 < p ^ n := pow_pos hp0 n
    have h1 : (p ^ (-s.re)) ^ n = (p ^ n) ^ (-s.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, mul_comm, Real.rpow_mul hp0.le,
        Real.rpow_natCast]
    rw [h1]
    have h2 : (p ^ n) ^ (-s.re) = (p ^ n) ^ (1 - s.re) * (p ^ n)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hpn]; ring_nf
    rw [h2]
    have h3 : (p ^ n) ^ (1 - s.re) ≤ y ^ (1 - s.re) :=
      Real.rpow_le_rpow_of_nonpos hy0 hgt.le (by linarith)
    have h6 : (p ^ n)⁻¹ ≤ p⁻¹ ^ n := by rw [inv_pow]
    calc (p ^ n) ^ (1 - s.re) * (p ^ n)⁻¹ / n ≤ (p ^ n) ^ (1 - s.re) * (p ^ n)⁻¹ := by
          apply div_le_self (by positivity) hn1
      _ ≤ y ^ (1 - s.re) * p⁻¹ ^ n := mul_le_mul h3 h6 (by positivity) (by positivity)
  have hmajS : Summable (fun n : ℕ => y ^ (1 - s.re) * p⁻¹ ^ n) :=
    hgeo.summable.mul_left _
  calc ‖∑' n, (if A n then 0 else z ^ n / n)‖ ≤ ∑' n, ‖(if A n then 0 else z ^ n / n)‖ :=
        norm_tsum_le_tsum_norm (hmajS.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj)
    _ ≤ ∑' n : ℕ, y ^ (1 - s.re) * p⁻¹ ^ n :=
        (hmajS.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj).tsum_le_tsum hmaj hmajS
    _ = y ^ (1 - s.re) * (1 - p⁻¹)⁻¹ := by rw [tsum_mul_left, hgeo.tsum_eq]
    _ ≤ y ^ (1 - s.re) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : p⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    _ = 2 * y ^ (1 - s.re) := by ring

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `‖log ζ_J - Ly‖ ≤ 2 #J y^{1-σ}` for `σ > 1`. -/
theorem norm_LJ_sub_Ly_le {s : ℂ} (hs : 1 < s.re) :
    ‖LJ P y s - Ly P y s‖ ≤ 2 * (P.primesLe y).card * y ^ (1 - s.re) := by
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  unfold LJ Ly
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j ∈ P.primesLe y, ‖-Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s)) -
        ∑ n ∈ Finset.range (Mcut y), (if 1 ≤ n ∧ P.p j ^ n ≤ y then
          ((P.p j ^ n : ℝ) : ℂ) ^ (-s) / n else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ P.primesLe y, 2 * y ^ (1 - s.re) := Finset.sum_le_sum fun j hj =>
        norm_log_tail_le (h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)) hy1 hs
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `1 + 8 log log y/log y`. -/
noncomputable def c1 (y : ℝ) : ℝ := 1 + 8 * Real.log (Real.log y) / Real.log y

omit h in
lemma c1_def (y : ℝ) : c1 y = 1 + 8 * Real.log (Real.log y) / Real.log y := rfl

lemma c1_gt : 1 < c1 y := by
  have hL := h.logy_ge
  unfold c1
  have : 0 < 8 * Real.log (Real.log y) / Real.log y :=
    div_pos (mul_pos (by norm_num) (Real.log_pos (by linarith))) (by linarith)
  linarith

lemma c1_le : c1 y ≤ 1 + 1 / 100 := by
  have hL := h.logy_ge
  unfold c1
  have hl := Real.log_le_rpow_div (x := Real.log y) (by linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [add_le_add_iff_left, div_le_iff₀ (by linarith)]
  have h2' : Real.log y ^ (1 / 2 : ℝ) * Real.log y ^ (1 / 2 : ℝ) = Real.log y := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : (10 : ℝ) ^ 4 ≤ Real.log y ^ (1 / 2 : ℝ) := by
    have : ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) ≤ Real.log y ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    rwa [show ((10 : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 10 ^ 4 by
      rw [show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num] at this
  have h5 : 0 ≤ Real.log y ^ (1 / 2 : ℝ) := by positivity
  rw [div_div_eq_mul_div] at hl
  nlinarith

/-- `ζ_J(c₁) ≤ log y`. -/
lemma zetaFR_c1_le : zetaFR P (P.primesLe y) (c1 y) ≤ Real.log y := by
  have hL := h.logy_ge
  set L := Real.log y
  have hc1 := h.c1_gt
  have hc2 := h.c1_le
  have hZ := h.zetaFR_le hc1 (by linarith)
  have hE := h.rpow_mul_log_pow_le (σ := c1 y) le_rfl
  have hEL : y ^ (1 - c1 y) * (Real.exp 11 * L ^ (2 : ℝ)) ≤ 1 := by
    have he11 : Real.exp 11 ≤ 60000 := by
      have e : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
        _ ≤ 60000 := by norm_num
    rw [Real.rpow_two]
    have hyp : 0 ≤ y ^ (1 - c1 y) := Real.rpow_nonneg (lt_of_lt_of_le h.X0_pos h.y_ge).le _
    have hL6 : (10 : ℝ) ^ 48 ≤ L ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hL 6; norm_num at this ⊢; linarith
    have h2 : y ^ (1 - c1 y) * L ^ 2 ≤ 1 / 10 ^ 48 := by
      rw [le_div_iff₀ (by norm_num)]
      have : y ^ (1 - c1 y) * L ^ 8 = y ^ (1 - c1 y) * L ^ 2 * L ^ 6 := by ring
      nlinarith [mul_nonneg hyp (sq_nonneg L)]
    calc y ^ (1 - c1 y) * (Real.exp 11 * L ^ 2) = Real.exp 11 * (y ^ (1 - c1 y) * L ^ 2) := by ring
      _ ≤ 60000 * (1 / 10 ^ 48) := mul_le_mul he11 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hκ := (kap_facts h.logX).2.2.2.1
  have hLL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hinv : 1 / (c1 y - 1) ≤ L / 8 := by
    rw [c1_def, add_sub_cancel_left, one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : (1 + 2 * kap X₀) / (c1 y - 1) ≤ 1.01 * (L / 8) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hinv (by apply div_nonneg zero_le_one; linarith) (by norm_num)
  linarith

/-- `σ y^{2-σ} ≤ 2` for `σ ≥ 2`, `y ≥ e`. -/
lemma mul_rpow_two_sub_le {σ : ℝ} (hσ : 2 ≤ σ) : σ * y ^ (2 - σ) ≤ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hL := h.logy_ge
  rw [Real.rpow_def_of_pos hy0]
  have h1 := Real.add_one_le_exp ((σ - 2) * Real.log y)
  have h2 : 0 < Real.exp (Real.log y * (2 - σ)) := Real.exp_pos _
  have e : Real.exp (Real.log y * (2 - σ)) * Real.exp ((σ - 2) * Real.log y) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h3 : σ ≤ 2 * Real.exp ((σ - 2) * Real.log y) := by nlinarith
  nlinarith

/-- **`|g(s)| ≤ y^{1-σ} (A₀ + B₀ σ)` and `|g(s)| ≤ 1/2`** for `σ ≥ c₁`, with
`A₀ = log y (log y + e^{11} log² y)`, `B₀ = log² y`. -/
theorem norm_g_le_all {s : ℂ} (hs : c1 y ≤ s.re) :
    ‖gJ P θ X₀ α γ xp y s‖ ≤ y ^ (1 - s.re) *
      (Real.log y * (Real.log y + Real.exp 11 * Real.log y ^ 2) +
        Real.log y ^ 2 * s.re) ∧ ‖gJ P θ X₀ α γ xp y s‖ ≤ 1 / 2 := by
  set L := Real.log y
  have hL := h.logy_ge
  have hy0 : 0 < y := lt_of_lt_of_le h.X0_pos h.y_ge
  have hc1 := h.c1_gt
  have hσ : 1 < s.re := by linarith
  have hκ := (kap_facts h.logX).2.2.2.1
  have hκ0 := (kap_facts h.logX).2.2.1
  have hΔ := h.norm_Delta_le hσ
  have hinv := norm_inv_zetaF_le P (P.primesLe y) (show 0 < s.re by linarith)
  have hanti : zetaFR P (P.primesLe y) s.re ≤ zetaFR P (P.primesLe y) (c1 y) :=
    zetaFR_antitoneOn P _ (show (0 : ℝ) < c1 y by linarith) (show (0 : ℝ) < s.re by linarith) hs
  have hZ := h.zetaFR_c1_le
  have hLL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hσ1 : 1 / (s.re - 1) ≤ L := by
    have h1 : 1 / (s.re - 1) ≤ 1 / (c1 y - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h2 : 1 / (c1 y - 1) ≤ L / 8 := by
      rw [c1_def, add_sub_cancel_left, one_div_div,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hyp : 0 ≤ y ^ (1 - s.re) := Real.rpow_nonneg hy0.le _
  have hfrac : (1 + 6 * kap X₀ * s.re) / (s.re - 1) ≤ L * (1 + s.re) := by
    rw [div_eq_mul_one_div]
    calc (1 + 6 * kap X₀ * s.re) * (1 / (s.re - 1)) ≤ (1 + s.re) * L :=
          mul_le_mul (by nlinarith) hσ1 (by apply div_nonneg zero_le_one; linarith) (by linarith)
      _ = L * (1 + s.re) := by ring
  have hgle : ‖gJ P θ X₀ α γ xp y s‖ ≤ y ^ (1 - s.re) *
      (L * (L + Real.exp 11 * L ^ 2) + L ^ 2 * s.re) := by
    unfold gJ
    rw [div_eq_mul_inv, norm_mul]
    have h1 : ‖(zetaF P (P.primesLe y) s)⁻¹‖ ≤ L := hinv.trans (hanti.trans hZ)
    rw [Real.rpow_two] at hΔ
    calc _ ≤ (y ^ (1 - s.re) * ((1 + 6 * kap X₀ * s.re) / (s.re - 1) +
          Real.exp 11 * L ^ 2)) * L := mul_le_mul hΔ h1 (norm_nonneg _) (by
            have : 0 ≤ (1 + 6 * kap X₀ * s.re) / (s.re - 1) :=
              div_nonneg (by nlinarith) (by linarith)
            positivity)
      _ ≤ (y ^ (1 - s.re) * (L * (1 + s.re) + Real.exp 11 * L ^ 2)) * L := by gcongr
      _ = _ := by ring
  refine ⟨hgle, ?_⟩
  by_cases h2 : s.re ≤ 2
  · have := h.norm_g_le (s := s) hs h2
    have hL4 : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
    nlinarith [norm_nonneg (gJ P θ X₀ α γ xp y s)]
  · push_neg at h2
    have hm := h.mul_rpow_two_sub_le (σ := s.re) h2.le
    have hq : y ^ (2 - s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_trans h.one_le_X0 h.y_ge) (by linarith)
    have hsplit : y ^ (1 - s.re) = y ^ (2 - s.re) * y⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hy0]; ring_nf
    have he11 : Real.exp 11 ≤ 60000 := by
      have e : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
        _ ≤ 60000 := by norm_num
    have hyL : L ^ 4 / 24 ≤ y := by
      have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ L by linarith) 5
      rw [Real.exp_log hy0] at this
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      nlinarith [pow_pos (show (0 : ℝ) < L by linarith) 3]
    have hy1 : y⁻¹ ≤ 24 / L ^ 4 := by
      rw [inv_le_comm₀ hy0 (by positivity), inv_div]; exact hyL
    have hA : L * (L + Real.exp 11 * L ^ 2) + L ^ 2 * 2 ≤ 60003 * L ^ 3 := by
      have : L ^ 2 ≤ L ^ 3 := by nlinarith
      nlinarith
    calc ‖gJ P θ X₀ α γ xp y s‖ ≤ y ^ (1 - s.re) *
          (L * (L + Real.exp 11 * L ^ 2) + L ^ 2 * s.re) := hgle
      _ = y⁻¹ * (L * (L + Real.exp 11 * L ^ 2) * y ^ (2 - s.re) +
          L ^ 2 * (s.re * y ^ (2 - s.re))) := by rw [hsplit]; ring
      _ ≤ y⁻¹ * (L * (L + Real.exp 11 * L ^ 2) * 1 + L ^ 2 * 2) := by
          gcongr
      _ ≤ 24 / L ^ 4 * (60003 * L ^ 3) := by
          apply mul_le_mul hy1 (by linarith) (by positivity) (by positivity)
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [pow_pos (show (0 : ℝ) < L by linarith) 3]

/-- **`|Hp(s)| ≤ y^{1-σ} (2#J + 1.5 (A₀ + B₀ σ))`** for `σ ≥ c₁`. -/
theorem norm_Hp_le {s : ℂ} (hs : c1 y ≤ s.re) :
    ‖Hp P θ X₀ α γ xp y s‖ ≤ y ^ (1 - s.re) * (2 * (P.primesLe y).card +
      1.5 * (Real.log y * (Real.log y + Real.exp 11 * Real.log y ^ 2) +
        Real.log y ^ 2 * s.re)) := by
  have hσ : 1 < s.re := lt_of_lt_of_le h.c1_gt hs
  obtain ⟨hg1, hg2⟩ := h.norm_g_le_all hs
  have hlog := Complex.norm_log_one_add_half_le_self hg2
  have hLJ := h.norm_LJ_sub_Ly_le hσ
  unfold Hp
  calc _ ≤ ‖LJ P y s - Ly P y s‖ + ‖Complex.log (1 + gJ P θ X₀ α γ xp y s)‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- `Hp` is holomorphic on `σ > c₁`. -/
theorem differentiableAt_Hp {s : ℂ} (hs : c1 y < s.re) :
    DifferentiableAt ℂ (Hp P θ X₀ α γ xp y) s := by
  have hσ : 1 < s.re := lt_of_lt_of_le h.c1_gt hs.le
  obtain ⟨-, hg2⟩ := h.norm_g_le_all hs.le
  have hre : 0 < (1 + gJ P θ X₀ α γ xp y s).re := by
    have := Complex.abs_re_le_norm (gJ P θ X₀ α γ xp y s)
    simp only [Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp this).1]
  have hLy : DifferentiableAt ℂ (Ly P y) s := by
    unfold Ly
    refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_sum fun n _ => ?_
    split_ifs with hc
    · have hp : ((P.p j ^ n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (pow_pos (P.p_pos j) n).ne'
      exact ((differentiableAt_id.neg).const_cpow (Or.inl hp)).div_const _
    · exact differentiableAt_const _
  unfold Hp
  exact ((differentiableAt_LJ P y (by linarith)).sub hLy).add
    (((differentiableAt_const 1).add (h.differentiableAt_gJ hσ)).clog
      (Complex.mem_slitPlane_iff.mpr (Or.inl hre)))

end LPHyp

end LocalPNT

end
