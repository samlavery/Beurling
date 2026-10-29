module

public import RequestProject.Beurling.LocalPNT.Defs
public import RequestProject.Beurling.Noise.BSDefs

/-!
# Lemma 5.32, Part (A): primes in a short window, from Theorem 5.24(iii)

`LocalPNT.Theorem524Concl P X₀ y'` is the statement of Theorem 5.24 at the height `y'` (stated
in `LocalPNT/Defs.lean`; it is used here as a hypothesis). From its part (iii):

* `relBound_le` : for `Λ = log X₀ ≥ 10⁸`, `Λ_p = log v ≥ 99 Λ³` and `e^{-2Λ} ≤ η ≤ 1/2`,
  the bound (eq. lpplus) satisfies `Rel ≤ 0.1` (the paper's case analysis, done here with
  `Λ_p ≥ 99Λ³`, the range of Lemma 5.32, where it has room);
* `sum_inv_window_le` : `∑_{v ≤ p ≤ v(1+η)} 1/p ≤ 1.1001 η/log v` for such `v, η` with
  `v(1 + 2η) ≤ y'`.

The proof is that of Lemma 5.32 (A): the window `φ` majorises `1_{[v, v(1+η)]}`, so the number
of primes there is at most `∫ φ dΠ ≤ 1.1 ∫ φ dΠ₀`, and `∫ φ dΠ₀ ≤ η(1 + 2Λ_p^{-2}) v/log(v(1-w))`
since `0 ≤ φ ≤ 1` is supported in `[v(1-w), v(1+η+w)]`, `w = ηΛ_p^{-2}`, and `π₀(u) ≤ 1/log u`.
-/

@[expose] public section

open Finset Real MeasureTheory Set

namespace BridgeSI

/-- `log x ≤ 0.0002 x` for `x ≥ 10⁸`. -/
lemma log_le_small {x : ℝ} (hx : 100000000 ≤ x) : Real.log x ≤ 0.0002 * x := by
  have hx0 : 0 < x := by linarith
  have hs : 10000 ≤ √x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  have h1 : Real.log x = 2 * Real.log √x := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr hx0), Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have h2 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3 : √x * √x = x := Real.mul_self_sqrt hx0.le
  nlinarith

lemma exp_ge_of_pow {c : ℝ} (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (h : c ≤ 2.7182818283 ^ n * (1 + r + r ^ 2 / 2)) : c ≤ Real.exp (n + r) := by
  rw [Real.exp_add, ← Real.exp_one_pow]
  have h3 := Real.exp_one_gt_d9
  have h4 : (2.7182818283 : ℝ) ^ n ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) h3.le n
  have h5 := Real.quadratic_le_exp_of_nonneg hr
  have : (2.7182818283 : ℝ) ^ n * (1 + r + r ^ 2 / 2) ≤ Real.exp 1 ^ n * Real.exp r :=
    mul_le_mul h4 h5 (by positivity) (by positivity)
  linarith

lemma log99_le : Real.log 99 ≤ 4.7 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_ge_of_pow (c := 99) 4 0.7 (by norm_num) (by norm_num)
  have e : ((4 : ℕ) : ℝ) + 0.7 = 4.7 := by norm_num
  rwa [e] at this

lemma log3_le : Real.log 3 ≤ 1.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_ge_of_pow (c := 3) 1 0.1 (by norm_num) (by norm_num)
  have e : ((1 : ℕ) : ℝ) + 0.1 = 1.1 := by norm_num
  rwa [e] at this

lemma log1600_le : Real.log 1600 ≤ 7.5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_ge_of_pow (c := 1600) 7 0.5 (by norm_num) (by norm_num)
  have e : ((7 : ℕ) : ℝ) + 0.5 = 7.5 := by norm_num
  rwa [e] at this

lemma log360_le : Real.log 360 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_ge_of_pow (c := 360) 6 0 le_rfl (by norm_num)
  have e : ((6 : ℕ) : ℝ) + 0 = 6 := by norm_num
  rwa [e] at this

/-- The polynomial inequality behind `Rel ≤ 0.1`. -/
lemma key_poly {Λ δ : ℝ} (hΛ : 100000000 ≤ Λ) (hδ0 : 0 ≤ δ) :
    Λ * (2.0036 * Λ + 4 * δ) * (2.003 * Λ + 4 * δ) ≤
      0.0792 * (99 * Λ ^ 3 * (1 + δ + δ ^ 2 / 2)) := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : 0 ≤ Λ ^ 2 * δ * (7.8408 * Λ - 16.0264) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ Λ * δ ^ 2 * (3.9204 * Λ ^ 2 - 16) :=
    mul_nonneg (by positivity) (by nlinarith)
  have h3 : 0 ≤ Λ ^ 3 := by positivity
  nlinarith

/-- `log Λ_p`-bookkeeping: with `q = 2Λ + 20 s + 1`, `log q ≤ log 3 + log Λ + s`. -/
lemma log_q_le {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : 0 < s) :
    Real.log (2 * Λ + 20 * s + 1) ≤ Real.log 3 + Real.log Λ + s := by
  have hΛ0 : 0 < Λ := by linarith
  have hq3 : 2 * Λ + 20 * s + 1 ≤ 3 * Λ * (1 + s) := by nlinarith
  have h1 := Real.log_le_log (by positivity) hq3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hΛ0.ne'] at h1
  have h2 : Real.log (1 + s) ≤ s := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + s by linarith); linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **`Rel ≤ 0.1`** in the range of Lemma 5.32. -/
theorem relBound_le {Λ v η : ℝ} (hΛ : 100000000 ≤ Λ) (hv : 99 * Λ ^ 3 ≤ Real.log v)
    (hη0 : Real.exp (-(2 * Λ)) ≤ η) (hη1 : η ≤ 1 / 2) :
    LocalPNT.relBound Λ v η ≤ 0.1 := by
  have hΛ0 : 0 < Λ := by linarith
  set Lp := Real.log v with hLp
  have hLp0 : 0 < Lp := lt_of_lt_of_le (by positivity) hv
  have hη : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hη0
  set s := Real.log Lp with hs
  set a := Real.log (1 / η) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  have ha2 : a ≤ 2 * Λ := by
    rw [ha, one_div, Real.log_inv]
    have := Real.log_le_log (Real.exp_pos _) hη0
    rw [Real.log_exp] at this; linarith
  have hlogΛ := log_le_small hΛ
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hs0 : Real.log (99 * Λ ^ 3) ≤ s := Real.log_le_log (by positivity) hv
  have hlog99 : Real.log (99 * Λ ^ 3) = Real.log 99 + 3 * Real.log Λ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hl99 := log99_le
  have hl99' : 0 < Real.log 99 := Real.log_pos (by norm_num)
  have hs_pos : 0 < s := by linarith
  have hl3 := log3_le
  -- `k`
  set k := LocalPNT.lpK v η with hk
  have hpos : 0 < Real.log (1 / η) + 20 * Real.log (Real.log v) := by
    rw [← ha, ← hLp, ← hs]; positivity
  have hk_le : (k : ℝ) ≤ a + 20 * s + 1 := by
    rw [hk, LocalPNT.lpK]
    have := Nat.ceil_lt_add_one hpos.le
    rw [← ha, ← hLp, ← hs] at this; linarith
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hk, LocalPNT.lpK]
    exact_mod_cast Nat.ceil_pos.mpr hpos
  set q := 2 * Λ + 20 * s + 1 with hq
  have hq_pos : 0 < q := by positivity
  have hkq : (k : ℝ) ≤ q := by linarith
  have hlogq : Real.log q ≤ Real.log 3 + Real.log Λ + s := log_q_le hΛ hs_pos
  have hlogk : Real.log k ≤ Real.log q := Real.log_le_log (by linarith) hkq
  have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  -- `L₁`
  set L1 := LocalPNT.lpL1 v η with hL1
  have hL1e : L1 = 2 * s + a + Real.log k + 3.08 := by rw [hL1, LocalPNT.lpL1]
  have hL1ge : 1 ≤ L1 := by rw [hL1e]; linarith
  have hL1pos : 0 < L1 := by linarith
  have hL1q : L1 ≤ 3 * q := by
    rw [hL1e]; have := Real.log_le_sub_one_of_pos hq_pos; linarith
  have hlogL1 : Real.log L1 ≤ Real.log 3 + Real.log q := by
    have := Real.log_le_log hL1pos hL1q
    rw [Real.log_mul (by norm_num) hq_pos.ne'] at this; exact this
  have hlogL10 : 0 ≤ Real.log L1 := Real.log_nonneg hL1ge
  -- `D` and the needed exponent
  set D := L1 + 442 + 2 * Real.log Λ + Real.log L1 with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  have hD_le : D ≤ 2.001 * Λ + 4 * s := by linarith [hD, hL1e]
  set G := LocalPNT.GLam Λ L1 with hG
  have hGe : G = 400 * (L1 + 450 + 2 * Real.log Λ) := rfl
  have hGpos : 0 < G := by rw [hGe]; linarith
  have hG_le : G ≤ 1600 * q := by rw [hGe]; linarith
  have hlogG : Real.log G ≤ Real.log 1600 + Real.log q := by
    have := Real.log_le_log hGpos hG_le
    rw [Real.log_mul (by norm_num) hq_pos.ne'] at this; exact this
  have hl1600 := log1600_le
  have hl360 := log360_le
  have hneed : Real.log (360 * G * Lp ^ 3 / η) ≤ 2.0003 * Λ + 4 * s := by
    have hLp3 : Real.log (Lp ^ 3) = 3 * s := by rw [Real.log_pow]; push_cast; ring
    rw [Real.log_div (by positivity) hη.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) hGpos.ne', hLp3]
    have : -Real.log η = a := by rw [ha, one_div, Real.log_inv]
    linarith
  -- the key inequality `0.0792 Λ_p ≥ Λ D (2.0003Λ + 4s)`
  have hkey : Λ * D * (2.0003 * Λ + 4 * s) ≤ 0.0792 * Lp := by
    set δ := s - Real.log (99 * Λ ^ 3) with hδ
    have hδ0 : 0 ≤ δ := by linarith
    have hexpδ : Real.exp δ = Lp / (99 * Λ ^ 3) := by
      rw [hδ, Real.exp_sub, hs, Real.exp_log hLp0, Real.exp_log (by positivity)]
    have hLpe : Lp = 99 * Λ ^ 3 * Real.exp δ := by rw [hexpδ]; field_simp
    have he := Real.quadratic_le_exp_of_nonneg hδ0
    have hs_le : 4 * s ≤ 4 * δ + 0.0026 * Λ := by
      have : s = δ + Real.log (99 * Λ ^ 3) := by rw [hδ]; ring
      rw [this, hlog99]; linarith
    have hA : D ≤ 2.0036 * Λ + 4 * δ := by linarith
    have hB : 2.0003 * Λ + 4 * s ≤ 2.003 * Λ + 4 * δ := by linarith
    have h1 : 0 ≤ 2.0003 * Λ + 4 * s := by positivity
    calc Λ * D * (2.0003 * Λ + 4 * s) ≤ Λ * (2.0036 * Λ + 4 * δ) * (2.003 * Λ + 4 * δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA hΛ0.le) hB h1 (by positivity)
      _ ≤ 0.0792 * (99 * Λ ^ 3 * (1 + δ + δ ^ 2 / 2)) := key_poly hΛ hδ0
      _ ≤ 0.0792 * Lp := by
          rw [hLpe]
          have : 0 ≤ 99 * Λ ^ 3 := by positivity
          have : 1 + δ + δ ^ 2 / 2 ≤ Real.exp δ := he
          nlinarith
  -- assembly
  have hE : Real.log (360 * G * Lp ^ 3 / η) ≤ 0.9 * LocalPNT.cZF Λ * Lp / D := by
    unfold LocalPNT.cZF
    rw [le_div_iff₀ hDpos]
    have e : 0.9 * (0.088 / Λ) * Lp = 0.0792 * Lp / Λ := by field_simp; ring
    rw [e, le_div_iff₀ hΛ0]
    have := mul_le_mul_of_nonneg_left hneed (mul_pos hΛ0 hDpos).le
    nlinarith
  have hexpE : 360 * G * Lp ^ 3 / η ≤ Real.exp (0.9 * LocalPNT.cZF Λ * Lp / D) := by
    rw [← Real.exp_log (show 0 < 360 * G * Lp ^ 3 / η by positivity)]
    exact Real.exp_le_exp.mpr hE
  have hpart : 18 * G * Lp ^ 3 / η * Real.exp (-(0.9 * LocalPNT.cZF Λ * Lp / D)) ≤ 0.05 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have : 18 * G * Lp ^ 3 / η = (360 * G * Lp ^ 3 / η) / 20 := by ring
    rw [this]; linarith
  have hsmall : 1 / Lp ^ 2 ≤ 0.05 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have : (100 : ℝ) ≤ Lp := le_trans (by linarith) hv
    nlinarith
  unfold LocalPNT.relBound
  rw [← hLp, ← hL1, ← hG]
  have e : 18 * LocalPNT.GLam Λ L1 * Lp ^ 3 / η *
      Real.exp (-(0.9 * LocalPNT.cZF Λ * Lp / (L1 + 442 + 2 * Real.log Λ + Real.log L1))) =
      18 * G * Lp ^ 3 / η * Real.exp (-(0.9 * LocalPNT.cZF Λ * Lp / D)) := rfl
  linarith

/-- `#{v ≤ p_j ≤ v(1+η)} ≤ ∫ φ dΠ` for a window `φ ≥ 0` with `φ = 1` on `[v, v(1+η)]` and
support in `(0, b]`. -/
lemma card_window_le_piInt (P : BeurlingSystem) {v η b : ℝ} (φ : ℝ → ℝ)
    (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u ∈ Icc v (v * (1 + η)), φ u = 1)
    (hs : ∀ u, φ u ≠ 0 → u ≤ b) (hb : v * (1 + η) ≤ b) :
    (((P.primesLe (v * (1 + η))).filter (fun j => v ≤ P.p j)).card : ℝ) ≤
      LocalPNT.piInt P φ := by
  set T := P.pps b
  set f : ℕ × ℕ → ℝ := fun jk => φ (P.p jk.1 ^ (jk.2 + 1)) / ((jk.2 : ℝ) + 1)
  have hsupp : Function.support f ⊆ ↑T := by
    intro jk hjk
    simp only [Function.mem_support, f] at hjk
    have : φ (P.p jk.1 ^ (jk.2 + 1)) ≠ 0 := fun h => hjk (by rw [h, zero_div])
    simp only [Finset.mem_coe, T, P.mem_pps]
    exact hs _ this
  have hfin : LocalPNT.piInt P φ = ∑ jk ∈ T, f jk := by
    unfold LocalPNT.piInt
    exact finsum_eq_sum_of_support_subset f hsupp
  rw [hfin]
  set W := (P.primesLe (v * (1 + η))).filter (fun j => v ≤ P.p j)
  have hW : (W.card : ℝ) = ∑ jk ∈ W.image (fun j => (j, 0)), f jk := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    rw [Finset.card_eq_sum_ones]; push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [W, Finset.mem_filter, P.mem_primesLe] at hj
    simp only [f, zero_add, pow_one, Nat.cast_zero, div_one]
    rw [h1 _ ⟨hj.2, hj.1⟩]
  rw [hW]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro jk hjk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
    simp only [W, Finset.mem_filter, P.mem_primesLe] at hj
    simp only [T, P.mem_pps, zero_add, pow_one]
    linarith [hj.1]
  · intro jk _ _
    exact div_nonneg (h0 _) (by positivity)

set_option maxHeartbeats 1000000 in
/-- **Lemma 5.32 (A), the prime sum**: from Theorem 5.24(iii) at the height `y'`, for
`Λ = log X₀ ≥ 10⁸`, `log v ≥ 99Λ³`, `e^{-2Λ} ≤ η ≤ 1/2` and `v(1+2η) ≤ y'`,
`∑_{v ≤ p ≤ v(1+η)} 1/p ≤ 1.1001 η/log v`. -/
theorem sum_inv_window_le (P : BeurlingSystem) {X0 : ℕ} {y' : ℝ}
    (hT : LocalPNT.Theorem524Concl P X0 y') (hΛ : 100000000 ≤ Real.log X0) {v η : ℝ}
    (hv : 99 * Real.log X0 ^ 3 ≤ Real.log v) (hη0 : Real.exp (-(2 * Real.log X0)) ≤ η)
    (hη1 : η ≤ 1 / 2) (hvy : v * (1 + 2 * η) ≤ y') :
    ∑ j ∈ (P.primesLe (v * (1 + η))).filter (fun j => v ≤ P.p j), 1 / P.p j ≤
      1.1001 * η / Real.log v := by
  set Λ := Real.log X0 with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  set Lp := Real.log v with hLp
  have hΛ3 : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hLp0 : 0 < Lp := lt_of_lt_of_le (by positivity) hv
  have hLpbig : 1000000000000000000000000 ≤ Lp := by
    have : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
    nlinarith
  have hη : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hη0
  have hRHS : 0 ≤ 1.1001 * η / Lp := by positivity
  rcases le_or_gt v 0 with hv0 | hv0
  · -- no prime in the window
    have : (P.primesLe (v * (1 + η))).filter (fun j => v ≤ P.p j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, P.mem_primesLe, Finset.notMem_empty, iff_false, not_and]
      intro h1 _
      have := P.p_pos j
      nlinarith
    rw [this, Finset.sum_empty]; exact hRHS
  have hv1 : 1 < v := by
    rw [← Real.log_pos_iff hv0.le]; exact hLp0
  have hv2 : 2 < v := by
    have h1 : Real.exp 1 ≤ v := by
      rw [← Real.exp_log hv0]; exact Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_one_gt_d9; linarith
  obtain ⟨-, h3⟩ := hT
  obtain ⟨hφ01, hφ1, hφs, hint⟩ := h3 v η (by nlinarith) hη0 hη1 hvy
  set φ := LocalPNT.lpWindow v η with hφ
  set w := LocalPNT.lpW v η with hw
  have hwe : w = η / Lp ^ 2 := rfl
  have hw0 : 0 ≤ w := by rw [hwe]; positivity
  have hw1 : w ≤ 1 / 2 := by
    rw [hwe, div_le_iff₀ (by positivity)]; nlinarith
  have hcard := card_window_le_piInt P φ (fun u => (hφ01 u).1) hφ1 (fun u hu => (hφs u hu).2)
    (b := v * (1 + η + w)) (by nlinarith)
  have hrel := relBound_le hΛ hv hη0 hη1
  -- `∫ φ dΠ₀ ≤ v(η + 2w)/(Λ_p - 2w)`
  set a := v * (1 - w) with ha
  set b := v * (1 + η + w) with hb
  have ha1 : 1 < a := by rw [ha]; nlinarith
  have hlog1w : -(2 * w) ≤ Real.log (1 - w) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - w by linarith)
    have hw' : 1 - w ≠ 0 := by linarith
    have h2 : -(2 * w) ≤ 1 - (1 - w)⁻¹ := by
      rw [show 1 - (1 - w)⁻¹ = -w / (1 - w) by field_simp; ring, le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  have hloga : Lp - 2 * w ≤ Real.log a := by
    rw [ha, Real.log_mul hv0.ne' (by linarith)]; linarith
  have hden : 0 < Lp - 2 * w := by linarith
  set c := 1 / (Lp - 2 * w) with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ u ∈ Ioi (1 : ℝ), φ u * LocalPNT.pi0Dens u ≤ (Icc a b).indicator (fun _ => c) u := by
    intro u hu
    rw [Set.mem_Ioi] at hu
    by_cases h0 : φ u = 0
    · rw [h0, zero_mul]; exact Set.indicator_nonneg (fun _ _ => hc0.le) u
    · have hmem := hφs u h0
      rw [Set.indicator_of_mem hmem]
      have hlu : Real.log a ≤ Real.log u := Real.log_le_log (by linarith) hmem.1
      have hlu0 : 0 < Real.log u := by linarith
      have hd : LocalPNT.pi0Dens u ≤ c := by
        unfold LocalPNT.pi0Dens
        rw [hc, div_le_div_iff₀ hlu0 hden]
        have : 0 ≤ 1 / u := by positivity
        have : 1 / u ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        nlinarith
      have hd0 : 0 ≤ LocalPNT.pi0Dens u := by
        unfold LocalPNT.pi0Dens
        apply div_nonneg _ hlu0.le
        have : 1 / u ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      calc φ u * LocalPNT.pi0Dens u ≤ 1 * c :=
            mul_le_mul (hφ01 u).2 hd hd0 zero_le_one
        _ = c := one_mul c
  have hnn : ∀ u ∈ Ioi (1 : ℝ), 0 ≤ φ u * LocalPNT.pi0Dens u := by
    intro u hu
    rw [Set.mem_Ioi] at hu
    apply mul_nonneg (hφ01 u).1
    unfold LocalPNT.pi0Dens
    apply div_nonneg _ (Real.log_pos hu).le
    have : 1 / u ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hgint : Integrable ((Icc a b).indicator (fun _ => c)) (volume.restrict (Ioi (1 : ℝ))) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Icc]
    exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Icc_lt_top).ne
  have hpi0 : LocalPNT.pi0Int φ ≤ (b - a) * c := by
    unfold LocalPNT.pi0Int
    calc ∫ u in Ioi (1 : ℝ), φ u * LocalPNT.pi0Dens u
        ≤ ∫ u in Ioi (1 : ℝ), (Icc a b).indicator (fun _ => c) u := by
          apply integral_mono_of_nonneg
          · exact ae_restrict_of_forall_mem measurableSet_Ioi hnn
          · exact hgint
          · exact ae_restrict_of_forall_mem measurableSet_Ioi hpt
      _ = ((volume.restrict (Ioi (1 : ℝ))) (Icc a b)).toReal * c := by
          rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Measure.real]
      _ ≤ (b - a) * c := by
          apply mul_le_mul_of_nonneg_right _ hc0.le
          rw [Measure.restrict_apply measurableSet_Icc]
          have hab : a ≤ b := by rw [ha, hb]; nlinarith
          calc ((volume (Icc a b ∩ Ioi (1 : ℝ)))).toReal ≤ (volume (Icc a b)).toReal :=
                ENNReal.toReal_mono measure_Icc_lt_top.ne (measure_mono Set.inter_subset_left)
            _ = b - a := by rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hpi0nn : 0 ≤ LocalPNT.pi0Int φ := by
    unfold LocalPNT.pi0Int
    exact setIntegral_nonneg measurableSet_Ioi hnn
  -- assembly
  set W := (P.primesLe (v * (1 + η))).filter (fun j => v ≤ P.p j)
  have hsum : ∑ j ∈ W, 1 / P.p j ≤ (W.card : ℝ) / v := by
    rw [div_eq_mul_one_div, Finset.card_eq_sum_ones]; push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [W, Finset.mem_filter] at hj
    rw [one_mul]
    exact one_div_le_one_div_of_le hv0 hj.2
  have hpiInt : (W.card : ℝ) ≤ 1.1 * ((b - a) * c) := by
    refine hcard.trans (hint.trans ?_)
    have : 1 + LocalPNT.relBound (Real.log X0) v η ≤ 1.1 := by linarith
    calc (1 + LocalPNT.relBound (Real.log X0) v η) * LocalPNT.pi0Int φ ≤ 1.1 * LocalPNT.pi0Int φ :=
          mul_le_mul_of_nonneg_right this hpi0nn
      _ ≤ 1.1 * ((b - a) * c) := by linarith
  have hba : b - a = v * (η + 2 * w) := by rw [ha, hb]; ring
  calc ∑ j ∈ W, 1 / P.p j ≤ (W.card : ℝ) / v := hsum
    _ ≤ 1.1 * (v * (η + 2 * w) * c) / v := by
        rw [← hba]; exact div_le_div_of_nonneg_right hpiInt hv0.le
    _ = 1.1 * (η + 2 * w) / (Lp - 2 * w) := by rw [hc]; field_simp
    _ ≤ 1.1001 * η / Lp := by
        rw [div_le_div_iff₀ hden hLp0, hwe]
        have hLp2 : 0 < Lp ^ 2 := by positivity
        have e : 1.1 * (η + 2 * (η / Lp ^ 2)) * Lp = 1.1 * η * Lp + 2.2 * η / Lp := by
          field_simp; ring
        have e2 : 1.1001 * η * (Lp - 2 * (η / Lp ^ 2)) =
            1.1001 * η * Lp - 2.2002 * η * η / Lp ^ 2 := by
          field_simp; ring
        rw [e, e2]
        have hLL : 1000000000000000000000000 * Lp ≤ Lp * Lp :=
          mul_le_mul_of_nonneg_right hLpbig hLp0.le
        have h1 : 2.2 * η / Lp ≤ 0.00005 * η * Lp := by
          rw [div_le_iff₀ hLp0]
          have := mul_le_mul_of_nonneg_left hLL hη.le
          nlinarith
        have h2 : 2.2002 * η * η / Lp ^ 2 ≤ 0.00005 * η * Lp := by
          rw [div_le_iff₀ hLp2]
          have : η * η ≤ η := by nlinarith
          have h3 : 1000000000000000000000000 * (Lp * Lp) ≤ Lp * (Lp * Lp) :=
            mul_le_mul_of_nonneg_right hLpbig (by positivity)
          have := mul_le_mul_of_nonneg_left h3 hη.le
          nlinarith
        nlinarith

end BridgeSI

end
