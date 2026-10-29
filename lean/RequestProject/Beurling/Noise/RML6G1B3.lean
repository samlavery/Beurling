module

public import RequestProject.Beurling.Noise.RML6G1B2

/-!
# Field `g1`, range (B), Step 3: the sizes of the pointwise changes

The bullets of Step 3 of the proof of Proposition 5.35(B) bound `ρ^sh(y) - ρ^sh(x)` for
`y ∈ J`. Proved here are the sizes the paper asserts for them, as explicit inequalities:

* `thresh_small` : threshold changes, `log x · 4 · (Lemma 5.23 at 2δ) ≤ 10⁻²⁷`, for
  `δ ≤ log⁻⁴ x`, `1 ≤ H(x) ≤ x^{1/8}`, `0 ≤ K_loc ≤ H(x)` (the `4` is `|T'| ≤ 2` twice);
* `jump_small` : the jump of `T'` at `X₀`, `log x · j₀ (4.1δ + 3H(N_*)/N_* + 2N_*^{θ/2-1}) ≤ 10⁻²⁷`
  for `j₀ ≤ 1`, `N_* = x/X₀ ≥ e^{(log x)/2}`, `H(N_*) ≤ N_*^{1/8}`, `0 ≤ θ ≤ 1/2`;
* `det_small` : the smooth change of `ρ_det`,
  `C_S [7Λ⁴X₀^{-1/12} + 90Λ^{4.7}e^{-Λ/12}] ≤ e^{-10⁶}` for `C_S ≤ 77`, `Λ ≥ 10⁸`.

Each takes the range-(B) hypotheses of `step1_g1` where needed.
-/

@[expose] public section

open Real

namespace KR.RML6

/-- `log x ≥ 10³¹` in range (B). -/
lemma logx_big {Λ L : ℝ} (hΛ : 100000000 ≤ Λ) (hL : Real.exp (Λ / 100) ≤ L) :
    (10 : ℝ) ^ 31 ≤ L := by
  have h6 := Real.pow_div_factorial_le_exp (x := Λ / 100) (by positivity) 6
  norm_num [Nat.factorial] at h6
  have hΛ6 : (100000000 : ℝ) ^ 6 ≤ Λ ^ 6 := pow_le_pow_left₀ (by norm_num) hΛ 6
  have : (10 : ℝ) ^ 31 ≤ (Λ / 100) ^ 6 / 720 := by
    rw [div_pow, le_div_iff₀ (by norm_num)]
    rw [le_div_iff₀ (by norm_num)]
    norm_num at hΛ6 ⊢; linarith
  linarith

/-- `log t ≤ t/8` and `2 log t ≤ t/8` for `t ≥ 10⁴`. -/
lemma two_log_le {t : ℝ} (ht : 10000 ≤ t) : 2 * Real.log t ≤ t / 8 := by
  have ht0 : 0 < t := by linarith
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht0)
  rw [Real.log_sqrt ht0.le] at h
  have hs : √t * √t = t := Real.mul_self_sqrt ht0.le
  have hs100 : 100 ≤ √t := by
    rw [show (100 : ℝ) = √(10000) by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  nlinarith

/-- In range (B), `1/δ ≤ e^{log x/16}`. -/
lemma invδ_le {X₀ : ℕ} {x δ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (_hx0 : 0 < x)
    (hx : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log x) (_hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log x) / 2) *
      Real.log x ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)) :
    1 / δ ≤ Real.exp (Real.log x / 16) := by
  set Λ := Real.log X₀ with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have hrp : ∀ a : ℝ, (X₀ : ℝ) ^ a = Real.exp (a * Λ) := fun a => by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  set L := Real.log x with hLdef
  have hL : Real.exp (Λ / 100) ≤ L := by
    rw [hrp] at hx; convert hx using 2; ring
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hs := sqrt_log_ge hΛ hL
  set s := √L with hsdef
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hΛ3' : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
  have hs0 : 0 < s := by nlinarith
  have hsbig : (10000 : ℝ) ≤ s := by nlinarith
  set c := LocalPNT.cLP Λ with hcdef
  have hc : c = 0.0176 / Λ := by
    rw [hcdef]; unfold LocalPNT.cLP LocalPNT.cZF; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hΛ0]; linarith
  have hL4 : L ^ 4 = Real.exp (8 * Real.log s) := by
    rw [← hss, ← pow_mul, show 8 * Real.log s = ((2 * 4 : ℕ) : ℝ) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs0]
  have hlog := two_log_le hsbig
  have hΛΛ : Λ ≤ Λ ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hΛs : Λ ≤ s := by nlinarith
  have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  refine hδlow.trans ?_
  rw [hL4, hrp, ← Real.exp_add]
  have hb1 : Real.exp (c * s / 2 + 8 * Real.log s) ≤ Real.exp (L / 16 - Real.log 2) := by
    apply Real.exp_le_exp.mpr
    rw [← hss]; nlinarith
  have hb2 : Real.exp (1 / 2 * Λ) ≤ Real.exp (L / 16 - Real.log 2) := by
    apply Real.exp_le_exp.mpr
    rw [← hss]; nlinarith
  have he : Real.exp (L / 16 - Real.log 2) + Real.exp (L / 16 - Real.log 2) =
      Real.exp (L / 16) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]; ring
  linarith

/-- **Threshold changes** (Step 3, first bullet): `log x · 4 · (Lemma 5.23 at 2δ) ≤ 10⁻²⁷`. -/
theorem thresh_small {X₀ : ℕ} {x δ Hx Kloc : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hx0 : 0 < x)
    (hx : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log x) (hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log x) / 2) *
      Real.log x ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ))
    (hδL : δ ≤ 1 / Real.log x ^ 4) (hH1 : 1 ≤ Hx) (hH : Hx ≤ Real.exp (Real.log x / 8))
    (hK0 : 0 ≤ Kloc) (hK : Kloc ≤ Hx) :
    Real.log x * 4 * (55 * (2 * δ) * Real.log x * (Real.log Hx + Real.log (1 / (2 * δ)) + 2) +
      14 * (Kloc + 2) * Real.log x * √(Hx / (2 * δ * x))) ≤ 1 / 10 ^ 27 := by
  set L := Real.log x with hLdef
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hL : Real.exp (Real.log X₀ / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hX0] at hx; convert hx using 2; ring
  have hLbig := logx_big hΛ hL
  have hL0 : 0 < L := by linarith
  have hiδ := invδ_le hΛ hx0 hx hδ0 hδlow
  rw [← hLdef] at hiδ
  have hxe : x = Real.exp L := (Real.exp_log hx0).symm
  -- part 1
  have hlogH : Real.log Hx ≤ L / 8 := by
    have := Real.log_le_log (by linarith) hH; rwa [Real.log_exp] at this
  have hlogδ : Real.log (1 / (2 * δ)) ≤ L / 16 := by
    have hpos : 0 < 1 / (2 * δ) := by positivity
    have h1 : 1 / (2 * δ) ≤ 1 / δ := by
      apply one_div_le_one_div_of_le hδ0; linarith
    have := Real.log_le_log hpos (h1.trans hiδ); rwa [Real.log_exp] at this
  have hlogH0 : 0 ≤ Real.log Hx := Real.log_nonneg hH1
  have hbr : Real.log Hx + Real.log (1 / (2 * δ)) + 2 ≤ L := by linarith
  have hbr0 : 0 ≤ Real.log Hx + Real.log (1 / (2 * δ)) + 2 := by
    have : 0 ≤ Real.log (1 / (2 * δ)) ∨ Real.log (1 / (2 * δ)) < 0 := le_or_gt _ _
    -- `1/(2δ) ≥ 1` would suffice; we only need an upper bound, so handle both signs
    rcases this with h | h
    · linarith
    · -- then `2δ > 1`, impossible since `δ ≤ L^{-4} ≤ 1/2`
      have hL4 : (2 : ℝ) ≤ L ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ L by linarith) 4
        linarith [show (2 : ℝ) ≤ 2 ^ 4 by norm_num]
      have hδh : δ ≤ 1 / 2 := hδL.trans (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      have : 1 ≤ 1 / (2 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
      have := Real.log_nonneg this; linarith
  have hδL3 : δ * L ^ 3 ≤ 1 / L := by
    rw [le_div_iff₀ hL0]
    have := mul_le_mul_of_nonneg_right hδL (show (0 : ℝ) ≤ L ^ 4 by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith
  have hP1 : L * 4 * (55 * (2 * δ) * L * (Real.log Hx + Real.log (1 / (2 * δ)) + 2)) ≤
      440 / L := by
    have : L * 4 * (55 * (2 * δ) * L * (Real.log Hx + Real.log (1 / (2 * δ)) + 2)) ≤
        440 * (δ * L ^ 3) := by
      have h := mul_le_mul_of_nonneg_left hbr (show (0 : ℝ) ≤ 440 * δ * L ^ 2 by positivity)
      nlinarith
    calc _ ≤ 440 * (δ * L ^ 3) := this
      _ ≤ 440 * (1 / L) := by gcongr
      _ = 440 / L := by ring
  -- part 2
  have hq : Hx / (2 * δ * x) ≤ Real.exp (-(13 * L / 16)) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Hx ≤ Real.exp (L / 8) := hH
    have h2 : 1 ≤ 2 * δ * Real.exp (L / 16) := by
      rw [div_le_iff₀ hδ0] at hiδ; linarith
    calc Hx ≤ Real.exp (L / 8) := h1
      _ ≤ Real.exp (L / 8) * (2 * δ * Real.exp (L / 16)) :=
          le_mul_of_one_le_right (Real.exp_pos _).le h2
      _ = Real.exp (-(13 * L / 16)) * (2 * δ * x) := by
          rw [hxe]
          have : Real.exp (L / 8) * Real.exp (L / 16) = Real.exp (-(13 * L / 16)) * Real.exp L := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (2 * δ) * this
  have hsq : √(Hx / (2 * δ * x)) ≤ Real.exp (-(13 * L / 32)) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le]
    refine hq.trans (le_of_eq ?_)
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hL2 : L ^ 2 ≤ Real.exp (L / 8) := by
    have h := two_log_le (show (10000 : ℝ) ≤ L by linarith)
    calc L ^ 2 = Real.exp (2 * Real.log L) := by
          rw [show (2 : ℝ) * Real.log L = ((2 : ℕ) : ℝ) * Real.log L by norm_num,
            Real.exp_nat_mul, Real.exp_log hL0]
      _ ≤ Real.exp (L / 8) := Real.exp_le_exp.mpr h
  have hKH : Kloc + 2 ≤ 3 * Real.exp (L / 8) := by linarith
  have hP2 : L * 4 * (14 * (Kloc + 2) * L * √(Hx / (2 * δ * x))) ≤
      168 * Real.exp (-(5 * L / 32)) := by
    have hs0 : 0 ≤ √(Hx / (2 * δ * x)) := Real.sqrt_nonneg _
    calc L * 4 * (14 * (Kloc + 2) * L * √(Hx / (2 * δ * x)))
        = 56 * L ^ 2 * (Kloc + 2) * √(Hx / (2 * δ * x)) := by ring
      _ ≤ 56 * Real.exp (L / 8) * (3 * Real.exp (L / 8)) * Real.exp (-(13 * L / 32)) := by
          gcongr
      _ = 168 * Real.exp (-(5 * L / 32)) := by
          rw [show (56 : ℝ) * Real.exp (L / 8) * (3 * Real.exp (L / 8)) *
              Real.exp (-(13 * L / 32)) = 168 * (Real.exp (L / 8) * Real.exp (L / 8) *
              Real.exp (-(13 * L / 32))) by ring, ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
  have he : Real.exp (-(5 * L / 32)) ≤ Real.exp (-200) := Real.exp_le_exp.mpr (by linarith)
  have h200 : 168 * Real.exp (-200) ≤ 1 / (2 * 10 ^ 27) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : (2.7 : ℝ) ^ 200 ≤ Real.exp 1 ^ 200 := pow_le_pow_left₀ (by norm_num) (by linarith) 200
    have h2 : (168 * (2 * 10 ^ 27) : ℝ) ≤ 1 * 2.7 ^ 200 := by norm_num
    linarith
  have h440 : 440 / L ≤ 1 / (2 * 10 ^ 27) := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  rw [mul_add]
  have : (1 : ℝ) / (2 * 10 ^ 27) + 1 / (2 * 10 ^ 27) = 1 / 10 ^ 27 := by norm_num
  linarith

/-- **The jump at `X₀`** (Step 3, second bullet):
`log x · j₀ (4.1δ + 3H(N_*)/N_* + 2N_*^{θ/2-1}) ≤ 10⁻²⁷`. -/
theorem jump_small {X₀ : ℕ} {x δ j0 N HN θ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (_hx0 : 0 < x)
    (hx : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log x) (hδ0 : 0 < δ)
    (hδL : δ ≤ 1 / Real.log x ^ 4) (_hj0 : 0 ≤ j0) (hj1 : j0 ≤ 1)
    (hN : Real.exp (Real.log x / 2) ≤ N) (hHN0 : 0 ≤ HN) (hHN : HN ≤ N ^ (1 / 8 : ℝ))
    (_hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) :
    Real.log x * j0 * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1)) ≤ 1 / 10 ^ 27 := by
  set L := Real.log x with hLdef
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have hL : Real.exp (Real.log X₀ / 100) ≤ L := by
    rw [Real.rpow_def_of_pos hX0] at hx; convert hx using 2; ring
  have hLbig := logx_big hΛ hL
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hN
  have hN1 : 1 ≤ N := le_trans (Real.one_le_exp (by linarith)) hN
  have hlogN : L / 2 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos _) hN; rwa [Real.log_exp] at this
  have hrp : ∀ a : ℝ, N ^ a = Real.exp (a * Real.log N) := fun a => by
    rw [Real.rpow_def_of_pos hN0, mul_comm]
  -- the three terms
  have hT1 : L * (4.1 * δ) ≤ 5 / L ^ 3 := by
    have hL4 : 0 < L ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hδL (show (0 : ℝ) ≤ 4.1 * L by positivity)
    calc L * (4.1 * δ) = 4.1 * L * δ := by ring
      _ ≤ 4.1 * L * (1 / L ^ 4) := this
      _ ≤ 5 / L ^ 3 := by
          rw [show 4.1 * L * (1 / L ^ 4) = 4.1 / L ^ 3 by field_simp]
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hL2 : L ≤ Real.exp (L / 16) := by
    have h := two_log_le (show (10000 : ℝ) ≤ L by linarith)
    calc L = Real.exp (Real.log L) := (Real.exp_log hL0).symm
      _ ≤ Real.exp (L / 16) := Real.exp_le_exp.mpr (by
          have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
          linarith)
  have hT2 : L * (3 * HN / N) ≤ 3 * Real.exp (-(3 * L / 8)) := by
    have hHN' : HN / N ≤ Real.exp (-(7 * L / 16)) := by
      rw [div_le_iff₀ hN0]
      calc HN ≤ N ^ (1 / 8 : ℝ) := hHN
        _ = N ^ (-(7 / 8) : ℝ) * N := by
            rw [← Real.rpow_add_one hN0.ne']; norm_num
        _ ≤ Real.exp (-(7 * L / 16)) * N := by
            apply mul_le_mul_of_nonneg_right _ hN0.le
            rw [hrp]; apply Real.exp_le_exp.mpr; nlinarith
    calc L * (3 * HN / N) = 3 * (L * (HN / N)) := by ring
      _ ≤ 3 * (Real.exp (L / 16) * Real.exp (-(7 * L / 16))) := by
          gcongr
      _ = 3 * Real.exp (-(3 * L / 8)) := by rw [← Real.exp_add]; congr 2; ring
  have hT3 : L * (2 * N ^ (θ / 2 - 1)) ≤ 2 * Real.exp (-(5 * L / 16)) := by
    have hp : N ^ (θ / 2 - 1) ≤ Real.exp (-(3 * L / 8)) := by
      rw [hrp]; apply Real.exp_le_exp.mpr
      have : θ / 2 - 1 ≤ -(3 / 4) := by linarith
      nlinarith
    calc L * (2 * N ^ (θ / 2 - 1)) = 2 * (L * N ^ (θ / 2 - 1)) := by ring
      _ ≤ 2 * (Real.exp (L / 16) * Real.exp (-(3 * L / 8))) := by
          have : 0 ≤ N ^ (θ / 2 - 1) := Real.rpow_nonneg hN0.le _
          gcongr
      _ = 2 * Real.exp (-(5 * L / 16)) := by rw [← Real.exp_add]; congr 2; ring
  have hsum : L * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1)) ≤ 1 / 10 ^ 27 := by
    have he1 : Real.exp (-(3 * L / 8)) ≤ Real.exp (-200) := Real.exp_le_exp.mpr (by linarith)
    have he2 : Real.exp (-(5 * L / 16)) ≤ Real.exp (-200) := Real.exp_le_exp.mpr (by linarith)
    have h200 : 5 * Real.exp (-200) ≤ 1 / (2 * 10 ^ 27) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have : (2.7 : ℝ) ^ 200 ≤ Real.exp 1 ^ 200 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 200
      have h2 : (5 * (2 * 10 ^ 27) : ℝ) ≤ 1 * 2.7 ^ 200 := by norm_num
      linarith
    have h5 : 5 / L ^ 3 ≤ 1 / (2 * 10 ^ 27) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (10 : ℝ) ^ 93 ≤ L ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num) hLbig 3; norm_num at this ⊢; linarith
      nlinarith
    have : (1 : ℝ) / (2 * 10 ^ 27) + 1 / (2 * 10 ^ 27) = 1 / 10 ^ 27 := by norm_num
    rw [mul_add, mul_add]
    linarith
  have hnn : 0 ≤ L * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1)) := by
    have : 0 ≤ N ^ (θ / 2 - 1) := Real.rpow_nonneg hN0.le _
    positivity
  calc L * j0 * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1))
      = j0 * (L * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1))) := by ring
    _ ≤ 1 * (L * (4.1 * δ + 3 * HN / N + 2 * N ^ (θ / 2 - 1))) :=
        mul_le_mul_of_nonneg_right hj1 hnn
    _ ≤ 1 / 10 ^ 27 := by rw [one_mul]; exact hsum

/-- **The smooth change of `ρ_det`** (Step 3, third bullet), the final numerical bound:
`C_S [7Λ⁴ X₀^{-1/12} + 90 Λ^{4.7} e^{-Λ/12}] ≤ e^{-10⁶}` for `0 ≤ C_S ≤ 77`, `Λ = log X₀ ≥ 10⁸`. -/
theorem det_small {X₀ : ℕ} {CS : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (_hCS0 : 0 ≤ CS)
    (hCS : CS ≤ 77) :
    CS * (7 * Real.log X₀ ^ 4 * (X₀ : ℝ) ^ (-(1 / 12) : ℝ) +
      90 * Real.log X₀ ^ (4.7 : ℝ) * Real.exp (-(Real.log X₀ / 12))) ≤
      Real.exp (-1000000) := by
  set Λ := Real.log X₀ with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have hX : (X₀ : ℝ) ^ (-(1 / 12) : ℝ) = Real.exp (-(Λ / 12)) := by
    rw [Real.rpow_def_of_pos hX0]; congr 1; ring
  rw [hX]
  -- `Λ⁴ ≤ Λ⁵` and `Λ^{4.7} ≤ Λ⁵`, `Λ⁵ = e^{5 log Λ}`, `5 log Λ ≤ Λ/1000`
  have hΛ1 : 1 ≤ Λ := by linarith
  have h4 : Λ ^ 4 ≤ Λ ^ 5 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have h47 : Λ ^ (4.7 : ℝ) ≤ Λ ^ 5 := by
    rw [show (Λ ^ 5 : ℝ) = Λ ^ ((5 : ℕ) : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hlog : 5 * Real.log Λ ≤ Λ / 1000 := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hΛ0)
    rw [Real.log_sqrt hΛ0.le] at h
    have hs : √Λ * √Λ = Λ := Real.mul_self_sqrt hΛ0.le
    have hs1 : 10000 ≤ √Λ := by
      rw [show (10000 : ℝ) = √(100000000) by
        rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hΛ
    nlinarith
  have h5 : Λ ^ 5 = Real.exp (5 * Real.log Λ) := by
    rw [show (5 : ℝ) * Real.log Λ = ((5 : ℕ) : ℝ) * Real.log Λ by norm_num, Real.exp_nat_mul,
      Real.exp_log hΛ0]
  have hE : 0 < Real.exp (-(Λ / 12)) := Real.exp_pos _
  calc CS * (7 * Λ ^ 4 * Real.exp (-(Λ / 12)) + 90 * Λ ^ (4.7 : ℝ) * Real.exp (-(Λ / 12)))
      ≤ 77 * (7 * Λ ^ 5 * Real.exp (-(Λ / 12)) + 90 * Λ ^ 5 * Real.exp (-(Λ / 12))) := by
        apply mul_le_mul hCS _ (by positivity) (by norm_num)
        gcongr
    _ = 7469 * Real.exp (5 * Real.log Λ - Λ / 12) := by
        rw [h5, sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp 9 * Real.exp (-1000009) := by
        apply mul_le_mul _ (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
          (Real.exp_pos _).le
        have h := Real.exp_one_gt_d9
        have e : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        have : (2.718 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) (by linarith) 9
        have h2 : (7469 : ℝ) ≤ 2.718 ^ 9 := by norm_num
        linarith
    _ = Real.exp (-1000000) := by rw [← Real.exp_add]; norm_num

end KR.RML6

end
