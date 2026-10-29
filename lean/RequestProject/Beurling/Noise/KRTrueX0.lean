module

public import RequestProject.Beurling.Noise.KRTrueTerm
public import RequestProject.Beurling.Noise.KRTrueX0Aux
public import RequestProject.Beurling.Noise.Saias59

/-!
# Proposition 5.18, step (iii): the bullets `EtaX0Sum`

`η_{X₀}(v) = ∑_{w ∈ 𝒩 : |v - w X₀⁻| ≤ 1.02 H(v)} 1/w` (`etaX0`). The paper's step (iii)
(04k-kernels.tex, proof of Proposition 5.18) proves

* for `v ≤ X₀²/2` the `w`-window has length `2.04H(v)/X₀⁻ < 1` and lies below `X₀⁻`, where
  `𝒩 = ℕ`: it holds at most one `w`, and `η_{X₀}(v) ≤ 1.01 X₀/v` (`etaX0_le_mid`); it is
  empty for `v < X₀` (`etaX0_eq_zero_low`), and at most `1/2` (as `w ≥ 2`);
* for `v > X₀²/2` the window holds at most
  `4.21 H(v)/X₀ + 2H(v/X₀) + 4 + 2(v/X₀)^{θ/2}` elements (the lag bound of Corollary 3.8, the
  target (6) and Lemma 6.26 / Lemma P for the absorbed set; the named input `count` below),
  so `η_{X₀}(v) ≤ 1.01(4 + 8.21 v^{1/4}) X₀/v` (`etaX0_le_high`);
* hence `∑_{v dyadic} log(2v) sup_{[v,2v)} η_{X₀} ≤ 1.52 log(2X₀)` (`etaX0Sum_of`).

`etaX0Sum_of` proves `EtaX0Sum P H X₀⁻ X₀ Sc (sX0 X₀)` for every family of dyadic scales
`Sc ⊆ {X₀ 2^k : k ∈ ℤ}` (the paper's dyadic `v`), with the explicit block bounds `sX0`.
We obtain `∑ log(2v) s_v ≤ L/2 + 1.01 (L + 4.84) + 1` with `L = log(2X₀)`: the block
`[X₀, 2X₀)` contributes `≤ L/2` (paper: `0.506 L`), the blocks above `≤ 1.01(L + 4.84)`.

The standing hypotheses (`Hyp`): (HBS) on `[1, Z]` with `X₀⁻ ≤ Z`, `log X₀ ≥ 10⁸`,
`X₀⁻ = X₀ - H(X₀)/2`, `H ≥ 0` and the growth of the width `H(y)^8 ≤ max(y, X₀⁻/2)` (the paper's
`H(x) ≤ x^{1/8}`, `InitialRange.capH_le_rpow` for `x ≥ X₀`), `0 ≤ θ ≤ 1/2`, and the window
count `count` for `v > X₀²/2` (the construction input above).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.X0S

variable {P : BeurlingSystem} {H : ℝ → ℝ} {X0m X0 Z η1 η2 θo Y : ℝ} {ε1 : ℝ → ℝ}

/-- The `w`-window of `η_{X₀}(y)`. -/
noncomputable def Win (P : BeurlingSystem) (H : ℝ → ℝ) (X0m y : ℝ) : Finset ℕ :=
  open scoped Classical in
  (CofH P X0m y).filter (fun m => |y - Vl P m * X0m| ≤ 1.02 * H y)

/-- **The standing hypotheses of step (iii).** -/
structure Hyp (P : BeurlingSystem) (H : ℝ → ℝ) (X0m X0 Z η1 η2 : ℝ) (ε1 : ℝ → ℝ)
    (θo Y : ℝ) : Prop where
  hbs : P.HBS X0m Z η1 η2 ε1
  hZ : X0m ≤ Z
  hX0pos : 0 < X0
  hX0 : 100000000 ≤ Real.log X0
  hX0e : X0m = X0 - H X0 / 2
  hH0 : ∀ y, 0 ≤ H y
  /-- the growth of the jitter width, `H(y) ≤ max(y, X₀⁻/2)^{1/8}` -/
  hHg : ∀ y, 0 < y → H y ^ 8 ≤ max y (X0m / 2)
  hθ0 : 0 ≤ θo
  hθ1 : θo ≤ 1 / 2
  /-- **the window count of step (iii), second bullet** (Corollary 3.8, target (6),
  Lemma 6.26): for `X₀²/2 < y ≤ Y` the window holds at most
  `4.21 H(y)/X₀ + 2H(y/X₀) + 4 + 2(y/X₀)^{θ/2}` elements (localized to the heights `≤ Y`) -/
  count : ∀ y, X0 ^ 2 / 2 < y → y ≤ Y →
    ((Win P H X0m y).card : ℝ) ≤ 4.21 * H y / X0 + 2 * H (y / X0) + 4 + 2 * (y / X0) ^ (θo / 2)

/-! ## Numerical facts for `t = X₀^{1/8} ≥ 10¹²` -/

lemma num_pow7 {t : ℝ} (ht : 10 ^ 12 ≤ t) : (10 : ℝ) ^ 84 ≤ t ^ 7 := by
  calc (10 : ℝ) ^ 84 = ((10 : ℝ) ^ 12) ^ 7 := by norm_num
    _ ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7

lemma num_low {t : ℝ} (ht : 10 ^ 12 ≤ t) : 4 * t ≤ t ^ 8 := by
  have h7 := num_pow7 ht
  have h0 : 0 ≤ t := le_trans (by norm_num) ht
  calc 4 * t ≤ t ^ 7 * t := mul_le_mul_of_nonneg_right (le_trans (by norm_num) h7) h0
    _ = t ^ 8 := by ring

lemma num_mid1 {t : ℝ} (ht : 10 ^ 12 ≤ t) :
    (t ^ 8) ^ 2 / 2 + 1.02 * t ^ 2 < t ^ 8 * t ^ 8 - t ^ 8 * t := by
  have h7 := num_pow7 ht
  have h0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h1 : 4 * t ^ 9 ≤ t ^ 16 := by
    calc 4 * t ^ 9 ≤ t ^ 7 * t ^ 9 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) h7)
          (by positivity)
      _ = t ^ 16 := by ring
  have h2 : 2 * t ^ 2 ≤ t ^ 9 := by
    calc 2 * t ^ 2 ≤ t ^ 7 * t ^ 2 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) h7)
          (by positivity)
      _ = t ^ 9 := by ring
  have e1 : (t ^ 8) ^ 2 = t ^ 16 := by ring
  have e2 : t ^ 8 * t ^ 8 = t ^ 16 := by ring
  have e3 : t ^ 8 * t = t ^ 9 := by ring
  rw [e1, e2, e3]
  have : 0 < t ^ 2 := by positivity
  linarith

lemma num_mid2 {t : ℝ} (ht : 10 ^ 12 ≤ t) : 2.04 * t ^ 2 + t / 2 < t ^ 8 := by
  have h7 := num_pow7 ht
  have h0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h6 : (10 : ℝ) ^ 72 ≤ t ^ 6 := by
    calc (10 : ℝ) ^ 72 = ((10 : ℝ) ^ 12) ^ 6 := by norm_num
      _ ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht 6
  have h1 : 3 * t ^ 2 ≤ t ^ 8 := by
    calc 3 * t ^ 2 ≤ t ^ 6 * t ^ 2 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) h6)
          (by positivity)
      _ = t ^ 8 := by ring
  have h2 : t ≤ t ^ 2 := by nlinarith
  nlinarith

namespace Hyp

variable (hy : Hyp P H X0m X0 Z η1 η2 ε1 θo Y)
include hy

/-! ## Sizes -/

lemma X0_big : (10 : ℝ) ^ 100 ≤ X0 := by
  have h1 : Real.exp 400 ≤ X0 := by
    rw [← Real.exp_log hy.hX0pos]; exact Real.exp_le_exp.mpr (by linarith [hy.hX0])
  have h2 : (10 : ℝ) ^ 100 ≤ Real.exp 400 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have : Real.exp 400 = Real.exp 1 ^ 400 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (10 : ℝ) ^ 100 ≤ 16 ^ 100 := pow_le_pow_left₀ (by norm_num) (by norm_num) 100
      _ = 2 ^ 400 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
      _ ≤ Real.exp 1 ^ 400 := pow_le_pow_left₀ (by norm_num) he 400
  linarith

/-- `t = X₀^{1/8}`. -/
lemma t_pow : r8 X0 ^ 8 = X0 := r8_pow8 hy.hX0pos.le

lemma t_big : (10 : ℝ) ^ 12 ≤ r8 X0 := by
  by_contra h
  push_neg at h
  have h1 : r8 X0 ^ 8 < ((10 : ℝ) ^ 12) ^ 8 :=
    pow_lt_pow_left₀ h (r8_nonneg _) (by norm_num)
  rw [hy.t_pow] at h1
  have := hy.X0_big
  norm_num at h1
  linarith

lemma HX0_le : H X0 ≤ r8 X0 := by
  refine le_r8_of_pow8 (hy.hH0 X0) ((hy.hHg X0 hy.hX0pos).trans (le_of_eq (max_eq_left ?_)))
  have := hy.hH0 X0
  have := hy.hX0pos
  rw [hy.hX0e]; linarith

lemma Xm_ge : X0 - r8 X0 / 2 ≤ X0m := by rw [hy.hX0e]; linarith [hy.HX0_le]

lemma Xm_le : X0m ≤ X0 := by rw [hy.hX0e]; linarith [hy.hH0 X0]

lemma t_le_X0 : r8 X0 ≤ X0 := by
  have h2 := hy.t_big
  have h3 := hy.t_pow
  have h7 : (1 : ℝ) ≤ r8 X0 ^ 7 := one_le_pow₀ (le_trans (by norm_num) h2)
  have e : r8 X0 ^ 8 = r8 X0 ^ 7 * r8 X0 := by ring
  have := r8_nonneg X0
  nlinarith

lemma Xm_pos : 0 < X0m := by
  have h1 := hy.Xm_ge
  have h2 := hy.t_big
  have h4 := hy.t_le_X0
  linarith

/-- `H(y) ≤ y^{1/8}` for `y ≥ X₀⁻/2`. -/
lemma H_le_r8 {y : ℝ} (hy0 : X0m / 2 ≤ y) : H y ≤ r8 y := by
  have hy1 : 0 < y := lt_of_lt_of_le (by linarith [hy.Xm_pos]) hy0
  exact le_r8_of_pow8 (hy.hH0 y) ((hy.hHg y hy1).trans (le_of_eq (max_eq_left hy0)))

/-- `H(y) ≤ X₀^{1/8}` for `0 < y ≤ X₀`. -/
lemma H_le_t {y : ℝ} (hy0 : 0 < y) (hyX : y ≤ X0) : H y ≤ r8 X0 := by
  refine le_r8_of_pow8 (hy.hH0 y) ((hy.hHg y hy0).trans (max_le hyX ?_))
  linarith [hy.Xm_le, hy.Xm_pos]

/-- `H(y) ≤ 10⁻³ y` for `y ≥ X₀`. -/
lemma H_small {y : ℝ} (hyX : X0 ≤ y) : H y ≤ y / 1000 := by
  have hXm := hy.Xm_le
  have hy1 : X0m / 2 ≤ y := by linarith [hy.Xm_pos]
  have h1 := hy.H_le_r8 hy1
  have hr : r8 X0 ≤ r8 y := r8_mono hyX
  have ht := hy.t_big
  have hy0 : 0 ≤ y := by linarith [hy.hX0pos]
  have hp := r8_pow8 hy0
  have : 1000 * r8 y ≤ y := by
    have hb : (10 : ℝ) ^ 12 ≤ r8 y := ht.trans hr
    have h7 : (1000 : ℝ) ≤ r8 y ^ 7 := by
      calc (1000 : ℝ) ≤ ((10 : ℝ) ^ 12) ^ 7 := by norm_num
        _ ≤ r8 y ^ 7 := pow_le_pow_left₀ (by norm_num) hb 7
    have e : r8 y ^ 8 = r8 y ^ 7 * r8 y := by ring
    have h0 := r8_nonneg y
    calc 1000 * r8 y ≤ r8 y ^ 7 * r8 y := mul_le_mul_of_nonneg_right h7 h0
      _ = y := by rw [← e, hp]
  linarith

/-! ## Elements of the window -/

omit hy in
lemma mem_Win {y : ℝ} {m : ℕ} (hm : m ∈ Win P H X0m y) :
    ∃ e : ℕ →₀ ℕ, m = iota e ∧ 2 ≤ iota e ∧ |y - P.val e * X0m| ≤ 1.02 * H y := by
  classical
  unfold Win CofH at hm
  simp only [Finset.mem_filter, Finset.mem_image] at hm
  obtain ⟨⟨⟨e, -, rfl⟩, h2⟩, hw⟩ := hm
  refine ⟨e, rfl, h2, ?_⟩
  have : Vl P (iota e) = P.val e := P.valN_iota e
  rw [this] at hw; exact hw

/-- Below `X₀⁻` the elements are integers. -/
lemma val_eq_nat {e : ℕ →₀ ℕ} (he : P.val e < X0m) : P.val e = (iota e : ℝ) := by
  apply P.val_eq_iota
  intro i hi
  exact hy.hbs.ident (x := P.val e) he (by linarith [hy.hZ]) i (Or.inl (P.p_le_val hi))

lemma term_le {y : ℝ} (hpos : 0 < y - 1.02 * H y) {m : ℕ} (hm : m ∈ Win P H X0m y) :
    1 / Vl P m ≤ X0m / (y - 1.02 * H y) := by
  obtain ⟨e, rfl, -, hw⟩ := mem_Win hm
  have hv : Vl P (iota e) = P.val e := P.valN_iota e
  rw [hv]
  have hXm := hy.Xm_pos
  have hval := P.val_pos e
  rw [abs_le] at hw
  rw [div_le_div_iff₀ hval hpos]
  linarith [hw.2]

lemma eta_le_card {y : ℝ} (hpos : 0 < y - 1.02 * H y) :
    etaX0 P H X0m y ≤ (Win P H X0m y).card * (X0m / (y - 1.02 * H y)) := by
  have e : etaX0 P H X0m y = ∑ m ∈ Win P H X0m y, 1 / Vl P m := rfl
  rw [e]
  have := Finset.sum_le_card_nsmul (Win P H X0m y) (fun m => 1 / Vl P m)
    (X0m / (y - 1.02 * H y)) (fun m hm => hy.term_le hpos hm)
  simpa [nsmul_eq_mul] using this

omit hy in
lemma etaX0_nonneg (y : ℝ) : 0 ≤ etaX0 P H X0m y := by
  unfold etaX0
  exact Finset.sum_nonneg fun m _ => (one_div_pos.mpr (KR.valN_labelVal_pos P m)).le

/-! ## The first bullet -/

/-- `η_{X₀}(y) = 0` for `0 < y < X₀`. -/
theorem etaX0_eq_zero_low {y : ℝ} (hy0 : 0 < y) (hyX : y < X0) : etaX0 P H X0m y = 0 := by
  have hW : Win P H X0m y = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    obtain ⟨e, rfl, h2, hw⟩ := mem_Win hm
    have hH := hy.H_le_t hy0 hyX.le
    have hHX := hy.HX0_le
    have ht := hy.t_big
    have htp := hy.t_pow
    have hXm := hy.Xm_ge
    have hXmp := hy.Xm_pos
    have hbig : X0 + 2.02 * r8 X0 < 2 * X0m := by
      have h8 := num_low ht
      rw [htp] at h8
      have hpos : 0 < r8 X0 := lt_of_lt_of_le (by norm_num) ht
      rw [hy.hX0e]; linarith
    rw [abs_le] at hw
    have hv : P.val e * X0m < 2 * X0m := by linarith [hw.1, hy.hH0 y]
    have hv2 : P.val e < 2 := by nlinarith
    have hvX : P.val e < X0m := by
      have : (2 : ℝ) < X0m := by
        have := hy.X0_big
        nlinarith [pow_le_pow_left₀ (by norm_num) ht 8]
      linarith
    rw [hy.val_eq_nat hvX] at hv2
    have : (2 : ℝ) ≤ (iota e : ℝ) := by exact_mod_cast h2
    linarith
  unfold etaX0
  have : (CofH P X0m y).filter (fun m => |y - Vl P m * X0m| ≤ 1.02 * H y) = ∅ := by
    rw [← hW]; unfold Win; congr
  rw [this, Finset.sum_empty]

/-- For `X₀ ≤ y ≤ X₀²/2` the window holds at most one element, of value `≥ 2`:
`η_{X₀}(y) ≤ 1/2` and `η_{X₀}(y) ≤ 1.01 X₀/y`. -/
theorem etaX0_le_mid {y : ℝ} (hyX : X0 ≤ y) (hy2 : y ≤ X0 ^ 2 / 2) :
    etaX0 P H X0m y ≤ 1 / 2 ∧ etaX0 P H X0m y ≤ 1.01 * X0 / y := by
  have ht := hy.t_big
  have htp := hy.t_pow
  have hXm := hy.Xm_ge
  have hXmp := hy.Xm_pos
  have hXmle := hy.Xm_le
  have hX0p := hy.hX0pos
  have hy1 : X0m / 2 ≤ y := by linarith
  have hH1 := hy.H_le_r8 hy1
  have hH0 := hy.hH0 y
  -- `H(y) ≤ t²`
  have hHt : H y ≤ r8 X0 ^ 2 := by
    have : r8 y ≤ r8 (X0 ^ 2) := r8_mono (by nlinarith)
    rw [pow_two, r8_mul hX0p.le hX0p.le] at this
    nlinarith
  have hX0eq : X0 = r8 X0 ^ 8 := htp.symm
  have ht0 : 0 ≤ r8 X0 := r8_nonneg _
  -- the window lies below `X₀⁻` and has length `< 1`
  have hlow : y + 1.02 * H y < X0m * X0m := by
    have h1 : X0 * X0 - X0 * r8 X0 ≤ X0m * X0m := by nlinarith
    have h2 : X0 ^ 2 / 2 + 1.02 * r8 X0 ^ 2 < X0 * X0 - X0 * r8 X0 := by
      have := num_mid1 ht
      rw [htp] at this; exact this
    nlinarith
  have hlen : 2.04 * H y < X0m := by
    have : 2.04 * r8 X0 ^ 2 + r8 X0 / 2 < X0 := by
      have := num_mid2 ht
      rw [htp] at this; exact this
    nlinarith
  have hpos : 0 < y - 1.02 * H y := by have := hy.H_small hyX; linarith
  -- the elements in the window are integers `≥ 2`, and there is at most one
  have hint : ∀ m ∈ Win P H X0m y, ∃ e : ℕ →₀ ℕ, m = iota e ∧ 2 ≤ iota e ∧
      P.val e = (iota e : ℝ) ∧ |y - (iota e : ℝ) * X0m| ≤ 1.02 * H y := by
    intro m hm
    obtain ⟨e, rfl, h2, hw⟩ := mem_Win hm
    have hval : P.val e < X0m := by
      rw [abs_le] at hw
      have : P.val e * X0m < X0m * X0m := by linarith [hw.1]
      exact lt_of_mul_lt_mul_right this hXmp.le
    have hv := hy.val_eq_nat hval
    exact ⟨e, rfl, h2, hv, by rw [← hv]; exact hw⟩
  have hcard : (Win P H X0m y).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨e1, rfl, -, -, hw1⟩ := hint a ha
    obtain ⟨e2, rfl, -, -, hw2⟩ := hint b hb
    rw [abs_le] at hw1 hw2
    have hd : |((iota e1 : ℕ) : ℝ) - (iota e2 : ℕ)| * X0m < X0m := by
      rw [← abs_of_pos hXmp, ← abs_mul, abs_of_pos hXmp, abs_lt]
      constructor <;> nlinarith
    have hd1 : |((iota e1 : ℕ) : ℝ) - (iota e2 : ℕ)| < 1 := by
      by_contra hc; push_neg at hc; nlinarith
    have : (iota e1 : ℤ) = iota e2 := by
      rw [abs_lt] at hd1
      have h1 : ((iota e1 : ℤ) : ℝ) - (iota e2 : ℤ) < 1 := by push_cast; linarith [hd1.2]
      have h2 : -1 < ((iota e1 : ℤ) : ℝ) - (iota e2 : ℤ) := by push_cast; linarith [hd1.1]
      have h1' : (iota e1 : ℤ) - iota e2 < 1 := by exact_mod_cast h1
      have h2' : -1 < (iota e1 : ℤ) - iota e2 := by exact_mod_cast h2
      omega
    exact_mod_cast this
  have hcard' : ((Win P H X0m y).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  have e : etaX0 P H X0m y = ∑ m ∈ Win P H X0m y, 1 / Vl P m := rfl
  constructor
  · rw [e]
    have hb : ∀ m ∈ Win P H X0m y, 1 / Vl P m ≤ 1 / 2 := by
      intro m hm
      obtain ⟨e', rfl, h2, hv, -⟩ := hint m hm
      have : Vl P (iota e') = P.val e' := P.valN_iota e'
      rw [this, hv]
      have : (2 : ℝ) ≤ (iota e' : ℝ) := by exact_mod_cast h2
      exact one_div_le_one_div_of_le (by norm_num) this
    have := Finset.sum_le_card_nsmul (Win P H X0m y) (fun m => 1 / Vl P m) (1 / 2) hb
    rw [nsmul_eq_mul] at this
    nlinarith
  · have h1 := hy.eta_le_card hpos
    have hXy : X0m / (y - 1.02 * H y) ≤ 1.01 * X0 / y := by
      have := hy.H_small hyX
      rw [div_le_div_iff₀ hpos (by linarith)]
      nlinarith
    have h0 : 0 ≤ X0m / (y - 1.02 * H y) := div_nonneg hXmp.le hpos.le
    calc etaX0 P H X0m y ≤ (Win P H X0m y).card * (X0m / (y - 1.02 * H y)) := h1
      _ ≤ 1 * (X0m / (y - 1.02 * H y)) := mul_le_mul_of_nonneg_right hcard' h0
      _ ≤ 1.01 * X0 / y := by rw [one_mul]; exact hXy

/-! ## The second bullet -/

omit hy in
lemma sqrt_sqrt_eq_rpow {y : ℝ} (hy0 : 0 ≤ y) : r8 y ^ 2 = y ^ (1 / 4 : ℝ) := by
  unfold r8
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hy0]
  norm_num

/-- For `y > X₀²/2`: `η_{X₀}(y) ≤ (4 + 8.21 y^{1/4}) · 1.01 X₀/y`. -/
theorem etaX0_le_high {y : ℝ} (hy2 : X0 ^ 2 / 2 < y) (hyY : y ≤ Y) :
    etaX0 P H X0m y ≤ (4 + 8.21 * r8 y ^ 2) * (1.01 * X0 / y) := by
  have hX0p := hy.hX0pos
  have hX1 : 1 ≤ X0 := le_trans (by norm_num) hy.X0_big
  have hX2 : 2 ≤ X0 := le_trans (by norm_num) hy.X0_big
  have hXy : X0 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have hXm := hy.Xm_le
  have hXmp := hy.Xm_pos
  have hy1 : X0m / 2 ≤ y := by linarith
  have hr1 : 1 ≤ r8 y := one_le_r8 (by linarith)
  have hrr : r8 y ≤ r8 y ^ 2 := by nlinarith
  -- the count
  have hc := hy.count y hy2 hyY
  have hA : 4.21 * H y / X0 ≤ 4.21 * r8 y ^ 2 := by
    have := hy.H_le_r8 hy1
    rw [div_le_iff₀ hX0p]
    have h0 := hy.hH0 y
    nlinarith
  have hB : H (y / X0) ≤ r8 y ^ 2 := by
    have hq : 0 < y / X0 := by positivity
    have hq1 : y / X0 ≤ y := div_le_self hy0.le hX1
    have := le_r8_of_pow8 (hy.hH0 _) ((hy.hHg (y / X0) hq).trans (max_le hq1 (by linarith)))
    exact this.trans hrr
  have hC : (y / X0) ^ (θo / 2) ≤ r8 y ^ 2 := by
    have hq1 : 1 ≤ y / X0 := by
      rw [le_div_iff₀ hX0p]; linarith
    have hq2 : y / X0 ≤ y := div_le_self hy0.le hX1
    calc (y / X0) ^ (θo / 2) ≤ (y / X0) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [hy.hθ1])
      _ ≤ y ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by linarith) hq2 (by norm_num)
      _ = r8 y ^ 2 := (sqrt_sqrt_eq_rpow hy0.le).symm
  have hcard : ((Win P H X0m y).card : ℝ) ≤ 4 + 8.21 * r8 y ^ 2 := by linarith
  have hpos : 0 < y - 1.02 * H y := by have := hy.H_small hXy; linarith
  have h1 := hy.eta_le_card hpos
  have hXy' : X0m / (y - 1.02 * H y) ≤ 1.01 * X0 / y := by
    have := hy.H_small hXy
    rw [div_le_div_iff₀ hpos hy0]
    nlinarith
  have h0 : 0 ≤ X0m / (y - 1.02 * H y) := div_nonneg hXmp.le hpos.le
  calc etaX0 P H X0m y ≤ (Win P H X0m y).card * (X0m / (y - 1.02 * H y)) := h1
    _ ≤ (4 + 8.21 * r8 y ^ 2) * (X0m / (y - 1.02 * H y)) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ ≤ (4 + 8.21 * r8 y ^ 2) * (1.01 * X0 / y) :=
        mul_le_mul_of_nonneg_left hXy' (by positivity)

end Hyp

/-! ## The block bounds and their sum -/

/-- The block bound `s_v` of step (iii): `0` below `X₀`, `1/2` on `[X₀, 2X₀)`, `1.01 X₀/v`
above, plus `12.34 X₀ (2v)^{1/4}/v` for `v > X₀²/4` (the second bullet). -/
noncomputable def sX0 (X0 v : ℝ) : ℝ :=
  (if v < X0 then 0 else if v < 2 * X0 then 1 / 2 else 1.01 * X0 / v) +
    (if X0 ^ 2 / 4 < v then 12.34 * X0 * r8 (2 * v) ^ 2 / v else 0)

lemma sX0_nonneg {X0 : ℝ} (hX : 0 < X0) (v : ℝ) : 0 ≤ sX0 X0 v := by
  unfold sX0
  have h1 : 0 ≤ (if v < X0 then 0 else if v < 2 * X0 then (1 : ℝ) / 2 else 1.01 * X0 / v) := by
    split_ifs with h h'
    · exact le_rfl
    · norm_num
    · push_neg at h; exact div_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ (if X0 ^ 2 / 4 < v then 12.34 * X0 * r8 (2 * v) ^ 2 / v else 0) := by
    split_ifs with h
    · have : 0 < v := lt_of_le_of_lt (by positivity) h
      positivity
    · exact le_rfl
  linarith

namespace Hyp

variable (hy : Hyp P H X0m X0 Z η1 η2 ε1 θo Y)
include hy

/-- The first part of `EtaX0Sum`: `η_{X₀} ≤ s_v` on `[v, 2v)`. -/
theorem eta_le_sX0 {Sc : Finset ℝ} (hSc : Dyadic X0 Sc) {v : ℝ} (hv : v ∈ Sc) {y : ℝ}
    (hvy : v ≤ y) (hy2v : y < 2 * v) (hyY : y ≤ Y) : etaX0 P H X0m y ≤ sX0 X0 v := by
  have hX0p := hy.hX0pos
  have hv0 : 0 < v := by
    obtain ⟨k, rfl⟩ := hSc v hv; positivity
  have hs0 := sX0_nonneg hX0p v
  rcases lt_or_ge v X0 with hlt | hge
  · have h2 := dyadic_lt hX0p hSc hv hlt
    rw [hy.etaX0_eq_zero_low (by linarith) (by linarith)]; exact hs0
  · have hyX : X0 ≤ y := hge.trans hvy
    unfold sX0
    rw [if_neg (not_lt.mpr hge)]
    have h2part : 0 ≤ (if X0 ^ 2 / 4 < v then 12.34 * X0 * r8 (2 * v) ^ 2 / v else 0) := by
      split_ifs with h
      · have := r8_nonneg (2 * v); exact div_nonneg (by positivity) hv0.le
      · exact le_rfl
    rcases le_or_gt y (X0 ^ 2 / 2) with hmid | hhigh
    · obtain ⟨hm1, hm2⟩ := hy.etaX0_le_mid hyX hmid
      have h1part : etaX0 P H X0m y ≤ (if v < 2 * X0 then (1 : ℝ) / 2 else 1.01 * X0 / v) := by
        split_ifs with h
        · exact hm1
        · exact hm2.trans (div_le_div_of_nonneg_left (by positivity) hv0 hvy)
      linarith
    · have hv4 : X0 ^ 2 / 4 < v := by linarith
      rw [if_pos hv4]
      have hb := hy.etaX0_le_high hhigh hyY
      have h1part : 0 ≤ (if v < 2 * X0 then (1 : ℝ) / 2 else 1.01 * X0 / v) := by
        split_ifs
        · norm_num
        · positivity
      have hr : r8 y ^ 2 ≤ r8 (2 * v) ^ 2 :=
        pow_le_pow_left₀ (r8_nonneg _) (r8_mono hy2v.le) 2
      have hr1 : 1 ≤ r8 (2 * v) ^ 2 := by
        have : 1 ≤ r8 (2 * v) := one_le_r8 (by nlinarith [hy.X0_big])
        nlinarith
      have hyv : 1.01 * X0 / y ≤ 1.01 * X0 / v := div_le_div_of_nonneg_left (by positivity) hv0 hvy
      have : (4 + 8.21 * r8 y ^ 2) * (1.01 * X0 / y) ≤ 12.34 * X0 * r8 (2 * v) ^ 2 / v := by
        have h3 : (4 + 8.21 * r8 y ^ 2) * (1.01 * X0 / y) ≤
            (12.21 * r8 (2 * v) ^ 2) * (1.01 * X0 / v) :=
          mul_le_mul (by linarith) hyv (div_nonneg (by positivity) (by linarith))
            (by positivity)
        have e : (12.21 * r8 (2 * v) ^ 2) * (1.01 * X0 / v) =
            12.3321 * X0 * r8 (2 * v) ^ 2 / v := by ring
        rw [e] at h3
        have : 12.3321 * X0 * r8 (2 * v) ^ 2 / v ≤ 12.34 * X0 * r8 (2 * v) ^ 2 / v :=
          div_le_div_of_nonneg_right (by nlinarith [r8_nonneg (2 * v)]) hv0.le
        linarith
      linarith

end Hyp

/-! ### The sums -/

lemma sep_mono {S T : Finset ℝ} (hST : T ⊆ S) (hS : Sep2 S) : Sep2 T :=
  fun v hv w hw h => hS v (hST hv) w (hST hw) h

/-- `∑_{v ≥ 2X₀} X₀/v ≤ 1` over a separated family. -/
lemma sum_g1 {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Sep2 S) (hSV : ∀ v ∈ S, 2 * X0 ≤ v) :
    ∑ v ∈ S, X0 / v ≤ 1 := by
  have := sum_sep_le (g := fun v => X0 / v) (V0 := 2 * X0) (r := 1 / 2) (by positivity)
    (by norm_num) (by norm_num) (fun v hv => div_nonneg hX.le (by linarith))
    (fun v w hv hvw => div_le_div_of_nonneg_left hX.le (by linarith) hvw)
    (fun v hv => by
      have : 0 < v := by linarith
      rw [div_le_iff₀ (by positivity)]; field_simp; linarith) S hS hSV
  refine this.trans (le_of_eq ?_)
  field_simp; norm_num

/-- `∑_{v ≥ 2X₀} √X₀/√v ≤ 2.42` over a separated family. -/
lemma sum_g2 {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Sep2 S) (hSV : ∀ v ∈ S, 2 * X0 ≤ v) :
    ∑ v ∈ S, √X0 / √v ≤ 2.42 := by
  have hs2 : (1.41421 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2p : 0 < √2 := by positivity
  have hc : (1 : ℝ) ≤ 0.70711 * √2 := by nlinarith
  have h1 := sum_sep_le (g := fun v => √X0 / √v) (V0 := 2 * X0) (r := 0.70711) (by positivity)
    (by norm_num) (by norm_num) (fun v hv => by positivity)
    (fun v w hv hvw => by
      have : 0 < √v := Real.sqrt_pos.mpr (by linarith)
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) this (Real.sqrt_le_sqrt hvw))
    (fun v hv => by
      have hv0 : 0 < v := by linarith
      have hsv : 0 < √v := Real.sqrt_pos.mpr hv0
      show √X0 / √(2 * v) ≤ 0.70711 * (√X0 / √v)
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) v, div_le_iff₀ (by positivity)]
      have e : 0.70711 * (√X0 / √v) * (√2 * √v) = (0.70711 * √2) * √X0 := by
        field_simp
      rw [e]
      nlinarith [Real.sqrt_nonneg X0]) S hS hSV
  simp only at h1
  refine h1.trans ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) X0]
  have hsX : 0 < √X0 := Real.sqrt_pos.mpr hX
  have e : √X0 / (√2 * √X0) = 1 / √2 := by field_simp
  rw [e, div_le_iff₀ (by norm_num), div_le_iff₀ hs2p]
  nlinarith

lemma r8_two_le : r8 2 ≤ 1.0906 := by
  apply (r8_mono (show (2 : ℝ) ≤ 1.0906 ^ 8 by norm_num)).trans
  rw [r8_of_pow8 (by norm_num)]

/-- `∑_{v > X₀²/4} X₀ (2v)^{3/8}/v ≤ 3.2/X₀^{1/4}` over a separated family. -/
lemma sum_g3 {X0 : ℝ} (hX : 0 < X0) {S : Finset ℝ} (hS : Sep2 S)
    (hSV : ∀ v ∈ S, X0 ^ 2 / 4 ≤ v) :
    ∑ v ∈ S, X0 * r8 (2 * v) ^ 3 / v ≤ 4 / r8 X0 ^ 2 / 0.35 := by
  have hV0 : 0 < X0 ^ 2 / 4 := by positivity
  have hanti : ∀ v w, X0 ^ 2 / 4 ≤ v → v ≤ w →
      X0 * r8 (2 * w) ^ 3 / w ≤ X0 * r8 (2 * v) ^ 3 / v := by
    intro v w hv hvw
    have hv0 : 0 < v := by linarith
    have hw0 : 0 < w := by linarith
    set a := r8 (2 * v)
    set b := r8 (2 * w)
    have ha : 0 < a := r8_pos (by linarith)
    have hab : a ≤ b := r8_mono (by linarith)
    have ha8 : a ^ 8 = 2 * v := r8_pow8 (by linarith)
    have hb8 : b ^ 8 = 2 * w := r8_pow8 (by linarith)
    rw [div_le_div_iff₀ hw0 hv0]
    have h5 : a ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ ha.le hab 5
    have hv' : v = a ^ 8 / 2 := by linarith
    have hw' : w = b ^ 8 / 2 := by linarith
    rw [hv', hw']
    have hb0 : 0 ≤ b := ha.le.trans hab
    have : b ^ 3 * a ^ 8 ≤ a ^ 3 * b ^ 8 := by
      have e1 : b ^ 3 * a ^ 8 = a ^ 3 * b ^ 3 * a ^ 5 := by ring
      have e2 : a ^ 3 * b ^ 8 = a ^ 3 * b ^ 3 * b ^ 5 := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith
  have h2 : ∀ v, X0 ^ 2 / 4 ≤ v →
      X0 * r8 (2 * (2 * v)) ^ 3 / (2 * v) ≤ 0.65 * (X0 * r8 (2 * v) ^ 3 / v) := by
    intro v hv
    have hv0 : 0 < v := by linarith
    have e : r8 (2 * (2 * v)) = r8 2 * r8 (2 * v) := r8_mul (by norm_num) (by linarith)
    rw [e]
    have hc : r8 2 ^ 3 ≤ 1.3 := by
      have := r8_two_le
      have h0 := r8_nonneg 2
      nlinarith [pow_le_pow_left₀ h0 this 3]
    have hpos : 0 ≤ X0 * r8 (2 * v) ^ 3 := by have := r8_nonneg (2 * v); positivity
    rw [mul_pow, div_le_iff₀ (by positivity)]
    have : X0 * (r8 2 ^ 3 * r8 (2 * v) ^ 3) ≤ X0 * (1.3 * r8 (2 * v) ^ 3) := by
      have := r8_nonneg (2 * v)
      apply mul_le_mul_of_nonneg_left _ hX.le
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    have e2 : 0.65 * (X0 * r8 (2 * v) ^ 3 / v) * (2 * v) = X0 * (1.3 * r8 (2 * v) ^ 3) := by
      field_simp; ring
    linarith
  have hsum := sum_sep_le (g := fun v => X0 * r8 (2 * v) ^ 3 / v) (V0 := X0 ^ 2 / 4)
    (r := 0.65) hV0 (by norm_num) (by norm_num)
    (fun v hv => div_nonneg (mul_nonneg hX.le (pow_nonneg (r8_nonneg _) 3)) (by linarith))
    hanti h2 S hS hSV
  refine hsum.trans ?_
  -- `g(X₀²/4) ≤ 4/t²`
  have ht := r8_pos hX
  have hXX : r8 (X0 ^ 2) = r8 X0 ^ 2 := by rw [pow_two, r8_mul hX.le hX.le, pow_two]
  have hle : r8 (2 * (X0 ^ 2 / 4)) ≤ r8 X0 ^ 2 := by
    rw [← hXX]; exact r8_mono (by nlinarith)
  have hX8 : X0 = r8 X0 ^ 8 := (r8_pow8 hX.le).symm
  have hg : X0 * r8 (2 * (X0 ^ 2 / 4)) ^ 3 / (X0 ^ 2 / 4) ≤ 4 / r8 X0 ^ 2 := by
    have h0 := r8_nonneg (2 * (X0 ^ 2 / 4))
    have h3 : r8 (2 * (X0 ^ 2 / 4)) ^ 3 ≤ (r8 X0 ^ 2) ^ 3 := pow_le_pow_left₀ h0 hle 3
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : X0 * r8 (2 * (X0 ^ 2 / 4)) ^ 3 * r8 X0 ^ 2 ≤ X0 * (r8 X0 ^ 2) ^ 3 * r8 X0 ^ 2 := by
      gcongr
    calc X0 * r8 (2 * (X0 ^ 2 / 4)) ^ 3 * r8 X0 ^ 2 ≤ X0 * (r8 X0 ^ 2) ^ 3 * r8 X0 ^ 2 := this
      _ = X0 * r8 X0 ^ 8 := by ring
      _ = X0 * X0 := by rw [r8_pow8 hX.le]
      _ = 4 * (X0 ^ 2 / 4) := by ring
  have : (1 : ℝ) - 0.65 = 0.35 := by norm_num
  rw [this]
  exact div_le_div_of_nonneg_right hg (by norm_num)

namespace Hyp

variable (hy : Hyp P H X0m X0 Z η1 η2 ε1 θo Y)
include hy

/-- The weighted sum of step (iii): `∑_v log(2v) s⁰_v ≤ 1.52 log(2X₀)` on dyadic scales. -/
theorem sum_sX0_le {Sc : Finset ℝ} (hSc : Dyadic X0 Sc) :
    ∑ v ∈ Sc, Real.log (2 * v) * sX0 X0 v ≤ 1.52 * Real.log (2 * X0) := by
  classical
  have hX0p := hy.hX0pos
  have hX1 : 1 ≤ X0 := le_trans (by norm_num) hy.X0_big
  have hSep := dyadic_sep hX0p hSc
  set L := Real.log (2 * X0)
  have hL : 100000000 ≤ L := by
    have : Real.log X0 ≤ L := Real.log_le_log hX0p (by linarith)
    linarith [hy.hX0]
  have hv0 : ∀ v ∈ Sc, 0 < v := fun v hv => by obtain ⟨k, rfl⟩ := hSc v hv; positivity
  -- split `s = s₁ + s₂`
  set s1 : ℝ → ℝ := fun v =>
    if v < X0 then 0 else if v < 2 * X0 then 1 / 2 else 1.01 * X0 / v
  set s2 : ℝ → ℝ := fun v => if X0 ^ 2 / 4 < v then 12.34 * X0 * r8 (2 * v) ^ 2 / v else 0
  have hs : ∀ v, sX0 X0 v = s1 v + s2 v := fun v => rfl
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib]
  -- the first part
  have hA : ∑ v ∈ Sc, Real.log (2 * v) * s1 v ≤ L / 2 + 1.01 * (L + 4.84) := by
    rw [← Finset.sum_filter_add_sum_filter_not Sc (fun v => v < 2 * X0)]
    have hlow : ∑ v ∈ Sc.filter (fun v => v < 2 * X0), Real.log (2 * v) * s1 v ≤ L / 2 := by
      have hb : ∀ v ∈ Sc.filter (fun v => v < 2 * X0), Real.log (2 * v) * s1 v ≤
          if v = X0 then L / 2 else 0 := by
        intro v hv
        obtain ⟨hvS, hv2⟩ := Finset.mem_filter.mp hv
        simp only [s1]
        rcases lt_or_ge v X0 with hlt | hge
        · rw [if_pos hlt, mul_zero]; split_ifs <;> linarith
        · have he := dyadic_eq hX0p hSc hvS hge hv2
          subst he
          rw [if_neg (lt_irrefl _), if_pos hv2, if_pos rfl]
          linarith
      refine (Finset.sum_le_sum hb).trans ?_
      rw [Finset.sum_ite_eq']
      split_ifs <;> linarith
    have hhigh : ∑ v ∈ Sc.filter (fun v => ¬ v < 2 * X0), Real.log (2 * v) * s1 v ≤
        1.01 * (L + 4.84) := by
      set T := Sc.filter (fun v => ¬ v < 2 * X0)
      have hT : Sep2 T := sep_mono (Finset.filter_subset _ _) hSep
      have hTV : ∀ v ∈ T, 2 * X0 ≤ v := fun v hv => not_lt.mp (Finset.mem_filter.mp hv).2
      have hb : ∀ v ∈ T, Real.log (2 * v) * s1 v ≤
          1.01 * (L * (X0 / v) + 2 * (√X0 / √v)) := by
        intro v hv
        have h2 := hTV v hv
        have hv0 : 0 < v := by linarith
        simp only [s1]
        rw [if_neg (by linarith), if_neg (by linarith)]
        have hlog : Real.log (2 * v) = L + Real.log (v / X0) := by
          rw [show 2 * v = (2 * X0) * (v / X0) by field_simp, Real.log_mul (by positivity)
            (by positivity)]
        have hlv := log_le_two_sqrt (show 0 < v / X0 by positivity)
        have hsq : √(v / X0) * (X0 / v) = √X0 / √v := by
          rw [Real.sqrt_div' _ hX0p.le]
          have hs1 : 0 < √X0 := Real.sqrt_pos.mpr hX0p
          have hs2 : 0 < √v := Real.sqrt_pos.mpr hv0
          rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
          calc √v * X0 * √v = (√v * √v) * X0 := by ring
            _ = v * X0 := by rw [Real.mul_self_sqrt hv0.le]
            _ = √X0 * (√X0 * v) := by rw [← mul_assoc, Real.mul_self_sqrt hX0p.le]; ring
        have hpos : 0 ≤ X0 / v := by positivity
        rw [hlog]
        have : (L + Real.log (v / X0)) * (1.01 * X0 / v) =
            1.01 * (L * (X0 / v) + Real.log (v / X0) * (X0 / v)) := by ring
        rw [this]
        have h3 : Real.log (v / X0) * (X0 / v) ≤ 2 * √(v / X0) * (X0 / v) :=
          mul_le_mul_of_nonneg_right hlv hpos
        rw [mul_assoc 2, hsq] at h3
        linarith
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have h1 := sum_g1 hX0p hT hTV
      have h2 := sum_g2 hX0p hT hTV
      have hL0 : 0 ≤ L := by linarith
      nlinarith
    linarith
  -- the second part
  have hB : ∑ v ∈ Sc, Real.log (2 * v) * s2 v ≤ 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not Sc (fun v => X0 ^ 2 / 4 < v)]
    have hz : ∑ v ∈ Sc.filter (fun v => ¬ X0 ^ 2 / 4 < v), Real.log (2 * v) * s2 v = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      simp only [s2]; rw [if_neg (Finset.mem_filter.mp hv).2, mul_zero]
    rw [hz, add_zero]
    set T := Sc.filter (fun v => X0 ^ 2 / 4 < v)
    have hT : Sep2 T := sep_mono (Finset.filter_subset _ _) hSep
    have hTV : ∀ v ∈ T, X0 ^ 2 / 4 ≤ v := fun v hv => (Finset.mem_filter.mp hv).2.le
    have hb : ∀ v ∈ T, Real.log (2 * v) * s2 v ≤ 98.72 * (X0 * r8 (2 * v) ^ 3 / v) := by
      intro v hv
      have h4 := (Finset.mem_filter.mp hv).2
      have hv0 : 0 < v := lt_of_le_of_lt (by positivity) h4
      simp only [s2]; rw [if_pos h4]
      have hl := log_le_r8 (show 0 < 2 * v by linarith)
      have hpos : 0 ≤ 12.34 * X0 * r8 (2 * v) ^ 2 / v := by
        have := r8_nonneg (2 * v); positivity
      calc Real.log (2 * v) * (12.34 * X0 * r8 (2 * v) ^ 2 / v)
          ≤ 8 * r8 (2 * v) * (12.34 * X0 * r8 (2 * v) ^ 2 / v) :=
            mul_le_mul_of_nonneg_right hl hpos
        _ = 98.72 * (X0 * r8 (2 * v) ^ 3 / v) := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have h3 := sum_g3 hX0p hT hTV
    have ht := hy.t_big
    have ht2 : (10 : ℝ) ^ 24 ≤ r8 X0 ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) ht 2; norm_num at this ⊢; linarith
    have hq : 4 / r8 X0 ^ 2 / 0.35 ≤ 1 / 98.72 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h0 : 0 ≤ ∑ v ∈ T, X0 * r8 (2 * v) ^ 3 / v :=
      Finset.sum_nonneg fun v hv => by
        have := r8_nonneg (2 * v)
        have : 0 < v := lt_of_lt_of_le (by positivity) (hTV v hv)
        positivity
    nlinarith
  have : L / 2 + 1.01 * (L + 4.84) + 1 ≤ 1.52 * L := by linarith
  linarith

/-- **Step (iii) of Proposition 5.18**: `EtaX0Sum` for every family of dyadic scales. -/
theorem etaX0Sum_of {Sc : Finset ℝ} (hSc : Dyadic X0 Sc) (hSY : ∀ v ∈ Sc, 2 * v ≤ Y) :
    EtaX0Sum P H X0m X0 Sc (sX0 X0) :=
  ⟨fun v hv => ⟨sX0_nonneg hy.hX0pos v, fun y h1 h2 =>
    hy.eta_le_sX0 hSc hv h1 h2 (by linarith [hSY v hv])⟩, hy.sum_sX0_le hSc⟩

/-- **Step (iii) of Proposition 5.18, localized**: the bounds `η_{X₀} ≤ s⁰_v` are needed only at
the positions `y ≤ x` of a start `x ≤ Y` (`EtaX0SumLoc`), so every dyadic family works. -/
theorem etaX0SumLoc_of {Sc : Finset ℝ} (hSc : Dyadic X0 Sc) {x : ℝ} (hxY : x ≤ Y) :
    EtaX0SumLoc P H X0m X0 Sc (sX0 X0) x :=
  ⟨fun v hv => ⟨sX0_nonneg hy.hX0pos v, fun y h1 h2 h3 =>
    hy.eta_le_sX0 hSc hv h1 h2 (h3.trans hxY)⟩, hy.sum_sX0_le hSc⟩

end Hyp

end KR.X0S

end
