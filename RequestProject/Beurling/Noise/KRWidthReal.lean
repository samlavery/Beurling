module

public import RequestProject.Beurling.Queue6.TNPHyp
public import RequestProject.Beurling.Noise.TauNearProofNum

/-!
# `PaperWidth` for the realised width `H_c(x) = H(max(x, X₀))`, and the standard-width input of
the Lemma 5.20 numerics

`Queue6.tnpHyp_R` needs `KR.PaperWidth (Hc X₀) (Xm X₀) ε θ'` for the realised width
`Hc X₀ x = capH X₀ (max x X₀)` (the jitter width `H = max(H_std, M̄₁²)`, frozen at `H(X₀)` below
`X₀`).

* `paperWidth_Hc` : `PaperWidth (Hc X₀) (Xm X₀) ε (ε/10)` for `log X₀ ≥ 10⁸` and
  `0 ≤ ε ≤ 4·10⁻⁶`, from two named inputs about `H = capH X₀` on `[X₀, ∞)`:
  - `CapHSlope X₀ ε` : `H(y) ≤ (y/x)^ε H(x)` for `X₀ ≤ x ≤ y`, i.e. `d log H/d log v ≤ ε`
    integrated; this is (RH) of §5.1, which the paper derives from
    `d log H_std/d log v = 16 log log v/log v ≤ 3·10⁻⁶` and, on the raised range, from
    Theorem 6.23(c) (`d log H/d log v ≤ 4·10⁻⁶`). No slope bound for `M̄₁²` is in Lean yet.
  - `CapHDiff X₀` : `H` is differentiable at every point `> X₀` off a countable set (the
    `WidthReg` regularity; `H` is piecewise smooth, §5.1 "Regularity of `H`").
  Everything else is proved: positivity, the global `1`-Lipschitz bound and `θ`-Lipschitz bound
  with `θ = ε/10` (from the slope, Bernoulli and `H(x) ≤ x/10`), (RH) for `H_c` on all of
  `(0, ∞)` (the frozen part only lowers the ratio), and `H_c(y) ≤ y/10` for `y ≥ X₀⁻/2`
  (from `capH_le_rpow`, `H(x) ≤ x^{1/8}`).
* The Lemma 5.20 numerics (`TauNearProofNum`) assume `H(X₀⁻/2) ≤ e^{8(log log(X₀⁻/2))²}`. For
  the frozen width this **fails**: `H_c(X₀⁻/2) = H(X₀) ≥ e^{8(log log X₀)²}`, and
  `X₀⁻/2 < X₀` (`not_hHstd_Hc`). The numerics only need `Φ_a(X₀⁻/2)` small, which follows from
  the weaker `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}` (`Hc_Xm_half_le`, true for `H_c`):
  `Phi_small_r`, `energy_small_r`, `etaBlk_small_r`, `thetaStar_small_r`, `thetaE_small_r` are
  the numerics under this hypothesis (same conclusions).
-/

@[expose] public section

open Real Set CaplLink

namespace KR.WidthReal

variable {X₀ : ℕ}

/-- **(RH) for the jitter width on `[X₀, ∞)`** (§5.1 "Regularity of `H`", with Theorem 6.23(c)
on the raised range): `H(y) ≤ (y/x)^ε H(x)` for `X₀ ≤ x ≤ y`. -/
def CapHSlope (X₀ : ℕ) (ε : ℝ) : Prop :=
  ∀ x y : ℝ, (X₀ : ℝ) ≤ x → x ≤ y → capH X₀ y ≤ (y / x) ^ ε * capH X₀ x

/-- **`H` is piecewise smooth** (§5.1): differentiable at every `y > X₀` off a countable set. -/
def CapHDiff (X₀ : ℕ) : Prop :=
  ∃ S : Set ℝ, S.Countable ∧ ∀ y : ℝ, (X₀ : ℝ) < y → y ∉ S → DifferentiableAt ℝ (capH X₀) y

section

variable (hX : 10 ^ 8 ≤ Real.log X₀)
include hX

lemma X0_pos : (0 : ℝ) < X₀ := by
  by_contra h; push_neg at h
  have : (X₀ : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
  rw [this, Real.log_zero] at hX; norm_num at hX

lemma X0_ge : (65536 : ℝ) ≤ X₀ := by
  have h := Real.add_one_le_exp (Real.log X₀)
  rw [Real.exp_log (X0_pos hX)] at h
  linarith

omit hX in
/-- `a^{1/8} ≤ a/40` for `a ≥ 2¹⁶`. -/
lemma rpow_eighth_le {a : ℝ} (ha : 65536 ≤ a) : a ^ (1 / 8 : ℝ) ≤ a / 40 := by
  have ha0 : 0 < a := by linarith
  have h1 : a = a ^ (1 / 8 : ℝ) * a ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add ha0]; norm_num
  have h2 : (65536 : ℝ) ^ (7 / 8 : ℝ) ≤ a ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) ha (by norm_num)
  have h3 : (65536 : ℝ) ^ (7 / 8 : ℝ) = 16384 := by
    rw [show (65536 : ℝ) = 2 ^ (16 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h4 : 0 < a ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ha0 _
  rw [h3] at h2
  nlinarith

lemma capH_le_tenth {a : ℝ} (ha : (X₀ : ℝ) ≤ a) : capH X₀ a ≤ a / 40 :=
  (InitialRange.capH_le_rpow (Nat.cast_nonneg _) hX ha).trans
    (rpow_eighth_le ((X0_ge hX).trans ha))

lemma capH_one_le {a : ℝ} (ha : (X₀ : ℝ) ≤ a) : 1 ≤ capH X₀ a :=
  BModel.capH_ge_one (Nat.cast_nonneg _) hX ha

lemma Xm_ge : (X₀ : ℝ) / 2 ≤ BModel.Xm X₀ := by
  unfold BModel.Xm
  have := capH_le_tenth hX (le_refl (X₀ : ℝ))
  linarith

lemma Xm_lt : BModel.Xm X₀ / 2 < X₀ := by
  have := capH_one_le hX (le_refl (X₀ : ℝ))
  unfold BModel.Xm
  have := X0_pos hX
  linarith

lemma Hc_pos (y : ℝ) : 0 < Queue6.Hc X₀ y := by
  unfold Queue6.Hc
  exact lt_of_lt_of_le one_pos (capH_one_le hX (le_max_right _ _))

lemma Hc_mono : Monotone (Queue6.Hc X₀) := by
  intro x y hxy
  unfold Queue6.Hc
  exact Construction.capH_monotoneOn (Nat.cast_nonneg _) hX (mem_Ici.mpr (le_max_right _ _))
    (mem_Ici.mpr (le_max_right _ _)) (max_le_max hxy le_rfl)

/-- The increment bound: `0 ≤ H_c(y) - H_c(x) ≤ (ε/10)(y - x)` for `x ≤ y`. -/
lemma Hc_incr {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hS : CapHSlope X₀ ε) {x y : ℝ}
    (hxy : x ≤ y) : Queue6.Hc X₀ y - Queue6.Hc X₀ x ≤ ε / 10 * (y - x) := by
  unfold Queue6.Hc
  set a := max x (X₀ : ℝ)
  set b := max y (X₀ : ℝ)
  have ha : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hab : a ≤ b := max_le_max hxy le_rfl
  have ha0 : 0 < a := lt_of_lt_of_le (X0_pos hX) ha
  have hba : b - a ≤ y - x := by
    simp only [a, b]
    rcases le_total y X₀ with h1 | h1
    · rw [max_eq_right h1, max_eq_right (hxy.trans h1)]; linarith
    · rw [max_eq_left h1]
      rcases le_total x X₀ with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]
  have h1 := hS a b ha hab
  -- Bernoulli: `(b/a)^ε ≤ 1 + ε (b/a - 1)`
  have hbern : (b / a) ^ ε ≤ 1 + ε * (b / a - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := b / a - 1)
      (by have : 0 ≤ b / a := div_nonneg (by linarith) ha0.le; linarith) hε0 hε1
    simpa using this
  have hHa := capH_le_tenth hX ha
  have hHa1 := capH_one_le hX ha
  have hq : b / a - 1 = (b - a) / a := by field_simp
  calc capH X₀ b - capH X₀ a ≤ (b / a) ^ ε * capH X₀ a - capH X₀ a := by linarith
    _ ≤ (1 + ε * (b / a - 1)) * capH X₀ a - capH X₀ a := by
        have := mul_le_mul_of_nonneg_right hbern (by linarith : 0 ≤ capH X₀ a)
        linarith
    _ = ε * (b - a) * (capH X₀ a / a) := by rw [hq]; field_simp; ring
    _ ≤ ε * (b - a) * (1 / 40) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hε0 (by linarith))
        rw [div_le_iff₀ ha0]; linarith
    _ ≤ ε / 10 * (y - x) := by nlinarith

lemma Hc_abs {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hS : CapHSlope X₀ ε) (x y : ℝ) :
    |Queue6.Hc X₀ y - Queue6.Hc X₀ x| ≤ ε / 10 * |y - x| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Hc_mono hX h)), abs_of_nonneg (by linarith)]
    exact Hc_incr hX hε0 hε1 hS h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Hc_mono hX h)), abs_sub_comm,
      abs_of_nonneg (by linarith)]
    exact Hc_incr hX hε0 hε1 hS h

omit hX in
/-- `H_c` is differentiable off a countable set. -/
lemma Hc_diff (hD : CapHDiff X₀) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ y ∉ S, DifferentiableAt ℝ (Queue6.Hc X₀) y := by
  obtain ⟨S, hS, hd⟩ := hD
  refine ⟨insert (X₀ : ℝ) S, hS.insert _, fun y hy => ?_⟩
  rw [Set.mem_insert_iff, not_or] at hy
  rcases lt_or_gt_of_ne hy.1 with h | h
  · -- locally constant
    have : Queue6.Hc X₀ =ᶠ[nhds y] fun _ => capH X₀ X₀ := by
      filter_upwards [Iio_mem_nhds h] with z hz
      unfold Queue6.Hc; rw [max_eq_right (le_of_lt hz)]
    exact (differentiableAt_const _).congr_of_eventuallyEq this
  · have : Queue6.Hc X₀ =ᶠ[nhds y] capH X₀ := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      unfold Queue6.Hc; rw [max_eq_left (le_of_lt hz)]
    exact (hd y h hy.2).congr_of_eventuallyEq this

/-- **`PaperWidth` for the realised width** `H_c = H(max(·, X₀))`, with `θ = ε/10`. -/
theorem paperWidth_Hc {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hS : CapHSlope X₀ ε)
    (hD : CapHDiff X₀) : KR.PaperWidth (Queue6.Hc X₀) (BModel.Xm X₀) ε (ε / 10) where
  reg :=
    { pos := Hc_pos hX
      lip := LipschitzWith.of_dist_le_mul fun y z => by
        rw [Real.dist_eq, Real.dist_eq]
        have := Hc_abs hX hε0 (by linarith) hS z y
        push_cast
        nlinarith [abs_nonneg (y - z)]
      diff := Hc_diff hD }
  X0m_pos := lt_of_lt_of_le (by have := X0_pos hX; linarith) (Xm_ge hX)
  eps_nonneg := hε0
  eps_le := hε
  RH := by
    intro v w hv hw
    have hXm0 : 0 < BModel.Xm X₀ := lt_of_lt_of_le (by have := X0_pos hX; linarith) (Xm_ge hX)
    have hv0 : 0 < v := by linarith
    unfold Queue6.Hc
    set a := max v (X₀ : ℝ)
    set b := max (v * w) (X₀ : ℝ)
    have ha : (X₀ : ℝ) ≤ a := le_max_right _ _
    have ha0 : 0 < a := lt_of_lt_of_le (X0_pos hX) ha
    have hvw : v ≤ v * w := le_mul_of_one_le_right hv0.le hw
    have hab : a ≤ b := max_le_max hvw le_rfl
    have hba : b / a ≤ w := by
      rw [div_le_iff₀ ha0]
      simp only [a, b]
      rcases le_total (v * w) X₀ with h1 | h1
      · rw [max_eq_right h1, max_eq_right (hvw.trans h1)]; nlinarith
      · rw [max_eq_left h1]
        exact mul_comm v w ▸ mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have h1 := hS a b ha hab
    have hHa := (capH_one_le hX ha)
    have h2 : (b / a) ^ ε ≤ w ^ ε :=
      Real.rpow_le_rpow (div_nonneg (by linarith) ha0.le) hba hε0
    calc capH X₀ b ≤ (b / a) ^ ε * capH X₀ a := h1
      _ ≤ w ^ ε * capH X₀ a := mul_le_mul_of_nonneg_right h2 (by linarith)
  theta_nonneg := by positivity
  theta_le := by linarith
  lip := fun y z _ _ => by
    exact Hc_abs hX hε0 (by linarith) hS z y
  small := by
    intro y hy
    have hXm := Xm_ge hX
    unfold Queue6.Hc
    rcases le_total y X₀ with h1 | h1
    · rw [max_eq_right h1]
      have := capH_le_tenth hX (le_refl (X₀ : ℝ))
      linarith
    · rw [max_eq_left h1]
      have := capH_le_tenth hX h1
      have := X0_pos hX
      linarith

/-! ## The standard-width input of the Lemma 5.20 numerics -/

/-- `H_c(X₀⁻/2) = H(X₀)`. -/
lemma Hc_Xm_half : Queue6.Hc X₀ (BModel.Xm X₀ / 2) = capH X₀ X₀ := by
  unfold Queue6.Hc; rw [max_eq_right (Xm_lt hX).le]

/-- The form of the paper's standard-width hypothesis used in `TauNearProofNum` fails for the
frozen width: `H_c(X₀⁻/2) = H(X₀) > e^{8(log log(X₀⁻/2))²}`. -/
theorem not_hHstd_Hc :
    ¬ Queue6.Hc X₀ (BModel.Xm X₀ / 2) ≤
      Real.exp (8 * Real.log (Real.log (BModel.Xm X₀ / 2)) ^ 2) := by
  rw [Hc_Xm_half hX]
  intro h
  have hstd : Real.exp (8 * Real.log (Real.log X₀) ^ 2) ≤ capH X₀ X₀ := le_max_left _ _
  have hXm := Xm_ge hX
  have hX0 := X0_ge hX
  have hlt := Xm_lt hX
  have hp : 0 < BModel.Xm X₀ / 2 := by linarith
  have l1 : Real.log (BModel.Xm X₀ / 2) < Real.log X₀ := Real.log_lt_log hp hlt
  have l0 : 1 < Real.log (BModel.Xm X₀ / 2) := by
    have : Real.log (X₀ / 4) ≤ Real.log (BModel.Xm X₀ / 2) := Real.log_le_log (by linarith)
      (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    have h4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith
  have l2 : Real.log (Real.log (BModel.Xm X₀ / 2)) < Real.log (Real.log X₀) :=
    Real.log_lt_log (by linarith) l1
  have l3 : 0 < Real.log (Real.log (BModel.Xm X₀ / 2)) := Real.log_pos l0
  have : Real.exp (8 * Real.log (Real.log (BModel.Xm X₀ / 2)) ^ 2) <
      Real.exp (8 * Real.log (Real.log X₀) ^ 2) := by
    apply Real.exp_lt_exp.mpr; nlinarith
  linarith

/-- The weaker standard-width input that holds for `H_c`: `H_c(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}`. -/
theorem Hc_Xm_half_le :
    Queue6.Hc X₀ (BModel.Xm X₀ / 2) ≤ 2 * (BModel.Xm X₀ / 2) ^ (1 / 8 : ℝ) := by
  rw [Hc_Xm_half hX]
  have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg _) hX (le_refl (X₀ : ℝ))
  have hXm := Xm_ge hX
  have hX0 := X0_pos hX
  have hle : (X₀ : ℝ) ≤ 4 * (BModel.Xm X₀ / 2) := by linarith
  have h2 : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (4 * (BModel.Xm X₀ / 2)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow hX0.le hle (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
  have h4 : (4 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ ((2 : ℝ) * (1 / 8)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h5 : 0 ≤ (BModel.Xm X₀ / 2) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith

end

/-! ## The Lemma 5.20 numerics under the weaker standard-width input -/

section num

open BeurlingSystem Finset

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `2·10¹⁴ ℓ³ ≤ e^{7ℓ/8}` for `ℓ ≥ 10⁷`. -/
lemma num_core_r {ℓ : ℝ} (hℓ : 10000000 ≤ ℓ) :
    200000000000000 * ℓ ^ 3 ≤ Real.exp (7 * ℓ / 8) := by
  set x := 7 * ℓ / 8 with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have h7 := Real.pow_div_factorial_le_exp x hx0 7
  norm_num [Nat.factorial] at h7
  have hℓx : ℓ = 8 * x / 7 := by rw [hx]; ring
  have hxbig : 8750000 ≤ x := by rw [hx]; linarith
  rw [hℓx]
  have hx4 : (8750000 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hxbig 4
  have hx3 : 0 ≤ x ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hx4 hx3]

/-- **`Φ_a(X₀⁻/2) ≤ 2·10⁻¹⁴`** for `a ≤ 3`, under `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`. -/
theorem Phi_small_r (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {a : ℕ} (ha : a ≤ 3) :
    TNP.Phi H a (X0m / 2) ≤ 2 / 10 ^ 14 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hl := TNP.log_Pk_ge hX h.hXm 0
  rw [TNP.Pk_zero] at hl
  set ℓ := Real.log (X0m / 2)
  have hP0 : X0m / 2 = Real.exp ℓ := (Real.exp_log (by positivity)).symm
  have hb : 1 ≤ ℓ + 2 := by linarith
  have hpow : (ℓ + 2) ^ a ≤ (ℓ + 2) ^ 3 := pow_le_pow_right₀ hb ha
  have h3 : (ℓ + 2) ^ 3 ≤ 2 * ℓ ^ 3 := by nlinarith [sq_nonneg ℓ]
  have hc := num_core_r hl
  have hr : (X0m / 2) ^ (1 / 8 : ℝ) = Real.exp (ℓ / 8) := by
    rw [hP0, ← Real.exp_mul]; ring_nf
  have hsplit : Real.exp ℓ = Real.exp (ℓ / 8) * Real.exp (7 * ℓ / 8) := by
    rw [← Real.exp_add]; ring_nf
  have hsplit' : X0m / 2 = Real.exp (ℓ / 8) * Real.exp (7 * ℓ / 8) := by
    rw [← Real.exp_add, show ℓ / 8 + 7 * ℓ / 8 = ℓ by ring, ← hP0]
  unfold TNP.Phi
  have hH0 := hP.reg.pos (X0m / 2)
  have he8 := Real.exp_pos (ℓ / 8)
  have he78 := Real.exp_pos (7 * ℓ / 8)
  rw [hr] at hH
  have hpos : 0 ≤ (ℓ + 2) ^ a := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc H (X0m / 2) * (ℓ + 2) ^ a ≤ (2 * Real.exp (ℓ / 8)) * (2 * ℓ ^ 3) := by
        gcongr; exact hpow.trans h3
    _ ≤ 2 / 10 ^ 14 * (Real.exp (ℓ / 8) * Real.exp (7 * ℓ / 8)) := by nlinarith
    _ = 2 / 10 ^ 14 * (X0m / 2) := by rw [← hsplit']

/-- `λ₀ C_N E_η ≤ ½` under the weaker standard-width input. -/
theorem energy_small_r (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) {lam0 CN : ℝ} (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2)
    (hCN0 : 0 ≤ CN) (hCN : CN ≤ 158) :
    lam0 * CN * ∑ v ∈ Sc, Real.log (2 * v) *
        TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v ≤ 1 / 2 := by
  have h1 := (TNP.etaBound_energy h hS hSc hZ hK).2.1
  have h2 := Phi_small_r h hH (a := 1) (by norm_num)
  have hlc : lam0 * CN ≤ 316 := by nlinarith
  have hE : ∑ v ∈ Sc, Real.log (2 * v) *
      TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v ≤ 1 / 1000000 := by
    linarith
  rcases le_or_gt 0 (∑ v ∈ Sc, Real.log (2 * v) *
      TNP.blk P H X0m K (fun k => 1 / (Real.log (TNP.Pk X0m k) - 0.18)) v) with h0 | h0
  · nlinarith [mul_nonneg hlam0 hCN0]
  · nlinarith [mul_nonneg hlam0 hCN0]

/-- `2.04 ∑_v s_v ≤ 0.02` under the weaker standard-width input. -/
theorem etaBlk_small_r (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 0 < v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) :
    2.04 * ∑ v ∈ Sc, TNP.blk P H X0m K (fun _ => 1) v ≤ 0.02 := by
  have h1 := (TNP.etaBlk_sum h hS hSc hZ hK).2
  have h2 := Phi_small_r h hH (a := 1) (by norm_num)
  nlinarith

/-- `2.04 λ₀ θ_* ≤ 0.02` for `θ_* = 207800 Φ₂(X₀⁻/2)`, under the weaker input. -/
theorem thetaStar_small_r (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {lam0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hlam : lam0 ≤ 2) :
    0 ≤ 207800 * TNP.Phi H 2 (X0m / 2) ∧
      2.04 * lam0 * (207800 * TNP.Phi H 2 (X0m / 2)) ≤ 0.02 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have h0 := TNP.Phi_nonneg hP 2 (le_refl _) (by
    have := TNP.Pk_ge_one hX h.hXm 0; rwa [TNP.Pk_zero] at this)
  have h2 := Phi_small_r h hH (a := 2) (by norm_num)
  refine ⟨by positivity, ?_⟩
  nlinarith

/-- `E_θ ≤ 10⁻⁷` under the weaker standard-width input. -/
theorem thetaE_small_r (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {Sc : Finset ℝ}
    (hS : TNP.Sep Sc) (hSc : ∀ v ∈ Sc, 1 ≤ v) (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) {K : ℕ}
    (hK : ∀ v ∈ Sc, √(2 * v) ≤ TNP.Pk X0m K) :
    ∑ v ∈ Sc, Real.log (2 * v) * TNP.blk P H X0m K (fun k => Real.log (TNP.Pk X0m k) + 2) v ≤
      1 / 10000000 := by
  have h1 := (TNP.thetaBlk_sum h hS hSc hZ hK).2
  have h2 := Phi_small_r h hH (a := 3) (by norm_num)
  nlinarith

end num

end KR.WidthReal

end
