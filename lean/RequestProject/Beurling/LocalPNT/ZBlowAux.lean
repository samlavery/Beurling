module

public import RequestProject.Beurling.ZBIdentity

/-!
# Lemma 4.3: the pieces of `Ê = Z_B - s/(s-1)`

Auxiliary estimates for Lemma 4.3 (`lem:ZBlow`), with `ℓ = log(1+κ)`:

* `W(s) = ((1+κ)^s - 1)/(sκ) = κ⁻¹ ∫_0^ℓ e^{su} du`, so `|W(s)| ≤ (1+κ)^σ` for `σ ≥ 0`
  (`norm_Wfac_le_rpow`), and `|1 - W(s)| ≤ κ(1+|s|)` when `κ(1+|s|) ≤ 1`
  (`norm_one_sub_Wfac_le`, from `|e^z - 1 - z| ≤ |z|²` and `κ/(1+κ) ≤ ℓ ≤ κ`);
* `|S_{≥X₀}(s)| ≤ X₀^{σ₀-σ} Z_∞(σ₀)` for `0 < σ₀ ≤ σ` (`norm_smooth_ge_le`);
* the boundary terms: each is `κ⁻¹ ∫_{log(d/(1+κ))}^{log X₀} e^{-su} du`, of modulus
  `≤ (d/(1+κ))^{-σ}`; with at most `κX₀ + 1` of them, `|boundary| ≤ 3κe^a`
  (`norm_boundary_le_three`);
* `∫_n^{n+1} x^{-s} dx = (n+1)^{1-s} - n^{1-s})/(1-s)` has modulus `≤ n^{-σ}`, and differs from
  `n^{-s}` by at most `|s| n^{-σ-1}/2` (`norm_cpow_sub_intCpow_le`).
-/

@[expose] public section

open Complex Real Finset BaseFactor

namespace LocalPNT

/-! ### The factor `W` -/

lemma one_add_cpow_eq {κ : ℝ} (hκ : 0 < κ) (s : ℂ) :
    (((1 + κ : ℝ)) : ℂ) ^ s = Complex.exp ((Real.log (1 + κ) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (1 + κ : ℝ) ≠ 0)),
    Complex.ofReal_log (by linarith)]

lemma log_one_add_le {κ : ℝ} (hκ : 0 < κ) : Real.log (1 + κ) ≤ κ := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + κ by linarith); linarith

lemma log_one_add_ge {κ : ℝ} (hκ : 0 < κ) : κ - κ ^ 2 ≤ Real.log (1 + κ) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + κ by linarith)
  have e : 1 - (1 + κ)⁻¹ = κ / (1 + κ) := by field_simp; ring
  rw [e] at h
  have : κ - κ ^ 2 ≤ κ / (1 + κ) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  linarith

lemma Wfac_eq_integral {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hs : s ≠ 0) :
    Wfac κ s = (κ : ℂ)⁻¹ * ∫ u in (0 : ℝ)..Real.log (1 + κ), Complex.exp (s * u) := by
  rw [integral_exp_mul_complex hs, Wfac, one_add_cpow_eq hκ]
  push_cast
  rw [mul_zero, Complex.exp_zero, mul_comm (s : ℂ)]
  field_simp

/-- `|W(s)| ≤ (1+κ)^σ` for `σ ≥ 0` (Lemma 4.3). -/
lemma norm_Wfac_le_rpow {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hσ : 0 ≤ s.re) :
    ‖Wfac κ s‖ ≤ (1 + κ) ^ s.re := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Wfac]
  rw [Wfac_eq_integral hκ hs, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hκ]
  have hℓ0 : 0 ≤ Real.log (1 + κ) := Real.log_nonneg (by linarith)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := Real.log (1 + κ))
    (C := (1 + κ) ^ s.re) (f := fun u : ℝ => Complex.exp (s * u)) (by
      intro u hu
      rw [Set.uIoc_of_le hℓ0] at hu
      rw [Complex.norm_exp, Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hu.2 hσ)
  rw [sub_zero, abs_of_nonneg hℓ0] at hb
  calc κ⁻¹ * ‖∫ u in (0 : ℝ)..Real.log (1 + κ), Complex.exp (s * u)‖ ≤
        κ⁻¹ * ((1 + κ) ^ s.re * Real.log (1 + κ)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hκ.le)
    _ ≤ κ⁻¹ * ((1 + κ) ^ s.re * κ) := by
        gcongr
        exact log_one_add_le hκ
    _ = _ := by field_simp

/-- `|1 - W(s)| ≤ κ(1 + |s|)` when `κ(1 + |s|) ≤ 1` (Lemma 4.3). -/
lemma norm_one_sub_Wfac_le {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hs : s ≠ 0)
    (hsκ : κ * (1 + ‖s‖) ≤ 1) : ‖1 - Wfac κ s‖ ≤ κ * (1 + ‖s‖) := by
  set ℓ := Real.log (1 + κ) with hℓ
  have hℓ1 := log_one_add_le hκ
  have hℓ2 := log_one_add_ge hκ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  set z : ℂ := (ℓ : ℂ) * s with hz
  have hzn : ‖z‖ = ℓ * ‖s‖ := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℓ0]
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hzn]; nlinarith
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have e : 1 - Wfac κ s = ((1 - ℓ / κ : ℝ) : ℂ) - (Complex.exp z - 1 - z) / (s * κ) := by
    rw [Wfac, one_add_cpow_eq hκ, ← hℓ, ← hz, hz]
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((1 - ℓ / κ : ℝ) : ℂ)‖ ≤ κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hκ]; nlinarith
    · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hκ]; nlinarith
  have h2 : ‖(Complex.exp z - 1 - z) / (s * κ)‖ ≤ κ * ‖s‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      div_le_iff₀ (by positivity)]
    refine (Complex.norm_exp_sub_one_sub_id_le hz1).trans ?_
    rw [hzn]
    have : ℓ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hℓ0 hℓ1 2
    calc (ℓ * ‖s‖) ^ 2 = ℓ ^ 2 * ‖s‖ ^ 2 := by ring
      _ ≤ κ ^ 2 * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = κ * ‖s‖ * (‖s‖ * κ) := by ring
  linarith

/-! ### The tail `S_{≥X₀}` -/

lemma Zinf_ofReal (X₀ : ℕ) (σ : ℝ) : Zinf X₀ (σ : ℂ) = ((ZinfR X₀ σ : ℝ) : ℂ) := by
  unfold Zinf ZinfR
  push_cast
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg p)]
  push_cast; rfl

lemma headSum_re_nonneg (X₀ : ℕ) (σ : ℝ) : 0 ≤ (headSum X₀ (σ : ℂ)).re := by
  unfold headSum
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun n _ => ?_
  rw [show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_re]
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `|S_{≥X₀}(s)| ≤ X₀^{σ₀ - σ} Z_∞(σ₀)` for `0 < σ₀ ≤ σ`. -/
lemma norm_smooth_ge_le {X₀ : ℕ} (hX : 1 ≤ X₀) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {s : ℂ}
    (hσ : σ₀ ≤ s.re) :
    ‖Zinf X₀ s - headSum X₀ s‖ ≤ (X₀ : ℝ) ^ (σ₀ - s.re) * ZinfR X₀ σ₀ := by
  classical
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  have hf := hasSum_smooth_ge X₀ (s := s) (by linarith)
  have hg0 := Complex.hasSum_re (hasSum_smooth_ge X₀ (s := (σ₀ : ℂ)) (by simpa using hσ₀))
  have hg := hg0.mul_left ((X₀ : ℝ) ^ (σ₀ - s.re))
  refine (hf.norm_le_of_bounded hg fun d => ?_).trans ?_
  · split_ifs with hd
    · have hd0 : (0 : ℝ) < d := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hd.1)
      have hdX : (X₀ : ℝ) ≤ d := by exact_mod_cast hd.2
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0, Complex.neg_re,
        show -(σ₀ : ℂ) = ((-σ₀ : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow hd0.le, Complex.ofReal_re]
      have e : (d : ℝ) ^ (-s.re) = (d : ℝ) ^ (σ₀ - s.re) * (d : ℝ) ^ (-σ₀) := by
        rw [← Real.rpow_add hd0]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by linarith) hdX (by linarith))
        (Real.rpow_nonneg hd0.le _)
    · simp
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    rw [Complex.sub_re, Zinf_ofReal, Complex.ofReal_re]
    linarith [headSum_re_nonneg X₀ σ₀]

/-! ### The boundary terms -/

lemma card_boundarySet_le' (X₀ : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ((boundarySet X₀ κ).card : ℝ) ≤ κ * X₀ + 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hsub : boundarySet X₀ κ ⊆ Finset.Ico X₀ ⌈(1 + κ) * X₀⌉₊ := by
    intro d hd
    rw [mem_boundarySet hκ] at hd
    exact Finset.mem_Ico.mpr ⟨hd.2.1, Nat.lt_ceil.mpr hd.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hle : X₀ ≤ ⌈(1 + κ) * X₀⌉₊ := by
    have : (X₀ : ℝ) ≤ ⌈(1 + κ) * X₀⌉₊ := le_trans (by nlinarith) (Nat.le_ceil _)
    exact_mod_cast this
  have h1 : ((⌈(1 + κ) * X₀⌉₊ - X₀ : ℕ) : ℝ) < κ * X₀ + 1 := by
    rw [Nat.cast_sub hle]
    have := Nat.ceil_lt_add_one (show 0 ≤ (1 + κ) * (X₀ : ℝ) by positivity)
    linarith
  have h2 : ((boundarySet X₀ κ).card : ℝ) ≤ ((⌈(1 + κ) * X₀⌉₊ - X₀ : ℕ) : ℝ) := by
    exact_mod_cast hc
  linarith

/-- One boundary term has modulus at most `(d/(1+κ))^{-σ}`. -/
lemma norm_boundary_term_le {X₀ : ℕ} (hX : 1 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) {s : ℂ}
    (hσ : 0 ≤ s.re) (hs : s ≠ 0) {d : ℕ} (hd : d ∈ boundarySet X₀ κ) :
    ‖((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ)‖ ≤
      Real.exp (-(s.re * Real.log ((d : ℝ) / (1 + κ)))) := by
  rw [mem_boundarySet hκ] at hd
  have hX' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX
  have hdX : (X₀ : ℝ) ≤ d := by exact_mod_cast hd.2.1
  set c : ℝ := (d : ℝ) / (1 + κ) with hc
  have hc0 : 0 < c := by rw [hc]; apply div_pos <;> linarith
  have hcX : c < X₀ := by rw [hc, div_lt_iff₀ (by linarith)]; linarith
  have hlc : Real.log c ≤ Real.log X₀ := Real.log_le_log hc0 hcX.le
  have hlen : Real.log X₀ - Real.log c ≤ κ := by
    rw [← Real.log_div (by linarith) hc0.ne']
    calc Real.log (X₀ / c) ≤ Real.log (1 + κ) := by
          apply Real.log_le_log (by positivity)
          rw [hc, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ κ := log_one_add_le hκ
  have hns : (-s) ≠ 0 := neg_ne_zero.mpr hs
  have hint := integral_exp_mul_complex (a := Real.log c) (b := Real.log X₀) hns
  have hcpow : ∀ x : ℝ, 0 < x → ((x : ℝ) : ℂ) ^ (-s) = Complex.exp (-s * (Real.log x : ℂ)) := by
    intro x hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le,
      mul_comm]
  have e : (((c : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ) =
      (κ : ℂ)⁻¹ * ∫ u in Real.log c..Real.log X₀, Complex.exp (-s * u) := by
    rw [hint, hcpow c hc0, hcpow X₀ (by linarith)]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := Real.log c)
    (b := Real.log X₀) (C := Real.exp (-(s.re * Real.log c)))
    (f := fun u : ℝ => Complex.exp (-s * u)) (by
      intro u hu
      rw [Set.uIoc_of_le hlc] at hu
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [hu.1])
  rw [abs_of_nonneg (by linarith)] at hb
  calc κ⁻¹ * ‖∫ u in Real.log c..Real.log X₀, Complex.exp (-s * u)‖ ≤
        κ⁻¹ * (Real.exp (-(s.re * Real.log c)) * κ) := by
        apply mul_le_mul_of_nonneg_left (hb.trans ?_) (inv_nonneg.mpr hκ.le)
        exact mul_le_mul_of_nonneg_left hlen (Real.exp_pos _).le
    _ = _ := by field_simp

/-- **The boundary terms** (Lemma 4.3): `|boundary| ≤ 3κe^a` for `σ ≥ 1 - a/Λ`. -/
lemma norm_boundary_le_three {X₀ : ℕ} (hX : 1 ≤ Real.log X₀) {κ : ℝ} (hκ : 0 < κ)
    (hκ3 : κ ≤ 1 / 3) (hκX : 1 / (X₀ : ℝ) ≤ κ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ Real.log X₀)
    {s : ℂ} (hσ : 1 - a / Real.log X₀ ≤ s.re) (hs : s ≠ 0) :
    ‖boundary X₀ κ s‖ ≤ 3 * κ * Real.exp a := by
  set Λ := Real.log X₀ with hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra h
    have : (X₀ : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [hΛ, this, Real.log_zero] at hX; linarith
  have hX1 : 1 ≤ X₀ := by exact_mod_cast hX0
  set δ := a / Λ with hδ
  have hδ0 : 0 ≤ δ := div_nonneg ha hΛ0.le
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hΛ0]; exact ha1
  have hδΛ : δ * Λ = a := by rw [hδ]; field_simp
  have hσ0 : 0 ≤ s.re := by linarith
  have hterm : ∀ d ∈ boundarySet X₀ κ,
      ‖((((d : ℝ) / (1 + κ) : ℝ) : ℂ) ^ (-s) - ((X₀ : ℝ) : ℂ) ^ (-s)) / (s * κ)‖ ≤
        Real.exp a * Real.exp κ / X₀ := by
    intro d hd
    refine (norm_boundary_term_le hX1 hκ hσ0 hs hd).trans ?_
    rw [mem_boundarySet hκ] at hd
    have hdX : (X₀ : ℝ) ≤ d := by exact_mod_cast hd.2.1
    have hc0 : 0 < (d : ℝ) / (1 + κ) := div_pos (by linarith) (by linarith)
    have hlc : Λ - κ ≤ Real.log ((d : ℝ) / (1 + κ)) := by
      rw [Real.log_div (by linarith) (by linarith)]
      have h1 : Λ ≤ Real.log d := Real.log_le_log hX0 hdX
      linarith [log_one_add_le hκ]
    have hlc0 : 0 ≤ Real.log ((d : ℝ) / (1 + κ)) := by linarith
    rw [show Real.exp a * Real.exp κ / X₀ = Real.exp (a + κ - Λ) by
      rw [Real.exp_sub, Real.exp_add, hΛ, Real.exp_log hX0]]
    apply Real.exp_le_exp.mpr
    have h1 : (1 - δ) * Real.log ((d : ℝ) / (1 + κ)) ≤ s.re * Real.log ((d : ℝ) / (1 + κ)) :=
      mul_le_mul_of_nonneg_right hσ hlc0
    have h2 : (1 - δ) * (Λ - κ) ≤ (1 - δ) * Real.log ((d : ℝ) / (1 + κ)) :=
      mul_le_mul_of_nonneg_left hlc (by linarith)
    nlinarith
  unfold boundary
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := card_boundarySet_le' X₀ hκ
  have hexpκ : Real.exp κ ≤ 3 / 2 := by
    have h := Real.add_one_le_exp (-κ)
    have h2 : Real.exp (-κ) * Real.exp κ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos κ]
  have hea := Real.exp_pos a
  calc ((boundarySet X₀ κ).card : ℝ) * (Real.exp a * Real.exp κ / X₀) ≤
        (κ * X₀ + 1) * (Real.exp a * Real.exp κ / X₀) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (κ + 1 / X₀) * Real.exp κ * Real.exp a := by field_simp
    _ ≤ (2 * κ) * (3 / 2) * Real.exp a := by gcongr; linarith
    _ = 3 * κ * Real.exp a := by ring

/-! ### The integrals `∫_n^{n+1} x^{-s} dx` -/

/-- `I_n(s) = ∫_n^{n+1} x^{-s} dx = ((n+1)^{1-s} - n^{1-s})/(1-s)`. -/
noncomputable def intCpow (s : ℂ) (n : ℕ) : ℂ :=
  ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((n : ℝ) : ℂ) ^ (1 - s)) / (1 - s)

lemma intCpow_eq_integral {s : ℂ} (hs : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    intCpow s n = ∫ x in (n : ℝ)..((n : ℝ) + 1), (x : ℂ) ^ (-s) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [integral_cpow (Or.inr ⟨fun h => hs (by linear_combination -h), by
    rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> linarith⟩)]
  unfold intCpow
  congr 1 <;> ring_nf

lemma sum_intCpow (s : ℂ) (hs : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico 1 N, intCpow s n = (1 - ((N : ℝ) : ℂ) ^ (1 - s)) / (s - 1) := by
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, ih]
    unfold intCpow
    push_cast
    field_simp
    ring

/-- `|I_n(s)| ≤ n^{-σ}` for `σ ≥ 0`. -/
lemma norm_intCpow_le {s : ℂ} (hs : s ≠ 1) (hσ : 0 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖intCpow s n‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [intCpow_eq_integral hs hn]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ))
    (b := (n : ℝ) + 1) (C := (n : ℝ) ^ (-s.re)) (f := fun x : ℝ => (x : ℂ) ^ (-s)) (by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1]), Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hx.1.le (by linarith))
  rwa [show (n : ℝ) + 1 - n = 1 by ring, abs_one, mul_one] at hb

/-- `|x^{-s} - n^{-s}| ≤ |s| n^{-σ-1} (x - n)` for `n ≤ x`, `σ ≥ 0`. -/
lemma norm_cpow_sub_cpow_le {s : ℂ} (hs : s ≠ 0) (hσ : 0 ≤ s.re) {n x : ℝ} (hn : 0 < n)
    (hx : n ≤ x) :
    ‖(x : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ * n ^ (-s.re - 1) * (x - n) := by
  have hint := integral_cpow (a := n) (b := x) (r := -s - 1) (Or.inr ⟨fun h => hs (by
    linear_combination -h), by rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> linarith⟩)
  rw [show -s - 1 + 1 = -s by ring] at hint
  have e : (x : ℂ) ^ (-s) - (n : ℂ) ^ (-s) =
      (-s) * ∫ u in n..x, (u : ℂ) ^ (-s - 1) := by
    rw [hint]; field_simp [neg_ne_zero.mpr hs]
  rw [e, norm_mul, norm_neg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := n) (b := x)
    (C := n ^ (-s.re - 1)) (f := fun u : ℝ => (u : ℂ) ^ (-s - 1)) (by
      intro u hu
      rw [Set.uIoc_of_le hx] at hu
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1])]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      exact Real.rpow_le_rpow_of_nonpos hn hu.1.le (by linarith))
  rw [abs_of_nonneg (by linarith)] at hb
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- `|n^{-s} - I_n(s)| ≤ |s| n^{-σ-1}/2` for `σ ≥ 0` (the bracket near the pole). -/
lemma norm_cpow_sub_intCpow_le {s : ℂ} (hs : s ≠ 1) (hs0 : s ≠ 0) (hσ : 0 ≤ s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖((n : ℝ) : ℂ) ^ (-s) - intCpow s n‖ ≤ ‖s‖ / 2 * (n : ℝ) ^ (-s.re - 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hI1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) := intervalIntegral.intervalIntegrable_cpow (Or.inr (by
        rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> linarith))
  have e : ((n : ℝ) : ℂ) ^ (-s) - intCpow s n =
      -∫ x in (n : ℝ)..((n : ℝ) + 1), ((x : ℂ) ^ (-s) - ((n : ℝ) : ℂ) ^ (-s)) := by
    rw [intervalIntegral.integral_sub hI1 intervalIntegrable_const,
      intervalIntegral.integral_const, intCpow_eq_integral hs hn]
    simp
  rw [e, norm_neg]
  set C := ‖s‖ * (n : ℝ) ^ (-s.re - 1)
  have hg : IntervalIntegrable (fun x : ℝ => C * (x - n)) MeasureTheory.volume
      (n : ℝ) ((n : ℝ) + 1) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Filter.Eventually.of_forall fun x hx => norm_cpow_sub_cpow_le hs0 hσ hn0 hx.1.le) hg).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- `∑_{1 ≤ n < N} n^{-σ-1} ≤ 1 + 1/σ` for `σ > 0`. -/
lemma sum_rpow_neg_le {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-σ - 1) ≤ 1 + 1 / σ := by
  -- `σ n^{-σ-1} ≤ (n-1)^{-σ} - n^{-σ}` for `n ≥ 2`
  have hstep : ∀ n : ℕ, 2 ≤ n →
      σ * (n : ℝ) ^ (-σ - 1) ≤ ((n : ℝ) - 1) ^ (-σ) - (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hm0 : (0 : ℝ) < n - 1 := by linarith
    have hlog : 1 / (n : ℝ) ≤ Real.log (n / (n - 1)) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (n : ℝ) / (n - 1) by positivity)
      rw [inv_div] at this
      have e : 1 - ((n : ℝ) - 1) / n = 1 / n := by field_simp; ring
      linarith
    have hpow : ((n : ℝ) - 1) ^ (-σ) = (n : ℝ) ^ (-σ) * Real.exp (σ * Real.log (n / (n - 1))) := by
      rw [Real.log_div hn0.ne' hm0.ne', Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0,
        ← Real.exp_add]
      ring_nf
    have hexp := Real.add_one_le_exp (σ * Real.log (n / (n - 1)))
    have hnσ : (n : ℝ) ^ (-σ - 1) = (n : ℝ) ^ (-σ) * (1 / n) := by
      rw [Real.rpow_sub hn0, Real.rpow_one]; ring
    rw [hpow, hnσ]
    have h0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn0.le _
    have : σ * (1 / n) ≤ σ * Real.log (n / (n - 1)) := mul_le_mul_of_nonneg_left hlog hσ.le
    nlinarith
  -- induction: `∑_{1 ≤ n < N} n^{-σ-1} ≤ 1 + (1 - (N-1)^{-σ})/σ` for `N ≥ 2`
  have key : ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-σ - 1) ≤ 1 + (1 - ((N : ℝ) - 1) ^ (-σ)) / σ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have := hstep M hM
      push_cast
      rw [show (M : ℝ) + 1 - 1 = M by ring]
      have e : 1 + (1 - (M : ℝ) ^ (-σ)) / σ =
          1 + (1 - ((M : ℝ) - 1) ^ (-σ)) / σ + (((M : ℝ) - 1) ^ (-σ) - (M : ℝ) ^ (-σ)) / σ := by
        field_simp; ring
      rw [e]
      have : (M : ℝ) ^ (-σ - 1) ≤ (((M : ℝ) - 1) ^ (-σ) - (M : ℝ) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hσ]; linarith
      linarith
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : Finset.Ico 1 N ⊆ {1} := by
      intro n hn; simp only [Finset.mem_Ico] at hn; simp; omega
    calc ∑ n ∈ Finset.Ico 1 N, (n : ℝ) ^ (-σ - 1) ≤ ∑ n ∈ ({1} : Finset ℕ), (n : ℝ) ^ (-σ - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg this fun n _ _ =>
            Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ ≤ 1 + 1 / σ := by simp; positivity
  · refine (key N hN).trans ?_
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : 0 ≤ ((N : ℝ) - 1) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have : (1 - ((N : ℝ) - 1) ^ (-σ)) / σ ≤ 1 / σ :=
      div_le_div_of_nonneg_right (by linarith) hσ.le
    linarith

end LocalPNT

end
