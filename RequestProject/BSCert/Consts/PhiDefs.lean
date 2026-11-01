module

public import Mathlib

/-!
# The cutoff `ϕ` of (1): derivatives on `(0, 1)`

`ϕ(t) = ψ(t)/(ψ(t) + ψ(1 - t))` with `ψ(t) = e^{-1/t}` for `t > 0` and `ψ(t) = 0` otherwise.
This is Mathlib's `Real.smoothTransition` (`phiCut_eq`). On `(0, 1)`, `ϕ = 1/(1 + e^g)` with
`g = 1/t - 1/(1-t)`; with `q = 1/t² + 1/(1-t)²` and `q' = -2/t³ + 2/(1-t)³`,
```
ϕ'  = e^g q/(1 + e^g)²,
ϕ'' = e^g/(1 + e^g)² · (q' + q² (e^g - 1)/(e^g + 1)).
```
We prove these formulas, the analytic bound `0 ≤ ϕ' ≤ 2` of (2) (with `ϕ'(1/2) = 2`), and the
bound `|ϕ''| ≤ e^{-|g|}(q² + |q'|)` used near the ends.
-/

@[expose] public section

namespace BSCert.Consts

open Real Filter Topology

/-- `ψ(t) = e^{-1/t}` for `t > 0`, `0` otherwise. -/
noncomputable def psiCut (t : ℝ) : ℝ := if t ≤ 0 then 0 else Real.exp (-1 / t)

/-- The cutoff `ϕ(t) = ψ(t)/(ψ(t) + ψ(1 - t))` of (1). -/
noncomputable def phiCut (t : ℝ) : ℝ := psiCut t / (psiCut t + psiCut (1 - t))

theorem phiCut_eq : phiCut = Real.smoothTransition := by
  funext t
  simp only [phiCut, psiCut, Real.smoothTransition, expNegInvGlue, neg_div, one_div]

noncomputable def gq (t : ℝ) : ℝ := 1 / t - 1 / (1 - t)
noncomputable def qq (t : ℝ) : ℝ := 1 / t ^ 2 + 1 / (1 - t) ^ 2
noncomputable def dq (t : ℝ) : ℝ := -2 / t ^ 3 + 2 / (1 - t) ^ 3

/-- `ϕ'` on `(0, 1)`. -/
noncomputable def D1 (t : ℝ) : ℝ := Real.exp (gq t) * qq t / (1 + Real.exp (gq t)) ^ 2

/-- `ϕ''` on `(0, 1)`. -/
noncomputable def D2 (t : ℝ) : ℝ :=
  Real.exp (gq t) / (1 + Real.exp (gq t)) ^ 2 *
    (dq t + qq t ^ 2 * ((Real.exp (gq t) - 1) / (Real.exp (gq t) + 1)))

lemma phiCut_eq_on {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    phiCut t = 1 / (1 + Real.exp (gq t)) := by
  have h1' : ¬ (1 - t ≤ 0) := by linarith
  simp only [phiCut, psiCut, not_le.mpr h0, h1', if_false, gq]
  have e1 := Real.exp_pos (-1 / t)
  have e2 := Real.exp_pos (-1 / (1 - t))
  have : Real.exp (1 / t - 1 / (1 - t)) = Real.exp (-1 / (1 - t)) / Real.exp (-1 / t) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [this]
  field_simp

lemma hasDerivAt_gq {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) : HasDerivAt gq (-qq t) t := by
  have h1' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha := (hasDerivAt_id t).inv h0
  have hb := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv h1'
  have := ha.sub hb
  unfold gq qq
  convert! this using 1
  · funext x; simp only [Pi.sub_apply, Pi.inv_apply, id, one_div]
  · simp only [Pi.sub_apply, id, one_div]; field_simp; ring

lemma hasDerivAt_qq {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) : HasDerivAt qq (dq t) t := by
  have h1' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 h0)
  have hb := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2).inv (pow_ne_zero 2 h1')
  have := ha.add hb
  unfold qq dq
  convert! this using 1
  · funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply, id, one_div]
  · simp only [Pi.sub_apply, Pi.pow_apply, id]; field_simp; ring

lemma hasDerivAt_phi0 {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    HasDerivAt (fun x => 1 / (1 + Real.exp (gq x))) (D1 t) t := by
  have hE := (hasDerivAt_gq h0 h1).exp
  have hpos : 1 + Real.exp (gq t) ≠ 0 := by positivity
  have := ((hasDerivAt_const t (1 : ℝ)).add hE).inv hpos
  unfold D1
  convert! this using 1
  · funext x; simp only [Pi.add_apply, Pi.inv_apply, one_div]
  · simp only [Pi.add_apply]; field_simp; ring

lemma hasDerivAt_D1 {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) : HasDerivAt D1 (D2 t) t := by
  have hE := (hasDerivAt_gq h0 h1).exp
  have hq := hasDerivAt_qq h0 h1
  have hpos : (1 + Real.exp (gq t)) ^ 2 ≠ 0 := by positivity
  have := (hE.mul hq).div (((hasDerivAt_const t (1 : ℝ)).add hE).pow 2) hpos
  unfold D2
  have hp1 : (Real.exp (gq t) + 1) ≠ 0 := by positivity
  have hp2 : (1 + Real.exp (gq t)) ≠ 0 := by positivity
  convert! this using 1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  simp only [Nat.cast_ofNat]
  field_simp
  ring

lemma deriv_phiCut_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : deriv phiCut t = D1 t := by
  have hev : phiCut =ᶠ[𝓝 t] fun x => 1 / (1 + Real.exp (gq x)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    exact phiCut_eq_on hx.1 hx.2
  rw [hev.deriv_eq]
  exact (hasDerivAt_phi0 h0.ne' (by linarith : t ≠ 1).symm.symm).deriv

lemma deriv_phiCut_eventually {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : deriv phiCut =ᶠ[𝓝 t] D1 := by
  filter_upwards [Ioo_mem_nhds h0 h1] with x hx
  exact deriv_phiCut_eq hx.1 hx.2

lemma deriv2_phiCut_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : deriv (deriv phiCut) t = D2 t := by
  rw [(deriv_phiCut_eventually h0 h1).deriv_eq]
  exact (hasDerivAt_D1 h0.ne' (by linarith : t ≠ 1)).deriv

/-! ## Outside `(0, 1)` -/

lemma phiCut_of_nonpos {t : ℝ} (h : t ≤ 0) : phiCut t = 0 := by
  rw [phiCut_eq]; exact Real.smoothTransition.zero_of_nonpos h

lemma phiCut_of_one_le {t : ℝ} (h : 1 ≤ t) : phiCut t = 1 := by
  rw [phiCut_eq]; exact Real.smoothTransition.one_of_one_le h

lemma deriv_phiCut_of_neg {t : ℝ} (h : t < 0) : deriv phiCut t = 0 := by
  have hev : phiCut =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with x hx
    exact phiCut_of_nonpos (le_of_lt hx)
  rw [hev.deriv_eq]; simp

lemma deriv_phiCut_of_gt {t : ℝ} (h : 1 < t) : deriv phiCut t = 0 := by
  have hev : phiCut =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact phiCut_of_one_le (le_of_lt hx)
  rw [hev.deriv_eq]; simp

lemma deriv2_phiCut_of_neg {t : ℝ} (h : t < 0) : deriv (deriv phiCut) t = 0 := by
  have hev : deriv phiCut =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with x hx
    exact deriv_phiCut_of_neg hx
  rw [hev.deriv_eq]; simp

lemma deriv2_phiCut_of_gt {t : ℝ} (h : 1 < t) : deriv (deriv phiCut) t = 0 := by
  have hev : deriv phiCut =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with x hx
    exact deriv_phiCut_of_gt hx
  rw [hev.deriv_eq]; simp

lemma continuous_deriv_phiCut : Continuous (deriv phiCut) := by
  rw [phiCut_eq]
  exact (ContDiff.iterate_deriv 1 (Real.smoothTransition.contDiff (n := ⊤))).continuous

lemma continuous_deriv2_phiCut : Continuous (deriv (deriv phiCut)) := by
  rw [phiCut_eq]
  exact (ContDiff.iterate_deriv 2 (Real.smoothTransition.contDiff (n := ⊤))).continuous

/-- A closed condition on a continuous function that holds off `{0, 1}` holds everywhere. -/
lemma mem_of_ne_zero_one {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ} (hS : IsClosed S)
    (h : ∀ t, t ≠ 0 → t ≠ 1 → f t ∈ S) (t : ℝ) : f t ∈ S := by
  by_cases ht : t ≠ 0 ∧ t ≠ 1
  · exact h t ht.1 ht.2
  have ht' : t = 0 ∨ t = 1 := by tauto
  have hne : 1 - t ≠ t := by rcases ht' with rfl | rfl <;> norm_num
  have hev : ∀ᶠ x in 𝓝[≠] t, f x ∈ S := by
    have h1 : ∀ᶠ x in 𝓝[≠] t, x ≠ 1 - t :=
      nhdsWithin_le_nhds ((isOpen_ne).mem_nhds hne.symm)
    have h2 : ∀ᶠ x in 𝓝[≠] t, x ≠ t := self_mem_nhdsWithin
    filter_upwards [h1, h2] with x hx1 hx2
    apply h x <;> rcases ht' with rfl | rfl <;> simp_all
  exact hS.mem_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-! ## The analytic bound `0 ≤ ϕ' ≤ 2` -/

lemma sq_le_exp_bound (g : ℝ) : Real.exp g * g ^ 2 ≤ (Real.exp g - 1) ^ 2 := by
  set h := g / 2
  have hg : g = 2 * h := by simp only [h]; ring
  have hE : Real.exp g = Real.exp h * Real.exp h := by rw [hg, two_mul, Real.exp_add]
  have hs : (Real.exp g - 1) ^ 2 = Real.exp g * (2 * Real.sinh h) ^ 2 := by
    rw [Real.sinh_eq, hE]
    have := Real.exp_pos h
    have e : Real.exp (-h) = (Real.exp h)⁻¹ := Real.exp_neg h
    rw [e]; field_simp
  have hsh : h ^ 2 ≤ Real.sinh h ^ 2 := by
    rcases le_total 0 h with h0 | h0
    · have := Real.self_le_sinh_iff.mpr h0; nlinarith
    · have := Real.sinh_le_self_iff.mpr h0; nlinarith
  rw [hs, hg]
  have := Real.exp_pos (2 * h)
  nlinarith

lemma D1_nonneg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 ≤ D1 t := by
  have h1' : 0 < 1 - t := by linarith
  have : 0 ≤ qq t := by unfold qq; positivity
  unfold D1; positivity

lemma D1_le_two {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : D1 t ≤ 2 := by
  have h1' : 0 < 1 - t := by linarith
  set E := Real.exp (gq t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have key := sq_le_exp_bound (gq t)
  rw [← hE] at key
  -- `E/(1+E)² ≤ 1/(4 + g²)`
  have hw : E * (4 + gq t ^ 2) ≤ (1 + E) ^ 2 := by nlinarith
  -- `q ≤ 2 (4 + g²)`
  have hq : qq t ≤ 2 * (4 + gq t ^ 2) := by
    unfold qq gq
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    have e : (1 / t - 1 / (1 - t)) = (1 - 2 * t) / (t * (1 - t)) := by field_simp; ring
    rw [e, div_pow]
    have hs : 0 < t * (1 - t) := by positivity
    rw [mul_add, mul_div_assoc', add_mul, div_mul_eq_mul_div]
    rw [show (2 * (1 - 2 * t) ^ 2 * (t ^ 2 * (1 - t) ^ 2)) / (t * (1 - t)) ^ 2
        = 2 * (1 - 2 * t) ^ 2 by field_simp]
    have hs4 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - t * (1 - t))
      (by linarith : (0 : ℝ) ≤ 1 / 2 - t * (1 - t)), hs]
  unfold D1
  rw [← hE, div_le_iff₀ (by positivity)]
  have hq0 : 0 ≤ qq t := by unfold qq; positivity
  nlinarith [mul_le_mul_of_nonneg_left hq hE0.le]

lemma D1_half : D1 (1 / 2) = 2 := by
  unfold D1 gq qq; norm_num

/-! ## The bound near the ends -/

lemma D2_symm (t : ℝ) : D2 (1 - t) = -D2 t := by
  unfold D2 gq qq dq
  have e : 1 / (1 - t) - 1 / (1 - (1 - t)) = -(1 / t - 1 / (1 - t)) := by ring_nf
  rw [e, Real.exp_neg]
  set E := Real.exp (1 / t - 1 / (1 - t)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e2 : (1 - (1 - t)) = t := by ring
  rw [e2]
  field_simp
  ring

/-- `|ϕ''| ≤ e^{-|g|} (q² + |q'|)` on `(0,1)`. -/
lemma abs_D2_le (t : ℝ) :
    |D2 t| ≤ Real.exp (-|gq t|) * (qq t ^ 2 + |dq t|) := by
  set E := Real.exp (gq t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hw : E / (1 + E) ^ 2 ≤ Real.exp (-|gq t|) := by
    rcases le_total 0 (gq t) with hg | hg
    · rw [abs_of_nonneg hg, Real.exp_neg, ← hE, div_le_iff₀ (by positivity)]
      rw [inv_mul_eq_div, le_div_iff₀ hE0]
      nlinarith
    · rw [abs_of_nonpos hg, neg_neg, ← hE, div_le_iff₀ (by positivity)]
      have : 0 ≤ E * (2 * E + E ^ 2) := by positivity
      nlinarith
  have hr : |(E - 1) / (E + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by linarith : 0 < E + 1), div_le_one (by linarith)]
    rw [abs_le]; constructor <;> linarith
  unfold D2
  rw [← hE, abs_mul, abs_of_nonneg (by positivity : 0 ≤ E / (1 + E) ^ 2)]
  have hX : |dq t + qq t ^ 2 * ((E - 1) / (E + 1))| ≤ qq t ^ 2 + |dq t| := by
    calc |dq t + qq t ^ 2 * ((E - 1) / (E + 1))| ≤ |dq t| + |qq t ^ 2 * ((E - 1) / (E + 1))| :=
          abs_add_le _ _
      _ = |dq t| + qq t ^ 2 * |(E - 1) / (E + 1)| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (qq t))]
      _ ≤ |dq t| + qq t ^ 2 * 1 := by gcongr
      _ = qq t ^ 2 + |dq t| := by ring
  exact mul_le_mul hw hX (abs_nonneg _) (Real.exp_pos _).le

lemma abs_D2_le_small {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 50) : |D2 t| ≤ 10 := by
  refine le_trans (abs_D2_le t) ?_
  set x := 1 / t with hx
  have hx50 : 50 ≤ x := by rw [hx, le_div_iff₀ h0]; linarith
  have hx0 : 0 < x := by linarith
  have ht : t = 1 / x := by rw [hx]; field_simp
  have h1t : 1 / 2 ≤ 1 - t := by linarith
  have hinv : 1 / (1 - t) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  -- `|g| ≥ x - 2`
  have hg : x - 2 ≤ |gq t| := by
    unfold gq
    have : 0 < 1 / (1 - t) := by positivity
    rw [← hx]
    exact le_trans (by linarith) (le_abs_self _)
  -- `q ≤ 2x²`, `|q'| ≤ 4x³`
  have hq : qq t ≤ 2 * x ^ 2 := by
    unfold qq
    have : 1 / (1 - t) ^ 2 ≤ 4 := by
      rw [one_div, ← inv_pow, ← one_div]; nlinarith [(by positivity : (0 : ℝ) ≤ 1 / (1 - t))]
    have e : 1 / t ^ 2 = x ^ 2 := by rw [hx]; field_simp
    nlinarith
  have h1t' : 0 < 1 - t := by linarith
  have hq0 : 0 ≤ qq t := by unfold qq; positivity
  have hdq : |dq t| ≤ 4 * x ^ 3 := by
    unfold dq
    have a1 : 1 / (1 - t) ^ 3 ≤ 8 := by
      rw [one_div, ← inv_pow, ← one_div]
      have h0' : (0 : ℝ) ≤ 1 / (1 - t) := by positivity
      calc (1 / (1 - t)) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0' hinv 3
        _ = 8 := by norm_num
    have a0 : 0 ≤ 1 / (1 - t) ^ 3 := by positivity
    have e : 1 / t ^ 3 = x ^ 3 := by rw [hx]; field_simp
    have e1 : -2 / t ^ 3 + 2 / (1 - t) ^ 3 = -2 * (1 / t ^ 3) + 2 * (1 / (1 - t) ^ 3) := by ring
    rw [e1, e, abs_le]
    constructor <;> nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 50) hx50 3]
  have hsum : qq t ^ 2 + |dq t| ≤ 8 * x ^ 4 := by
    have : qq t ^ 2 ≤ 4 * x ^ 4 := by nlinarith
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 50) hx50 3]
  -- `e^{-|g|} ≤ e² e^{-x}` and `x⁴ e^{-x} ≤ 8!/x⁴`
  have hexp : Real.exp (-|gq t|) ≤ Real.exp 2 * Real.exp (-x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hfac := Real.pow_div_factorial_le_exp x hx0.le 8
  have hex := Real.exp_pos x
  have e2 : Real.exp 2 ≤ 7.39 := by
    have := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  have hx4 : x ^ 4 * Real.exp (-x) ≤ 40320 / x ^ 4 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hex (by positivity)]
    simp [Nat.factorial] at hfac
    rw [div_le_iff₀ (by norm_num)] at hfac
    nlinarith
  have hx4' : 40320 / x ^ 4 ≤ 40320 / 50 ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx50 4)
  have hpos : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  calc Real.exp (-|gq t|) * (qq t ^ 2 + |dq t|) ≤ Real.exp 2 * Real.exp (-x) * (8 * x ^ 4) :=
        mul_le_mul hexp hsum (by positivity) (by positivity)
    _ = 8 * Real.exp 2 * (x ^ 4 * Real.exp (-x)) := by ring
    _ ≤ 8 * 7.39 * (40320 / 50 ^ 4) := by
        apply mul_le_mul (by linarith) (le_trans hx4 hx4') (by positivity) (by norm_num)
    _ ≤ 10 := by norm_num

end BSCert.Consts
