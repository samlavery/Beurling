module

public import RequestProject.Beurling.DesignedZero

/-!
# Bounds on the transforms of the oscillations (Section 4.2, bullets after (17), and (18))

* `oscHat` : `R̂_k(s) = s ∫_1^∞ R_k(x) x^{-s-1} dx`;
* `oscHat_eq_Mk_add_Ek` : `R̂_k = M_k + E_k` (the resonant and the conjugate term of (17));
* `norm_Ek_le` : `|E_k| ≤ 0.51 x_k^{θ-σ}` on `0.99 ≤ σ ≤ 2`, `|t - γ_k| ≤ 1`;
* `norm_oscHat_le_of_re` : `|R̂_k(s)| ≤ 5 |s| x_k^{-2/5}` for `σ ≥ θ + 2/5`;
* `norm_tsum_oscHat_le` : (18), `∑_k |R̂_k(s)| ≤ |s| e^{-0.39 X₀²}` when the switch-on points
  satisfy `x⁺_0 ≥ e^{X₀²}` and `x⁺_{k+1} ≥ e^{x⁺_k}`.
-/

@[expose] public section

open Complex Metric Set Filter MeasureTheory SmoothStep Oscillation

namespace DesignedZero

/-- The transform `R̂_k(s) = s ∫_1^∞ R_k(x) x^{-s-1} dx = ∫ x^{-s} dR_k` of one oscillation. -/
noncomputable def oscHat (θ α γ xk : ℝ) (s : ℂ) : ℂ :=
  s * ∫ x in Ioi (1 : ℝ), (oscTerm θ α γ xk x : ℂ) * (x : ℂ) ^ (-s - 1)

/-- The conjugate term `E_k(s) = (α s/2) (x⁺)^{-w'} Φ(w')/w'`, `w' = s - θ + iγ`, of (17). -/
noncomputable def Ek (θ α γ x : ℝ) (s : ℂ) : ℂ :=
  α * s / 2 * ((x : ℂ) ^ (-(s - θ + γ * I)) * phiTransform (s - θ + γ * I) / (s - θ + γ * I))

/-- (17): `R̂_k = M_k + E_k` for `Re s > θ`. -/
theorem oscHat_eq_Mk_add_Ek {θ α γ xk : ℝ} (hxk : 1 ≤ xk) {s : ℂ} (hs : θ < s.re) :
    oscHat θ α γ xk s = Mk θ α γ xk s + Ek θ α γ xk s := by
  unfold oscHat Mk Ek
  rw [mellin_oscTerm hxk hs]
  ring

/-- `|(α s/2) x^{-w} Φ(w)/w| ≤ (|α| |s|/2) x^{θ - σ}/|w|` when `Re w = σ - θ ≥ 0`. -/
lemma norm_term_le {θ α xk : ℝ} (hxk : 1 ≤ xk) {s w : ℂ} (hw : w.re = s.re - θ)
    (hw0 : 0 ≤ w.re) :
    ‖α * s / 2 * ((xk : ℂ) ^ (-w) * phiTransform w / w)‖ ≤
      |α| * ‖s‖ / 2 * (xk ^ (θ - s.re) / ‖w‖) := by
  have hxk0 : 0 < xk := by linarith
  rw [norm_mul]
  have hn : ‖(α : ℂ) * s / 2‖ = |α| * ‖s‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]; simp
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxk0, neg_re, hw, neg_sub]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_of_le_one_right (Real.rpow_nonneg hxk0.le _) (norm_phiTransform_le hw0)

/-- **The conjugate term**: on `0.99 ≤ σ ≤ 2`, `|t - γ_k| ≤ 1`, with `|α_k| ≤ 2`, `θ ≤ 1/2` and
`γ_k ≥ 200`, `|E_k(s)| ≤ 0.51 x_k^{θ-σ}`. -/
theorem norm_Ek_le {θ α γ xk : ℝ} (hxk : 1 ≤ xk) (hα : |α| ≤ 2) (hθ : θ ≤ 1 / 2)
    (hγ : 200 ≤ γ) {s : ℂ} (hσ1 : 99 / 100 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : |s.im - γ| ≤ 1) :
    ‖Ek θ α γ xk s‖ ≤ 0.51 * xk ^ (θ - s.re) := by
  have hxk0 : 0 < xk := by linarith
  set w' := s - θ + γ * I with hw'
  have hre : w'.re = s.re - θ := by simp [hw']
  have h1 := norm_term_le (α := α) hxk hre (by rw [hre]; linarith)
  have him : w'.im = s.im + γ := by simp [hw']
  have ht' := abs_le.mp ht
  have hw'n : 2 * γ - 1 ≤ ‖w'‖ := by
    have := Complex.abs_im_le_norm w'; rw [him, abs_of_pos (by linarith)] at this; linarith
  have hsn : ‖s‖ ≤ γ + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at this; linarith
  have hratio : ‖s‖ / ‖w'‖ ≤ 0.51 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hX := Real.rpow_nonneg hxk0.le (θ - s.re)
  unfold Ek
  rw [← hw']
  calc _ ≤ |α| * ‖s‖ / 2 * (xk ^ (θ - s.re) / ‖w'‖) := h1
    _ = |α| / 2 * (‖s‖ / ‖w'‖) * xk ^ (θ - s.re) := by ring
    _ ≤ 1 * 0.51 * xk ^ (θ - s.re) := by
        gcongr
        · linarith
    _ = 0.51 * xk ^ (θ - s.re) := by ring

/-- **One term of (18)**: for `σ ≥ θ + 2/5`, `|α_k| ≤ 2` and `x_k ≥ 1`,
`|R̂_k(s)| ≤ 5 |s| x_k^{-2/5}`. -/
theorem norm_oscHat_le_of_re {θ α γ xk : ℝ} (hxk : 1 ≤ xk) (hα : |α| ≤ 2) {s : ℂ}
    (hσ : θ + 2 / 5 ≤ s.re) :
    ‖oscHat θ α γ xk s‖ ≤ 5 * ‖s‖ * xk ^ (-(2 / 5 : ℝ)) := by
  have hxk0 : 0 < xk := by linarith
  rw [oscHat_eq_Mk_add_Ek hxk (by linarith)]
  set w := s - θ - γ * I with hw
  set w' := s - θ + γ * I with hw'
  have hre : w.re = s.re - θ := by simp [hw]
  have hre' : w'.re = s.re - θ := by simp [hw']
  have h1 := norm_term_le (α := α) hxk hre (by rw [hre]; linarith)
  have h2 := norm_term_le (α := α) hxk hre' (by rw [hre']; linarith)
  have hwn : 2 / 5 ≤ ‖w‖ := le_trans (by rw [hre]; linarith) (Complex.re_le_norm w)
  have hw'n : 2 / 5 ≤ ‖w'‖ := le_trans (by rw [hre']; linarith) (Complex.re_le_norm w')
  have hX : xk ^ (θ - s.re) ≤ xk ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hxk (by linarith)
  have hX0 := Real.rpow_nonneg hxk0.le (θ - s.re)
  have hinv : ∀ v : ℂ, 2 / 5 ≤ ‖v‖ → xk ^ (θ - s.re) / ‖v‖ ≤ 5 / 2 * xk ^ (-(2 / 5 : ℝ)) := by
    intro v hv
    rw [div_le_iff₀ (by linarith)]
    have : 5 / 2 * xk ^ (-(2 / 5 : ℝ)) * (2 / 5) ≤ 5 / 2 * xk ^ (-(2 / 5 : ℝ)) * ‖v‖ :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    linarith
  unfold Mk Ek
  rw [← hw, ← hw']
  calc _ ≤ ‖α * s / 2 * ((xk : ℂ) ^ (-w) * phiTransform w / w)‖ +
        ‖α * s / 2 * ((xk : ℂ) ^ (-w') * phiTransform w' / w')‖ := norm_add_le _ _
    _ ≤ |α| * ‖s‖ / 2 * (xk ^ (θ - s.re) / ‖w‖) + |α| * ‖s‖ / 2 * (xk ^ (θ - s.re) / ‖w'‖) :=
        add_le_add h1 h2
    _ ≤ 2 * ‖s‖ / 2 * (5 / 2 * xk ^ (-(2 / 5 : ℝ))) +
        2 * ‖s‖ / 2 * (5 / 2 * xk ^ (-(2 / 5 : ℝ))) := by
        gcongr
        · exact hinv w hwn
        · exact hinv w' hw'n
    _ = 5 * ‖s‖ * xk ^ (-(2 / 5 : ℝ)) := by ring

/-- `x_{k+1}^{-2/5} ≤ x_k^{-2/5}/2` when `x_{k+1} ≥ e^{x_k}` and `x_k ≥ 20`. -/
lemma rpow_neg_two_fifths_succ_le {a b : ℝ} (ha : 20 ≤ a) (hb : Real.exp a ≤ b) :
    b ^ (-(2 / 5 : ℝ)) ≤ a ^ (-(2 / 5 : ℝ)) / 2 := by
  have ha0 : 0 < a := by linarith
  have hb6 : 6 * a ≤ b := by
    have h1 := Real.add_one_le_exp (a / 2)
    have h2 : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : (a / 2 + 1) ^ 2 ≤ Real.exp (a / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  have hb0 : 0 < b := by linarith
  have hmono : b ^ (-(2 / 5 : ℝ)) ≤ (6 * a) ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hb6 (by norm_num)
  rw [Real.mul_rpow (by norm_num) ha0.le] at hmono
  have h6 : (6 : ℝ) ^ (-(2 / 5 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ (5 : ℝ) ≤ 6 ^ (2 : ℝ) := by norm_num
    calc (1 / 2 : ℝ)⁻¹ = (2 ^ (5 : ℝ)) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (6 ^ (2 : ℝ)) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) this (by norm_num)
      _ = 6 ^ (2 / 5 : ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  have hapos := Real.rpow_nonneg ha0.le (-(2 / 5 : ℝ))
  nlinarith

/-- `x_k^{-2/5} ≤ x_0^{-2/5} / 2^k` under the spacing `x_0 ≥ 20`, `x_{k+1} ≥ e^{x_k}`. -/
lemma rpow_neg_two_fifths_le_geom {xp : ℕ → ℝ} (h0 : 20 ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) (k : ℕ) :
    xp k ^ (-(2 / 5 : ℝ)) ≤ xp 0 ^ (-(2 / 5 : ℝ)) * (1 / 2) ^ k := by
  have hge : ∀ k, 20 ≤ xp k := by
    intro k
    induction k with
    | zero => exact h0
    | succ n ih =>
      have := hsp n
      have := Real.add_one_le_exp (xp n)
      linarith
  induction k with
  | zero => simp
  | succ n ih =>
    have := rpow_neg_two_fifths_succ_le (hge n) (hsp n)
    rw [pow_succ]
    nlinarith

/-- **(18)**: if `|α_k| ≤ 2`, `x⁺_0 ≥ e^{X₀²}` with `X₀² ≥ 400`, and `x⁺_{k+1} ≥ e^{x⁺_k}`, then for
`σ ≥ θ + 2/5`, `∑_k |R̂_k(s)| ≤ |s| e^{-0.39 X₀²}` (and the series converges). -/
theorem norm_tsum_oscHat_le {θ X : ℝ} {α γ xp : ℕ → ℝ} (hα : ∀ k, |α k| ≤ 2)
    (hX : 400 ≤ X ^ 2) (h0 : Real.exp (X ^ 2) ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) {s : ℂ} (hσ : θ + 2 / 5 ≤ s.re) :
    Summable (fun k => ‖oscHat θ (α k) (γ k) (xp k) s‖) ∧
      ∑' k, ‖oscHat θ (α k) (γ k) (xp k) s‖ ≤ ‖s‖ * Real.exp (-(39 / 100) * X ^ 2) := by
  have h3 : 20 ≤ xp 0 := by
    have := Real.add_one_le_exp (X ^ 2); linarith
  have hge : ∀ k, 1 ≤ xp k := by
    intro k
    induction k with
    | zero => linarith
    | succ n ih =>
      have := hsp n; have := Real.add_one_le_exp (xp n); linarith
  set c := xp 0 ^ (-(2 / 5 : ℝ))
  have hbound : ∀ k, ‖oscHat θ (α k) (γ k) (xp k) s‖ ≤ 5 * ‖s‖ * c * (1 / 2) ^ k := by
    intro k
    have := norm_oscHat_le_of_re (γ := γ k) (hge k) (hα k) hσ
    have hg := rpow_neg_two_fifths_le_geom h3 hsp k
    calc _ ≤ 5 * ‖s‖ * xp k ^ (-(2 / 5 : ℝ)) := this
      _ ≤ 5 * ‖s‖ * (c * (1 / 2) ^ k) := by gcongr
      _ = _ := by ring
  have hgeom : Summable (fun k : ℕ => 5 * ‖s‖ * c * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_two).mul_left _
  have hsum : Summable (fun k => ‖oscHat θ (α k) (γ k) (xp k) s‖) :=
    hgeom.of_nonneg_of_le (fun k => norm_nonneg _) hbound
  refine ⟨hsum, ?_⟩
  have htsum : ∑' k : ℕ, 5 * ‖s‖ * c * (1 / 2 : ℝ) ^ k = 10 * ‖s‖ * c := by
    rw [tsum_mul_left, tsum_geometric_two]; ring
  have hle := hsum.tsum_le_tsum hbound hgeom
  rw [htsum] at hle
  refine hle.trans ?_
  -- `10 x_0^{-2/5} ≤ e^{-0.39 X²}`
  have hx0 : 0 < xp 0 := by linarith
  have hc : c ≤ Real.exp (-(2 / 5) * X ^ 2) := by
    have : c ≤ (Real.exp (X ^ 2)) ^ (-(2 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h0 (by norm_num)
    rw [← Real.exp_mul] at this
    calc c ≤ Real.exp (X ^ 2 * (-(2 / 5 : ℝ))) := this
      _ = Real.exp (-(2 / 5) * X ^ 2) := by ring_nf
  have h10 : 10 * Real.exp (-(2 / 5) * X ^ 2) ≤ Real.exp (-(39 / 100) * X ^ 2) := by
    have e : Real.exp (-(39 / 100) * X ^ 2) =
        Real.exp (X ^ 2 / 100) * Real.exp (-(2 / 5) * X ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h4 : (4 : ℝ) ≤ X ^ 2 / 100 := by linarith
    have := Real.add_one_le_exp (X ^ 2 / 100)
    have h5 : Real.exp 4 ≤ Real.exp (X ^ 2 / 100) := Real.exp_le_exp.mpr h4
    have h6 : (10 : ℝ) ≤ Real.exp 4 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
      rw [← Real.exp_nat_mul] at this; norm_num at this ⊢; linarith
    linarith
  have hsn := norm_nonneg s
  calc 10 * ‖s‖ * c ≤ ‖s‖ * (10 * Real.exp (-(2 / 5) * X ^ 2)) := by nlinarith
    _ ≤ ‖s‖ * Real.exp (-(39 / 100) * X ^ 2) := mul_le_mul_of_nonneg_left h10 hsn

end DesignedZero

end
