module

public import Mathlib

/-!
# The Riemann zeta function on `(1, ∞)` as a real series

For real `s > 1` we write `zetaR s = ∑_{n ≥ 1} n^{-s}` and
`zetaDR s = ∑_{n ≥ 1} log n · n^{-s}`, and prove

* `riemannZeta s = zetaR s` and `deriv riemannZeta s = -zetaDR s` (Mathlib's `riemannZeta`);
* tail bounds `F(N+1) ≤ ∑_{n > N} f(n) ≤ F(N)` for a decreasing `f` with `F' = -f`, applied to
  `f(x) = x^{-s}` and `f(x) = log x · x^{-s}`;
* `zetaR` is continuous and strictly decreasing on `(1, ∞)`.
-/

@[expose] public section

namespace BSCert.Consts

open Real Filter Topology Finset

/-! ## Generic tail bounds -/

lemma step_bounds {f F : ℝ → ℝ} {a : ℝ} (hd : ∀ x, a ≤ x → HasDerivAt F (-f x) x)
    (hanti : AntitoneOn f (Set.Ici a)) {x : ℝ} (hx : a ≤ x) :
    f (x + 1) ≤ F x - F (x + 1) ∧ F (x + 1) - F (x + 2) ≤ f (x + 1) := by
  have hcont : ∀ u v : ℝ, a ≤ u → ContinuousOn F (Set.Icc u v) := fun u v hu y hy =>
    (hd y (le_trans hu hy.1)).continuousAt.continuousWithinAt
  constructor
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope F (fun y => -f y) (by linarith : x < x + 1)
      (hcont _ _ hx) (fun y hy => hd y (by linarith [hy.1]))
    have h1 : f (x + 1) ≤ f c := hanti (by simp; linarith [hc.1]) (by simp; linarith) hc.2.le
    have : f c = F x - F (x + 1) := by
      have e : (x + 1 - x) = 1 := by ring
      rw [e, div_one] at hc'; linarith
    linarith
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope F (fun y => -f y)
      (by linarith : x + 1 < x + 2) (hcont _ _ (by linarith))
      (fun y hy => hd y (by linarith [hy.1]))
    have h1 : f c ≤ f (x + 1) := hanti (by simp; linarith) (by simp; linarith [hc.1]) hc.1.le
    have : f c = F (x + 1) - F (x + 2) := by
      have e : (x + 2 - (x + 1)) = 1 := by ring
      rw [e, div_one] at hc'; linarith
    linarith

lemma le_add_nat {a : ℝ} (k : ℕ) : a ≤ a + k := by
  have := k.cast_nonneg (α := ℝ); linarith

lemma le_add_nat_add_one {a : ℝ} (k : ℕ) : a ≤ a + k + 1 := by
  have := k.cast_nonneg (α := ℝ); linarith

/-- Upper tail bound: `∑_{k ≥ 0} f(a+k+1) ≤ F(a)`. -/
lemma tail_le {f F : ℝ → ℝ} {a : ℝ} (hd : ∀ x, a ≤ x → HasDerivAt F (-f x) x)
    (hanti : AntitoneOn f (Set.Ici a)) (hnn : ∀ x, a ≤ x → 0 ≤ f x)
    (hF : ∀ x, a ≤ x → 0 ≤ F x) :
    ∑' k : ℕ, f (a + k + 1) ≤ F a := by
  apply Real.tsum_le_of_sum_range_le (fun k => hnn _ (le_add_nat_add_one _))
  intro M
  have key : ∀ M : ℕ, ∑ k ∈ range M, f (a + k + 1) ≤ F a - F (a + M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have := (step_bounds hd hanti (x := a + M) (le_add_nat _)).1
      push_cast
      have e : a + M + 1 = a + (M + 1) := by ring
      rw [e] at this ⊢
      linarith
  have := hF (a + M) (le_add_nat _)
  linarith [key M]

/-- Lower tail bound: `F(a+1) ≤ ∑_{k ≥ 0} f(a+k+1)`. -/
lemma le_tail {f F : ℝ → ℝ} {a : ℝ} (hd : ∀ x, a ≤ x → HasDerivAt F (-f x) x)
    (hanti : AntitoneOn f (Set.Ici a)) (hnn : ∀ x, a ≤ x → 0 ≤ f x)
    (hs : Summable fun k : ℕ => f (a + k + 1)) (hlim : Tendsto F atTop (𝓝 0)) :
    F (a + 1) ≤ ∑' k : ℕ, f (a + k + 1) := by
  have key : ∀ M : ℕ, F (a + 1) - F (a + M + 1) ≤ ∑ k ∈ range M, f (a + k + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have := (step_bounds hd hanti (x := a + M) (le_add_nat _)).2
      push_cast
      have e : a + M + 2 = a + (M + 1) + 1 := by ring
      rw [e] at this
      linarith
  have hle : ∀ M : ℕ, F (a + 1) - F (a + M + 1) ≤ ∑' k : ℕ, f (a + k + 1) := fun M =>
    le_trans (key M) (hs.sum_le_tsum _ (fun k _ => hnn _ (le_add_nat_add_one _)))
  have ht : Tendsto (fun M : ℕ => F (a + 1) - F (a + M + 1)) atTop (𝓝 (F (a + 1) - 0)) := by
    apply tendsto_const_nhds.sub
    apply hlim.comp
    apply tendsto_atTop_add_const_right
    apply tendsto_atTop_add_const_left
    exact tendsto_natCast_atTop_atTop
  rw [sub_zero] at ht
  exact le_of_tendsto' ht hle

/-! ## The two series -/

/-- `ζ(s) = ∑_{n ≥ 1} n^{-s}` for real `s > 1`. -/
noncomputable def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s)

/-- `-ζ'(s) = ∑_{n ≥ 1} log n · n^{-s}` for real `s > 1`. -/
noncomputable def zetaDR (s : ℝ) : ℝ := ∑' n : ℕ, Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s)

lemma summable_zeta_terms {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s) := by
  have h := (Real.summable_nat_rpow (p := -s)).mpr (by linarith)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

lemma summable_zetaD_terms {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s) := by
  set ε := (s - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hsum := (summable_zeta_terms (s := s - ε) (by rw [hε]; linarith)).mul_left (1 / ε)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · have h1 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)])
    positivity
  · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hl := Real.log_le_rpow_div hpos.le hε0
    have e : ((n : ℝ) + 1) ^ (-(s - ε)) = ((n : ℝ) + 1) ^ ε * ((n : ℝ) + 1) ^ (-s) := by
      rw [← Real.rpow_add hpos]; ring_nf
    rw [e]
    have := Real.rpow_nonneg hpos.le (-s)
    calc Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s)
        ≤ (((n : ℝ) + 1) ^ ε / ε) * ((n : ℝ) + 1) ^ (-s) := by gcongr
      _ = 1 / ε * (((n : ℝ) + 1) ^ ε * ((n : ℝ) + 1) ^ (-s)) := by ring

/-- `riemannZeta s = zetaR s` for real `s > 1`. -/
theorem riemannZeta_eq_zetaR {s : ℝ} (hs : 1 < s) : riemannZeta (s : ℂ) = (zetaR s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), zetaR,
    Complex.ofReal_tsum]
  congr 1
  funext n
  have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hpos, Complex.ofReal_inv, Complex.ofReal_cpow hpos, one_div]
  push_cast; rfl

/-! ## Tail bounds for the two series -/

lemma zeta_hasDeriv {s : ℝ} (hs : 1 < s) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ (1 - s) / (s - 1)) (-(x ^ (-s))) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x) (p := 1 - s) (Or.inl hx.ne')).div_const (s - 1)
  convert h using 1
  have hs1 : s - 1 ≠ 0 := by linarith
  field_simp
  ring_nf

lemma zeta_anti {s : ℝ} (hs : 1 < s) : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici 1) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (by simp at hx; linarith) hxy (by linarith)

lemma zetaR_split {s : ℝ} (hs : 1 < s) (N : ℕ) :
    zetaR s = ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-s)
      + ∑' k : ℕ, ((N : ℝ) + k + 1) ^ (-s) := by
  rw [zetaR, ← (summable_zeta_terms hs).sum_add_tsum_nat_add N]
  congr 1
  refine tsum_congr (fun k => ?_)
  push_cast; ring_nf

lemma zetaR_tail_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ((N : ℝ) + k + 1) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine tail_le (f := fun x : ℝ => x ^ (-s)) (F := fun y : ℝ => y ^ (1 - s) / (s - 1))
    (a := (N : ℝ)) (fun x hx => zeta_hasDeriv hs (by linarith)) ?_ ?_ ?_
  · exact (zeta_anti hs).mono (fun x hx => by simp at hx ⊢; linarith)
  · intro x hx; exact Real.rpow_nonneg (by linarith) _
  · intro x hx
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (1 - s)
    have : (0 : ℝ) < s - 1 := by linarith
    positivity

lemma zetaR_tail_ge {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ (1 - s) / (s - 1) ≤ ∑' k : ℕ, ((N : ℝ) + k + 1) ^ (-s) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine le_tail (f := fun x : ℝ => x ^ (-s)) (F := fun y : ℝ => y ^ (1 - s) / (s - 1))
    (a := (N : ℝ)) (fun x hx => zeta_hasDeriv hs (by linarith)) ?_ ?_ ?_ ?_
  · exact (zeta_anti hs).mono (fun x hx => by simp at hx ⊢; linarith)
  · intro x hx; exact Real.rpow_nonneg (by linarith) _
  · have := (summable_nat_add_iff N).mpr (summable_zeta_terms hs)
    refine this.congr (fun k => ?_)
    push_cast; ring_nf
  · have h := (tendsto_rpow_neg_atTop (y := s - 1) (by linarith)).div_const (s - 1)
    rw [zero_div] at h
    refine h.congr' (Eventually.of_forall (fun y => ?_))
    simp only
    ring_nf

/-! ### `log x · x^{-s}` -/

/-- An antiderivative of `-log x · x^{-s}`. -/
noncomputable def zetaDF (s x : ℝ) : ℝ := x ^ (1 - s) * (Real.log x / (s - 1) + 1 / (s - 1) ^ 2)

lemma zetaD_hasDeriv {s : ℝ} (hs : 1 < s) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaDF s) (-(Real.log x * x ^ (-s))) x := by
  have h1 := Real.hasDerivAt_rpow_const (x := x) (p := 1 - s) (Or.inl hx.ne')
  have h2 := ((Real.hasDerivAt_log hx.ne').div_const (s - 1)).add_const (1 / (s - 1) ^ 2)
  have h := h1.mul h2
  unfold zetaDF
  convert h using 1
  have hs1 : s - 1 ≠ 0 := by linarith
  have e : x ^ (1 - s - 1) = x ^ (-s) := by ring_nf
  have e2 : x ^ (1 - s) = x * x ^ (-s) := by
    rw [show 1 - s = 1 + -s by ring, Real.rpow_add hx, Real.rpow_one]
  rw [e, e2]
  field_simp
  ring

lemma zetaD_anti {s : ℝ} (hs : 1 / Real.log 2 ≤ s) :
    AntitoneOn (fun x : ℝ => Real.log x * x ^ (-s)) (Set.Ici 2) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  set t := y / x with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hx0]; linarith
  have hyt : y = x * t := by rw [ht]; field_simp
  have ht0 : 0 < t := by linarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hslx : 1 ≤ s * Real.log x := by
    rw [div_le_iff₀ hl2] at hs; nlinarith
  -- `t^s ≥ 1 + s log t`
  have hts : 1 + s * Real.log t ≤ t ^ s := by
    rw [Real.rpow_def_of_pos ht0]
    have := Real.add_one_le_exp (Real.log t * s); linarith
  have key : Real.log x + Real.log t ≤ Real.log x * t ^ s := by
    have h0 : 0 ≤ Real.log x := by linarith
    nlinarith
  simp only
  rw [hyt, Real.log_mul hx0.ne' ht0.ne', Real.mul_rpow hx0.le ht0.le]
  have htsp : 0 < t ^ s := Real.rpow_pos_of_pos ht0 s
  have e : t ^ (-s) = (t ^ s)⁻¹ := Real.rpow_neg ht0.le s
  rw [e]
  have hxs : 0 < x ^ (-s) := Real.rpow_pos_of_pos hx0 _
  calc (Real.log x + Real.log t) * (x ^ (-s) * (t ^ s)⁻¹)
      = x ^ (-s) * ((Real.log x + Real.log t) / t ^ s) := by ring
    _ ≤ x ^ (-s) * Real.log x := by
        gcongr
        rw [div_le_iff₀ htsp]; linarith
    _ = Real.log x * x ^ (-s) := by ring

lemma zetaDR_split {s : ℝ} (hs : 1 < s) (N : ℕ) :
    zetaDR s = ∑ n ∈ range N, Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s)
      + ∑' k : ℕ, Real.log ((N : ℝ) + k + 1) * ((N : ℝ) + k + 1) ^ (-s) := by
  rw [zetaDR, ← (summable_zetaD_terms hs).sum_add_tsum_nat_add N]
  congr 1
  refine tsum_congr (fun k => ?_)
  push_cast; ring_nf

lemma zetaDR_tail_le {s : ℝ} (hs : 1 < s) (hs2 : 1 / Real.log 2 ≤ s) {N : ℕ} (hN : 2 ≤ N) :
    ∑' k : ℕ, Real.log ((N : ℝ) + k + 1) * ((N : ℝ) + k + 1) ^ (-s) ≤ zetaDF s N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  refine tail_le (f := fun x : ℝ => Real.log x * x ^ (-s)) (F := zetaDF s)
    (a := (N : ℝ)) (fun x hx => zetaD_hasDeriv hs (by linarith)) ?_ ?_ ?_
  · exact (zetaD_anti hs2).mono (fun x hx => by simp at hx ⊢; linarith)
  · intro x hx
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (-s)
    positivity
  · intro x hx
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (1 - s)
    have : (0 : ℝ) < s - 1 := by linarith
    unfold zetaDF
    positivity

/-! ## `-ζ'(s)` -/

/-- `deriv riemannZeta s = -zetaDR s` for real `s > 1`. -/
theorem deriv_riemannZeta_eq {s : ℝ} (hs : 1 < s) :
    deriv riemannZeta (s : ℂ) = -((zetaDR s : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  have hev : riemannZeta =ᶠ[𝓝 (s : ℂ)] LSeries 1 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [hev.deriv_eq, LSeries_deriv (by rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hre)]
  congr 1
  rw [LSeries, zetaDR, Complex.ofReal_tsum, tsum_eq_zero_add']
  · simp only [LSeries.term_zero, zero_add]
    refine tsum_congr (fun n => ?_)
    rw [LSeries.term_of_ne_zero (by omega)]
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [Complex.ofReal_mul, Real.rpow_neg hpos, Complex.ofReal_inv, Complex.ofReal_cpow hpos,
      Complex.ofReal_log hpos]
    push_cast
    ring
  · -- summability of the shifted series
    have h := (summable_zetaD_terms hs)
    have h' : Summable fun n : ℕ => (((Real.log ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s) : ℝ)) : ℂ) :=
      Complex.ofRealCLM.summable h
    refine h'.congr (fun n => ?_)
    rw [LSeries.term_of_ne_zero (by omega)]
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    simp only [LSeries.logMul, Pi.one_apply, mul_one]
    rw [Complex.ofReal_mul, Real.rpow_neg hpos, Complex.ofReal_inv, Complex.ofReal_cpow hpos,
      Complex.ofReal_log hpos]
    push_cast
    ring

/-! ## `zetaR` is continuous and strictly decreasing on `(1, ∞)` -/

lemma zetaR_strictAntiOn : StrictAntiOn zetaR (Set.Ioi 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold zetaR
  apply Summable.tsum_lt_tsum (i := 1)
  · intro n
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  · exact summable_zeta_terms hb
  · exact summable_zeta_terms ha

lemma zetaR_continuousOn : ContinuousOn zetaR (Set.Ioi 1) := by
  intro s hs
  have hs' : (1 : ℝ) < s := hs
  have hc : ContinuousAt (fun t : ℝ => (riemannZeta (t : ℂ)).re) s := by
    apply Complex.continuous_re.continuousAt.comp
    apply ContinuousAt.comp (g := riemannZeta)
    · exact (differentiableAt_riemannZeta (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)).continuousAt
    · exact Complex.continuous_ofReal.continuousAt
  have hev : (fun t : ℝ => (riemannZeta (t : ℂ)).re) =ᶠ[𝓝 s] zetaR := by
    filter_upwards [Ioi_mem_nhds hs'] with t ht
    rw [riemannZeta_eq_zetaR ht, Complex.ofReal_re]
  exact (hc.congr hev).continuousWithinAt

end BSCert.Consts
