module

public import RequestProject.Beurling.BaseRange.EdgeIdentity

/-!
# §7.2: the split `MA[ℙ] = f₀ + f₁` and the rational half of Lemma 7.3(c)

§7.2 splits `MA[ℙ] = f₀ + f₁` with `f₀(q) = MA_{κq}[1_{t ≥ X₀} dt/log t](q)`, so that
`|f₁(q)| ≤ η_H(q) f₀(q) ≤ η_H(q)/log q` for `q ≥ X₀`, and puts
`μ₁ = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})`, with the sharp rational operator
`K^sh_ℚ h(x) = ∑_{m ≥ 2} m⁻¹ 1[P⁺(m) ≤ x/m] h(x/m)`.

* `f0`, `f1`, `KshQ` : the paper's `f₀`, `f₁` and `K^sh_ℚ(h 1_{[X₀,∞)})`;
* `f0_le`, `abs_f1_le` : `f₀(q) ≤ 1/log q` and `|f₁(q)| ≤ (log q)^{-3} f₀(q)` for `q ≥ X₀`,
  from (84);
* `sum_inv_mul_log_le` : `∑_{2 ≤ m ≤ M} 1/(m log(x/m)) ≤ log log x - log log(x/M)` when
  `x/M ≥ e` (the integrand `1/(t log(x/t))` is decreasing on `[1, x/e]`);
* `KshQ_f1_le` : the rational half of the first bound of Lemma 7.3(c):
  `|K^sh_ℚ(f₁ 1_{[X₀,∞)})(x)| ≤ Λ⁻³ log v` (`v = log x/Λ`), so at most half of
  `2Λ⁻³(log v + 1.01)`.

The realised half `K_pt(f₁ 1_{[X₀,∞)})` needs the realised operator, which is not formalized in
this repository (see `Margin.lean`).
-/

@[expose] public section

open Real MeasureTheory Set

namespace BaseRange

/-- `f₀(q) = MA_{κq}[1_{t ≥ X₀} dt/log t](q) = ∫_{max(q,X₀)}^{max((1+κ)q,X₀)} dt/log t/(κq)`. -/
noncomputable def f0 (X0 : ℕ) (κ q : ℝ) : ℝ := liI (max q X0) (max ((1 + κ) * q) X0) / (κ * q)

/-- `f₁ = MA[ℙ] - f₀`. -/
noncomputable def f1 (X0 : ℕ) (κ q : ℝ) : ℝ := MAP X0 κ q - f0 X0 κ q

open Classical in
/-- `K^sh_ℚ(h 1_{[X₀,∞)})(x) = ∑_{2 ≤ m ≤ x/X₀} m⁻¹ 1[P⁺(m) ≤ x/m] h(x/m)`. -/
noncomputable def KshQ (X0 : ℕ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 ⌊x / X0⌋₊, if (Pplus m : ℝ) ≤ x / m then h (x / m) / m else 0

lemma f0_eq {X0 : ℕ} {κ q : ℝ} (hκ : 0 ≤ κ) (hq : (X0 : ℝ) ≤ q) :
    f0 X0 κ q = liI q ((1 + κ) * q) / (κ * q) := by
  have hq0 : 0 ≤ q := le_trans (Nat.cast_nonneg _) hq
  unfold f0
  rw [max_eq_left hq, max_eq_left (by nlinarith)]

/-- `f₀(q) ≤ 1/log q` for `q ≥ X₀ > 1`. -/
lemma f0_le {X0 : ℕ} {κ q : ℝ} (hX : 1 < (X0 : ℝ)) (hκ : 0 < κ) (hq : (X0 : ℝ) ≤ q) :
    f0 X0 κ q ≤ 1 / Real.log q := by
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  rw [f0_eq hκ.le hq]
  have h := liI_le hq1 (by nlinarith : q ≤ (1 + κ) * q)
  have e : (1 + κ) * q - q = κ * q := by ring
  rw [e] at h
  rw [div_le_iff₀ (mul_pos hκ hq0)]
  calc liI q ((1 + κ) * q) ≤ κ * q / Real.log q := h
    _ = 1 / Real.log q * (κ * q) := by ring

lemma f0_nonneg {X0 : ℕ} {κ q : ℝ} (hX : 1 < (X0 : ℝ)) (hκ : 0 < κ) (hq : (X0 : ℝ) ≤ q) :
    0 ≤ f0 X0 κ q := by
  have hq1 : 1 < q := by linarith
  rw [f0_eq hκ.le hq]
  exact div_nonneg (liI_pos hq1 (by nlinarith)).le (by positivity)

/-- `|f₁(q)| ≤ (log q)^{-3} f₀(q)` for `q ≥ X₀` (from (84); §7.2). -/
theorem abs_f1_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq : (X0 : ℝ) ≤ q) :
    |f1 X0 (Construction.kappaParam X0) q| ≤
      Real.log q ^ (-3 : ℤ) * f0 X0 (Construction.kappaParam X0) q := by
  set κ := Construction.kappaParam X0
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hadm := window_admissible hX hq
  have hX2 : (2 : ℝ) ≤ X0 := by
    have h2 : Real.exp (10 ^ 8) ≤ X0 := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X0)]; exact Real.exp_le_exp.mpr hX
    linarith [Real.add_one_le_exp (10 ^ 8 : ℝ)]
  have he := hH q q ((1 + κ) * q) hq hadm
  have hli := liI_pos hq1 (by nlinarith : q < (1 + κ) * q)
  have hκq := mul_pos hκ0 hq0
  unfold f1
  rw [MAP_eq hq, f0_eq hκ0.le hq]
  unfold relErr at he
  have e : (primeCount q ((1 + κ) * q) : ℝ) / (κ * q) - liI q ((1 + κ) * q) / (κ * q) =
      ((primeCount q ((1 + κ) * q) : ℝ) / liI q ((1 + κ) * q) - 1) *
        (liI q ((1 + κ) * q) / (κ * q)) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (div_nonneg hli.le hκq.le)]
  exact mul_le_mul_of_nonneg_right he (div_nonneg hli.le hκq.le)

/-! ### The cofactor sum `∑ 1/(m log(x/m))` -/

/-- `t ↦ 1/(t log(x/t))` is antitone on `[1, x/e]`. -/
lemma antitoneOn_inv_mul_log {x : ℝ} (hx : 0 < x) :
    AntitoneOn (fun t => 1 / (t * Real.log (x / t))) (Icc 1 (x / Real.exp 1)) := by
  intro s hs t ht hst
  simp only
  have hs0 : 0 < s := by linarith [hs.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hlog : ∀ u ∈ Icc 1 (x / Real.exp 1), 1 ≤ Real.log (x / u) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [Real.le_log_iff_exp_le (div_pos hx hu0), le_div_iff₀ hu0]
    have := hu.2; rw [le_div_iff₀ (Real.exp_pos 1)] at this; linarith
  have hls := hlog s hs
  have hlt := hlog t ht
  apply one_div_le_one_div_of_le (by positivity)
  -- `s log(x/s) ≤ t log(x/t)`: `t log(x/t) - s log(x/s) = (t - s) log(x/t) - s log(t/s)`
  have e : t * Real.log (x / t) - s * Real.log (x / s) =
      (t - s) * Real.log (x / t) - s * Real.log (t / s) := by
    rw [Real.log_div hx.ne' ht0.ne', Real.log_div hx.ne' hs0.ne',
      Real.log_div ht0.ne' hs0.ne']
    ring
  have h1 : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
  have h2 : s * Real.log (t / s) ≤ t - s := by
    have := mul_le_mul_of_nonneg_left h1 hs0.le
    have e2 : s * (t / s - 1) = t - s := by field_simp
    linarith
  have h3 : t - s ≤ (t - s) * Real.log (x / t) := by nlinarith
  linarith

/-- `∫_1^M dt/(t log(x/t)) = log log x - log log(x/M)` for `1 ≤ M < x`. -/
lemma integral_inv_mul_log {x M : ℝ} (hM : 1 ≤ M) (hMx : M < x) :
    ∫ t in (1 : ℝ)..M, 1 / (t * Real.log (x / t)) =
      Real.log (Real.log x) - Real.log (Real.log (x / M)) := by
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ Set.uIcc (1 : ℝ) M, 0 < t ∧ 0 < Real.log (x / t) := by
    intro t ht
    rw [Set.uIcc_of_le hM] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨ht0, Real.log_pos ?_⟩
    rw [lt_div_iff₀ ht0, one_mul]; linarith [ht.2]
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) M,
      HasDerivAt (fun t => -Real.log (Real.log (x / t))) (1 / (t * Real.log (x / t))) t := by
    intro t ht
    obtain ⟨ht0, hl⟩ := hpos t ht
    have h1 := (hasDerivAt_inv ht0.ne').const_mul x
    have h1' : HasDerivAt (fun t => x / t) (x * -(t ^ 2)⁻¹) t := by
      simpa [div_eq_mul_inv] using h1
    have h2 := ((h1'.log (div_pos hx0 ht0).ne').log hl.ne').neg
    convert h2 using 1
    field_simp
  have hcont : ContinuousOn (fun t => 1 / (t * Real.log (x / t))) (Set.uIcc (1 : ℝ) M) := by
    intro t ht
    obtain ⟨ht0, hl⟩ := hpos t ht
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div (continuousAt_id.mul
      ((continuousAt_const.div continuousAt_id ht0.ne').log (div_pos hx0 ht0).ne'))
      (mul_pos ht0 hl).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [div_one]
  ring

/-- `∑_{2 ≤ m ≤ M} 1/(m log(x/m)) ≤ log log x - log log(x/M)` for `M ≥ 1` with `x/M ≥ e`. -/
theorem sum_inv_mul_log_le {x : ℝ} {M : ℕ} (hM : 1 ≤ M) (hxM : Real.exp 1 ≤ x / M) :
    ∑ m ∈ Finset.Icc 2 M, 1 / ((m : ℝ) * Real.log (x / m)) ≤
      Real.log (Real.log x) - Real.log (Real.log (x / M)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := by
    have := Real.exp_pos 1
    have : 0 < x / M := by linarith
    exact (div_pos_iff_of_pos_right hM0).mp this
  have hMx : (M : ℝ) ≤ x / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]; rw [le_div_iff₀ hM0] at hxM; linarith
  have hMlt : (M : ℝ) < x := by
    have : x / Real.exp 1 < x := div_lt_self hx0 (by linarith [Real.add_one_le_exp (1 : ℝ)])
    linarith
  set g : ℝ → ℝ := fun t => 1 / (t * Real.log (x / t)) with hg
  have hanti := antitoneOn_inv_mul_log hx0
  have hint : ∀ m : ℕ, 2 ≤ m → m ≤ M →
      g m ≤ ∫ t in ((m : ℝ) - 1)..m, g t := by
    intro m hm2 hmM
    have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
    have hsub : Icc ((m : ℝ) - 1) m ⊆ Icc 1 (x / Real.exp 1) := by
      intro t ht; exact ⟨hm1.trans ht.1, ht.2.trans (hmM'.trans hMx)⟩
    have hc : g m = ∫ _ in ((m : ℝ) - 1)..m, g m := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hc]
    have hgi : IntervalIntegrable g volume ((m : ℝ) - 1) m := by
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      exact hanti.mono hsub
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hgi
    intro t ht
    exact hanti (hsub ht) (hsub ⟨by linarith, le_rfl⟩) ht.2
  -- telescoping the cells `[m-1, m]`
  have hsum : ∑ m ∈ Finset.Icc 2 M, g m ≤ ∫ t in (1 : ℝ)..M, g t := by
    rcases Nat.lt_or_ge M 2 with hM2 | hM2
    · have : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
      have hM1 : M = 1 := by omega
      subst hM1; simp
    have hIcc : Finset.Icc 2 M = Finset.Ico 2 (M + 1) := rfl
    have hcells : ∑ m ∈ Finset.Ico 1 M, ∫ t in ((m : ℕ) : ℝ)..((m + 1 : ℕ) : ℝ), g t =
        ∫ t in ((1 : ℕ) : ℝ)..((M : ℕ) : ℝ), g t := by
      apply intervalIntegral.sum_integral_adjacent_intervals_Ico (by omega)
      intro k hk
      have hk1 : 1 ≤ k := hk.1
      have hkM : k < M := hk.2
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkM' : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hkM
      have hsub : Icc (k : ℝ) ((k + 1 : ℕ) : ℝ) ⊆ Icc 1 (x / Real.exp 1) := by
        intro t ht; exact ⟨hk1'.trans ht.1, ht.2.trans (hkM'.trans hMx)⟩
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (by push_cast; linarith)]
      exact hanti.mono hsub
    push_cast at hcells
    rw [← hcells]
    have hshift : ∑ m ∈ Finset.Icc 2 M, g m = ∑ k ∈ Finset.Ico 1 M, g ((k + 1 : ℕ) : ℝ) := by
      rw [hIcc]
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr (by congr 1)
      intro k _
      congr 2; ring
    rw [hshift]
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkM : k < M := (Finset.mem_Ico.mp hk).2
    have := hint (k + 1) (by omega) (by omega)
    push_cast at this ⊢
    simpa using this
  have hI := integral_inv_mul_log (by exact_mod_cast hM) hMlt
  rw [hI] at hsum
  exact hsum

/-! ### The rational half of the first bound of Lemma 7.3(c) -/

/-- **Lemma 7.3(c), rational half of the first bound**: for `x ≥ X₀` with `log X₀ ≥ 10⁸`,
`|K^sh_ℚ(f₁ 1_{[X₀,∞)})(x)| ≤ Λ⁻³ log v`, `Λ = log X₀`, `v = log x/Λ`. -/
theorem KshQ_f1_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) :
    |KshQ X0 (f1 X0 (Construction.kappaParam X0)) x| ≤
      1 / Real.log X0 ^ 3 * Real.log (Real.log x / Real.log X0) := by
  set κ := Construction.kappaParam X0
  set Λ := Real.log X0 with hΛdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hx0 : 0 < x := by linarith
  set M := ⌊x / X0⌋₊ with hMdef
  -- each component: `|f₁(x/m)|/m ≤ Λ⁻³ /(m log(x/m))`
  have hcomp : ∀ m ∈ Finset.Icc 2 M,
      |(if (Pplus m : ℝ) ≤ x / m then f1 X0 κ (x / m) / m else 0)| ≤
        1 / Λ ^ 3 * (1 / ((m : ℝ) * Real.log (x / m))) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hq : (X0 : ℝ) ≤ x / m := by
      rw [le_div_iff₀ hm0]
      have : (m : ℝ) ≤ x / X0 := (Nat.cast_le.mpr hmM).trans (Nat.floor_le (by positivity))
      rw [le_div_iff₀ hX0] at this; linarith
    have hLq : Λ ≤ Real.log (x / m) := Real.log_le_log hX0 hq
    have hLq0 : 0 < Real.log (x / m) := by linarith
    have hb : 0 ≤ 1 / Λ ^ 3 * (1 / ((m : ℝ) * Real.log (x / m))) := by positivity
    split_ifs
    · rw [abs_div, abs_of_pos hm0]
      have h1 := abs_f1_le hX hH hq
      have h2 := f0_le hX1 hκ0 hq
      have h3 : Real.log (x / m) ^ (-3 : ℤ) ≤ 1 / Λ ^ 3 := by
        rw [zpow_neg, zpow_ofNat, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hΛ0.le hLq 3)
      have h0 := f0_nonneg hX1 hκ0 hq
      have h4 : |f1 X0 κ (x / m)| ≤ 1 / Λ ^ 3 * (1 / Real.log (x / m)) :=
        h1.trans (mul_le_mul h3 h2 h0 (by positivity))
      rw [div_le_iff₀ hm0]
      calc |f1 X0 κ (x / m)| ≤ 1 / Λ ^ 3 * (1 / Real.log (x / m)) := h4
        _ = 1 / Λ ^ 3 * (1 / ((m : ℝ) * Real.log (x / m))) * m := by field_simp
    · simpa using hb
  unfold KshQ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcomp).trans ?_)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    apply Real.log_nonneg
    rw [le_div_iff₀ hΛ0, one_mul]; exact Real.log_le_log hX0 hx
  have hM1 : 1 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hxM : (X0 : ℝ) ≤ x / M := by
    rw [le_div_iff₀ hM0]
    have : (M : ℝ) ≤ x / X0 := Nat.floor_le (by positivity)
    rw [le_div_iff₀ hX0] at this; linarith
  have hE : Real.exp 1 ≤ (X0 : ℝ) := by
    rw [← Real.exp_log hX0]; exact Real.exp_le_exp.mpr (by linarith)
  refine (sum_inv_mul_log_le hM1 (hE.trans hxM)).trans ?_
  have hlx : 0 < Real.log x := by linarith [Real.log_le_log hX0 hx]
  rw [Real.log_div hlx.ne' hΛ0.ne']
  have : Real.log Λ ≤ Real.log (Real.log (x / M)) :=
    Real.log_le_log hΛ0 (Real.log_le_log hX0 hxM)
  linarith

end BaseRange
