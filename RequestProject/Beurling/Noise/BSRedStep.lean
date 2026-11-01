module

public import RequestProject.Beurling.Noise.BSRedRatio
public import RequestProject.Beurling.Noise.BSRedPS
public import RequestProject.Beurling.Noise.BSRedRec
public import RequestProject.Beurling.Noise.BSRedPhi

/-!
# Theorem 5.6, Steps 5–6: the induction step `Σ(ℓ, u) ≥ 0 ⟹ Ψ(ℓ, u) ≤ G(ℓ, u)`

`BeurlingSystem.bs_step`: let `τ = log t ≥ 10⁸`, `ℓ > 30τ`, `0 ≤ u ≤ U(ℓ)`, `2e^ℓ ≤ Z`, and
assume (HBS) on `[1, Z]`, Lemma 5.3 on `[1, Z]`, and the claim (bs-claim) at every height
`m ∈ [τ, ℓ - log 2]`. If `Σ(ℓ, u) ≥ 0` then `(ℓ/τ) W_t(e^ℓ; e^{ℓ/u}) ≤ G(ℓ, u)`.

The primes are split at `σ = ℓ/u*`: the primes with `σ ≤ ℓ/u*` give `e^{ℓ/u*}`-smooth elements
and are bounded by Lemma 5.3 (the term `T`, Step 6); the others have `w ∈ [w_lo, U(ℓ) - 1/2)`,
where the induction hypothesis applies (`U_shift`), and partial summation with Lemma 5.1(iv)
(`ps_bound`) bounds their contribution by `G(ℓ, u)(M + E₁ + E₂ + E₃)`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral Finset

namespace BSaias

/-- The position of a main prime in the `w` variable. -/
lemma main_window {τ ℓ u σ b : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 ≤ b)
    (hs0 : ℓ / (1 + b) < σ) (hu : u * σ ≤ ℓ) (h2 : 2 * σ ≤ ℓ + τ + Real.log 2) :
    wlo τ ℓ u ≤ (ℓ - σ) / σ ∧ (ℓ - σ) / σ < b := by
  have hσ : 0 < σ := lt_of_le_of_lt (by positivity) hs0
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨max_le ?_ ?_, ?_⟩
  · rw [le_div_iff₀ hσ]; linarith
  · unfold w1
    rw [div_le_div_iff₀ (by linarith) hσ]
    nlinarith
  · rw [div_lt_iff₀ hσ]
    rw [div_lt_iff₀ (by linarith)] at hs0
    linarith

/-- The counting identity: the main primes with `w < x` are the primes of
`(e^{ℓ/(1+x)}, e^{ℓ/(1+w_lo)}]`. -/
lemma main_count {τ ℓ u σ b x : ℝ} (hτ : 0 < τ) (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hla : 0 < wlo τ ℓ u) (hx : wlo τ ℓ u ≤ x) (hxb : x ≤ b) (hσ : 0 < σ) :
    ((ℓ / (1 + b) < σ ∧ u * σ ≤ ℓ ∧ 2 * σ ≤ ℓ + τ + Real.log 2 ∧ σ ≤ ℓ) ∧ (ℓ - σ) / σ < x) ↔
      (σ ≤ ℓ / (1 + wlo τ ℓ u) ∧ ℓ / (1 + x) < σ) := by
  set a := wlo τ ℓ u with ha
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hau : u - 1 ≤ a := le_max_left _ _
  have haw : w1 τ ℓ ≤ a := le_max_right _ _
  have hx0 : 0 < x := lt_of_lt_of_le hla hx
  constructor
  · rintro ⟨⟨hs0, hus, h2, hσℓ⟩, hwx⟩
    have hw := (main_window hτ hℓ (hx.trans hxb |> le_trans hla.le) hs0 hus h2).1
    rw [← ha] at hw
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hσ] at hw
      rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ hσ] at hwx
      rw [div_lt_iff₀ (by linarith)]; linarith
  · rintro ⟨h1, h2⟩
    have h1' : σ * (1 + a) ≤ ℓ := by rwa [le_div_iff₀ (by linarith)] at h1
    have h2' : ℓ < σ * (1 + x) := by rwa [div_lt_iff₀ (by linarith)] at h2
    have hw1 : 1 + w1 τ ℓ = 2 * ℓ / (ℓ + τ + Real.log 2) := one_add_w1 (by linarith)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (by linarith)]; nlinarith
    · nlinarith
    · have : σ * (1 + w1 τ ℓ) ≤ ℓ := by nlinarith
      rw [hw1] at this
      rw [mul_div_assoc', div_le_iff₀ (by linarith)] at this
      nlinarith
    · nlinarith
    · rw [div_lt_iff₀ hσ]; linarith


lemma etaF_nonneg {τ ℓ x : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hx : 0 < x) : 0 ≤ etaF τ ℓ x := by
  have hm0 := red_mOf_pos hℓ hx
  have hd := dpos_nonneg (mOf ℓ x) x
  have hk : 0 ≤ kappa τ := by unfold kappa; linarith
  have hlog : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hu' := u0_nonneg (mOf ℓ x)
  unfold etaF BSCert.Z2.A
  simp only
  have : 0 < 2 + x := by linarith
  positivity

/-- The four terms of `Σ` are non-negative. -/
lemma terms_nonneg {τ ℓ u : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (ha0 : 0 < wlo τ ℓ u)
    (haU : wlo τ ℓ u ≤ Uf τ ℓ) :
    0 ≤ Mterm τ ℓ u (paperCut τ ℓ) + E1term τ ℓ u (paperCut τ ℓ) +
      E2term τ ℓ u (paperCut τ ℓ) + E3term τ ℓ u (paperCut τ ℓ) := by
  set a := wlo τ ℓ u
  have hM0 : 0 ≤ Mterm τ ℓ u (paperCut τ ℓ) := by
    unfold Mterm
    exact integral_nonneg haU fun x hx => div_nonneg (gfun_nonneg _ _ _ _ _)
      (lt_of_lt_of_le ha0 hx.1).le
  have hE10 : 0 ≤ E1term τ ℓ u (paperCut τ ℓ) := by
    unfold E1term; have := gfun_nonneg τ ℓ u (paperCut τ ℓ) a; unfold Kp; positivity
  have hE20 : 0 ≤ E2term τ ℓ u (paperCut τ ℓ) := by
    unfold E2term
    have : 0 ≤ ∫ x in a..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * (1 + x) / x :=
      integral_nonneg haU fun x hx => by
        have := lt_of_lt_of_le ha0 hx.1; have := gfun_nonneg τ ℓ u (paperCut τ ℓ) x
        positivity
    unfold Kp; positivity
  have hE30 : 0 ≤ E3term τ ℓ u (paperCut τ ℓ) := by
    unfold E3term
    have : 0 ≤ ∫ x in a..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * etaF τ ℓ x / x :=
      integral_nonneg haU fun x hx => by
        have h0 := lt_of_lt_of_le ha0 hx.1; have := gfun_nonneg τ ℓ u (paperCut τ ℓ) x
        have := etaF_nonneg hτ hℓ h0
        positivity
    unfold Kp; positivity
  linarith

lemma conv_M {τ ℓ u a b : ℝ} (hℓ : 0 < ℓ) (ha0 : 0 < a) (hab : a ≤ b) (hbU : b ≤ Uf τ ℓ)
    (ha : a = wlo τ ℓ u) (hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ) :
    ∫ x in a..b, Hf τ ℓ x / (1 + x) ≤ Gf τ ℓ u * Mterm τ ℓ u (paperCut τ ℓ) := by
  have hpos : ∀ x ∈ Icc a (Uf τ ℓ), 0 < x := fun x hx => lt_of_lt_of_le ha0 hx.1
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Icc a (Uf τ ℓ)) :=
    continuousOn_const.div continuousOn_id fun x hx => (hpos x hx).ne'
  have hM := integral_le_cut (τ := τ) (u := u) hℓ ha0 hab hbU hcut hcont
    (fun x hx => le_of_lt (by have := hpos x hx; positivity))
  have hI : ∫ x in a..b, Hf τ ℓ x / (1 + x) =
      Gf τ ℓ u * ∫ x in a..b, g0 τ ℓ u x * (1 / x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    simp only
    rw [Hf_eq_G (u := u) hℓ hx0]
    field_simp
  have hMeq : ∫ x in a..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * (1 / x) =
      Mterm τ ℓ u (paperCut τ ℓ) := by
    unfold Mterm; rw [← ha]; congr 1; funext x; ring
  rw [hI, ← hMeq]
  exact mul_le_mul_of_nonneg_left hM (Gf_pos τ ℓ u).le

lemma conv_E1 {τ ℓ u a b : ℝ} (hℓ : 0 < ℓ) (ha0 : 0 < a) (hab : a ≤ b)
    (ha : a = wlo τ ℓ u) (hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ) :
    Kp * Hf τ ℓ a * (1 + a) / ℓ ≤ Gf τ ℓ u * E1term τ ℓ u (paperCut τ ℓ) := by
  unfold E1term
  rw [← ha, gfun_eq_indicator, indicator_of_mem (hcut a ⟨le_rfl, hab⟩),
    Hf_eq_G (u := u) hℓ ha0]
  have := g0_nonneg τ ℓ u a
  have hG := Gf_pos τ ℓ u
  have hK : (0 : ℝ) ≤ Kp := by unfold Kp; norm_num
  have e : Kp * (Gf τ ℓ u * ((1 + a) / a) * g0 τ ℓ u a) * (1 + a) / ℓ =
      Gf τ ℓ u * (Kp * (1 + a) ^ 2 * g0 τ ℓ u a / (a * ℓ)) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hG.le
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ Kp * (1 + a) ^ 2 * g0 τ ℓ u a := by positivity
  linarith

lemma conv_E2 {τ ℓ u a b : ℝ} (hℓ : 0 < ℓ) (ha0 : 0 < a) (hab : a ≤ b) (hbU : b ≤ Uf τ ℓ)
    (ha : a = wlo τ ℓ u) (hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ) :
    Kp / ℓ * ∫ x in a..b, Hf τ ℓ x ≤ Gf τ ℓ u * E2term τ ℓ u (paperCut τ ℓ) := by
  have hpos : ∀ x ∈ Icc a (Uf τ ℓ), 0 < x := fun x hx => lt_of_lt_of_le ha0 hx.1
  have hcont : ContinuousOn (fun x : ℝ => (1 + x) / x) (Icc a (Uf τ ℓ)) :=
    (continuousOn_const.add continuousOn_id).div continuousOn_id fun x hx => (hpos x hx).ne'
  have hE := integral_le_cut (τ := τ) (u := u) hℓ ha0 hab hbU hcut hcont
    (fun x hx => le_of_lt (by have := hpos x hx; positivity))
  have hI : ∫ x in a..b, Hf τ ℓ x = Gf τ ℓ u * ∫ x in a..b, g0 τ ℓ u x * ((1 + x) / x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    simp only
    rw [Hf_eq_G (u := u) hℓ hx0]
    ring
  have hEeq : ∫ x in a..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * ((1 + x) / x) =
      ∫ x in wlo τ ℓ u..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * (1 + x) / x := by
    rw [← ha]; congr 1; funext x; ring
  unfold E2term
  rw [hI, ← hEeq]
  have hG := Gf_pos τ ℓ u
  have hK : (0 : ℝ) < Kp := by unfold Kp; norm_num
  have := mul_le_mul_of_nonneg_left hE (show 0 ≤ Kp / ℓ * Gf τ ℓ u by positivity)
  linarith

lemma conv_E3 {τ ℓ u a b : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (ha0 : 0 < a) (hab : a ≤ b)
    (hbU : b ≤ Uf τ ℓ)
    (ha : a = wlo τ ℓ u) (hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ) :
    2 * Kp / ℓ * ∫ x in a..b, Hf τ ℓ x * etaW τ ℓ x * (1 + x) ≤
      Gf τ ℓ u * E3term τ ℓ u (paperCut τ ℓ) := by
  have hpos : ∀ x ∈ Icc a (Uf τ ℓ), 0 < x := fun x hx => lt_of_lt_of_le ha0 hx.1
  have hcont : ContinuousOn (fun x : ℝ => etaF τ ℓ x / x) (Icc a (Uf τ ℓ)) := by
    have h1 : ContinuousOn (etaF τ ℓ) (Icc a (Uf τ ℓ)) := fun x hx =>
      (continuousAt_etaF hℓ (hpos x hx)).continuousWithinAt
    exact h1.div continuousOn_id fun x hx => (hpos x hx).ne'
  have hE := integral_le_cut (τ := τ) (u := u) hℓ ha0 hab hbU hcut hcont
    (fun x hx => by have := hpos x hx; have := etaF_nonneg hτ hℓ this; positivity)
  have hI : ∫ x in a..b, Hf τ ℓ x * etaW τ ℓ x * (1 + x) =
      Gf τ ℓ u * ℓ * ∫ x in a..b, g0 τ ℓ u x * (etaF τ ℓ x / x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    simp only
    rw [Hf_eq_G (u := u) hℓ hx0]
    unfold etaW mOf'
    field_simp
  have hEeq : ∫ x in a..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * (etaF τ ℓ x / x) =
      ∫ x in wlo τ ℓ u..Uf τ ℓ, gfun τ ℓ u (paperCut τ ℓ) x * etaF τ ℓ x / x := by
    rw [← ha]; congr 1; funext x; ring
  unfold E3term
  rw [hI, ← hEeq]
  have hG := Gf_pos τ ℓ u
  have hK : (0 : ℝ) < Kp := by unfold Kp; norm_num
  have e : 2 * Kp / ℓ * (Gf τ ℓ u * ℓ * ∫ x in a..b, g0 τ ℓ u x * (etaF τ ℓ x / x)) =
      2 * Kp * Gf τ ℓ u * ∫ x in a..b, g0 τ ℓ u x * (etaF τ ℓ x / x) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 * Kp * Gf τ ℓ u by positivity)
  linarith

/-- **Step 5, main part**: partial summation of `ν G(m, w)` over the main primes, divided by
`G(ℓ, u)`, is at most `M + E₁ + E₂ + E₃`. The window is `w ∈ [w_lo, U(ℓ) - 1/2)`; the counting
function hypothesis is Lemma 5.1(iv) in the variable `w`. -/
theorem main_ps {ι : Type*} (s : Finset ι) (wj c : ι → ℝ) {τ ℓ u : ℝ} (hτ : 1 ≤ τ)
    (hℓτ : 30 * τ ≤ ℓ) (hℓ : 3000000000 ≤ ℓ) (hu0 : 0 ≤ u) (huU : u ≤ Uf τ ℓ)
    (hw : ∀ j ∈ s, wlo τ ℓ u ≤ wj j ∧ wj j < Uf τ ℓ - 1 / 2)
    (hR : wlo τ ℓ u ≤ Uf τ ℓ - 1 / 2 → ∀ x ∈ Icc (wlo τ ℓ u) (Uf τ ℓ - 1 / 2),
      |cnt s wj c x - Real.log ((1 + x) / (1 + wlo τ ℓ u))| ≤ Kp * (1 + x) / ℓ) :
    ∑ j ∈ s, c j * Hf τ ℓ (wj j) ≤ Gf τ ℓ u *
      (Mterm τ ℓ u (paperCut τ ℓ) + E1term τ ℓ u (paperCut τ ℓ) + E2term τ ℓ u (paperCut τ ℓ) +
        E3term τ ℓ u (paperCut τ ℓ)) := by
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set a := wlo τ ℓ u with hadef
  set b := Uf τ ℓ - 1 / 2 with hbdef
  have hw1pos : 0 < w1 τ ℓ := red_w1_pos hτ0.le (by have := Real.log_two_lt_d9; linarith)
  have ha0 : 0 < a := lt_of_lt_of_le hw1pos (le_max_right _ _)
  have hU1 : 1 ≤ Uf τ ℓ := le_trans
    (le_u0_of_pow4 (by norm_num) (by norm_num; linarith)) (u0_le_Uf τ ℓ)
  have haU : a ≤ Uf τ ℓ := max_le (by linarith) (by linarith [w1_lt_one hτ0.le hℓ0])
  have hG := Gf_pos τ ℓ u
  by_cases hab : a ≤ b
  swap
  · have hse : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      obtain ⟨h1, h2⟩ := hw j hj
      exact hab (h1.trans h2.le)
    rw [hse, Finset.sum_empty]
    exact mul_nonneg hG.le (terms_nonneg hτ0.le hℓ0 ha0 haU)
  have hps := ps_bound s wj c ha0 hab hℓ0 (by unfold Kp; norm_num)
    hw (hR hab) (Hf τ ℓ) (Hf' τ ℓ) (etaW τ ℓ) (Set.countable_singleton 2)
    (continuousOn_Hf hℓ0 ha0) (fun x hx => hasDerivAt_Hf hℓ0 (lt_of_lt_of_le ha0 hx.1.1.le)
      hx.2) (intervalIntegrable_Hf' hℓ0 ha0 hab)
    (fun x hx => by
      rw [Hf_eq]; exact mul_nonneg (H1_nonneg (lt_of_lt_of_le ha0 hx.1))
        (H2_pos τ ℓ x).le)
    (continuousOn_etaW hℓ0 ha0)
    (fun x hx => Hf_deriv_bound hτ0.le hℓ0 (lt_of_lt_of_le ha0 hx.1.1.le))
  have hcut : ∀ x ∈ Icc a b, x ∈ paperCut τ ℓ := fun x hx =>
    U_shift hτ hℓτ hℓ ((le_max_right _ _).trans hx.1) hx.2
  have hbU : b ≤ Uf τ ℓ := by linarith
  have t1 := conv_M (u := u) hℓ0 ha0 hab hbU hadef hcut
  have t2 := conv_E1 (u := u) hℓ0 ha0 hab hadef hcut
  have t3 := conv_E2 (u := u) hℓ0 ha0 hab hbU hadef hcut
  have t4 := conv_E3 (u := u) hτ0.le hℓ0 ha0 hab hbU hadef hcut
  have e2 : 2 * Kp / ℓ * ∫ x in a..b, Hf τ ℓ x * etaW τ ℓ x * (1 + x) =
      2 * Kp / ℓ * ∫ x in a..b, Hf τ ℓ x * etaW τ ℓ x * (1 + x) := rfl
  linarith

end BSaias

namespace BeurlingSystem

open BSaias

variable (P : BeurlingSystem)

/-- **Lemma 5.1(iv) in the variable `w`**: the counting function of the main primes. -/
lemma main_cnt_bound {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {t ℓ u : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : 30 * Real.log t < ℓ)
    (hu0 : 0 ≤ u) (hZ : 2 * Real.exp ℓ ≤ Z) {x : ℝ}
    (hx : x ∈ Icc (wlo (Real.log t) ℓ u) (Uf (Real.log t) ℓ - 1 / 2)) :
    |cnt ((P.primesLe (2 * Real.exp ℓ)).filter (fun j =>
        ℓ / ustar (Real.log t) ℓ < Real.log (P.p j) ∧ u * Real.log (P.p j) ≤ ℓ ∧
        P.p j ^ 2 ≤ 2 * t * Real.exp ℓ ∧ P.p j ≤ Real.exp ℓ))
      (fun j => (ℓ - Real.log (P.p j)) / Real.log (P.p j)) (fun j => 1 / P.p j) x -
      Real.log ((1 + x) / (1 + wlo (Real.log t) ℓ u))| ≤ Kp * (1 + x) / ℓ := by
  set τ := Real.log t with hτdef
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ3 : 3000000000 ≤ ℓ := by linarith
  have htexp : t = Real.exp τ := (Real.exp_log ht).symm
  set a := wlo τ ℓ u with hadef
  set b := Uf τ ℓ - 1 / 2 with hbdef
  have hus : ustar τ ℓ = 1 + b := by unfold ustar; rw [hbdef]; ring
  obtain ⟨_, hus100, _⟩ := ustar_lemma53 (τ := τ) (by linarith) hℓ.le hℓ3
  have hw1pos : 0 < w1 τ ℓ := red_w1_pos hτ0.le (by have := Real.log_two_lt_d9; linarith)
  have ha0 : 0 < a := lt_of_lt_of_le hw1pos (le_max_right _ _)
  have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
  set X := Real.exp (ℓ / (1 + a)) with hX
  set y := Real.exp (ℓ / (1 + x)) with hy
  have hcnt : cnt ((P.primesLe (2 * Real.exp ℓ)).filter (fun j =>
        ℓ / ustar τ ℓ < Real.log (P.p j) ∧ u * Real.log (P.p j) ≤ ℓ ∧
        P.p j ^ 2 ≤ 2 * t * Real.exp ℓ ∧ P.p j ≤ Real.exp ℓ))
      (fun j => (ℓ - Real.log (P.p j)) / Real.log (P.p j)) (fun j => 1 / P.p j) x =
      ∑ j ∈ (P.primesLe X).filter (fun j => y < P.p j), 1 / P.p j := by
    unfold cnt
    rw [← Finset.sum_filter_add_sum_filter_not _
      (fun j => (ℓ - Real.log (P.p j)) / Real.log (P.p j) < x)]
    have hz : ∑ j ∈ ((P.primesLe (2 * Real.exp ℓ)).filter (fun j =>
        ℓ / ustar τ ℓ < Real.log (P.p j) ∧ u * Real.log (P.p j) ≤ ℓ ∧
        P.p j ^ 2 ≤ 2 * t * Real.exp ℓ ∧ P.p j ≤ Real.exp ℓ)).filter
          (fun j => ¬ (ℓ - Real.log (P.p j)) / Real.log (P.p j) < x),
        (Set.Ioi ((ℓ - Real.log (P.p j)) / Real.log (P.p j))).indicator
          (fun _ => 1 / P.p j) x = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact indicator_of_notMem (show x ∉ Set.Ioi _ from hj.2) _
    rw [hz, add_zero, Finset.filter_filter]
    have hone : ∀ j ∈ (P.primesLe (2 * Real.exp ℓ)).filter (fun j =>
        (ℓ / ustar τ ℓ < Real.log (P.p j) ∧ u * Real.log (P.p j) ≤ ℓ ∧
        P.p j ^ 2 ≤ 2 * t * Real.exp ℓ ∧ P.p j ≤ Real.exp ℓ) ∧
          (ℓ - Real.log (P.p j)) / Real.log (P.p j) < x),
        (Set.Ioi ((ℓ - Real.log (P.p j)) / Real.log (P.p j))).indicator (fun _ => 1 / P.p j) x =
          1 / P.p j := fun j hj => indicator_of_mem (Finset.mem_filter.mp hj).2.2 _
    rw [Finset.sum_congr rfl hone]
    congr 1
    ext j
    simp only [Finset.mem_filter, mem_primesLe]
    have hp := P.p_pos j
    have hpX : P.p j ≤ X ↔ Real.log (P.p j) ≤ ℓ / (1 + a) := by
      rw [hX, ← Real.log_le_log_iff hp (Real.exp_pos _), Real.log_exp]
    have hpy : y < P.p j ↔ ℓ / (1 + x) < Real.log (P.p j) := by
      rw [hy, ← Real.log_lt_log_iff (Real.exp_pos _) hp, Real.log_exp]
    rw [hpX, hpy]
    rcases lt_or_ge 0 (Real.log (P.p j)) with hσ0 | hσ0
    · have key := main_count (σ := Real.log (P.p j)) (b := b) (x := x) hτ0 hℓ0 hu0 ha0
        hx.1 hx.2 hσ0
      rw [← hus] at key
      constructor
      · rintro ⟨_, ⟨hs, hu, hp2, hpY⟩, hwx⟩
        apply key.mp
        refine ⟨⟨hs, hu, ?_, ?_⟩, hwx⟩
        · have := Real.log_le_log (by positivity) hp2
          rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) ht.ne', Real.log_exp] at this
          push_cast at this; linarith
        · have := Real.log_le_log hp hpY; rwa [Real.log_exp] at this
      · intro hh
        obtain ⟨⟨hs, hu, h2, hσℓ⟩, hwx⟩ := key.mpr hh
        have hpY : P.p j ≤ Real.exp ℓ := by
          rw [← Real.exp_log hp]; exact Real.exp_le_exp.mpr hσℓ
        refine ⟨?_, ⟨hs, hu, ?_, hpY⟩, hwx⟩
        · linarith [Real.exp_pos ℓ]
        · rw [← Real.exp_log hp, ← Real.exp_nat_mul, htexp,
            show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
            ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          push_cast; linarith
    · have h1 : 0 < ℓ / ustar τ ℓ := div_pos hℓ0 (by rw [hus]; linarith)
      have h2 : 0 < ℓ / (1 + x) := div_pos hℓ0 (by linarith)
      constructor
      · rintro ⟨_, ⟨hs, _⟩, _⟩; linarith
      · rintro ⟨_, h3⟩; linarith
  rw [hcnt]
  have hy2 : 2 ≤ y := by
    have h1 : 100 ≤ ℓ / (1 + x) := by
      refine hus100.trans ?_
      rw [hus]
      exact div_le_div_of_nonneg_left hℓ0.le (by linarith) (by linarith [hx.2])
    have : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  have hyX : y ≤ X := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_left hℓ0.le (by linarith) (by linarith [hx.1]))
  have hXZ : X ≤ Z := by
    have : X ≤ Real.exp ℓ := Real.exp_le_exp.mpr (div_le_self hℓ0.le (by linarith))
    linarith [Real.exp_pos ℓ]
  have hiv := h.mertens_iv hy2 hyX hXZ
  have e1 : Real.log X / Real.log y = (1 + x) / (1 + a) := by
    rw [hX, hy, Real.log_exp, Real.log_exp]; field_simp
  have e2 : 2.20 / Real.log y = Kp * (1 + x) / ℓ := by
    rw [hy, Real.log_exp]; unfold Kp; field_simp; norm_num
  rw [e1, e2] at hiv
  exact hiv

/-- **The induction step of Theorem 5.6** (Steps 5–6). -/
theorem bs_step {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) (h53 : P.Lemma53 Z)
    {t ℓ u : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : 30 * Real.log t < ℓ)
    (hu0 : 0 ≤ u) (huU : u ≤ Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z)
    (hSig : 0 ≤ BSaias.Sigma (Real.log t) ℓ u)
    (IH : ∀ m w, Real.log t ≤ m → m ≤ ℓ - Real.log 2 → 0 ≤ w → w ≤ Uf (Real.log t) m →
      2 * Real.exp m ≤ Z → m / Real.log t * P.Wsm t (Real.exp m) w ≤ Gf (Real.log t) m w) :
    ℓ / Real.log t * P.Wsm t (Real.exp ℓ) u ≤ Gf (Real.log t) ℓ u := by
  set τ := Real.log t with hτdef
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ3 : 3000000000 ≤ ℓ := by linarith
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have htexp : t = Real.exp τ := (Real.exp_log ht).symm
  set Y := Real.exp ℓ with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_exp hℓ0.le
  have hlogY : Real.log Y = ℓ := Real.log_exp ℓ
  set b := Uf τ ℓ - 1 / 2 with hbdef
  set a := wlo τ ℓ u with hadef
  have hus : ustar τ ℓ = 1 + b := by unfold ustar; rw [hbdef]; ring
  obtain ⟨hus1, hus100, husle⟩ := ustar_lemma53 (τ := τ) (by linarith) hℓ.le hℓ3
  set s0 := ℓ / ustar τ ℓ with hs0def
  have hb0 : 0 ≤ b := by linarith
  have hw1pos : 0 < w1 τ ℓ := red_w1_pos hτ0.le (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le hw1pos (le_max_right _ _)
  have hU1 : 1 ≤ Uf τ ℓ := le_trans
    (le_u0_of_pow4 (by norm_num) (by norm_num; linarith)) (u0_le_Uf τ ℓ)
  have haU : a ≤ Uf τ ℓ := max_le (by linarith) (by linarith [w1_lt_one hτ0.le hℓ0])
  have hG := Gf_pos τ ℓ u
  -- the recursion
  have hJ : ∀ j, u * Real.log (P.p j) ≤ Real.log Y → P.p j ^ 2 ≤ 2 * t * Y → P.p j ≤ Y := by
    intro j _ hp2
    have hp := P.p_pos j
    by_contra hcon
    push_neg at hcon
    have : Y ^ 2 < P.p j ^ 2 := pow_lt_pow_left₀ hcon (by linarith) (by norm_num)
    have h2tY : 2 * t * Y < Y ^ 2 := by
      have : 2 * t < Y := by
        rw [htexp, hYdef, show (2 : ℝ) = Real.exp (Real.log 2) from
          (Real.exp_log (by norm_num)).symm, ← Real.exp_add]
        exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    linarith
  have hrec := P.Wsm_le_rec t Y u s0 hY1 hJ
  rw [hlogY] at hrec
  set J := (P.primesLe (2 * Y)).filter (fun j => s0 < Real.log (P.p j) ∧
    u * Real.log (P.p j) ≤ ℓ ∧ P.p j ^ 2 ≤ 2 * t * Y ∧ P.p j ≤ Y) with hJdef
  set σ : ℕ → ℝ := fun j => Real.log (P.p j) with hσdef
  set wj : ℕ → ℝ := fun j => (ℓ - σ j) / σ j with hwjdef
  -- facts about the main primes
  have hJfacts : ∀ j ∈ J, 0 < σ j ∧ s0 < σ j ∧ u * σ j ≤ ℓ ∧
      2 * σ j ≤ ℓ + τ + Real.log 2 ∧ σ j ≤ ℓ ∧ P.p j ≤ Z := by
    intro j hj
    simp only [hJdef, Finset.mem_filter, mem_primesLe] at hj
    obtain ⟨_, hs, hu, hp2, hpY⟩ := hj
    have hp := P.p_pos j
    have hs0pos : 0 < s0 := by rw [hs0def]; exact div_pos hℓ0 (by linarith)
    refine ⟨lt_trans hs0pos hs, hs, hu, ?_, ?_, ?_⟩
    · have := Real.log_le_log (by positivity) hp2
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) ht.ne', hlogY] at this
      push_cast at this
      linarith
    · have := Real.log_le_log hp hpY; rw [hlogY] at this; exact this
    · linarith
  have hJwin : ∀ j ∈ J, a ≤ wj j ∧ wj j < b := by
    intro j hj
    obtain ⟨hσ0, hs, hu, h2, _, _⟩ := hJfacts j hj
    have : ℓ / (1 + b) < σ j := by rw [← hus]; exact hs
    exact main_window hτ0 hℓ0 hb0 this hu h2
  -- the induction hypothesis on the main primes
  have hmain_term : ∀ j ∈ J, ℓ / τ * (1 / P.p j * P.Wsm t (Y / P.p j) ((ℓ - σ j) / σ j)) ≤
      1 / P.p j * Hf τ ℓ (wj j) := by
    intro j hj
    obtain ⟨hσ0, hs, hu, h2, hσℓ, hpZ⟩ := hJfacts j hj
    obtain ⟨hwa, hwb⟩ := hJwin j hj
    have hp := P.p_pos j
    have hp2 := h.p_ge_two hpZ
    have hσ2 : Real.log 2 ≤ σ j := Real.log_le_log (by norm_num) hp2
    have hwpos : 0 < wj j := lt_of_lt_of_le ha0 hwa
    have hσℓ' : σ j < ℓ := by
      have : 0 < (ℓ - σ j) / σ j := hwpos
      have := (div_pos_iff.mp this)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    have hm : mOf ℓ (wj j) = ℓ - σ j := by
      have hσne := hσ0.ne'
      have e : 1 + (ℓ - σ j) / σ j = ℓ / σ j := by field_simp; ring
      simp only [hwjdef]; unfold mOf; rw [e]; field_simp
    have hmτ : τ ≤ ℓ - σ j := by
      rw [← hm]; exact mOf_ge_tau hτ0 (by linarith) ((le_max_right _ _).trans hwa)
    have hshift : wj j ≤ Uf τ (ℓ - σ j) := by
      rw [← hm]
      exact U_shift (by linarith) hℓ.le hℓ3 ((le_max_right _ _).trans hwa) hwb.le
    have hexp : Real.exp (ℓ - σ j) = Y / P.p j := by
      rw [Real.exp_sub, Real.exp_log hp]
    have hIH := IH (ℓ - σ j) (wj j) hmτ (by linarith) hwpos.le hshift
      (by rw [hexp]; have : Y / P.p j ≤ Y := div_le_self (by linarith) (by linarith); linarith)
    rw [hexp] at hIH
    have hmpos : 0 < ℓ - σ j := by linarith
    have hHf : Hf τ ℓ (wj j) = ℓ / (ℓ - σ j) * Gf τ (ℓ - σ j) (wj j) := by
      unfold Hf; rw [hm]; congr 1; simp only [hwjdef]; field_simp; ring
    rw [hHf]
    have hWnn : 0 ≤ P.Wsm t (Y / P.p j) (wj j) := by
      unfold Wsm; exact Finset.sum_nonneg fun e _ => div_nonneg zero_le_one (P.val_pos e).le
    have : ℓ / τ * P.Wsm t (Y / P.p j) (wj j) ≤ ℓ / (ℓ - σ j) * Gf τ (ℓ - σ j) (wj j) := by
      have e : ℓ / τ * P.Wsm t (Y / P.p j) (wj j) =
          ℓ / (ℓ - σ j) * ((ℓ - σ j) / τ * P.Wsm t (Y / P.p j) (wj j)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hIH (by positivity)
    have hp' : 0 < 1 / P.p j := by positivity
    calc ℓ / τ * (1 / P.p j * P.Wsm t (Y / P.p j) ((ℓ - σ j) / σ j))
        = 1 / P.p j * (ℓ / τ * P.Wsm t (Y / P.p j) (wj j)) := by simp only [hwjdef]; ring
      _ ≤ 1 / P.p j * (ℓ / (ℓ - σ j) * Gf τ (ℓ - σ j) (wj j)) :=
          mul_le_mul_of_nonneg_left this hp'.le
  -- the tail (Step 6)
  have htail : ℓ / τ * P.vSmooth Y (Real.exp s0) ≤ Gf τ ℓ u * Tterm τ ℓ u := by
    have hlogz : Real.log (Real.exp s0) = s0 := Real.log_exp s0
    have hus0 : ustar τ ℓ * s0 = ℓ := by rw [hs0def]; field_simp
    have := h53 (Real.exp s0) (ustar τ ℓ) (by rw [hlogz]; exact hus100) hus1
      (by rw [hlogz]; exact husle) (by rw [hlogz, hus0]; exact hZ)
    rw [hlogz, hus0] at this
    have e : Gf τ ℓ u * Tterm τ ℓ u =
        ℓ / τ * (C0 * Dickman.rho (ustar τ ℓ) * Real.exp (aV ℓ (ustar τ ℓ))) := by
      unfold Tterm; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- the main part: partial summation
  have hmain : ∑ j ∈ J, 1 / P.p j * Hf τ ℓ (wj j) ≤ Gf τ ℓ u *
      (Mterm τ ℓ u (paperCut τ ℓ) + E1term τ ℓ u (paperCut τ ℓ) + E2term τ ℓ u (paperCut τ ℓ) +
        E3term τ ℓ u (paperCut τ ℓ)) :=
    main_ps J wj (fun j => 1 / P.p j) (by linarith) hℓ.le hℓ3 hu0 huU hJwin
      (fun hab x hx => P.main_cnt_bound h ht hτ hℓ hu0 hZ hx)
  -- assembly
  have hfinal : ℓ / τ * P.Wsm t Y u ≤ Gf τ ℓ u * (1 - BSaias.Sigma τ ℓ u) := by
    have hsum : ℓ / τ * (∑ j ∈ J, 1 / P.p j * P.Wsm t (Y / P.p j) ((ℓ - σ j) / σ j)) ≤
        ∑ j ∈ J, 1 / P.p j * Hf τ ℓ (wj j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hmain_term
    have h1 := mul_le_mul_of_nonneg_left hrec (show 0 ≤ ℓ / τ by positivity)
    rw [mul_add] at h1
    unfold BSaias.Sigma SigmaGen
    have : Gf τ ℓ u * (1 - (1 - (Mterm τ ℓ u (paperCut τ ℓ) + E1term τ ℓ u (paperCut τ ℓ) +
        E2term τ ℓ u (paperCut τ ℓ) + E3term τ ℓ u (paperCut τ ℓ) + Tterm τ ℓ u))) =
        Gf τ ℓ u * (Mterm τ ℓ u (paperCut τ ℓ) + E1term τ ℓ u (paperCut τ ℓ) +
          E2term τ ℓ u (paperCut τ ℓ) + E3term τ ℓ u (paperCut τ ℓ)) +
        Gf τ ℓ u * Tterm τ ℓ u := by ring
    rw [this]
    simp only [hσdef] at hsum
    linarith
  calc ℓ / τ * P.Wsm t Y u ≤ Gf τ ℓ u * (1 - BSaias.Sigma τ ℓ u) := hfinal
    _ ≤ Gf τ ℓ u * 1 := by
        apply mul_le_mul_of_nonneg_left _ hG.le; linarith
    _ = Gf τ ℓ u := mul_one _

end BeurlingSystem

end
