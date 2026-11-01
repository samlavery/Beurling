module

public import RequestProject.Beurling.Noise.BSL57PSize
public import RequestProject.Beurling.Noise.BSZ1Size

/-!
# Lemma 5.7: pointwise bounds (P1)–(P3)

With `s = w - u`, `Λ = Λ(u)`, `D' = (B/ℓ) h_A + D_a` (`Dp_eq`), on the large range:

* (P1) `h_A ≤ ((1+u)/u) Λ` and `h_A ≥ -4Λ` on `[u-1, u]`; `0 ≤ h_A ≤ Λ((1+u)/u + 8s(1+s)³)` for
  `w ≥ u` (the paper's `φ_A`, with the head constant `4` in place of `8`);
* (P2) `D_a = a(m,w) - a(ℓ,u)`: `|D_a| ≤ a'(|s| + 0.2502) + (s₊² + 0.2502 s₊ + 0.0314)/√ℓ`;
* (P3) `D' ≤ 0.0003 + 0.0012 s₊` for `w ≤ Ū` (the paper: `0.7·10⁻⁴ + 3·10⁻⁴ s₊`; we use the
  cruder sizes `λ ≤ 1.5·10⁻⁶`, `α' ≤ 10⁻³` that follow from `ε(ℓ) ≤ 0.03`).
-/

@[expose] public section

open Real

namespace BSaias.Large

variable {τ ℓ u : ℝ}

/-! ## (P1) -/

lemma hfun_le_head {w : ℝ} (hu : 2 ≤ u) (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    hfun w ≤ hfun u := by
  have h := h_sub_ge (u := u) (w := w) hu hw1 hwu
  have h0 : 0 ≤ u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 * (u - w) := by
    apply mul_nonneg _ (by linarith)
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (Real.log_nonneg (by linarith))
  linarith

lemma hA_u_eq (hu : 2 ≤ u) : hA u u = (1 + u) / u * Lam u := by
  unfold hA hfun Lam
  have hu0 : 0 < u := by linarith
  field_simp
  ring

lemma hA_head_upper {w : ℝ} (hu : 2 ≤ u) (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    hA u w ≤ (1 + u) / u * Lam u := by
  have := hfun_le_head hu hw1 hwu
  rw [← hA_u_eq hu]; unfold hA; linarith

lemma hA_head_lower {w : ℝ} (hu : 2 ≤ u) (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    -(4 * Lam u) ≤ hA u w := by
  have hw0 : 0 < w := by linarith
  have hu0 : 0 < u := by linarith
  -- `h(w) ≥ u³ log(1+u)`
  have hL1 : Real.log (1 + u) ≤ Real.log (2 + w) := Real.log_le_log (by linarith) (by linarith)
  have hL10 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hp : u ^ 4 ≤ (1 + w) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hh : u ^ 3 * Real.log (1 + u) ≤ hfun w := by
    unfold hfun
    rw [le_div_iff₀ hw0]
    have h1 : u ^ 4 * Real.log (1 + u) ≤ (1 + w) ^ 4 * Real.log (2 + w) :=
      mul_le_mul hp hL1 hL10 (by positivity)
    have h2 : u ^ 3 * Real.log (1 + u) * w ≤ u ^ 3 * Real.log (1 + u) * u :=
      mul_le_mul_of_nonneg_left hwu (by positivity)
    nlinarith
  -- `(1+u)³ L₂ - u³ L₁ ≤ 4 (1+u)² L₂`
  have hL2 : Real.log (2 + u) - Real.log (1 + u) ≤ 1 / (1 + u) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < (2 + u) / (1 + u) by positivity)
    have e : (2 + u) / (1 + u) - 1 = 1 / (1 + u) := by field_simp; ring
    linarith
  have hL4 : 1 ≤ Real.log (2 + u) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have key : (1 + u) ^ 3 * Real.log (2 + u) - u ^ 3 * Real.log (1 + u) ≤
      4 * ((1 + u) ^ 2 * Real.log (2 + u)) := by
    have e1 : u ^ 3 * (Real.log (2 + u) - Real.log (1 + u)) ≤ u ^ 3 * (1 / (1 + u)) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have e2 : u ^ 3 * (1 / (1 + u)) ≤ (1 + u) ^ 2 * Real.log (2 + u) := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      have : u ^ 3 ≤ (1 + u) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      have h4 := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ (1 + u) ^ 3)
      nlinarith
    nlinarith
  unfold hA Lam
  linarith

lemma hA_tail {w : ℝ} (hu : 2 ≤ u) (huw : u ≤ w) :
    0 ≤ hA u w ∧ hA u w ≤ Lam u * ((1 + u) / u + 8 * (w - u) * (1 + (w - u)) ^ 3) := by
  refine ⟨by unfold hA; linarith [hfun_ge hu huw], ?_⟩
  have h1 := h_sub_le (u := u) (w := w) (by linarith) huw
  have h2 := Lam_shift_le hu huw
  have hs : 0 ≤ w - u := by linarith
  have h3 : 8 * (1 + w) ^ 2 * Real.log (2 + w) * (w - u) ≤
      8 * (Lam u * (1 + (w - u)) ^ 3) * (w - u) := by
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith
  have e : hA u w = hfun w - hfun u + hA u u := by unfold hA; ring
  rw [e, hA_u_eq hu]
  nlinarith

/-- The slope form of (P1) for (P3): `h_A ≤ ((1+u)/u) Λ(u) + 8 Λ(w) (w - u)`. -/
lemma hA_tail_lin {w : ℝ} (hu : 2 ≤ u) (huw : u ≤ w) :
    hA u w ≤ (1 + u) / u * Lam u + 8 * Lam w * (w - u) := by
  have h1 := h_sub_le (u := u) (w := w) (by linarith) huw
  have e : hA u w = hfun w - hfun u + hA u u := by unfold hA; ring
  rw [e, hA_u_eq hu]; unfold Lam; nlinarith

lemma Lam_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Lam x ≤ Lam y := by
  unfold Lam
  have h1 : (1 + x) ^ 2 ≤ (1 + y) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : Real.log (2 + x) ≤ Real.log (2 + y) := Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.log_nonneg (by linarith)) (by positivity)

lemma Lam_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Lam x := by
  unfold Lam; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + x); positivity

/-! ## (P2) -/

/-- `a(ℓ, w) ≤ a(m, w)` (`m ≤ ℓ`). -/
lemma aQ_le_mOf (hℓ : 0 < ℓ) {w : ℝ} (hw0 : 0 < w) : aQ ℓ w ≤ aQ (mOf ℓ w) w := by
  unfold aQ
  have hm : 0 < mOf ℓ w := BSaias.mOf_pos hℓ hw0
  have hmℓ : mOf ℓ w ≤ ℓ := by
    unfold mOf; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hu0 := u0_mOf_le hℓ hw0.le
  have hnum : max (w - u0 ℓ) 0 ≤ max (w - u0 (mOf ℓ w)) 0 := max_le_max (by linarith) le_rfl
  have hs : √(mOf ℓ w) ≤ √ℓ := Real.sqrt_le_sqrt hmℓ
  have hsm : 0 < √(mOf ℓ w) := Real.sqrt_pos.mpr hm
  calc (max (w - u0 ℓ) 0) ^ 2 / (2 * √ℓ) ≤ (max (w - u0 ℓ) 0) ^ 2 / (2 * √(mOf ℓ w)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ ≤ (max (w - u0 (mOf ℓ w)) 0) ^ 2 / (2 * √(mOf ℓ w)) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hnum 2) (by positivity)

/-- The shift: `a(m, w) ≤ a(ℓ, w) + 0.2502 (w-u₀)₊/√ℓ + 0.0314/√ℓ` for every `w ≥ 1`. -/
lemma aQ_mOf_le_shift (hℓ : 1000000000000000000 ≤ ℓ) {w : ℝ} (hw : 1 ≤ w) :
    aQ (mOf ℓ w) w ≤ aQ ℓ w + 0.2502 * max (w - u0 ℓ) 0 / √ℓ + 0.0314 / √ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
  rcases le_or_gt (u0 ℓ - 3) w with h3 | h3
  · have := aQ_mOf_le hℓ h3
    unfold aQ at this ⊢
    linarith
  · rw [aQ_mOf_eq_zero_low hℓ0 hw h3.le]
    have := aQ_nonneg ℓ w
    have : 0 ≤ 0.2502 * max (w - u0 ℓ) 0 / √ℓ := by positivity
    have : 0 ≤ 0.0314 / √ℓ := by positivity
    linarith

lemma aQ_sub_head {w : ℝ} (hwu : w ≤ u) :
    aQ ℓ u - aQ ℓ w ≤ aprime ℓ u * (u - w) ∧ aQ ℓ w ≤ aQ ℓ u := by
  obtain ⟨h1, h2⟩ := sq_pos_part_sub (u0 ℓ) w u hwu
  have hs := Real.sqrt_nonneg ℓ
  unfold aQ aprime
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]; simp
  constructor
  · rw [div_sub_div_same, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) h0]
    nlinarith
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_nonneg (le_max_right (w - u0 ℓ) 0) (by linarith : (0 : ℝ) ≤ u - w)
    nlinarith

lemma aQ_sub_tail {w : ℝ} (huw : u ≤ w) :
    0 ≤ aQ ℓ w - aQ ℓ u ∧
      aQ ℓ w - aQ ℓ u ≤ max (w - u0 ℓ) 0 * (w - u) / √ℓ := by
  obtain ⟨h1, h2⟩ := sq_pos_part_sub (u0 ℓ) u w huw
  have hs := Real.sqrt_nonneg ℓ
  unfold aQ
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]; simp
  constructor
  · rw [sub_nonneg]; apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_nonneg (le_max_right (u - u0 ℓ) 0) (by linarith : (0 : ℝ) ≤ w - u)
    nlinarith
  · rw [div_sub_div_same, div_le_div_iff₀ (by positivity) h0]
    nlinarith

/-- `D_a = a(m,w) - a(ℓ,u)`. -/
noncomputable def Da (ℓ u w : ℝ) : ℝ := aQ (mOf ℓ w) w - aQ ℓ u

lemma LargeRange.sigma_le (hR : LargeRange τ ℓ u) {w : ℝ} (hw : 1 ≤ w) :
    0 ≤ aQ (mOf ℓ w) w - aQ ℓ w ∧
      aQ (mOf ℓ w) w - aQ ℓ w ≤ 0.2502 * max (w - u0 ℓ) 0 / √ℓ + 0.0314 / √ℓ := by
  have hℓ0 := hR.ℓ_pos
  refine ⟨by linarith [aQ_le_mOf hℓ0 (by linarith : (0 : ℝ) < w)], ?_⟩
  linarith [aQ_mOf_le_shift hR.2.2.1 hw]

/-- (P2) on the head `[u-1, u]`. -/
lemma LargeRange.Da_head (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    |Da ℓ u w| ≤ 1.2502 * aprime ℓ u + 0.0314 / √ℓ ∧
      Da ℓ u w ≤ 0.2502 * aprime ℓ u + 0.0314 / √ℓ := by
  have hu := hR.2.2.2.1
  obtain ⟨h0, h1⟩ := hR.sigma_le (w := w) (by linarith)
  obtain ⟨h2, h3⟩ := aQ_sub_head (ℓ := ℓ) hwu
  have hs := hR.sqrt_pos
  have hm : max (w - u0 ℓ) 0 / √ℓ ≤ aprime ℓ u := by
    unfold aprime
    exact div_le_div_of_nonneg_right (max_le_max (by linarith) le_rfl) hs.le
  have ha := hR.ap_nonneg
  have e : 0.2502 * max (w - u0 ℓ) 0 / √ℓ = 0.2502 * (max (w - u0 ℓ) 0 / √ℓ) := by ring
  have hap : aprime ℓ u * (u - w) ≤ aprime ℓ u := by nlinarith
  unfold Da
  rw [abs_le]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith

/-- (P2) beyond `u`. -/
lemma LargeRange.Da_tail (hR : LargeRange τ ℓ u) {w : ℝ} (huw : u ≤ w) :
    0 ≤ Da ℓ u w ∧ Da ℓ u w ≤ aprime ℓ u * ((w - u) + 0.2502) +
      ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ := by
  have hu := hR.2.2.2.1
  obtain ⟨h0, h1⟩ := hR.sigma_le (w := w) (by linarith)
  obtain ⟨h2, h3⟩ := aQ_sub_tail (ℓ := ℓ) huw
  have hs := hR.sqrt_pos
  have hmax : max (w - u0 ℓ) 0 ≤ max (u - u0 ℓ) 0 + (w - u) :=
    max_le (by linarith [le_max_left (u - u0 ℓ) 0]) (by linarith [le_max_right (u - u0 ℓ) 0])
  have hsw : 0 ≤ w - u := by linarith
  refine ⟨by unfold Da; linarith, ?_⟩
  have e1 : max (w - u0 ℓ) 0 * (w - u) / √ℓ ≤ aprime ℓ u * (w - u) + (w - u) ^ 2 / √ℓ := by
    unfold aprime
    rw [div_mul_eq_mul_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  have e2 : 0.2502 * max (w - u0 ℓ) 0 / √ℓ ≤
      0.2502 * aprime ℓ u + 0.2502 * (w - u) / √ℓ := by
    unfold aprime
    rw [mul_div_assoc', ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  unfold Da
  have e3 : aprime ℓ u * ((w - u) + 0.2502) + ((w - u) ^ 2 + 0.2502 * (w - u) + 0.0314) / √ℓ =
      aprime ℓ u * (w - u) + (w - u) ^ 2 / √ℓ +
        (0.2502 * aprime ℓ u + 0.2502 * (w - u) / √ℓ) + 0.0314 / √ℓ := by ring
  rw [e3]
  linarith

/-- (P2), linear form for `u ≤ w ≤ Ū`. -/
lemma LargeRange.Da_lin (hR : LargeRange τ ℓ u) {w : ℝ} (huw : u ≤ w) (hwU : w ≤ Uf τ ℓ) :
    Da ℓ u w ≤ alphaL τ ℓ * ((w - u) + 0.2502) + 0.0314 / √ℓ := by
  have hu := hR.2.2.2.1
  obtain ⟨h0, h1⟩ := hR.sigma_le (w := w) (by linarith)
  obtain ⟨h2, h3⟩ := aQ_sub_tail (ℓ := ℓ) huw
  have hs := hR.sqrt_pos
  have hmax : max (w - u0 ℓ) 0 / √ℓ ≤ alphaL τ ℓ := by
    rw [hR.alpha_eq]
    exact div_le_div_of_nonneg_right (max_le (by linarith) (by linarith [hR.U_ge, hR.u0_ge]))
      hs.le
  have hsw : 0 ≤ w - u := by linarith
  have e1 : max (w - u0 ℓ) 0 * (w - u) / √ℓ ≤ alphaL τ ℓ * (w - u) := by
    rw [mul_comm, mul_div_assoc, mul_comm]
    exact mul_le_mul_of_nonneg_right hmax hsw
  have e2 : 0.2502 * max (w - u0 ℓ) 0 / √ℓ ≤ 0.2502 * alphaL τ ℓ := by
    rw [mul_div_assoc]; linarith
  unfold Da
  nlinarith

lemma LargeRange.c_div_sqrt_le (hR : LargeRange τ ℓ u) {c : ℝ} (hc : 0 ≤ c) :
    c / √ℓ ≤ c * alphaL τ ℓ / 63244 := by
  have h := hR.inv_sqrt_le
  have e : c / √ℓ = c * (1 / √ℓ) := by ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h hc

lemma Dp_eq_Da (hℓ : 0 < ℓ) {w : ℝ} (hw : 0 < w) :
    Dp ℓ u w = 11 / ℓ * hA u w + Da ℓ u w := by
  rw [Dp_eq hℓ hw]; rfl

/-- **(P3)**: `D' ≤ 0.0003 + 0.0012 (w - u)₊` for `u - 1 ≤ w ≤ Ū`. -/
lemma LargeRange.Dp_le (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : u - 1 ≤ w) (hwU : w ≤ Uf τ ℓ) :
    Dp ℓ u w ≤ 0.0003 + 0.0012 * max (w - u) 0 := by
  have hu := hR.2.2.2.1
  have hℓ0 := hR.ℓ_pos
  have hlam := hR.lam_le
  have hlam0 := lamL_nonneg (τ := τ) hℓ0
  have hα := hR.alpha_le
  have hα0 := alphaL_nonneg (τ := τ) (ℓ := ℓ)
  have hap := hR.ap_le
  have hinv := hR.inv_sqrt_le
  have hΛ := hR.Lam_le
  have hΛU := hR.LamU_le
  have hΛ0 := Lam_nonneg (x := u) (by linarith)
  have h15 : (1 + u) / u ≤ 1.5 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hq := hR.c_div_sqrt_le (c := 0.0314) (by norm_num)
  have hDA1 : 11 / ℓ * ((1 + u) / u * Lam u) ≤ 0.0000248 := by
    have : (1 + u) / u * Lam u ≤ 1.5 * Lam u := mul_le_mul_of_nonneg_right h15 hΛ0
    rw [div_mul_eq_mul_div, div_le_iff₀ hℓ0]; nlinarith
  rw [Dp_eq_Da hℓ0 (by linarith)]
  rcases le_or_gt w u with hwu | hwu
  · rw [max_eq_right (by linarith)]
    have h1 := hA_head_upper hu hw1 hwu
    obtain ⟨-, h2⟩ := hR.Da_head hw1 hwu
    have h3 : 11 / ℓ * hA u w ≤ 11 / ℓ * ((1 + u) / u * Lam u) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  · rw [max_eq_left (by linarith)]
    have h1 := hA_tail_lin hu hwu.le
    have hΛw : Lam w ≤ Lam (Uf τ ℓ) := Lam_mono (by linarith) hwU
    have h2 := hR.Da_lin hwu.le hwU
    have hs : 0 ≤ w - u := by linarith
    have h3 : 11 / ℓ * hA u w ≤ 0.0000248 + 0.0001322 * (w - u) := by
      have h4 : 11 / ℓ * hA u w ≤ 11 / ℓ * ((1 + u) / u * Lam u) +
          11 / ℓ * (8 * Lam (Uf τ ℓ) * (w - u)) := by
        have h6 : 8 * Lam w * (w - u) ≤ 8 * Lam (Uf τ ℓ) * (w - u) :=
          mul_le_mul_of_nonneg_right (by linarith) hs
        have h7 : hA u w ≤ (1 + u) / u * Lam u + 8 * Lam (Uf τ ℓ) * (w - u) := by linarith
        have := mul_le_mul_of_nonneg_left h7 (by positivity : 0 ≤ 11 / ℓ)
        linarith
      have h5 : 11 / ℓ * (8 * Lam (Uf τ ℓ) * (w - u)) ≤ 0.0001322 * (w - u) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hℓ0]
        have : Lam (Uf τ ℓ) * (w - u) ≤ 1.001 * lamL τ ℓ * ℓ * (w - u) :=
          mul_le_mul_of_nonneg_right hΛU hs
        have h8 := mul_le_mul_of_nonneg_right hlam (mul_nonneg hℓ0.le hs)
        nlinarith
      linarith
    nlinarith

lemma exp_small_le {x : ℝ} (hx : x ≤ 0.0003) : Real.exp x ≤ 1.0004 := by
  have h := Real.add_one_le_exp (-x)
  have hpos := Real.exp_pos x
  have e : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- `e^{D'₊} ≤ 1.0004 e^{0.0012 (w-u)₊}` for `u - 1 ≤ w ≤ Ū`. -/
lemma LargeRange.exp_Dp_le (hR : LargeRange τ ℓ u) {w : ℝ} (hw1 : u - 1 ≤ w)
    (hwU : w ≤ Uf τ ℓ) :
    Real.exp (max (Dp ℓ u w) 0) ≤ 1.0004 * Real.exp (0.0012 * max (w - u) 0) := by
  have h := hR.Dp_le hw1 hwU
  have hs : 0 ≤ 0.0012 * max (w - u) 0 := by positivity
  have hm : max (Dp ℓ u w) 0 ≤ 0.0003 + 0.0012 * max (w - u) 0 := max_le h (by linarith)
  calc Real.exp (max (Dp ℓ u w) 0) ≤ Real.exp (0.0003 + 0.0012 * max (w - u) 0) :=
        Real.exp_le_exp.mpr hm
    _ = Real.exp 0.0003 * Real.exp (0.0012 * max (w - u) 0) := Real.exp_add _ _
    _ ≤ 1.0004 * Real.exp (0.0012 * max (w - u) 0) :=
        mul_le_mul_of_nonneg_right (exp_small_le le_rfl) (Real.exp_pos _).le

end BSaias.Large

end
