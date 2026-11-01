module

public import RequestProject.Beurling.Noise.BSZ2Hfun

/-!
# Pointwise majorants of `D(w)` and `η_f` in region Z2 (Theorem 5.6, Step 7(iii))

Throughout `u ≥ 2`, `w ≥ u - 1` and `m = ℓw/(1+w)`. With `c_u = u₀/(3u)`,
`k_u = 1 + 1/(2(u-1))` and `φ(w) = (w - u₀ + c_u)₊²/(2√ℓ)` (`phiZ`):

* "two elementary majorants": `m^{1/4} ≥ u₀ - c_u` (`u0_mOf_ge`), so
  `(w - m^{1/4})₊ ≤ (w - u₀ + c_u)₊` (`dpos_le`), and `a(m, w) ≤ k_u φ(w)` (`aQ_mOf_le`);
  `A(m, w) = (B/ℓ) h(w)` (`A_mOf`);
* `k_u φ(u) - a(ℓ, u) ≤ β_a` (`betaa_ge`);
* **Part I**: `D(w) ≤ β_I - α(u - w)` for `u - 1 ≤ w ≤ u` (`D_partI`);
* **Part II**: `D(w) ≤ β_II + γ₁ (w - u)` for `u ≤ w ≤ u + 60` (`D_le_gamma1`) and
  `D(w) ≤ β_II + γ_max (w - u)` for `u ≤ w ≤ Ū` (`D_le_gammaMax`);
* `η_f(w) ≤ η̄(w, w - u₀)` (`etaF_le_eta`) and the monotonicity of `η̄` (`eta_mono`).
-/

@[expose] public section

open Real Set

namespace BSaias

open BSCert.Z2 (cu ku)

/-- `φ(w) = (w - u₀ + c_u)₊²/(2√ℓ)`. -/
noncomputable def phiZ (ℓ u w : ℝ) : ℝ := (max (w - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)

lemma A_mOf {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 < w) :
    BSCert.Z2.A (mOf ℓ w) w = 11 / ℓ * hfun w := by
  unfold BSCert.Z2.A mOf hfun
  field_simp

lemma A_self {ℓ u : ℝ} (hu : 0 < u) :
    11 / ℓ * hfun u = BSCert.Z2.A ℓ u + BSCert.Z2.A ℓ u / u := by
  unfold BSCert.Z2.A hfun
  field_simp
  ring

lemma u0_pos {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < u0 ℓ :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hℓ)

lemma u0_pow_four {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : u0 ℓ ^ 4 = ℓ := by
  show (√(√ℓ)) ^ 4 = ℓ
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt hℓ]

lemma u0_sq (ℓ : ℝ) : u0 ℓ ^ 2 = √ℓ := by
  show (√(√ℓ)) ^ 2 = √ℓ
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]

/-- `u₀` is monotone. -/
lemma u0_mono {a b : ℝ} (h : a ≤ b) : u0 a ≤ u0 b :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

lemma mOf_ge {ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : u - 1 ≤ w) :
    ℓ * (1 - 1 / u) ≤ mOf ℓ w := by
  unfold mOf
  have hw0 : 0 < w := by linarith
  have hu0 : 0 < u := by linarith
  rw [le_div_iff₀ (by linarith)]
  have : (1 - 1 / u) * (1 + w) ≤ w := by
    rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    have : (1 + w) / u ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hu0]; linarith
    linarith
  nlinarith

lemma mOf_ge_half {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 1 ≤ w) : ℓ / 2 ≤ mOf ℓ w := by
  unfold mOf
  rw [le_div_iff₀ (by linarith)]
  nlinarith

lemma mOf_le {ℓ w : ℝ} (hℓ : 0 < ℓ) (hw : 0 ≤ w) : mOf ℓ w ≤ ℓ := by
  unfold mOf
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `m^{1/4} ≥ u₀ - c_u` for `w ≥ u - 1`, `u ≥ 2`. -/
lemma u0_mOf_ge {ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : u - 1 ≤ w) :
    u0 ℓ - cu ℓ u ≤ u0 (mOf ℓ w) := by
  have hu0 : 0 < u := by linarith
  set c := 1 - 1 / (3 * u) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; have : 1 / (3 * u) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have e : u0 ℓ - cu ℓ u = u0 ℓ * c := by unfold cu; rw [hc]; field_simp
  rw [e]
  have hpoly : c ^ 4 ≤ 1 - 1 / u := by
    set y := 1 / u with hy
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ 1 / 2 := by rw [hy, div_le_div_iff₀ hu0 (by norm_num)]; linarith
    have : c = 1 - y / 3 := by rw [hc, hy]; field_simp
    rw [this]
    nlinarith [mul_pos hy0 hy0, mul_pos (mul_pos hy0 hy0) hy0, mul_pos (mul_pos hy0 hy0)
      (mul_pos hy0 hy0)]
  have hX : (u0 ℓ * c) ^ 4 ≤ mOf ℓ w := by
    rw [mul_pow, u0_pow_four hℓ.le]
    exact (mul_le_mul_of_nonneg_left hpoly hℓ.le).trans (mOf_ge hℓ hu hw)
  have hX0 : 0 ≤ u0 ℓ * c := mul_nonneg (u0_pos hℓ).le hc0
  have h2 : ((u0 ℓ * c) ^ 2) ^ 2 ≤ mOf ℓ w := by rw [← pow_mul]; exact hX
  have h3 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (by positivity)] at h3
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq hX0] at h4
  exact h4

lemma cu_nonneg {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u) : 0 ≤ cu ℓ u := by
  unfold cu; exact div_nonneg (u0_pos hℓ).le (by positivity)

/-- `(w - m^{1/4})₊ ≤ (w - u₀ + c_u)₊`. -/
lemma dpos_le {ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : u - 1 ≤ w) :
    dpos (mOf ℓ w) w ≤ max (w - u0 ℓ + cu ℓ u) 0 := by
  unfold dpos
  have := u0_mOf_ge hℓ hu hw
  exact max_le_max (by linarith) le_rfl

lemma ku_pos {u : ℝ} (hu : 2 ≤ u) : 1 < ku u := by
  unfold ku; have : 0 < 1 / (2 * (u - 1)) := by apply div_pos one_pos; linarith
  linarith

/-- `a(m, w) ≤ k_u φ(w)` for `w ≥ u - 1`. -/
lemma aQ_mOf_le {ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : u - 1 ≤ w) :
    aQ (mOf ℓ w) w ≤ ku u * phiZ ℓ u w := by
  unfold aQ phiZ
  have hw0 : 0 < w := by linarith
  have hm : 0 < mOf ℓ w := by unfold mOf; positivity
  have hd := dpos_le hℓ hu hw
  unfold dpos at hd
  have hsq : (max (w - u0 (mOf ℓ w)) 0) ^ 2 ≤ (max (w - u0 ℓ + cu ℓ u) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hd 2
  -- `√ℓ ≤ k_u √m`
  have hkm : √ℓ ≤ ku u * √(mOf ℓ w) := by
    have hk := ku_pos hu
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ku u), ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    unfold mOf
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    -- `ℓ (1 + w) ≤ k_u² ℓ w`, as `k_u² ≥ 1 + 1/(u-1) ≥ 1 + 1/w`
    have h1 : 1 + 1 / (u - 1) ≤ ku u ^ 2 := by
      unfold ku; nlinarith [sq_nonneg (1 / (2 * (u - 1))), show 1 / (2 * (u - 1)) * 2 =
        1 / (u - 1) by field_simp]
    have h2 : 1 / w ≤ 1 / (u - 1) := one_div_le_one_div_of_le (by linarith) hw
    have h3 : (1 + w) ≤ ku u ^ 2 * w := by
      have : (1 + 1 / w) * w = 1 + w := by rw [add_mul, one_div, inv_mul_cancel₀ hw0.ne']; ring
      nlinarith
    nlinarith
  have hpos : 0 < 2 * √(mOf ℓ w) := by positivity
  calc (max (w - u0 (mOf ℓ w)) 0) ^ 2 / (2 * √(mOf ℓ w))
      ≤ (max (w - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √(mOf ℓ w)) :=
        div_le_div_of_nonneg_right hsq hpos.le
    _ ≤ ku u * ((max (w - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) := by
        rw [mul_div_assoc', div_le_div_iff₀ hpos (by positivity)]
        have := sq_nonneg (max (w - u0 ℓ + cu ℓ u) 0)
        nlinarith [mul_le_mul_of_nonneg_left hkm this]

/-- `k_u φ(u) - a(ℓ, u) ≤ β_a`. -/
lemma betaa_ge {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) :
    ku u * phiZ ℓ u u - aQ ℓ u ≤ BSCert.Z2.betaa ℓ u := by
  unfold phiZ aQ BSCert.Z2.betaa
  have hc := cu_nonneg hℓ (by linarith : (0 : ℝ) < u)
  have hs : 0 < 2 * √ℓ := by positivity
  set v := u - u0 ℓ
  have ev : u - u0 ℓ + cu ℓ u = v + cu ℓ u := rfl
  rw [ev]
  set c := cu ℓ u
  have key : (max (v + c) 0) ^ 2 - (max v 0) ^ 2 ≤
      (if v + c ≤ 0 then 0 else c * (2 * max v 0 + c)) := by
    split_ifs with h
    · rw [max_eq_right h, max_eq_right (by linarith)]; simp
    · push_neg at h
      rw [max_eq_left h.le]
      rcases le_total v 0 with hv | hv
      · rw [max_eq_right hv]; nlinarith
      · rw [max_eq_left hv]; nlinarith
  have e2 : (if v + c ≤ 0 then (0 : ℝ) else c * (2 * max v 0 + c) / (2 * √ℓ)) =
      (if v + c ≤ 0 then 0 else c * (2 * max v 0 + c)) / (2 * √ℓ) := by
    split_ifs <;> simp
  rw [e2]
  have : ku u * ((max (v + c) 0) ^ 2 / (2 * √ℓ)) - (max v 0) ^ 2 / (2 * √ℓ) =
      ((ku u - 1) * (max (v + c) 0) ^ 2 + ((max (v + c) 0) ^ 2 - (max v 0) ^ 2)) /
        (2 * √ℓ) := by ring
  rw [this, add_div]
  have := div_le_div_of_nonneg_right key hs.le
  linarith

/-- The common upper bound: `D(w) ≤ (B/ℓ) h(w) + k_u φ(w) - A(ℓ,u) - a(ℓ,u) - κ_Φ/(wℓ)`. -/
lemma D_le_F {τ ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : u - 1 ≤ w) :
    Dfun τ ℓ u w ≤ 11 / ℓ * hfun w + ku u * phiZ ℓ u w - BSCert.Z2.A ℓ u - aQ ℓ u
      - kappa τ / (w * ℓ) := by
  unfold Dfun Qf
  rw [A_mOf hℓ (by linarith)]
  have := aQ_mOf_le hℓ hu hw
  linarith

/-- **Part I**: `D(w) ≤ β_I - α (u - w)` for `u - 1 ≤ w ≤ u`. -/
lemma D_partI {τ ℓ u w : ℝ} (hτ : 100000000 ≤ τ) (hℓ : 0 < ℓ) (hu : 2 ≤ u)
    (hw1 : u - 1 ≤ w) (hwu : w ≤ u) :
    Dfun τ ℓ u w ≤ BSCert.Z2.betaI ℓ u - BSCert.Z2.alpha ℓ u * (u - w) := by
  have hu0 : 0 < u := by linarith
  have hw0 : 0 < w := by linarith
  have hD := D_le_F (τ := τ) hℓ hu hw1
  have hh := h_sub_ge hu hw1 hwu
  have hφ := (sq_pos_part_sub (u0 ℓ - cu ℓ u) w u hwu).2
  have e : ∀ x, x - (u0 ℓ - cu ℓ u) = x - u0 ℓ + cu ℓ u := fun x => by ring
  simp only [e] at hφ
  have hk := ku_pos hu
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  -- the φ-part
  have hφ2 : ku u * max (u - u0 ℓ - 1 + cu ℓ u) 0 / √ℓ * (u - w) ≤
      ku u * phiZ ℓ u u - ku u * phiZ ℓ u w := by
    unfold phiZ
    have hm : max (u - u0 ℓ - 1 + cu ℓ u) 0 ≤ max (w - u0 ℓ + cu ℓ u) 0 :=
      max_le_max (by linarith) le_rfl
    have huw : 0 ≤ u - w := by linarith
    have h1 : max (u - u0 ℓ - 1 + cu ℓ u) 0 * (u - w) ≤
        ((max (u - u0 ℓ + cu ℓ u) 0) ^ 2 - (max (w - u0 ℓ + cu ℓ u) 0) ^ 2) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm huw]
    have h2 : ku u * max (u - u0 ℓ - 1 + cu ℓ u) 0 / √ℓ * (u - w) =
        ku u * (max (u - u0 ℓ - 1 + cu ℓ u) 0 * (u - w)) / √ℓ := by ring
    have h3 : ku u * ((max (u - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) -
        ku u * ((max (w - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) =
        ku u * (((max (u - u0 ℓ + cu ℓ u) 0) ^ 2 - (max (w - u0 ℓ + cu ℓ u) 0) ^ 2) / 2) /
          √ℓ := by field_simp
    rw [h2, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hs.le
  -- the h-part
  have hh2 : 11 / ℓ * (u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2) * (u - w) ≤
      11 / ℓ * hfun u - 11 / ℓ * hfun w := by
    have h0 : 0 ≤ 11 / ℓ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hh h0]
  -- the κ-part
  have hκ : 400000000 / (u * ℓ) ≤ kappa τ / (w * ℓ) := by
    unfold kappa
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 400000000 * (w * ℓ) ≤ 400000000 * (u * ℓ) := by nlinarith
    nlinarith [mul_pos hu0 hℓ]
  have hb := betaa_ge hℓ hu
  have hA := A_self (ℓ := ℓ) hu0
  unfold BSCert.Z2.betaI BSCert.Z2.alpha
  have e2 : (11 / ℓ * u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2 +
      ku u * max (u - u0 ℓ - 1 + cu ℓ u) 0 / √ℓ) * (u - w) =
      11 / ℓ * (u ^ 3 * (3 * u - 4) * Real.log (1 + u) / (u - 1) ^ 2) * (u - w) +
      ku u * max (u - u0 ℓ - 1 + cu ℓ u) 0 / √ℓ * (u - w) := by ring
  rw [e2]
  linarith

/-- The Part II slope: `(B/ℓ) 8 (1+w)² log(2+w) + k_u (w - u₀ + c_u)₊/√ℓ`. -/
noncomputable def slopeZ (ℓ u w : ℝ) : ℝ :=
  11 / ℓ * 8 * (1 + w) ^ 2 * Real.log (2 + w) + ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ

/-- **Part II**: `D(w) ≤ β_II + slope(w) (w - u)` for `w ≥ u`. -/
lemma D_partII {τ ℓ u w : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hu : 2 ≤ u) (huw : u ≤ w) :
    Dfun τ ℓ u w ≤ BSCert.Z2.betaII ℓ u + slopeZ ℓ u w * (w - u) := by
  have hu0 : 0 < u := by linarith
  have hw0 : 0 < w := by linarith
  have hD := D_le_F (τ := τ) hℓ hu (by linarith : u - 1 ≤ w)
  have hh := h_sub_le (by linarith : (1 : ℝ) ≤ u) huw
  have hφ := (sq_pos_part_sub (u0 ℓ - cu ℓ u) u w huw).1
  have e : ∀ x, x - (u0 ℓ - cu ℓ u) = x - u0 ℓ + cu ℓ u := fun x => by ring
  simp only [e] at hφ
  have hk := ku_pos hu
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  have hφ2 : ku u * phiZ ℓ u w - ku u * phiZ ℓ u u ≤
      ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ * (w - u) := by
    unfold phiZ
    have h3 : ku u * ((max (w - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) -
        ku u * ((max (u - u0 ℓ + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) =
        ku u * (((max (w - u0 ℓ + cu ℓ u) 0) ^ 2 - (max (u - u0 ℓ + cu ℓ u) 0) ^ 2) / 2) /
          √ℓ := by field_simp
    have h2 : ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ * (w - u) =
        ku u * (max (w - u0 ℓ + cu ℓ u) 0 * (w - u)) / √ℓ := by ring
    rw [h3, h2]
    apply div_le_div_of_nonneg_right _ hs.le
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have hh2 : 11 / ℓ * hfun w - 11 / ℓ * hfun u ≤
      11 / ℓ * 8 * (1 + w) ^ 2 * Real.log (2 + w) * (w - u) := by
    have h0 : 0 ≤ 11 / ℓ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hh h0]
  have hκ : 0 ≤ kappa τ / (w * ℓ) := by unfold kappa; positivity
  have hb := betaa_ge hℓ hu
  have hA := A_self (ℓ := ℓ) hu0
  unfold BSCert.Z2.betaII slopeZ
  have e2 : (11 / ℓ * 8 * (1 + w) ^ 2 * Real.log (2 + w) +
      ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ) * (w - u) =
      11 / ℓ * 8 * (1 + w) ^ 2 * Real.log (2 + w) * (w - u) +
      ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ * (w - u) := by ring
  rw [e2]
  linarith

lemma slopeZ_mono {ℓ u w w' : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : 0 ≤ w) (hww : w ≤ w') :
    slopeZ ℓ u w ≤ slopeZ ℓ u w' := by
  unfold slopeZ
  have hk := ku_pos hu
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  have h1 : (1 + w) ^ 2 ≤ (1 + w') ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : Real.log (2 + w) ≤ Real.log (2 + w') := Real.log_le_log (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have h4 : max (w - u0 ℓ + cu ℓ u) 0 ≤ max (w' - u0 ℓ + cu ℓ u) 0 :=
    max_le_max (by linarith) le_rfl
  have h5 : 11 / ℓ * 8 * (1 + w) ^ 2 * Real.log (2 + w) ≤
      11 / ℓ * 8 * (1 + w') ^ 2 * Real.log (2 + w') := by
    have h0 : 0 ≤ 11 / ℓ * 8 := by positivity
    have := mul_le_mul h1 h2 h3 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have h6 : ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ ≤ ku u * max (w' - u0 ℓ + cu ℓ u) 0 / √ℓ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by linarith)) hs.le
  linarith

lemma slopeZ_nonneg {ℓ u w : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : 0 ≤ w) : 0 ≤ slopeZ ℓ u w := by
  unfold slopeZ
  have hk := ku_pos hu
  have : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have : 0 ≤ max (w - u0 ℓ + cu ℓ u) 0 := le_max_right _ _
  have : 0 ≤ ku u * max (w - u0 ℓ + cu ℓ u) 0 / √ℓ := by
    apply div_nonneg (mul_nonneg (by linarith) this) (Real.sqrt_nonneg _)
  positivity

lemma slopeZ_gamma1 {ℓ u : ℝ} : slopeZ ℓ u (u + 60) = BSCert.Z2.gamma1 ℓ u := by
  unfold slopeZ BSCert.Z2.gamma1; ring_nf

lemma slopeZ_gammaMax {ℓ u : ℝ} : slopeZ ℓ u (BSCert.Z2.Ubar ℓ) = BSCert.Z2.gammaMax ℓ u := by
  unfold slopeZ BSCert.Z2.gammaMax BSCert.Z2.Ubar
  have : BSCert.Z2.u0 ℓ + BSCert.Z2.UbMu0 ℓ - u0 ℓ + cu ℓ u = BSCert.Z2.UbMu0 ℓ + cu ℓ u := by
    simp only [u0]; ring
  rw [this]

lemma gamma1_nonneg {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) : 0 ≤ BSCert.Z2.gamma1 ℓ u := by
  rw [← slopeZ_gamma1]; exact slopeZ_nonneg hℓ hu (by linarith)

/-- Part II with the first slope: `D(w) ≤ β_II + γ₁ (w - u)` for `u ≤ w ≤ u + 60`. -/
lemma D_le_gamma1 {τ ℓ u w : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hu : 2 ≤ u) (huw : u ≤ w)
    (hw60 : w ≤ u + 60) :
    Dfun τ ℓ u w ≤ BSCert.Z2.betaII ℓ u + BSCert.Z2.gamma1 ℓ u * (w - u) := by
  have := D_partII hτ hℓ hu huw
  have hs := slopeZ_mono hℓ hu (by linarith) hw60
  rw [slopeZ_gamma1] at hs
  nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ w - u)]

/-- Part II with the second slope: `D(w) ≤ β_II + γ_max (w - u)` for `u ≤ w ≤ Ū`. -/
lemma D_le_gammaMax {τ ℓ u w : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 < ℓ) (hu : 2 ≤ u) (huw : u ≤ w)
    (hwU : w ≤ BSCert.Z2.Ubar ℓ) :
    Dfun τ ℓ u w ≤ BSCert.Z2.betaII ℓ u + BSCert.Z2.gammaMax ℓ u * (w - u) := by
  have := D_partII hτ hℓ hu huw
  have hs := slopeZ_mono hℓ hu (by linarith) hwU
  rw [slopeZ_gammaMax] at hs
  nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ w - u)]

/-! ## `η_f ≤ η̄` -/

lemma eta_nonneg {ℓ u w d : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : 0 ≤ w) :
    0 ≤ BSCert.Z2.eta ℓ u w d := by
  unfold BSCert.Z2.eta BSCert.Z2.kmax
  have hk := ku_pos hu
  have : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have : 0 ≤ max (d + cu ℓ u) 0 := le_max_right _ _
  have : 0 ≤ ku u * ((max (d + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) / ℓ := by
    apply div_nonneg (mul_nonneg (by linarith) (by positivity)) hℓ.le
  positivity

/-- `η̄(w, d)` is non-decreasing in `w ≥ 0` and in `d`. -/
lemma eta_mono {ℓ u w w' d d' : ℝ} (hℓ : 0 < ℓ) (hu : 2 ≤ u) (hw : 0 ≤ w) (hww : w ≤ w')
    (hdd : d ≤ d') : BSCert.Z2.eta ℓ u w d ≤ BSCert.Z2.eta ℓ u w' d' := by
  have hw' : 0 ≤ w' := le_trans hw hww
  unfold BSCert.Z2.eta
  have hk := ku_pos hu
  have hL : Real.log (2 + w) ≤ Real.log (2 + w') := Real.log_le_log (by linarith) (by linarith)
  have hL0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hD : max (d + cu ℓ u) 0 ≤ max (d' + cu ℓ u) 0 := max_le_max (by linarith) le_rfl
  have hD0 : 0 ≤ max (d + cu ℓ u) 0 := le_max_right _ _
  have h1 : (1 + w) ^ 2 ≤ (1 + w') ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h1' : (1 + w) ^ 3 ≤ (1 + w') ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  have t2 : 4 * (11 * (1 + w) ^ 3 * Real.log (2 + w) / ℓ) / ℓ ≤
      4 * (11 * (1 + w') ^ 3 * Real.log (2 + w') / ℓ) / ℓ := by
    gcongr
  have t3 : max (d + cu ℓ u) 0 / (4 * (ℓ / 2) * √(√(ℓ / 2))) ≤
      max (d' + cu ℓ u) 0 / (4 * (ℓ / 2) * √(√(ℓ / 2))) :=
    div_le_div_of_nonneg_right hD (by positivity)
  have t4 : ku u * ((max (d + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) / ℓ ≤
      ku u * ((max (d' + cu ℓ u) 0) ^ 2 / (2 * √ℓ)) / ℓ := by
    gcongr
  have t5 : (1 + w) ^ 2 / ℓ * (2 * 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) / ℓ
      + √2 * max (d + cu ℓ u) 0 / √ℓ) ≤ (1 + w') ^ 2 / ℓ * (2 * 11 * (1 + w') ^ 2 *
        (3 * Real.log (2 + w') + 1) / ℓ + √2 * max (d' + cu ℓ u) 0 / √ℓ) := by
    gcongr
  linarith

lemma cube_aux {ℓ m y k : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hk : 2 * k = 2 + y) (hratio : ℓ ≤ (1 + y) * m) : ℓ * √ℓ ≤ 2 * k * (m * √m) := by
  have hp : (1 + y) ^ 3 ≤ (2 + y) ^ 2 := by
    have h2 : y ^ 2 ≤ 1 := by nlinarith
    have h3 : y ^ 3 ≤ 1 := by nlinarith
    nlinarith
  have hsq : (ℓ * √ℓ) ^ 2 ≤ (2 * k * (m * √m)) ^ 2 := by
    have e1 : (ℓ * √ℓ) ^ 2 = ℓ ^ 3 := by rw [mul_pow, Real.sq_sqrt hℓ.le]; ring
    have e2 : (2 * k * (m * √m)) ^ 2 = (2 * k) ^ 2 * m ^ 3 := by
      rw [mul_pow (2 * k), mul_pow m, Real.sq_sqrt hm.le]; ring
    rw [e1, e2, hk]
    have h3 : ℓ ^ 3 ≤ ((1 + y) * m) ^ 3 := pow_le_pow_left₀ hℓ.le hratio 3
    rw [mul_pow] at h3
    have hm3 : 0 ≤ m ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hp hm3]
  have h2k : 0 ≤ 2 * k * (m * √m) := by
    rw [hk]; positivity
  exact (pow_le_pow_iff_left₀ (by positivity) h2k two_ne_zero).mp hsq

/-- `η_f(w) ≤ η̄(w, w - u₀)` for `w ≥ u - 1`, `u ≥ 2`, `30τ < ℓ`. -/
lemma etaF_le_eta {τ ℓ u w : ℝ} (hτ : 0 ≤ τ) (hℓτ : 30 * τ < ℓ) (hu : 2 ≤ u)
    (hw : u - 1 ≤ w) : etaF τ ℓ w ≤ BSCert.Z2.eta ℓ u w (w - u0 ℓ) := by
  have hℓ : 0 < ℓ := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  set m := mOf ℓ w with hmdef
  have hm2 : ℓ / 2 ≤ m := mOf_ge_half hℓ hw1
  have hm : 0 < m := by linarith
  have hmℓ : m ≤ ℓ := mOf_le hℓ hw0.le
  have hd := dpos_le hℓ hu hw
  rw [← hmdef] at hd
  set d := dpos m w
  set D := max (w - u0 ℓ + cu ℓ u) 0
  have hd0 : 0 ≤ d := le_max_right _ _
  have hk := ku_pos hu
  have hL0 : 0 ≤ Real.log (2 + w) := Real.log_nonneg (by linarith)
  have hs : 0 < √ℓ := Real.sqrt_pos.mpr hℓ
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  unfold etaF BSCert.Z2.eta
  simp only [← hmdef]
  have e1 : w - u0 ℓ + cu ℓ u = w - u0 ℓ + cu ℓ u := rfl
  -- term 1: κ_Φ/m² ≤ 4 κ_max/ℓ²
  have t1 : kappa τ / m ^ 2 ≤ 4 * BSCert.Z2.kmax ℓ / (ℓ * ℓ) := by
    unfold kappa BSCert.Z2.kmax
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ℓ * ℓ ≤ 4 * m ^ 2 := by nlinarith
    have hk1 : 4 * τ + 1500 ≤ 4 * ℓ / 30 + 1500 := by linarith
    nlinarith [mul_le_mul hk1 this (by positivity) (by positivity)]
  -- term 2
  have t2 : BSCert.Z2.A m w / m ≤ 4 * (11 * (1 + w) ^ 3 * Real.log (2 + w) / ℓ) / ℓ := by
    unfold BSCert.Z2.A
    set X := 11 * (1 + w) ^ 3 * Real.log (2 + w)
    rw [show X / m / m = X / (m * m) by ring, show 4 * (X / ℓ) / ℓ = 4 * X / (ℓ * ℓ) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : ℓ * ℓ ≤ 4 * (m * m) := by nlinarith
    have hp : 0 ≤ X := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  -- term 3
  have t3 : d / (4 * (m * u0 m)) ≤ D / (4 * (ℓ / 2) * √(√(ℓ / 2))) := by
    have hu0m : u0 (ℓ / 2) ≤ u0 m := u0_mono hm2
    have hpos : 0 < 4 * (ℓ / 2) * √(√(ℓ / 2)) := by
      have := u0_pos (by linarith : 0 < ℓ / 2); simp only [u0, BSCert.Z2.u0] at this
      positivity
    have hle : 4 * (ℓ / 2) * √(√(ℓ / 2)) ≤ 4 * (m * u0 m) := by
      have : √(√(ℓ / 2)) = u0 (ℓ / 2) := rfl
      rw [this]
      have := u0_pos (by linarith : 0 < ℓ / 2)
      nlinarith [mul_le_mul hm2 hu0m this.le hm.le]
    calc d / (4 * (m * u0 m)) ≤ d / (4 * (ℓ / 2) * √(√(ℓ / 2))) :=
          div_le_div_of_nonneg_left hd0 hpos hle
      _ ≤ D / (4 * (ℓ / 2) * √(√(ℓ / 2))) := div_le_div_of_nonneg_right hd hpos.le
  -- term 4: `ℓ√ℓ ≤ 2 k_u m√m`
  have t4 : d ^ 2 / (4 * (m * √m)) ≤ ku u * (D ^ 2 / (2 * √ℓ)) / ℓ := by
    have hcube : ℓ * √ℓ ≤ 2 * ku u * (m * √m) := by
      have hy : 1 / w ≤ 1 / (u - 1) := one_div_le_one_div_of_le (by linarith) hw
      have hy0 : 0 < 1 / (u - 1) := by apply div_pos one_pos; linarith
      have hy1 : 1 / (u - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      set y := 1 / (u - 1)
      have hku : 2 * ku u = 2 + y := by
        unfold ku; rw [show y = 1 / (u - 1) from rfl]; field_simp
      -- (ℓ/m) = (1+w)/w = 1 + 1/w ≤ 1 + y
      have hratio : ℓ ≤ (1 + y) * m := by
        rw [hmdef]; unfold mOf
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        have : (1 + 1 / w) * w = 1 + w := by rw [add_mul, one_div, inv_mul_cancel₀ hw0.ne']; ring
        nlinarith [mul_le_mul_of_nonneg_left hy hℓ.le]
      exact cube_aux hℓ hm hy0.le hy1 hku hratio
    have hD2 : d ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hd0 hd 2
    have hpos : 0 < 4 * (m * √m) := by positivity
    calc d ^ 2 / (4 * (m * √m)) ≤ D ^ 2 / (4 * (m * √m)) :=
          div_le_div_of_nonneg_right hD2 hpos.le
      _ ≤ ku u * (D ^ 2 / (2 * √ℓ)) / ℓ := by
        rw [div_le_iff₀ hpos]
        have e : ku u * (D ^ 2 / (2 * √ℓ)) / ℓ * (4 * (m * √m)) =
            D ^ 2 * (2 * ku u * (m * √m)) / (ℓ * √ℓ) := by field_simp; ring
        rw [e, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hcube (sq_nonneg _)
  -- term 5
  have t5 : (1 + w) ^ 2 / ℓ * (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w))
      / m + d / √m) ≤ (1 + w) ^ 2 / ℓ * (2 * 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) / ℓ
        + √2 * D / √ℓ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hfrac : (1 + w) ^ 3 / (2 + w) ≤ (1 + w) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (1 + w)]
    have ha : 11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m ≤
        2 * 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) / ℓ := by
      set X := 11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w))
      have h0 : 0 ≤ X := by positivity
      have h1 : X ≤ 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) := by
        have e1 : X = 33 * ((1 + w) ^ 2 * Real.log (2 + w)) + 11 * ((1 + w) ^ 3 / (2 + w)) := by
          simp only [X]; ring
        have e2 : 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) =
            33 * ((1 + w) ^ 2 * Real.log (2 + w)) + 11 * (1 + w) ^ 2 := by ring
        rw [e1, e2]; linarith
      calc X / m ≤ 2 * X / ℓ := by
            rw [div_le_div_iff₀ hm hℓ]; nlinarith [mul_le_mul_of_nonneg_left hm2 h0]
        _ ≤ 2 * 11 * (1 + w) ^ 2 * (3 * Real.log (2 + w) + 1) / ℓ :=
            div_le_div_of_nonneg_right (by linarith) hℓ.le
    have hb : d / √m ≤ √2 * D / √ℓ := by
      have h2 : √ℓ ≤ √2 * √m := by
        rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
      rw [div_le_div_iff₀ hsm hs]
      calc d * √ℓ ≤ D * (√2 * √m) := mul_le_mul hd h2 hs.le (le_max_right _ _)
        _ = √2 * D * √m := by ring
    exact add_le_add ha hb
  have := add_le_add (add_le_add (add_le_add t1 t2) (add_le_add t3 t4)) t5
  refine this.trans (le_of_eq ?_)
  ring

end BSaias

end
