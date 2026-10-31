module

public import RequestProject.Beurling.InitialRange
public import RequestProject.BSCert.CaplMono
public import RequestProject.Beurling.Construction.LandingDerive

/-!
# The jitter width varies slowly (Theorem 6.23(c)): `JitterWidthRegular` is a theorem

`Construction.JitterWidthRegular X₀` (if `X₀ ≤ x ≤ y` and `y - H(y)/2 ≤ x` then
`H(y) ≤ H(x) + 1/4`) was a conjunct of `Theorem21InputsO`. Here it is **proved** for the paper's
`H = max(H_std, M̄₁²)` and `log X₀ ≥ 10⁸`:

* `BSCert.Capl.G_lip`, `gstar_lip`, `gam_lip` : `γ` is locally Lipschitz,
  `γ(t) - γ(s) ≤ 8 (t - s)` for `s ≤ t ≤ s + 10⁻³`;
* `JitterRegular.capH_regular` : the statement for real `X₀`, with `H(y) ≤ e^{48Δ} H(x)`,
  `Δ = log y - log x ≤ x^{-7/8}`;
* `Construction.jitterWidthRegular` : `JitterWidthRegular X₀` for `log X₀ ≥ 10⁸`;
* `Construction.Theorem21InputsP` : `Theorem21InputsO` without the conjunct
  `JitterWidthRegular X₀`, and Theorem 2.1 / Corollary 2.2 from it.
-/

@[expose] public section

namespace BSCert.Capl

open Real

lemma exp_le_one_add_two {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : Real.exp u ≤ 1 + 2 * u := by
  have h := Real.abs_exp_sub_one_le (x := u) (by rw [abs_of_nonneg hu0]; exact hu1)
  rw [abs_of_nonneg hu0] at h
  have := (le_abs_self (Real.exp u - 1)).trans h
  linarith

set_option maxHeartbeats 2000000 in
/-- **Local Lipschitz bound for `G(Λ_s, s)`**: `G(Λ_t, t) ≤ G(Λ_s, s) (1 + 4 (t - s))` for
`s ≤ t ≤ 6`, `t - s ≤ 10⁻³`. -/
lemma G_lip {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 6) (hδ : t - s ≤ 1 / 1000) :
    G (LamS t) t ≤ G (LamS s) s * (1 + 4 * (t - s)) := by
  set δ := t - s with hδdef
  have hδ0 : 0 ≤ δ := by linarith
  set Λ := LamS s with hΛdef
  set Λ' := LamS t with hΛ'def
  have hΛ : 100000000 ≤ Λ := LamS_ge s
  have hΛ' : 100000000 ≤ Λ' := LamS_ge t
  have hs : -Real.log Λ ≤ s := neg_log_LamS_le s
  have ht' : -Real.log Λ' ≤ t := neg_log_LamS_le t
  have hΛΛ : Λ' ≤ Λ := LamS_anti hst
  have hlow : Λ * Real.exp (-δ) ≤ Λ' := by
    rw [hΛdef, hΛ'def]; unfold LamS
    rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le]
    apply max_le_max
    · have : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    · rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hΛ0 : 0 < Λ := by linarith
  have hΛ'0 : 0 < Λ' := by linarith
  have hlow1 : Λ * (1 - δ) ≤ Λ' := by
    have := Real.add_one_le_exp (-δ)
    nlinarith
  have hlogΛ : Real.log Λ - δ ≤ Real.log Λ' := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul hΛ0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    linarith
  have hlogΛΛ : Real.log Λ' ≤ Real.log Λ := Real.log_le_log hΛ'0 hΛΛ
  have hL := log_ge_18 hΛ
  have hL' := log_ge_18 hΛ'
  set ℓ := 2 * Real.log Λ + s with hℓ
  set ℓ' := 2 * Real.log Λ' + t with hℓ'
  have hl0 : 0 < ℓ := by linarith
  have hl0' : 18 ≤ ℓ' := by linarith
  set a := A Λ s with ha
  set a' := A Λ' t with ha'
  have ea : a = Real.log 2 + 3 * Real.log Λ + 2 * s - Real.log ℓ := A_eq hΛ0 hl0
  have ea' : a' = Real.log 2 + 3 * Real.log Λ' + 2 * t - Real.log ℓ' := A_eq hΛ'0 (by linarith)
  have hlogl : Real.log ℓ - Real.log ℓ' ≤ δ := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hl0 (by linarith : 0 < ℓ'))
    rw [Real.log_div hl0.ne' (by linarith)] at h1
    have h2 : ℓ / ℓ' - 1 ≤ δ := by
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have haa : a' ≤ a + 3 * δ := by rw [ea, ea']; linarith
  have hA6 : 6 ≤ a := A_ge_six hΛ hs
  have hA6' : 6 ≤ a' := A_ge_six hΛ' ht'
  have hAup : a ≤ 3 * Real.log Λ + 13 := A_le_lin hΛ hs (by linarith)
  have hlog8 := log_le_eighth hΛ0
  set D := Λ - a - 1 with hD
  have hD2 : Λ / 2 ≤ D := by rw [hD]; linarith
  set D' := Λ' - a' - 1 with hD'
  have hDD : D * (1 - 3 * δ) ≤ D' := by
    have h1 : δ * Λ + 3 * δ ≤ 3 * δ * D := by nlinarith [mul_le_mul_of_nonneg_left hD2 hδ0]
    have h2 : D' = Λ' - a' - 1 := hD'
    have h3 : D = Λ - a - 1 := hD
    rw [h2]; rw [h3] at h1 ⊢; nlinarith
  have hD0 : 0 < D := by linarith
  have hD'0 : 0 < D' := lt_of_lt_of_le (mul_pos hD0 (by linarith)) hDD
  have hN : a' * (a' + 1) ≤ a * (a + 1) * (1 + 2 * δ) := by
    have h1 : a' * (a' + 1) ≤ (a + 3 * δ) * (a + 3 * δ + 1) :=
      mul_le_mul haa (by linarith) (by linarith) (by linarith)
    have h2 : 0 ≤ 2 * a ^ 2 - 4 * a - 3 - 9 * δ := by nlinarith
    have h3 : 0 ≤ δ * (2 * a ^ 2 - 4 * a - 3 - 9 * δ) := mul_nonneg hδ0 h2
    have h4 : (a + 3 * δ) * (a + 3 * δ + 1) + δ * (2 * a ^ 2 - 4 * a - 3 - 9 * δ) =
        a * (a + 1) * (1 + 2 * δ) := by ring
    linarith
  have hE : Real.exp t ≤ Real.exp s * (1 + 2 * δ) := by
    have : Real.exp t = Real.exp s * Real.exp δ := by rw [← Real.exp_add, hδdef]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_left (exp_le_one_add_two hδ0 (by linarith)) (Real.exp_pos _).le
  rw [G_eq_sqrt (by linarith) hD'0, G_eq_sqrt (by linarith) hD0]
  rw [← hD, ← hD']
  set X := a * (a + 1) * Real.exp s / D with hX
  have hX0 : 0 ≤ X := by positivity
  have hXD : X * D = a * (a + 1) * Real.exp s := by rw [hX, div_mul_cancel₀ _ hD0.ne']
  have hkey : a' * (a' + 1) * Real.exp t / D' ≤ X * (1 + 4 * δ) ^ 2 := by
    rw [div_le_iff₀ hD'0]
    have hes := Real.exp_pos s
    have hNN : 0 ≤ a' * (a' + 1) := mul_nonneg (by linarith) (by linarith)
    have hpoly : (1 + 2 * δ) ^ 2 ≤ (1 + 4 * δ) ^ 2 * (1 - 3 * δ) := by
      have e : (1 + 4 * δ) ^ 2 * (1 - 3 * δ) - (1 + 2 * δ) ^ 2 = δ * (1 - 12 * δ - 48 * δ ^ 2) :=
        by ring
      have : 0 ≤ δ * (1 - 12 * δ - 48 * δ ^ 2) := mul_nonneg hδ0 (by nlinarith)
      linarith
    calc a' * (a' + 1) * Real.exp t
        ≤ a * (a + 1) * (1 + 2 * δ) * (Real.exp s * (1 + 2 * δ)) :=
          mul_le_mul hN hE (Real.exp_pos _).le (by nlinarith)
      _ = X * D * (1 + 2 * δ) ^ 2 := by rw [hXD]; ring
      _ ≤ X * D * ((1 + 4 * δ) ^ 2 * (1 - 3 * δ)) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = X * (1 + 4 * δ) ^ 2 * (D * (1 - 3 * δ)) := by ring
      _ ≤ X * (1 + 4 * δ) ^ 2 * D' := mul_le_mul_of_nonneg_left hDD (by positivity)
  have hs2 := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_mul hX0, Real.sqrt_sq (by linarith)] at hs2
  linarith

/-- `γ*(t) - γ*(s) ≤ 2 (t - s)` for `s ≤ t ≤ 6`, `t - s ≤ 10⁻³`, `γ*(s) ≤ 1/3`. -/
lemma gstar_lip {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 6) (hδ : t - s ≤ 1 / 1000)
    (hg : gstar s ≤ 1 / 3) : gstar t - gstar s ≤ 2 * (t - s) := by
  have h := G_lip hst ht hδ
  unfold gstar at hg ⊢
  nlinarith [mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ 4 * (t - s))]

/-- **`γ` is locally Lipschitz**: `γ(t) - γ(s) ≤ 8 (t - s)` for `s ≤ t ≤ s + 10⁻³`, for a break
point `s_H ≤ 6` with `0 ≤ γ*(s_H) ≤ 1/3`. -/
theorem gam_lip {sH s t : ℝ} (hsH : sH ≤ 6) (hg0 : 0 ≤ gstar sH) (hg : gstar sH ≤ 1 / 3)
    (hst : s ≤ t) (hδ : t - s ≤ 1 / 1000) : gam sH t - gam sH s ≤ 8 * (t - s) := by
  unfold gam
  by_cases hs : s ≤ sH
  · have hgs : gstar s ≤ 1 / 3 := (gstar_mono hs hsH).trans hg
    rw [if_pos hs]
    by_cases ht : t ≤ sH
    · rw [if_pos ht]
      have := gstar_lip hst (ht.trans hsH) hδ hgs
      linarith
    · rw [if_neg ht, if_pos (by linarith)]
      push_neg at ht
      have h1 := gstar_lip hs hsH (by linarith) hgs
      have h2 : (7.5 - gstar sH) * (t - sH) ≤ 7.5 * (t - sH) := by nlinarith
      linarith
  · push_neg at hs
    rw [if_neg (by linarith), if_neg (not_le.mpr hs)]
    by_cases hs1 : s ≤ sH + 1
    · rw [if_pos hs1]
      by_cases ht1 : t ≤ sH + 1
      · rw [if_pos ht1]
        have h2 : (7.5 - gstar sH) * (t - s) ≤ 7.5 * (t - s) := by nlinarith
        nlinarith
      · rw [if_neg ht1]
        push_neg at ht1
        have h2 : (7.5 - gstar sH) * (sH + 1 - s) ≤ 7.5 * (t - s) := by nlinarith
        nlinarith
    · rw [if_neg hs1, if_neg (by linarith)]
      linarith

end BSCert.Capl

namespace JitterRegular

open Real CaplLink BSCert.Capl

set_option maxHeartbeats 4000000 in
/-- **The jitter width varies slowly**: for `log X₀ ≥ 10⁸`, `X₀ ≤ x ≤ y` and `y - H(y)/2 ≤ x`,
`H(y) ≤ H(x) + 1/4`. With `w = x^{1/8}` one has `y - x ≤ H(y)/2 ≤ w`, so
`Δ = log y - log x ≤ w^{-7}`; then `H(y) ≤ e^{48Δ} H(x) ≤ (1 + 96Δ) H(x)` and
`96 Δ H(x) ≤ 96 w^{-6}`. -/
theorem capH_regular {X₀ x y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxy : x ≤ y) (hy : y - capH X₀ y / 2 ≤ x) : capH X₀ y ≤ capH X₀ x + 1 / 4 := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hyX : X₀ ≤ y := hx.trans hxy
  obtain ⟨hLx, hℓΛx, hℓx⟩ := logs_of_ge hX0 hX hx
  obtain ⟨hLy, hℓΛy, hℓy⟩ := logs_of_ge hX0 hX hyX
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hHx := InitialRange.capH_le_rpow hX0 hX hx
  have hHy := InitialRange.capH_le_rpow hX0 hX hyX
  have hHx0 : 0 ≤ capH X₀ x := le_trans (Real.exp_pos _).le (le_max_left _ _)
  -- `w = x^{1/8}`, `v = y^{1/8}`
  set w := x ^ (1 / 8 : ℝ) with hw
  set v := y ^ (1 / 8 : ℝ) with hv
  have hw8 : w ^ 8 = x := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hv8 : v ^ 8 = y := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hwv : w ≤ v := Real.rpow_le_rpow hx0.le hxy (by norm_num)
  have hxbig : 6561 ≤ x := by
    have h1 : Real.exp (10 ^ 8) ≤ x := by
      rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hLx
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  have hw3 : 3 ≤ w := by
    by_contra hc; push_neg at hc
    have hw0 : 0 ≤ w := Real.rpow_nonneg hx0.le _
    have : w ^ 8 < 3 ^ 8 := by gcongr
    norm_num at this; linarith
  have hv1 : 1 ≤ v := by linarith
  have hyx : y - x ≤ v / 2 := by linarith
  have hv2 : v ≤ 2 * w := by
    by_contra hc; push_neg at hc
    have h1 : 256 * w ^ 8 < v ^ 8 := by
      have : (2 * w) ^ 8 < v ^ 8 := by gcongr
      nlinarith
    have h2 : v ≤ v ^ 8 := by
      calc v = v ^ 1 := (pow_one v).symm
        _ ≤ v ^ 8 := pow_le_pow_right₀ hv1 (by norm_num)
    nlinarith
  -- `Δ = log y - log x ≤ w^{-7}`
  set Lx := Real.log x with hLxdef
  set Ly := Real.log y with hLydef
  set Δ := Ly - Lx with hΔdef
  have hΔ0 : 0 ≤ Δ := by
    have := Real.log_le_log hx0 hxy; rw [hΔdef]; linarith
  have hΔx : Δ * x ≤ y - x := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h1
    have h2 : (y / x - 1) * x = y - x := by field_simp
    nlinarith
  have hw0 : 0 < w := by linarith
  have hΔw7 : Δ * w ^ 7 ≤ 1 := by
    have : Δ * w ^ 8 ≤ w := by rw [hw8]; linarith
    have e : Δ * w ^ 8 = (Δ * w ^ 7) * w := by ring
    rw [e] at this
    nlinarith
  have hw6 : 729 ≤ w ^ 6 := by
    have : (3 : ℝ) ^ 6 ≤ w ^ 6 := by gcongr
    norm_num at this; linarith
  have hΔw : Δ * w ≤ 1 / 729 := by
    have e : Δ * w ^ 7 = (Δ * w) * w ^ 6 := by ring
    rw [e] at hΔw7
    have : (Δ * w) * 729 ≤ (Δ * w) * w ^ 6 :=
      mul_le_mul_of_nonneg_left hw6 (mul_nonneg hΔ0 hw0.le)
    linarith
  have hΔs : Δ ≤ 1 / 2187 := by
    have : Δ * 3 ≤ Δ * w := mul_le_mul_of_nonneg_left hw3 hΔ0
    linarith
  -- `ℓ`
  set ℓx := Real.log Lx with hℓxdef
  set ℓy := Real.log Ly with hℓydef
  set δ := ℓy - ℓx with hδdef
  have hLx0 : 0 < Lx := by linarith
  have hLy0 : 0 < Ly := by linarith
  have hδ0 : 0 ≤ δ := by
    have := Real.log_le_log hLx0 (by linarith : Lx ≤ Ly); rw [hδdef]; linarith
  have hδL : δ * Lx ≤ Δ := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hLy0 hLx0)
    rw [Real.log_div hLy0.ne' hLx0.ne'] at h1
    have h2 : (Ly / Lx - 1) * Lx = Δ := by rw [hΔdef]; field_simp
    nlinarith
  have hδΔ : δ ≤ Δ := by nlinarith
  have hℓxL : ℓx ≤ Lx := by
    have := Real.log_le_sub_one_of_pos hLx0; linarith
  have hℓyL : ℓy ≤ Ly := by
    have := Real.log_le_sub_one_of_pos hLy0; linarith
  have hsq : ℓy ^ 2 ≤ ℓx ^ 2 + 3 * Δ := by
    have e : ℓy ^ 2 - ℓx ^ 2 = δ * (ℓy + ℓx) := by rw [hδdef]; ring
    have h1 : δ * (ℓy + ℓx) ≤ δ * (3 * Lx) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hδ0
    nlinarith
  set Λ := Real.log X₀ with hΛdef
  have hΛL : Λ ≤ Lx := Real.log_le_log (by linarith) hx
  have hΛ0 : 0 ≤ Λ := by linarith
  have hδΛ : δ * Λ ≤ Δ := le_trans (mul_le_mul_of_nonneg_left hΛL hδ0) hδL
  -- the capacity parameters
  set sx := capS X₀ x with hsx
  set sy := capS X₀ y with hsy
  have eℓx : 2 * Real.log Λ + sx = ℓx := ell_eq X₀ x
  have eℓy : 2 * Real.log Λ + sy = ℓy := ell_eq X₀ y
  have hss : sy - sx = δ := by linarith
  have hsH := sHroot_mem
  have hgH : gstar sHroot = 1 / 3 - 1 / 100000 := by rw [gstar_sHroot]; rfl
  have hgam := gam_lip (sH := sHroot) (s := sx) (t := sy) (by linarith [hsH.2])
    (by rw [hgH]; norm_num) (by rw [hgH]; norm_num) (by linarith) (by linarith)
  -- `ρ = e^{12Δ}`
  set ρ := Real.exp (12 * Δ) with hρ
  have hρ1 : 1 + Δ ≤ ρ := by
    have := Real.add_one_le_exp (12 * Δ); linarith
  have hlogc : logc sHroot Λ sy ≤ logc sHroot Λ sx + 12 * Δ := by
    unfold logc
    rw [eℓx, eℓy]
    apply max_le
    · have := le_max_left (4 * ℓx ^ 2 - Real.log 4) (gam sHroot sx * Λ)
      linarith
    · have := le_max_right (4 * ℓx ^ 2 - Real.log 4) (gam sHroot sx * Λ)
      have h1 : (gam sHroot sy - gam sHroot sx) * Λ ≤ 8 * δ * Λ := by
        rw [← hss]; exact mul_le_mul_of_nonneg_right hgam hΛ0
      nlinarith
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1' : 1 ≤ ρ := by linarith
  set cx := Real.exp (logc sHroot Λ sx) with hcx
  set cy := Real.exp (logc sHroot Λ sy) with hcy
  have hcxy : cy ≤ ρ * cx := by
    rw [hcy, hcx, hρ, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hcx0 : 0 < cx := Real.exp_pos _
  set rx := rbar0 Λ sx with hrx
  set ry := rbar0 Λ sy with hry
  have erx : rx = Lx / (3 * ℓx) + 4 := by
    rw [hrx]; unfold rbar0; rw [eℓx, Real.exp_log hLx0]
  have ery : ry = Ly / (3 * ℓy) + 4 := by
    rw [hry]; unfold rbar0; rw [eℓy, Real.exp_log hLy0]
  have hℓxy : ℓx ≤ ℓy := by linarith
  have hrx0 : 0 ≤ rx := by rw [erx]; positivity
  have hrxy : ry ≤ ρ * rx := by
    rw [ery, erx]
    have h1 : Ly / (3 * ℓy) ≤ Ly / (3 * ℓx) :=
      div_le_div_of_nonneg_left hLy0.le (by positivity) (by linarith)
    have h2 : Ly / (3 * ℓx) ≤ (1 + Δ) * (Lx / (3 * ℓx)) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [hΔdef]; nlinarith
    have h3 : (1 + Δ) * (Lx / (3 * ℓx)) ≤ ρ * (Lx / (3 * ℓx)) :=
      mul_le_mul_of_nonneg_right hρ1 (by positivity)
    linarith
  -- `M̄₁(y) ≤ ρ² M̄₁(x)`
  have hM : capM1 X₀ y ≤ ρ ^ 2 * capM1 X₀ x := by
    unfold capM1 Mbar1
    simp only
    rw [← hsx, ← hsy, ← hΛdef, ← hcx, ← hcy, ← hrx, ← hry]
    have hry0 : 0 ≤ ry := by rw [ery]; positivity
    have hρρ : ρ ≤ ρ ^ 2 := by nlinarith
    have hsc : Real.sqrt cy ≤ ρ * Real.sqrt cx := by
      have : cy ≤ ρ ^ 2 * cx := le_trans hcxy (mul_le_mul_of_nonneg_right hρρ hcx0.le)
      have h := Real.sqrt_le_sqrt this
      rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ0.le] at h
    have hq0 := Real.sqrt_nonneg cx
    have h1 : ry * Real.sqrt cy ≤ ρ * rx * (ρ * Real.sqrt cx) :=
      mul_le_mul hrxy hsc (Real.sqrt_nonneg _) (by positivity)
    have h2 : ry * (ry + 1) ≤ ρ * rx * (ρ * rx + ρ) :=
      mul_le_mul hrxy (by linarith) (by linarith) (by positivity)
    have h3 : ρ * rx ≤ ρ ^ 2 * rx := mul_le_mul_of_nonneg_right hρρ hrx0
    have h4 : ρ * cx ≤ ρ ^ 2 * cx := mul_le_mul_of_nonneg_right hρρ hcx0.le
    have h5 : 1 ≤ ρ ^ 2 := by linarith
    linarith
  have hM0 : 0 < capM1 X₀ y := capM1_pos hX0 hX hyX
  have hH : capH X₀ y ≤ ρ ^ 4 * capH X₀ x := by
    unfold capH
    have hρ4 : 0 ≤ ρ ^ 4 := by positivity
    apply max_le
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hρ4)
      rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right _ _) hρ4)
      have := pow_le_pow_left₀ hM0.le hM 2
      calc capM1 X₀ y ^ 2 ≤ (ρ ^ 2 * capM1 X₀ x) ^ 2 := this
        _ = ρ ^ 4 * capM1 X₀ x ^ 2 := by ring
  have hρ4 : ρ ^ 4 ≤ 1 + 96 * Δ := by
    have e : ρ ^ 4 = Real.exp (48 * Δ) := by
      rw [hρ, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    have := exp_le_one_add_two (u := 48 * Δ) (by positivity) (by linarith)
    linarith
  have h1 : ρ ^ 4 * capH X₀ x ≤ (1 + 96 * Δ) * capH X₀ x :=
    mul_le_mul_of_nonneg_right hρ4 hHx0
  have h2 : Δ * capH X₀ x ≤ Δ * w := mul_le_mul_of_nonneg_left hHx hΔ0
  linarith

end JitterRegular

namespace Construction

open CaplLink

/-- **`JitterWidthRegular` holds** for `log X₀ ≥ 10⁸`. -/
theorem jitterWidthRegular {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) : JitterWidthRegular X₀ :=
  fun _ _ hx hxy hy => JitterRegular.capH_regular (Nat.cast_nonneg _) hX hx hxy hy

/-- **Theorem 2.1, hypothesis on the concrete construction**: `Theorem21InputsO` without the
conjunct `JitterWidthRegular X₀`, which is now a theorem (`jitterWidthRegular`). -/
def Theorem21InputsP : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (M : JitterΩ → SlotModel X₀) (ι : Type) (_ : Countable ι) (E : ι → Set JitterΩ)
      (time : ι → ℕ),
      (∃ scale : ι → ℕ, TableBudget jitterMeasure X₀ E time scale) ∧
      ∀ ω ∈ goodAll E, (∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) →
        ArrivalsLinked (M ω) (capH X₀) ω ∧ SlotFacts (M ω) ω ∧
        PartIRestO θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) (constructionScale X₀) (M ω) ∧
        Theorem410RestM θ X₀ (realisedSystem (M ω) (capH X₀) ω) (realisedA (M ω) (capH X₀) ω)
          (fun n => solveU (thetaB θ) n) ∧
        ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem (M ω) (capH X₀) ω) X₀
          (4 * v / Real.log v ^ 11) (capM1 X₀ v)

/-- `Theorem21InputsP` implies `Theorem21InputsO`. -/
theorem theorem21InputsO_of_P (h : Theorem21InputsP) : Theorem21InputsO := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ⟨?_, hX X₀ hev h1 h2⟩⟩
  apply jitterWidthRegular
  have := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at this

/-- Theorem 2.1 from `Theorem21InputsP`. -/
theorem theorem21_of_P (h : Theorem21InputsP) : Theorem21 :=
  theorem21_of_O (theorem21InputsO_of_P h)

/-- **Corollary 2.2** from `Theorem21InputsP`. -/
theorem corollary_2_2_of_P (h : Theorem21InputsP) : ¬ QuestionQ :=
  corollary_2_2_of_O (theorem21InputsO_of_P h)

end Construction

end
