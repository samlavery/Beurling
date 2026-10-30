module

public import RequestProject.Beurling.LocalPNT.Rect

/-!
# Step 8 of the proof of Theorem 5.24: `|𝔊₁| ≤ 190 Y(t)` on the discs

For `1/16 ≤ |t| ≤ T₁`, `s₁ = 1 + η_t + it`, `δ_t = η_t/3.79`, `R₁ = η_t + 0.95 δ_t` and
`r₁ = η_t + 0.9 δ_t`: Borel–Carathéodory for `log ζ^♯ - log ζ^♯(s₁)` on `|s - s₁| < R₁`
(where `Re ≤ log M₁ ≤ Y(t)`, Step 7) gives `|𝔊₁(s)| ≤ 190 Y(t)` for `|s - s₁| ≤ r₁`, `s ∈ U`.
-/

@[expose] public section

open Set Real Complex Metric Construction Decomp Filter Topology

namespace LocalPNT

/-- `Y(t') ≤ Y(t) + (|t'| - |t|)` for `|t| ≤ |t'|`. -/
lemma Yt_le_add {Λ t t' : ℝ} (hΛ : 1 ≤ Λ) (h : |t| ≤ |t'|) :
    Yt Λ t' ≤ Yt Λ t + (|t'| - |t|) := by
  unfold Yt
  have ha := abs_nonneg t
  have h1 : Lt t' - Lt t ≤ (|t'| - |t|) / 3 := by
    unfold Lt
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < (|t'| + 3) / (|t| + 3) by positivity)
    have e : (|t'| + 3) / (|t| + 3) - 1 = (|t'| - |t|) / (|t| + 3) := by field_simp; ring
    rw [e] at this
    have : (|t'| - |t|) / (|t| + 3) ≤ (|t'| - |t|) / 3 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
    linarith
  have hL0 := Lt_nonneg t
  have hlΛ := Real.log_nonneg hΛ
  set X := Lt t + 442 + 2 * Real.log Λ
  set X' := Lt t' + 442 + 2 * Real.log Λ
  have hXX : X ≤ X' := by have := Lt_mono h; simp only [X, X']; linarith
  have h2 : Real.log X' - Real.log X ≤ (X' - X) / X := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < X' / X by apply div_pos <;> linarith)
    have hX0 : X ≠ 0 := by linarith
    have e : X' / X - 1 = (X' - X) / X := by rw [sub_div, div_self hX0]
    linarith
  have h3 : (X' - X) / X ≤ (X' - X) / 442 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have : X' - X = Lt t' - Lt t := by simp only [X, X']; ring
  linarith

/-- `η_{t'} ≥ 0.99 η_t` for `|t| ≤ |t'| ≤ |t| + 1`. -/
lemma etat_ge_near {Λ t t' : ℝ} (hΛ : 1 ≤ Λ) (h : |t| ≤ |t'|) (h1 : |t'| ≤ |t| + 1) :
    0.99 * etat Λ t ≤ etat Λ t' := by
  unfold etat
  have hY := Yt_le_add hΛ h
  have hY0 := Yt_ge hΛ t
  have hY0' := Yt_ge hΛ t'
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have : Yt Λ t' ≤ Yt Λ t + 1 := by linarith
  nlinarith

/-- `Q ≤ Y`: `L_t + log Λ + log(1/η_t) + 439 ≤ Y(t)` for `Λ ≥ 10⁸`. -/
lemma Q_le_Y {Λ t : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    Lt t + Real.log Λ + Real.log (1 / etat Λ t) + 439 ≤ Yt Λ t := by
  have hΛ0 : 0 < Λ := by linarith
  have hY := Yt_ge (Λ := Λ) (by linarith) t
  have hlog1η : Real.log (1 / etat Λ t) = Real.log Λ + Real.log (Yt Λ t) - Real.log 0.33769 := by
    unfold etat
    rw [one_div_div, Real.log_div (by positivity) (by norm_num),
      Real.log_mul hΛ0.ne' (by linarith)]
  have hl33 := log_033769_ge
  have hX1 : 1 ≤ Lt t + 442 + 2 * Real.log Λ := by
    have := Lt_nonneg t; have := Real.log_nonneg (show (1 : ℝ) ≤ Λ by linarith); linarith
  have hlY := log_Y_le hX1
  unfold Yt at hlY ⊢
  rw [hlog1η]
  unfold Yt
  linarith

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}
variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- The growth bound of Step 7 on a disc of radius `6.9/Λ` around `1 + η + ikt`. -/
theorem norm_zetaSharp_le_Bk {η t : ℝ} {k : ℕ} (hk4 : k ≤ 4) (hkt : 1 / 16 ≤ |(k : ℝ) * t|)
    (hη0 : 0 ≤ η) (hη2 : η ≤ 1 / 10 ^ 10) {w : ℂ}
    (hw : ‖w - (((1 + η : ℝ) : ℂ) + k * t * I)‖ ≤ 6.9 / Real.log X₀) :
    ‖zetaSharp P θ X₀ α γ xp y w‖ ≤ Bk X₀ k t := by
  set Λ := Real.log X₀
  have hX := h.logX
  have hΛ0 : 0 < Λ := by linarith
  set z : ℂ := ((1 + η : ℝ) : ℂ) + k * t * I with hzdef
  have hzre : z.re = 1 + η := by simp [hzdef]
  have hzim : z.im = k * t := by simp [hzdef]
  have hRs : 6.9 / Λ ≤ 6.9 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
  have h1 := Complex.abs_re_le_norm (w - z)
  have h2 := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_re, Complex.sub_im, hzre, hzim] at h1 h2
  have hwre : 1 + η - 6.9 / Λ ≤ w.re := by linarith [(abs_le.mp (h1.trans hw)).1]
  have hwim : |(k : ℝ) * t| - 6.9 / Λ ≤ |w.im| := by
    have h3 := abs_sub_abs_le_abs_sub (k * t) w.im
    rw [abs_sub_comm] at h2; linarith
  have hw1 : w ≠ 1 := by
    intro e; rw [e] at hwim; simp at hwim
    have := hkt; rw [abs_mul, Nat.abs_cast] at this; linarith
  have hwn : ‖w‖ ≤ k * |t| + 1.02 := by
    have : ‖w‖ ≤ ‖z‖ + 6.9 / Λ := by
      have := norm_le_norm_add_norm_sub' w z; linarith
    have hz : ‖z‖ ≤ 1 + η + k * |t| := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [hzre, hzim, abs_mul, Nat.abs_cast, abs_of_pos (by linarith : (0 : ℝ) < 1 + η)]
        at this
      exact this
    linarith
  have hgr := h.norm_zetaSharp_sub_le (s := w) (by
    have : 8 / Λ ≥ 6.9 / Λ := div_le_div_of_nonneg_right (by norm_num) hΛ0.le
    linarith) hw1
  have hpole : ‖w / (w - 1)‖ ≤ 17.1 := by
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    have e : w / (w - 1) = 1 + 1 / (w - 1) := by field_simp; ring
    rw [e]
    have him : 1 / 16.1 ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    calc ‖1 + 1 / (w - 1)‖ ≤ 1 + ‖1 / (w - 1)‖ := by
          have := norm_add_le (1 : ℂ) (1 / (w - 1)); simpa using this
      _ = 1 + 1 / ‖w - 1‖ := by rw [norm_div, norm_one]
      _ ≤ 1 + 16.1 := by
          have : 1 / ‖w - 1‖ ≤ 1 / (1 / 16.1) := one_div_le_one_div_of_le (by norm_num) him
          norm_num at this ⊢; linarith
      _ = 17.1 := by norm_num
  have hκ0 := (kap_facts hX).2.2.1
  have hC0 : 0 < C8 := by unfold C8; positivity
  have hγ0 := Real.exp_pos Real.eulerMascheroniConstant
  have hXp : 0 ≤ (X₀ : ℝ) ^ (-(0.48 : ℝ)) := by positivity
  have hmono1 : C8 * (1 + kap X₀ * ‖w‖) * Real.exp Real.eulerMascheroniConstant * Λ ≤
      C8 * (1 + kap X₀ * (k * |t| + 1.02)) * Real.exp Real.eulerMascheroniConstant * Λ := by
    gcongr
  have hmono2 : (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * ‖w‖ ≤
      (1 + 5 * (X₀ : ℝ) ^ (-(0.48 : ℝ))) * (k * |t| + 1.02) := by gcongr
  have htri : ‖zetaSharp P θ X₀ α γ xp y w‖ ≤ ‖w / (w - 1)‖ +
      ‖zetaSharp P θ X₀ α γ xp y w - w / (w - 1)‖ := by
    have := norm_add_le (w / (w - 1)) (zetaSharp P θ X₀ α γ xp y w - w / (w - 1))
    simpa using this
  unfold Bk; linarith

omit h in
/-- `|log w| ≤ |log |w|| + π`. -/
lemma norm_log_le_abs_log_add_pi (w : ℂ) : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
  have := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
  rw [Complex.log_re, Complex.log_im] at this
  have h2 := Complex.abs_arg_le_pi w
  linarith

omit h in
/-- `|log((s-1)/s)| ≤ 6.3` for `1/17 ≤ |Im s|`, `|Re s - 1| ≤ 1/100`. -/
lemma norm_log_sub_one_div_le {s : ℂ} (hi : 1 / 17 ≤ |s.im|) (hr : |s.re - 1| ≤ 1 / 100) :
    ‖Complex.log ((s - 1) / s)‖ ≤ 6.3 := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at hi; simp at hi; linarith
  have hn1 : |s.im| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa using this
  have hn2 : ‖s - 1‖ ≤ |s.im| + 1 / 100 := by
    have := Complex.norm_le_abs_re_add_abs_im (s - 1); simp at this; linarith
  have hn3 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hn4 : ‖s‖ ≤ |s.im| + 1.01 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have : |s.re| ≤ 1.01 := by rw [abs_le]; constructor <;> linarith [(abs_le.mp hr).1,
      (abs_le.mp hr).2]
    linarith
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set w := ‖s - 1‖ / ‖s‖
  have hw : ‖(s - 1) / s‖ = w := norm_div _ _
  have hwlo : 1 / 20 ≤ w := by
    simp only [w]; rw [le_div_iff₀ hpos]; nlinarith
  have hwhi : w ≤ 2 := by
    simp only [w]; rw [div_le_iff₀ hpos]; nlinarith
  have hlog : |Real.log w| ≤ 3 := by
    rw [abs_le]; constructor
    · have := Real.log_le_log (by norm_num) hwlo
      have h20 : Real.log (1 / 20) ≥ -3 := by
        rw [one_div, Real.log_inv, ge_iff_le, neg_le_neg_iff]
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (3 : ℝ)
        have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e3]; nlinarith [pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3]
      linarith
    · have := Real.log_le_sub_one_of_pos (by linarith : 0 < w); linarith
  have h5 := norm_log_le_abs_log_add_pi ((s - 1) / s)
  rw [hw] at h5
  linarith [Real.pi_lt_d2]

set_option maxHeartbeats 4000000 in
/-- **Step 8**: `|𝔊₁(s)| ≤ 190 Y(t)` on the disc `|s - s₁| ≤ r₁` (inside `U`). -/
theorem G1_disc_bound {T₁ : ℝ} (hT : 1 ≤ T₁)
    (hyr : 10 ^ 4 * Real.log X₀ ^ 2 * Real.log (Real.log y) ≤ Real.log y)
    (hTy : Lt (T₁ + 1) ≤ logTy (Real.log X₀) (Real.log y) + 1)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rectU (Real.log X₀) T₁))
    (hGe : ∀ s ∈ rectU (Real.log X₀) T₁, Complex.exp (G s) = gfun P θ X₀ α γ xp y s)
    (hGr : ∀ s ∈ rectU (Real.log X₀) T₁, 1 + 8 * Real.log (Real.log y) / Real.log y < s.re →
      G s = Gright P θ X₀ α γ xp y s)
    {t : ℝ} (ht : 1 / 16 ≤ |t|) (htT : |t| ≤ T₁) {s : ℂ}
    (hs : ‖s - (((1 + etat (Real.log X₀) t : ℝ) : ℂ) + t * I)‖ ≤
      etat (Real.log X₀) t + 0.9 * (etat (Real.log X₀) t / 3.79))
    (hsU : s ∈ rectU (Real.log X₀) T₁) :
    ‖G s‖ ≤ 190 * Yt (Real.log X₀) t := by
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log y
  set f := zetaSharp P θ X₀ α γ xp y
  set η := etat Λ t with hηdef
  set δ := η / 3.79 with hδdef
  set s₁ : ℂ := ((1 + η : ℝ) : ℂ) + t * I with hs₁def
  set R₁ := η + 0.95 * δ with hR₁def
  set r₁ := η + 0.9 * δ with hr₁def
  have hX := h.logX
  have hΛ0 : 0 < Λ := by linarith
  have hL := h.logy_ge
  have hη0 : 0 < η := etat_pos (by linarith) t
  have hηs : η ≤ 1 / 10 ^ 10 := etat_le hX t
  have hηΛ : η * Λ ≤ 0.33769 / 442 := by
    simp only [η, etat]
    have hY := Yt_ge (Λ := Λ) (by linarith) t
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hYt := Yt_ge (Λ := Λ) (by linarith) t
  have hR1 : R₁ ≤ 1.26 * η := by rw [hR₁def, hδdef, div_eq_mul_one_div]; nlinarith
  have hR1Λ : R₁ ≤ 6.9 / Λ := by
    rw [le_div_iff₀ hΛ0]; nlinarith
  have hR1s : R₁ ≤ 1 / 10 ^ 9 := by nlinarith
  have hrR : r₁ < R₁ := by rw [hr₁def, hR₁def, hδdef, div_eq_mul_one_div]; nlinarith
  have hr0 : 0 < r₁ := by rw [hr₁def, hδdef]; positivity
  have hs₁re : s₁.re = 1 + η := by simp [hs₁def]
  have hs₁im : s₁.im = t := by simp [hs₁def]
  have hTt : |t| < T₁ + 1 := by linarith
  -- height condition at every height `≤ T₁ + 1`
  have hheight : ∀ t' : ℝ, |t'| ≤ T₁ + 1 → 16 * Real.log L / L ≤ etat Λ t' := by
    intro t' ht'
    refine etat_ge_of_height hX hL hyr (le_trans (Lt_mono ?_) hTy)
    rw [abs_of_pos (by linarith : (0 : ℝ) < T₁ + 1)]; exact ht'
  have hη16 := hheight t hTt.le
  -- points of the ball `|w - s₁| < R₁`
  have hball : ∀ w ∈ ball s₁ R₁, |w.re - (1 + η)| < R₁ ∧ |w.im - t| < R₁ := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - s₁)
    have h2 := Complex.abs_im_le_norm (w - s₁)
    simp only [Complex.sub_re, Complex.sub_im, hs₁re, hs₁im] at h1 h2
    exact ⟨lt_of_le_of_lt h1 hw, lt_of_le_of_lt h2 hw⟩
  have him : ∀ w ∈ ball s₁ R₁, 1 / 16 - 1 / 10 ^ 9 < |w.im| ∧ |w.im| ≤ |t| + R₁ := by
    intro w hw
    obtain ⟨-, h2⟩ := hball w hw
    have h3 := abs_sub_abs_le_abs_sub t w.im
    have h4 := abs_sub_abs_le_abs_sub w.im t
    rw [abs_sub_comm] at h3
    constructor <;> linarith
  have hne1 : ∀ w ∈ ball s₁ R₁, w ≠ 1 := by
    intro w hw e
    have := (him w hw).1; rw [e] at this; simp at this; linarith
  have hdiff : DifferentiableOn ℂ f (ball s₁ R₁) := by
    intro w hw
    obtain ⟨h1, -⟩ := hball w hw
    refine (h.differentiableAt_zetaSharp ?_ (hne1 w hw)).differentiableWithinAt
    linarith [(abs_lt.mp h1).1, h.theta_mem.2]
  have hnz : ∀ w ∈ ball s₁ R₁, f w ≠ 0 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hball w hw
    obtain ⟨h3, h4⟩ := him w hw
    by_cases hw16 : 1 / 16 ≤ |w.im|
    · have hη' := hheight w.im (by linarith)
      have hcmp : 0.99 * η ≤ etat Λ w.im := by
        rcases le_total |w.im| |t| with hc | hc
        · have := etat_anti (Λ := Λ) (by linarith) hc; linarith
        · exact etat_ge_near (by linarith) hc (by linarith)
      have hσ : 1 - etat Λ w.im / 3.79 ≤ w.re := by
        have : 0.95 * δ ≤ etat Λ w.im / 3.79 := by
          calc 0.95 * δ = 0.95 * η / 3.79 := by rw [hδdef]; ring
            _ ≤ etat Λ w.im / 3.79 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
        rw [hR₁def] at h1
        linarith [(abs_lt.mp h1).1]
      have := h.zeroFree_width (t := w.im) hw16 hη' hσ (by linarith [(abs_lt.mp h1).2])
      rwa [Complex.re_add_im] at this
    · push_neg at hw16
      have hn : ‖w - 1‖ ≤ 1 / 8 := by
        have := Complex.norm_le_abs_re_add_abs_im (w - 1)
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          sub_zero] at this
        have : |w.re - 1| ≤ 1 / 100 := by
          rw [abs_le]; constructor <;> linarith [(abs_lt.mp h1).1, (abs_lt.mp h1).2]
        linarith
      have h8 : 8 / Λ ≤ 8 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      have h69 : 6.9 / Λ ≤ 8 / Λ := div_le_div_of_nonneg_right (by norm_num) hΛ0.le
      have hnp := h.near_pole (s := w) (by linarith [(abs_lt.mp h1).1, hR1Λ]) hn (hne1 w hw)
      intro hz0
      have : ‖(w - 1) * zetaSharp P θ X₀ α γ xp y w - 1‖ = 1 := by
        rw [show zetaSharp P θ X₀ α γ xp y w = 0 from hz0]; simp
      linarith
  obtain ⟨ℓ, hℓd, hℓe⟩ := exists_log_ball hdiff hnz
  have hs₁b : s₁ ∈ ball s₁ R₁ := mem_ball_self (by linarith)
  -- `Re(ℓ w - ℓ s₁) < Y + 1`
  have hfs₁ := h.norm_zetaSharp_ge (s := s₁) (by rw [hs₁re]; linarith) (by rw [hs₁re]; linarith)
  rw [hs₁re, show 1 + η - 1 = η by ring] at hfs₁
  have hlogBk := log_Bk_le hX (k := 1) (by norm_num) t
  have hQ := Q_le_Y (Λ := Λ) (t := t) hX
  have hlog98 : -0.021 ≤ Real.log 0.98 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h4 : Real.exp (-0.021) ≤ 1 / (1 + 0.021) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (0.021 : ℝ)])
    have : (1 : ℝ) / (1 + 0.021) ≤ 0.98 := by norm_num
    linarith
  have hre : ∀ w ∈ ball s₁ R₁, (ℓ w - ℓ s₁).re < Yt Λ t + 1 := by
    intro w hw
    have e1 : (ℓ w).re = Real.log ‖f w‖ := by
      rw [← hℓe w hw, Complex.norm_exp, Real.log_exp]
    have e2 : (ℓ s₁).re = Real.log ‖f s₁‖ := by
      rw [← hℓe s₁ hs₁b, Complex.norm_exp, Real.log_exp]
    rw [Complex.sub_re, e1, e2]
    have hw' : ‖w - (((1 + η : ℝ) : ℂ) + (1 : ℕ) * t * I)‖ ≤ 6.9 / Λ := by
      have := mem_ball.mp hw; rw [dist_eq_norm] at this
      simp only [Nat.cast_one, one_mul]; linarith
    have hB := h.norm_zetaSharp_le_Bk (k := 1) (t := t) (η := η) (by norm_num)
      (by simpa using ht) hη0.le hηs hw'
    have hfw : 0 < ‖f w‖ := norm_pos_iff.mpr (hnz w hw)
    have hl1 : Real.log ‖f w‖ ≤ Real.log (Bk X₀ 1 t) := Real.log_le_log hfw hB
    have hl2 : Real.log (0.98 * η) ≤ Real.log ‖f s₁‖ := Real.log_le_log (by positivity) hfs₁
    rw [Real.log_mul (by norm_num) hη0.ne'] at hl2
    have h5 : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
    linarith
  -- Borel–Carathéodory
  set F : ℂ → ℂ := fun z => ℓ (s₁ + z) - ℓ s₁
  have hFd : DifferentiableOn ℂ F (ball 0 R₁) := by
    intro z hz
    have hz' : s₁ + z ∈ ball s₁ R₁ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hz
    have := (hℓd.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
      ((differentiableAt_const s₁).add differentiableAt_id)
    exact (this.sub_const _).differentiableWithinAt
  have hFm : Set.MapsTo F (ball 0 R₁) {z | z.re < Yt Λ t + 1} := by
    intro z hz
    have hz' : s₁ + z ∈ ball s₁ R₁ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hz
    exact hre _ hz'
  have hsz : ‖s - s₁‖ ≤ r₁ := hs
  have hBC := Complex.borelCaratheodory_zero (M := Yt Λ t + 1) (by linarith) hFd
    (hFm.mono_right fun _ hz => Set.mem_setOf.mpr (le_of_lt (Set.mem_setOf.mp hz))) (by linarith)
    (show s - s₁ ∈ ball (0 : ℂ) R₁ by rw [mem_ball, dist_zero_right]; linarith)
    (by simp [F])
  have hFs : F (s - s₁) = ℓ s - ℓ s₁ := by simp [F]
  rw [hFs] at hBC
  have hBC' : ‖ℓ s - ℓ s₁‖ ≤ 187.6 * (Yt Λ t + 1) := by
    refine hBC.trans ?_
    have hden : 0 < R₁ - ‖s - s₁‖ := by linarith
    rw [div_le_iff₀ hden]
    have : R₁ - r₁ = 0.05 * δ := by simp only [R₁, r₁]; ring
    have hδ : 0 < δ := by simp only [δ]; positivity
    have hr1 : r₁ = 4.69 * δ := by simp only [r₁, δ]; ring
    nlinarith [norm_nonneg (s - s₁)]
  -- relating `G` and `ℓ` on `ball s₁ R₁ ∩ U`
  have hs₁U : s₁ ∈ rectU Λ T₁ := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hs₁re]
      have := etat_pos (by linarith : (1 : ℝ) ≤ Λ) (T₁ + 1)
      simp only [c0]
      linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.99) this.le)
        (by norm_num : (0 : ℝ) ≤ 3.79)]
    · rw [hs₁re]; linarith
    · rw [hs₁im]; linarith [(abs_lt.mp hTt).1]
    · rw [hs₁im]; linarith [(abs_lt.mp hTt).2]
  have hslit : ∀ w ∈ ball s₁ R₁, (w - 1) / w ∈ Complex.slitPlane := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro e; have := (him w hw).1; rw [e] at this; simp at this; linarith
    apply Complex.mem_slitPlane_iff.mpr; right
    have hi : w.im ≠ 0 := by
      intro e; have := (him w hw).1; rw [e] at this; simp at this; linarith
    rw [sub_div, div_self hw0, Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero,
      Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, zero_sub, neg_div]
    rw [neg_ne_zero]
    exact div_ne_zero (by simpa using hi) (Complex.normSq_pos.mpr hw0).ne'
  set C := G s₁ - Complex.log ((s₁ - 1) / s₁) - ℓ s₁
  have hs₁1 : s₁ ≠ 1 := hne1 s₁ hs₁b
  have hs₁0 : s₁ ≠ 0 := by
    intro e; have := (him s₁ hs₁b).1; rw [e] at this; simp at this; linarith
  have hexpC : Complex.exp C = 1 := by
    simp only [C, Complex.exp_sub, hGe s₁ hs₁U, hℓe s₁ hs₁b]
    rw [Complex.exp_log (div_ne_zero (sub_ne_zero.mpr hs₁1) hs₁0)]
    simp only [gfun, Function.update_of_ne hs₁1]
    have := hnz s₁ hs₁b
    have h1' : s₁ - 1 ≠ 0 := sub_ne_zero.mpr hs₁1
    field_simp
    rfl
  have hV : IsPreconnected (ball s₁ R₁ ∩ rectU Λ T₁) :=
    ((convex_ball s₁ R₁).inter (convex_rect _ _ _ _)).isPreconnected
  have hrel := log_eq_of_exp_eq hV (L₁ := G)
    (L₂ := fun w => Complex.log ((w - 1) / w) + ℓ w + C)
    (hGd.continuousOn.mono Set.inter_subset_right)
    (by
      intro w hw
      refine ContinuousAt.continuousWithinAt ?_
      have hw0 : w ≠ 0 := by
        intro e; have := (him w hw.1).1; rw [e] at this; simp at this; linarith
      have hc0 : ContinuousAt (fun w : ℂ => (w - 1) / w) w :=
        (continuousAt_id.sub continuousAt_const).div continuousAt_id hw0
      have hc1 : ContinuousAt (fun w : ℂ => Complex.log ((w - 1) / w)) w :=
        ContinuousAt.clog hc0 (hslit w hw.1)
      exact (hc1.add (hℓd.continuousOn.continuousAt (isOpen_ball.mem_nhds hw.1))).add
        continuousAt_const)
    (by
      intro w hw
      have hw0 : w ≠ 0 := by
        intro e; have := (him w hw.1).1; rw [e] at this; simp at this; linarith
      have hw1 := hne1 w hw.1
      rw [hGe w hw.2, Complex.exp_add, Complex.exp_add, hexpC, mul_one, hℓe w hw.1,
        Complex.exp_log (div_ne_zero (sub_ne_zero.mpr hw1) hw0)]
      simp only [gfun, Function.update_of_ne hw1]
      field_simp
      rfl)
    (⟨hs₁b, hs₁U⟩ : s₁ ∈ ball s₁ R₁ ∩ rectU Λ T₁) (by simp only [C]; ring)
  have hsb : s ∈ ball s₁ R₁ := by rw [mem_ball, dist_eq_norm]; linarith
  have hGs := hrel s ⟨hsb, hsU⟩
  have hGdecomp : G s = G s₁ + (Complex.log ((s - 1) / s) - Complex.log ((s₁ - 1) / s₁)) +
      (ℓ s - ℓ s₁) := by rw [hGs]; simp only [C]; ring
  -- the anchor `G(s₁) = Gright(s₁)`
  have hr8 : 1 + 8 * Real.log L / L < s₁.re := by
    rw [hs₁re]
    have : 8 * Real.log L / L < 16 * Real.log L / L := by
      apply div_lt_div_of_pos_right _ (by linarith)
      have := Real.log_pos (show (1 : ℝ) < L by linarith); linarith
    linarith
  have hanch : G s₁ = Gright P θ X₀ α γ xp y s₁ := hGr s₁ hs₁U hr8
  -- `|log((s-1)/s)| ≤ 6.3` at `s` and `s₁`
  have hlog1 : ‖Complex.log ((s - 1) / s)‖ ≤ 6.3 := by
    obtain ⟨h1, h2⟩ := hball s hsb
    obtain ⟨h3, -⟩ := him s hsb
    exact norm_log_sub_one_div_le (by linarith) (by
      rw [abs_le]; constructor <;> linarith [(abs_lt.mp h1).1, (abs_lt.mp h1).2])
  have hlog2 : ‖Complex.log ((s₁ - 1) / s₁)‖ ≤ 6.3 := by
    refine norm_log_sub_one_div_le (by rw [hs₁im]; linarith) (by
      rw [hs₁re]; rw [abs_le]; constructor <;> linarith)
  -- `|Gright(s₁)|`
  have hσ₁ : 1 < s₁.re := by rw [hs₁re]; linarith
  have hLJ : ‖LJ P y s₁‖ ≤ 1.5 * Real.log (zetaFR P (P.primesLe y) s₁.re) := by
    unfold LJ zetaFR
    rw [Real.log_prod (fun j _ => (factorR_pos P j (by linarith)).ne')]
    calc ‖∑ j ∈ P.primesLe y, -Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s₁))‖
        ≤ ∑ j ∈ P.primesLe y, ‖-Complex.log (1 - ((P.p j : ℝ) : ℂ) ^ (-s₁))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ P.primesLe y, 1.5 * Real.log (1 - P.p j ^ (-s₁.re))⁻¹ := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hp2 := h.p_ge_two' ((BeurlingSystem.mem_primesLe P).mp hj)
          have hq : ‖-((P.p j : ℝ) : ℂ) ^ (-s₁)‖ ≤ 1 / 2 := by
            rw [norm_neg, norm_p_cpow_neg]
            calc P.p j ^ (-s₁.re) ≤ P.p j ^ (-(1 : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
              _ = 1 / P.p j := by rw [Real.rpow_neg_one, one_div]
              _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
          have h1 := Complex.norm_log_one_add_half_le_self hq
          rw [← sub_eq_add_neg, norm_neg] at h1
          rw [norm_neg]
          refine h1.trans ?_
          rw [norm_p_cpow_neg]
          have hx0 : 0 < P.p j ^ (-s₁.re) := Real.rpow_pos_of_pos (P.p_pos j) _
          have hx1 : P.p j ^ (-s₁.re) < 1 := p_rpow_neg_lt_one P j (by linarith)
          have := Real.log_le_sub_one_of_pos (show 0 < 1 - P.p j ^ (-s₁.re) by linarith)
          rw [Real.log_inv]
          nlinarith
      _ = 1.5 * ∑ j ∈ P.primesLe y, Real.log (1 - P.p j ^ (-s₁.re))⁻¹ := by
          rw [Finset.mul_sum]
  have hZ := h.zetaFR_le hσ₁ (by rw [hs₁re]; linarith)
  rw [hs₁re, show 1 + η - 1 = η by ring] at hZ
  have hEL : y ^ (1 - (1 + η)) * (Real.exp 11 * Real.log y ^ (2 : ℝ)) ≤ 1 := by
    have hlL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have h816 : 8 * Real.log L / L ≤ 16 * Real.log L / L :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hE := h.rpow_mul_log_pow_le (σ := 1 + η) (by linarith)
    have he11 : Real.exp 11 ≤ 60000 := by
      have e : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
        _ ≤ 60000 := by norm_num
    rw [Real.rpow_two]
    have hyp : 0 ≤ y ^ (1 - (1 + η)) := Real.rpow_nonneg (lt_of_lt_of_le h.X0_pos h.y_ge).le _
    have hL6 : (10 : ℝ) ^ 48 ≤ L ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hL 6; norm_num at this ⊢; linarith
    have h2 : y ^ (1 - (1 + η)) * L ^ 2 ≤ 1 / 10 ^ 48 := by
      rw [le_div_iff₀ (by norm_num)]
      have : y ^ (1 - (1 + η)) * L ^ 8 = y ^ (1 - (1 + η)) * L ^ 2 * L ^ 6 := by ring
      nlinarith [mul_nonneg hyp (sq_nonneg L)]
    calc y ^ (1 - (1 + η)) * (Real.exp 11 * L ^ 2) = Real.exp 11 * (y ^ (1 - (1 + η)) * L ^ 2) := by
          ring
      _ ≤ 60000 * (1 / 10 ^ 48) := mul_le_mul he11 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hκ := (kap_facts hX).2.2.2.1
  have hZ' : zetaFR P (P.primesLe y) (1 + η) ≤ 2 / η := by
    have : (1 + 2 * kap X₀) / η ≤ 1.01 / η := div_le_div_of_nonneg_right (by linarith) hη0.le
    have h71 : 71 ≤ 0.99 / η := by rw [le_div_iff₀ hη0]; nlinarith
    have : (2 : ℝ) / η = 1.01 / η + 0.99 / η := by ring
    linarith
  have hlogZ : Real.log (zetaFR P (P.primesLe y) (1 + η)) ≤ Real.log 2 + Real.log (1 / η) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (zetaFR_pos P _ (by linarith)) (by rw [mul_one_div]; exact hZ')
  rw [hs₁re] at hLJ
  have hg := h.norm_g_le (s := s₁) hr8.le (by rw [hs₁re]; linarith)
  have hL4 : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hg' : ‖gJ P θ X₀ α γ xp y s₁‖ ≤ 1 / 10 ^ 32 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [norm_nonneg (gJ P θ X₀ α γ xp y s₁)]
  have hlg : ‖Complex.log (1 + gJ P θ X₀ α γ xp y s₁)‖ ≤ 3 / 2 * (1 / 10 ^ 32) :=
    (Complex.norm_log_one_add_half_le_self (hg'.trans (by norm_num))).trans (by linarith)
  have hGs₁ : ‖G s₁‖ ≤ 1.5 * (Real.log 2 + Real.log (1 / η)) + 3 / 2 * (1 / 10 ^ 32) + 6.3 := by
    rw [hanch]; unfold Gright
    calc _ ≤ ‖LJ P y s₁‖ + ‖Complex.log (1 + gJ P θ X₀ α γ xp y s₁)‖ +
          ‖Complex.log ((s₁ - 1) / s₁)‖ := norm_add₃_le
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hlogZ (by norm_num : (0 : ℝ) ≤ 1.5)
          linarith
  have hlog2' : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlΛ : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hLt0 := Lt_nonneg t
  rw [hGdecomp]
  calc ‖G s₁ + (Complex.log ((s - 1) / s) - Complex.log ((s₁ - 1) / s₁)) + (ℓ s - ℓ s₁)‖
      ≤ ‖G s₁‖ + (‖Complex.log ((s - 1) / s)‖ + ‖Complex.log ((s₁ - 1) / s₁)‖) +
          ‖ℓ s - ℓ s₁‖ := by
        refine (norm_add₃_le).trans ?_
        gcongr; exact norm_sub_le _ _
    _ ≤ 190 * Yt Λ t := by linarith

end LPHyp

end LocalPNT

end
