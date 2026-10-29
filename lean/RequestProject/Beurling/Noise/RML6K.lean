module

public import RequestProject.Beurling.Noise.RML6PredMain
public import RequestProject.Beurling.Noise.TauNearLocMain

/-!
# Lemma 5.34, the two bullets, and the size of `log t · η(t)`

* `KR.RML6K.abs_int_mul_gK_le` : `|∫ F dC_n^y| ≤ c · TV(C_n^y)` when `|F| ≤ c` on the support
  window `|t - y/n| ≤ 1.02 H(y/n)` of the true kernel `C_n^y` (`n ≥ 2`).
* `KR.RML6K.kernel_sum_le` : the kernel part of `R_res F` at a start `y` is at most
  `∑_u F̄(u) W^op_y(u)`, `F̄(u)` a bound for `|F|` on the windows of the levels of the scale `u`.
* `KR.RML6K.hK_of_scales` : **the first bullet of Lemma 5.34**: with Proposition 5.18's weights
  `W^op_y(u) ≤ 5.1 C_N log(2u)/log y` at every start `y` of the window of `x` and
  `∑_u log(2u) F̄_y(u) ≤ S`, `log x · |B K_pt B R F_r (x)| ≤ aK CN S H x`,
  `aK = 5.1 C_N S · log x/log(x - H(x)/2)` (the paper's `5.1 C_N ∑_u log(2u) F̄_r(u)`, up to the
  passage from `log y` to `log x`).
* `KR.RML6K.hG_of_start` : the second bullet reduced to a bound on `R_res G` at the starts of the
  window (`log x · |R_res G(y)| ≤ bb`; the paper bounds it by `15.3 C_N C_S' ∑_v (log 3v)² F_r^+(v)`
  through Lemma 5.21(iii)).
* `KR.RML6K.logt_eta_le` : `log t · η(t) ≤ log b · 207800 Φ₂(X₀⁻/2)` for `t ≤ b` at the cofactor
  horizon (`η(t) = ∑_{w τ-near at t} 1/w`, from `TNP.thetaStar_on_loc`). This is not uniform in
  `b`; the paper's uniform bound `sup_y log y · η(y) ≤ e^{-0.99Λ}` (the last claim of Lemma 5.20)
  needs the decay of the smooth sums and is not proved here.
-/

@[expose] public section

open MeasureTheory Set Finset BeurlingSystem

namespace KR.RML6K

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m ε θ : ℝ}

lemma TVt_nonneg (y : ℝ) (n : ℕ) : 0 ≤ TVt P H tw X0m y n := by
  unfold TVt; split_ifs <;> exact ENNReal.toReal_nonneg

/-- `|∫ F dC_n^y| ≤ c · TV(C_n^y)` for `|F| ≤ c` on the support window of `C_n^y`. -/
lemma abs_int_mul_gK_le (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p)
    {y : ℝ} {n : ℕ} (hn : 2 ≤ n) {F : ℝ → ℝ} (hFm : Measurable F) {c : ℝ}
    (hF : ∀ t, |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |F t| ≤ c) :
    |∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t| ≤ c * TVt P H tw X0m y n := by
  obtain ⟨hg, hgm⟩ := integrable_gKT (val := P.labelVal) (x := y) (tw := tw) (X0m := X0m) hP.reg n
  set g := gK P.labelVal y H (phiT tw X0m) n
  have hsupp := gK_support (x := y) hP hval2 (φ := phiT tw X0m)
    (fun d n c h => trueFilter_ne_zero h) n
  have hpt : ∀ t, |F t * g t| ≤ c * |g t| := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hF t (hsupp t h0).2) (abs_nonneg _)
  have hFg : Integrable (fun t => F t * g t) := by
    refine (hg.abs.const_mul c).mono' (hFm.mul hgm).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hpt t
  have hTV : TVt P H tw X0m y n = ∫ t, |g t| := by
    unfold TVt
    rw [if_neg (by omega)]
    have := integral_norm_eq_lintegral_enorm hgm.aestronglyMeasurable (μ := volume)
    simp only [Real.norm_eq_abs] at this
    exact this.symm
  rw [hTV, ← integral_const_mul]
  calc |∫ t, F t * g t| ≤ ∫ t, |F t * g t| := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans (le_of_eq (by simp [Real.norm_eq_abs]))
    _ ≤ ∫ t, c * |g t| := integral_mono hFg.abs (hg.abs.const_mul c) hpt

/-- **The kernel part of `R_res F` at a start `y`** is at most `∑_u F̄(u) W^op_y(u)`. -/
theorem kernel_sum_le (hP : PaperWidth H X0m ε θ) (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p)
    {y : ℝ} {Sc : Finset ℝ} (hcov : ∀ n ∈ levels P X0m y, ∃ u ∈ Sc, n ∈ NW P y u)
    {F : ℝ → ℝ} (hFm : Measurable F) {Fb : ℝ → ℝ} (hFb0 : ∀ u ∈ Sc, 0 ≤ Fb u)
    (hF : ∀ u ∈ Sc, ∀ n ∈ NW P y u, ∀ t,
      |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |F t| ≤ Fb u) :
    |∑ n ∈ levels P X0m y, (∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n| ≤
      ∑ u ∈ Sc, Fb u * Wop P H tw X0m y u := by
  classical
  have hV : ∀ n, 0 < Vl P n := fun n => KR.valN_labelVal_pos P n
  set T : ℕ → ℝ := fun n => TVt P H tw X0m y n / Vl P n
  have hT0 : ∀ n, 0 ≤ T n := fun n => div_nonneg (TVt_nonneg y n) (hV n).le
  have hterm : ∀ n ∈ levels P X0m y,
      |(∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n| ≤
        ∑ u ∈ Sc, (if n ∈ NW P y u then Fb u * T n else 0) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2
    obtain ⟨u0, hu0, hn0⟩ := hcov n hn
    have h1 := abs_int_mul_gK_le (tw := tw) hP hval2 hn2 hFm (hF u0 hu0 n hn0)
    rw [abs_div, abs_of_pos (hV n)]
    calc |∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t| / Vl P n ≤ Fb u0 * T n := by
          simp only [T]; rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right h1 (hV n).le
      _ = (if n ∈ NW P y u0 then Fb u0 * T n else 0) := by rw [if_pos hn0]
      _ ≤ ∑ u ∈ Sc, (if n ∈ NW P y u then Fb u * T n else 0) :=
          Finset.single_le_sum (f := fun u => if n ∈ NW P y u then Fb u * T n else 0)
            (fun u hu => by
              show 0 ≤ (if n ∈ NW P y u then Fb u * T n else 0)
              split_ifs
              · exact mul_nonneg (hFb0 u hu) (hT0 n)
              · exact le_rfl) hu0
  calc |∑ n ∈ levels P X0m y, (∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n|
      ≤ ∑ n ∈ levels P X0m y, |(∫ t, F t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ levels P X0m y, ∑ u ∈ Sc, (if n ∈ NW P y u then Fb u * T n else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ u ∈ Sc, ∑ n ∈ levels P X0m y, (if n ∈ NW P y u then Fb u * T n else 0) :=
        Finset.sum_comm
    _ ≤ ∑ u ∈ Sc, Fb u * Wop P H tw X0m y u := by
        refine Finset.sum_le_sum fun u hu => ?_
        rw [← Finset.sum_filter, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hFb0 u hu)
        unfold Wop
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn; exact (Finset.mem_filter.mp hn).2
        · intro n _ _; exact hT0 n

/-- `a(x) = 5.1 C_N S · log x/log(x - H(x)/2)`. -/
noncomputable def aK (CN S : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  5.1 * CN * S * (Real.log x / Real.log (x - H x / 2))

/-- **The first bullet of Lemma 5.34**, from Proposition 5.18's weights at the starts of the
window and a scale-wise bound `F̄_y` for `|F_r|` on the windows of the levels. -/
theorem hK_of_scales (hO : Ops.OpHyp P H X0m) (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p) (F : Ops.LocInt) (hF : Ops.LBd (F : ℝ → ℝ))
    (hFm : Measurable (F : ℝ → ℝ)) {x CN S : ℝ} (hx : 1 < x - H x / 2) (hCN : 0 ≤ CN)
    (hstart : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 → ∃ Sc : Finset ℝ, ∃ Fb : ℝ → ℝ,
      (∀ n ∈ levels P X0m y, ∃ u ∈ Sc, n ∈ NW P y u) ∧ (∀ u ∈ Sc, 0 ≤ Fb u) ∧
      (∀ u ∈ Sc, ∀ n ∈ NW P y u, ∀ t,
        |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |(F : ℝ → ℝ) t| ≤ Fb u) ∧
      (∀ u ∈ Sc, Wop P H tw X0m y u ≤ 5.1 * CN * Real.log (2 * u) / Real.log y) ∧
      (∀ u ∈ Sc, 0 ≤ Real.log (2 * u)) ∧ ∑ u ∈ Sc, Real.log (2 * u) * Fb u ≤ S) :
    Real.log x * |(Ops.Bo hO (Ops.Ko (tw := tw) hO (Ops.Bo hO (Ops.Ro (tw := tw) hO F))) :
      ℝ → ℝ) x| ≤ aK CN S H x := by
  have hHx := hO.pos x
  have hlx0 : 0 < Real.log (x - H x / 2) := Real.log_pos hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlxy : Real.log (x - H x / 2) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  refine Ops.hK_of_kernel hO hP F hF hlx fun y hy1 hy2 => ?_
  obtain ⟨Sc, Fb, hcov, hFb0, hFb, hW, hl2, hS⟩ := hstart y hy1 hy2
  have hly : Real.log (x - H x / 2) ≤ Real.log y := Real.log_le_log (by linarith) hy1
  have hly0 : 0 < Real.log y := lt_of_lt_of_le hlx0 hly
  have hks := kernel_sum_le (tw := tw) hP hval2 hcov hFm hFb0 hFb
  have hS0 : 0 ≤ ∑ u ∈ Sc, Real.log (2 * u) * Fb u :=
    Finset.sum_nonneg fun u hu => mul_nonneg (hl2 u hu) (hFb0 u hu)
  have hsum : ∑ u ∈ Sc, Fb u * Wop P H tw X0m y u ≤ 5.1 * CN * S / Real.log y := by
    calc ∑ u ∈ Sc, Fb u * Wop P H tw X0m y u
        ≤ ∑ u ∈ Sc, Fb u * (5.1 * CN * Real.log (2 * u) / Real.log y) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hW u hu) (hFb0 u hu)
      _ = 5.1 * CN * (∑ u ∈ Sc, Real.log (2 * u) * Fb u) / Real.log y := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun u _ => by ring
      _ ≤ 5.1 * CN * S / Real.log y := by
          apply div_le_div_of_nonneg_right _ hly0.le
          exact mul_le_mul_of_nonneg_left hS (by positivity)
  have hSS : 0 ≤ S := hS0.trans hS
  calc Real.log x * |∑ n ∈ levels P X0m y,
        (∫ t, (F : ℝ → ℝ) t * gK P.labelVal y H (phiT tw X0m) n t) / Vl P n|
      ≤ Real.log x * (5.1 * CN * S / Real.log y) :=
        mul_le_mul_of_nonneg_left (hks.trans hsum) hlx
    _ ≤ Real.log x * (5.1 * CN * S / Real.log (x - H x / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hlx
        exact div_le_div_of_nonneg_left (by positivity) hlx0 hly
    _ = aK CN S H x := by unfold aK; ring

/-- **The second bullet of Lemma 5.34**, reduced to a bound on `R_res G` at the starts of the
window of `x`. -/
theorem hG_of_start (hO : Ops.OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (G : Ops.LocInt)
    (hG : Ops.LBd (G : ℝ → ℝ)) {x bb : ℝ} (hlx : 0 ≤ Real.log x)
    (hstart : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      Real.log x * |Rres P H tw X0m y (G : ℝ → ℝ)| ≤ bb) :
    Real.log x * |(Ops.Bo hO (Ops.Ro (tw := tw) hO G) : ℝ → ℝ) x| ≤ bb := by
  have hHx := hO.pos x
  have e : ((Ops.Ro (tw := tw) hO G : Ops.LocInt) : ℝ → ℝ) =
      fun y => Rres P H tw X0m y (G : ℝ → ℝ) := by
    funext y; exact (Ops.Rres_eq_Nop hO hP G hG y).symm
  show Real.log x * |Margin.Bavg (H x) ((Ops.Ro (tw := tw) hO G : Ops.LocInt) : ℝ → ℝ) x| ≤ bb
  rw [e]
  rcases eq_or_lt_of_le hlx with h0 | hpos
  · rw [← h0, zero_mul]
    have := hstart x (by linarith) (by linarith)
    rw [← h0, zero_mul] at this; exact this
  have hb : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 →
      |Rres P H tw X0m y (G : ℝ → ℝ)| ≤ bb / Real.log x := by
    intro y h1 h2
    rw [le_div_iff₀ hpos, mul_comm]; exact hstart y h1 h2
  have := Ops.abs_Bavg_le_on hHx hb
  rw [le_div_iff₀ hpos] at this
  linarith

/-- The weight `1` is at most the weight `log c + 1` on the `τ`-near cofactors (`c ≥ X₀⁻ ≥ 1`). -/
lemma etaG_one_le (hX : 1 ≤ X0m) (v : ℝ) :
    etaG P H tw X0m (fun _ => 1) v ≤ etaG P H tw X0m (fun c => Real.log c + 1) v := by
  classical
  unfold etaG
  refine Finset.sum_le_sum fun m hm => ?_
  have hV := KR.valN_labelVal_pos P m
  have hc : X0m ≤ v / Vl P m := ((Finset.mem_filter.mp hm).2).2
  have hl : 0 ≤ Real.log (v / Vl P m) := Real.log_nonneg (by linarith)
  exact div_le_div_of_nonneg_right (by linarith) hV.le

lemma etaG_one_nonneg (v : ℝ) : 0 ≤ etaG P H tw X0m (fun _ => 1) v := by
  unfold etaG
  exact Finset.sum_nonneg fun m _ => div_nonneg zero_le_one (KR.valN_labelVal_pos P m).le

/-- **`log t · η(t)` at the cofactor horizon**: for `0 < t ≤ b` with `2500 ≤ Z`, `9b ≤ Z²`,
`log t · η(t) ≤ log b · 207800 Φ₂(X₀⁻/2)`, `η(t) = ∑_{w τ-near at t} 1/w`. -/
theorem logt_eta_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {t b : ℝ} (ht : 1 ≤ t) (htb : t ≤ b)
    (hZ0 : 2500 ≤ Z) (hZ : 9 * b ≤ Z ^ 2) :
    Real.log t * etaG P H tw X0m (fun _ => 1) t ≤
      Real.log b * (207800 * TNP.Phi H 2 (X0m / 2)) := by
  have hX1 : 1 ≤ X0m := by
    have := h.hXm
    by_contra hc; push_neg at hc
    have : Real.log X0m < 0 ∨ Real.log X0m ≤ 0 := Or.inr
      (Real.log_nonpos_iff (h.width.X0m_pos.le) |>.mpr hc.le)
    rcases this with h' | h' <;> linarith
  have hθ := TNP.thetaStar_on_loc h (by linarith) hZ0 (by linarith : 9 * t ≤ Z ^ 2)
  have h1 := etaG_one_le (P := P) (H := H) (tw := tw) hX1 t
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hltb : Real.log t ≤ Real.log b := Real.log_le_log (by linarith) htb
  have he0 := etaG_one_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) t
  have hΦ : 0 ≤ 207800 * TNP.Phi H 2 (X0m / 2) := (he0.trans h1).trans hθ
  calc Real.log t * etaG P H tw X0m (fun _ => 1) t
      ≤ Real.log t * (207800 * TNP.Phi H 2 (X0m / 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans hθ) hlt
    _ ≤ Real.log b * (207800 * TNP.Phi H 2 (X0m / 2)) :=
        mul_le_mul_of_nonneg_right hltb hΦ

end KR.RML6K

end
