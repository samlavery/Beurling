module

public import RequestProject.Beurling.Noise.RML9XBSplit

/-!
# Proposition 5.31(iii): the bounds of a pair `(d, w)` (eq. (TVD-bounds))

With `R(d) = |c_d|/V(d) + ∑_{e ∣ d, 1<e<d} H_ord(d/e) V(d/e)^{ε-2} |c_e|/V(e)`:

* `TVD_div_le` : `½ TV(D_d)/V(d) ≤ |c_d|/V(d) + ¼λ₀ ∑ … ≤ R(d)` (for `λ₀ ≤ 4`);
* `KRD_div_le` : `λ₀ ‖D_d‖_KR/(w H_n)/(V(d) w) ≤ (λ₀²/4) w^{ε-2} R(d)` (`n = d·w`, eq. (RH));
* `Gpair_le_beta` : `G(d, w) ≤ (2/w) R(d)` on the window;
* `Gpair_le_gamma` : `G(d, w) ≤ [X₀-near] ½ TV(D_d)/(V(d) w) + [Win] (λ₀²/4) w^{ε-2} R(d)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

/-- `R(d) = |c_d|/V(d) + ∑_{e ∣ d, 1<e<d} H_ord(d/e) V(d/e)^{ε-2} |c_e|/V(e)`. -/
noncomputable def Rd (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m y ε : ℝ) (d : ℕ) : ℝ :=
  |cN P tw X0m y d| / Vl P d + ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
    (BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ (ε - 2) * (|cN P tw X0m y e| / Vl P e)

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma Rd_nonneg (ε : ℝ) (d : ℕ) : 0 ≤ Rd P tw X0m y ε d := by
  unfold Rd
  have h1 := KR.valN_labelVal_pos P d
  refine add_nonneg (by positivity) (Finset.sum_nonneg fun e _ => ?_)
  have h2 := KR.valN_labelVal_pos P (d / e)
  have h3 := KR.valN_labelVal_pos P e
  have h4 : 0 ≤ Vl P (d / e) ^ (ε - 2) := Real.rpow_nonneg h2.le _
  positivity

lemma Vl_eq_mul {d e : ℕ} (hed : e ∣ d) (hd0 : d ≠ 0) : Vl P d = Vl P e * Vl P (d / e) :=
  valN_div_mul (fun p _ => P.one_le_labelVal p) hed hd0

/-- The per-term identity `(V(e)/V(d))/V(d) = V(d/e)^{-2}/V(e)`. -/
lemma ratio_term {d e : ℕ} (hed : e ∣ d) (hd0 : d ≠ 0) :
    (Vl P e / Vl P d) / Vl P d = Vl P (d / e) ^ (-2 : ℝ) / Vl P e := by
  have hm := KR.valN_labelVal_pos P (d / e)
  have he := KR.valN_labelVal_pos P e
  rw [Vl_eq_mul hed hd0, Real.rpow_neg hm.le, Real.rpow_two]
  field_simp

/-- **(TVD-bounds), first, divided by `V(d)`.** -/
lemma TVD_div_le {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) {d : ℕ}
    (hd : 2 ≤ d) (hpd : X0m / 2 ≤ posn P.labelVal y d) :
    1 / 2 * TVD P H tw X0m y d / Vl P d ≤ |cN P tw X0m y d| / Vl P d + 1 / 4 * lam0 *
      ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        (BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ (ε - 2) *
          (|cN P tw X0m y e| / Vl P e) := by
  have hd0 : d ≠ 0 := by omega
  have hVd := KR.valN_labelVal_pos P d
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have h1 := halfTVD_le hP hp2 ht hlam hy hd (tw := tw)
  have hHd := hP.reg.pos (posn P.labelVal y d)
  rw [div_le_iff₀ hVd]
  refine h1.trans ?_
  rw [add_mul, div_mul_cancel₀ _ hVd.ne']
  apply add_le_add le_rfl
  have hsum : ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
        (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) ≤
      (∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        (BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ (ε - 2) *
          (|cN P tw X0m y e| / Vl P e)) * Vl P d := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨hed', -, -⟩ := Finset.mem_filter.mp he
    have hed : e ∣ d := Nat.dvd_of_mem_divisors hed'
    have hm := KR.valN_labelVal_pos P (d / e)
    have hVe := KR.valN_labelVal_pos P e
    have hRH : Hlev P.labelVal y H e / Hlev P.labelVal y H d ≤ Vl P (d / e) ^ ε := by
      unfold Hlev
      rw [div_le_iff₀ hHd]
      exact Hlev_le hP hed hd0 hpd
    have hc := abs_nonneg (cN P tw X0m y e)
    have hHo : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
    have key : |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
        (BSCert.X0Band.Hord (d / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) ≤
        |cN P tw X0m y e| * Vl P (d / e) ^ ε * (BSCert.X0Band.Hord (d / e) : ℝ) *
          (Vl P e / Vl P d) := by
      have hr : 0 ≤ Vl P e / Vl P d := by positivity
      have := mul_le_mul_of_nonneg_left hRH hc
      have := mul_le_mul_of_nonneg_right this hHo
      exact mul_le_mul_of_nonneg_right this hr
    refine key.trans (le_of_eq ?_)
    have e1 : Vl P (d / e) ^ (ε - 2) = Vl P (d / e) ^ ε * Vl P (d / e) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hm]; ring_nf
    have e2 := ratio_term (P := P) hed hd0
    rw [e1]
    calc |cN P tw X0m y e| * Vl P (d / e) ^ ε * (BSCert.X0Band.Hord (d / e) : ℝ) *
          (Vl P e / Vl P d)
        = |cN P tw X0m y e| * Vl P (d / e) ^ ε * (BSCert.X0Band.Hord (d / e) : ℝ) *
            ((Vl P e / Vl P d) / Vl P d) * Vl P d := by field_simp
      _ = _ := by rw [e2]; field_simp
  calc 1 / 4 * lam0 * ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
          (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d)
      ≤ 1 / 4 * lam0 * ((∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        (BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ (ε - 2) *
          (|cN P tw X0m y e| / Vl P e)) * Vl P d) := by gcongr
    _ = _ := by ring

/-- `½ TV(D_d)/V(d) ≤ R(d)` (for `λ₀ ≤ 4`). -/
lemma TVD_div_le_Rd {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hlam4 : lam0 ≤ 4)
    (hy : X0m ≤ y) {d : ℕ} (hd : 2 ≤ d) (hpd : X0m / 2 ≤ posn P.labelVal y d) :
    1 / 2 * TVD P H tw X0m y d / Vl P d ≤ Rd P tw X0m y ε d := by
  have h := TVD_div_le hP hp2 ht hlam hy hd hpd (tw := tw)
  unfold Rd
  have hS : 0 ≤ ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      (BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ (ε - 2) *
        (|cN P tw X0m y e| / Vl P e) := by
    have := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
    refine Finset.sum_nonneg fun e _ => ?_
    have h2 := KR.valN_labelVal_pos P (d / e)
    have h3 := KR.valN_labelVal_pos P e
    have h4 : 0 ≤ Vl P (d / e) ^ (ε - 2) := Real.rpow_nonneg h2.le _
    positivity
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  nlinarith

/-- **(TVD-bounds), second, for the `𝔹₂` step `d → n = d·w`.** -/
lemma KRD_div_le {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) {d w : ℕ}
    (hd : 2 ≤ d) (hw : 2 ≤ w) (hpn : X0m / 2 ≤ posn P.labelVal y (d * w)) :
    lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w))) /
        (Vl P d * Vl P w) ≤
      lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hd0 : d ≠ 0 := by omega
  have hw0 : w ≠ 0 := by omega
  have hn0 : d * w ≠ 0 := mul_ne_zero hd0 hw0
  have hVd := KR.valN_labelVal_pos P d
  have hVw := KR.valN_labelVal_pos P w
  have hHn := hP.reg.pos (posn P.labelVal y (d * w))
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hK := KRD_le hP hp2 ht hlam hy hd (tw := tw)
  -- the sum of `KRD_le`, with `H_e ≤ V(n/e)^ε H_n`
  set Sk := ∑ e ∈ d.divisors.filter (1 < ·), |cN P tw X0m y e| * Hlev P.labelVal y H e *
      (BSCert.X0Band.Hord (d / e) : ℝ) * (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d)
  have hSk : Sk ≤ H (posn P.labelVal y (d * w)) * Vl P w ^ ε * Vl P d *
      Rd P tw X0m y ε d := by
    have hsplit := divisors_filter_one_lt hd
    simp only [Sk]
    rw [hsplit, Finset.sum_insert (by simp)]
    unfold Rd
    rw [mul_add, Finset.mul_sum]
    -- the term `e = d`
    have hdd : d / d = 1 := Nat.div_self (by omega)
    have hRHd : Hlev P.labelVal y H d ≤ Vl P w ^ ε * H (posn P.labelVal y (d * w)) := by
      have := Hlev_le hP (Dvd.intro w rfl) hn0 hpn
      unfold Hlev
      rwa [show d * w / d = w from Nat.mul_div_cancel_left w (by omega)] at this
    apply add_le_add
    · rw [hdd, BSCert.X0Band.Hord_eq 1, if_pos le_rfl, div_self hVd.ne']
      have hc := abs_nonneg (cN P tw X0m y d)
      calc |cN P tw X0m y d| * Hlev P.labelVal y H d * ((1 : ℕ) : ℝ) * 1
          ≤ |cN P tw X0m y d| * (Vl P w ^ ε * H (posn P.labelVal y (d * w))) := by
            push_cast; rw [mul_one, mul_one]
            exact mul_le_mul_of_nonneg_left hRHd hc
        _ = _ := by field_simp
    · refine Finset.sum_le_sum fun e he => ?_
      obtain ⟨hed', -, -⟩ := Finset.mem_filter.mp he
      have hed : e ∣ d := Nat.dvd_of_mem_divisors hed'
      have hen : e ∣ d * w := hed.mul_right w
      have hm := KR.valN_labelVal_pos P (d / e)
      have hVe := KR.valN_labelVal_pos P e
      have hdiv : d * w / e = d / e * w := (Nat.div_mul_right_comm hed w).symm
      have hVne : Vl P (d * w / e) = Vl P (d / e) * Vl P w := by
        rw [hdiv]
        have he1 := (Finset.mem_filter.mp he).2.1
        have hde : 0 < d / e := Nat.div_pos (Nat.le_of_dvd (by omega) hed) (by omega)
        exact LemmaM.valN_mul _ hde.ne' hw0
      have hRHe : Hlev P.labelVal y H e ≤
          (Vl P (d / e) * Vl P w) ^ ε * H (posn P.labelVal y (d * w)) := by
        have := Hlev_le hP hen hn0 hpn
        unfold Hlev
        rwa [show LemmaM.valN P.labelVal (d * w / e) = Vl P (d / e) * Vl P w from hVne] at this
      have hc := abs_nonneg (cN P tw X0m y e)
      have hHo : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
      have hr : 0 ≤ Vl P e / Vl P d := by positivity
      calc |cN P tw X0m y e| * Hlev P.labelVal y H e * (BSCert.X0Band.Hord (d / e) : ℝ) *
            (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d)
          ≤ |cN P tw X0m y e| * ((Vl P (d / e) * Vl P w) ^ ε *
              H (posn P.labelVal y (d * w))) * (BSCert.X0Band.Hord (d / e) : ℝ) *
              (Vl P e / Vl P d) := by
            have := mul_le_mul_of_nonneg_left hRHe hc
            have := mul_le_mul_of_nonneg_right this hHo
            exact mul_le_mul_of_nonneg_right this hr
        _ = H (posn P.labelVal y (d * w)) * Vl P w ^ ε * Vl P d *
              ((BSCert.X0Band.Hord (d / e) : ℝ) * Vl P (d / e) ^ ε *
                (|cN P tw X0m y e| * ((Vl P e / Vl P d) / Vl P d))) := by
            rw [Real.mul_rpow hm.le hVw.le]; field_simp
        _ = _ := by
            rw [ratio_term hed hd0]
            have e1 : Vl P (d / e) ^ (ε - 2) = Vl P (d / e) ^ ε * Vl P (d / e) ^ (-2 : ℝ) := by
              rw [← Real.rpow_add hm]; ring_nf
            rw [e1]; field_simp
  have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
  rw [div_div, div_le_iff₀ (by positivity)]
  calc lam0 * KRD P H tw X0m y d ≤ lam0 * (1 / 4 * lam0 * Sk) :=
        mul_le_mul_of_nonneg_left hK hlam0
    _ ≤ lam0 * (1 / 4 * lam0 * (H (posn P.labelVal y (d * w)) * Vl P w ^ ε * Vl P d *
          Rd P tw X0m y ε d)) := by gcongr
    _ = _ := by
        have e1 : Vl P w ^ (ε - 2) = Vl P w ^ ε * Vl P w ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hVw]; ring_nf
        rw [e1, Real.rpow_neg hVw.le, Real.rpow_two]
        field_simp

end KR.RML9

end
