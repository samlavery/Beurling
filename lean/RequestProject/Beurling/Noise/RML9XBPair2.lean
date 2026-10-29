module

public import RequestProject.Beurling.Noise.RML9XBPair

/-!
# Proposition 5.31(iii): `G(d, w)` for small and for large cofactors

* `Gpair_le_beta` : `G(d, w) ≤ [Win(d·w)] (2/w) R(d)`;
* `Gpair_le_gamma` : `G(d, w) ≤ [X₀-near] ½ TV(D_d)/(V(d) w) + [Win(d·w)] (λ₀²/4) w^{ε-2} R(d)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- On the window, `y/n ≥ X₀⁻/2`. -/
lemma win_posn_ge {ε θ X0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hX0 : 0 < X0) (hδ : H X0 / X0 ≤ 1 / 1000) {n : ℕ} (hw : Win P H y X0 n) :
    X0m / 2 ≤ posn P.labelVal y n := by
  have hH0 := hP.reg.pos X0
  have hHX : H X0 ≤ X0 / 1000 := by
    rw [div_le_iff₀ hX0] at hδ; linarith
  unfold Win at hw
  rw [abs_le] at hw
  rw [hX0e]; linarith [hw.1]

lemma Vl_mul_eq {d w : ℕ} (hd : d ≠ 0) (hw : w ≠ 0) : Vl P (d * w) = Vl P d * Vl P w :=
  LemmaM.valN_mul _ hd hw

open scoped Classical in
/-- **`G(d, w)` for the small cofactors** (both parts). -/
lemma Gpair_le_beta {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hX0 : 0 < X0) (hδ : H X0 / X0 ≤ 1 / 1000) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hy : X0m ≤ y) {d w : ℕ} (hd : 2 ≤ d) (hw : 2 ≤ w) :
    Gpair P H tw X0m y X0 θ lam0 d w ≤
      if Win P H y X0 (d * w) then 2 / Vl P w * Rd P tw X0m y ε d else 0 := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hd0 : d ≠ 0 := by omega
  have hw0 : w ≠ 0 := by omega
  have hVd := KR.valN_labelVal_pos P d
  have hVw := KR.valN_labelVal_pos P w
  have hVw2 : 2 ≤ Vl P w := two_le_valN (fun p _ => hp2 _) hw
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
  have hdw : d * w / d = w := Nat.mul_div_cancel_left w (by omega)
  unfold Gpair stepBd
  by_cases hW : Win P H y X0 (d * w)
  · have hc : Win P H y X0 (d * w) ∧ d ≠ 1 := ⟨hW, by omega⟩
    rw [if_pos hc, if_pos hW, hdw, Vl_mul_eq hd0 hw0]
    have hpn := win_posn_ge hP hX0e hX0 hδ hW
    have hpd : X0m / 2 ≤ posn P.labelVal y d := by
      rw [posn_mul hval (Dvd.intro w rfl) (mul_ne_zero hd0 hw0), hdw]
      have hVw2' : (2 : ℝ) ≤ LemmaM.valN P.labelVal w := hVw2
      have := hP.X0m_pos
      nlinarith
    have hT := TVD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
    have hK := KRD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
    have hHn := hP.reg.pos (posn P.labelVal y (d * w))
    have hA : (if X0Near P.labelVal y H X0m d (d * w) then 1 / 2 * TVD P H tw X0m y d else 0) ≤
        1 / 2 * TVD P H tw X0m y d := by split_ifs <;> linarith
    have hB : (if |posn P.labelVal y (d * w) - X0| ≤ (1 + θ) * H (posn P.labelVal y (d * w)) / 2 +
          1.02 * H (posn P.labelVal y d) / Vl P w
        then lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w))) else 0) ≤
        lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w))) := by
      split_ifs
      · exact le_rfl
      · positivity
    have h1 := TVD_div_le_Rd hP hp2 ht hlam (by linarith) hy hd hpd (tw := tw) (ε := ε)
    have h2 := KRD_div_le hP hp2 ht hlam hy hd hw hpn (tw := tw)
    have hpow : Vl P w ^ (ε - 2) ≤ 1 / Vl P w := by
      have e1 : Vl P w ^ (ε - 2) = Vl P w ^ (ε - 1) / Vl P w := by
        rw [show ε - 2 = (ε - 1) - 1 by ring, Real.rpow_sub_one hVw.ne']
      rw [e1]
      apply div_le_div_of_nonneg_right _ hVw.le
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [hP.eps_le])
    have hl2 : lam0 ^ 2 / 4 ≤ 0.2506 := by nlinarith
    calc ((if X0Near P.labelVal y H X0m d (d * w) then 1 / 2 * TVD P H tw X0m y d else 0) +
          (if |posn P.labelVal y (d * w) - X0| ≤ (1 + θ) * H (posn P.labelVal y (d * w)) / 2 +
              1.02 * H (posn P.labelVal y d) / Vl P w
            then lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w)))
            else 0)) / (Vl P d * Vl P w)
        ≤ (1 / 2 * TVD P H tw X0m y d +
            lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w)))) /
            (Vl P d * Vl P w) := by
          apply div_le_div_of_nonneg_right (add_le_add hA hB) (by positivity)
      _ = (1 / 2 * TVD P H tw X0m y d / Vl P d) / Vl P w +
            lam0 * KRD P H tw X0m y d / (Vl P w * H (posn P.labelVal y (d * w))) /
              (Vl P d * Vl P w) := by
          field_simp
      _ ≤ Rd P tw X0m y ε d / Vl P w + lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d :=
          add_le_add (div_le_div_of_nonneg_right h1 hVw.le) h2
      _ ≤ Rd P tw X0m y ε d / Vl P w + 0.2506 * (1 / Vl P w) * Rd P tw X0m y ε d := by
          gcongr
      _ ≤ 2 / Vl P w * Rd P tw X0m y ε d := by
          have hq : 0 ≤ Rd P tw X0m y ε d / Vl P w := by positivity
          have e1 : 2 / Vl P w * Rd P tw X0m y ε d = 2 * (Rd P tw X0m y ε d / Vl P w) := by ring
          have e2 : 0.2506 * (1 / Vl P w) * Rd P tw X0m y ε d =
              0.2506 * (Rd P tw X0m y ε d / Vl P w) := by ring
          rw [e1, e2]; linarith
  · have hc : ¬ (Win P H y X0 (d * w) ∧ d ≠ 1) := fun h => hW h.1
    rw [if_neg hc, if_neg hW, zero_div]

open scoped Classical in
/-- **`G(d, w)` for the large cofactors**: the two parts kept apart. -/
lemma Gpair_le_gamma {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hX0 : 0 < X0) (hδ : H X0 / X0 ≤ 1 / 1000)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0)
    (hy : X0m ≤ y) {d w : ℕ} (hd : 2 ≤ d) (hw : 2 ≤ w) :
    Gpair P H tw X0m y X0 θ lam0 d w ≤
      (if X0Near P.labelVal y H X0m d (d * w)
        then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) +
      (if Win P H y X0 (d * w)
        then lam0 ^ 2 / 4 * Vl P w ^ (ε - 2) * Rd P tw X0m y ε d else 0) := by
  have hd0 : d ≠ 0 := by omega
  have hw0 : w ≠ 0 := by omega
  have hVd := KR.valN_labelVal_pos P d
  have hVw := KR.valN_labelVal_pos P w
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
  have hdw : d * w / d = w := Nat.mul_div_cancel_left w (by omega)
  have hT := TVD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
  have hK := KRD_nonneg (P := P) (H := H) (tw := tw) (X0m := X0m) (y := y) d
  have hX0n : 0 ≤ (if X0Near P.labelVal y H X0m d (d * w)
        then 1 / 2 * TVD P H tw X0m y d / Vl P d / Vl P w else 0) := by
    split_ifs <;> positivity
  have hpw : 0 ≤ Vl P w ^ (ε - 2) := Real.rpow_nonneg hVw.le _
  unfold Gpair stepBd
  by_cases hW : Win P H y X0 (d * w)
  · have hc : Win P H y X0 (d * w) ∧ d ≠ 1 := ⟨hW, by omega⟩
    rw [if_pos hc, if_pos hW, hdw, Vl_mul_eq hd0 hw0, add_div]
    have hpn := win_posn_ge hP hX0e hX0 hδ hW
    have hHn := hP.reg.pos (posn P.labelVal y (d * w))
    apply add_le_add
    · split_ifs
      · field_simp; rfl
      · simp
    · have h2 := KRD_div_le hP hp2 ht hlam hy hd hw hpn (tw := tw) (ε := ε)
      split_ifs
      · exact h2
      · rw [zero_div]; positivity
  · have hc : ¬ (Win P H y X0 (d * w) ∧ d ≠ 1) := fun h => hW h.1
    rw [if_neg hc, if_neg hW, zero_div, add_zero]
    exact hX0n

end KR.RML9

end
