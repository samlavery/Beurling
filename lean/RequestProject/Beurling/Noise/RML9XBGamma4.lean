module

public import RequestProject.Beurling.Noise.RML9XBGamma3

/-!
# Proposition 5.31(iii), part (γ′): summing the dyadic blocks

`dyadic_le` : for `V₀ ≥ X₀ ≥ X₀⁻`, with `K_c = 3.0674 Λ + 320`,
`∑_{d, y/d ≥ V₀} c (y/(dX₀))^{-3/4} R(d) ≤ 4 c C_S K_c (V₀/X₀)^{-0.74}/log y`
(the blocks `y/d ∈ [v, 2v)`, `v = V₀2^k`, by `Rd_block_le`, and the geometric series
`sum_sep_le` with ratio `2^{-0.74} ≤ 3/4`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

lemma two_rpow_le : (2 : ℝ) ^ (-(0.74 : ℝ)) ≤ 0.75 := by
  have h1 : (2 : ℝ) ^ (-(0.74 : ℝ)) ≤ 2 ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 2 := by
    rw [Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow]; simp
  have h3 : (1.4 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [h2] at h1
  have : 1 / Real.sqrt 2 ≤ 1 / 1.4 := one_div_le_one_div_of_le (by norm_num) h3
  linarith

lemma log_le_rpow {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ 100 * t ^ (0.01 : ℝ) := by
  have h0 : 0 < t := by linarith
  have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h0 (0.01 : ℝ))
  rw [Real.log_rpow h0] at this
  have h1 : 0 ≤ t ^ (0.01 : ℝ) := (Real.rpow_pos_of_pos h0 _).le
  nlinarith

/-- `t^{-3/4}(3.0674 log(2X₀t) + 9.4091) ≤ (3.0674 log X₀ + 320) t^{-0.74}` for `t ≥ 1`. -/
lemma block_num {X0 t : ℝ} (hX : 1 ≤ X0) (ht : 1 ≤ t) :
    t ^ (-(3 / 4 : ℝ)) * (3.0674 * Real.log (2 * (X0 * t)) + 9.4091) ≤
      (3.0674 * Real.log X0 + 320) * t ^ (-(0.74 : ℝ)) := by
  have h0 : 0 < t := by linarith
  have hX0 : 0 < X0 := by linarith
  have hl : Real.log (2 * (X0 * t)) = Real.log 2 + Real.log X0 + Real.log t := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hX0.ne' h0.ne']; ring
  have hl2 := Real.log_two_lt_d9
  have hlX := Real.log_nonneg hX
  have hlt := log_le_rpow ht
  have hs1 : 1 ≤ t ^ (0.01 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have e : t ^ (-(0.74 : ℝ)) = t ^ (-(3 / 4 : ℝ)) * t ^ (0.01 : ℝ) := by
    rw [← Real.rpow_add h0]; norm_num
  rw [e, hl]
  have hp : 0 < t ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos h0 _
  have : 3.0674 * (Real.log 2 + Real.log X0 + Real.log t) + 9.4091 ≤
      (3.0674 * Real.log X0 + 320) * t ^ (0.01 : ℝ) := by nlinarith
  calc t ^ (-(3 / 4 : ℝ)) * (3.0674 * (Real.log 2 + Real.log X0 + Real.log t) + 9.4091)
      ≤ t ^ (-(3 / 4 : ℝ)) * ((3.0674 * Real.log X0 + 320) * t ^ (0.01 : ℝ)) :=
        mul_le_mul_of_nonneg_left this hp.le
    _ = _ := by ring

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **The dyadic sum of (γ′).** -/
theorem dyadic_le {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hy : X0m ≤ y) (hZ : 2 * y / X0m ≤ Z)
    {ε : ℝ} (hε : ε ≤ 0.03) {X0 V0 c : ℝ} (hXm : X0m ≤ X0) (hV0 : X0 ≤ V0) (hc : 0 ≤ c) :
    ∑ d ∈ Dset P X0m y, (if V0 ≤ posn P.labelVal y d
      then c * (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d else 0) ≤
      4 * (c * CSc * (3.0674 * Real.log X0 + 320) / Real.log y * (V0 / X0) ^ (-(0.74 : ℝ))) := by
  have hXm0 := h.X0m_pos
  have hX1 : 1 < X0m := by
    by_contra hc; push_neg at hc
    have := Real.log_le_log hXm0 hc
    rw [Real.log_one] at this; linarith
  have hX0 : 0 < X0 := by linarith
  have hV0p : 0 < V0 := by linarith
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hCS : 0 ≤ CSc := le_max_of_le_right (by norm_num)
  set Kc := 3.0674 * Real.log X0 + 320 with hKc
  have hKc0 : 0 ≤ Kc := by have := Real.log_nonneg (show 1 ≤ X0 by linarith); positivity
  set F : ℕ → ℝ := fun d => if V0 ≤ posn P.labelVal y d
    then c * (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) * Rd P tw X0m y ε d else 0 with hF
  have hF0 : ∀ d, 0 ≤ F d := by
    intro d
    have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
    simp only [hF]
    split_ifs with h1
    · have : 0 ≤ (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_nonneg (div_nonneg (by linarith) hX0.le) _
      positivity
    · exact le_rfl
  obtain ⟨K, -, hK⟩ := KR.TNP.exists_N (show 0 < 4 * V0 by positivity) y
  set S := KR.TNP.dyScales (4 * V0) y K with hS
  have hSv : ∀ v ∈ S, V0 ≤ v ∧ v ≤ y := by
    intro v hv
    obtain ⟨k, -, rfl, hvy⟩ := KR.TNP.mem_dyScales.mp hv
    refine ⟨?_, hvy⟩
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  -- every `d` lies in a block
  have hcov : ∀ d ∈ Dset P X0m y, F d ≤ ∑ v ∈ S,
      (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v then F d else 0) := by
    intro d _
    by_cases hd : V0 ≤ posn P.labelVal y d
    · have hpy : posn P.labelVal y d ≤ y := div_le_self hy0.le (KR.one_le_valN_label P d)
      obtain ⟨v, hvS, hv1, hv2⟩ := KR.TNP.dyScales_cover (show 0 < 4 * V0 by positivity) hK
        (show 4 * V0 / 4 ≤ posn P.labelVal y d by linarith) hpy
      have := Finset.single_le_sum (f := fun v => if v ≤ posn P.labelVal y d ∧
        posn P.labelVal y d < 2 * v then F d else 0) (fun v _ => by
          dsimp only
          split_ifs
          · exact hF0 d
          · exact le_rfl) hvS
      simp only [hv1, hv2, and_self, if_true] at this
      exact this
    · have : F d = 0 := by simp only [hF, if_neg hd]
      rw [this]
      exact Finset.sum_nonneg fun v _ => by split_ifs <;> simp
  -- one block
  set g : ℝ → ℝ := fun v => c * CSc * Kc / Real.log y * (v / X0) ^ (-(0.74 : ℝ)) with hg
  have hblock : ∀ v ∈ S, ∑ d ∈ Dset P X0m y,
      (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v then F d else 0) ≤ g v := by
    intro v hvS
    obtain ⟨hv1, hv2⟩ := hSv v hvS
    have ht1 : 1 ≤ v / X0 := by rw [le_div_iff₀ hX0]; linarith
    have htp : 0 < v / X0 := by linarith
    have hpt : ∀ d ∈ Dset P X0m y,
        (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v then F d else 0) ≤
        c * (v / X0) ^ (-(3 / 4 : ℝ)) * (if v ≤ posn P.labelVal y d ∧
          posn P.labelVal y d < 2 * v then Rd P tw X0m y ε d else 0) := by
      intro d _
      have hRd := Rd_nonneg (P := P) (tw := tw) (X0m := X0m) (y := y) ε d
      have hp0 : 0 ≤ (v / X0) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg htp.le _
      by_cases hb : v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v
      · rw [if_pos hb, if_pos hb]
        simp only [hF]
        split_ifs with hV
        · have : (posn P.labelVal y d / X0) ^ (-(3 / 4 : ℝ)) ≤ (v / X0) ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos htp (div_le_div_of_nonneg_right hb.1 hX0.le)
              (by norm_num)
          have := mul_le_mul_of_nonneg_right this hRd
          have := mul_le_mul_of_nonneg_left this hc
          linarith
        · positivity
      · rw [if_neg hb, if_neg hb, mul_zero]
    have hB := Rd_block_le h hXl ht htv hy hZ hε (by linarith) hv2 (P := P) (tw := tw)
    have hn := block_num (show 1 ≤ X0 by linarith) ht1
    rw [show X0 * (v / X0) = v by field_simp] at hn
    calc _ ≤ ∑ d ∈ Dset P X0m y, c * (v / X0) ^ (-(3 / 4 : ℝ)) * (if v ≤ posn P.labelVal y d ∧
            posn P.labelVal y d < 2 * v then Rd P tw X0m y ε d else 0) := Finset.sum_le_sum hpt
      _ = c * (v / X0) ^ (-(3 / 4 : ℝ)) * ∑ d ∈ Dset P X0m y, (if v ≤ posn P.labelVal y d ∧
            posn P.labelVal y d < 2 * v then Rd P tw X0m y ε d else 0) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ c * (v / X0) ^ (-(3 / 4 : ℝ)) *
            (CSc * (3.0674 * Real.log (2 * v) + 9.4091) / Real.log y) := by
          apply mul_le_mul_of_nonneg_left hB
          exact mul_nonneg hc (Real.rpow_nonneg htp.le _)
      _ = c * CSc / Real.log y * ((v / X0) ^ (-(3 / 4 : ℝ)) *
            (3.0674 * Real.log (2 * v) + 9.4091)) := by ring
      _ ≤ c * CSc / Real.log y * (Kc * (v / X0) ^ (-(0.74 : ℝ))) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = g v := by simp only [hg]; ring
  -- the geometric series
  have hsep : KR.X0S.Sep2 S := fun v hv w hw hvw =>
    KR.TNP.dyScales_sep (show 0 < 4 * V0 by positivity) v hv w hw hvw
  have hgeo := KR.X0S.sum_sep_le (g := g) (V0 := V0) (r := 0.75) hV0p (by norm_num)
    (by norm_num)
    (fun v hv => by
      have : 0 ≤ (v / X0) ^ (-(0.74 : ℝ)) :=
        Real.rpow_nonneg (div_nonneg (by linarith) hX0.le) _
      simp only [hg]; positivity)
    (fun v w hv hvw => by
      simp only [hg]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) hX0)
        (div_le_div_of_nonneg_right hvw hX0.le) (by norm_num))
    (fun v hv => by
      simp only [hg]
      have hvp : 0 < v / X0 := div_pos (by linarith) hX0
      have e : 2 * v / X0 = 2 * (v / X0) := by ring
      rw [e, Real.mul_rpow (by norm_num) hvp.le]
      have hk : 0 ≤ c * CSc * Kc / Real.log y := by positivity
      have hq : 0 ≤ (v / X0) ^ (-(0.74 : ℝ)) := Real.rpow_nonneg hvp.le _
      have := two_rpow_le
      calc c * CSc * Kc / Real.log y * (2 ^ (-(0.74 : ℝ)) * (v / X0) ^ (-(0.74 : ℝ)))
          = 2 ^ (-(0.74 : ℝ)) * (c * CSc * Kc / Real.log y * (v / X0) ^ (-(0.74 : ℝ))) := by
            ring
        _ ≤ 0.75 * (c * CSc * Kc / Real.log y * (v / X0) ^ (-(0.74 : ℝ))) :=
            mul_le_mul_of_nonneg_right this (by positivity))
    S hsep (fun v hv => (hSv v hv).1)
  calc ∑ d ∈ Dset P X0m y, F d
      ≤ ∑ d ∈ Dset P X0m y, ∑ v ∈ S,
          (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v then F d else 0) :=
        Finset.sum_le_sum hcov
    _ = ∑ v ∈ S, ∑ d ∈ Dset P X0m y,
          (if v ≤ posn P.labelVal y d ∧ posn P.labelVal y d < 2 * v then F d else 0) :=
        Finset.sum_comm
    _ ≤ ∑ v ∈ S, g v := Finset.sum_le_sum hblock
    _ ≤ g V0 / (1 - 0.75) := hgeo
    _ = 4 * (c * CSc * Kc / Real.log y * (V0 / X0) ^ (-(0.74 : ℝ))) := by
        simp only [hg]; ring

end KR.RML9

end
