module

public import RequestProject.Beurling.BaseRange.HoneG
public import RequestProject.Beurling.BaseRange.MismatchG
public import RequestProject.Beurling.BaseRange.CoreReal

/-!
# Lemma 7.3(d)(iii): the telescoping with `g` (`KDiffBound`)

`kDiffBound_of` : **`|(K'_ℚ - K_pt) g(u)| ≤ 4κ (log u)³` on `[X₀, x_max]`**, under the hypotheses
of `lemma73bCore_of` and (huxley). The proof of (d)(iii): the operators are compared through the
strict value-order operator of each system (`kQ'_eq_kvalG`, `kpt_sub_kvalG_le` with
`sup |g| ≤ 1.01/Λ`), and Step 3 of (b) is run with the kernel `G(t, M) = 1[M t < u] g(u/t)/t`
(`kval_diffG`, with the one-replacement bound `hone_g`).

`lemma73diii_full` : **Lemma 7.3(d)(iii) for `ρ_edge`** (from `lemma73diii_of`, `gEdge_bound`
and `kDiffBound_of`).
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-- `sup |g| ≤ 1.01/Λ`. -/
lemma abs_gEdge_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (z : ℝ) :
    |gEdge X0 z| ≤ 1.01 / Real.log X0 := by
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  have hΛ : 0 < Real.log X0 := by linarith
  rcases lt_or_ge z X0 with hz | hz
  · rw [gEdge_zero_below hX0 hz, abs_zero]; positivity
  have h := gEdge_bound hX hH z hz
  have hκs : Construction.kappaParam X0 ≤ 1 / 10 ^ 21 := kappa_le_tiny hX0 hX
  have h1 : (X0 : ℝ) / z ≤ 1 := by rw [div_le_one (by linarith)]; exact hz
  refine h.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hΛ]
  nlinarith

lemma maxV_mul_lt_iff (S : BeurlingSystem) {e : ℕ →₀ ℕ} (he : e ≠ 0) {V u : ℝ} (hV : 0 < V) :
    S3.maxV S e * V < u ↔ ∀ j ∈ e.support, S.p j * V < u := by
  rw [← lt_div_iff₀ hV]
  unfold S3.maxV
  rw [Finset.fold_max_lt]
  constructor
  · rintro ⟨-, h⟩ j hj; rw [← lt_div_iff₀ hV]; exact h j hj
  · intro h
    obtain ⟨j0, hj0⟩ := Finsupp.support_nonempty_iff.mpr he
    refine ⟨?_, fun j hj => by rw [lt_div_iff₀ hV]; exact h j hj⟩
    have := h j0 hj0
    have hp := S.p_pos j0
    rw [lt_div_iff₀ hV]; nlinarith

/-- `K'_ℚ g = ` the strict value-order operator of the rational system. -/
lemma kQ'_eq_kvalG {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u : ℝ} (hu : 0 < u) :
    KQ' X0 (gEdge X0) u = S3.KvalG ratSys (u / X0) (Gg X0 u) := by
  classical
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  unfold KQ'
  rw [kpt_h_eq ratSys tQ hX0 le_rfl hu (gEdge X0) (fun z hz => gEdge_zero_below hX0 hz)]
  unfold S3.KvalG
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 := (Finset.mem_filter.mp he).2
  have hv := ratSys.val_pos e
  unfold Gg
  have hiff : (∀ j ∈ e.support, tQ (qp j) * ratSys.val e < u) ↔
      S3.maxV ratSys e * ratSys.val e < u := by
    rw [maxV_mul_lt_iff ratSys he0 hv]
    rfl
  by_cases h : S3.maxV ratSys e * ratSys.val e < u
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- The numerics of `kDiffBound_of`. -/
lemma kdiff_numerics {κ L Λ lx B E A0 Q2 ηH : ℝ} (hκ0 : 0 < κ) (hΛ : 10 ^ 8 ≤ Λ)
    (hLΛ : Λ ≤ L) (hlx0 : 0 ≤ lx) (hlxL : lx ≤ L) (hB9 : B ≤ 9 * κ)
    (hE0 : 0 ≤ E) (hE : E ≤ 3 * L / Λ) (hA0 : A0 = 1.01 / Λ)
    (hQ2 : Q2 ≤ 12.8 * κ) (hηκ : ηH ≤ κ) :
    2.01 * B * (lx + 7) ^ 2 * (5 * Λ) / Λ * E + A0 * (5 * Λ) * Q2 * E +
        2 * (A0 * (Q2 * (lx + 1))) + 56 * A0 * ηH * (lx + 1) ≤ 4 * κ * L ^ 3 := by
  have hΛ0 : 0 < Λ := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hEL : E * Λ ≤ 3 * L := by rw [le_div_iff₀ hΛ0] at hE; linarith
  have hL7 : (lx + 7) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  have hLL : L ≤ L ^ 3 := by
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    nlinarith
  subst hA0
  -- multiply through by `Λ`
  have e : 2.01 * B * (lx + 7) ^ 2 * (5 * Λ) / Λ * E + 1.01 / Λ * (5 * Λ) * Q2 * E +
      2 * (1.01 / Λ * (Q2 * (lx + 1))) + 56 * (1.01 / Λ) * ηH * (lx + 1) =
      (10.05 * (B * (lx + 7) ^ 2) * (E * Λ) + 5.05 * Q2 * (E * Λ) +
        2.02 * (Q2 * (lx + 1)) + 56.56 * (ηH * (lx + 1))) / Λ := by
    field_simp; ring
  rw [e, div_le_iff₀ hΛ0]
  have h1 : B * (lx + 7) ^ 2 ≤ 9 * κ * (2 * L ^ 2) :=
    mul_le_mul hB9 hL7 (sq_nonneg _) (by positivity)
  have h1' : 10.05 * (B * (lx + 7) ^ 2) * (E * Λ) ≤ 10.05 * (9 * κ * (2 * L ^ 2)) * (3 * L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hEL (by positivity) (by positivity)
  have h2' : 5.05 * Q2 * (E * Λ) ≤ 5.05 * (12.8 * κ) * (3 * L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hQ2 (by norm_num)) hEL (by positivity) (by positivity)
  have h3' : Q2 * (lx + 1) ≤ 12.8 * κ * (2 * L) := mul_le_mul hQ2 (by linarith) (by linarith)
    (by positivity)
  have h4' : ηH * (lx + 1) ≤ κ * (2 * L) := mul_le_mul hηκ (by linarith) (by linarith) hκ0.le
  have hkL : κ * L ≤ κ * L ^ 3 := mul_le_mul_of_nonneg_left hLL hκ0.le
  have hk3 : 0 ≤ κ * L ^ 3 := by positivity
  have hb : κ * L ^ 3 * 1000 ≤ κ * L ^ 3 * (4 * Λ) := mul_le_mul_of_nonneg_left (by linarith) hk3
  nlinarith

/-- **`KDiffBound`** (proof of Lemma 7.3(d)(iii)): `|(K'_ℚ - K_pt) g(u)| ≤ 4κ (log u)³` on
`[X₀, x_max]`. -/
theorem kDiffBound_of {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    {X0 : ℕ} {xmax : ℝ} (h : P.HBS X0m Z η1 η2 ε1) (hX : 10 ^ 8 ≤ Real.log X0)
    (hH : HuxleyFrom X0)
    (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) (hZ : xmax / X0 ≤ Z) (hXZ : X0m ≤ Z)
    (hloc : ∀ v, X0m ≤ v → v ≤ Z → |P.N v - ⌊v⌋₊| ≤ Construction.hbsEps X0 v * v)
    (H : ℝ → ℝ)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    {ηH : ℝ} (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη0 : 0 ≤ ηH)
    (hηκ : ηH ≤ Construction.kappaParam X0) :
    KDiffBound P tw X0m X0 xmax := by
  intro u hu hux
  set κ := Construction.kappaParam (X0 : ℝ) with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX0 := X0_pos' hX
  have hXe := exp_one_le_X0 hX
  have hu0 : 0 < u := by linarith
  have hX7 := h.X0m_ge
  have hQ := ratSys_hbs (X0m := X0m) (Z := Z) hX7
  set x := u / (X0 : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hX0]; linarith
  have hxZ : x ≤ Z := (div_le_div_of_nonneg_right hux hX0.le).trans hZ
  set Λ := Real.log (X0 : ℝ) with hΛdef
  set L := Real.log u with hLdef
  have hΛ : 10 ^ 8 ≤ Λ := hX
  have hΛ0 : 0 < Λ := by linarith
  have hLΛ : Λ ≤ L := Real.log_le_log hX0 hu
  have hL1 : 1 ≤ L := by linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlxL : Real.log x ≤ L := Real.log_le_log (by linarith) (div_le_self hu0.le (by linarith))
  have hXm' : Real.exp 1 ≤ X0m / 2 := by
    have h4 : Real.exp 1 * 4 ≤ X0 := by
      rw [← Real.exp_log hX0]
      have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.exp 1 * 4 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
        _ = Real.exp 3 := by rw [← Real.exp_add, ← Real.exp_add]; norm_num
        _ ≤ Real.exp (Real.log X0) := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- the parameters
  set B := 2 * (4 * κ) + 2.1 / Real.sqrt (X0m / 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB9 : B ≤ 9 * κ := B_le hX hXm1
  set A0 := 1.01 / Λ with hA0def
  have hA00 : 0 ≤ A0 := by positivity
  have hgA : ∀ z, |gEdge X0 z| ≤ A0 := abs_gEdge_le hX hH
  have hG : ∀ t M, 0 < t → t ≤ x → |Gg X0 u t M| ≤ A0 / t := by
    intro t M ht _
    unfold Gg
    split_ifs
    · rw [abs_div, abs_of_pos ht]; exact div_le_div_of_nonneg_right (hgA _) ht.le
    · simp; positivity
  have hpq : ∀ j < J1 X0m, P.p j = ratSys.p j := fun j hj => (small_eq h hXZ hj).1
  have hΔ := thetaF_diff_le h (A := 4 * κ) (by positivity) hxZ hXZ (hloc_A h hX hXm1 hxZ hloc)
  have hD := D0_le h hX hXm1 hXm2 hXZ x
  have hone := hone_g (P := P) (Q := ratSys) (J1 := J1 X0m) hX hH hu hXm' hB0
    (fun j hj => large_ge h hXZ (Finset.mem_filter.mp hj).2)
    (fun j hj => large_ge hQ hXZ (Finset.mem_filter.mp hj).2) hΔ hD
  set c := 2.01 * B * (Real.log x + 7) ^ 2 * (5 * Λ) / Λ with hcdef
  have hc : 0 ≤ c := by positivity
  have h3 := S3.kval_diffG (P := P) (Q := ratSys) (J1 := J1 X0m) hpq x (Gg X0 u) hA00 hc hG
    (fun j hj => (small_eq h hXZ hj).2) (fun j hj => large_ge h hXZ hj)
    (fun j hj => (small_eq hQ hXZ hj).2) (fun j hj => large_ge hQ hXZ hj)
    hone hD (S1_le h hXZ hxZ) (S1_le hQ hXZ hxZ) (Q2_le h hXZ hxZ) (Q2_le hQ hXZ hxZ)
    (h.harm_le hx1 hxZ) (hQ.harm_le hx1 hxZ)
  have hm := kpt_sub_kvalG_le P tw H hXe (by linarith) hXm2 hu0 (gEdge X0)
    (fun z hz => gEdge_zero_below hX0 hz) hgA hdhi hdlo hlip hsmall hcount hrat hη0
    (h.harm_le hx1 hxZ)
  rw [kQ'_eq_kvalG hX hu0]
  set E := Real.exp (Real.log (Real.log (max x (X0m / 2)) / Real.log (X0m / 2)) +
    2.2 / Real.log (X0m / 2)) with hEdef
  have hE : E ≤ 3 * L / Λ := exp_S1_le hX hXm1 hXm2 hu
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hQ2 : 12.8 / X0m ≤ 12.8 * κ := by
    have := inv_X0m_le hX hXm1
    rw [div_eq_mul_one_div]; nlinarith
  have hQ20 : 0 ≤ 12.8 / X0m := by positivity
  have htri : |S3.KvalG ratSys x (Gg X0 u) - KR.Sharp.Kpt P tw X0m (gEdge X0) u| ≤
      |S3.KvalG P x (Gg X0 u) - S3.KvalG ratSys x (Gg X0 u)| +
        |KR.Sharp.Kpt P tw X0m (gEdge X0) u - S3.KvalG P x (Gg X0 u)| := by
    have := abs_sub_le (S3.KvalG ratSys x (Gg X0 u)) (S3.KvalG P x (Gg X0 u))
      (KR.Sharp.Kpt P tw X0m (gEdge X0) u)
    rw [abs_sub_comm (S3.KvalG ratSys x (Gg X0 u)) (S3.KvalG P x (Gg X0 u)),
      abs_sub_comm (S3.KvalG P x (Gg X0 u)) (KR.Sharp.Kpt P tw X0m (gEdge X0) u)] at this
    exact this
  have hm' : |KR.Sharp.Kpt P tw X0m (gEdge X0) u - S3.KvalG P x (Gg X0 u)| ≤
      56 * A0 * ηH * (Real.log x + 1) := hm
  refine htri.trans ((add_le_add h3 hm').trans ?_)
  exact kdiff_numerics hκ0 hΛ hLΛ hlx0 hlxL hB9 hE0 hE hA0def hQ2 hηκ

end BaseRange
