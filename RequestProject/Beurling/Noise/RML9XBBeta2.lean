module

public import RequestProject.Beurling.Noise.RML9XBBeta

/-!
# Proposition 5.31(iii): `∑ R(d)` over the window of a small cofactor `w ≤ W₁ = e^{100}`

`Rdwin_bound` : by (TVD-sums) (`Rd_win_le`), Lemma 5.32 (`SD_le_SI`) for `m ≤ N^{1/20}/w`, the
trivial bound (`SD_le_harm`) and the tail of `A₀` (`tail_hord`) for larger `m`:
`∑_{V(d) ∈ (N/w)[1∓1.7δ]} R(d) ≤ 250δ((Λ + log w + 1.4)(1 + A₀) + A₁)/J + e^{-Λ}/J`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.RML9

open KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **The window sum of `R` at a small cofactor** (Proposition 5.31(iii), (β)). -/
theorem Rdwin_bound {Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hXl : 100000000 ≤ Real.log X0m) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hXm0 : 0 < X0m)
    (hXm : X0m ≤ (X0 : ℝ)) (hXm2 : (X0 : ℝ) ≤ 2 * X0m) (hy : X0m ≤ y)
    (hJ : 600 * Real.log X0 ^ 4 ≤ Real.log (y / X0)) {δ : ℝ}
    (hδ0 : Real.exp (-Real.log X0) ≤ δ) (hδ1 : δ ≤ 1 / 1000) (hZ : 2 * y / X0m ≤ Z)
    (hT : LocalPNT.Theorem524Concl P X0 (2 * (y / X0) ^ (0.55 : ℝ))) {ε : ℝ} (hε : ε ≤ 0.005)
    {Vw : ℝ} (hw1 : 1 ≤ Vw) (hw2 : Vw ≤ Real.exp 100) :
    ∑ d ∈ Dset P X0m y, (if y / X0 / Vw * (1 - 1.7 * δ) ≤ Vl P d ∧
        Vl P d ≤ y / X0 / Vw * (1 + 1.7 * δ) then Rd P tw X0m y ε d else 0) ≤
      250 * δ * ((Real.log X0 + Real.log Vw + 1.4) * 3.0674 + 9.4091) / Real.log (y / X0) +
        Real.exp (-Real.log X0) / Real.log (y / X0) := by
  set Λ := Real.log X0 with hΛdef
  set N := y / X0 with hNdef
  set J := Real.log N with hJdef
  set a := 1.7 * δ with ha
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm0 hXm
  have hΛ : 100000000 ≤ Λ := hXl.trans (Real.log_le_log hXm0 hXm)
  have hy0 : 0 < y := by linarith
  have hN0 : 0 < N := by positivity
  have hΛ4 : (100000000 : ℝ) ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ (by norm_num) hΛ 4
  have hJ0 : 2000 ≤ J := by nlinarith
  have hδpos : 0 < δ := lt_of_lt_of_le (Real.exp_pos _) hδ0
  have hw0 : 0 < Vw := by linarith
  have hlw0 : 0 ≤ Real.log Vw := Real.log_nonneg hw1
  have hlw : Real.log Vw ≤ 100 := by
    calc Real.log Vw ≤ Real.log (Real.exp 100) := Real.log_le_log hw0 hw2
      _ = 100 := Real.log_exp 100
  set c := Λ + Real.log Vw + 1.4 with hc
  have hc0 : 0 ≤ c := by linarith
  set hB := Real.log (2 * y / X0m) + 1 with hhB
  have hSI := fun (M : ℝ) (h0 : 0 < M) (h1 : 0.95 * J ≤ Real.log M) (h2 : M ≤ N) =>
    SD_le_SI (tw := tw) h hΛ ht htv hXm0 hXm hy hJ hδ0 hδ1 hZ hT h0 h1 h2
  -- the term `m = 1`
  have hS0 : SD P tw X0m y a (N / Vw) ≤ 250 * δ * c / J := by
    have hl : Real.log (N / Vw) = J - Real.log Vw := Real.log_div hN0.ne' hw0.ne'
    have := hSI (N / Vw) (by positivity) (by rw [hl]; linarith)
      (div_le_self hN0.le hw1)
    rwa [show N / (N / Vw) = Vw by field_simp] at this
  -- the terms `m ≥ 2`
  set L := 0.05 * J - Real.log Vw with hL
  have hm : ∀ m ∈ Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
      SD P tw X0m y a (N / Vw / Vl P m) ≤
      250 * δ * c / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) +
      250 * δ / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) * Real.log (Vl P m)) +
      hB * (if L < Real.log (Vl P m)
        then (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) else 0) := by
    intro m hmD
    have hV := KR.valN_labelVal_pos P m
    have hV1 : 1 ≤ Vl P m := KR.one_le_valN_label P m
    have hlV : 0 ≤ Real.log (Vl P m) := Real.log_nonneg hV1
    have hHV : 0 ≤ (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hV.le _)
    have hA : 0 ≤ 250 * δ / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
        Real.log (Vl P m)) := by positivity
    have hA' : 0 ≤ 250 * δ * c / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) := by
      positivity
    by_cases hcm : L < Real.log (Vl P m)
    · rw [if_pos hcm]
      have := SD_le_harm (P := P) (tw := tw) (a := a) (M := N / Vw / Vl P m) h ht hXm0 hy hZ
      have := mul_le_mul_of_nonneg_left this hHV
      nlinarith
    · rw [if_neg hcm, mul_zero, add_zero]
      have hl : Real.log (N / Vw / Vl P m) = J - Real.log Vw - Real.log (Vl P m) := by
        rw [Real.log_div (by positivity) hV.ne', Real.log_div hN0.ne' hw0.ne']
      have hle : N / Vw / Vl P m ≤ N :=
        (div_le_self (by positivity) hV1).trans (div_le_self hN0.le hw1)
      have := hSI (N / Vw / Vl P m) (by positivity) (by rw [hl]; linarith) hle
      rw [show N / (N / Vw / Vl P m) = Vw * Vl P m by field_simp,
        Real.log_mul hw0.ne' hV.ne'] at this
      rw [← hNdef, ← hJdef, ← hΛdef, ← ha] at this
      have := mul_le_mul_of_nonneg_left this hHV
      have e : (BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
          (250 * δ * (Λ + (Real.log Vw + Real.log (Vl P m)) + 1.4) / J) =
          250 * δ * c / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2)) +
          250 * δ / J * ((BSCert.X0Band.Hord m : ℝ) * Vl P m ^ (ε - 2) *
            Real.log (Vl P m)) := by rw [hc]; ring
      linarith
  have hsB := hordSumsB P h hXl (ε := ε) (by linarith) hZ (Dset P X0m y)
    (fun m hm => ⟨(mem_Dset.mp hm).2, Dset_val_le hm⟩)
  have htl := tail_hord h hXl hε hZ L (P := P)
  have hsum := Finset.sum_le_sum hm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the tail numerics
  have hB0 : 0 ≤ hB := by
    have : 1 ≤ 2 * y / X0m := by rw [le_div_iff₀ hXm0]; linarith
    have := Real.log_nonneg this; linarith
  have hBJ : hB ≤ J + 3 := by
    have h4 : 2 * y / X0m ≤ 4 * N := by
      rw [div_le_iff₀ hXm0, hNdef]
      have : y / X0 * X0 = y := by field_simp
      nlinarith
    have : Real.log (2 * y / X0m) ≤ Real.log 4 + J := by
      rw [hJdef, ← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) h4
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith
  have hexpL : Real.exp (-(0.04 * L)) ≤ Real.exp (4 - 0.002 * J) :=
    Real.exp_le_exp.mpr (by rw [hL]; linarith)
  have htn := tail_num hΛ hJ
  have htail : hB * (2.2181 * Real.exp (-(0.04 * L))) ≤ Real.exp (-Λ) / J := by
    calc hB * (2.2181 * Real.exp (-(0.04 * L)))
        ≤ (J + 3) * (2.2181 * Real.exp (4 - 0.002 * J)) := by
          apply mul_le_mul hBJ (by linarith) (by positivity) (by linarith)
      _ = (J + 3) * 2.2181 * Real.exp (4 - 0.002 * J) := by ring
      _ ≤ _ := htn
  have hJpos : 0 < J := by linarith
  have hk1 : 0 ≤ 250 * δ * c / J := by positivity
  have hk2 : 0 ≤ 250 * δ / J := by positivity
  calc _ ≤ SD P tw X0m y a (N / Vw) + ∑ m ∈ Dset P X0m y, (BSCert.X0Band.Hord m : ℝ) *
          Vl P m ^ (ε - 2) * SD P tw X0m y a (N / Vw / Vl P m) := Rd_win_le ε a (N / Vw)
    _ ≤ 250 * δ * c / J + (250 * δ * c / J * 2.0674 + 250 * δ / J * 9.4091 +
          hB * (2.2181 * Real.exp (-(0.04 * L)))) := by
        apply add_le_add hS0
        refine hsum.trans ?_
        gcongr
        · exact hsB.1
        · exact hsB.2
    _ ≤ 250 * δ * (c * 3.0674 + 9.4091) / J + Real.exp (-Λ) / J := by
        have e : 250 * δ * c / J + (250 * δ * c / J * 2.0674 + 250 * δ / J * 9.4091) =
            250 * δ * (c * 3.0674 + 9.4091) / J := by ring
        linarith

end KR.RML9

end
