module

public import RequestProject.Beurling.Noise.RML6G1B1

/-!
# Field `g1`, range (B): Steps 2–4 of the proof of Proposition 5.35(B), averaged

* `step2_avg` : **Step 2** (`ρ^sh` against `ρ̃` on average). From the decomposition
  `ρ̃ - ρ^sh = [ρ̃ + ν + NT - B R_res T'] - ν - NT + [B R_res T' - B ρ^sh] + (B ρ^sh - ρ^sh)`
  and the pointwise bounds on `J` (Lemma 5.34: `|ρ̃ + ν + NT - B R_res T'| ≤ ε_N/L`;
  Proposition 5.26 with Lemma 5.27: `|B R_res T' - B ρ^sh| ≤ (E_BR + j)/L`; `|ν| ≤ ν̄`,
  `|NT| ≤ 54η`) and the boundary term `∫_J (B ρ^sh - ρ^sh) ≤ Bnd`:
  `avg_J ρ^sh ≥ avg_J ρ̃ - (ε_N + E_BR + j + o₂)/L`, `o₂ = L(ν̄ + 54η) + L·Bnd/|J|`.
* `step34_avg` : **Steps 3–4** (pointwise against average): if `ρ^sh(y) - ρ^sh(x) ≤ o₃/L` on
  `J`, then `ρ^sh(x) ≥ avg_J ρ^sh - o₃/L`.
* `window_small` : the boundary term is negligible: with the range-(B) hypotheses on `δ`,
  `L · (1/δ) · (F/x) ≤ e^{-71}` for `0 ≤ F ≤ 40√x` (used for `Bnd ≤ 4H(x)(log x + 1)`,
  `H(x) ≤ x^{1/8}`).
-/

@[expose] public section

open Real MeasureTheory Set

namespace KR.RML6

/-- **Step 2 of Proposition 5.35(B)**, averaged over `J = [a, b]`. -/
theorem step2_avg {a b L εN EBR j nb η Bnd : ℝ} {ρt ρs Bρs ν NT BRT : ℝ → ℝ} (hab : a < b)
    (hL : 0 < L) (hit : IntervalIntegrable ρt volume a b)
    (his : IntervalIntegrable ρs volume a b) (hiB : IntervalIntegrable Bρs volume a b)
    (h34 : ∀ y ∈ Icc a b, |ρt y + ν y + NT y - BRT y| ≤ εN / L)
    (hbr : ∀ y ∈ Icc a b, |BRT y - Bρs y| ≤ (EBR + j) / L)
    (hν : ∀ y ∈ Icc a b, |ν y| ≤ nb) (hNT : ∀ y ∈ Icc a b, |NT y| ≤ 54 * η)
    (hbd : ∫ y in a..b, (Bρs y - ρs y) ≤ Bnd) :
    (∫ y in a..b, ρt y) / (b - a) -
        (εN + EBR + j + (L * (nb + 54 * η) + L * Bnd / (b - a))) / L ≤
      (∫ y in a..b, ρs y) / (b - a) := by
  set C := εN / L + nb + 54 * η + (EBR + j) / L
  have hpt : ∀ y ∈ Icc a b, ρt y - C - (Bρs y - ρs y) ≤ ρs y := by
    intro y hy
    have h1 := (abs_le.mp (h34 y hy)).2
    have h2 := (abs_le.mp (hbr y hy)).2
    have h3 := (abs_le.mp (hν y hy)).1
    have h4 := (abs_le.mp (hNT y hy)).1
    simp only [C]
    linarith
  have hmono := intervalIntegral.integral_mono_on hab.le
    ((hit.sub intervalIntegrable_const).sub (hiB.sub his)) his hpt
  rw [intervalIntegral.integral_sub (hit.sub intervalIntegrable_const) (hiB.sub his),
    intervalIntegral.integral_sub hit intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hba : 0 < b - a := by linarith
  rw [div_sub' hba.ne', div_le_div_iff_of_pos_right hba]
  have e : (εN + EBR + j + (L * (nb + 54 * η) + L * Bnd / (b - a))) / L * (b - a) =
      (b - a) * C + Bnd := by
    simp only [C]; field_simp; ring
  have e' : (b - a) * ((εN + EBR + j + (L * (nb + 54 * η) + L * Bnd / (b - a))) / L) =
      (b - a) * C + Bnd := by rw [mul_comm]; exact e
  rw [e']
  linarith

/-- **Steps 3–4 of Proposition 5.35(B)**, averaged over `J = [a, b]`. -/
theorem step34_avg {a b L o3 ρx : ℝ} {ρs : ℝ → ℝ} (hab : a < b)
    (his : IntervalIntegrable ρs volume a b) (hpt : ∀ y ∈ Icc a b, ρs y - ρx ≤ o3 / L) :
    (∫ y in a..b, ρs y) / (b - a) - o3 / L ≤ ρx := by
  have hmono := intervalIntegral.integral_mono_on hab.le his
    (intervalIntegrable_const (c := ρx + o3 / L))
    (fun y hy => by have := hpt y hy; linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hba : 0 < b - a := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ hba]
  nlinarith

/-- **The window terms are negligible in range (B)**: under the hypotheses on `δ` of `step1_g1`,
`L · (1/δ) · (F/x) ≤ e^{-71}` for `0 ≤ F ≤ 40√x`. -/
theorem window_small {X₀ : ℕ} {x δ F : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hx0 : 0 < x)
    (hx : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log x) (_hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log x) / 2) *
      Real.log x ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ))
    (hF0 : 0 ≤ F) (hF : F ≤ 40 * √x) :
    Real.log x * (1 / δ) * (F / x) ≤ Real.exp (-71) := by
  set Λ := Real.log X₀ with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have hrp : ∀ a : ℝ, (X₀ : ℝ) ^ a = Real.exp (a * Λ) := fun a => by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  set L := Real.log x with hLdef
  have hL : Real.exp (Λ / 100) ≤ L := by
    rw [hrp] at hx; convert! hx using 2; ring
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hxe : x = Real.exp L := (Real.exp_log hx0).symm
  have hs := sqrt_log_ge hΛ hL
  set s := √L with hsdef
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hΛ3 : 0 < Λ ^ 3 := pow_pos hΛ0 3
  have hs0 : 0 < s := by nlinarith
  set c := LocalPNT.cLP Λ with hcdef
  have hc : c = 0.0176 / Λ := by
    rw [hcdef]; unfold LocalPNT.cLP LocalPNT.cZF; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨-, hex2⟩ := step1_exponents hΛ hs
  rw [← hc] at hex2
  have hL4 : L ^ 4 = Real.exp (8 * Real.log s) := by
    rw [← hss, ← pow_mul, show 8 * Real.log s = ((2 * 4 : ℕ) : ℝ) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs0]
  have hlogs : Real.log s ≤ 2 * √s := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hs0)
    rw [Real.log_sqrt hs0.le] at h
    linarith [Real.sqrt_nonneg s]
  have hΛ3' : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by nlinarith)
  have hinvδ : 1 / δ ≤ 2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2) := by
    refine hδlow.trans ?_
    rw [hL4, hrp, ← Real.exp_add, two_mul]
    apply add_le_add
    · apply Real.exp_le_exp.mpr; linarith
    · apply Real.exp_le_exp.mpr
      have : 0 ≤ c * s := by positivity
      linarith
  have hLs : L = Real.exp (2 * Real.log s) := by
    rw [← hss, show (2 : ℝ) * Real.log s = ((2 : ℕ) : ℝ) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs0]
  have hsqx : √x = Real.exp (L / 2) := by
    rw [hxe, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
      ← Real.exp_add]
    congr 1; ring
  have hEx : F / x ≤ 40 * Real.exp (-(L / 2)) := by
    rw [div_le_iff₀ hx0]
    calc F ≤ 40 * Real.exp (L / 2) := by rw [← hsqx]; exact hF
      _ = 40 * Real.exp (-(L / 2)) * x := by
        rw [hxe, mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [hLs]
  exact o1_term2 hex2 hss hinvδ hlogs (div_nonneg hF0 hx0.le) hEx

end KR.RML6

end
