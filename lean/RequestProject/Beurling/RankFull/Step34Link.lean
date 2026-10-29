module

public import RequestProject.Beurling.RankFull.Step2Link
public import RequestProject.Beurling.RankFull.RankinRows
public import RequestProject.BSCert.CaplStep3

/-!
# Theorem 6.23(a), Steps 3 and 4: Dickman rows (`s > s_H + 1`, `ℓ ≤ 0.3Λ`) and (T2) (`ℓ ≥ 0.3Λ`)

In both ranges the rows outside the cover are only required to have degree `≥ 1` (`k = 0` in
`theorem_6_23a`; `hlow` is then trivial), `j = ⌊(X - 1)/(2a) - 1/2⌋` with
`a = a3 = log((L/(3ℓ) + 4)(2L/Λ + 1)) ≥ log(r₀(D+1))`, and:
* Step 3: `w = e^{-g}` with `g` the exponent of Lemma 6.22(d) (`dickman_sum_le`), and the
  criterion (80) follows from `BSCert.Capl.step3` (`(1 + j) g/L ≥ 1.001`) and `g ≥ (g/L)·L`;
* Step 4 (T2): `w = e^{-0.24L}` (`T2_weight`, from Lemma 6.22(e)), and `j ≥ 4`.

(The paper's (T1), `ℓ_std ≤ ℓ ≤ 0.3Λ`, is contained in Step 3: `BSCert.Capl.step3` holds for
all `s > s_H + 1` with `ℓ ≤ 0.3Λ`, since there `log c ≥ 7.5Λ`.)

Main results: `theorem_6_23a_step3`, `theorem_6_23a_T2`, and the weight bounds
`step3_hadm`, `T2_hadm` used to discharge `TypeUnionBound` in `CapLwAll.lean`.
-/

@[expose] public section

open Finset MeasureTheory BSCert.Capl
open scoped ENNReal

namespace RankFull

/-- `a3 = log(1/(3ℓ) + 4e^{-ℓ}) + ℓ + log(2e^ℓ/Λ + 1)` (Step 3 of Theorem 6.23). -/
noncomputable def a3 (Λ s : ℝ) : ℝ :=
  Real.log (1 / (3 * (2 * Real.log Λ + s)) + 4 * Real.exp (-(2 * Real.log Λ + s))) +
    (2 * Real.log Λ + s) + Real.log (2 * Real.exp (2 * Real.log Λ + s) / Λ + 1)

/-- `j = ⌊(X - 1)/(2a) - 1/2⌋`. -/
noncomputable def jA (X a : ℝ) : ℕ := (⌊(X - 1) / (2 * a) - 1 / 2⌋).toNat

lemma exp_a3 {Λ s : ℝ} (hΛ : 0 < Λ) (hl : 0 < 2 * Real.log Λ + s) :
    Real.exp (a3 Λ s) = (Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4) *
      (2 * Real.exp (2 * Real.log Λ + s) / Λ + 1) := by
  unfold a3
  set ℓ := 2 * Real.log Λ + s
  rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  rw [Real.exp_neg]
  have := Real.exp_pos ℓ
  field_simp

/-- Rows of degree `0` are the zero vector, so with `0 ∉ S` the input `hlow` holds for `k = 0`. -/
lemma hlow_zero {m : ℕ} {S : Finset (Fin m → ℕ)} (h0 : 0 ∉ S) {Q : ℝ} (hQ : 0 ≤ Q)
    (V : Submodule ℚ (Fin m → ℚ)) :
    (((Covers.inter S V).filter (fun y => Covers.deg y ≤ 0)).card : ℝ) ≤ Q := by
  classical
  have : (Covers.inter S V).filter (fun y => Covers.deg y ≤ 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro y hy hdeg
    have hyS : y ∈ S := by unfold Covers.inter at hy; exact (Finset.mem_filter.mp hy).1
    have : y = 0 := by
      funext i
      have h := Nat.le_zero.mp hdeg
      unfold Covers.deg at h
      exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
    exact h0 (this ▸ hyS)
  rw [this]; simpa using hQ

/-- `hc` from `r₀(D+1) ≤ e^a` and `(2j+1)a ≤ X - 1`. -/
lemma hc_le {X a : ℝ} {r₀ D j : ℕ} (hr : (r₀ : ℝ) * (D + 1) ≤ Real.exp a)
    (hj : (2 * j + 1 : ℝ) * a ≤ X - 1) :
    Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) ≤ Real.exp X := by
  have h1 : ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) ≤ Real.exp a ^ (2 * j + 1) :=
    pow_le_pow_left₀ (by positivity) hr _
  have h2 : Real.exp a ^ (2 * j + 1) ≤ Real.exp (X - 1) := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; linarith
  calc Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * j + 1) ≤ Real.exp 1 * Real.exp (X - 1) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos 1).le
    _ = Real.exp X := by rw [← Real.exp_add]; ring_nf

/-- The size facts common to Steps 3–4: for `s ≥ 6.9`, `L = e^ℓ ≥ Λ e^{6.9} Λ`,
`r₀ ≤ L/(3ℓ) + 4`, `D ≤ 2L/Λ`: `r₀(D+1) ≤ e^{a3}`, `r₀ ≤ L`, `r₀ D ≤ L²`, `60 ≤ L`, `900Λ ≤ L/Λ`. -/
lemma sizes34 {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : 6.9 ≤ s) {r₀ D : ℕ}
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) / (3 * (2 * Real.log Λ + s)) + 4)
    (hD : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log Λ + s) / Λ) :
    (r₀ : ℝ) * (D + 1) ≤ Real.exp (a3 Λ s) ∧ (r₀ : ℝ) ≤ Real.exp (2 * Real.log Λ + s) ∧
      ((r₀ * D : ℕ) : ℝ) ≤ Real.exp (2 * Real.log Λ + s) ^ 2 ∧
      60 ≤ Real.exp (2 * Real.log Λ + s) ∧ 900 * Λ ≤ Real.exp (2 * Real.log Λ + s) / Λ ∧
      43 ≤ 2 * Real.log Λ + s := by
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : 18.42 ≤ Real.log Λ :=
    le_trans log1e8_bounds.1 (Real.log_le_log (by norm_num) hΛ)
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hl : 43 ≤ ℓ := by linarith
  set L := Real.exp ℓ with hL
  have hLe : L = Λ ^ 2 * Real.exp s := exp_two_log_add hΛ0
  have hes : 900 ≤ Real.exp s := by
    have h1 : Real.exp 6.9 ≤ Real.exp s := Real.exp_le_exp.mpr hs
    have h2 : Real.exp 6.9 = Real.exp 1 ^ 6 * Real.exp 0.9 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h3 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 6
    have h4 := Real.sum_le_exp_of_nonneg (x := (0.9 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h4
    have h5 : 0 < Real.exp 1 ^ 6 := by positivity
    nlinarith
  have hLΛ : 900 * Λ ≤ L / Λ := by
    rw [le_div_iff₀ hΛ0, hLe]; nlinarith
  have hcube : ℓ ^ 3 / 6 ≤ L := by
    have h := Real.sum_le_exp_of_nonneg (x := ℓ) (by linarith) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have : 0 ≤ ℓ ^ 2 / 2 := by positivity
    rw [hL]; linarith
  have hL60 : 60 ≤ L := by nlinarith
  have hLl : 4 * ℓ ≤ L := by
    have h24 : (24 : ℝ) ≤ ℓ ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h24 (by linarith : (0 : ℝ) ≤ ℓ)
    nlinarith
  have hr₀L : (r₀ : ℝ) ≤ L := by
    have : L / (3 * ℓ) + 4 ≤ L := by
      rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hDL : (D : ℝ) ≤ L := by
    have : 2 * L / Λ ≤ L := by rw [div_le_iff₀ hΛ0]; nlinarith [Real.exp_pos ℓ]
    linarith
  refine ⟨?_, hr₀L, ?_, hL60, hLΛ, hl⟩
  · rw [exp_a3 hΛ0 (by linarith)]
    exact mul_le_mul hr₀ (by linarith) (by positivity) (by positivity)
  · push_cast
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    rw [sq]; exact mul_le_mul hr₀L hDL this (by linarith)

/-- `g ≥ (g/L) · L` (Step 3): `0.9(d-1) log d ≤ 0.9(D-1) log(D-1) + log Xm - log(3π) - e^{-0.4Λ}`
for `d = L/Λ ≤ D`, `d ≥ 2`, `log Xm ≥ Λ - 1`, `1 ≤ π ≤ e^{0.6Λ}`. -/
lemma g_ge_gL {Λ d D Xm : ℝ} {π : ℕ} (hΛ : 10 ^ 8 ≤ Λ) (hd : 2 ≤ d) (hdD : d ≤ D)
    (hXm : Λ - 1 ≤ Real.log Xm) (hπ1 : 1 ≤ π) (hπ : (π : ℝ) ≤ Real.exp (0.6 * Λ)) :
    0.9 * ((d - 1) * Real.log d) ≤ Real.log Xm - Real.log (3 * π) +
      0.9 * ((D - 1) * Real.log (D - 1)) - Real.exp (-0.4 * Λ) := by
  have h1 : (d - 1) * Real.log (d - 1) ≤ (D - 1) * Real.log (D - 1) :=
    xlogx_mono (by linarith) (by linarith)
  have h2 : (d - 1) * Real.log d - (d - 1) * Real.log (d - 1) ≤ 1 := by
    have hd1 : 0 < d - 1 := by linarith
    rw [← mul_sub, ← Real.log_div (by linarith) hd1.ne']
    have := Real.log_le_sub_one_of_pos (x := d / (d - 1)) (by positivity)
    have e : (d - 1) * (d / (d - 1) - 1) = 1 := by field_simp; ring
    nlinarith
  have hπ0 : (0 : ℝ) < π := by exact_mod_cast hπ1
  have h3 : Real.log (3 * π) ≤ 1.2 + 0.6 * Λ := by
    rw [Real.log_mul (by norm_num) hπ0.ne']
    have : Real.log π ≤ 0.6 * Λ := by
      rw [Real.log_le_iff_le_exp hπ0]; exact hπ
    have : Real.log 3 ≤ 1.2 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this
      have := Real.log_two_lt_d9; linarith
    linarith
  have h4 : Real.exp (-0.4 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

lemma log_le_div_1e6 {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 1000000 + 14 := by
  have h := Real.log_le_sub_one_of_pos (x := x / 1000000) (by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h14 : Real.log 1000000 ≤ 15 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.sum_le_exp_of_nonneg (x := (15 : ℝ)) (by norm_num) 30
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  linarith

lemma u1_bound {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    (max (10 ^ 4) (Real.log Λ) + 1) * Real.log (max (10 ^ 4) (Real.log Λ) + 1) ≤ 0.1 * Λ := by
  have hΛ0 : 0 < Λ := by linarith
  rcases le_total (Real.log Λ) (10 ^ 4) with h | h
  · rw [max_eq_left h]
    have hl : Real.log (10 ^ 4 + 1) ≤ 10 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have h2 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      have : (2.7182818283 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
      rw [h2]; nlinarith
    have : (10 ^ 4 + 1 : ℝ) * Real.log (10 ^ 4 + 1) ≤ (10 ^ 4 + 1) * 10 :=
      mul_le_mul_of_nonneg_left hl (by norm_num)
    norm_num at this hΛ ⊢; linarith
  · rw [max_eq_right h]
    set u := Real.log Λ with hu
    have hlu : Real.log (u + 1) ≤ u := by
      have := Real.log_le_sub_one_of_pos (x := u + 1) (by linarith); linarith
    have hΛe : Λ = Real.exp u := (Real.exp_log hΛ0).symm
    have hcube : u ^ 3 / 6 ≤ Real.exp u := by
      have h := Real.sum_le_exp_of_nonneg (x := u) (by linarith) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      have : 0 ≤ u ^ 2 / 2 := by positivity
      linarith
    have h1 : (u + 1) * Real.log (u + 1) ≤ (u + 1) * u :=
      mul_le_mul_of_nonneg_left hlu (by linarith)
    have h2 : (u + 1) * u ≤ 0.1 * (u ^ 3 / 6) := by
      have h3 : (u + 1) * u ≤ 2 * u ^ 2 := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h (sq_nonneg u)
      have h5 : u ^ 2 * u = u ^ 3 := by ring
      nlinarith
    linarith

/-- `X₀ ≥ 3` from `log X₀ ≥ 10⁸`. -/
lemma three_le_of_log {X₀ : ℕ} (hΛ : 10 ^ 8 ≤ Real.log X₀) : 3 ≤ X₀ := by
  by_contra h
  push_neg at h
  have : Real.log X₀ ≤ Real.log 3 := by
    rcases Nat.eq_zero_or_pos X₀ with h0 | h0
    · subst h0; simp; positivity
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h.le)
  have : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num); linarith
  linarith

set_option maxHeartbeats 2000000 in
/-- **The parameters of Step 3** (`s > s_H + 1`, `ℓ ≤ 0.3Λ`): `hc`, criterion (80) with
`w = e^{-g}` (`g` of Lemma 6.22(d)), `0 < w ≤ 1`, and the weight bound `#admDick ≤ z w`
(Lemma 6.22(a),(d)). -/
theorem step3_params {X₀ : ℕ} (hΛ : 10 ^ 8 ≤ Real.log X₀) {sH s Xm : ℝ} (hsH : 5.9745 ≤ sH)
    (hs : sH + 1 < s) (hl : 2 * Real.log (Real.log X₀) + s ≤ 0.3 * Real.log X₀) {r₀ D : ℕ}
    (hr0 : 1 ≤ r₀) (hD1 : 1 ≤ D)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * (2 * Real.log (Real.log X₀) + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s) / Real.log X₀)
    (hXm0 : 0 < Xm)
    (hXmlo : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log Xm)
    (hXmhi : Real.log Xm ≤ Real.log X₀) (τl : Fin (r₀ * D) → ℝ) (hτl : ∀ i, Xm ≤ τl i) :
    let Λ := Real.log X₀
    let L := Real.exp (2 * Real.log Λ + s)
    let z := Real.exp L
    let X := logc sH Λ s
    let g := Real.log Xm - Real.log (3 * (r₀ * D : ℕ)) +
      0.9 * ((Real.log (2 * z + 1) / Real.log Xm - 1) *
        Real.log (Real.log (2 * z + 1) / Real.log Xm - 1)) - Real.exp (-0.4 * Λ)
    60 ≤ L ∧ (r₀ : ℝ) ≤ L ∧
      Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * jA X (a3 Λ s) + 1) ≤ Real.exp X ∧
      L + 10 * Real.log L + 10 ≤ (1 + (jA X (a3 Λ s) : ℕ)) * Real.log (1 / Real.exp (-g)) ∧
      0 < Real.exp (-g) ∧ Real.exp (-g) ≤ 1 ∧
      ((admDick (r₀ * D) D X₀ τl (2 * z + 1)).card : ℝ) ≤ z * Real.exp (-g) := by
  intro Λ L z X g
  have hX₀ := three_le_of_log hΛ
  have hΛ0 : 0 < Λ := by show 0 < Real.log X₀; linarith
  have hΛ8 : (100000000 : ℝ) ≤ Λ := by
    show (100000000 : ℝ) ≤ Real.log X₀; norm_num at hΛ ⊢; linarith
  have hs69 : 6.9 ≤ s := by linarith
  obtain ⟨hsz1, hr0L, hπL, hL60, hLΛ, hl43⟩ := sizes34 hΛ8 hs69 hr₀ hDle
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hLdef : L = Real.exp ℓ := rfl
  have hLle : L ≤ Real.exp (0.3 * Λ) := Real.exp_le_exp.mpr hl
  have hLΛ' : Λ ≤ L := by
    have : 900 * Λ * Λ ≤ L := by rw [le_div_iff₀ hΛ0] at hLΛ; linarith
    nlinarith
  -- `a`, `j`
  set a := a3 Λ s with ha
  have hea := exp_a3 hΛ0 (by linarith : 0 < 2 * Real.log Λ + s)
  rw [← ha] at hea
  have ha0 : 0 < a := by
    have h1 : 1 < Real.exp a := by
      rw [hea]
      have h4 : 4 ≤ L / (3 * ℓ) + 4 := by
        have : 0 ≤ L / (3 * ℓ) := by positivity
        linarith
      have h5 : 1 ≤ 2 * L / Λ + 1 := by
        have : 0 ≤ 2 * L / Λ := by positivity
        linarith
      nlinarith
    exact (Real.one_lt_exp_iff.mp h1) -- 1 < exp a ↔ 0 < a
  have hst := step3 hsH hΛ8 hs hl
  set gL := 0.9 * (1 - Real.exp (-(ℓ - Real.log Λ))) * (ℓ - Real.log Λ) / Λ with hgL
  have hst' : 1.001 ≤ ((X - 1) / (2 * a) - 1 / 2) * gL := by
    have : step3Ratio X Λ s = ((X - 1) / (2 * a) - 0.5) * gL := rfl
    rw [this] at hst; norm_num at hst ⊢; linarith
  set d := L / Λ with hd
  have hd2 : 2 ≤ d := by nlinarith
  have hgLL : gL * L = 0.9 * ((d - 1) * Real.log d) := by
    have he : Real.exp (ℓ - Real.log Λ) = d := by
      rw [Real.exp_sub, Real.exp_log hΛ0]
    have hl' : ℓ - Real.log Λ = Real.log d := by rw [← he, Real.log_exp]
    rw [hgL, Real.exp_neg, he, hl']
    have : d * Λ = L := by rw [hd]; field_simp
    field_simp
    rw [← this]; ring
  have hgL0 : 0 < gL := by
    have : 0 < 0.9 * ((d - 1) * Real.log d) :=
      mul_pos (by norm_num) (mul_pos (by linarith) (Real.log_pos (by linarith)))
    rw [← hgLL] at this
    exact pos_of_mul_pos_left this (by linarith)
  set v := (X - 1) / (2 * a) - 1 / 2 with hv
  have hv0 : 0 < v := by
    by_contra h; push_neg at h
    have : v * gL ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hgL0.le
    linarith
  have hfl : 0 ≤ ⌊v⌋ := Int.floor_nonneg.mpr hv0.le
  have hj : ((jA X a : ℕ) : ℝ) = (⌊v⌋ : ℝ) := by
    unfold jA; rw [← hv]; exact_mod_cast Int.toNat_of_nonneg hfl
  have hjv : v ≤ 1 + (jA X a : ℕ) := by rw [hj]; linarith [Int.lt_floor_add_one v]
  have hjA : (2 * (jA X a : ℕ) + 1 : ℝ) * a ≤ X - 1 := by
    rw [hj]
    have := Int.floor_le v
    have e : (2 * v + 1) * a = X - 1 := by rw [hv]; field_simp; ring
    nlinarith
  have hc := hc_le hsz1 hjA
  -- `D` real, `g`
  set Dr := Real.log (2 * z + 1) / Real.log Xm with hDr
  have hz1 : 1 ≤ z := Real.one_le_exp (by linarith)
  have hlXm : Λ / 2 ≤ Real.log Xm := by
    have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    show Real.log X₀ / 2 ≤ Real.log Xm; linarith
  have hlXm0 : 0 < Real.log Xm := by linarith
  have hlogz : Real.log (2 * z + 1) ≥ L := by
    have : Real.log z ≤ Real.log (2 * z + 1) := Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_exp] at this
  have hlogz2 : Real.log (2 * z + 1) ≤ L + 1.2 := by
    have : Real.log (2 * z + 1) ≤ Real.log (3 * z) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at this
    have : Real.log 3 ≤ 1.2 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this
      have := Real.log_two_lt_d9; linarith
    linarith
  have hdD : d ≤ Dr := by
    rw [hd, hDr]
    calc L / Λ ≤ Real.log (2 * z + 1) / Λ := div_le_div_of_nonneg_right hlogz hΛ0.le
      _ ≤ Real.log (2 * z + 1) / Real.log Xm :=
          div_le_div_of_nonneg_left (by linarith) hlXm0 hXmhi
  have hDrL : Dr ≤ L := by
    rw [hDr, div_le_iff₀ hlXm0]; nlinarith
  have hXmlow : Real.exp (Λ - 1) ≤ Xm := by
    rw [← Real.exp_log hXm0]
    apply Real.exp_le_exp.mpr
    have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    show Real.log X₀ - 1 ≤ Real.log Xm; linarith
  have hπ1 : 1 ≤ r₀ * D := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hπ06 : ((r₀ * D : ℕ) : ℝ) ≤ Real.exp (0.6 * Λ) := by
    calc ((r₀ * D : ℕ) : ℝ) ≤ L ^ 2 := hπL
      _ ≤ Real.exp (0.3 * Λ) ^ 2 := pow_le_pow_left₀ (by linarith) hLle 2
      _ = Real.exp (0.6 * Λ) := by rw [← Real.exp_nat_mul]; ring_nf
  have hgge := g_ge_gL (π := r₀ * D) hΛ hd2 hdD (by
    have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    show Real.log X₀ - 1 ≤ Real.log Xm; linarith) hπ1 hπ06
  have hg : gL * L ≤ g := by rw [hgLL]; exact hgge
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  -- (80)
  have hlogL : 10 * Real.log L + 10 ≤ 0.001 * L := by
    have := log_le_div_1e6 (x := L) (by linarith)
    have : (10 : ℝ) ^ 8 ≤ L := by norm_num; linarith
    linarith
  have h80 : L + 10 * Real.log L + 10 ≤ (1 + (jA X a : ℕ)) * Real.log (1 / Real.exp (-g)) := by
    have hw : Real.log (1 / Real.exp (-g)) = g := by
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    rw [hw]
    have h1 : 1.001 * L ≤ v * gL * L := by nlinarith
    have h2 : v * gL * L ≤ (1 + (jA X a : ℕ)) * g := by
      have := mul_le_mul hjv hg (by positivity) (by positivity)
      linarith [mul_assoc v gL L]
    linarith
  -- the weight bound (Lemma 6.22(a),(d))
  have hcard := card_admDick_le (K := D) (X₀ := X₀) hXm0 (by positivity : (0 : ℝ) ≤ 2 * z + 1) hτl
  have hz0 : 0 < z := Real.exp_pos L
  have hzX : (X₀ : ℝ) ≤ z := by
      have : Real.exp Λ ≤ z := Real.exp_le_exp.mpr hLΛ'
      rwa [show Λ = Real.log X₀ from rfl, Real.exp_log (by exact_mod_cast (by omega : 0 < X₀))]
        at this
  have hDd1 : 2 * max (10 ^ 4) (Real.log (Real.log X₀)) ≤ Dr - 1 := by
      have hlog : Real.log Λ ≤ Λ := by have := Real.log_le_sub_one_of_pos hΛ0; linarith
      have : max (10 ^ 4 : ℝ) (Real.log Λ) ≤ 10 ^ 4 + Λ := max_le (by linarith) (by linarith)
      have : 900 * Λ ≤ Dr := le_trans (by linarith) hdD
      show 2 * max (10 ^ 4) (Real.log Λ) ≤ Dr - 1
      linarith
  have hDd2 : Dr ≤ Real.exp (0.3 * Real.log X₀) := by
    show Dr ≤ Real.exp (0.3 * Λ); linarith
  have hπDd : ((r₀ * D : ℕ) : ℝ) * Xm⁻¹ * (Real.exp 1 * Dr) ^ (0.9 : ℝ) ≤ 1 / 3 := by
      have hD1' : 1 ≤ Real.exp 1 * Dr := by
        have := Real.add_one_le_exp (1 : ℝ); nlinarith
      have h09 : (Real.exp 1 * Dr) ^ (0.9 : ℝ) ≤ Real.exp 1 * Dr := by
        calc (Real.exp 1 * Dr) ^ (0.9 : ℝ) ≤ (Real.exp 1 * Dr) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hD1' (by norm_num)
          _ = _ := Real.rpow_one _
      have hL3 : L ^ 3 ≤ Real.exp (0.9 * Λ) := by
        calc L ^ 3 ≤ Real.exp (0.3 * Λ) ^ 3 := pow_le_pow_left₀ (by linarith) hLle 3
          _ = Real.exp (0.9 * Λ) := by rw [← Real.exp_nat_mul]; ring_nf
      have hfin : Real.exp 1 * Real.exp (0.9 * Λ) ≤ Real.exp (Λ - 1) / 3 := by
        rw [le_div_iff₀ (by norm_num), ← Real.exp_add]
        have : Real.exp (1 + 0.9 * Λ) * 3 ≤ Real.exp (1 + 0.9 * Λ) * Real.exp 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 : ℝ); linarith
        rw [← Real.exp_add] at this
        calc Real.exp (1 + 0.9 * Λ) * 3 ≤ Real.exp (1 + 0.9 * Λ + 2) := this
          _ ≤ Real.exp (Λ - 1) := Real.exp_le_exp.mpr (by linarith)
      calc ((r₀ * D : ℕ) : ℝ) * Xm⁻¹ * (Real.exp 1 * Dr) ^ (0.9 : ℝ)
          ≤ L ^ 2 * Xm⁻¹ * (Real.exp 1 * L) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hπL (inv_nonneg.mpr hXm0.le))
              (h09.trans (mul_le_mul_of_nonneg_left hDrL (Real.exp_pos 1).le)) (by positivity)
              (by positivity)
        _ = Real.exp 1 * L ^ 3 / Xm := by field_simp
        _ ≤ Real.exp 1 * Real.exp (0.9 * Λ) / Real.exp (Λ - 1) := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hL3 (Real.exp_pos 1).le)
              (Real.exp_pos _) hXmlow
        _ ≤ 1 / 3 := by
            rw [div_le_iff₀ (Real.exp_pos _)]; linarith
  have hπud : ((r₀ * D : ℕ) : ℝ) * Real.exp (0.9 * ((max (10 ^ 4) (Real.log (Real.log X₀)) + 1) *
        Real.log (max (10 ^ 4) (Real.log (Real.log X₀)) + 1))) ≤ Xm / 3 := by
      have hu := u1_bound hΛ
      have h1 : Real.exp (0.9 * ((max (10 ^ 4) (Real.log (Real.log X₀)) + 1) *
          Real.log (max (10 ^ 4) (Real.log (Real.log X₀)) + 1))) ≤
            Real.exp (0.09 * Real.log X₀) :=
        Real.exp_le_exp.mpr (by linarith [hu])
      have h2 : Real.exp (0.6 * Λ) * Real.exp (0.09 * Λ) ≤ Real.exp (Λ - 1) / 3 := by
        rw [← Real.exp_add, le_div_iff₀ (by norm_num)]
        have : Real.exp (0.6 * Λ + 0.09 * Λ) * 3 ≤ Real.exp (0.6 * Λ + 0.09 * Λ) * Real.exp 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 : ℝ); linarith
        rw [← Real.exp_add] at this
        calc Real.exp (0.6 * Λ + 0.09 * Λ) * 3 ≤ Real.exp (0.6 * Λ + 0.09 * Λ + 2) := this
          _ ≤ Real.exp (Λ - 1) := Real.exp_le_exp.mpr (by linarith)
      show ((r₀ * D : ℕ) : ℝ) * Real.exp (0.9 * ((max (10 ^ 4) (Real.log (Real.log X₀)) + 1) *
        Real.log (max (10 ^ 4) (Real.log (Real.log X₀)) + 1))) ≤ Xm / 3
      calc ((r₀ * D : ℕ) : ℝ) * Real.exp (0.9 * ((max (10 ^ 4) (Real.log (Real.log X₀)) + 1) *
            Real.log (max (10 ^ 4) (Real.log (Real.log X₀)) + 1)))
          ≤ Real.exp (0.6 * Λ) * Real.exp (0.09 * Λ) :=
            mul_le_mul hπ06 h1 (Real.exp_pos _).le (Real.exp_pos _).le
        _ ≤ Real.exp (Λ - 1) / 3 := h2
        _ ≤ Xm / 3 := by linarith
  have hdk := dickman_sum_le (K := D) hX₀ hΛ hXm0 hXmlo hXmhi hzX hπ1 hDd1 hDd2 hπDd hπud
  have hsum : ∑ k ∈ Icc 1 D, ((r₀ * D + k - 1).choose k : ℝ) *
      Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) ≤ z * Real.exp (-g) := by
    rw [← inv_mul_le_iff₀ hz0]; exact hdk
  refine ⟨hL60, hr0L, hc, h80, Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_⟩
  exact hcard.trans hsum

set_option maxHeartbeats 2000000 in
/-- **The parameters of Step 4 (T2)** (`ℓ ≥ 0.3Λ`): `hc`, `j ≥ 4` and criterion (80) with
`w = e^{-0.24L}`, `0 < w ≤ 1`, and the weight bound `#admGen ≤ z w` (Lemma 6.22(e),
`T2_weight`). -/
theorem T2_params {X₀ : ℕ} (hΛ : 10 ^ 8 ≤ Real.log X₀) {sH s : ℝ}
    (hl : 0.3 * Real.log X₀ ≤ 2 * Real.log (Real.log X₀) + s) {r₀ D : ℕ}
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * (2 * Real.log (Real.log X₀) + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s) / Real.log X₀)
    (τl : Fin (r₀ * D) → ℝ) (hτ3 : ∀ i, 3 ≤ τl i)
    (hτi : ∀ i : Fin (r₀ * D), (((i : ℕ) : ℝ) + 1) / 2 ≤ τl i) :
    let Λ := Real.log X₀
    let L := Real.exp (2 * Real.log Λ + s)
    let z := Real.exp L
    let X := logc sH Λ s
    60 ≤ L ∧ (r₀ : ℝ) ≤ L ∧
      Real.exp 1 * ((r₀ : ℝ) * (D + 1)) ^ (2 * jA X (a3 Λ s) + 1) ≤ Real.exp X ∧
      L + 10 * Real.log L + 10 ≤
        (1 + (jA X (a3 Λ s) : ℕ)) * Real.log (1 / Real.exp (-0.24 * L)) ∧
      0 < Real.exp (-0.24 * L) ∧ Real.exp (-0.24 * L) ≤ 1 ∧
      ((admGen (r₀ * D) 1 D X₀ τl (2 * z + 1)).card : ℝ) ≤ z * Real.exp (-0.24 * L) := by
  intro Λ L z X
  have hX₀ := three_le_of_log hΛ
  have hΛ0 : 0 < Λ := by show 0 < Real.log X₀; linarith
  have hΛ8 : (100000000 : ℝ) ≤ Λ := by
    show (100000000 : ℝ) ≤ Real.log X₀; norm_num at hΛ ⊢; linarith
  have hlogΛ : Real.log Λ ≤ Λ / 1000 + 999 := by
    have := Real.log_le_sub_one_of_pos (x := Λ / 1000) (by positivity)
    rw [Real.log_div hΛ0.ne' (by norm_num)] at this
    have h1000 := Real.log_le_sub_one_of_pos (x := 1000) (by norm_num)
    linarith
  have hs69 : 6.9 ≤ s := by
    have : 0.3 * Λ ≤ 2 * Real.log Λ + s := hl
    linarith
  obtain ⟨hsz1, hr0L, hπL, hL60, hLΛ, hl43⟩ := sizes34 hΛ8 hs69 hr₀ hDle
  set ℓ := 2 * Real.log Λ + s with hℓ
  have hl3 : 0.3 * Λ ≤ ℓ := hl
  have hℓbig : 30000000 ≤ ℓ := by linarith
  have hLdef : L = Real.exp ℓ := rfl
  have hLsq : ℓ ^ 2 / 2 ≤ L := by
    have h := Real.sum_le_exp_of_nonneg (x := ℓ) (by linarith) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [hLdef]; nlinarith
  -- `a ≤ log 3 + 2ℓ`, `j ≥ 4`
  set a := a3 Λ s with ha
  have hea := exp_a3 hΛ0 (by linarith : 0 < 2 * Real.log Λ + s)
  rw [← ha] at hea
  have hL1 : 1 ≤ L / Λ := by
    rw [le_div_iff₀ hΛ0]; nlinarith
  have ha0 : 0 < a := by
    have h1 : 1 < Real.exp a := by
      rw [hea]
      have h4 : 4 ≤ L / (3 * ℓ) + 4 := by
        have : 0 ≤ L / (3 * ℓ) := by positivity
        linarith
      have h5 : 1 ≤ 2 * L / Λ + 1 := by
        have : 0 ≤ 2 * L / Λ := by positivity
        linarith
      nlinarith
    exact Real.one_lt_exp_iff.mp h1
  have hau : a ≤ 1.2 + 2 * ℓ := by
    have h1 : Real.exp a ≤ 3 * L ^ 2 := by
      rw [hea]
      have h4 : L / (3 * ℓ) + 4 ≤ L := by
        rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]; nlinarith
      have h5 : 2 * L / Λ + 1 ≤ 3 * L := by
        have : 2 * L / Λ ≤ 2 * L := by
          rw [div_le_iff₀ hΛ0]; nlinarith [Real.exp_pos ℓ]
        linarith
      calc (L / (3 * ℓ) + 4) * (2 * L / Λ + 1) ≤ L * (3 * L) :=
            mul_le_mul h4 h5 (by positivity) (by linarith)
        _ = 3 * L ^ 2 := by ring
    have h2 : a ≤ Real.log (3 * L ^ 2) := by
      rw [← Real.log_exp a]; exact Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hLdef, Real.log_exp] at h2
    have : Real.log 3 ≤ 1.2 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at this
      have := Real.log_two_lt_d9; linarith
    push_cast at h2; linarith
  have hXl : 4 * ℓ ^ 2 - Real.log 4 ≤ X := le_max_left _ _
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; norm_num at this; linarith
  set v := (X - 1) / (2 * a) - 1 / 2 with hv
  have hv5 : 5 ≤ v := by
    rw [hv]
    have : 11 * a ≤ X - 1 := by nlinarith
    have : 5.5 ≤ (X - 1) / (2 * a) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hfl : 0 ≤ ⌊v⌋ := Int.floor_nonneg.mpr (by linarith)
  have hj : ((jA X a : ℕ) : ℝ) = (⌊v⌋ : ℝ) := by
    unfold jA; rw [← hv]; exact_mod_cast Int.toNat_of_nonneg hfl
  have hj4 : (5 : ℝ) ≤ 1 + (jA X a : ℕ) := by rw [hj]; linarith [Int.lt_floor_add_one v]
  have hjA : (2 * (jA X a : ℕ) + 1 : ℝ) * a ≤ X - 1 := by
    rw [hj]
    have := Int.floor_le v
    have e : (2 * v + 1) * a = X - 1 := by rw [hv]; field_simp; ring
    nlinarith
  have hc := hc_le hsz1 hjA
  -- (80)
  have hw : Real.log (1 / Real.exp (-0.24 * L)) = 0.24 * L := by
    rw [one_div, ← Real.exp_neg, Real.log_exp]; ring
  have h80 : L + 10 * Real.log L + 10 ≤
      (1 + (jA X a : ℕ)) * Real.log (1 / Real.exp (-0.24 * L)) := by
    rw [hw, hLdef, Real.log_exp]
    have h1 : 10 * ℓ + 10 ≤ 0.2 * Real.exp ℓ := by nlinarith
    have h2 : 5 * (0.24 * Real.exp ℓ) ≤ (1 + (jA X a : ℕ)) * (0.24 * Real.exp ℓ) :=
      mul_le_mul_of_nonneg_right hj4 (by positivity)
    linarith
  have hLle : Real.exp (0.3 * Real.log X₀) ≤ L := Real.exp_le_exp.mpr hl
  have hadm := T2_weight (k₁ := 1) (K := D) hX₀ hΛ hLle hπL hτ3 hτi
  refine ⟨hL60, hr0L, hc, h80, Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), hadm⟩

end RankFull
