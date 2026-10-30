module

public import RequestProject.BSCert.Consts.IntCells
public import RequestProject.BSCert.Consts.ZetaCert
public import RequestProject.BSCert.EiCert
meta import RequestProject.BSCert.Consts.IntCells
meta import RequestProject.BSCert.Consts.ZetaCert
meta import RequestProject.BSCert.EiCert

/-!
# `margins.py` (m1–m6): definitions, cell bounds and their soundness

The chain bounds themselves are checked by the kernel in `MarginSegs/*.lean`; the statements
are in `MarginCert`.
-/

@[expose] public section

namespace BSCert.Consts

open Real MeasureTheory Set BSCert BSCert.EiFn

/-! ## Definitions -/

/-- `I₁ = ∫₁⁴ v (log v + 1.01) dv`. -/
noncomputable def I1 : ℝ := ∫ v in (1 : ℝ)..4, v * (Real.log v + 1.01)

/-- The integrand of `I₂`: `U³ (log U + 1.01)/v²`, `U = 1 + 2 log v`. -/
noncomputable def f2 (v : ℝ) : ℝ := Uf v ^ 3 * (Real.log (Uf v) + 1.01) / v ^ 2

/-- `I₂ = ∫₄^∞ U³ (log U + 1.01) v⁻² dv`. -/
noncomputable def I2 : ℝ := ∫ v in Ioi (4 : ℝ), f2 v

/-- The integrand of `I₃` without its constant: `1/(U v²)`. -/
noncomputable def f3 (v : ℝ) : ℝ := 1 / (Uf v * v ^ 2)

/-- `c₃ = 2 e^γ e^{Ein(2)}`. -/
noncomputable def c3 : ℝ := 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2)

/-- `I₃ = c₃ ∫₄^∞ dv/(U v²)`. -/
noncomputable def I3 : ℝ := c3 * ∫ v in Ioi (4 : ℝ), f3 v

/-! ## m1: `Ein(2)` -/

lemma Ein2_check : EinHiQ 30 2 < 369 / 100 ∧ 36838 / 10000 < EinLoQ 30 2 := by decide +kernel

/-- **m1.** `3.6838 < Ein(2) < 3.69`. -/
theorem Ein_two_bounds : 3.6838 < Ein 2 ∧ Ein 2 < 3.69 := by
  have hhi : Ein 2 ≤ ((EinHiQ 30 2 : ℚ) : ℝ) := by
    rw [EinHiQ_cast]; push_cast; exact Ein_le_EinHi (by norm_num) (by norm_num)
  have hlo : ((EinLoQ 30 2 : ℚ) : ℝ) ≤ Ein 2 := by
    rw [EinLoQ_cast]; push_cast; exact EinLo_le_Ein (by norm_num) 30
  obtain ⟨h1, h2⟩ := Ein2_check
  have h1' := (Rat.cast_lt (K := ℝ)).mpr h1
  have h2' := (Rat.cast_lt (K := ℝ)).mpr h2
  push_cast at h1' h2'
  constructor <;> norm_num <;> linarith

/-! ## m2: `I₁` -/

/-- **m2.** `I₁ = 16 log 2 + 3.825`. -/
theorem I1_eq : I1 = 16 * Real.log 2 + 3.825 := by
  have hd : ∀ x ∈ uIcc (1 : ℝ) 4, HasDerivAt
      (fun v : ℝ => v ^ 2 * Real.log v / 2 - v ^ 2 / 4 + 1.01 * v ^ 2 / 2)
      (x * (Real.log x + 1.01)) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := ((((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_log hx0)).div_const 2).sub
      ((hasDerivAt_pow 2 x).div_const 4)).add (((hasDerivAt_pow 2 x).const_mul 1.01).div_const 2)
    convert! h using 1
    field_simp
    ring
  unfold I1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    simp only [Real.log_one, h4]
    ring
  · apply ContinuousOn.intervalIntegrable
    have : ContinuousOn Real.log (uIcc (1 : ℝ) 4) := Real.continuousOn_log.mono (by
      intro x hx; rw [uIcc_of_le (by norm_num)] at hx; simp; linarith [hx.1])
    fun_prop

/-- **m2.** `I₁ ≤ 14.92` (value `14.9154`). -/
theorem I1_le : I1 ≤ 14.92 := by
  rw [I1_eq]; have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-! ## Pointwise bounds -/

lemma Uf_pos {v : ℝ} (hv : 1 ≤ v) : 0 < Uf v := by
  unfold Uf; have := Real.log_nonneg hv; linarith

lemma Uf_mono {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) : Uf v ≤ Uf w := by
  unfold Uf; have := Real.log_le_log hv hvw; linarith

lemma f2_le {v : ℝ} (hv : 1 ≤ v) {c lam : ℚ} (hc : 0 < c)
    (hlam : Real.log c + 1 / 100 ≤ lam) :
    f2 v ≤ polyU ⟨0, 0, 0, lam, 1 / c⟩ (Uf v) / v ^ 2 := by
  have hU := Uf_pos hv
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  -- tangent bound for `log`
  have ht : Real.log (Uf v) ≤ Real.log c + Uf v / c - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hU hc')
    rw [Real.log_div hU.ne' hc'.ne'] at this
    linarith
  unfold f2 polyU
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast
  have hU3 : 0 ≤ Uf v ^ 3 := by positivity
  have : Uf v ^ 3 * (Real.log (Uf v) + 1.01) ≤ Uf v ^ 3 * (lam + Uf v / c) :=
    mul_le_mul_of_nonneg_left (by linarith) hU3
  calc Uf v ^ 3 * (Real.log (Uf v) + 1.01) ≤ Uf v ^ 3 * (lam + Uf v / c) := this
    _ = 0 + 0 * Uf v + 0 * Uf v ^ 2 + lam * Uf v ^ 3 + 1 / c * Uf v ^ 4 := by
      field_simp; ring

lemma f3_le {v : ℝ} (hv : 1 ≤ v) {c : ℚ} (hc : 0 < c) (hcU : (c : ℝ) ≤ Uf v) :
    f3 v ≤ polyU ⟨3 / c, -3 / c ^ 2, 1 / c ^ 3, 0, 0⟩ (Uf v) / v ^ 2 := by
  have hU := Uf_pos hv
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : f3 v = (1 / Uf v) / v ^ 2 := by unfold f3; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold polyU
  push_cast
  rw [one_div, inv_le_iff_one_le_mul₀ hU]
  have h3 : 0 ≤ (Uf v - c) ^ 3 := pow_nonneg (by linarith) 3
  have e : (3 / (c : ℝ) + -3 / (c : ℝ) ^ 2 * Uf v + 1 / (c : ℝ) ^ 3 * Uf v ^ 2 + 0 * Uf v ^ 3
      + 0 * Uf v ^ 4) * Uf v = 1 + (Uf v - c) ^ 3 / (c : ℝ) ^ 3 := by
    field_simp; ring
  rw [e]
  have : 0 ≤ (Uf v - c) ^ 3 / (c : ℝ) ^ 3 := by positivity
  linarith

lemma f3_le_tail {v : ℝ} (hv : 1 ≤ v) {c : ℚ} (hc : 0 < c) (hcU : (c : ℝ) ≤ Uf v) :
    f3 v ≤ polyU ⟨1 / c, 0, 0, 0, 0⟩ (Uf v) / v ^ 2 := by
  have hU := Uf_pos hv
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : f3 v = (1 / Uf v) / v ^ 2 := by unfold f3; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold polyU
  push_cast
  simp only [zero_mul, add_zero]
  rw [one_div, one_div]
  exact inv_anti₀ hc' hcU

lemma f2_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ f2 v := by
  have hU := Uf_pos hv
  have : 0 ≤ Real.log (Uf v) := by
    apply Real.log_nonneg; unfold Uf; have := Real.log_nonneg hv; linarith
  unfold f2; positivity

lemma f3_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ f3 v := by
  have hU := Uf_pos hv
  unfold f3; positivity

lemma continuousOn_Uf {s : Set ℝ} (hs : ∀ v ∈ s, 0 < v) : ContinuousOn Uf s := by
  have : ContinuousOn Real.log s := Real.continuousOn_log.mono (fun v hv => (hs v hv).ne')
  unfold Uf; fun_prop

lemma continuousOn_f2 : ContinuousOn f2 (Ici 1) := by
  have hpos : ∀ v ∈ Ici (1 : ℝ), 0 < v := fun v hv => lt_of_lt_of_le one_pos hv
  have hU := continuousOn_Uf hpos
  have hlU : ContinuousOn (fun v => Real.log (Uf v)) (Ici 1) :=
    hU.log (fun v hv => (Uf_pos hv).ne')
  unfold f2
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro v hv; exact pow_ne_zero 2 (hpos v hv).ne'

lemma continuousOn_f3 : ContinuousOn f3 (Ici 1) := by
  have hpos : ∀ v ∈ Ici (1 : ℝ), 0 < v := fun v hv => lt_of_lt_of_le one_pos hv
  have hU := continuousOn_Uf hpos
  unfold f3
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro v hv; exact mul_ne_zero (Uf_pos hv).ne' (pow_ne_zero 2 (hpos v hv).ne')

lemma numU_nonneg {c : Co} (h0 : 0 ≤ c.a0) (h1 : 0 ≤ c.a1) (h2 : 0 ≤ c.a2) (h3 : 0 ≤ c.a3)
    (h4 : 0 ≤ c.a4) {U : ℝ} (hU : 0 ≤ U) : 0 ≤ numU c U := by
  have h0' : (0 : ℝ) ≤ c.a0 := by exact_mod_cast h0
  have h1' : (0 : ℝ) ≤ c.a1 := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ c.a2 := by exact_mod_cast h2
  have h3' : (0 : ℝ) ≤ c.a3 := by exact_mod_cast h3
  have h4' : (0 : ℝ) ≤ c.a4 := by exact_mod_cast h4
  unfold numU; positivity

/-! ## The cells -/

/-- The cell points `4, 5, …`, `q = p + max(1, ⌊p/8⌋)`, until `10¹³`. -/
def ptsUntil : ℕ → ℕ → List ℕ
  | 0, p => [p]
  | n + 1, p => if 10 ^ 13 ≤ p then [p] else p :: ptsUntil n (p + max 1 (p / 8))

/-- The points used for `I₂` and `I₃`. -/
def pts : List ℕ := ptsUntil 400 4

/-- The last point. -/
def ptN : ℕ := pts.getLastD 0

lemma pts_eq : pts = 4 :: pts.tail := by
  unfold pts; rw [ptsUntil]; simp

lemma ptN_eq : (4 :: pts.tail).getLast (by simp) = ptN := by
  rw [List.getLast_eq_getLastD]
  unfold ptN
  conv_rhs => rw [pts_eq]
  simp only [List.getLastD_eq_getLast?]
  rw [List.getLast?_cons]; simp

/-- Cell bound for `I₂` (tangent at `c ≈ U` in the middle of the cell). -/
def cb2 (p q : ℕ) : Option ℚ :=
  let c : ℚ := (UItv p).lo / 2 + (UItv q).lo / 2
  let lam : ℚ := FX.logHiQF c + 1 / 100
  if 1 ≤ p ∧ p ≤ q ∧ 0 < c then some (phiDiffHi ⟨0, 0, 0, lam, 1 / c⟩ p q) else none

/-- Cell bound for `∫ dv/(U v²)` (`c = ` lower end of `U_p`). -/
def cb3 (p q : ℕ) : Option ℚ :=
  let c : ℚ := (UItv p).lo
  if 1 ≤ p ∧ p ≤ q ∧ 0 < c then some (phiDiffHi ⟨3 / c, -3 / c ^ 2, 1 / c ^ 3, 0, 0⟩ p q)
  else none

/-- Tail bound for `I₂` beyond `p`. -/
def tail2 (p : ℕ) : Option ℚ :=
  let c : ℚ := (UItv p).lo
  let lam : ℚ := FX.logHiQF c + 1 / 100
  if 1 ≤ p ∧ 0 < c ∧ 0 ≤ lam then some (phiTailHi ⟨0, 0, 0, lam, 1 / c⟩ p) else none

/-- Tail bound for `∫ dv/(U v²)` beyond `p`. -/
def tail3 (p : ℕ) : Option ℚ :=
  let c : ℚ := (UItv p).lo
  if 1 ≤ p ∧ 0 < c then some (phiTailHi ⟨1 / c, 0, 0, 0, 0⟩ p) else none

lemma lam_ok {c : ℚ} (hc : 0 < c) : Real.log c + 1 / 100 ≤ ((FX.logHiQF c + 1 / 100 : ℚ) : ℝ) := by
  have := FX.le_logHiQF hc; push_cast; linarith

lemma cb2_sound : ∀ p q u, cb2 p q = some u → p ≤ q ∧ ∫ v in (p : ℝ)..q, f2 v ≤ u := by
  intro p q u h
  unfold cb2 at h
  simp only at h
  split_ifs at h with hc
  cases h
  obtain ⟨hp, hpq, hc0⟩ := hc
  refine ⟨hpq, ?_⟩
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  refine le_trans (cell_le (by linarith) hpq' (continuousOn_f2.mono (fun v hv => le_trans hp' hv.1))
    (fun v hv => f2_le (le_trans hp' hv.1) hc0 (lam_ok hc0))) ?_
  exact Phi_sub_le (by omega) (by omega)

lemma cb3_sound : ∀ p q u, cb3 p q = some u → p ≤ q ∧ ∫ v in (p : ℝ)..q, f3 v ≤ u := by
  intro p q u h
  unfold cb3 at h
  simp only at h
  split_ifs at h with hc
  cases h
  obtain ⟨hp, hpq, hc0⟩ := hc
  refine ⟨hpq, ?_⟩
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hcU : ∀ v : ℝ, (p : ℝ) ≤ v → (((UItv p).lo : ℚ) : ℝ) ≤ Uf v := fun v hv =>
    le_trans (mem_UItv (by omega)).1 (Uf_mono (by linarith) hv)
  refine le_trans (cell_le (by linarith) hpq' (continuousOn_f3.mono (fun v hv => le_trans hp' hv.1))
    (fun v hv => f3_le (le_trans hp' hv.1) hc0 (hcU v hv.1))) ?_
  exact Phi_sub_le (by omega) (by omega)

lemma tail2_sound {p : ℕ} {u : ℚ} (h : tail2 p = some u) {M : ℝ} (hM : (p : ℝ) ≤ M) :
    ∫ v in (p : ℝ)..M, f2 v ≤ u := by
  unfold tail2 at h
  simp only at h
  split_ifs at h with hc
  cases h
  obtain ⟨hp, hc0, hlam⟩ := hc
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  refine le_trans (tail_cell_le (by linarith) (continuousOn_f2.mono (fun v hv => le_trans hp' hv))
    (fun v hv => f2_le (le_trans hp' hv) hc0 (lam_ok hc0)) (fun v hv => ?_) hM)
    (neg_Phi_le (by omega))
  exact numU_nonneg le_rfl le_rfl le_rfl hlam (by positivity) (Uf_pos (le_trans hp' hv)).le

lemma tail3_sound {p : ℕ} {u : ℚ} (h : tail3 p = some u) {M : ℝ} (hM : (p : ℝ) ≤ M) :
    ∫ v in (p : ℝ)..M, f3 v ≤ u := by
  unfold tail3 at h
  simp only at h
  split_ifs at h with hc
  cases h
  obtain ⟨hp, hc0⟩ := hc
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcU : ∀ v : ℝ, (p : ℝ) ≤ v → (((UItv p).lo : ℚ) : ℝ) ≤ Uf v := fun v hv =>
    le_trans (mem_UItv (by omega)).1 (Uf_mono (by linarith) hv)
  refine le_trans (tail_cell_le (by linarith) (continuousOn_f3.mono (fun v hv => le_trans hp' hv))
    (fun v hv => f3_le_tail (le_trans hp' hv) hc0 (hcU v hv)) (fun v hv => ?_) hM)
    (neg_Phi_le (by omega))
  exact numU_nonneg (by positivity) le_rfl le_rfl le_rfl le_rfl (Uf_pos (le_trans hp' hv)).le

/-- Total bound: chain of cells plus tail. -/
def totalBound (cb : ℕ → ℕ → Option ℚ) (tl : ℕ → Option ℚ) : Option ℚ :=
  (chainBound cb pts).bind fun u => (tl ptN).map fun t => u + t

lemma totalBound_sound {f : ℝ → ℝ} {cb : ℕ → ℕ → Option ℚ} {tl : ℕ → Option ℚ}
    (hf : ContinuousOn f (Ici 1)) (hnn : ∀ v, 1 ≤ v → 0 ≤ f v)
    (hcb : ∀ p q u, cb p q = some u → p ≤ q ∧ ∫ v in (p : ℝ)..q, f v ≤ u)
    (htl : ∀ u, tl ptN = some u → ∀ M : ℝ, (ptN : ℝ) ≤ M → ∫ v in (ptN : ℝ)..M, f v ≤ u)
    {B : ℚ} (h : totalBound cb tl = some B) :
    IntegrableOn f (Ioi 4) ∧ ∫ v in Ioi (4 : ℝ), f v ≤ B := by
  unfold totalBound at h
  obtain ⟨u, hu, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hint : ∀ p q : ℕ, p ≤ q → 0 < p → IntervalIntegrable f volume p q := by
    intro p q hpq hp
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by exact_mod_cast hpq)]
    exact hf.mono (fun v hv => le_trans hp' hv.1)
  rw [pts_eq] at hu
  obtain ⟨hle, hchain⟩ := chainBound_sound hcb hint pts.tail 4 u (by norm_num) hu
  rw [ptN_eq] at hle hchain
  have hle' : (4 : ℝ) ≤ ptN := by exact_mod_cast hle
  apply integral_Ioi_le hle' (fun x hx => hnn x (by linarith))
    (hf.mono (fun x hx => by simp at hx ⊢; linarith))
  intro M hM
  have hi1 : IntervalIntegrable f volume 4 ptN := by
    have := hint 4 ptN hle (by norm_num); exact_mod_cast this
  have hi2 : IntervalIntegrable f volume ptN M := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hM]
    exact hf.mono (fun v hv => by simp; linarith [hv.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have := htl t ht M hM
  push_cast at hchain ⊢
  linarith

/-! ## m3: `I₂` -/

end BSCert.Consts
