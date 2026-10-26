module

public import RequestProject.BSCert.Consts.ZetaItv
meta import RequestProject.BSCert.Consts.ZetaItv

/-!
# `consts.py`, lines k1–k5 and x1, x5–x7 (Appendix B.4)

The constants of the ordered-factorisation sums (Section 5.5.2) and of Proposition 5.31,
for `N = ℕ`. Here `A(s) := 1/(2 - ζ(s)) - 1`, which is `∑_{m ≥ 2} H_ord(m) m^{-s}` (see
`OrdFact.lean`), and `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))²`.

`ζ` is Mathlib's `riemannZeta`; on `(1, ∞)` it equals the real series `zetaR`
(`riemannZeta_eq_zetaR`), and `-ζ'` equals `zetaDR` (`deriv_riemannZeta_eq`).
-/

@[expose] public section

namespace BSCert.Consts

open Real

/-- The paper's `A(s) = 1/(2 - ζ(s)) - 1` (real `s > 1`). -/
noncomputable def ordA (s : ℝ) : ℝ := 1 / (2 - zetaR s) - 1

/-- The paper's `A₁(ε) = -ζ'(2-ε)/(2 - ζ(2-ε))²`, written at `s = 2 - ε`. -/
noncomputable def ordA1 (s : ℝ) : ℝ := zetaDR s / (2 - zetaR s) ^ 2

/-! ## Checking `Option`-valued bounds -/

/-- `o = some u` with `u ≤ c`. -/
def optLe (o : Option ℚ) (c : ℚ) : Bool :=
  match o with
  | some u => decide (u ≤ c)
  | none => false

/-- `o = some u` with `u < c`. -/
def optLt (o : Option ℚ) (c : ℚ) : Bool :=
  match o with
  | some u => decide (u < c)
  | none => false

/-- `o = some u` with `c < u`. -/
def optGt (o : Option ℚ) (c : ℚ) : Bool :=
  match o with
  | some u => decide (c < u)
  | none => false

lemma of_optLe {o : Option ℚ} {c : ℚ} (h : optLe o c = true) : ∃ u, o = some u ∧ u ≤ c := by
  unfold optLe at h
  split at h
  · rename_i u; exact ⟨u, rfl, of_decide_eq_true h⟩
  · cases h

lemma of_optLt {o : Option ℚ} {c : ℚ} (h : optLt o c = true) : ∃ u, o = some u ∧ u < c := by
  unfold optLt at h
  split at h
  · rename_i u; exact ⟨u, rfl, of_decide_eq_true h⟩
  · cases h

lemma of_optGt {o : Option ℚ} {c : ℚ} (h : optGt o c = true) : ∃ u, o = some u ∧ c < u := by
  unfold optGt at h
  split at h
  · rename_i u; exact ⟨u, rfl, of_decide_eq_true h⟩
  · cases h

/-- Upper bound for `A(s)` from an upper bound `u < 2` for `ζ(s)`. -/
def ordAHiQ (s : ℚ) (N : ℕ) : Option ℚ :=
  (zetaHiQ s N).bind fun u => if u < 2 then some (1 / (2 - u) - 1) else none

/-- Upper bound for `A₁` at `s`. -/
def ordA1HiQ (s : ℚ) (N : ℕ) : Option ℚ :=
  (zetaHiQ s N).bind fun u => (zetaDHiQ s N).bind fun d =>
    if u < 2 ∧ 0 ≤ d then some (d / (2 - u) ^ 2) else none

lemma zetaR_pos {s : ℝ} (hs : 1 < s) : 0 < zetaR s := by
  unfold zetaR
  apply (summable_zeta_terms hs).tsum_pos (i := 0)
  · intro n; exact Real.rpow_nonneg (by positivity) _
  · simp

lemma ordA_le {s : ℚ} {N : ℕ} {a : ℚ} (hs : 1 < s) (hN : 1 ≤ N) (h : ordAHiQ s N = some a) :
    zetaR s < 2 ∧ ordA s ≤ a := by
  unfold ordAHiQ at h
  obtain ⟨u, hu, h2⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h2 with hu2
  cases h2
  have hz := zetaR_le_of_zetaHiQ hs hN hu
  have hu2' : (u : ℝ) < 2 := by exact_mod_cast hu2
  refine ⟨by linarith, ?_⟩
  unfold ordA
  push_cast
  have : 1 / (2 - zetaR s) ≤ 1 / (2 - (u : ℝ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

lemma ordA1_le {s : ℚ} {N : ℕ} {a : ℚ} (hs : 1 < s) (hs2 : 1 / Real.log 2 ≤ s) (hN : 2 ≤ N)
    (h : ordA1HiQ s N = some a) : ordA1 s ≤ a := by
  unfold ordA1HiQ at h
  obtain ⟨u, hu, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, hd, h3⟩ := Option.bind_eq_some_iff.mp h2
  split_ifs at h3 with hc
  cases h3
  have hz := zetaR_le_of_zetaHiQ hs (by omega) hu
  have hzd := zetaDR_le_of_zetaDHiQ hs hs2 hN hd
  have hu2' : (u : ℝ) < 2 := by exact_mod_cast hc.1
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have hd0 : 0 ≤ zetaDR s := by
    unfold zetaDR
    apply tsum_nonneg
    intro n
    have := Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (n : ℝ) + 1)
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (-(s : ℝ))
    positivity
  unfold ordA1
  push_cast
  have h1 : (2 - (u : ℝ)) ^ 2 ≤ (2 - zetaR s) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  have h2' : 0 < 2 - (u : ℝ) := by linarith
  have h2 : 0 < (2 - (u : ℝ)) ^ 2 := by positivity
  calc zetaDR s / (2 - zetaR s) ^ 2 ≤ zetaDR s / (2 - (u : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_left hd0 h2 h1
    _ ≤ (d : ℝ) / (2 - (u : ℝ)) ^ 2 := div_le_div_of_nonneg_right hzd h2.le

lemma inv_log_two_le {s : ℝ} (hs : 1.45 ≤ s) : 1 / Real.log 2 ≤ s := by
  have := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The finite checks -/

lemma check_k1a : optGt (zetaLoQ (17286 / 10000) 3000) 2 = true := by native_decide
lemma check_k1b : optLt (zetaHiQ (17287 / 10000) 3000) 2 = true := by native_decide
lemma check_k2 : optLe (ordAHiQ (197 / 100) 3000) (207 / 100) = true := by native_decide
lemma check_k3 : optLe (ordA1HiQ (197 / 100) 3000) (942 / 100) = true := by native_decide
lemma check_k4 : optLe (zetaHiQ (18 / 10) 3000) (1883 / 1000 - 1 / 10 ^ 30) = true := by
  native_decide
lemma check_x1 : optLe (ordAHiQ (18 / 10 - 3 / 10 ^ 6) 3000) (74915 / 10000) = true := by
  native_decide
lemma check_x5 : optLe (ordAHiQ (177 / 100) 3000) (131 / 10) = true := by native_decide
lemma check_x6 : optLe (zetaHiQ (197 / 100) 3000) (1674 / 1000) = true := by native_decide
lemma check_x7 : optLe (zetaDHiQ (197 / 100) 3000) (10001 / 10000) = true := by native_decide

/-! ## The statements -/

/-- **k1.** `ζ(1.7286) > 2 > ζ(1.7287)`. -/
theorem zeta_bracket : 2 < zetaR 1.7286 ∧ zetaR 1.7287 < 2 := by
  obtain ⟨l, hl, hl2⟩ := of_optGt check_k1a
  obtain ⟨u, hu, hu2⟩ := of_optLt check_k1b
  have h1 := zetaLoQ_le_zetaR (by norm_num) (by norm_num) hl
  have h2 := zetaR_le_of_zetaHiQ (by norm_num) (by norm_num) hu
  have hl2' : (2 : ℝ) < l := by exact_mod_cast hl2
  have hu2' : (u : ℝ) < 2 := by exact_mod_cast hu2
  push_cast at h1 h2
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- **k1.** `ζ(s) = 2` has exactly one root `ρ₀` in `(1, ∞)`, and `ρ₀ ∈ (1.7286, 1.7287)`. -/
theorem rho0_spec : ∃! ρ : ℝ, 1 < ρ ∧ riemannZeta (ρ : ℂ) = 2 ∧ 1.7286 < ρ ∧ ρ < 1.7287 := by
  obtain ⟨h1, h2⟩ := zeta_bracket
  have hcont : ContinuousOn zetaR (Set.Icc 1.7286 1.7287) :=
    zetaR_continuousOn.mono (fun x hx => by simp at hx ⊢; linarith [hx.1])
  obtain ⟨ρ, hρ, hρ2⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨h2.le, h1.le⟩
  have hlo : (1.7286 : ℝ) < ρ := lt_of_le_of_ne hρ.1 (by rintro rfl; linarith)
  have hhi : ρ < 1.7287 := lt_of_le_of_ne hρ.2 (by rintro rfl; linarith)
  refine ⟨ρ, ⟨by linarith, ?_, hlo, hhi⟩, ?_⟩
  · rw [riemannZeta_eq_zetaR (by linarith), hρ2]; norm_num
  · rintro σ ⟨hσ, hσ2, -, -⟩
    rw [riemannZeta_eq_zetaR hσ] at hσ2
    have hσ3 : zetaR σ = 2 := by exact_mod_cast hσ2
    exact zetaR_strictAntiOn.injOn hσ (show (1 : ℝ) < ρ by linarith) (hσ3.trans hρ2.symm)

/-- Every root of `ζ(s) = 2` in `(1, ∞)` lies in `(1.7286, 1.7287)`. -/
theorem rho0_mem {ρ : ℝ} (hρ : 1 < ρ) (h : riemannZeta (ρ : ℂ) = 2) :
    1.7286 < ρ ∧ ρ < 1.7287 := by
  obtain ⟨h1, h2⟩ := zeta_bracket
  rw [riemannZeta_eq_zetaR hρ] at h
  have h' : zetaR ρ = 2 := by exact_mod_cast h
  constructor
  · by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hc | hc
    · have := zetaR_strictAntiOn (show (1 : ℝ) < ρ from hρ) (show (1 : ℝ) < 1.7286 by norm_num) hc
      linarith
    · rw [hc] at h'; linarith
  · by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hc | hc
    · have := zetaR_strictAntiOn (show (1 : ℝ) < 1.7287 by norm_num) (show (1 : ℝ) < ρ from hρ) hc
      linarith
    · rw [← hc] at h'; linarith

/-- **k2.** `A₀(0.03) = A(1.97) ≤ 2.07`. -/
theorem ordA_197_le : ordA 1.97 ≤ 2.07 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_k2
  have h := (ordA_le (by norm_num) (by norm_num) ha).2
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **k3.** `A₁(0.03) = -ζ'(1.97)/(2 - ζ(1.97))² ≤ 9.42`. -/
theorem ordA1_197_le : ordA1 1.97 ≤ 9.42 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_k3
  have h := ordA1_le (by norm_num) (inv_log_two_le (by norm_num)) (by norm_num) ha
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **k4.** `ζ(1.8) + 10⁻³⁰ ≤ 1.883` (the paper bounds `X₀^{-0.7} < 10⁻³⁰`). -/
theorem zeta_18_le : zetaR 1.8 + 1 / 10 ^ 30 ≤ 1.883 := by
  obtain ⟨u, hu, hu2⟩ := of_optLe check_k4
  have h := zetaR_le_of_zetaHiQ (by norm_num) (by norm_num) hu
  have := Rat.cast_le (K := ℝ) |>.mpr hu2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **k5.** `1/(2 - 1.883) ≤ 8.6`. -/
theorem k5 : (1 : ℝ) / (2 - 1.883) ≤ 8.6 := by norm_num

/-- **x1.** `A(1.8 - 3·10⁻⁶) ≤ 7.4915`. -/
theorem ordA_x1_le : ordA (1.8 - 3e-6) ≤ 7.4915 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_x1
  have h := (ordA_le (by norm_num) (by norm_num) ha).2
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **x5.** `A(1.77) ≤ 13.1` (and `ζ(1.77) < 2`, so `1.77` is beyond the abscissa `ρ₀`). -/
theorem ordA_177_le : zetaR 1.77 < 2 ∧ ordA 1.77 ≤ 13.1 := by
  obtain ⟨a, ha, ha2⟩ := of_optLe check_x5
  have h := ordA_le (by norm_num) (by norm_num) ha
  have := Rat.cast_le (K := ℝ) |>.mpr ha2
  push_cast at this
  push_cast at h; norm_num at h ⊢
  exact ⟨h.1, by linarith [h.2]⟩

/-- **x6.** `∑_{w ≥ 2} w^{-1.97} = ζ(1.97) - 1 ≤ 0.674`. -/
theorem zeta_197_sub_one_le : zetaR 1.97 - 1 ≤ 0.674 := by
  obtain ⟨u, hu, hu2⟩ := of_optLe check_x6
  have h := zetaR_le_of_zetaHiQ (by norm_num) (by norm_num) hu
  have := Rat.cast_le (K := ℝ) |>.mpr hu2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- **x7.** `∑_{w ≥ 2} w^{-1.97} log w = -ζ'(1.97) ≤ 1.0001`. -/
theorem zetaD_197_le : zetaDR 1.97 ≤ 1.0001 := by
  obtain ⟨u, hu, hu2⟩ := of_optLe check_x7
  have h := zetaDR_le_of_zetaDHiQ (by norm_num) (inv_log_two_le (by norm_num)) (by norm_num) hu
  have := Rat.cast_le (K := ℝ) |>.mpr hu2
  push_cast at this
  push_cast at h; norm_num at h ⊢; linarith

/-- `-ζ'(1.97) ≤ 1.0001`, stated with Mathlib's `riemannZeta`. -/
theorem neg_deriv_riemannZeta_197_le :
    -(deriv riemannZeta (1.97 : ℂ)).re ≤ 1.0001 := by
  have h := deriv_riemannZeta_eq (s := 1.97) (by norm_num)
  have e : ((1.97 : ℝ) : ℂ) = (1.97 : ℂ) := by norm_num
  rw [e] at h
  rw [h]
  simpa using zetaD_197_le

end BSCert.Consts
