module

public import RequestProject.BSCert.CaplSH
meta import RequestProject.BSCert.CaplSH

/-!
# Steps 1 and 5 of the proof of Theorem 6.23

`caplw_check_independent.py` (and, at sample points, `analytic_capl.py`) test numerically:
* Step 1: `G(Λ, s)` is decreasing in `Λ` at fixed `s`;
* Step 5: `eˢ log(Λeˢ/(8 · 3.01 γ)) ≥ 107.6 γ²` for `s ≥ s_H`.

Here both are proved for all real parameters in the stated ranges.
-/

@[expose] public section

namespace BSCert.Capl

open Real Set

/-! ## Step 5 -/

/-- Partial sum of the exponential series. -/
def expLo (n : ℕ) (x : ℚ) : ℚ := ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)

lemma expLo_le {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : ((expLo n x : ℚ) : ℝ) ≤ Real.exp x := by
  unfold expLo; push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) n

lemma exp_sH_ge : (393 : ℝ) ≤ Real.exp 5.9745 := by
  have h := expLo_le (x := 59745 / 10000) (by norm_num) 40
  have hc : (393 : ℚ) ≤ expLo 40 (59745 / 10000) := by decide +kernel
  have hc' : (393 : ℝ) ≤ ((expLo 40 (59745 / 10000) : ℚ) : ℝ) := by exact_mod_cast hc
  have e : (((59745 / 10000 : ℚ)) : ℝ) = 5.9745 := by norm_num
  rw [e] at h
  linarith

lemma log_217e6_ge : (19.19 : ℝ) ≤ Real.log 217000000 := by
  have h := FX.logLoQF_le (a := 217000000) (by norm_num)
  have hc : (1919 / 100 : ℚ) ≤ FX.logLoQF 217000000 := by decide +kernel
  have hc' : ((1919 / 100 : ℚ) : ℝ) ≤ ((FX.logLoQF 217000000 : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at h hc'
  linarith

/-- **Step 5 of the proof of Theorem 6.23** (checked at random points by
`caplw_check_independent.py`): for `Λ ≥ 10⁸`, `s ≥ 5.9745` and `0 < γ ≤ 7.5`,
`eˢ log(Λeˢ/(8 · 3.01 γ)) ≥ 107.6 γ²`. -/
theorem step5 {Λ s γ : ℝ} (hΛ : 100000000 ≤ Λ) (hs : 5.9745 ≤ s) (hγ0 : 0 < γ) (hγ : γ ≤ 7.5) :
    107.6 * γ ^ 2 ≤ Real.exp s * Real.log (Λ * Real.exp s / (8 * 3.01 * γ)) := by
  have hE : 393 ≤ Real.exp s := le_trans exp_sH_ge (Real.exp_le_exp.mpr hs)
  have harg : (217000000 : ℝ) ≤ Λ * Real.exp s / (8 * 3.01 * γ) := by
    rw [le_div_iff₀ (by positivity)]
    have : (100000000 : ℝ) * 393 ≤ Λ * Real.exp s := mul_le_mul hΛ hE (by norm_num) (by linarith)
    nlinarith
  have hlog : 19.19 ≤ Real.log (Λ * Real.exp s / (8 * 3.01 * γ)) :=
    le_trans log_217e6_ge (Real.log_le_log (by norm_num) harg)
  have h1 : (393 : ℝ) * 19.19 ≤ Real.exp s * Real.log (Λ * Real.exp s / (8 * 3.01 * γ)) :=
    mul_le_mul hE hlog (by norm_num) (by linarith)
  have h2 : γ ^ 2 ≤ 7.5 ^ 2 := pow_le_pow_left₀ hγ0.le hγ 2
  nlinarith

/-! ## Step 1 -/

/-- `A(Λ, s)` written out, as a function of `Λ`. -/
noncomputable def Af (s Λ : ℝ) : ℝ :=
  Real.log 2 + 3 * Real.log Λ + 2 * s - Real.log (2 * Real.log Λ + s)

/-- `A(A+1)/(Λ - A - 1)`, so that `G = 2 e^{s/2} √(Qf)`. -/
noncomputable def Qf (s Λ : ℝ) : ℝ := Af s Λ * (Af s Λ + 1) / (Λ - Af s Λ - 1)

lemma log40_le : Real.log 40 ≤ 3.7 := by
  have h := FX.le_logHiQF (a := 40) (by norm_num)
  have hc : FX.logHiQF 40 ≤ (37 / 10 : ℚ) := by decide +kernel
  have hc' : ((FX.logHiQF 40 : ℚ) : ℝ) ≤ ((37 / 10 : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at h hc'
  linarith

/-- The facts about the domain used in Step 1. -/
lemma step1_dom {s Λ₁ Λ : ℝ} (h1 : 100000000 ≤ Λ₁) (hs : -Real.log Λ₁ ≤ s) (hs60 : s ≤ 60)
    (hΛ : Λ₁ ≤ Λ) :
    0 < Λ ∧ 18.42 ≤ Real.log Λ ∧ 1 ≤ 2 * Real.log Λ + s ∧ 12 ≤ Af s Λ ∧ Af s Λ + 1 < Λ ∧
      100000000 ≤ Λ := by
  have hΛ8 : 100000000 ≤ Λ := le_trans h1 hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : 18.42 ≤ Real.log Λ :=
    le_trans log1e8_bounds.1 (Real.log_le_log (by norm_num) hΛ8)
  have hlog1 : Real.log Λ₁ ≤ Real.log Λ := Real.log_le_log (by linarith) hΛ
  have hl : 1 ≤ 2 * Real.log Λ + s := by linarith
  refine ⟨hΛ0, hlogΛ, hl, ?_, ?_, hΛ8⟩
  · -- lower bound for `A`
    unfold Af
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have htan : Real.log (2 * Real.log Λ + s) ≤ (2 * Real.log Λ + s) / 40 + Real.log 40 - 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2 * Real.log Λ + s) / 40) (by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      linarith
    have := log40_le
    linarith
  · -- upper bound for `A`
    unfold Af
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
    have hl0 : 0 ≤ Real.log (2 * Real.log Λ + s) := Real.log_nonneg hl
    have hlogΛ' : Real.log Λ ≤ Λ / 1000 + 999 := by
      have := Real.log_le_sub_one_of_pos (x := Λ / 1000) (by positivity)
      rw [Real.log_div hΛ0.ne' (by norm_num)] at this
      have h1000 := Real.log_le_sub_one_of_pos (x := 1000) (by norm_num)
      linarith
    linarith

lemma hasDerivAt_Af {s Λ : ℝ} (hΛ : 0 < Λ) (hl : 0 < 2 * Real.log Λ + s) :
    HasDerivAt (Af s) (3 / Λ - 2 / Λ / (2 * Real.log Λ + s)) Λ := by
  have hlog := Real.hasDerivAt_log hΛ.ne'
  have h1 : HasDerivAt (fun x => 2 * Real.log x + s) (2 * Λ⁻¹) Λ :=
    (hlog.const_mul 2).add_const s
  have h2 := h1.log hl.ne'
  have h3 := (((hasDerivAt_const Λ (Real.log 2)).add (hlog.const_mul 3)).add_const (2 * s)).sub h2
  convert! h3 using 1
  field_simp
  ring

/-- `∂A/∂Λ`. -/
noncomputable def dA (s Λ : ℝ) : ℝ := 3 / Λ - 2 / Λ / (2 * Real.log Λ + s)

/-- `∂Qf/∂Λ`. -/
noncomputable def dQ (s Λ : ℝ) : ℝ :=
  ((dA s Λ * (Af s Λ + 1) + Af s Λ * dA s Λ) * (Λ - Af s Λ - 1)
    - Af s Λ * (Af s Λ + 1) * (1 - dA s Λ)) / (Λ - Af s Λ - 1) ^ 2

lemma hasDerivAt_Qf {s Λ : ℝ} (hΛ : 0 < Λ) (hl : 0 < 2 * Real.log Λ + s)
    (hden : Af s Λ + 1 < Λ) : HasDerivAt (Qf s) (dQ s Λ) Λ := by
  have hA := hasDerivAt_Af hΛ hl
  have hnum := hA.mul (hA.add_const 1)
  have hden' := ((hasDerivAt_id' Λ).sub hA).sub_const 1
  have := hnum.div hden' (by simp only [Pi.sub_apply]; linarith)
  exact this

lemma Qf_deriv_nonpos {s Λ : ℝ} (hΛ8 : 100000000 ≤ Λ) (hl : 1 ≤ 2 * Real.log Λ + s)
    (hA6 : 12 ≤ Af s Λ) (hden : Af s Λ + 1 < Λ) : dQ s Λ ≤ 0 := by
  have hΛ0 : 0 < Λ := by linarith
  unfold dQ
  have hd0 : 0 ≤ dA s Λ := by
    unfold dA
    rw [sub_nonneg, div_div, div_le_div_iff₀ (by positivity) hΛ0]
    nlinarith
  have hd3 : dA s Λ ≤ 3 / Λ := by
    unfold dA; have : 0 ≤ 2 / Λ / (2 * Real.log Λ + s) := by positivity
    linarith
  set a := Af s Λ
  set d := dA s Λ
  have hdΛ : d * Λ ≤ 3 := by
    have := mul_le_mul_of_nonneg_right hd3 hΛ0.le
    rwa [div_mul_cancel₀ _ hΛ0.ne'] at this
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have h1 : (d * (a + 1) + a * d) * (Λ - a - 1) ≤ 3 * (2 * a + 1) := by
    have : d * (Λ - a - 1) ≤ 3 := by nlinarith
    have e : (d * (a + 1) + a * d) * (Λ - a - 1) = (2 * a + 1) * (d * (Λ - a - 1)) := by ring
    rw [e]
    nlinarith
  have h3 : a * (a + 1) * d ≤ 3 * a := by
    have : (a + 1) * d ≤ 3 := by nlinarith
    nlinarith
  have h2 : 3 * (2 * a + 1) ≤ a * (a + 1) * (1 - d) := by nlinarith
  linarith

lemma G_eq_Qf {s Λ : ℝ} (hΛ : 0 < Λ) (hl : 0 < 2 * Real.log Λ + s) (hA : 0 ≤ Af s Λ) :
    G Λ s = 2 * Real.exp (s / 2) * Real.sqrt (Qf s Λ) := by
  unfold G Qf
  rw [A_eq hΛ hl, ← Af, Real.sqrt_div (by positivity)]
  ring

/-- **Step 1 of the proof of Theorem 6.23** (checked by `analytic_capl.py` at sample values of
`s` and by `caplw_check_independent.py` at random points): at fixed `s`, `G(Λ, s)` is
non-increasing in `Λ` on `Λ ≥ Λ₁`, whenever `Λ₁ ≥ 10⁸` and `-log Λ₁ ≤ s ≤ 60`. -/
theorem G_antitone {s Λ₁ Λ₂ : ℝ} (h1 : 100000000 ≤ Λ₁) (hs : -Real.log Λ₁ ≤ s) (hs60 : s ≤ 60)
    (h12 : Λ₁ ≤ Λ₂) : G Λ₂ s ≤ G Λ₁ s := by
  have hanti : AntitoneOn (Qf s) (Ici Λ₁) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici Λ₁)
    · intro Λ hΛ
      obtain ⟨hΛ0, -, hl, -, hden, -⟩ := step1_dom h1 hs hs60 hΛ
      exact (hasDerivAt_Qf hΛ0 (by linarith) hden).continuousAt.continuousWithinAt
    · intro Λ hΛ
      rw [interior_Ici] at hΛ
      obtain ⟨hΛ0, -, hl, -, hden, -⟩ := step1_dom h1 hs hs60 (le_of_lt hΛ)
      exact (hasDerivAt_Qf hΛ0 (by linarith) hden).hasDerivWithinAt
    · intro Λ hΛ
      rw [interior_Ici] at hΛ
      obtain ⟨-, -, hl, hA6, hden, hΛ8⟩ := step1_dom h1 hs hs60 (le_of_lt hΛ)
      exact Qf_deriv_nonpos hΛ8 hl hA6 hden
  obtain ⟨hΛ0₁, -, hl₁, hA₁, -, -⟩ := step1_dom h1 hs hs60 le_rfl
  obtain ⟨hΛ0₂, -, hl₂, hA₂, -, -⟩ := step1_dom h1 hs hs60 h12
  rw [G_eq_Qf hΛ0₁ (by linarith) (by linarith), G_eq_Qf hΛ0₂ (by linarith) (by linarith)]
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h12) h12
  gcongr

end BSCert.Capl
