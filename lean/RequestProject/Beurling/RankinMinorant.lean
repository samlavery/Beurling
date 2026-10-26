module

public import Mathlib

/-!
# The Rankin minorant `ς_*` of the absorbed-set count (proof of Lemma 4.4, via Lemma 6.26)

In the proof of Lemma 4.4 the paper bounds the absorbed set by

  `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}`,  `ς_*(v) := 0.9 ũ(v) log ũ(v)`,  `ũ(v) := v / λ(v)`,

with `λ(v) := max(22.6 Λ, 12 (log v)² + 9 log v + 8)` and `Λ = log X₀`, wherever `A ≠ ∅`; and
`A = ∅` at low heights. Here:

* `rankinU_monotoneOn`, `sigmaStar_monotoneOn` : `ũ` and `ς_*` are non-decreasing on `[Λ², ∞)`
  (the paper: "`ς_*` is continuous and increasing, since `v λ'(v) ≤ 24 log v + 9 < λ(v)`");
* `sigmaExt Λ ℓ := ς_*(max(ℓ, Λ²))` is a monotone exponent on all of `ℝ`;
* `sigmaExt_growth` : `42 log(2 + ℓ) + 5 ≤ sigmaExt Λ ℓ` for every `ℓ ≥ 0`, when `Λ ≥ 10⁸`;
* `countA_le_sigmaExt` : if `A ∩ [1, x]` is empty for `log x ≤ Λ²` and the bound with `ς_*`
  holds for `log x > Λ²`, then `#(A ∩ [1, x]) ≤ x e^{-sigmaExt Λ (log x)}` for all `x ≥ 1`.
-/

@[expose] public section

open Real Set

namespace RankinMinorant

/-- `λ(v) = max(22.6 Λ, 12 (log v)² + 9 log v + 8)`. -/
noncomputable def rankinLambda (Λ v : ℝ) : ℝ :=
  max (22.6 * Λ) (12 * Real.log v ^ 2 + 9 * Real.log v + 8)

/-- `ũ(v) = v / λ(v)`. -/
noncomputable def rankinU (Λ v : ℝ) : ℝ := v / rankinLambda Λ v

/-- The Rankin minorant `ς_*(v) = 0.9 ũ(v) log ũ(v)`. -/
noncomputable def sigmaStar (Λ v : ℝ) : ℝ := 0.9 * rankinU Λ v * Real.log (rankinU Λ v)

/-- The exponent `ς_*(max(ℓ, Λ²))`, monotone on all of `ℝ`. -/
noncomputable def sigmaExt (Λ ℓ : ℝ) : ℝ := sigmaStar Λ (max ℓ (Λ ^ 2))

/-- The polynomial part `g(v) = 12 (log v)² + 9 log v + 8` of `λ`. -/
noncomputable def polyPart (v : ℝ) : ℝ := 12 * Real.log v ^ 2 + 9 * Real.log v + 8

lemma polyPart_pos_of_one_le {v : ℝ} (hv : 1 ≤ v) : 0 < polyPart v := by
  have := Real.log_nonneg hv
  unfold polyPart; positivity

lemma hasDerivAt_polyPart {v : ℝ} (hv0 : v ≠ 0) :
    HasDerivAt polyPart (12 * (2 * Real.log v * v⁻¹) + 9 * v⁻¹) v := by
  have hl := Real.hasDerivAt_log hv0
  have := (((hl.pow 2).const_mul 12).add (hl.const_mul 9)).add_const 8
  convert this using 1
  norm_num

/-- `v / g(v)` is non-decreasing on `[e², ∞)`: its derivative has numerator
`g - v g' = 12 L² - 15 L - 1 ≥ 0` for `L = log v ≥ 2`. -/
lemma div_polyPart_monotoneOn : MonotoneOn (fun v => v / polyPart v) (Ici (Real.exp 2)) := by
  have he : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro v hv
    have hv1 : 1 ≤ v := he.trans hv
    have hv0 : v ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div continuousAt_id _ (polyPart_pos_of_one_le hv1).ne'
    unfold polyPart
    have := Real.continuousAt_log hv0
    fun_prop
  · intro v hv
    rw [interior_Ici] at hv
    have hv1 : 1 ≤ v := he.trans (le_of_lt hv)
    have hv0 : v ≠ 0 := by positivity
    have hg := hasDerivAt_polyPart hv0
    exact ((hasDerivAt_id' v).div hg (polyPart_pos_of_one_le hv1).ne').differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Ici] at hv
    have hv1 : 1 ≤ v := he.trans (le_of_lt hv)
    have hv0 : v ≠ 0 := by positivity
    have hvpos : 0 < v := by positivity
    have hg := hasDerivAt_polyPart hv0
    have hd : HasDerivAt (fun v => v / polyPart v) _ v :=
      (hasDerivAt_id' v).div hg (polyPart_pos_of_one_le hv1).ne'
    rw [hd.deriv]
    apply div_nonneg _ (sq_nonneg _)
    have hL : 2 ≤ Real.log v := by
      rw [Real.le_log_iff_exp_le hvpos]; exact le_of_lt hv
    simp only [polyPart]
    have : v * (12 * (2 * Real.log v * v⁻¹) + 9 * v⁻¹) = 24 * Real.log v + 9 := by
      field_simp; ring
    nlinarith

lemma rankinLambda_pos {Λ v : ℝ} (hΛ : 0 < Λ) : 0 < rankinLambda Λ v :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

/-- `ũ(v) = min(v / (22.6 Λ), v / g(v))` for `v ≥ 1`. -/
lemma rankinU_eq_min {Λ v : ℝ} (hΛ : 0 < Λ) (hv : 1 ≤ v) :
    rankinU Λ v = min (v / (22.6 * Λ)) (v / polyPart v) := by
  have hg := polyPart_pos_of_one_le hv
  have hv0 : 0 < v := by linarith
  unfold rankinU rankinLambda
  rcases le_total (22.6 * Λ) (polyPart v) with h | h
  · have h' : max (22.6 * Λ) (12 * Real.log v ^ 2 + 9 * Real.log v + 8) = polyPart v :=
      max_eq_right h
    rw [h', min_eq_right (div_le_div_of_nonneg_left hv0.le (by positivity) h)]
  · have h' : max (22.6 * Λ) (12 * Real.log v ^ 2 + 9 * Real.log v + 8) = 22.6 * Λ :=
      max_eq_left h
    rw [h', min_eq_left (div_le_div_of_nonneg_left hv0.le hg h)]

lemma sq_ge_exp_two {Λ : ℝ} (hΛ : 10 ≤ Λ) : Real.exp 2 ≤ Λ ^ 2 := by
  have : Real.exp 2 ≤ 10 := by
    have := Real.exp_one_lt_d9
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
  nlinarith

/-- `ũ` is non-decreasing on `[Λ², ∞)`. -/
lemma rankinU_monotoneOn {Λ : ℝ} (hΛ : 10 ≤ Λ) : MonotoneOn (rankinU Λ) (Ici (Λ ^ 2)) := by
  have hΛ0 : 0 < Λ := by linarith
  have he := sq_ge_exp_two hΛ
  have h1 : (1 : ℝ) ≤ Λ ^ 2 := by nlinarith
  intro v hv w hw hvw
  simp only [mem_Ici] at hv hw
  rw [rankinU_eq_min hΛ0 (h1.trans hv), rankinU_eq_min hΛ0 (h1.trans hw)]
  apply min_le_min
  · exact div_le_div_of_nonneg_right hvw (by positivity)
  · exact div_polyPart_monotoneOn (mem_Ici.mpr (he.trans hv)) (mem_Ici.mpr (he.trans hw)) hvw

/-- `g(v) ≤ √v` once `log v ≥ 33`. -/
lemma polyPart_le_sqrt {v : ℝ} (hvpos : 0 < v) (hv : 33 ≤ Real.log v) :
    polyPart v ≤ Real.sqrt v := by
  set y := Real.log v / 2 with hy
  have hy18 : 16.5 ≤ y := by rw [hy]; linarith
  have hsq : Real.sqrt v = Real.exp y := by
    rw [hy, Real.sqrt_eq_rpow, ← Real.exp_log hvpos, ← Real.exp_mul, Real.log_exp]
    ring_nf
  have hexp : y ^ 6 / 720 ≤ Real.exp y := by
    have := Real.pow_div_factorial_le_exp y (by linarith) 6
    simpa [Nat.factorial] using this
  have hL : Real.log v = 2 * y := by rw [hy]; ring
  rw [hsq]
  unfold polyPart
  rw [hL]
  have h4 : (16.5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  nlinarith [sq_nonneg y, mul_le_mul_of_nonneg_left h4 (sq_nonneg y)]

/-- Lower bounds on `ũ(v)` for `v ≥ Λ²`, `Λ ≥ 10⁸`: `ũ ≥ 4·10⁶` and `ũ² ≥ v/511`. -/
lemma rankinU_lower {Λ v : ℝ} (hΛ : 10 ^ 8 ≤ Λ) (hv : Λ ^ 2 ≤ v) :
    4 * 10 ^ 6 ≤ rankinU Λ v ∧ v ≤ 511 * rankinU Λ v ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hv1 : 1 ≤ v := by nlinarith
  have hvpos : 0 < v := by linarith
  have hlogv : 33 ≤ Real.log v := by
    have h1 : Real.log ((10 : ℝ) ^ 16) ≤ Real.log v := by
      apply Real.log_le_log (by norm_num); nlinarith
    have h2 : (33 : ℝ) ≤ Real.log ((10 : ℝ) ^ 16) := by
      have h8 : Real.log ((2 : ℝ) ^ 48) ≤ Real.log ((10 : ℝ) ^ 16) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h8
      have := Real.log_two_gt_d9
      push_cast at h8; linarith
    linarith
  have hg := polyPart_le_sqrt hvpos hlogv
  have hgpos := polyPart_pos_of_one_le hv1
  have hsqrt : Λ ≤ Real.sqrt v := Real.le_sqrt_of_sq_le hv
  have hsv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hvpos.le
  have hb : Real.sqrt v ≤ v / polyPart v := by
    rw [le_div_iff₀ hgpos]
    calc Real.sqrt v * polyPart v ≤ Real.sqrt v * Real.sqrt v :=
          mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)
      _ = v := hsv
  have ha : Λ / 22.6 ≤ v / (22.6 * Λ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  rw [rankinU_eq_min hΛ0 hv1]
  constructor
  · apply le_min
    · exact le_trans (by rw [le_div_iff₀ (by norm_num)]; nlinarith) ha
    · nlinarith
  · rcases min_choice (v / (22.6 * Λ)) (v / polyPart v) with h | h <;> rw [h]
    · rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
      have : v * Λ ^ 2 ≤ v * v := mul_le_mul_of_nonneg_left hv hvpos.le
      nlinarith
    · nlinarith [mul_le_mul hb hb (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hb)]

/-- `ς_*` is non-decreasing on `[Λ², ∞)`. -/
lemma sigmaStar_monotoneOn {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) :
    MonotoneOn (sigmaStar Λ) (Ici (Λ ^ 2)) := by
  intro v hv w hw hvw
  have hu := rankinU_monotoneOn (by linarith) hv hw hvw
  have hv1 := (rankinU_lower hΛ (mem_Ici.mp hv)).1
  have hlog := Real.log_le_log (by linarith) hu
  have hl0 : 0 ≤ Real.log (rankinU Λ v) := Real.log_nonneg (by linarith)
  unfold sigmaStar
  have := mul_le_mul hu hlog hl0 (by linarith)
  nlinarith

/-- `sigmaExt Λ` is monotone on `ℝ`. -/
lemma sigmaExt_monotone {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : Monotone (sigmaExt Λ) := by
  intro a b hab
  exact sigmaStar_monotoneOn hΛ (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
    (max_le_max hab le_rfl)

/-- **The uniform growth of the Rankin exponent**: `42 log(2 + ℓ) + 5 ≤ ς_*(max(ℓ, Λ²))` for every
`ℓ ≥ 0`, when `Λ ≥ 10⁸`. -/
theorem sigmaExt_growth {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    42 * Real.log (2 + ℓ) + 5 ≤ sigmaExt Λ ℓ := by
  set w := max ℓ (Λ ^ 2) with hw
  have hwΛ : Λ ^ 2 ≤ w := le_max_right _ _
  have hℓw : ℓ ≤ w := le_max_left _ _
  obtain ⟨hm, hm2⟩ := rankinU_lower hΛ hwΛ
  set m := rankinU Λ w with hmdef
  have hw1 : 1 ≤ w := by nlinarith
  have hlog1 : Real.log (2 + ℓ) ≤ Real.log (512 * m ^ 2) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlog2 : Real.log (512 * m ^ 2) = Real.log 512 + 2 * Real.log m := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h512 : Real.log 512 ≤ 7 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; linarith
  have hlm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  show 42 * Real.log (2 + ℓ) + 5 ≤ 0.9 * m * Real.log m
  nlinarith

/-- **The counting bound with the exponent `sigmaExt`**: if `A ∩ [1, x]` is empty for
`log x ≤ Λ²`, and `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` for `log x > Λ²`, then
`#(A ∩ [1, x]) ≤ x e^{-sigmaExt Λ (log x)}` for every `x ≥ 1`. -/
theorem le_sigmaExt {Λ : ℝ} (cnt : ℝ → ℝ)
    (hempty : ∀ x ≥ (1 : ℝ), Real.log x ≤ Λ ^ 2 → cnt x = 0)
    (hbound : ∀ x ≥ (1 : ℝ), Λ ^ 2 < Real.log x →
      cnt x ≤ x * Real.exp (-sigmaStar Λ (Real.log x))) :
    ∀ x ≥ (1 : ℝ), cnt x ≤ x * Real.exp (-sigmaExt Λ (Real.log x)) := by
  intro x hx
  rcases le_or_gt (Real.log x) (Λ ^ 2) with h | h
  · rw [hempty x hx h]; have : 0 < x := by linarith
    positivity
  · unfold sigmaExt; rw [max_eq_left h.le]; exact hbound x hx h

end RankinMinorant

end
