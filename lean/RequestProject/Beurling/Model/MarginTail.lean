module

public import RequestProject.Beurling.Model.MarginSteps

/-!
# Small range facts for Step 5 of Proposition 5.38 (`htail` via `Margin.Rec.htail_loc`)

For `X₀^{1.01} ≤ t ≤ b`: `t > 0`, `log t ≥ 10⁸`, and `2t/X₀⁻ ≤ Zc b`.
-/

@[expose] public section

open Set Real Construction CaplLink Queue6

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀)
include hc

lemma htX_c {t : ℝ} (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) : (X₀ : ℝ) ≤ t := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  exact (Real.self_le_rpow_of_one_le hX1.le (by norm_num)).trans ht

lemma htpos_c {t : ℝ} (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) : 0 < t := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  linarith [htX_c hc ht]

lemma htlog_c {t : ℝ} (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) : 100000000 ≤ Real.log t := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have := Real.log_le_log (by linarith) (htX_c hc ht)
  have := hc.hX
  norm_num at this ⊢; linarith

lemma htZ_c {b t : ℝ} (hb : (X₀ : ℝ) ≤ b) (ht : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t) (htb : t ≤ b) :
    2 * t / Xm X₀ ≤ Zc X₀ b := by
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hH := (KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) b).le
  refine le_trans ?_ (Zc_facts hc hb).2.2.2
  rw [div_le_div_iff_of_pos_right hXm]; linarith

omit hc in
lemma hS2mi_c (hc : Cond θ X₀) (hev : Even X₀) (ω : JitterΩ) (z : ℝ) {s : ℝ} (hs0 : 0 ≤ s) :
    IntervalIntegrable (marginM θ X₀ ω) MeasureTheory.volume
      (z - Queue6.Hc X₀ z / 2) (z + Queue6.Hc X₀ z / 2 + s) :=
  marginM_ii hc hev ω (by linarith [KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) z])

end BModel

end
