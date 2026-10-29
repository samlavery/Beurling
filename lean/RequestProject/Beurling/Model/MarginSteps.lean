module

public import RequestProject.Beurling.Model.RestWire
public import RequestProject.Beurling.Noise.RML7Canon

/-!
# Proposition 5.38, Steps 1–5: the simple fields of `RestMargin` at the canonical parameters

For `p = canonP X₀ ε_H E_S j` (`BModel.RML7.canonP`) and `T₀ = c_∞ + K_c` (the cut-off
`c(1)` of the super-solution):

* `hT0wf_c`, `hT0T_c`, `hT0'_c` : `2 ≤ T₀(1 - θ₀)`, `T₀ ≤ b`, and `1.01 H(t) ≤ t` on `[T₀, b]`;
* `hρ0_c` : `ρ̃ = 0` below `X₀⁻` (the slot boxes `[s - H(s)/2, s + H(s)/2)`, `s ≥ X₀`, start
  above `X₀⁻ = X₀ - H(X₀)/2`, as `s - H(s)/2` is non-decreasing by (R_H));
* `hS2H_c` : `H(z) ≤ 1.01 H(x)` for `x ∈ [z - H(z)/2, z + 0.51 H(z)]` (`H` is
  `ε_H/10`-Lipschitz, `KR.WidthReal.Hc_abs`);
* `hS2mi_c` : `m` is integrable on every bounded interval;
* `hbase_c` : the base case below `T₀`: the window of `v(t)` lies below `X₀`, where `m = 0`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section

variable (hc : Cond θ X₀)
include hc

lemma hc_basics : (65536 : ℝ) ≤ X₀ ∧ (X₀ : ℝ) / 2 ≤ Xm X₀ ∧ Xm X₀ ≤ X₀ ∧
    Queue6.Hc X₀ (2 * X₀) ≤ 2 * X₀ / 40 ∧ Queue6.Hc X₀ X₀ ≤ X₀ / 40 := by
  have hX := hc.hX
  have h1 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  refine ⟨h1, KR.WidthReal.Xm_ge hX, RML7.Xm_le_X0 hX, ?_, ?_⟩
  · unfold Queue6.Hc; rw [max_eq_left (by linarith)]
    exact KR.WidthReal.capH_le_tenth hX (by linarith)
  · unfold Queue6.Hc; rw [max_self]
    exact KR.WidthReal.capH_le_tenth hX le_rfl

/-- `2 ≤ T₀(1 - θ₀)` (Proposition 5.38, Step 1). -/
theorem hT0wf_c (ES j : ℝ) :
    2 ≤ ((RML7.canonP X₀ epsH ES j).cinf + (RML7.canonP X₀ epsH ES j).Kc) *
      (1 - (RML7.canonP X₀ epsH ES j).θ0) := by
  obtain ⟨h1, h2, -, -, -⟩ := hc_basics hc
  have hH := KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) (2 * X₀)
  show 2 ≤ (1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀)) * (1 - 0.21)
  nlinarith

/-- `T₀ ≤ b` for `X₀ ≤ b`. -/
theorem hT0T_c (ES j : ℝ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b) :
    (RML7.canonP X₀ epsH ES j).cinf + (RML7.canonP X₀ epsH ES j).Kc ≤ b := by
  obtain ⟨-, -, h3, h4, -⟩ := hc_basics hc
  show 1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀) ≤ b
  linarith

/-- `0 ≤ t` and `1.01 H(t) ≤ t` on `[T₀, b]`. -/
theorem hT0'_c (ES j : ℝ) {b : ℝ} : ∀ t,
    (RML7.canonP X₀ epsH ES j).cinf + (RML7.canonP X₀ epsH ES j).Kc ≤ t → t ≤ b →
      0 ≤ t ∧ 1.01 * Queue6.Hc X₀ t ≤ t := by
  intro t ht _
  obtain ⟨h1, h2, -, -, h5⟩ := hc_basics hc
  have hH := KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) (2 * X₀)
  change 1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀) ≤ t at ht
  have ht0 : 0.3 * (X₀ : ℝ) ≤ t := by linarith
  refine ⟨by linarith, ?_⟩
  rcases le_total (X₀ : ℝ) t with h | h
  · have : Queue6.Hc X₀ t ≤ t / 40 := by
      unfold Queue6.Hc; rw [max_eq_left h]; exact KR.WidthReal.capH_le_tenth hc.hX h
    linarith
  · have : Queue6.Hc X₀ t = Queue6.Hc X₀ X₀ := by
      unfold Queue6.Hc; rw [max_eq_right h, max_self]
    rw [this]; linarith

/-- `H` is `4·10⁻⁷`-Lipschitz (`(R_H)`, `CapHSlope X₀ (4·10⁻⁶)`). -/
lemma Hc_lip (x y : ℝ) : |Queue6.Hc X₀ y - Queue6.Hc X₀ x| ≤ 4 / 10000000 * |y - x| := by
  have h := KR.WidthReal.Hc_abs hc.hX (by norm_num) (by norm_num)
    (CapHSlopeProof.capHSlope hc.hX) x y
  have e : (4 / 1000000 : ℝ) / 10 = 4 / 10000000 := by norm_num
  rwa [e] at h

/-- **`ρ̃ = 0` below `X₀⁻`** (§5.1: the slots are `≥ X₀`, their boxes start above
`X₀ - H(X₀)/2`). -/
theorem hρ0_c (ω : JitterΩ) : ∀ z, z < Xm X₀ → rhoT θ X₀ ω z = 0 := by
  intro z hz
  have hterm : ∀ k, (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
      (RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)).indicator 1 z) ω = 0 := by
    intro k
    set s := slotF θ X₀ k ω
    have hs : (X₀ : ℝ) ≤ s := slotF_ge hc k ω
    have hHs : HF θ X₀ k ω = Queue6.Hc X₀ s := by
      unfold HF Queue6.Hc; rw [max_eq_left hs]
    have hlip := Hc_lip hc X₀ s
    have hmono : Queue6.Hc X₀ X₀ ≤ Queue6.Hc X₀ s := KR.WidthReal.Hc_mono hc.hX hs
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hs)] at hlip
    have hXmH : Xm X₀ = X₀ - Queue6.Hc X₀ X₀ / 2 := by
      unfold Xm Queue6.Hc; rw [max_self]
    have hnot : z ∉ RankFull.box s (HF θ X₀ k ω) := by
      intro hm
      have h1 := hm.1
      rw [hHs] at h1
      nlinarith
    by_cases hA : ω ∈ lawA θ X₀ k
    · rw [Set.indicator_of_mem hA]
      show ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
        (RankFull.box s (HF θ X₀ k ω)).indicator 1 z = 0
      rw [Set.indicator_of_notMem hnot, mul_zero]
    · rw [Set.indicator_of_notMem hA]
  unfold rhoT
  simp only [hterm, tsum_zero, ENNReal.toReal_zero]

/-- **`H(z) ≤ 1.01 H(x)` on `[z - H(z)/2, z + 0.51 H(z)]`** (Proposition 5.38, Step 2; for every
`z`, by (R_H)). -/
theorem hS2H_c : ∀ z x, x ∈ Icc (z - Queue6.Hc X₀ z / 2) (z + 0.51 * Queue6.Hc X₀ z) →
    Queue6.Hc X₀ z ≤ 1.01 * Queue6.Hc X₀ x := by
  intro z x hx
  have hH := KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) z
  have hl := Hc_lip hc z x
  have hd : |x - z| ≤ 0.51 * Queue6.Hc X₀ z := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have h1 := abs_le.mp hl
  nlinarith [abs_nonneg (x - z)]

/-- **`m` is integrable on every bounded interval** (Step 2, `hS2mi`). -/
theorem marginM_ii (hev : Even X₀) (ω : JitterΩ) {p q : ℝ} (hpq : p ≤ q) :
    IntervalIntegrable (marginM θ X₀ ω) volume p q := by
  have h := (integral_TpCont hc ω (hpq.trans (le_max_left q (X₀ : ℝ)))
    (le_max_right _ _)).1.sub (compR_intervalIntegrable hc hev ω
      (hpq.trans (le_max_left q (X₀ : ℝ))))
  refine h.mono_set ?_
  rw [Set.uIcc_of_le hpq, Set.uIcc_of_le (hpq.trans (le_max_left _ _))]
  exact Set.Icc_subset_Icc le_rfl (le_max_left _ _)

/-- **The base case below `T₀`** (Proposition 5.38, Step 1): for `t < T₀`, the window
`|h| ≤ 1.01 H(t)` lies below `X₀`, where `m = 0`; and `Φ(t, 1) ≥ 0` (`t < c(1) = T₀`). -/
theorem hbase_c (ω : JitterΩ) {ES j : ℝ} (hj : 0 ≤ j) : ∀ t,
    t < (RML7.canonP X₀ epsH ES j).cinf + (RML7.canonP X₀ epsH ES j).Kc →
    Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω) t ≤
      Margin.Rec.PhiC (PR θ X₀ ω) (RML7.canonP X₀ epsH ES j) t 1 := by
  intro t ht
  obtain ⟨-, h2, h3, h4, h5⟩ := hc_basics hc
  change t < 1.21 * (Xm X₀ / 2) + 5 * Queue6.Hc X₀ (2 * X₀) at ht
  have htX : t < X₀ := by linarith
  have hHt : Queue6.Hc X₀ t = Queue6.Hc X₀ X₀ := by
    unfold Queue6.Hc; rw [max_eq_right htX.le, max_self]
  have hH0 := (KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) t).le
  have hv : Margin.Rec.vSup (Queue6.Hc X₀) (marginM θ X₀ ω) t ≤ 0 := by
    refine Margin.Rec.vSup_le hH0 fun hh hhh => ?_
    have h1 : t + hh < X₀ := by
      have := (abs_le.mp hhh).2; rw [hHt] at this; linarith
    rw [RML6.marginM_eq_zero_low hc ω h1, RML6.marginM_eq_zero_low hc ω htX]; simp
  refine hv.trans ?_
  unfold Margin.Rec.PhiC Margin.Rec.cutL
  simp only [KR.Sharp.Vl_one, Real.one_rpow, mul_one]
  have hn : ¬ ((RML7.canonP X₀ epsH ES j).cinf + (RML7.canonP X₀ epsH ES j).Kc ≤ t) :=
    not_le.mpr ht
  rw [if_neg hn, zero_add]
  split_ifs
  · exact hj
  · exact le_rfl

end

end BModel

end
