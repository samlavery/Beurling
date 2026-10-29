module

public import RequestProject.Beurling.Model.MarginH
public import RequestProject.Beurling.Noise.RML13Tail
public import RequestProject.Beurling.Noise.RML13VX

/-!
# Proposition 5.38, Steps 4–5 at the Model's objects (`RestMarginH`)

At `m* = MfH` (the harmonic local bound), `e = e12`, `j = jzX X₀` and the explicit
`E_S = 0.0014` (`ESH`):

* `MfH_le` : under (HBS) on `[1, Zc b]`, `MfH z ≤ 3.1 log(max z X₀) + 4.2` for `z ≤ b`
  (`RML12M.harmBound_le`), so Queue6's `fE_le_nuQ` applies on every strip;
* `h4K_H` : Step 4 with the filter `κ_w(t)` of 04g Step 3,
  `log t (o_V + 2η_V + ∑_w κ_w e/w) ≤ E_S`, from the inputs `log t · o_V ≤ so`,
  `log t · η_V ≤ sη`, `so + 2sη ≤ 0.0013`;
* `hEV_H`, `ha5_H` : `6.5 E_S + V_{X₀}(t) ≤ a₅ := 6.5 E_S + 10⁻⁶` on `[X₀^{1.01}, b]`
  (`VX_le`) and `a₅ ≤ 0.0097`.

The field `h4` of `RestMarginH` sums `e/w` over all of `F` without `κ_w(t)`; that sum is
`≳ log t/Λ⁵` (each `e(t, w) ≥ 210/log(t/w)⁶`), so the field fails for `log t ≫ Λ⁵ E_S` and
`b` is unbounded there. `h4K_H` is the paper's (filtered) Step 4.
-/

@[expose] public section

open Finset Real Set BeurlingSystem Construction BModel KR KR.Chain Queue6 CaplLink

namespace BModel.RML13

variable {θ : ℝ} {X₀ : ℕ}

/-- The explicit size parameter `E_S = 0.0014` of the recursion. -/
noncomputable def ESH : ℝ := 0.0014

/-- `a₅ = 6.5 E_S + 10⁻⁶` (Step 5). -/
noncomputable def a5H : ℝ := 6.5 * ESH + 1 / 10 ^ 6

theorem hES0_H : 0 ≤ ESH := by norm_num [ESH]

theorem ha5_H : a5H ≤ 0.0097 := by norm_num [a5H, ESH]

section Model

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

omit hev in
/-- **`m* ≤ 3.1 log(max z X₀) + 4.2`** for `z ≤ b`, under (HBS) at the horizon `Zc b`. -/
theorem MfH_le {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀)) :
    ∀ z, z ≤ b → MfH θ X₀ ω z ≤ 3.1 * Real.log (max z X₀) + 4.2 := by
  intro z hz
  have hX0 := X0_pos hc
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  obtain ⟨hXm1, -⟩ := Xm_bounds hc
  have hXm0 : 0 < Xm X₀ := by linarith
  set m := max z (X₀ : ℝ) with hm
  have hmX : (X₀ : ℝ) ≤ m := le_max_right _ _
  have hHz : Queue6.Hc X₀ z = Queue6.Hc X₀ m := by
    unfold Queue6.Hc; rw [hm, max_assoc, max_self]
  have hHm : Queue6.Hc X₀ m ≤ m / 10 ^ 7 := by
    have := Queue6.Hc_le hc m; rwa [max_eq_left hmX] at this
  have hH0 := Queue6.Hc_nonneg (X₀ := X₀) z
  have hHb : Queue6.Hc X₀ z ≤ Queue6.Hc X₀ b := KR.WidthReal.Hc_mono hc.hX hz
  set X := 2 * (max z 0 + 3 * Queue6.Hc X₀ z) / Xm X₀ with hXdef
  have hz0 : max z 0 ≤ m := max_le (le_max_left _ _) (by linarith)
  have hXm : X ≤ m := by
    rw [hXdef, div_le_iff₀ hXm0]
    have hX3 : (3 : ℝ) ≤ X₀ := by
      have := hc.hX
      have h3 : Real.log 3 < 10 ^ 8 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      by_contra hlt; push_neg at hlt
      have := Real.log_le_log hX0 hlt.le; linarith
    nlinarith
  have hXZ : X ≤ Zc X₀ b := by
    have h18 := Zc_18 hc hb
    have hb0 : 0 ≤ b := by linarith
    have : X ≤ 18 * (b + Queue6.Hc X₀ b) / Xm X₀ := by
      rw [hXdef]
      refine div_le_div_of_nonneg_right ?_ hXm0.le
      have := max_le hz hb0
      linarith
    linarith
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hmf : MfH θ X₀ ω z = 2 + 2 * ∑ e ∈ (PR θ X₀ ω).elems X, 1 / (PR θ X₀ ω).val e := rfl
  rw [hmf]
  rcases le_or_gt 1 X with h1 | h1
  · have := RML12M.harmBound_le hbs h1 hXZ
    have := Real.log_le_log (by linarith) hXm
    linarith
  · have hZ1 : (1 : ℝ) ≤ Zc X₀ b := by
      have := (Zc_facts hc hb).2.1; linarith
    have := (RML12M.harmBound_mono (PR θ X₀ ω) h1.le).trans
      (RML12M.harmBound_le hbs le_rfl hZ1)
    rw [Real.log_one] at this
    linarith

/-- **Step 4 of Proposition 5.38 at the Model's objects, with the filter `κ_w(t)`** (04g
Step 3): at `E_S = ESH`, `j = jzX X₀`, `e = e12` at `m* = MfH`, on `[T₀, b]`. Inputs: the
oscillation and average bounds `ho`, `hη` (Step 4's `o`, `η`) with `so + 2sη ≤ 0.0013`. -/
theorem h4K_H {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) (so sη : ℝ)
    (ho : ∀ t, ((RML7.canonP X₀ epsH ESH (jzX X₀)).cinf +
      (RML7.canonP X₀ epsH ESH (jzX X₀)).Kc) ≤ t → t ≤ b →
        Real.log t * oVc θ X₀ ω t ≤ so)
    (hη : ∀ t, ((RML7.canonP X₀ epsH ESH (jzX X₀)).cinf +
      (RML7.canonP X₀ epsH ESH (jzX X₀)).Kc) ≤ t → t ≤ b →
        Real.log t * ηVc θ X₀ ω (RML7.canonP X₀ epsH ESH (jzX X₀)) t ≤ sη)
    (hsize : so + 2 * sη ≤ 0.0013) :
    ∀ t, ((RML7.canonP X₀ epsH ESH (jzX X₀)).cinf +
      (RML7.canonP X₀ epsH ESH (jzX X₀)).Kc) ≤ t → t ≤ b →
      Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ESH (jzX X₀))) t +
        ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ESH (jzX X₀)) t,
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w *
            (RML12M.e12 X₀ (PR θ X₀ ω) (MfH θ X₀ ω) t w / KR.Vl (PR θ X₀ ω) w)) ≤ ESH := by
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hZ := Zc_facts hc hb
  obtain ⟨hXm1, -⟩ := Xm_bounds hc
  have hX0 := X0_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  have hbZ : 2 * b / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans (div_le_div_of_nonneg_right ?_ hXm0.le) hZ.2.2.2
    have := Queue6.Hc_nonneg (X₀ := X₀) b; linarith
  have hΛ : 60000 / Real.log X₀ ^ 4 ≤ 0.0001 := by
    have h8 := hc.hX
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (by norm_num) h8 4
    norm_num at this ⊢
    linarith
  exact h4_13 hc ω (MfH_nonneg hc hev ω) (MfH_mono hc hev ω) (MfH_le hc hb hbs) hT ESH (jzX X₀)
    so sη hZ.1 hbZ ho hη (by unfold ESH; linarith)

/-- **The field `hEV` of `RestMarginH`** at `E_S = ESH`, `a₅ = a5H`: on `[X₀^{1.01}, b]`,
`6.5 E_S + V_{X₀}(t) ≤ 6.5 E_S + 10⁻⁶` (`VX_le`; `j₀ ≤ 1.0001/Λ` from (huxley)). -/
theorem hEV_H {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) (hH : BaseRange.HuxleyFrom (X₀ : ℝ)) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      6.5 * (RML7.canonP X₀ epsH ESH (jzX X₀)).ES +
        VX (PR θ X₀ ω) (RML7.canonP X₀ epsH ESH (jzX X₀)) t ≤ a5H := by
  intro t ht htb
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hZ := Zc_facts hc hb
  obtain ⟨hXm1, -⟩ := Xm_bounds hc
  have hX0 := X0_pos hc
  have hXm0 : 0 < Xm X₀ := by linarith
  have htZ : 2 * t / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans (div_le_div_of_nonneg_right ?_ hXm0.le) hZ.2.2.2
    have := Queue6.Hc_nonneg (X₀ := X₀) b; linarith
  have hXm : 100000000 ≤ Real.log (Xm X₀) := by
    have := hT.hXm; norm_num at this ⊢; linarith
  have := VX_le hc.hX (εH := epsH) (ES := ESH) hbs hXm hXm1 (jzX_nonneg hc)
    (BaseRange.jzX_le hc.hX hH) ht htZ
  show 6.5 * ESH + _ ≤ a5H
  unfold a5H
  linarith

end Model

end BModel.RML13

end
