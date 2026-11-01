module

public import RequestProject.Beurling.Noise.RML6G1
public import RequestProject.Beurling.Noise.KRWidthReal

/-!
# The heights read by Proposition 5.35(B) at a start `y` lie below the event height `b`

At a range-(B) start `y` (`X₀^{1/100} < log y`) the window parameter `δ` of Proposition
5.35(B) satisfies `1/δ ≤ e^{c_LP √(log y)/2} log⁴ y + X₀^{1/2}` (`hδlow`). Since `H_c(y) ≤ y^{1/8}`
this gives `δ y ≥ 2 H_c(y)` (`two_Hc_le_delta_mul`), so the top of the read range,
`Ytop y δ = y(1-δ) + H_c(y)/2`, is at most `y - (3/2) H_c(y)` (`Ytop_le`). Hence for
`y ≤ b + H_c(b)` every height read (`J = [y(1-2δ), y(1-δ)]` and the windows of its points) is
`≤ b` (`Ytop_le_b`): Proposition 5.35(B) at `y` reads no event past `b` (cf. corrections
#106–#109).
-/

@[expose] public section

open Real

namespace KR.RML9

/-- The top of the heights read at a start `y`: `y(1-δ) + H_c(y)/2`. -/
noncomputable def Ytop (X₀ : ℕ) (y δ : ℝ) : ℝ := y * (1 - δ) + Queue6.Hc X₀ y / 2

lemma Hc_le_rpow8 {X₀ : ℕ} (hX : 100000000 ≤ Real.log X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    Queue6.Hc X₀ y ≤ y ^ (1 / 8 : ℝ) := by
  unfold Queue6.Hc
  rw [max_eq_left hy]
  exact InitialRange.capH_le_rpow (Nat.cast_nonneg _) (by norm_num; linarith) hy

lemma exp_div100_ge_top {Λ : ℝ} (hΛ : 100000000 ≤ Λ) : Λ + 2 ≤ Real.exp (Λ / 100) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := Λ / 100) (by linarith)
  nlinarith

/-- `log L ≤ L/16` for `L ≥ 10⁸`. -/
lemma log_le_div16 {L : ℝ} (hL : 100000000 ≤ L) : Real.log L ≤ L / 16 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < L / 64 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h1
  have h64 : Real.log 64 ≤ 64 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 by norm_num); linarith
  linarith

/-- **`δ y ≥ 2 H_c(y)`** at a range-(B) start, from the lower bound `hδlow` on `δ`. -/
theorem two_Hc_le_delta_mul {X₀ : ℕ} {y δ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)) :
    2 * Queue6.Hc X₀ y ≤ δ * y := by
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hΛ; linarith
  have h8 : (10 : ℝ) ^ 8 ≤ Real.log X₀ := by norm_num; linarith
  have hr : (X₀ : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Real.log X₀ / 100) := by
    rw [Real.rpow_def_of_pos hX0]; ring_nf
  have hHp := KR.WidthReal.Hc_pos h8 y
  set L := Real.log y with hLdef
  set Λ := Real.log X₀ with hΛdef
  have hLΛ : Λ + 2 ≤ L := by
    have := exp_div100_ge_top hΛ; rw [hr] at hy; linarith
  have hL : 100000000 ≤ L := by linarith
  have hyeq : y = Real.exp L := (Real.exp_log hy0).symm
  -- `X₀ ≤ y`
  have hXy : (X₀ : ℝ) ≤ y := by
    rw [hyeq, ← Real.exp_log hX0]; exact Real.exp_le_exp.mpr (by linarith)
  -- the first term: `e^{c √L /2} L⁴ ≤ e^{L/2}`
  have hc0 : 0 ≤ LocalPNT.cLP Λ := by
    unfold LocalPNT.cLP LocalPNT.cZF; positivity
  have hc1 : LocalPNT.cLP Λ ≤ 1 := by
    unfold LocalPNT.cLP LocalPNT.cZF
    rw [div_div, div_le_one (by positivity)]; linarith
  have hsq : √L ≤ L / 4 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqn : 0 ≤ √L := Real.sqrt_nonneg _
  have he1 : Real.exp (LocalPNT.cLP Λ * √L / 2) ≤ Real.exp (L / 4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hL4 : L ^ 4 ≤ Real.exp (L / 4) := by
    have hlog := log_le_div16 hL
    have : L ^ 4 = Real.exp (4 * Real.log L) := by
      rw [← Real.exp_log (show 0 < L ^ 4 by positivity), Real.log_pow]; norm_num
    rw [this]; exact Real.exp_le_exp.mpr (by linarith)
  have hT1 : Real.exp (LocalPNT.cLP Λ * √L / 2) * L ^ 4 ≤ Real.exp (L / 2) := by
    calc Real.exp (LocalPNT.cLP Λ * √L / 2) * L ^ 4 ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
          mul_le_mul he1 hL4 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (L / 2) := by rw [← Real.exp_add]; ring_nf
  -- the second term: `X₀^{1/2} = e^{Λ/2} ≤ e^{L/2}`
  have hT2 : (X₀ : ℝ) ^ (1 / 2 : ℝ) ≤ Real.exp (L / 2) := by
    rw [Real.rpow_def_of_pos hX0]; exact Real.exp_le_exp.mpr (by linarith)
  have hinv : 1 / δ ≤ 2 * Real.exp (L / 2) := by linarith
  -- `H_c(y) ≤ y^{1/8} = e^{L/8}`
  have hH : Queue6.Hc X₀ y ≤ Real.exp (L / 8) := by
    have := Hc_le_rpow8 hΛ hXy
    rwa [Real.rpow_def_of_pos hy0, ← hLdef, show L * (1 / 8) = L / 8 by ring] at this
  -- `4 e^{L/8} e^{L/2} ≤ e^{L}`
  have hkey : 4 * (Real.exp (L / 8) * Real.exp (L / 2)) ≤ Real.exp L := by
    rw [← Real.exp_add]
    have h4 : (4 : ℝ) ≤ Real.exp (3 * L / 8) := by
      have := Real.add_one_le_exp (3 * L / 8); linarith
    calc 4 * Real.exp (L / 8 + L / 2) ≤ Real.exp (3 * L / 8) * Real.exp (L / 8 + L / 2) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp L := by rw [← Real.exp_add]; ring_nf
  have hδy : 1 / δ * (2 * Queue6.Hc X₀ y) ≤ y := by
    have : 1 / δ * (2 * Queue6.Hc X₀ y) ≤ Real.exp L :=
      calc 1 / δ * (2 * Queue6.Hc X₀ y) ≤ 2 * Real.exp (L / 2) * (2 * Real.exp (L / 8)) :=
            mul_le_mul hinv (by linarith) (by linarith) (by positivity)
        _ = 4 * (Real.exp (L / 8) * Real.exp (L / 2)) := by ring
        _ ≤ Real.exp L := hkey
    exact this.trans_eq hyeq.symm
  rw [one_div, inv_mul_le_iff₀ hδ0] at hδy
  linarith

/-- **The top of the read range**: `y(1-δ) + H_c(y)/2 ≤ y - (3/2) H_c(y)`. -/
theorem Ytop_le {X₀ : ℕ} {y δ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)) :
    Ytop X₀ y δ ≤ y - 3 / 2 * Queue6.Hc X₀ y := by
  have := two_Hc_le_delta_mul hΛ hy0 hy hδ0 hδlow
  unfold Ytop; nlinarith

/-- **`J < b`**: for a start `y ≤ b + H_c(b)`, every height read by Proposition 5.35(B) at
`y` (the interval `J = [y(1-2δ), y(1-δ)]` and the windows `[z ± H_c(z)/2]`, `z ∈ J`) lies
below `b`. -/
theorem Ytop_le_b {X₀ : ℕ} {y δ b : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hy0 : 0 < y)
    (hy : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hδ0 : 0 < δ)
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log y) / 2) *
      Real.log y ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ)) (hyb : y ≤ b + Queue6.Hc X₀ b) :
    Ytop X₀ y δ ≤ b := by
  have h := Ytop_le hΛ hy0 hy hδ0 hδlow
  have h8 : (10 : ℝ) ^ 8 ≤ Real.log X₀ := by norm_num; linarith
  rcases le_or_gt y b with hb | hb
  · have := KR.WidthReal.Hc_pos h8 y; linarith
  · have := KR.WidthReal.Hc_mono h8 hb.le; linarith

/-- The window points of `J` lie below `Ytop`. -/
lemma win_le_Ytop {X₀ : ℕ} {y δ : ℝ} (hΛ : 100000000 ≤ Real.log X₀) (hy0 : 0 < y)
    (hδ0 : 0 < δ) {z s : ℝ} (hz : z ∈ Set.Icc (y * (1 - 2 * δ)) (y * (1 - δ)))
    (hs : s ≤ z + Queue6.Hc X₀ z / 2) : s ≤ Ytop X₀ y δ := by
  obtain ⟨-, hz2⟩ := hz
  have hzy : z ≤ y := by nlinarith
  have := KR.WidthReal.Hc_mono (by norm_num; linarith : (10 : ℝ) ^ 8 ≤ Real.log X₀) hzy
  unfold Ytop; linarith

end KR.RML9

end
