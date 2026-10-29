module

public import RequestProject.Beurling.Model.G1BQ6
public import RequestProject.Beurling.Noise.RML10G1
public import RequestProject.Beurling.Noise.RML10Rest

/-!
# The §5 group `G1ResSec5` of Proposition 5.35(B) at the Model's bounds (`RML10.sec5_of`)

`g1Sec5_c` supplies `KR.RML10.sec5_of`'s Model inputs at a range-(B) start `y`:

* `WinGlob` (the global facts: `tnpR`, `opR`, the width at `X₀⁻/2`, `X₀⁻ = X₀ - H(X₀)/2`,
  `dec_R`, `3θ ≤ 10⁻³`, `|T_c| ≤ 2` below `3y`, the horizons `4y/X₀⁻ ≤ Z`, `36y ≤ Z²` (`Zc_36`),
  `H(X₀)/X₀` tiny);
* the two bullets of Lemma 5.34 on `J = [y(1-2δ), y(1-δ)]`: `hK_c`, `hG_c` at the centres
  `z ∈ J` (`X₀^{1.01} ≤ z ≤ b`, `horJ`), with `S = SK`, `G = ∑ (log 3v)² (obG + F̄_r)`;
* `h6`: `6 log y/H(z) ≤ 5·10⁻²¹` on `J`; `δ` facts.

The remaining inputs are §5's `WinAt` at the window heights (`W`) and the two sizes
`S ≤ 10⁻²⁰`, `G ≤ e^{-41} + 2·10⁻²²` on `J` (`hSb`, `hGbd`: the Lemma 5.20 block sums of `s_η`
together with `sum_oscG_le`, `sum_sixH_le`, `Queue6.sum_nbQ_le`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (θ X₀) in
/-- The `G`-term of Lemma 5.34, second bullet, at the centre `z`. -/
noncomputable def Gsum (ω : JitterΩ) (nb : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Jc X₀ z + 1), Real.log (3 * (Xm X₀ * 2 ^ i)) ^ 2 *
    (obG X₀ i + FrBv θ X₀ ω nb i)

variable (hc : Cond θ X₀)
include hc

/-- `36 (b + H(b)) ≤ Z²`. -/
theorem Zc_36 {b : ℝ} (hb : (X₀ : ℝ) ≤ b) : 36 * (b + Queue6.Hc X₀ b) ≤ Zc X₀ b ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXmh := Xm_half hc
  have hH : Queue6.Hc X₀ b ≤ b / 4 := by
    unfold Queue6.Hc
    rw [max_eq_left hb]
    have := four_capH_le hX0 hc.hX hb
    linarith
  unfold Zc
  split_ifs with hbig
  · nlinarith
  · push_neg at hbig
    nlinarith

/-- A range-(B) start is far above `X₀^{1.01}`: `X₀^{1.01} ≤ y/2`. -/
lemma X1_le_half {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    (X₀ : ℝ) ^ (1.01 : ℝ) ≤ y / 2 := by
  have hX := hc.hX
  have hX1 := one_lt_X0 hc
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hy0 : 0 < y := by linarith
  have hLe : Real.exp (Real.log X₀ / 100) ≤ Real.log y := by
    rw [Real.rpow_def_of_pos hXp] at hyL
    have : Real.log X₀ * (1 / 100) = Real.log X₀ / 100 := by ring
    rw [this] at hyL; exact hyL.le
  obtain ⟨-, h3⟩ := D_le hX hLe (c := 0) le_rfl zero_le_one
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hXp,
    Real.log_div hy0.ne' (by norm_num)]
  have := Real.log_two_lt_d9
  nlinarith

variable (hev : Even X₀)
include hev

set_option maxHeartbeats 4000000 in
/-- **`G1ResSec5` at the Model's bounds** (`RML10.sec5_of`), from §5's window inputs `W` and
the two sizes `hSb`, `hGbd`. -/
noncomputable def g1Sec5_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) (hnu : Nu522 θ X₀ ω b (nbQ X₀))
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyL : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y)
    (W : ∀ s, y / 4 ≤ s → s ≤ KR.RML9.Ytop X₀ y (deltaB θ X₀ ω y) →
      KR.RML10.WinAt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (TcR θ X₀ ω (jzX X₀)) s)
    (hSb : ∀ z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y), SK θ X₀ ω (nbQ X₀) z ≤ 1 / 10 ^ 20)
    (hGbd : ∀ z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y),
      Gsum θ X₀ ω (nbQ X₀) z ≤ Real.exp (-41) + 2 / 10 ^ 22) :
    KR.RML9.G1ResSec5 (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ y (deltaB θ X₀ ω y) (ρLd θ X₀ ω)
      (nuLd θ X₀ ω) (NTd θ X₀ ω) 0 (TcLd θ X₀ ω) (JL (jzX X₀) X₀) (TcR θ X₀ ω (jzX X₀)) hO :=
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hZ := Zc_facts hc hb
  have hZ18 := Zc_18 hc hb
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  have hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n :=
    fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have x0s := Queue6.x0sHyp_G0 (e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  have hR := KR.RML9.g1_range (by norm_num at hX ⊢; linarith) (y_pos_c hc hy) hyL
    (deltaB_le (θ := θ) ω y)
  have hJ : ∀ z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y),
      (X₀ : ℝ) ^ (1.01 : ℝ) ≤ z ∧ z ≤ b ∧ (X₀ : ℝ) ≤ z ∧ y / 2 ≤ z := fun z hz => by
    obtain ⟨-, -, -, -, hδ4, -, -⟩ := hR
    have hδ0 := deltaB_pos hc ω hy
    have hz1 : y / 2 ≤ z := by nlinarith [hz.1]
    have h1 := X1_le_half hc hy hyL
    have hX1t := RML10.X0_le_X1 hX
    have hzX : (X₀ : ℝ) ≤ z := by linarith
    have h2 := horJ hc ω hb hy hyb hyL hzX hz.2
    have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) z).le
    exact ⟨by linarith, by linarith, hzX, hz1⟩
  have Gw : KR.RML10.WinGlob (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ y (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10) (TcR θ X₀ ω (jzX X₀)) :=
    { htnp := hT
      hO := hO
      hHw := KR.WidthReal.Hc_Xm_half_le hX
      hX0e := by unfold Xm Queue6.Hc; rw [max_self]
      hX0m := Xm_le_X0 hc
      hXmZ := hZ.1
      ht := (KR.Chain.dec_R hT).1
      htv := (KR.Chain.dec_R hT).2
      hθ3 := by norm_num [epsH]
      hTm := measurable_TcR hc ω _
      hTb := fun s hs => TcR_abs_le hc hev ω hT (le_trans
        (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ18)
      hZ0 := hZ.2.1
      hZ := le_trans (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ.2.2.2
      hZ18 := le_trans (by linarith) hZ.2.2.1
      hH1 := KR.WidthReal.capH_one_le hX le_rfl |>.trans (by unfold Queue6.Hc; rw [max_self])
      hδ := by
        have h := Queue6.capH_le_div hX (le_refl (X₀ : ℝ))
        have hXp : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
        unfold Queue6.Hc; rw [max_self, div_le_iff₀ hXp]
        linarith
      hδs := by
        have hX1' := one_lt_X0 hc
        have hXp : (0 : ℝ) < X₀ := by linarith
        have h8 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hX le_rfl
        have hsq : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1'.le (by norm_num)
        have hsplit : (X₀ : ℝ) = (X₀ : ℝ) ^ (1 / 2 : ℝ) * (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hXp]; norm_num
        have hs0 : 0 < (X₀ : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXp _
        have hsE : (X₀ : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Real.log X₀ / 2) := by
          rw [Real.rpow_def_of_pos hXp]; congr 1; ring
        have hbig : 200000 * Real.exp 61 ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
          rw [hsE]
          have h1 : Real.exp 61 * Real.exp 13 = Real.exp (74 : ℝ) := by
            rw [← Real.exp_add]; norm_num
          have h2 : (200000 : ℝ) ≤ Real.exp 13 := by
            have := Real.add_one_le_exp (13 : ℝ)
            have e : Real.exp 13 = Real.exp 1 ^ 13 := by
              rw [← Real.exp_nat_mul]; norm_num
            have h := Real.exp_one_gt_d9
            rw [e]
            calc (200000 : ℝ) ≤ 2.7182818283 ^ 13 := by norm_num
              _ ≤ Real.exp 1 ^ 13 := by gcongr
          have h3 : Real.exp (74 : ℝ) ≤ Real.exp (Real.log X₀ / 2) :=
            Real.exp_le_exp.mpr (by linarith)
          nlinarith [Real.exp_pos 61]
        unfold Queue6.Hc; rw [max_self]
        have hq : capH (X₀ : ℝ) (X₀ : ℝ) / X₀ ≤ 1 / (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
          rw [div_le_div_iff₀ hXp hs0, one_mul]
          nlinarith
        have h61 : 200000 * (1 / (X₀ : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.exp (-61) := by
          rw [Real.exp_neg, mul_one_div, div_le_iff₀ hs0]
          have := Real.exp_pos 61
          rw [inv_mul_eq_div, le_div_iff₀ this]
          linarith
        linarith }
  KR.RML10.sec5_of hO Gw (y_pos_c hc hy) hyL (deltaB_pos hc ω hy) (deltaB_le (θ := θ) ω y)
    (SK θ X₀ ω (nbQ X₀)) (Gsum θ X₀ ω (nbQ X₀))
    (fun z hz => by
      obtain ⟨h1, h2, -, -⟩ := hJ z hz
      have := hK_c hc hev hb hT x0s (SK θ X₀ ω (nbQ X₀)) (fun _ _ u => GK θ X₀ ω (nbQ X₀) u)
        (hFr_c hc hev hb hbt hG.1 hE1 hN hT hnu) hO z h1 h2
      rw [nuLd_eq ω hO]; exact this)
    (fun z hz => by
      obtain ⟨h1, h2, -, -⟩ := hJ z hz
      have := hG_c hc hev hb hbt hG.1 hE1 hN hT x0s (fun _ i => FrBv θ X₀ ω (nbQ X₀) i)
        (fun _ i => FrBv_nonneg hc hev hT hnu.1 i) (hFrB_c hc hev hb hbt hG.1 hE1 hN hT hnu)
        hO z h1 h2
      rw [nuLd_eq ω hO]; exact this)
    (1 / 10 ^ 20) (Real.exp (-41) + 2 / 10 ^ 22) (5 / 10 ^ 21)
    (fun z _ => by
      unfold SK
      refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (GK_nonneg hc hev hT hnu.1 _)
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have := KR.WidthReal.X0_ge hX (X₀ := X₀)
      exact Real.log_nonneg (by nlinarith))
    hSb le_rfl
    (fun z _ => by
      unfold Gsum
      refine Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) ?_
      have h1 := Bsc_nonneg hc (u := Xm X₀ * 2 ^ i) (by positivity)
      have h2 := FrBv_nonneg hc hev hT hnu.1 i
      unfold obG; linarith)
    hGbd le_rfl
    (fun z hz => by
      obtain ⟨-, -, hzX, hz2⟩ := hJ z hz
      have h := RML10.logH_tiny hX hzX
      have hz0 : 0 < z := by linarith [one_lt_X0 hc]
      have hly : Real.log y ≤ 2 * Real.log z := by
        have h1 : Real.log y ≤ Real.log (2 * z) := Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul (by norm_num) hz0.ne'] at h1
        have : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) (by
          have := KR.WidthReal.X0_ge hX (X₀ := X₀); linarith)
        linarith
      have hH := KR.WidthReal.Hc_pos hX (X₀ := X₀) z
      have : 6 * Real.log y / Queue6.Hc X₀ z ≤ 2 * (6 * Real.log z / Queue6.Hc X₀ z) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) hH.le
      linarith)
    (by norm_num) (deltaB_low hc ω hy) W

end BModel

end
