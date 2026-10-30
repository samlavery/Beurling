module

public import RequestProject.Beurling.Model.WinAtR
public import RequestProject.Beurling.Model.RestMargin10
public import RequestProject.Beurling.Noise.RML12Sz
public import RequestProject.Beurling.Noise.RML12HJR
public import RequestProject.Beurling.Noise.RML12M
public import RequestProject.Beurling.Queue6.ShortRecipQ

/-!
# Inputs of §5's RML12 lemmas from the Model

* `JcBound_c` : `Jc` is least (`RML12.JcBound`), so the sums `SK`, `Gsum` stay below the
  (H_BS) horizon;
* `srl_c` : Lemma 5.29 (`ShortRecipLow`) at heights `s ≤ 1.1 b`, `b ≥ X₀^{1.01}`, on `Good(< t)`
  (`Queue6.shortRecipLow_G0`);
* `T524_mono`, `hjA_c` : `j_{X₀} ≤ e^{-59}` on `[X₀^{1.01}, b]` (`RML12.hj_all` with its
  per-start inputs: horizons, Theorem 5.24 at `2(y/X₀)^{0.55}` via `hT_at`, `srl_c`);
* `MfH` : the harmonic local bound `m*(z) = 2 + 2 ∑_{n ≤ 2(z⁺ + 3H(z))/X₀⁻} 1/n` of the margin
  density on `[z ± 3H(z)]` (`hmH`; `compDen ≤ 2 ∑_{n ≤ x/X₀⁻} 1/n` by `compDen_eq`, `ρ̃ ≤ 2`),
  monotone in `z` and independent of `b`; under (H_BS) it is `≤ 4 + 2 log(2(z+3H)/X₀⁻)`
  (`RML12M.harmBound_le`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Queue6 KR KR.TNP Finset

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀)
include hc

/-- `6 X₀ ≤ X₀^{1.01}`. -/
lemma six_X0_le_X1 : 6 * (X₀ : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) := by
  have hX := hc.hX
  have hXp : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
  rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add hXp, Real.rpow_one]
  have : (6 : ℝ) ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := by
    rw [Real.rpow_def_of_pos hXp]
    have := Real.add_one_le_exp (Real.log X₀ * 0.01)
    nlinarith
  nlinarith

/-- **`Jc` is least** (`RML12.JcBound`). -/
theorem JcBound_c (b : ℝ) : RML12.JcBound X₀ b := by
  intro t ht _
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have h := Jc_le hXm t
  have hXmX := Xm_le_X0 hc
  have h6 := six_X0_le_X1 hc
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hH := (KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) t).le
  have : Xm X₀ ≤ 2 * (t + Queue6.Hc X₀ t / 2) := by linarith
  rwa [max_eq_right this] at h

/-- **Lemma 5.29 at heights `s ≤ 1.1 b`** on `Good(< t)`, `X₀^{1.01} ≤ b ≤ t`. -/
theorem srl_c (hev : Even X₀) {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) {b s : ℝ} (hbt : b ≤ t) (hb : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ b)
    (hs : s ≤ 1.1 * b) : KR.RML9.ShortRecipLow (PR θ X₀ ω) X₀ s := by
  have hX0p : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
  have h6 := six_X0_le_X1 hc
  have hXb : (10 : ℝ) ^ 8 ≤ X₀ := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log hX0p]; exact Real.exp_le_exp.mpr hc.hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  refine Queue6.shortRecipLow_G0 (e3Family θ X₀) hc hev hG hN ?_
  have h1 : 2.1 * (s / X₀) ≤ 2.31 * b / X₀ := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by linarith) hX0p.le
  have h2 : 2.31 * b / X₀ ≤ b / 1000 := by
    rw [div_le_div_iff₀ hX0p (by norm_num)]; nlinarith
  linarith

omit hc in
/-- Theorem 5.24's conclusion is downward closed in the height. -/
lemma T524_mono {P : BeurlingSystem} {y y' : ℝ} (h : LocalPNT.Theorem524Concl P X₀ y')
    (hy : y ≤ y') : LocalPNT.Theorem524Concl P X₀ y :=
  ⟨fun v h1 h2 => h.1 v h1 (h2.trans hy), fun v η h1 h2 h3 h4 => h.2 v η h1 h2 h3 (h4.trans hy)⟩

/-- `2(y/X₀)^{0.55} ≤ y/2` for `y ≥ X₀`. -/
lemma pow55_le {y : ℝ} (hy : (X₀ : ℝ) ≤ y) : 2 * (y / X₀) ^ (0.55 : ℝ) ≤ y / 2 := by
  have hX := hc.hX
  have hXp : (0 : ℝ) < X₀ := by linarith [one_lt_X0 hc]
  have hy0 : 0 < y := by linarith
  have hL : Real.log X₀ ≤ Real.log y := Real.log_le_log hXp hy
  have hp : (y / X₀) ^ (0.55 : ℝ) = Real.exp (0.55 * (Real.log y - Real.log X₀)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div hy0.ne' hXp.ne']; ring_nf
  rw [hp]
  have e : Real.exp (Real.log y) = Real.exp (0.55 * (Real.log y - Real.log X₀)) *
      Real.exp (0.45 * Real.log y + 0.55 * Real.log X₀) := by rw [← Real.exp_add]; ring_nf
  rw [Real.exp_log hy0] at e
  have h5 : (4 : ℝ) ≤ Real.exp (0.45 * Real.log y + 0.55 * Real.log X₀) := by
    have := Real.add_one_le_exp (0.45 * Real.log y + 0.55 * Real.log X₀); nlinarith
  have := Real.exp_pos (0.55 * (Real.log y - Real.log X₀))
  nlinarith

variable (hev : Even X₀)
include hev

set_option maxHeartbeats 2000000 in
/-- **`j_{X₀} ≤ e^{-59}` on `[X₀^{1.01}, b]`** (`RML12.hj_all`), on `Good(< t)`, `b ≤ t`, given
(huxley). -/
theorem hjA_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t) (hbt : b ≤ t) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) (hH : BaseRange.HuxleyFrom (X₀ : ℝ)) :
    ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b →
      0 ≤ jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) x ∧
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) x ≤ Real.exp (-59) := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n :=
    fun n hn => mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have hZ := Zc_facts hc hb
  have hX1' := one_lt_X0 hc
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hHb := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
  -- the global facts (as in `g1Sec5_c`)
  have hX0e : Xm X₀ = X₀ - Queue6.Hc X₀ X₀ / 2 := by unfold Xm Queue6.Hc; rw [max_self]
  have hH1 : 1 ≤ Queue6.Hc X₀ X₀ :=
    KR.WidthReal.capH_one_le hX le_rfl |>.trans (by unfold Queue6.Hc; rw [max_self])
  have hH8 : Queue6.Hc X₀ X₀ ≤ (X₀ : ℝ) ^ (1 / 8 : ℝ) := by
    unfold Queue6.Hc; rw [max_self]
    exact InitialRange.capH_le_rpow (Nat.cast_nonneg _) hX le_rfl
  have hδ : Queue6.Hc X₀ X₀ / X₀ ≤ 1 / 1000 := by
    have h := Queue6.capH_le_div hX (le_refl (X₀ : ℝ))
    unfold Queue6.Hc; rw [max_self, div_le_iff₀ hXp]
    linarith
  have hδs : 200000 * (Queue6.Hc X₀ X₀ / X₀) ≤ Real.exp (-61) := by
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
        have e : Real.exp 13 = Real.exp 1 ^ 13 := by
          rw [← Real.exp_nat_mul]; norm_num
        have h := Real.exp_one_gt_d9
        rw [e]
        calc (200000 : ℝ) ≤ 2.7182818283 ^ 13 := by norm_num
          _ ≤ Real.exp 1 ^ 13 := by gcongr
      have h3 : Real.exp (74 : ℝ) ≤ Real.exp (Real.log X₀ / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.exp_pos 61]
    have hq : Queue6.Hc X₀ X₀ / X₀ ≤ 1 / (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
      rw [div_le_div_iff₀ hXp hs0, one_mul]
      nlinarith
    have h61 : 200000 * (1 / (X₀ : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.exp (-61) := by
      rw [Real.exp_neg, mul_one_div, div_le_iff₀ hs0]
      have := Real.exp_pos 61
      rw [inv_mul_eq_div, le_div_iff₀ this]
      linarith
    linarith
  refine RML12.hj_all hc hev hT hX0e hH1 hδ hδs hH8 (KR.Chain.p_ge_two_of hT (Xm_le_Zc' hc b))
    (KR.Chain.dec_R hT).1 (KR.Chain.dec_R hT).2 (BaseRange.jzX_le hX hH) hZ.2.1 ?_
  intro x hx hxb y hy
  have hHx : Queue6.Hc X₀ x ≤ Queue6.Hc X₀ b := KR.WidthReal.Hc_mono hX hxb
  have hHx0 := (KR.WidthReal.Hc_pos hX (X₀ := X₀) x).le
  have hxX : 2 * (X₀ : ℝ) ≤ x := by linarith [six_X0_le_X1 hc]
  have hHx4 : Queue6.Hc X₀ x ≤ x / 40 := by
    unfold Queue6.Hc; rw [max_eq_left (by linarith)]
    exact KR.WidthReal.capH_le_tenth hX (by linarith)
  have hyb : y ≤ b + Queue6.Hc X₀ b := by linarith [hy.2]
  have hyX : (X₀ : ℝ) ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have hHb40 : Queue6.Hc X₀ b ≤ b / 40 := by
    unfold Queue6.Hc; rw [max_eq_left hb]; exact KR.WidthReal.capH_le_tenth hX hb
  have hx6 := six_X0_le_X1 hc
  have hy2 : 2 * (X₀ : ℝ) ≤ y := by linarith [hy.1]
  refine ⟨le_trans (div_le_div_of_nonneg_right (by linarith) hXm0.le) hZ.2.2.2,
    le_trans (by linarith) hZ.2.2.1, ?_, srl_c hc hev hG hN hbt (hx.trans hxb) (by linarith)⟩
  -- Theorem 5.24 at `2(y/X₀)^{0.55} ≤ max(·, X₀) ≤ y/2`
  have hp := pow55_le hc hyX
  have hp0 : 0 ≤ 2 * (y / X₀) ^ (0.55 : ℝ) := by positivity
  refine T524_mono (hT_at hc hev hb hbt hG.1 hE1 hN (zc := max (2 * (y / X₀) ^ (0.55 : ℝ)) X₀)
    (le_max_right _ _) (max_le (by linarith) (by linarith)) ?_) (le_max_left _ _)
  intro u hu huz
  have hu2 : u ≤ y / 2 := huz.trans (max_le hp (by linarith))
  have hl : Real.log u ≤ Real.log b := Real.log_le_log (by linarith) (by linarith)
  have hlb : 26 * Real.log b + 2 < b / 4 := by
    have hb0 : 0 < b := by linarith
    have h1 := Real.add_one_le_exp (Real.log b / 2)
    have h2 : Real.exp (Real.log b / 2) ^ 2 = b := by
      rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ (by norm_num),
        Real.exp_log hb0]
    have hLb : 10 ^ 8 ≤ Real.log b := by
      have := Real.log_le_log hXp hb; linarith
    nlinarith
  have : (t : ℝ) ≥ b := hbt
  linarith

/-! ### The harmonic local bound of `m` -/

variable (θ X₀) in
/-- **The local bound `m*(z)`**: `2 + 2 ∑_{n ∈ 𝒩, n ≤ 2(z⁺ + 3H(z))/X₀⁻} 1/n`. -/
noncomputable def MfH (ω : JitterΩ) (z : ℝ) : ℝ :=
  2 + 2 * ∑ e ∈ (PR θ X₀ ω).elems (2 * (max z 0 + 3 * Queue6.Hc X₀ z) / Xm X₀),
    1 / (PR θ X₀ ω).val e

lemma MfH_nonneg (ω : JitterΩ) (z : ℝ) : 0 ≤ MfH θ X₀ ω z := by
  unfold MfH
  have : 0 ≤ ∑ e ∈ (PR θ X₀ ω).elems (2 * (max z 0 + 3 * Queue6.Hc X₀ z) / Xm X₀),
      1 / (PR θ X₀ ω).val e :=
    Finset.sum_nonneg fun e _ => (one_div_pos.mpr ((PR θ X₀ ω).val_pos e)).le
  linarith

lemma MfH_mono (ω : JitterΩ) : Monotone (MfH θ X₀ ω) := by
  intro z z' hzz
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hH := KR.WidthReal.Hc_mono hc.hX hzz
  have hX : 2 * (max z 0 + 3 * Queue6.Hc X₀ z) / Xm X₀ ≤
      2 * (max z' 0 + 3 * Queue6.Hc X₀ z') / Xm X₀ :=
    div_le_div_of_nonneg_right (by
      have := max_le_max hzz (le_refl (0 : ℝ)); linarith) hXm.le
  exact RML12M.harmBound_mono (PR θ X₀ ω) hX

/-- `c(x) ≤ 2 ∑_{n ≤ x/X₀⁻} 1/n` (`compDen_eq`, `ρ̃ ≤ 2`). -/
lemma compDen_le_harm (ω : JitterΩ) (x : ℝ) :
    (compDen θ X₀ ω x).toReal ≤ 2 * ∑ e ∈ (PR θ X₀ ω).elems (x / Xm X₀),
      1 / (PR θ X₀ ω).val e := by
  classical
  have h := realisedOK_Mcl hc ω
  set P := PR θ X₀ ω
  set F := (P.elems (x / Xm X₀)).filter (fun f => 2 ≤ BeurlingSystem.iota f)
  have hle : compDen θ X₀ ω x ≤ ∑ f ∈ F, 2 * ENNReal.ofReal (P.val f)⁻¹ := by
    rw [compDen_eq hc h x]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_left ((r_le h f x).trans
      (bw_sum_le hc hev ω _)) _
  have e : ∑ f ∈ F, 2 * ENNReal.ofReal (P.val f)⁻¹ =
      ENNReal.ofReal (∑ f ∈ F, 2 * (P.val f)⁻¹) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun f _ => by
      have := P.val_pos f; positivity)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e] at hle
  have h1 := ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg fun f _ => by
    have := P.val_pos f; positivity) hle
  have h2 : ∑ f ∈ F, 2 * (P.val f)⁻¹ ≤ ∑ f ∈ P.elems (x / Xm X₀), 2 * (P.val f)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun f _ _ => by
      have := P.val_pos f; positivity
  rw [Finset.mul_sum]
  refine h1.trans (h2.trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun f _ => by rw [one_div]

/-- **The input `hm` of `RML12M.hS2sp_12`, `hS2sm_12`** at `Mf = m*` (`MfH`), at every `z`. -/
theorem hmH (ω : JitterΩ) (z : ℝ) :
    IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z),
        |marginM θ X₀ ω x| ≤ MfH θ X₀ ω z := by
  have hX := hc.hX
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  have hH := (KR.WidthReal.Hc_pos hX (X₀ := X₀) z).le
  have hle : z - 3 * Queue6.Hc X₀ z ≤ z + 3 * Queue6.Hc X₀ z := by linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp (marginM_ii hc hev ω hle),
    fun x hx => ?_⟩
  have hc1 := compDen_le_harm hc hev ω x
  have h0 : 0 ≤ (compDen θ X₀ ω x).toReal := ENNReal.toReal_nonneg
  have hT := abs_le.mp (TpCont_abs_le hc ω x)
  have hsub : ∑ e ∈ (PR θ X₀ ω).elems (x / Xm X₀), 1 / (PR θ X₀ ω).val e ≤
      ∑ e ∈ (PR θ X₀ ω).elems (2 * (max z 0 + 3 * Queue6.Hc X₀ z) / Xm X₀),
        1 / (PR θ X₀ ω).val e := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ((PR θ X₀ ω).elems_mono ?_)
      (fun e _ _ => (one_div_pos.mpr ((PR θ X₀ ω).val_pos e)).le)
    refine div_le_div_of_nonneg_right ?_ hXm.le
    have := hx.2
    have := le_max_left z 0
    have := le_max_right z 0
    linarith
  unfold MfH marginM
  rw [abs_le]; constructor <;> linarith [hT.1, hT.2]

end BModel

end
