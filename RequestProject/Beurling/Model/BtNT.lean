module

public import RequestProject.Beurling.Model.NTEta
public import RequestProject.Beurling.Model.MarginMine
public import RequestProject.Beurling.Noise.RML7Eta

/-!
# Step 6(a) of Proposition 5.38: `B_t = ϑ/H + B NT_pt` and the fields `hBt`, `hsη`, `intm`

With `K_pt = Ko` and `B = Bo` the window average (`KR.Ops.Kop_apply`, `Bop_apply`), the
canonical `B_t = ρ̃ + ν + NT - B m` of `Btc` is `ϑ/H + B NT_pt` (`Btc_eq`): `ν` is the residual of
the margin identity, and `T_c + J - K_pt ρ̃ - m = NT_pt` (`marginM_eq`). By eq. (NT)
(`NTpt_abs_le_eta`, 04b-identity.tex) `|NT_pt| ≤ 2η` with the `τ`-near `η`, and by Lemma 5.20,
last claim (`KR.TNP.logy_eta_le`), `log z · η(z) ≤ 831200 Φ₂(X₀⁻/2)` uniformly. So, with

  `η_B(t) := |B NT_pt(t)|/54`,   `s_η := (2.02/54) · 831200 Φ₂(X₀⁻/2)`,

`hBt` (`|B_t| ≤ 54 η_B + 6/H`, from `|ϑ| ≤ 6`) holds by definition (`hBt_c`) and `hsη`
(`log t · η_B(t) ≤ s_η`) is `hsη_c`. `intm_c` is the window integrability of `m`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `|B f(t)| ≤ M` if `|f| ≤ M` on the window (no integrability needed). -/
lemma abs_Bavg_le {h t M : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hf : ∀ z, t - h / 2 ≤ z → z ≤ t + h / 2 → |f z| ≤ M) : |Margin.Bavg h f t| ≤ M := by
  unfold Margin.Bavg
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf t (by linarith) (by linarith))
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := t - h / 2) (b := t + h / 2)
    (C := M) (f := f) (fun z hz => by
      rw [Set.uIoc_of_le (by linarith)] at hz
      exact hf z hz.1.le hz.2)
  rw [abs_mul, abs_inv, abs_of_pos hh]
  rw [Real.norm_eq_abs, show t + h / 2 - (t - h / 2) = h by ring, abs_of_pos hh] at hI
  rw [inv_mul_le_iff₀ hh]
  linarith

variable (θ X₀) in
/-- **`η` of Step 6(a)**: `η_B(t) = |B NT_pt(t)|/54`. -/
noncomputable def ηB (ω : JitterΩ) (t : ℝ) : ℝ :=
  |Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t| / 54

variable (X₀) in
/-- `s_η = (2.02/54) · 831200 Φ₂(X₀⁻/2)`. -/
noncomputable def sηB : ℝ :=
  2.02 / 54 * (831200 * KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2))

section

variable (hc : Cond θ X₀)
include hc

/-- **The field `intm`**: `m` is integrable on every window. -/
theorem intm_c (hev : Even X₀) (ω : JitterΩ) (t : ℝ) :
    IntervalIntegrable (marginM θ X₀ ω) volume (t - Queue6.Hc X₀ t / 2)
      (t + Queue6.Hc X₀ t / 2) := by
  have hH := KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) t
  have hmi : ∀ p q : ℝ, p ≤ q → IntervalIntegrable (marginM θ X₀ ω) volume p (max q X₀) :=
    fun p q hpq => (integral_TpCont hc ω (hpq.trans (le_max_left _ _))
      (le_max_right _ _)).1.sub (compR_intervalIntegrable hc hev ω
        (hpq.trans (le_max_left _ _)))
  have h1 : t - Queue6.Hc X₀ t / 2 ≤ t + Queue6.Hc X₀ t / 2 := by linarith
  have h2 : t + Queue6.Hc X₀ t / 2 ≤ max (t + Queue6.Hc X₀ t / 2) (X₀ : ℝ) := le_max_left _ _
  refine (hmi _ _ h1).mono_set ?_
  rw [Set.uIcc_of_le h1, Set.uIcc_of_le (h1.trans h2)]
  exact Set.Icc_subset_Icc le_rfl h2

/-- **`B_t = ϑ/H + B NT_pt`** (Step 6(a) of Proposition 5.38, with eq. (Ttilde)): `K_pt = Ko`,
`B = Bo`, and `T_c + J - K_pt ρ̃ - m = NT_pt`. -/
theorem Btc_eq (hev : Even X₀) (ω : JitterΩ)
    (hO₀ : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) (ρL TcL vtH NT : KR.Ops.LocInt)
    (hρL : (ρL : ℝ → ℝ) = rhoT θ X₀ ω) (hTcL : (TcL : ℝ → ℝ) = TcR θ X₀ ω (jzX X₀)) (t : ℝ) :
    Btc θ X₀ ω hO₀ ρL TcL vtH NT t =
      (vtH : ℝ → ℝ) t + Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t := by
  set H := Queue6.Hc X₀ t with hH
  have hH0 : 0 < H := KR.WidthReal.Hc_pos hc.hX t
  set a := t - H / 2
  set c := t + H / 2
  have hTJ : IntervalIntegrable (((TcL + JL (jzX X₀) X₀ : KR.Ops.LocInt)) : ℝ → ℝ) volume a c :=
    (TcL + JL (jzX X₀) X₀).2 a c
  have hK : IntervalIntegrable ((KR.Ops.Ko (tw := twR θ X₀ ω) hO₀ ρL : KR.Ops.LocInt) :
      ℝ → ℝ) volume a c := (KR.Ops.Ko (tw := twR θ X₀ ω) hO₀ ρL).2 a c
  have hm := intm_c hc hev ω t
  unfold Btc nuRes
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply,
    KR.Ops.Bop_apply]
  rw [hρL]
  have e : ∀ z, ((TcL + JL (jzX X₀) X₀ : KR.Ops.LocInt) : ℝ → ℝ) z -
      (KR.Ops.Ko (tw := twR θ X₀ ω) hO₀ ρL : ℝ → ℝ) z - marginM θ X₀ ω z = NTpt θ X₀ ω z := by
    intro z
    rw [marginM_eq]
    simp only [AddSubgroup.coe_add, Pi.add_apply, KR.Ops.Kop_apply, hTcL, hρL]
    unfold JL
    unfold TcR KptR
    simp only
    ring
  have hB : Margin.Bavg H (((TcL + JL (jzX X₀) X₀ : KR.Ops.LocInt)) : ℝ → ℝ) t -
      Margin.Bavg H (KR.Ops.Ko (tw := twR θ X₀ ω) hO₀ ρL : ℝ → ℝ) t -
      Margin.Bavg H (marginM θ X₀ ω) t = Margin.Bavg H (NTpt θ X₀ ω) t := by
    unfold Margin.Bavg
    rw [← mul_sub, ← mul_sub, ← intervalIntegral.integral_sub hTJ hK,
      ← intervalIntegral.integral_sub (hTJ.sub hK) hm]
    congr 1
    exact intervalIntegral.integral_congr fun z _ => e z
  rw [← hB]
  simp only [AddSubgroup.coe_add]
  ring

/-- **The field `hBt`** at `η = η_B`: `|B_t| ≤ 54 η_B + 6/H`, from `|ϑ| ≤ 6`. -/
theorem hBt_c (hev : Even X₀) (ω : JitterΩ)
    (hO₀ : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) (ρL TcL vtH NT : KR.Ops.LocInt)
    (hρL : (ρL : ℝ → ℝ) = rhoT θ X₀ ω) (hTcL : (TcL : ℝ → ℝ) = TcR θ X₀ ω (jzX X₀))
    {ϑ : ℝ → ℝ} (hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / Queue6.Hc X₀ z) {b : ℝ}
    (hϑ : ∀ x, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x → x ≤ b → |ϑ x| ≤ 6) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      |Btc θ X₀ ω hO₀ ρL TcL vtH NT t| ≤ 54 * ηB θ X₀ ω t + 6 / Queue6.Hc X₀ t := by
  intro t ht htb
  rw [Btc_eq hc hev ω hO₀ ρL TcL vtH NT hρL hTcL t, hvt]
  have hH0 : 0 < Queue6.Hc X₀ t := KR.WidthReal.Hc_pos hc.hX t
  have h1 : |ϑ t / Queue6.Hc X₀ t| ≤ 6 / Queue6.Hc X₀ t := by
    rw [abs_div, abs_of_pos hH0]
    exact div_le_div_of_nonneg_right (hϑ t ht htb) hH0.le
  unfold ηB
  have := abs_add_le (ϑ t / Queue6.Hc X₀ t) (Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The field `hsη`** at `η = η_B`, `s_η = sηB`: `log t · η_B(t) ≤ s_η` (eq. (NT) and
Lemma 5.20, last claim), given (H_BS) on `[1, Zc b]` (through `KR.TNP.Hyp`). -/
theorem hsη_c (hev : Even X₀) (ω : JitterΩ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10)) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b → Real.log t * ηB θ X₀ ω t ≤ sηB X₀ := by
  intro t ht htb
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hX1t : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) :=
    Real.self_le_rpow_of_one_le hX1.le (by norm_num)
  have htX : (X₀ : ℝ) ≤ t := hX1t.trans ht
  have hH0 : 0 < Queue6.Hc X₀ t := KR.WidthReal.Hc_pos hX t
  have hHt : Queue6.Hc X₀ t ≤ t / 40 := by
    unfold Queue6.Hc; rw [max_eq_left htX]
    exact KR.WidthReal.capH_le_tenth hX htX
  have hHb : Queue6.Hc X₀ t ≤ Queue6.Hc X₀ b := KR.WidthReal.Hc_mono hX htb
  have hZ := Zc_facts hc hb
  set S := 831200 * KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2) with hS
  have hS0 : 0 ≤ S := by
    have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
    have := KR.WidthReal.Hc_pos hX (X₀ := X₀) (Xm X₀ / 2)
    rw [hS]; unfold KR.TNP.Phi
    have : 0 ≤ Real.log (Xm X₀ / 2) + 2 := by
      have h2 : (1 : ℝ) ≤ Xm X₀ / 2 := by
        have := KR.WidthReal.Xm_ge hX (X₀ := X₀)
        have := KR.WidthReal.X0_ge hX (X₀ := X₀)
        linarith
      linarith [Real.log_nonneg h2]
    positivity
  have hLt : 10 ^ 8 ≤ Real.log t := hX.trans (Real.log_le_log hXp htX)
  -- the pointwise bound on the window
  have hpt : ∀ z, t - Queue6.Hc X₀ t / 2 ≤ z → z ≤ t + Queue6.Hc X₀ t / 2 →
      |NTpt θ X₀ ω z| ≤ 2.02 * S / Real.log t := by
    intro z hz1 hz2
    have hz0 : 0.98 * t ≤ z := by linarith
    have hz1' : (1 : ℝ) ≤ z := by linarith [KR.WidthReal.X0_ge hX (X₀ := X₀)]
    have hzb : 9 * z ≤ Zc X₀ b ^ 2 := by
      have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
      linarith [hZ.2.2.1]
    have hη := KR.TNP.logy_eta_le hT hz1' hZ.2.1 hzb
    have hN := NTpt_abs_le_eta hc hev ω z
    have hlz : 0.999 * Real.log t ≤ Real.log z := by
      have h1 : Real.log (0.98 * t) ≤ Real.log z := Real.log_le_log (by linarith) hz0
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have : -0.03 ≤ Real.log 0.98 := by
        have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.98 by norm_num)
        norm_num at this ⊢; linarith
      linarith
    have hlz0 : 0 < Real.log z := by linarith
    have hη' : KR.etaG (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (fun _ => 1) z ≤
        S / Real.log z := by
      rw [le_div_iff₀ hlz0, mul_comm]; exact hη
    have h3 : S / Real.log z ≤ 1.01 * S / Real.log t := by
      rw [div_le_div_iff₀ hlz0 (by linarith)]; nlinarith
    have e : 2 * (1.01 * S / Real.log t) = 2.02 * S / Real.log t := by ring
    linarith
  have hB := abs_Bavg_le hH0 hpt
  unfold ηB sηB
  rw [← hS]
  have hlt0 : 0 < Real.log t := by linarith
  rw [show Real.log t * (|Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t| / 54) =
    (Real.log t * |Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t|) / 54 by ring]
  have : Real.log t * |Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t| ≤ 2.02 * S := by
    calc Real.log t * |Margin.Bavg (Queue6.Hc X₀ t) (NTpt θ X₀ ω) t|
        ≤ Real.log t * (2.02 * S / Real.log t) := mul_le_mul_of_nonneg_left hB hlt0.le
      _ = 2.02 * S := by field_simp
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- `s_η ≤ 0.04 · 831200 e^{-200}` (`KR.TNP.sη_tiny`). -/
theorem sηB_tiny (ω : JitterΩ) {b : ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10)) :
    sηB X₀ ≤ 2.02 / 54 * (831200 * Real.exp (-200)) := by
  have := KR.TNP.sη_tiny hT (KR.WidthReal.Hc_Xm_half_le hc.hX)
  unfold sηB
  exact mul_le_mul_of_nonneg_left this (by norm_num)

end

end BModel

end
