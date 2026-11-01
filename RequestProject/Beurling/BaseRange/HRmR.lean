module

public import RequestProject.Beurling.BaseRange.HRmNT
public import RequestProject.Beurling.BaseRange.HRmIdent
public import RequestProject.Beurling.Model.MarginH
public import RequestProject.Beurling.Noise.RML8GMain
public import RequestProject.Beurling.Queue6.NuBlock
public import RequestProject.Beurling.Queue6.RhoNoise
public import RequestProject.Beurling.Queue6.RhoLow

/-!
# The field `hRm` of `BModel.RestMarginH` (Proposition 5.38, Step 6(b), "Sum")

On `[2X₀, X₀^{1.01}]` (`t ≤ b`, on `Good(< t_b) ∩ NiceEv`):

  `(R_res T'(t) - m(t)) log t ≤ 10⁻¹² - E_BR`.

Proof (all in the small range):
* `R_res T' - m = R_res g`, `g = NT_pt - K_pt ν'`, `ν' = Bm - ρ̃` (`resid_eq_Rres`, exact);
* `NT_pt = 0` below `0.7 (X₀⁻)²` (no `τ`-near cofactors, `NTpt_small_zero`), so `g = -K_pt ν'`
  at every height read (`≤ t ≤ X₀^{1.01}`);
* Lemma 5.22 (`Queue6.rho_noise`, `rho_noise_low`, at the event time `t_b`, heights
  `y + 2H(y) ≤ 0.63 t ≤ b`): `|ν'| ≤ ν̄ ≤ ν̄_j` on the dyadic block `j` (`Queue6.nuB_le_nbQ`);
* Lemma 5.34, second bullet, for `G = K_pt ν'` (`KR.RML7G.gScaleBound_Kpt_tight`, Lemma 5.21(iii),
  `C'_S = 10`): `log t·|G(t)| ≤ A` and the scale bounds with `∑_u log(2u) Ḡ(u) ≤ A`,
  `A = 10 ∑_j (log 3v_j)² ν̄_j ≤ 10⁻²¹` (`Queue6.sum_nbQ_le`);
* Proposition 5.18 at the start `t` (`KR.TNP.wop_start`) and the kernel sum
  (`KR.RML6K.kernel_sum_le`): `log t·|R_res g(t)| ≤ (1 + 5.1 C_N) A ≤ 10⁻¹⁸` (`Rres_start_le`, the
  pointwise core of `KR.TNP.hG_loc`, copied at the centre with the range `x ≥ X₀^{1.01}`
  replaced by `x ≥ 2X₀`).

Main results: `BaseRange.hRm_R` (explicit noise hypothesis) and `BaseRange.hRm_ae` (a.s., from
`Queue6.rho_noise`, `Queue6.rho_noise_low`).
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction KR KR.TNP KR.Chain

namespace BaseRange

section Core

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **The pointwise core of Lemma 5.34, second bullet** (from `KR.TNP.hG_loc`): at a start
`y ≥ X₀⁻` within the horizon, with `log y·|G(y)| ≤ A` and scale bounds `Ḡ(u)` of `|G|` on the
windows of the levels with `∑_u log(2u) Ḡ(u) ≤ A`, `log y·|R_res G(y)| ≤ (1 + 5.1 C_N) A`. -/
theorem Rres_start_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {lam0 X0 : ℝ}
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) (G : ℝ → ℝ) (hGm : Measurable G)
    {y A : ℝ} (hy : X0m ≤ y) (hXmZ : X0m ≤ Z) (hyZ : 2 * y / X0m ≤ Z) (h18 : 18 * y ≤ Z ^ 2)
    {N K : ℕ} (hN : y < X0 * 2 ^ N / 4) (hK : √(2 * y) ≤ Pk X0m K) {s0 : ℝ → ℝ}
    (hX0s : EtaX0SumLoc P H X0m X0 (dyScales X0 y N) s0 y) (Gb : ℝ → ℝ)
    (hGy : Real.log y * |G y| ≤ A)
    (hGb : ∀ u ∈ dyScales X0 y N, 0 ≤ Gb u ∧ ∀ n ∈ NW P y u, 2 ≤ n → ∀ t,
      |t - posn P.labelVal y n| ≤ 1.02 * H (posn P.labelVal y n) → |G t| ≤ Gb u)
    (hGS : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Gb u ≤ A) :
    Real.log y * |Rres P H tw X0m y G| ≤ (1 + 5.1 * CNt X0) * A := by
  obtain ⟨hX, hl, h2, h4, hX0⟩ := sizes h hX0e hX0m
  obtain ⟨hC0, -⟩ := CNt_bounds hl
  have hXm7 : (10 : ℝ) ^ 7 ≤ X0m := h.hbs.X0m_ge
  have hZ0 : 2500 ≤ Z := by norm_num at hXm7; linarith
  have hly0 : 0 < Real.log y := Real.log_pos (by norm_num at hXm7; linarith)
  have hA0 : 0 ≤ A := le_trans (mul_nonneg hly0.le (abs_nonneg _)) hGy
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := by
    intro p _; unfold BeurlingSystem.labelVal; exact hp2 _
  have hks := RML6K.kernel_sum_le (tw := tw) h.width hval2 (cover_levels hX0 hX h2 hN) hGm
    (fun u hu => (hGb u hu).1) (fun u hu => (hGb u hu).2)
  have hW := wop_start h hH hX0e hX0m hp2 ht htv hlam hlam1 hy hyZ hZ0 h18 hN hK hX0s
  have hsum : ∑ u ∈ dyScales X0 y N, Gb u * Wop P H tw X0m y u ≤
      5.1 * CNt X0 * A / Real.log y := by
    calc ∑ u ∈ dyScales X0 y N, Gb u * Wop P H tw X0m y u
        ≤ ∑ u ∈ dyScales X0 y N, Gb u * (5.1 * CNt X0 * Real.log (2 * u) / Real.log y) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hW u hu) (hGb u hu).1
      _ = 5.1 * CNt X0 * (∑ u ∈ dyScales X0 y N, Real.log (2 * u) * Gb u) / Real.log y := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun u _ => by ring
      _ ≤ 5.1 * CNt X0 * A / Real.log y := by
          apply div_le_div_of_nonneg_right _ hly0.le
          exact mul_le_mul_of_nonneg_left hGS (by positivity)
  have hR : |Rres P H tw X0m y G| ≤ |G y| + 5.1 * CNt X0 * A / Real.log y := by
    unfold Rres
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hks.trans hsum))
  have hGy' : |G y| ≤ A / Real.log y := by
    rw [le_div_iff₀ hly0, mul_comm]; exact hGy
  have hB : |Rres P H tw X0m y G| ≤ (1 + 5.1 * CNt X0) * A / Real.log y := by
    have : A / Real.log y + 5.1 * CNt X0 * A / Real.log y =
        (1 + 5.1 * CNt X0) * A / Real.log y := by ring
    linarith
  calc Real.log y * |Rres P H tw X0m y G|
      ≤ Real.log y * ((1 + 5.1 * CNt X0) * A / Real.log y) :=
        mul_le_mul_of_nonneg_left hB hly0.le
    _ = (1 + 5.1 * CNt X0) * A := by field_simp

end Core

open BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `X₀^{1.01} ≤ X₀²/8`. -/
lemma rpow101_le_sq {X : ℝ} (hX0 : 0 < X) (hX : 10 ^ 8 ≤ Real.log X) :
    X ^ (1.01 : ℝ) ≤ X ^ 2 / 8 := by
  have h8 : (8 : ℝ) ≤ X ^ (0.99 : ℝ) := by
    rw [Real.rpow_def_of_pos hX0]
    have := Real.add_one_le_exp (Real.log X * 0.99)
    nlinarith
  have e : X ^ (1.01 : ℝ) * X ^ (0.99 : ℝ) = X ^ 2 := by
    rw [← Real.rpow_add hX0]; norm_num
  have hp : 0 < X ^ (1.01 : ℝ) := Real.rpow_pos_of_pos hX0 _
  nlinarith

section Main

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 4000000 in
/-- **The field `hRm` of `RestMarginH`** (Proposition 5.38, Step 6(b), "Sum"), given Lemma 5.22
at the event time `T ≥ b` (`|ρ̃ - Bm| ≤ ν̄` at `X₀⁻ ≤ y`, `y + 2H(y) ≤ T`). -/
theorem hRm_R {ω : JitterΩ} {b T : ℝ} (hb : (X₀ : ℝ) ≤ b) (hbT : b ≤ T)
    (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀)
    (x0s : KR.X0S.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) X₀ (Zc X₀ b) (1 / 1000) (1 / 1000)
      (hbsEps X₀) θ (b + Queue6.Hc X₀ b))
    (hnoise : ∀ y : ℝ, Xm X₀ ≤ y → y + 2 * Queue6.Hc X₀ y ≤ T →
      |rhoT θ X₀ ω y - Margin.Bavg (Queue6.Hc X₀ y) (marginM θ X₀ ω) y| ≤ Queue6.nuB X₀ y) :
    ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
          (fun s => TcR θ X₀ ω (jzX X₀) s + (jzX X₀) * ind X₀ s) - marginM θ X₀ ω t) *
        Real.log t ≤ 1 / 10 ^ 12 - EBRc := by
  intro t ht2 ht1 htb
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hO := opR hc hev hbs hN.2.1 hX1
  have hP := hT.width
  have hXm0 : 0 < Xm X₀ := hP.X0m_pos
  have hX0e : Xm X₀ = (X₀ : ℝ) - Queue6.Hc X₀ X₀ / 2 := by
    unfold Xm Queue6.Hc; rw [max_self]
  have hHpos := KR.WidthReal.Hc_pos hX (X₀ := X₀)
  have hXmX : Xm X₀ ≤ X₀ := by rw [hX0e]; linarith [hHpos (X₀ : ℝ)]
  obtain ⟨-, -, h2, -, hX0p⟩ := sizes hT hX0e hXmX
  have hp2 := KR.Chain.p_ge_two_of hT (Xm_le_Zc' hc b)
  obtain ⟨htw, htv⟩ := dec_R hT
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := Zc_facts hc hb
  have hXm7 : (10 : ℝ) ^ 7 ≤ Xm X₀ := hT.hbs.X0m_ge
  have htsm : Queue6.Hc X₀ t ≤ t / 10 := hP.small t (by linarith)
  have hHtb : Queue6.Hc X₀ t ≤ Queue6.Hc X₀ b := KR.WidthReal.Hc_mono hX htb
  have htXm : Xm X₀ ≤ t := by linarith
  -- the small range: `t < 0.7 (X₀⁻)²`
  have hsq := rpow101_le_sq hX0p hX
  have ht07 : t < 0.7 * Xm X₀ ^ 2 := by nlinarith
  -- the residual
  rw [resid_eq_Rres hc hev hO hP t]
  set F : KR.Ops.LocInt := KR.Ops.Bo hO (mL θ X₀ hO) - ρLd θ X₀ ω with hFdef
  have hFm : Measurable (F : ℝ → ℝ) :=
    ((LMb.Bo hO (LMb_mL hc hev hO)).sub (LMb_ρLd hc hev ω)).2
  have hFe : ∀ s, (F : ℝ → ℝ) s =
      Margin.Bavg (Queue6.Hc X₀ s) (marginM θ X₀ ω) s - rhoT θ X₀ ω s := by
    intro s
    show Margin.Bavg (Queue6.Hc X₀ s) (mL θ X₀ hO : ℝ → ℝ) s - (ρLd θ X₀ ω : ℝ → ℝ) s = _
    rw [mL_coe hc hev hO, ρLd_coe hc hev ω]
  -- `g = -K_pt F` below `t`
  have hge : ∀ s, s ≤ t → (gR θ X₀ hO : ℝ → ℝ) s =
      -Sharp.Kpt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) (F : ℝ → ℝ) s := by
    intro s hs
    show (NTptLd θ X₀ ω : ℝ → ℝ) s - Sharp.Kpt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀)
      (F : ℝ → ℝ) s = _
    rw [NTptLd_coe hc hev ω, NTpt_small_zero hc hev hT (by linarith), zero_sub]
  -- the block bounds of `F`
  set J := Jc X₀ t
  have hJ : t + Queue6.Hc X₀ t / 2 ≤ Xm X₀ * 2 ^ J := Jc_spec hXm0 t
  have hFb : ∀ j < J, ∀ s, Xm X₀ * 2 ^ j ≤ s → s < 2 * (Xm X₀ * 2 ^ j) →
      s ≤ (t + Queue6.Hc X₀ t / 2) / 2 → |(F : ℝ → ℝ) s| ≤ Queue6.nbQ X₀ j := by
    intro j _ s hs1 hs2 hs3
    have hj1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hsX : Xm X₀ ≤ s := le_trans (by nlinarith) hs1
    have hss : Queue6.Hc X₀ s ≤ s / 10 := hP.small s (by linarith)
    have hsT : s + 2 * Queue6.Hc X₀ s ≤ T := by linarith
    rw [hFe, abs_sub_comm]
    exact (hnoise s hsX hsT).trans (Queue6.nuB_le_nbQ hc hsX ⟨hs2, Or.inr hs1⟩)
  -- Lemma 5.34, second bullet, for `G = K_pt F`
  have hwin : ∀ y, t - Queue6.Hc X₀ t / 2 ≤ y → y ≤ t + Queue6.Hc X₀ t / 2 →
      2 * y / Xm X₀ ≤ Zc X₀ b := by
    intro y _ hy2
    refine le_trans ?_ hZ4
    apply div_le_div_of_nonneg_right _ hXm0.le
    linarith [hHpos t]
  have hGS := KR.RML7G.gScaleBound_Kpt_tight (tw := twR θ X₀ ω) hT hO (X0 := (X₀ : ℝ))
    (by linarith) (fun y => (NKc X₀ y).1) (F : ℝ → ℝ) hJ (by linarith) hwin
    (fun j => Queue6.nbQ X₀ j) (fun j => Queue6.nbQ_nonneg hc j) hFb
  obtain ⟨hG1, hG2, hG3⟩ := hGS t (by linarith [hHpos t]) (by linarith [hHpos t])
  set A := 10 * ∑ j ∈ range J, Real.log (3 * (Xm X₀ * 2 ^ j)) ^ 2 * Queue6.nbQ X₀ j
  have hA : A ≤ 10 / 10 ^ 22 := by
    have := Queue6.sum_nbQ_le hc J
    simp only [A]; linarith
  -- transfer to `g`
  have hgt : Real.log t * |(gR θ X₀ hO : ℝ → ℝ) t| ≤ A := by
    rw [hge t le_rfl, abs_neg]; exact hG1
  have hgb : ∀ u ∈ dyScales (X₀ : ℝ) t (NKc X₀ t).1,
      0 ≤ (fun u => ∑ j ∈ range J, Queue6.nbQ X₀ j * RML8G.Om8 (Xm X₀ * 2 ^ j) u) u ∧
      ∀ n ∈ NW (PR θ X₀ ω) t u, 2 ≤ n → ∀ s,
        |s - posn (PR θ X₀ ω).labelVal t n| ≤
          1.02 * Queue6.Hc X₀ (posn (PR θ X₀ ω).labelVal t n) →
        |(gR θ X₀ hO : ℝ → ℝ) s| ≤
          (fun u => ∑ j ∈ range J, Queue6.nbQ X₀ j * RML8G.Om8 (Xm X₀ * 2 ^ j) u) u := by
    intro u hu
    refine ⟨(hG2 u hu).1, fun n hn hn2 s hs => ?_⟩
    have hV2 := KR.Ops.Vl_ge_two (P := PR θ X₀ ω) hp2 hn2
    have hpos : posn (PR θ X₀ ω).labelVal t n ≤ t / 2 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hV2
    have hpos0 : 0 ≤ posn (PR θ X₀ ω).labelVal t n :=
      div_nonneg (by linarith) (by linarith)
    have hHn : Queue6.Hc X₀ (posn (PR θ X₀ ω).labelVal t n) ≤ t / 10 := by
      rcases le_or_gt (Xm X₀ / 2) (posn (PR θ X₀ ω).labelVal t n) with h' | h'
      · have := hP.small _ h'; linarith
      · have := hO.low _ h'; linarith
    have hst : s ≤ t := by linarith [(abs_le.mp hs).2]
    rw [hge s hst, abs_neg]
    exact (hG2 u hu).2 n hn hn2 s hs
  have hlam := KR.WidthReal.Hc_Xm_half_le hX (X₀ := X₀)
  have hcore := Rres_start_le hT hlam hX0e hXmX hp2 htw htv (lam0 := lamH)
    (by norm_num [epsH, lamH]) (by norm_num [lamH]) _ (LMb_gR hc hev hO).2 htXm hZ1
    (hwin t (by linarith [hHpos t]) (by linarith [hHpos t])) (by nlinarith [hHpos t, hHpos b])
    (NKc_spec hc t).2.1 (NKc_spec hc t).2.2
    (x0s.etaX0SumLoc_of dyScales_dyadic (by linarith [hHpos b])) _ hgt hgb hG3
  obtain ⟨hC0, hC⟩ := CNt_bounds (X0 := (X₀ : ℝ)) (by linarith)
  have hE := BModel.RML10.EBRc_tiny
  have hlt : 0 < Real.log t := Real.log_pos (by norm_num at hXm7; linarith)
  have hA0 : 0 ≤ A := le_trans (mul_nonneg hlt.le (abs_nonneg _)) hgt
  have hfin : (1 + 5.1 * CNt (X₀ : ℝ)) * A ≤ (1 + 5.1 * 158) * (10 / 10 ^ 22) :=
    mul_le_mul (by linarith) hA hA0 (by norm_num)
  calc Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t (gR θ X₀ hO : ℝ → ℝ) *
        Real.log t ≤ Real.log t * |Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
          (gR θ X₀ hO : ℝ → ℝ)| := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hlt.le
    _ ≤ (1 + 5.1 * CNt (X₀ : ℝ)) * A := hcore
    _ ≤ 1 / 10 ^ 12 - EBRc := by
        have : (1 + 5.1 * 158) * (10 / 10 ^ 22 : ℝ) ≤ 1 / 10 ^ 12 - 1 / 10 ^ 30 := by
          norm_num
        linarith

/-- **The field `hRm` of `RestMarginH`, almost surely**: a.s., at every event time `t`, on
`Good(< t) ∩ NiceEv`, for every `X₀ ≤ b ≤ t` (with the `HBS` of the realised system at the
horizon `Zc X₀ b`), the bound of `RestMarginH.hRm` holds. Lemma 5.22 enters through
`Queue6.rho_noise` (`y ≥ X₀`) and `Queue6.rho_noise_low` (`X₀⁻ ≤ y < X₀`) at time `t`. -/
theorem hRm_ae : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ Queue6.G0 θ X₀ (Queue6.e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → ∀ b : ℝ, (X₀ : ℝ) ≤ b → b ≤ t →
    (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀) →
    10 ^ 8 + 1 ≤ Real.log X₀ →
    ∀ s, 2 * (X₀ : ℝ) ≤ s → s ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → s ≤ b →
      (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) s
          (fun r => TcR θ X₀ ω (jzX X₀) r + (jzX X₀) * ind X₀ r) - marginM θ X₀ ω s) *
        Real.log s ≤ 1 / 10 ^ 12 - EBRc := by
  filter_upwards [Queue6.rho_noise hc hev, Queue6.rho_noise_low hc hev] with ω h1 h2
  intro t hG hN b hb hbt hbs hX1
  have x0s := Queue6.x0sHyp_G0 (Queue6.e3Family θ X₀) hc hev hG hN hbt hbs (Zc_facts hc hb).1 le_rfl
    (by linarith [hc.hθ.2])
  refine hRm_R hc hev hb hbt hN hbs hX1 x0s fun y hy hyt => ?_
  rcases le_or_gt (X₀ : ℝ) y with hyX | hyX
  · exact h1 t hG hN y hyX hyt
  · exact h2 t hG hN y hy hyX hyt

end Main

end BaseRange

end
