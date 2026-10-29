module

public import RequestProject.Beurling.Model.TcLow
public import RequestProject.Beurling.Queue6.S2Err
public import RequestProject.Beurling.Queue6.S2Ep
public import RequestProject.Beurling.Noise.RML6BridgeLoc

/-!
# Model wiring, round 14: `NT_pt` bounded, canonical `η_V` and `B_t`, the Step 2 deviations

* `NTpt_abs_le` : `|NT_pt(y)| ≤ C(Y)` for `y ≤ Y` (`NT_pt = c - K_pt ρ̃ + K_𝒜 ρ̃`, `ρ̃ ≤ 2`,
  `compDen_le`);
* `Gsw`, `ηVc`, `hsw_c` : the switching expression, `η_V(t) = ½ sup_{|h| ≤ 1.01H(t)} G(t, h)` and
  the field `hsw`;
* `opR` : an `OpHyp` proof for the realised system; `Btc`, `hdec_c` : the canonical `B_t` of
  Step 6(a) and the field `hdec` (its content is `hBt`);
* `S2Rng_cases`, `hS2E_field` : the fields `hS2Ep`, `hS2Em` from `Queue6.hS2Epm_R` (the time
  condition `max(z, X₀) + 2H(z) ≤ b` holds on `S2Rng` unless `z < X₀ - 1.6H(X₀)`, where both
  sides vanish).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### `TNP.Hyp` -/

/-- **`TNP.Hyp` for the realised system** at the Model choices (`Queue6.tnpHyp_R`, with
`PaperWidth` from `paperWidth_Hc`, `capHSlope`, `capHDiff`). -/
theorem tnpR (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) :
    KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10) := by
  have hX : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hw : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) epsH (epsH / 10) :=
    KR.WidthReal.paperWidth_Hc hX (by unfold epsH; norm_num) (by unfold epsH; norm_num)
      (CapHSlopeProof.capHSlope hX) (CapHDiffProof.capHDiff hX)
  have h := Queue6.tnpHyp_R hc hev hSG hX1 hbs hw
  rw [← twR_eq hc ω] at h
  exact h

/-! ### `NT_pt` -/

/-- `|K_pt g(y)| ≤ 2 ∑_{w ∈ 𝒩(Y/X₀⁻)} 1/w` for `|g| ≤ 2`, `y ≤ Y`. -/
lemma Kpt_abs_le {P : BeurlingSystem} {tw : ℕ → ℝ} {X0m : ℝ} (hX : 0 < X0m) {g : ℝ → ℝ}
    (hg : ∀ z, |g z| ≤ 2) {y Y : ℝ} (hyY : y ≤ Y) :
    |KR.Sharp.Kpt P tw X0m g y| ≤ ∑ w ∈ KR.NAll P Y X0m, 2 / Vl P w := by
  classical
  unfold KR.Sharp.Kpt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (s := (KR.NAll P y X0m).filter
    (2 ≤ ·)) ?_ fun w _ _ => div_nonneg (by norm_num) (KR.Sharp.Vl_pos P w).le)
  · refine Finset.sum_le_sum fun w _ => ?_
    have hV := KR.Sharp.Vl_pos P w
    split_ifs
    · rw [abs_div, abs_of_pos hV]; exact div_le_div_of_nonneg_right (hg _) hV.le
    · simp only [abs_zero]; positivity
  · intro w hw
    have h1 := (KR.Sharp.mem_NAll_iff P hX).mp (Finset.mem_filter.mp hw).1
    refine (KR.Sharp.mem_NAll_iff P hX).mpr ⟨h1.1, h1.2.trans ?_⟩
    exact div_le_div_of_nonneg_right hyY hX.le

/-- `|K_𝒜 g(y)| ≤ 2 ∑_{w ∈ 𝒩(Y/X₀⁻)} 1/w` for `|g| ≤ 2`, `y ≤ Y`. -/
lemma KAbsR_abs_le (hc : Cond θ X₀) (ω : JitterΩ) {g : ℝ → ℝ} (hg : ∀ z, |g z| ≤ 2) {y Y : ℝ}
    (hyY : y ≤ Y) :
    |KAbsR θ X₀ ω g y| ≤ ∑ w ∈ KR.NAll (PR θ X₀ ω) Y (Xm X₀), 2 / Vl (PR θ X₀ ω) w := by
  classical
  have hX : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  unfold KAbsR
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (s := (KR.NAll (PR θ X₀ ω) y (Xm X₀)).filter (2 ≤ ·)) ?_
    fun w _ _ => div_nonneg (by norm_num) (KR.Sharp.Vl_pos _ w).le)
  · refine Finset.sum_le_sum fun w _ => ?_
    have hV := KR.Sharp.Vl_pos (PR θ X₀ ω) w
    split_ifs
    · rw [abs_div, abs_of_pos hV]; exact div_le_div_of_nonneg_right (hg _) hV.le
    · simp only [abs_zero]; positivity
  · intro w hw
    have h1 := (KR.Sharp.mem_NAll_iff (PR θ X₀ ω) hX).mp (Finset.mem_filter.mp hw).1
    refine (KR.Sharp.mem_NAll_iff (PR θ X₀ ω) hX).mpr ⟨h1.1, h1.2.trans ?_⟩
    exact div_le_div_of_nonneg_right hyY hX.le

/-- **`NT_pt` is bounded below any height** (`NT_pt = c - K_pt ρ̃ + K_𝒜 ρ̃`). -/
theorem NTpt_bdd (hc : Cond θ X₀) (hev : Even X₀) (ω : JitterΩ) (Y : ℝ) :
    ∃ C, ∀ y, y ≤ Y → |NTpt θ X₀ ω y| ≤ C := by
  classical
  have hX : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  set K := 2 * ∑ w ∈ (cof_finite hc Y ω).toFinset, ENNReal.ofReal (eval (DD θ X₀ ω) w)⁻¹
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.ofReal_ne_top)
  set S := ∑ w ∈ KR.NAll (PR θ X₀ ω) Y (Xm X₀), 2 / Vl (PR θ X₀ ω) w
  have hg : ∀ z, |rhoT θ X₀ ω z| ≤ 2 := fun z => by
    rw [abs_of_nonneg (rhoT_nonneg ω z)]; exact rhoT_le_two hc hev ω z
  refine ⟨K.toReal + S + S, fun y hy => ?_⟩
  have h1 : (compDen θ X₀ ω y).toReal ≤ K.toReal := ENNReal.toReal_mono hK (compDen_le hc hev ω hy)
  have h0 : 0 ≤ (compDen θ X₀ ω y).toReal := ENNReal.toReal_nonneg
  have h2 := Kpt_abs_le (P := PR θ X₀ ω) (tw := twR θ X₀ ω) hX hg hy
  have h3 := KAbsR_abs_le hc ω hg hy
  unfold NTpt KptR
  have e := abs_le.mp h2
  have e3 := abs_le.mp h3
  rw [abs_le]; constructor <;> linarith [e.1, e.2, e3.1, e3.2]

/-! ### The canonical `η_V` and the field `hsw` -/

variable (θ X₀) in
/-- The switching expression of the field `hsw` (filter switching plus `|ΔNT_pt|`). -/
noncomputable def Gsw (ω : JitterΩ) (p : Margin.Rec.CP) (t h : ℝ) : ℝ :=
  |∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
      (Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) (t + h) w -
        Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w) *
      (rhoT θ X₀ ω ((t + h) / KR.Vl (PR θ X₀ ω) w) / KR.Vl (PR θ X₀ ω) w)| +
    |NTpt θ X₀ ω (t + h) - NTpt θ X₀ ω t|

variable (θ X₀) in
/-- **The canonical `η_V(t) = ½ sup_{|h| ≤ 1.01 H(t)} G(t, h)`**. -/
noncomputable def ηVc (ω : JitterΩ) (p : Margin.Rec.CP) (t : ℝ) : ℝ :=
  1 / 2 * Margin.RML6.supW (Gsw θ X₀ ω p t) (1.01 * Queue6.Hc X₀ t)

/-- **The field `hsw`** at `η_V = ηVc`, for `t ≤ b`. -/
theorem hsw_c (hc : Cond θ X₀) (hev : Even X₀) (ω : JitterΩ) (p : Margin.Rec.CP) {b t : ℝ}
    (htb : t ≤ b) {hh : ℝ} (hhh : |hh| ≤ 1.01 * Queue6.Hc X₀ t) :
    Gsw θ X₀ ω p t hh ≤ 2 * ηVc θ X₀ ω p t := by
  obtain ⟨C, hC⟩ := NTpt_bdd hc hev ω (b + 1.01 * Queue6.Hc X₀ b)
  have hmono := KR.WidthReal.Hc_mono hc.hX
  have hHt : Queue6.Hc X₀ t ≤ Queue6.Hc X₀ b := hmono htb
  set S := ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t, 2 / KR.Vl (PR θ X₀ ω) w
  have hb : ∀ h, |h| ≤ 1.01 * Queue6.Hc X₀ t → Gsw θ X₀ ω p t h ≤ S + 2 * C := by
    intro h hh'
    have hh1 := (abs_le.mp hh').2
    have e1 := hC (t + h) (by linarith)
    have e2 := hC t (by
      have : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
      linarith)
    have hsum : |∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) p t,
        (Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) (t + h) w -
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w) *
        (rhoT θ X₀ ω ((t + h) / KR.Vl (PR θ X₀ ω) w) / KR.Vl (PR θ X₀ ω) w)| ≤ S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      have hV := KR.Sharp.Vl_pos (PR θ X₀ ω) w
      have k1 := Margin.Rec.kap_mem (PR θ X₀ ω) (twR θ X₀ ω) (t + h) w
      have k2 := Margin.Rec.kap_mem (PR θ X₀ ω) (twR θ X₀ ω) t w
      have r0 := rhoT_nonneg (θ := θ) (X₀ := X₀) ω ((t + h) / KR.Vl (PR θ X₀ ω) w)
      have r2 := rhoT_le_two hc hev ω ((t + h) / KR.Vl (PR θ X₀ ω) w)
      rw [abs_mul, abs_div, abs_of_pos hV, abs_of_nonneg r0]
      have hk : |Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) (t + h) w -
          Margin.Rec.kap (PR θ X₀ ω) (twR θ X₀ ω) t w| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [k1.1, k1.2, k2.1, k2.2]
      calc _ ≤ 1 * (2 / KR.Vl (PR θ X₀ ω) w) :=
            mul_le_mul hk (div_le_div_of_nonneg_right r2 hV.le) (by positivity) (by norm_num)
        _ = 2 / KR.Vl (PR θ X₀ ω) w := one_mul _
    unfold Gsw
    have : |NTpt θ X₀ ω (t + h) - NTpt θ X₀ ω t| ≤ 2 * C :=
      (abs_sub _ _).trans (by linarith)
    linarith
  have := Margin.RML6.le_supW (F := Gsw θ X₀ ω p t) hb hhh
  unfold ηVc; linarith

/-! ### `OpHyp`, the canonical `B_t` and the field `hdec` -/

/-- `X₀⁻ ≤ Zc b`. -/
lemma Xm_le_Zc' (hc : Cond θ X₀) (b : ℝ) : Xm X₀ ≤ Zc X₀ b := by
  unfold Zc
  split_ifs with h
  · have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have := capH_ge_one hX0 hc.hX (le_refl (X₀ : ℝ))
    unfold Xm; linarith
  · exact le_rfl

/-- An `OpHyp` proof for the realised system (`KR.Ops.opHyp_Hc`). -/
theorem opR (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hSG : ω ∈ Queue6.SG (θ := θ) (X₀ := X₀)) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) :
    KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) :=
  let h := tnpR hc hev hbs hSG hX1
  KR.Ops.opHyp_Hc hc.hX h.width (KR.Chain.p_ge_two_of h (Xm_le_Zc' hc b))

variable (θ X₀) in
/-- **The canonical `B_t`** of Step 6(a): `ρ̃ + ν + NT - B m` (`hdec_canon`; the content is
`hBt`). -/
noncomputable def Btc (ω : JitterΩ) (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL vtH NT : KR.Ops.LocInt) (t : ℝ) : ℝ :=
  rhoT θ X₀ ω t + (nuRes hO (twR θ X₀ ω) ρL TcL (JL (jzX X₀) X₀) vtH NT : ℝ → ℝ) t +
    (NT : ℝ → ℝ) t - Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t

/-- **The field `hdec`** at `B_t = Btc`. -/
theorem hdec_c (ω : JitterΩ) (hO₀ : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (ρL TcL vtH NT : KR.Ops.LocInt) (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    (t : ℝ) :
    rhoT θ X₀ ω t + (nuRes hO (twR θ X₀ ω) ρL TcL (JL (jzX X₀) X₀) vtH NT : ℝ → ℝ) t +
      (NT : ℝ → ℝ) t = Margin.Bavg (Queue6.Hc X₀ t) (marginM θ X₀ ω) t +
        Btc θ X₀ ω hO₀ ρL TcL vtH NT t := by
  have : hO = hO₀ := Subsingleton.elim _ _
  subst this
  unfold Btc; ring

/-! ### The Step 2 deviations -/

/-- `e(m) ≥ 0`. -/
lemma eB_nonneg (hc : Cond θ X₀) (m : ℕ) : 0 ≤ Queue6.eB X₀ m := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hu : (X₀ : ℝ) ≤ uS X₀ m := X₀_le_uS (X₀ := X₀) (by linarith) m
  obtain ⟨hL, -, hℓ⟩ := logs_of_ge hX0 hc.hX hu
  have hH1 := capH_ge_one hX0 hc.hX hu
  have hlH : 0 ≤ Real.log (capH X₀ (uS X₀ m)) := Real.log_nonneg hH1
  have hlam : 0 ≤ lamE3 X₀ (uS X₀ m) := by unfold lamE3; linarith
  have hM := capM1_pos hX0 hc.hX hu
  have hs2 : 0 ≤ s2E3 X₀ (uS X₀ m) := by unfold s2E3; positivity
  have hb2 : 0 ≤ b2E3 X₀ (uS X₀ m) := by unfold b2E3; positivity
  have hLen : 0 ≤ LenB X₀ m := by unfold LenB; positivity
  have hl2 : 0 ≤ Real.log (2 * uS X₀ m) := Real.log_nonneg (by linarith)
  unfold Queue6.eB a1B a2B
  positivity

/-- `ε_z ≥ 0`. -/
lemma s2ε_nonneg (hc : Cond θ X₀) (z : ℝ) : 0 ≤ Queue6.s2ε X₀ z := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hq := queueB_nonneg hX0 hc.hX (show (X₀ : ℝ) ≤ 4 * max z X₀ by
    have := le_max_right z (X₀ : ℝ); linarith)
  have h1 := eB_nonneg hc (m1z X₀ z)
  have h2 := eB_nonneg hc (m1z X₀ z + 1)
  unfold Queue6.s2ε; linarith

/-- **The fields `hS2Ep`, `hS2Em`** from `Queue6.hS2Epm_R` (at `ω`, `t ≥ b`): on `S2Rng`, either
the time condition `max(z, X₀) + 2H(z) ≤ b` holds, or `z < X₀ - 1.6H(X₀)` and both sides vanish
(no slot and `m = 0` below `X₀⁻`). -/
theorem hS2E_field (hc : Cond θ X₀) (ω : JitterΩ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hbt : b ≤ t) (hp2 : ∀ j, 2 ≤ (PR θ X₀ ω).p j)
    (hE : ∀ z s : ℝ, 0 ≤ s → s ≤ 1.01 * Hc X₀ z → max z X₀ + 2 * Hc X₀ z ≤ t →
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aplus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z ∧
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aminus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z)
    (p : Margin.Rec.CP) (T0 : ℝ) :
    ∀ z, S2Rng θ X₀ ω p T0 b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Hc X₀ z →
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aplus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z ∧
      |Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s) (Margin.Exact.Aminus (Hc X₀) z s) -
          ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r| ≤ s2ε X₀ z := by
  classical
  intro z hz s hs0 hs
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  set H0 := capH X₀ X₀ with hH0
  have h4H := four_capH_le hX0 hc.hX (le_refl (X₀ : ℝ))
  have hH1 := capH_ge_one hX0 hc.hX (le_refl (X₀ : ℝ))
  have h40 : capH X₀ X₀ ≤ (X₀ : ℝ) / 40 := KR.WidthReal.capH_le_tenth hc.hX le_rfl
  -- `z ≤ b/2` or `z < 0`
  obtain ⟨t', -, ht'b, w, hw, -, hzw⟩ := hz
  have hw2 : 2 ≤ w := (Finset.mem_filter.mp hw).2
  have hV2 := KR.Ops.Vl_ge_two hp2 hw2
  have hzb : z ≤ b / 2 ∨ z < 0 := by
    rcases le_or_gt 0 t' with ht0 | ht0
    · left
      have : t' / KR.Vl (PR θ X₀ ω) w ≤ t' / 2 := div_le_div_of_nonneg_left ht0 (by norm_num) hV2
      linarith
    · right
      have : t' / KR.Vl (PR θ X₀ ω) w < 0 := div_neg_of_neg_of_pos ht0 (by linarith)
      linarith
  have hHz : ∀ y : ℝ, y < X₀ → Hc X₀ y = H0 := fun y hy => by
    unfold Hc; rw [max_eq_right hy.le]
  rcases le_or_gt (max z X₀ + 2 * Hc X₀ z) t with htime | htime
  · exact hE z s hs0 hs htime
  -- otherwise `z < X₀ - 1.6 H(X₀)`
  have hzlow : z < X₀ - 1.6 * H0 := by
    by_contra hcon; push_neg at hcon
    apply absurd htime (not_lt.mpr _)
    rcases le_or_gt (X₀ : ℝ) z with hzX | hzX
    · have hHz' : Hc X₀ z ≤ z / 4 := by
        unfold Hc; rw [max_eq_left hzX]; have := four_capH_le hX0 hc.hX hzX; linarith
      rw [max_eq_left hzX]
      rcases hzb with h | h <;> linarith
    · rw [max_eq_right hzX.le, hHz z hzX]
      rcases hzb with h | h
      · linarith
      · linarith
  have hzX : z < X₀ := by linarith
  have hsH : s ≤ 1.01 * H0 := by rw [← hHz z hzX]; exact hs
  have hXm : Xm X₀ = X₀ - H0 / 2 := rfl
  -- the floor: `x - H(x)/2 ≥ X₀⁻` for `x ≥ X₀`
  have hfl : ∀ x : ℝ, (X₀ : ℝ) ≤ x → Xm X₀ ≤ x - Hc X₀ x / 2 := fun x hx => by
    unfold Hc; rw [max_eq_left hx]; exact JitterFloor.capH_floor hX0 hc.hX hx
  have hHnn : ∀ x : ℝ, 0 ≤ Hc X₀ x := fun x => by unfold Hc; exact capH_nonneg _ _
  -- `A±` lies below `X₀`
  have hAp : ∀ x ∈ Margin.Exact.Aplus (Hc X₀) z s, x < X₀ := by
    rintro x ⟨-, h2⟩
    by_contra hx; push_neg at hx
    have := hfl x hx; linarith
  have hAm : ∀ x ∈ Margin.Exact.Aminus (Hc X₀) z s, x < X₀ := by
    rintro x ⟨-, h2⟩
    have := hHnn x; linarith
  -- the slots are `≥ X₀`
  have hsl : ∀ q, (X₀ : ℝ) ≤ s2sl θ X₀ ω z s q := fun q => slotF_ge hc q ω
  have hσp : Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s)
      (Margin.Exact.Aplus (Hc X₀) z s) = 0 := by
    unfold Margin.Exact.sigmaS
    rw [Finset.card_eq_zero.mpr, Nat.cast_zero]
    exact Finset.filter_eq_empty_iff.mpr fun q _ h => absurd (hAp _ h) (not_lt.mpr (hsl q))
  have hσm : Margin.Exact.sigmaS (s2Q θ X₀ ω z s) (s2sl θ X₀ ω z s)
      (Margin.Exact.Aminus (Hc X₀) z s) = 0 := by
    unfold Margin.Exact.sigmaS
    rw [Finset.card_eq_zero.mpr, Nat.cast_zero]
    exact Finset.filter_eq_empty_iff.mpr fun q _ h => absurd (hAm _ h) (not_lt.mpr (hsl q))
  have hip : ∫ r in Margin.Exact.Aplus (Hc X₀) z s, marginM θ X₀ ω r = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      BModel.RML6.marginM_eq_zero_low hc ω (hAp x hx)
  have him : ∫ r in Margin.Exact.Aminus (Hc X₀) z s, marginM θ X₀ ω r = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      BModel.RML6.marginM_eq_zero_low hc ω (hAm x hx)
  rw [hσp, hσm, hip, him, sub_zero, abs_zero]
  exact ⟨s2ε_nonneg hc z, s2ε_nonneg hc z⟩

end BModel
