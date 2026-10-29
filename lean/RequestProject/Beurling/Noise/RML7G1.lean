module

public import RequestProject.Beurling.Noise.RML6G1
public import RequestProject.Beurling.Noise.RML6PredMain
public import RequestProject.Beurling.Noise.TcLocal

/-!
# The §5 inputs of `KR.RML6.G1BInputs` (Proposition 5.35(B), Step 2)

Theorems producing the fields of `G1BInputs` that come from §5, at a start `y`, on the interval
`J = [lo, hi]` (in `G1BInputs`, `lo = y(1 - 2δ)`, `hi = y(1 - δ)`):

* `abs_D_le_ops` : Lemma 5.34, two-sided: `log x · |ρ + ν + NT - B R_res T'| ≤ a + b + 6 log x/H`;
* `h34_of` : the field `h34`, with `BRT z = B(R_res T')(z)`, from the two bullets of Lemma 5.34,
  `|ϑ| ≤ 6` and the size condition `(a + b + 6 log z/H)/log z ≤ ε_N/log y` on `J`;
* `abs_Rres_sub_rhoSh_loc` : Proposition 5.26 with Lemma 5.27, pointwise and two-sided:
  `|R_res T'(s) - ρ^sh T'(s)| ≤ E/log s + |j₀| 𝔟` from `log s |BR_c(s)| ≤ E` and
  `|R_res 1_{[X₀,∞)} - ρ^sh 1_{[X₀,∞)}|(s) ≤ 𝔟`, with `|T_c| ≤ 2` only below `1.2 s`;
* `hbr_of` : the field `hbr`, with `BRT = B(R_res T')`, `Bρs = B(ρ^sh T')`, from a pointwise
  bound on the windows;
* `hit_of`, `his_of`, `hiB_of` : the integrability fields;
* `hNT_of` : the field `hNT` for `NT = B NT_pt` from `|NT_pt| ≤ 54η` on the windows.
-/

@[expose] public section

open MeasureTheory Set Real

namespace KR.RML7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m ε θ : ℝ}

open KR.Ops

/-- **Lemma 5.34, two-sided**, with the operators of §5.3 on `LocInt`. -/
theorem abs_D_le_ops (hO : OpHyp P H X0m) (ρ ν NT vtH Tc J : LocInt) (ϑ : ℝ → ℝ)
    (hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / H z)
    (hmargin : ρ + Bo hO (Ko (tw := tw) hO ρ) = Bo hO (Tc + J) + vtH - ν - NT)
    {x a b : ℝ} (hlx : 0 ≤ Real.log x)
    (hK : Real.log x * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO Tc - Tc) + vtH - ν - NT)))) : ℝ → ℝ) x| ≤ a)
    (hG : Real.log x * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (Tc + J) + vtH - ν - NT - Bo hO J) -
        Bo hO (Bo hO (Tc + J) + vtH - ν - NT - Bo hO J)))) : ℝ → ℝ) x| ≤ b)
    (hϑ : |ϑ x| ≤ 6) :
    Real.log x * |(ρ : ℝ → ℝ) x + (ν : ℝ → ℝ) x + (NT : ℝ → ℝ) x -
        Margin.Bavg (H x) (Ro (tw := tw) hO (Tc + J)) x| ≤ a + b + 6 * Real.log x / H x := by
  have hid := Pred.predictable_identity_gen (Bo hO) (Ko (tw := tw) hO) (Ro (tw := tw) hO)
    (Nop_spec hO) (fun f f' h => inj_spec hO f f' h) ρ ν NT vtH Tc J hmargin
  have hDx := congrArg (fun u : LocInt => (u : ℝ → ℝ) x) hid
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.add_apply, Pi.sub_apply] at hDx
  exact Pred.lemma_5_34_bound (D := fun z => (ρ : ℝ → ℝ) z + (ν : ℝ → ℝ) z +
      (NT : ℝ → ℝ) z - (Bo hO (Ro (tw := tw) hO (Tc + J)) : ℝ → ℝ) z) (vt := ϑ) (H := H)
    (x := x) (by simp only; rw [hDx, hvt]) hlx (hO.pos x) hK hG hϑ

/-- **The field `h34`** of `G1BInputs` on `J = [lo, hi]`, with `ρ_t = ρ`, `BRT = B(R_res T')`:
from the two bullets of Lemma 5.34 at every `z ∈ J` (bounds `aK z`, `bG z`), `|ϑ| ≤ 6`, `T'`
locally bounded (`LBd`, Model), and the size condition. -/
theorem h34_of (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ) (ρ ν NT vtH Tc J : LocInt)
    (ϑ : ℝ → ℝ) (hvt : ∀ z, (vtH : ℝ → ℝ) z = ϑ z / H z)
    (hmargin : ρ + Bo hO (Ko (tw := tw) hO ρ) = Bo hO (Tc + J) + vtH - ν - NT)
    (hT : LBd ((Tc + J : LocInt) : ℝ → ℝ)) {lo hi y εN : ℝ} (aK bG : ℝ → ℝ)
    (hlz : ∀ z ∈ Icc lo hi, 0 < Real.log z)
    (hK : ∀ z ∈ Icc lo hi, Real.log z * |(Bo hO (Ko (tw := tw) hO (Bo hO (Ro (tw := tw) hO
      ((Bo hO Tc - Tc) + vtH - ν - NT)))) : ℝ → ℝ) z| ≤ aK z)
    (hG : ∀ z ∈ Icc lo hi, Real.log z * |(Bo hO (Ro (tw := tw) hO (Ko (tw := tw) hO
      ((Bo hO (Tc + J) + vtH - ν - NT - Bo hO J) -
        Bo hO (Bo hO (Tc + J) + vtH - ν - NT - Bo hO J)))) : ℝ → ℝ) z| ≤ bG z)
    (hϑ : ∀ z ∈ Icc lo hi, |ϑ z| ≤ 6)
    (hsize : ∀ z ∈ Icc lo hi,
      (aK z + bG z + 6 * Real.log z / H z) / Real.log z ≤ εN / Real.log y) :
    ∀ z ∈ Icc lo hi, |(ρ : ℝ → ℝ) z + (ν : ℝ → ℝ) z + (NT : ℝ → ℝ) z -
      Margin.Bavg (H z) (fun s => Rres P H tw X0m s ((Tc + J : LocInt) : ℝ → ℝ)) z| ≤
        εN / Real.log y := by
  intro z hz
  have hl := hlz z hz
  have h := abs_D_le_ops (tw := tw) hO ρ ν NT vtH Tc J ϑ hvt hmargin hl.le (hK z hz) (hG z hz)
    (hϑ z hz)
  have e : (fun s => Rres P H tw X0m s ((Tc + J : LocInt) : ℝ → ℝ)) =
      ((Ro (tw := tw) hO (Tc + J) : LocInt) : ℝ → ℝ) := by
    funext s; exact Rres_eq_Nop hO hP (Tc + J) hT s
  rw [e]
  refine le_trans ?_ (hsize z hz)
  rw [le_div_iff₀ hl, mul_comm]
  exact h

/-- **Proposition 5.26 with Lemma 5.27, pointwise and two-sided**, with `|T_c| ≤ 2` only below
`1.2 s`: `|R_res T'(s) - ρ^sh T'(s)| ≤ E/log s + |j₀| 𝔟`. -/
theorem abs_Rres_sub_rhoSh_loc (hO : OpHyp P H X0m) (hP : PaperWidth H X0m ε θ)
    {s X0 j0 E bX : ℝ} (hs : X0m ≤ s) (hls : 0 < Real.log s) {Tc : ℝ → ℝ} (hTm : Measurable Tc)
    (hTb : ∀ t, t ≤ 1.2 * s → |Tc t| ≤ 2)
    (hBR : Real.log s * |BRc P H tw X0m s Tc| ≤ E)
    (hXB : |Rres P H tw X0m s (KR.Chain.ind X0) - rhoSh P tw X0m s (KR.Chain.ind X0)| ≤ bX) :
    |Rres P H tw X0m s (fun t => Tc t + j0 * KR.Chain.ind X0 t) -
        rhoSh P tw X0m s (fun t => Tc t + j0 * KR.Chain.ind X0 t)| ≤
      E / Real.log s + |j0| * bX := by
  have hs0 : 0 ≤ s := by have := hO.X0m_pos; linarith
  set Tc' := KR.TcLoc.clampT (1.2 * s) Tc
  have hcong : ∀ t, t ≤ 1.2 * s →
      Tc' t + j0 * KR.Chain.ind X0 t = Tc t + j0 * KR.Chain.ind X0 t :=
    fun t ht => by show KR.TcLoc.clampT (1.2 * s) Tc t + _ = _; rw [KR.TcLoc.clampT_eq ht]
  have hR : Rres P H tw X0m s (fun t => Tc t + j0 * KR.Chain.ind X0 t) =
      Rres P H tw X0m s (fun t => Tc' t + j0 * KR.Chain.ind X0 t) :=
    (Rres_congr (tw := tw) hO hP fun t ht =>
      hcong t (by rwa [abs_of_nonneg hs0] at ht)).symm
  have hS : rhoSh P tw X0m s (fun t => Tc t + j0 * KR.Chain.ind X0 t) =
      rhoSh P tw X0m s (fun t => Tc' t + j0 * KR.Chain.ind X0 t) :=
    (KR.TcLoc.rhoSh_congr hs0 fun t ht => hcong t (by linarith)).symm
  have hBR' : Real.log s * |BRc P H tw X0m s Tc'| ≤ E := by
    rwa [KR.TcLoc.BRc_congr (tw := tw) hO hP hs (G := Tc)
      (fun t ht => KR.TcLoc.clampT_eq ht)]
  rw [hR, hS, KR.Chain.rhoSh_add_smul,
    KR.Chain.Rres_add_smul hP.reg s (KR.TcLoc.measurable_clampT hTm)
      (KR.TcLoc.clampT_abs_le hTb) (KR.Chain.ind_measurable X0) (KR.Chain.ind_abs_le X0)]
  unfold BRc at hBR'
  have h1 : |Rres P H tw X0m s Tc' - rhoSh P tw X0m s Tc'| ≤ E / Real.log s := by
    rw [le_div_iff₀ hls, mul_comm]; exact hBR'
  have h2 : |j0 * (Rres P H tw X0m s (KR.Chain.ind X0) - rhoSh P tw X0m s (KR.Chain.ind X0))|
      ≤ |j0| * bX := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hXB (abs_nonneg _)
  calc |Rres P H tw X0m s Tc' + j0 * Rres P H tw X0m s (KR.Chain.ind X0) -
        (rhoSh P tw X0m s Tc' + j0 * rhoSh P tw X0m s (KR.Chain.ind X0))|
      = |(Rres P H tw X0m s Tc' - rhoSh P tw X0m s Tc') +
          j0 * (Rres P H tw X0m s (KR.Chain.ind X0) - rhoSh P tw X0m s (KR.Chain.ind X0))| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The window average of a difference. -/
lemma Bavg_sub {h x : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (x - h / 2) (x + h / 2))
    (hg : IntervalIntegrable g volume (x - h / 2) (x + h / 2)) :
    Margin.Bavg h f x - Margin.Bavg h g x = Margin.Bavg h (fun t => f t - g t) x := by
  unfold Margin.Bavg
  rw [intervalIntegral.integral_sub hf hg]
  ring

/-- **The field `hbr`** of `G1BInputs` on `J = [lo, hi]`, with `BRT = B(R_res T')` and
`Bρs = B(ρ^sh T')`: from window integrability and a pointwise bound on the windows (which
`abs_Rres_sub_rhoSh_loc` provides at each point `s`). -/
theorem hbr_of (hO : OpHyp P H X0m) {lo hi c : ℝ} {F : ℝ → ℝ}
    (hiR : ∀ z ∈ Icc lo hi, IntervalIntegrable (fun s => Rres P H tw X0m s F) volume
      (z - H z / 2) (z + H z / 2))
    (hiS : ∀ z ∈ Icc lo hi, IntervalIntegrable (fun s => rhoSh P tw X0m s F) volume
      (z - H z / 2) (z + H z / 2))
    (hpt : ∀ z ∈ Icc lo hi, ∀ s, z - H z / 2 ≤ s → s ≤ z + H z / 2 →
      |Rres P H tw X0m s F - rhoSh P tw X0m s F| ≤ c) :
    ∀ z ∈ Icc lo hi, |Margin.Bavg (H z) (fun s => Rres P H tw X0m s F) z -
      Margin.Bavg (H z) (fun s => rhoSh P tw X0m s F) z| ≤ c := by
  intro z hz
  rw [Bavg_sub (hiR z hz) (hiS z hz)]
  exact abs_Bavg_le_on (hO.pos z) (hpt z hz)

/-- **The field `hit`** for a locally integrable `ρ̃`. -/
theorem hit_of (ρ : LocInt) (a b : ℝ) : IntervalIntegrable (ρ : ℝ → ℝ) volume a b := ρ.2 a b

/-- **The field `his`**: window integrability of `ρ^sh T'` with `|T_c| ≤ 2` only below `Y`. -/
theorem his_of (hX : 0 < X0m) {Tc : ℝ → ℝ} (hTm : Measurable Tc) {Y : ℝ}
    (hTb : ∀ t, t ≤ Y → |Tc t| ≤ 2) (j0 X0 : ℝ) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hbY : b ≤ Y) :
    IntervalIntegrable
      (fun z => rhoSh P tw X0m z (fun t => Tc t + j0 * KR.Chain.ind X0 t)) volume a b :=
  KR.TcLoc.intRS_loc hX hTm hTb j0 X0 hab ha hbY

/-- **The field `hiB`**: `z ↦ B f(z)` is integrable on `[lo, hi]` if `f` is integrable on
`[0, Y]` and the windows of the points of `[lo, hi]` lie in `[0, Y]`. -/
theorem hiB_of (hO : OpHyp P H X0m) {f : ℝ → ℝ} {Y lo hi : ℝ} (hlh : lo ≤ hi)
    (hf : IntervalIntegrable f volume 0 Y) (hY : 0 ≤ Y)
    (hwin : ∀ z ∈ Icc lo hi, 0 ≤ z - H z / 2 ∧ z + H z / 2 ≤ Y) :
    IntervalIntegrable (fun z => Margin.Bavg (H z) f z) volume lo hi := by
  set g : ℝ → ℝ := (Icc 0 Y).indicator f
  have hgi : Integrable g := by
    have := (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mp hf
    exact this.integrable_indicator measurableSet_Icc
  have hg : g ∈ LocInt := fun a b => hgi.intervalIntegrable
  have hc := continuous_Bavg hO.cont hO.pos hg
  refine (hc.intervalIntegrable lo hi).congr ?_
  rw [uIoc_of_le hlh]
  intro z hz
  have hw := hwin z ⟨hz.1.le, hz.2⟩
  refine Bavg_congr (hO.pos z).le fun t ht1 ht2 => ?_
  have hmem : t ∈ Icc 0 Y := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  exact indicator_of_mem hmem f

/-- **The field `hNT`** for `NT = B NT_pt`, from `|NT_pt| ≤ 54η` on the windows. -/
theorem hNT_of (hO : OpHyp P H X0m) {lo hi η : ℝ} {NTpt : ℝ → ℝ}
    (hpt : ∀ z ∈ Icc lo hi, ∀ s, z - H z / 2 ≤ s → s ≤ z + H z / 2 → |NTpt s| ≤ 54 * η) :
    ∀ z ∈ Icc lo hi, |Margin.Bavg (H z) NTpt z| ≤ 54 * η :=
  fun z hz => abs_Bavg_le_on (hO.pos z) (hpt z hz)

end KR.RML7

end
