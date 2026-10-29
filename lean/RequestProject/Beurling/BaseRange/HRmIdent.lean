module

public import RequestProject.Beurling.Model.RestWire
public import RequestProject.Beurling.Noise.RML6PredRres

/-!
# Proposition 5.38, Step 6(b): `R_res T' - m` as a resolvent of the noise

With `m = T' - K_pt ρ̃ - NT_pt` (§5.3, `BModel.marginM_eq`), `R_res = (1 + K_pt B)⁻¹` on
`LocInt` (`KR.Ops.Nop_spec`) and `1 + B K_pt` injective (`KR.Ops.inj_spec`), the residual
`R := R_res T' - m` solves `R + K_pt B R = NT_pt - K_pt ν'` with `ν' := Bm - ρ̃`, so

  `R_res T' - m = R_res (NT_pt - K_pt (Bm - ρ̃))`   (exactly, pointwise).

(Indeed `R = R_res T' - T' + K_pt ρ̃ + NT_pt = K_pt(ρ̃ - B R_res T') + NT_pt`, and
`B R_res T' = BR + Bm`.) This is the identity behind the paper's Step 6(b) "Sum", where the
lower bound `m ≥ ρ^sh - …` is obtained from `log x·|M - B R_res T'| ≤ ε_N` (eq. (predictable)):
here the difference `R_res T' - m` is written directly through the noise `ν' = Bm - ρ̃` of
Lemma 5.22.

* `KR.Ops.nop_sub_eq` : the operator identity on `LocInt`;
* `BaseRange.resid_eq_Rres` : `R_res T'(t) - m(t) = R_res g(t)` with
  `g = NT_pt - K_pt (Bm - ρ̃)` (`gR`), for the realised system.
-/

@[expose] public section

open Finset BeurlingSystem

namespace KR.Ops

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- **The resolvent form of the margin residual**: if `m = T - K_pt ρ - NT`, then
`R T - m = R (NT - K_pt (B m - ρ))`, `R = (1 + K_pt B)⁻¹`. -/
theorem nop_sub_eq (hO : OpHyp P H X0m) (T m ρ NT : LocInt)
    (hm : m = T - Ko (tw := tw) hO ρ - NT) :
    Nop (tw := tw) hO T - m = Nop (tw := tw) hO (NT - Ko (tw := tw) hO (Bo hO m - ρ)) := by
  set N := Nop (tw := tw) hO T with hNdef
  have hN : N + Ko (tw := tw) hO (Bo hO N) = T := Nop_spec (tw := tw) hO T
  have e1 : Ko (tw := tw) hO (Bo hO N) = T - N := by rw [← hN]; abel
  set g := NT - Ko (tw := tw) hO (Bo hO m - ρ) with hg
  set R := N - m with hR
  have hRe : R + Ko (tw := tw) hO (Bo hO R) = g := by
    simp only [hR, hg, map_sub]
    rw [e1]
    subst hm
    simp only [map_sub]
    abel
  have hgs : Nop (tw := tw) hO g + Ko (tw := tw) hO (Bo hO (Nop (tw := tw) hO g)) = g :=
    Nop_spec (tw := tw) hO g
  set d := R - Nop (tw := tw) hO g with hd
  have hd0 : d + Ko (tw := tw) hO (Bo hO d) = 0 := by
    have : d + Ko (tw := tw) hO (Bo hO d) = (R + Ko (tw := tw) hO (Bo hO R)) -
        (Nop (tw := tw) hO g + Ko (tw := tw) hO (Bo hO (Nop (tw := tw) hO g))) := by
      simp only [hd, map_sub]; abel
    rw [this, hRe, hgs, sub_self]
  have hB : Bo hO d = 0 := by
    refine inj_spec (tw := tw) hO (Bo hO d) 0 ?_
    have : Bo hO d + Bo hO (Ko (tw := tw) hO (Bo hO d)) =
        Bo hO (d + Ko (tw := tw) hO (Bo hO d)) := (map_add _ _ _).symm
    simp only [Bo, Ko] at this ⊢
    rw [this]
    simp only [Bo, Ko] at hd0
    rw [hd0, map_zero, map_zero, map_zero, add_zero]
  have hd1 : d = 0 := by
    rw [hB, map_zero, add_zero] at hd0; exact hd0
  exact sub_eq_zero.mp hd1

end KR.Ops

namespace BaseRange

open BModel Construction KR KR.Chain

variable {θ : ℝ} {X₀ : ℕ}

variable (θ X₀) in
/-- `T' = T_c + j₀ 1_{[X₀,∞)}` on `LocInt`. -/
noncomputable def TpL (ω : JitterΩ) : KR.Ops.LocInt := TcLd θ X₀ ω + JL (jzX X₀) X₀

variable (θ X₀) in
/-- `m = T' - K_pt ρ̃ - NT_pt` on `LocInt`. -/
noncomputable def mL {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    KR.Ops.LocInt :=
  TpL θ X₀ ω - KR.Ops.Ko (tw := twR θ X₀ ω) hO (ρLd θ X₀ ω) - NTptLd θ X₀ ω

variable (θ X₀) in
/-- The source `g = NT_pt - K_pt (Bm - ρ̃)` of the residual `R_res T' - m`. -/
noncomputable def gR {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    KR.Ops.LocInt :=
  NTptLd θ X₀ ω - KR.Ops.Ko (tw := twR θ X₀ ω) hO (KR.Ops.Bo hO (mL θ X₀ hO) - ρLd θ X₀ ω)

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma TpL_coe (ω : JitterΩ) :
    (TpL θ X₀ ω : ℝ → ℝ) = fun s => TcR θ X₀ ω (jzX X₀) s + jzX X₀ * ind X₀ s := by
  funext s
  show (TcLd θ X₀ ω : ℝ → ℝ) s + (JL (jzX X₀) X₀ : ℝ → ℝ) s = _
  rw [TcLd_coe hc hev ω]; rfl

lemma mL_coe {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    (mL θ X₀ hO : ℝ → ℝ) = marginM θ X₀ ω := by
  funext s
  show (TpL θ X₀ ω : ℝ → ℝ) s - Sharp.Kpt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀)
      (ρLd θ X₀ ω : ℝ → ℝ) s - (NTptLd θ X₀ ω : ℝ → ℝ) s = _
  rw [TpL_coe hc hev ω, ρLd_coe hc hev ω, NTptLd_coe hc hev ω, marginM_eq]
  unfold TcR KptR
  ring

lemma LMb_NTptLd (ω : JitterΩ) : LMb (NTptLd θ X₀ ω) := by
  unfold NTptLd; rw [dif_pos ⟨hc, hev⟩]; exact LMb_NTptL hc hev ω

lemma LMb_TpL (ω : JitterΩ) : LMb (TpL θ X₀ ω) := (LMb_TcLd hc hev ω).add (LMb.JL _)

lemma LMb_mL {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    LMb (mL θ X₀ hO) :=
  ((LMb_TpL hc hev ω).sub (LMb.Ko hO (LMb_ρLd hc hev ω))).sub (LMb_NTptLd hc hev ω)

lemma LMb_gR {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀)) :
    LMb (gR θ X₀ hO) :=
  (LMb_NTptLd hc hev ω).sub (LMb.Ko hO ((LMb.Bo hO (LMb_mL hc hev hO)).sub (LMb_ρLd hc hev ω)))

/-- **`R_res T'(t) - m(t) = R_res g(t)`**, `g = NT_pt - K_pt (Bm - ρ̃)`, at every `t`. -/
theorem resid_eq_Rres {ω : JitterΩ} (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {ε θH : ℝ} (hP : PaperWidth (Queue6.Hc X₀) (Xm X₀) ε θH) (t : ℝ) :
    Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
        (fun s => TcR θ X₀ ω (jzX X₀) s + jzX X₀ * ind X₀ s) - marginM θ X₀ ω t =
      Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t (gR θ X₀ hO : ℝ → ℝ) := by
  have h1 := KR.Ops.Rres_eq_Nop (tw := twR θ X₀ ω) hO hP (TpL θ X₀ ω) (LMb_TpL hc hev ω).1 t
  have h2 := KR.Ops.Rres_eq_Nop (tw := twR θ X₀ ω) hO hP (gR θ X₀ hO) (LMb_gR hc hev hO).1 t
  rw [TpL_coe hc hev ω] at h1
  rw [h1, h2, ← mL_coe hc hev hO]
  have e := KR.Ops.nop_sub_eq (tw := twR θ X₀ ω) hO (TpL θ X₀ ω) (mL θ X₀ hO) (ρLd θ X₀ ω)
    (NTptLd θ X₀ ω) rfl
  have e' := congrArg (fun u : KR.Ops.LocInt => (u : ℝ → ℝ) t) e
  simp only [AddSubgroup.coe_sub, Pi.sub_apply] at e'
  exact e'

end

end BaseRange

end
