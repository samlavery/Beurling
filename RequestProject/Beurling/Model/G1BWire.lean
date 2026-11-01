module

public import RequestProject.Beurling.Model.G1BDelta
public import RequestProject.Beurling.Model.G1BStep3Fields

/-!
# `G1BInputs` from its Model part and the remaining (Queue6, §5) inputs

`G1BRest P tw X₀⁻ X₀ T' y δ ρ̃ thr` collects the fields of `KR.RML6.G1BInputs` that are not
Model's (Queue6: Step 1's `hcount` with `E_loc`, the sizes `H`, `K_loc` and `hthr` of Lemma 5.23
at `2δ` for the threshold mass `thr`; §5: Step 2's inputs), at a given window parameter `δ`, a
given `ρ̃` and a given threshold mass. `g1B_mk` assembles `G1BInputs` from them and the Model
fields: `δ = deltaB` with its bounds and Theorem 5.24 at `y(1-δ)` (`G1BDelta.lean`), `ρ̃ = rhoT`,
and the Step 3–4 fields (`step3_R`, with `thrS = threshSum tJ y (2δ)`, `thrS_eq`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace KR.RML6

/-- **The non-Model inputs of Proposition 5.35(B)** at a start `y`, window parameter `δ`, `ρ̃` and
threshold mass `thr` (field names and statements as in `G1BInputs`). -/
structure G1BRest (P : BeurlingSystem) (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (Tp : ℝ → ℝ)
    (y δ : ℝ) (ρt : ℝ → ℝ) (thr : ℝ) where
  /-- Step 1, first bullet (Queue6) -/
  Eloc : ℝ
  hE0 : 0 ≤ Eloc
  hE : Eloc ≤ 40 * √y
  hcount : LocalPNT.piCount P (y * (1 - δ)) - LocalPNT.piCount P (y * (1 - 2 * δ)) - Eloc ≤
    ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), ρt z
  -- Step 2
  ν : ℝ → ℝ
  NT : ℝ → ℝ
  BRT : ℝ → ℝ
  Bρs : ℝ → ℝ
  εN : ℝ
  EBR : ℝ
  j : ℝ
  nb : ℝ
  η : ℝ
  Bnd : ℝ
  hit : IntervalIntegrable ρt volume (y * (1 - 2 * δ)) (y * (1 - δ))
  his : IntervalIntegrable (fun z => rhoSh P tw X0m z Tp) volume (y * (1 - 2 * δ)) (y * (1 - δ))
  hiB : IntervalIntegrable Bρs volume (y * (1 - 2 * δ)) (y * (1 - δ))
  /-- Lemma 5.34 on `J` (§5) -/
  h34 : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    |ρt z + ν z + NT z - BRT z| ≤ εN / Real.log y
  /-- Proposition 5.26 with Lemma 5.27 on `J` (§5) -/
  hbr : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |BRT z - Bρs z| ≤ (EBR + j) / Real.log y
  /-- `|ν| ≤ ν̄` (Lemma 5.22; Queue6) -/
  hν : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |ν z| ≤ nb
  /-- `|NT| ≤ 54η` (§5; pointwise eq. (NT): `BModel.NTpt_abs_le_eta`) -/
  hNT : ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)), |NT z| ≤ 54 * η
  /-- the boundary term of Step 2 (§5) -/
  hbd : ∫ z in (y * (1 - 2 * δ))..(y * (1 - δ)), (Bρs z - rhoSh P tw X0m z Tp) ≤ Bnd
  hBnd0 : 0 ≤ Bnd
  hBnd : Bnd ≤ 40 * √y
  /-- sizes of Step 2 (§5: Lemma 5.20, Lemma 5.22) -/
  hsmall2 : Real.log y * (nb + 54 * η) ≤ 1 / 10 ^ 26
  hεN : εN ≤ 1 / 10 ^ 13
  hEBR : EBR ≤ Real.exp (-76)
  hj : j ≤ Real.exp (-59)
  /-- Lemma 5.23 at `2δ` (via `threshold_mass`; Queue6) -/
  Hy : ℝ
  Kloc : ℝ
  hthr : thr ≤ 55 * (2 * δ) * Real.log y * (Real.log Hy + Real.log (1 / (2 * δ)) + 2) +
    14 * (Kloc + 2) * Real.log y * √(Hy / (2 * δ * y))
  hH1 : 1 ≤ Hy
  hH : Hy ≤ Real.exp (Real.log y / 8)
  hK0 : 0 ≤ Kloc
  hK : Kloc ≤ Hy

end KR.RML6

open Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`G1BInputs` for the realised system** at a range-(B) start `y` (Proposition 5.35(B)),
from the Model fields (`δ = deltaB`, `hT_c`, `ρ̃ = rhoT`, `step3_R`) and the remaining inputs
`G1BRest` at `δ = deltaB`, `ρ̃ = rhoT`, `thr = threshSum tJ y (2δ)`. The Model inputs still
named are `JumpCountR` and `RprimeChangeR` (Step 3 of the proof). -/
noncomputable def g1B_mk {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y)
    (hJ : JumpCountR θ X₀ ω y (deltaB θ X₀ ω y))
    (hRp : RprimeChangeR θ X₀ ω y (deltaB θ X₀ ω y))
    (R : KR.RML6.G1BRest (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
      (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) y (deltaB θ X₀ ω y)
      (rhoT θ X₀ ω)
      ((PR θ X₀ ω).threshSum (Queue6.tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y))) :
    KR.RML6.G1BInputs (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
      (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) y :=
  let S := step3_R hc hev hb hbt hQC hE1 hN hT hy hyb hyB (deltaB_pos hc ω hy)
    (deltaB_le (θ := θ) ω y) hJ hRp
  { δ := deltaB θ X₀ ω y
    hδ0 := deltaB_pos hc ω hy
    hδ := deltaB_le (θ := θ) ω y
    hδlow := deltaB_low hc ω hy
    hδL := deltaB_L hc ω hy
    hT := hT_c hc hev hb hbt hQC hE1 hN hy hyb hyB
    ρt := rhoT θ X₀ ω
    Eloc := R.Eloc
    hE0 := R.hE0
    hE := R.hE
    hcount := R.hcount
    ν := R.ν
    NT := R.NT
    BRT := R.BRT
    Bρs := R.Bρs
    εN := R.εN
    EBR := R.EBR
    j := R.j
    nb := R.nb
    η := R.η
    Bnd := R.Bnd
    hit := R.hit
    his := R.his
    hiB := R.hiB
    h34 := R.h34
    hbr := R.hbr
    hν := R.hν
    hNT := R.hNT
    hbd := R.hbd
    hBnd0 := R.hBnd0
    hBnd := R.hBnd
    hsmall2 := R.hsmall2
    hεN := R.hεN
    hEBR := R.hEBR
    hj := R.hj
    thrS := S.thrS
    j0 := S.j0
    jS := S.jS
    detS := S.detS
    othS := S.othS
    hdec34 := S.hdec34
    Hy := R.Hy
    Kloc := R.Kloc
    hthr := by
      rw [thrS_eq hc hev hb hbt hQC hE1 hN hT hy hyb hyB (deltaB_pos hc ω hy)
        (deltaB_le (θ := θ) ω y) hJ hRp]
      exact R.hthr
    hH1 := R.hH1
    hH := R.hH
    hK0 := R.hK0
    hK := R.hK
    N := S.N
    HN := S.HN
    θ := S.θ
    hj0 := S.hj0
    hj1 := S.hj1
    hjS := S.hjS
    hN := S.hN
    hHN0 := S.hHN0
    hHN := S.hHN
    hθ0 := S.hθ0
    hθ := S.hθ
    CS := S.CS
    hCS0 := S.hCS0
    hCS := S.hCS
    hdet := S.hdet
    hoth := S.hoth }

end BModel

end
