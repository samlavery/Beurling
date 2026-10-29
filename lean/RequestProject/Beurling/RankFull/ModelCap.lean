module

public import RequestProject.Beurling.RankFull.CapLwAll
public import RequestProject.Beurling.RankFull.ConfigReduction

/-!
# Theorem 6.23(a) for the window model

`RankFull.Config.theorem_6_23a_model` : `theorem_6_23a_all` specialised to the window sets
`S(J) = windowVecs` of the window model, with the skeleton counts `X = cfgSkelCount`. The
inputs `0 ∉ S(J)`, `deg ≤ D` on `S(J)` and the reduction to skeletons
(`ConfigSkeletonReduction`, Lemma 6.21(ii)) are discharged; what remains is the Cover Bound
(`CoverSkeletonBound`, Lemmas 6.17–6.19 via Lemma A.5), measurability, and the parameters, plus
the model hypotheses (prime values `≥ 1`, windows in `(-∞, 2z+1]` with `z = e^L`, and the
label bound `τl_ℓ ≤ q_n` for `ℓ ≤ #{decided slots before n}`).
-/

@[expose] public section

open Finset MeasureTheory BSCert.Capl
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

/-- **Theorem 6.23(a) for the window model** (`theorem_6_23a_all` with `S = windowVecs`,
`X = cfgSkelCount`; `ConfigSkeletonReduction` proved by `configSkeletonReduction`). -/
theorem theorem_6_23a_model {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) (dec : Ω → Finset (Fin N))
    (q : Ω → Fin N → ℝ) (Dmax : ℕ) (Jw : ι → Set ℝ) {X₀ : ℕ} (hΛ : 10 ^ 8 ≤ Real.log X₀)
    {sH s Xm : ℝ} (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746) (hval : gstar sH = gTarget)
    (hs : -Real.log (Real.log X₀) ≤ s) {r₀ D : ℕ} (hr0 : 1 ≤ r₀) (hD1 : 1 ≤ D)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * (2 * Real.log (Real.log X₀) + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s) / Real.log X₀)
    (hXm0 : 0 < Xm) (hXmlo : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log Xm)
    (hXmhi : Real.log Xm ≤ Real.log X₀)
    (τl : Fin (r₀ * D) → ℝ) (hτlXm : ∀ i, Xm ≤ τl i)
    (hτi : ∀ i : Fin (r₀ * D), (((i : ℕ) : ℝ) + 1) / 2 ≤ τl i)
    (hq1 : ∀ ω, ∀ n ∈ dec ω, 1 ≤ q ω n)
    (hJz : ∀ J ∈ W, Jw J ⊆
      Set.Iic (2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s)) + 1))
    (hτq : ∀ ω, ∀ n ∈ dec ω, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ ((dec ω).filter (· < n)).card →
      τl ℓ ≤ q ω n)
    {Ch B lam Atop Eu : ℝ} (τ : (r : ℕ) → Fin r → ℝ) (hτ : ∀ r, ∀ i, 1 < τ r i)
    (hlam0 : 0 ≤ lam) (hrlam : 1 + r₀ * lam ≤ Real.exp (2 * Real.log (Real.log X₀) + s))
    (hCh : Ch ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s))
    (hBτ : ∀ r < r₀, ∏ i, (1 - (τ r i)⁻¹)⁻¹ ≤ B)
    (hB : B ≤ 2.1 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (1.02 : ℝ))
    (hEu : 0 < Eu) (hEuA : Eu ≤ Atop) (hACh : Atop ≤ Ch) (hlam : Real.log (Atop / Eu) ≤ lam)
    (hW : (W.card : ℝ) ≤ 2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s)) /
      (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) + 1)
    (hmeas : ∀ j k, ∀ J ∈ W, Measurable fun ω =>
      (configCount r₀ j k (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) : ℝ≥0∞))
    (hXm' : ∀ J r C lab ex s4, Measurable fun ω =>
      cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax (Jw J))
        (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4)
    (hcov : ∀ j, ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r (1 + 1 / Real.log X₀)
          (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) Atop Eu
          (Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s))) (τ r) (exExcess ex)
          (r - C.card) l (fun ω => cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax
            (Jw J)) (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4)) :
    P ({ω | ∃ J ∈ W, Covers.rank (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) < r₀ ∧
      (r₀ : ℝ) + Covers.phi (Real.exp (logc sH (Real.log X₀) s))
        (Real.exp (logc sH (Real.log X₀) s / 2)) r₀ ≤
          (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)).card} ∩ Good) ≤
      ENNReal.ofReal (Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-3 : ℝ)) :=
  theorem_6_23a_all P hGood W (fun J ω => windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J))
    (fun J ω => zero_notMem_windowVecs _ _ _ _ _ _) hΛ hsH hval hs hr0 hD1 hr₀ hDle
    (fun J ω v hv => windowVecs_deg hv) hXm0 hXmlo hXmhi τl hτlXm hτi τ hτ hlam0 hrlam hCh hBτ
    hB hEu hEuA hACh hlam hW hmeas
    (fun J r C lab ex s4 ω => cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax (Jw J))
      (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4) hXm'
    (fun j k => configSkeletonReduction W dec q X₀ D Dmax Jw hq1 hJz
      (fun ℓ => le_trans (by positivity) (hτi ℓ)) hτq)
    hcov

/-- **Proposition 6.11 for the window model**, with Theorem 6.23(a) (`theorem_6_23a_model`)
inserted for the cap input: `L = e^{2 log Λ + s}`, `z = e^L`, `c = e^{logc}`, `Q = e^{logc/2}`.
The bound `#(N ∩ J) ≤ |S(J)| + 1`, both reductions to skeletons, `0 ∉ S(J)` and `deg ≤ D` are
proved; the residual inputs are the two skeleton bounds (Lemma A.5 + Theorem A.10):
`SkeletonBound` for `skelCount` (cover `C = B'`) and `CoverSkeletonBound` for `cfgSkelCount`,
measurability, and the parameter bounds. -/
theorem prop_6_11_window {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Good : Set Ω}
    (hGood : MeasurableSet Good) (W : Finset ι) (dec : Ω → Finset (Fin N))
    (q : Ω → Fin N → ℝ) (Dmax : ℕ) (Jw : ι → Set ℝ) (a : ι → ℝ) {δ : ℝ}
    (hJ : ∀ J, Jw J ⊆ Set.Ico (a J) (a J + δ)) (hδ : δ < 1) {X₀ : ℕ}
    (hΛ : 10 ^ 8 ≤ Real.log X₀) {sH s Xm : ℝ} (hsH : sH ∈ Set.Ioo (5.9745 : ℝ) 5.9746)
    (hval : gstar sH = gTarget) (hs : -Real.log (Real.log X₀) ≤ s) {r₀ D : ℕ} (hD1 : 1 ≤ D)
    (hr₀lo : Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * Real.log (Real.exp (2 * Real.log (Real.log X₀) + s))) + 3 ≤ r₀)
    (hr₀ : (r₀ : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
      (3 * (2 * Real.log (Real.log X₀) + s)) + 4)
    (hDle : (D : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s) / Real.log X₀)
    (hXm0 : 0 < Xm) (hXmlo : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log Xm)
    (hXmhi : Real.log Xm ≤ Real.log X₀)
    (τl : Fin (r₀ * D) → ℝ) (hτlXm : ∀ i, Xm ≤ τl i)
    (hτi : ∀ i : Fin (r₀ * D), (((i : ℕ) : ℝ) + 1) / 2 ≤ τl i)
    (hq1 : ∀ ω, ∀ n ∈ dec ω, 1 ≤ q ω n)
    (hJz : ∀ J ∈ W, Jw J ⊆
      Set.Iic (2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s)) + 1))
    (hτq : ∀ ω, ∀ n ∈ dec ω, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ ((dec ω).filter (· < n)).card →
      τl ℓ ≤ q ω n)
    {Ch B lam Atop Eu : ℝ} (τ : (r : ℕ) → Fin r → ℝ) (hτ : ∀ r, ∀ i, 1 < τ r i)
    (hlam0 : 0 ≤ lam) (hrlam : 1 + r₀ * lam ≤ Real.exp (2 * Real.log (Real.log X₀) + s))
    (hCh : Ch ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s))
    (hBτ : ∀ r < r₀, ∏ i, (1 - (τ r i)⁻¹)⁻¹ ≤ B)
    (hB : B ≤ 2.1 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (1.02 : ℝ))
    (hEu : 0 < Eu) (hEuA : Eu ≤ Atop) (hACh : Atop ≤ Ch) (hlam : Real.log (Atop / Eu) ≤ lam)
    (hW : (W.card : ℝ) ≤ 2 * Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s)) /
      (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) + 1)
    {θ A Eu' A_R b : ℝ} {H : ℝ → ℝ} (hH : SlotHyp H X₀) (hθ : 0 < θ) (hb : 0 < b)
    (hθab : θ * Real.exp ((3 * H X₀ + 2) / X₀) * b ≤ 1.01) (hAR0 : 0 ≤ A_R)
    (hAR : A_R ≤ 1.8 * (Real.exp (2 * Real.log (Real.log X₀) + s) + 4))
    (hu : 1 + r₀ / (X₀ : ℝ) ≤ 2 * Real.exp (2 * Real.log (Real.log X₀) + s))
    (hEu' : 0 < Eu') (hEuA' : Eu' ≤ A) (hAtop' : A ≤ A_R * b)
    (hXm : ∀ J (E : Matrix (Fin r₀) (Fin r₀) ℕ) l,
      Measurable fun ω => skelCount (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) E l)
    (hmeasR : ∀ J ∈ W, Measurable fun ω =>
      (rankFullCount r₀ (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) : ℝ≥0∞))
    (hmeas : ∀ j k, ∀ J ∈ W, Measurable fun ω =>
      (configCount r₀ j k (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) : ℝ≥0∞))
    (hXm' : ∀ J r C lab ex s4, Measurable fun ω =>
      cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax (Jw J))
        (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4)
    (hbound : ∀ J ∈ W, SkeletonBound P Good r₀ θ
      (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) A Eu'
      (fun j => tauSlot H X₀ j)
      (fun E l ω => skelCount (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) E l))
    (hcov : ∀ j, ∀ J ∈ W, ∀ r < r₀, ∀ C ∈ CSet r j, ∀ lab ex s4, ExOK C ex →
      ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound P Good r (1 + 1 / Real.log X₀)
          (4 * Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-6 : ℝ)) Atop Eu
          (Real.exp (Real.exp (2 * Real.log (Real.log X₀) + s))) (τ r) (exExcess ex)
          (r - C.card) l (fun ω => cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax
            (Jw J)) (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4)) :
    P ({ω | ∃ J ∈ W, (r₀ : ℝ) + Covers.phi (Real.exp (logc sH (Real.log X₀) s))
        (Real.exp (logc sH (Real.log X₀) s / 2)) r₀ + 1 <
          (windowElems (dec ω) (q ω) X₀ D Dmax (Jw J)).card} ∩ Good) ≤
      ENNReal.ofReal (Real.exp (2 * Real.log (Real.log X₀) + s) ^ (-2 : ℝ)) := by
  have hΛ0 : (0 : ℝ) < Real.log X₀ := lt_of_lt_of_le (by norm_num) hΛ
  have hLΛ : Real.log X₀ ≤ Real.exp (2 * Real.log (Real.log X₀) + s) := by
    calc Real.log X₀ = Real.exp (Real.log (Real.log X₀)) := (Real.exp_log hΛ0).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hL : (465 : ℝ) ≤ Real.exp (2 * Real.log (Real.log X₀) + s) := by
    have : (465 : ℝ) ≤ 10 ^ 8 := by norm_num
    linarith
  have hr0 : 1 ≤ r₀ := by
    have h0 : 0 ≤ Real.exp (2 * Real.log (Real.log X₀) + s) /
        (3 * Real.log (Real.exp (2 * Real.log (Real.log X₀) + s))) := by
      have : 0 < Real.log (Real.exp (2 * Real.log (Real.log X₀) + s)) :=
        Real.log_pos (by linarith)
      positivity
    have : (1 : ℝ) ≤ r₀ := by linarith
    exact_mod_cast this
  refine prop_6_11_model P hGood W dec q hq1 X₀ D Dmax Jw a hJ hδ r₀ hH rfl hL
    (Real.exp_pos _) le_rfl hθ hb hθab hAR0 hAR hu hr₀lo hW hEu' hEuA' hAtop' hXm hmeasR hbound
    ?_
  exact theorem_6_23a_model P hGood W dec q Dmax Jw hΛ hsH hval hs hr0 hD1 hr₀ hDle hXm0 hXmlo
    hXmhi τl hτlXm hτi hq1 hJz hτq τ hτ hlam0 hrlam hCh hBτ hB hEu hEuA hACh hlam hW hmeas hXm'
    hcov

end RankFull.Config
