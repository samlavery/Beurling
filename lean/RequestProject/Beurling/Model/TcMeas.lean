module

public import RequestProject.Beurling.Model.Choices
public import RequestProject.Beurling.Model.MeasIter

/-!
# `T_c` is measurable (the field `hTm` of `RealMarginLoc`)

`T_c = T'_cont + K_𝒜 ρ̃ - j₀ 1_{[X₀,∞)}` (§5.1, "The jump at `X₀`"):

* `measurable_TpCont` : `T'_cont = 1 - ρ_det - ρ̄_A + R'` on `[X₀, ∞)` (`measurable_rhoDet`,
  `measurable_rhoCap`, `measurable_deriv`);
* `measurable_rhoT` : `ρ̃ = ∑_q H(s_q)⁻¹ 1_{box(s_q)}`;
* `measurable_KAbsR` : `K_𝒜 g` for measurable `g` (a sum over the labels `w ∈ 𝒩(y/X₀⁻)`, written
  as a sum over all `w` with finite support at each `y`);
* `measurable_TcR` : `T_c` at any `j₀`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section

variable (hc : Cond θ X₀)
include hc

/-- `T'_cont` is measurable. -/
lemma measurable_TpCont (ω : JitterΩ) : Measurable (TpCont θ X₀ ω) := by
  unfold TpCont
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  have hD := DF_dfam hc
  have hL : ∀ ω : JitterΩ, LocFinD (DM (Mcl θ X₀ ω) (Ucl ω)) := fun ω =>
    locFinD_DM hc.hX (fun j => clamp01_mem (ω j)) _
  have hP : ∀ ω : JitterΩ, Pos2 (DM (Mcl θ X₀ ω) (Ucl ω)) := fun ω =>
    pos2_DM hc.hX (fun j => clamp01_mem (ω j)) (by rw [Mcl_eq hc]; exact (hc.std ω).limModel_low)
  have hr := measurable_rhoCap hD hL hP hc.hX (θ := θ) (by linarith [hc.hθ.1])
  have hr' : Measurable fun y => absorbedDensityCap (θ / 2)
      (absSet X₀ (DM (Mcl θ X₀ ω) (Ucl ω))) (uA θ) y :=
    hr.comp (f := fun y : ℝ => ((ω, y) : JitterΩ × ℝ)) (measurable_const.prodMk measurable_id)
  rw [show DF θ X₀ ω = DM (Mcl θ X₀ ω) (Ucl ω) from rfl]
  have h1 : Measurable fun y : ℝ => 1 - Target.rhoDet X₀ (kappaParam X₀) y :=
    measurable_const.sub (measurable_rhoDet _ _)
  exact (h1.sub hr').add (measurable_deriv _)

omit hc in
/-- `ρ̃` is measurable. -/
lemma measurable_rhoT (ω : JitterΩ) : Measurable (rhoT θ X₀ ω) := by
  unfold rhoT
  refine ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun k => ?_)
  by_cases hA : ω ∈ lawA θ X₀ k
  · simp only [indicator_of_mem hA]
    exact measurable_const.mul (measurable_one.indicator measurableSet_Ico)
  · simp only [indicator_of_notMem hA]
    exact measurable_const

/-- `K_𝒜 g` is measurable for measurable `g`. -/
lemma measurable_KAbsR (ω : JitterΩ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (KAbsR θ X₀ ω g) := by
  classical
  have hXm : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  set P := PR θ X₀ ω
  set F : ℕ → ℝ → ℝ := fun w y =>
    if w ∈ (NAll P y (Xm X₀)).filter (2 ≤ ·) then
      (if (∀ p ∈ w.primeFactors, twR θ X₀ ω p * Vl P w < y) ∧
        (10 ^ 7 ≤ Real.log y ∧ y / Vl P w < absorbY X₀ y) then g (y / Vl P w) / Vl P w else 0)
    else 0 with hF
  have key : KAbsR θ X₀ ω g = fun y => ∑' w, F w y := by
    funext y
    unfold KAbsR
    rw [tsum_eq_sum (s := (NAll P y (Xm X₀)).filter (2 ≤ ·)) (fun w hw => by
      simp only [hF]; exact if_neg hw)]
    exact Finset.sum_congr rfl fun w hw => by simp only [hF, if_pos hw]; split_ifs <;> rfl
  rw [key]
  refine measurable_tsum_of_finite_support (fun w => ?_) (fun y => ?_)
  · have hmem : MeasurableSet {y : ℝ | w ∈ (NAll P y (Xm X₀)).filter (2 ≤ ·)} := by
      have e : {y : ℝ | w ∈ (NAll P y (Xm X₀)).filter (2 ≤ ·)} =
          {y : ℝ | w ≠ 0 ∧ Vl P w ≤ y / Xm X₀ ∧ 2 ≤ w} := by
        ext y
        simp only [mem_setOf_eq, Finset.mem_filter, KR.Sharp.mem_NAll_iff P hXm]
        tauto
      rw [e]
      exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const
        (measurable_id.div_const _)).inter (MeasurableSet.const _))
    have hcond : MeasurableSet {y : ℝ | (∀ p ∈ w.primeFactors, twR θ X₀ ω p * Vl P w < y) ∧
        (10 ^ 7 ≤ Real.log y ∧ y / Vl P w < absorbY X₀ y)} := by
      have e : {y : ℝ | ∀ p ∈ w.primeFactors, twR θ X₀ ω p * Vl P w < y} =
          ⋂ p ∈ w.primeFactors, {y : ℝ | twR θ X₀ ω p * Vl P w < y} := by
        ext y; simp
      refine MeasurableSet.inter ?_ ((measurableSet_le measurable_const
        Real.measurable_log).inter (measurableSet_lt (measurable_id.div_const _)
          (measurable_absorbY hc.hX)))
      show MeasurableSet {y : ℝ | ∀ p ∈ w.primeFactors, twR θ X₀ ω p * Vl P w < y}
      rw [e]
      exact Finset.measurableSet_biInter _ fun p _ => measurableSet_lt measurable_const
        measurable_id
    exact Measurable.ite hmem (Measurable.ite hcond
      ((hg.comp (measurable_id.div_const _)).div_const _) measurable_const) measurable_const
  · refine ((NAll P y (Xm X₀)).filter (2 ≤ ·)).finite_toSet.subset fun w hw => ?_
    by_contra hn
    exact hw (by simp only [hF]; exact if_neg hn)

/-- **`T_c` is measurable** (the field `hTm` of `RealMarginLoc`), at any `j₀`. -/
theorem measurable_TcR (ω : JitterΩ) (j0 : ℝ) : Measurable (TcR θ X₀ ω j0) := by
  unfold TcR
  exact ((measurable_TpCont hc ω).add (measurable_KAbsR hc ω (measurable_rhoT ω))).sub
    (measurable_const.mul (KR.Chain.ind_measurable _))

end

end BModel
