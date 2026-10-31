module

public import RequestProject.Beurling.Model.MeasData

/-!
# The heights and the target of measurable prime data are measurable

For measurable, locally finite prime data with values `≥ 2` (`DFam`):

* `measurable_gammaD` : **the designed heights `γ_k` are measurable** (Lemma 4.8: "`γ_k` is defined
  for every `ω` by the rule of Lemma 4.8, as a measurable function of the system on `[1, x_k)`").
  By strong induction on `k`: `γ_k` is the least good height of `D̂_{<a_k}`, which is computed from
  `N` and the target on `(0, a_k]` with `γ_j`, `j < k` (`designedGammaN_rec`); `D̂_{<a_k}(s)` is
  measurable in `ω` (`measurable_earlyNoise`) and continuous in `s` (`continuous_earlyNoise`), and
  the least good height is measurable in the data (`measurable_chooseHeight`);
* `measurable_targetD` : the target (6) of the data is jointly measurable in `(ω, x)`.
-/

@[expose] public section

open MeasureTheory Set Real Target Oscillation Absorbed Construction DesignedZero Decomp
  AbsorbEmpty CaplLink QueueMono

namespace BModel

variable {Ω : Type*} [MeasurableSpace Ω] {θ : ℝ} {X₀ : ℕ}

lemma measurable_amplitudes {g : Ω → ℕ → ℝ} (hg : ∀ j, Measurable fun ω => g ω j) (j : ℕ) :
    Measurable fun ω => amplitudes θ kappa0Param (switchOn X₀) (g ω) j := by
  unfold amplitudes amplitudeOf
  exact measurable_const.div (hg j)

section Heights

variable (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
  (hHB : ShortIntervalPNTFrom X₀) {D : Ω → PrimeData} (hD : DFam D)
  (hL : ∀ ω, LocFinD (D ω)) (hP : ∀ ω, Pos2 (D ω))
include hθ hX hD hL hP

/-- The lag `N - T` with measurable heights is jointly measurable. -/
lemma measurable_lag_fam {g : Ω → ℕ → ℝ} (hg : ∀ j, Measurable fun ω => g ω j) :
    Measurable fun p : Ω × ℝ => lagN (NCount X₀ (D p.1)) θ X₀ (kappaParam X₀)
      (absSet X₀ (D p.1)) (uA θ) (amplitudes θ kappa0Param (switchOn X₀) (g p.1)) (g p.1)
      (switchOn X₀) p.2 := by
  unfold lagN
  refine (measurable_NCount hD hL hP).sub ?_
  rw [show (fun p : Ω × ℝ => targetOf θ X₀ (kappaParam X₀) (absSet X₀ (D p.1)) (uA θ)
      (amplitudes θ kappa0Param (switchOn X₀) (g p.1)) (g p.1) (switchOn X₀) p.2) =
      fun p : Ω × ℝ => target X₀ (kappaParam X₀) (countA (absSet X₀ (D p.1)))
        (absorbedDensityCap (thetaB θ) (absSet X₀ (D p.1)) (uA θ))
        (osc θ (amplitudes θ kappa0Param (switchOn X₀) (g p.1)) (g p.1) (switchOn X₀)) p.2
      from rfl]
  exact measurable_target_fam X₀ _ (cnt := fun ω => countA (absSet X₀ (D ω)))
    (rho := fun ω => absorbedDensityCap (thetaB θ) (absSet X₀ (D ω)) (uA θ))
    (R := fun ω => osc θ (amplitudes θ kappa0Param (switchOn X₀) (g ω)) (g ω) (switchOn X₀))
    (measurable_countA hD hL hP hX)
    (measurable_rhoCap hD hL hP hX (by linarith [hθ.1]))
    (measurable_osc_fam hX (measurable_amplitudes (θ := θ) (X₀ := X₀) hg) hg)

include hHB in
/-- **The designed heights are measurable.** -/
theorem measurable_gammaD (k : ℕ) : Measurable fun ω => gammaD θ X₀ (D ω) k := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) ≤ X₀ := (one_lt_of_logX hX0 hX).le
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1
  have hκ : 0 < kappaParam (X₀ : ℝ) := kappaParam_pos (by linarith)
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  set g : Ω → ℕ → ℝ := fun ω i => if i < k then gammaD θ X₀ (D ω) i else 0 with hgdef
  have hg : ∀ i, Measurable fun ω => g ω i := by
    intro i
    by_cases hi : i < k
    · simp only [hgdef, if_pos hi]; exact IH i hi
    · simp only [hgdef, if_neg hi]; exact measurable_const
  set F : Ω → ℂ → ℂ := fun ω => earlyN (NCount X₀ (D ω)) θ X₀ (kappaParam X₀)
    (absSet X₀ (D ω)) (uA θ) (amplitudes θ kappa0Param (switchOn X₀) (g ω)) (g ω)
    (switchOn X₀) (constructionScale X₀) k with hF
  have hrec : (fun ω => gammaD θ X₀ (D ω) k) = fun ω =>
      chooseHeight X₀ (kappaParam X₀) (F ω) (heightScale θ kappa0Param (switchOn X₀ k)) := by
    funext ω
    unfold gammaD
    rw [designedGammaN_rec]
    rfl
  rw [hrec]
  obtain ⟨-, ha0, hak, -⟩ := constructionScale_spec hX0 hX k
  have ha1 : 1 ≤ constructionScale (X₀ : ℝ) k := by
    linarith [(constructionScale_spec hX0 hX k).1]
  refine measurable_chooseHeight X₀ hκ (heightScale_switchOn_pos θ hX1 k)
    (fun s => ?_) (fun ω => ?_)
  · exact measurable_earlyNoise (measurable_lag_fam hθ hX hD hL hP hg) _ s
  · -- continuity: on `(0, a_k]` the lag is `N - T` for the data
    have hv := tvalid_targetD hθ hX hHB (D ω) (hL ω)
    have he : F ω = earlyNoise (fun x => NCount X₀ (D ω) x - targetD θ X₀ (D ω) x)
        (constructionScale X₀ k) := by
      simp only [hF, earlyN]
      refine earlyNoise_congr ha0 fun x hx hxa => ?_
      have := lagN_congr_lt (NCount X₀ (D ω)) (θ := θ) (κ := kappaParam X₀)
        (A := absSet X₀ (D ω)) (u := uA θ)
        (α := amplitudes θ kappa0Param (switchOn X₀) (g ω)) (γ := g ω)
        (α' := alphaD θ X₀ (D ω)) (γ' := gammaD θ X₀ (D ω)) (switchOn_spacing _) hX1n
        (switchOn_zero_ge _) (k := k) (fun i hi => by simp [amplitudes, alphaD, hgdef, hi])
        (fun i hi => by simp [hgdef, hi]) hx (hxa.trans hak)
      rw [this]; rfl
    rw [he]
    have hNm : Measurable fun x => NCount X₀ (D ω) x :=
      (measurable_NCount hD hL hP).comp (f := fun x : ℝ => (ω, x))
        (measurable_const.prodMk measurable_id)
    refine continuous_earlyNoise ha1 (hNm.sub hv.mono.measurable) ?_
    refine ⟨NCount X₀ (D ω) (constructionScale X₀ k) + |targetD θ X₀ (D ω) 1| +
      |targetD θ X₀ (D ω) (constructionScale X₀ k)|, fun x hx => ?_⟩
    have hN0 : 0 ≤ NCount X₀ (D ω) x := Nat.cast_nonneg _
    have hsub : elemsLe X₀ (D ω) x ⊆ elemsLe X₀ (D ω) (constructionScale X₀ k) :=
      fun e he => ⟨he.1, he.2.trans hx.2⟩
    have hN1 : NCount X₀ (D ω) x ≤ NCount X₀ (D ω) (constructionScale X₀ k) := by
      unfold NCount
      exact_mod_cast Set.ncard_le_ncard hsub (finite_le hL hP ω _)
    have hT1 := hv.mono hx.1
    have hT2 := hv.mono hx.2
    set T1 := targetD θ X₀ (D ω) 1
    set Ta := targetD θ X₀ (D ω) (constructionScale X₀ k)
    have hTx : |targetD θ X₀ (D ω) x| ≤ |T1| + |Ta| :=
      abs_le.mpr ⟨by linarith [neg_abs_le T1, abs_nonneg Ta],
        by linarith [le_abs_self Ta, abs_nonneg T1]⟩
    calc |NCount X₀ (D ω) x - targetD θ X₀ (D ω) x|
        ≤ |NCount X₀ (D ω) x| + |targetD θ X₀ (D ω) x| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg hN0]; linarith

include hHB in
/-- **The target of measurable data is jointly measurable.** -/
theorem measurable_targetD :
    Measurable fun p : Ω × ℝ => targetD θ X₀ (D p.1) p.2 := by
  have hγ := measurable_gammaD hθ hX hHB hD hL hP
  have hα : ∀ j, Measurable fun ω => alphaD θ X₀ (D ω) j :=
    measurable_amplitudes (θ := θ) (X₀ := X₀) hγ
  have hR := measurable_osc_fam (θ := θ) hX hα hγ
  have hc := measurable_countA hD hL hP hX
  have hr := measurable_rhoCap hD hL hP hX (by linarith [hθ.1] : 0 < θ)
  have h := measurable_target_fam (cnt := fun ω => countA (absSet X₀ (D ω)))
    (rho := fun ω => absorbedDensityCap (thetaB θ) (absSet X₀ (D ω)) (uA θ))
    (R := fun ω => osc θ (alphaD θ X₀ (D ω)) (gammaD θ X₀ (D ω)) (switchOn X₀))
    X₀ (kappaParam X₀) hc hr hR
  exact h

end Heights

end BModel

end
