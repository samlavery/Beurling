module

public import RequestProject.Beurling.Model.MarginFinal
public import RequestProject.Beurling.Model.HoC
public import RequestProject.Beurling.Noise.RML15Eta

/-!
# Corollary 2.2 from eq. (84) alone

`restMarginR_c` builds the last open inputs `RestMarginR` (Step 4 of Proposition 5.38 at
`E_S = 0.0014`): `so = 10⁻²⁰` (`ho_c`, the oscillation of `T_c`), `sη = s_η` (`RML15.hη_canon`),
`so + 2 s_η ≤ 0.0013` (`RML15.hsize_of`). So `Theorem21InputsH` holds given (84)
(`theorem21InputsH_proved`), and `corollary_2_2_complete : Huxley84 → ¬ QuestionQ`.
`theoremA_full : Huxley84 → Theorem21` is Theorem A for every `θ ∈ [1/20, 1/2 - 10⁻⁴]`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP KR.Chain
  CaplLink Queue6

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- **The inputs `RestMarginR`** on `Good(< t) ∩ NiceEv`, `X₀ ≤ b ≤ t`, with (H_BS) on
`[1, Zc b]`. -/
noncomputable def restMarginR_c (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t) (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) : RestMarginR θ X₀ ω b :=
  have hT := tnpR hc hev hbs hN.2.1 hX1
  { so := 1 / 10 ^ 20
    sη := RML15.sηc X₀
    ho := fun t' ht' htb => ho_c hc hev hb hbt hQC hE1 hN hT (by
      have h1 := RML15.canonP_T0_ge hc epsH RML13.ESH (jzX X₀)
      have h2 := Xm_half hc
      linarith) htb
    hη := RML15.hη_canon hc hev hb hT epsH RML13.ESH (jzX X₀)
    hsize := RML15.hsize_of hc hT (by norm_num) }

/-- **`Theorem21InputsH` holds** given eq. (84). -/
theorem theorem21InputsH_proved (h84 : BaseRange.Huxley84) : Theorem21InputsH := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := BaseRange.shortIntervalPNT_of_huxley h84
  refine ⟨max x₁ (Real.exp (10 ^ 8 + 1)), fun X₀ hev h2 m a b hadm => ?_⟩
  have h2b : x₁ ≤ X₀ := (le_max_left _ _).trans h2
  have h2c : Real.exp (10 ^ 8 + 1) ≤ X₀ := (le_max_right _ _).trans h2
  have hlog1 : 10 ^ 8 + 1 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h2c
    rwa [Real.log_exp] at this
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono h2b⟩
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; exact this
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  have hb : (X₀ : ℝ) ≤ b := (X₀_le_uS (X₀ := X₀) (by linarith) m).trans hadm.1
  filter_upwards [hnice] with ω hN hG
  have hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat := hG.1
  have hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n := fun n hn =>
    mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
  have hbs := hbs_Zc hc hev hb hQC hE1 hN
  have hb0 : (0 : ℤ) ≤ b := by
    have : (0 : ℝ) ≤ b := le_trans hX0 hb
    exact_mod_cast this
  have hbt : (b : ℝ) ≤ ((tE2 b : ℕ) : ℝ) := by
    unfold tE2; rw [show ((b.toNat : ℕ) : ℝ) = (b : ℝ) by exact_mod_cast Int.toNat_of_nonneg hb0]
  exact ⟨restMarginR_c hc hev hb hbt hQC hE1 hN hbs hlog1⟩

/-- **Corollary 2.2** from eq. (84) (Heath-Brown's short-interval theorem, `Huxley84`) alone. -/
theorem corollary_2_2_complete (h84 : BaseRange.Huxley84) : ¬ QuestionQ :=
  corollary_2_2_hux h84 (theorem21InputsH_proved h84)

/-- **Theorem A (Theorem 2.1) for every `θ ∈ [1/20, 1/2 - 10⁻⁴]`**, from eq. (84) alone:
for each such `θ` there is `X_Hux` such that for every even `X₀ ≥ max(e^{10⁸}, X_Hux)` the random
system of Section 3 satisfies (i) `|N(x) - x| ≤ C x^θ + 3 x^θ log* x + x^η` and (ii) the designed
zeros `Re ρ_k = 1 - (log log x_k + O(1))/log x_k`, `log Im ρ_k = (1-θ) log x_k - log log x_k + O(1)` on an event of probability
`≥ 1 - 1.5/log X₀` (`Theorem21`, `TheoremAConclusion`). The absorption window is
`h(u) = u^{θ_b}`, `θ_b = min(θ, max(θ/2, 1/8))` (`thetaB`). -/
theorem theoremA_full (h84 : BaseRange.Huxley84) : Theorem21 :=
  Queue6.theorem21_of_X (BaseRange.shortIntervalPNT_of_huxley h84)
    (Queue6.theorem21InputsX_of_Y (Queue6.theorem21InputsY_of_Z
      (theorem21InputsZ_hux h84 (theorem21InputsH_proved h84))))

/-- **Theorem 2.1 (Theorem A)** from eq. (84) alone: the full conclusion, (i) and (ii), for the
realised systems on an event of probability `≥ 1 - 1.5/log X₀`. -/
theorem theorem21_complete (h84 : BaseRange.Huxley84) : Theorem21 :=
  theorem21_of_S (BaseRange.shortIntervalPNT_of_huxley h84) tiesNull
    (Queue6.theorem21InputsS_of_X (BaseRange.shortIntervalPNT_of_huxley h84)
      (Queue6.theorem21InputsX_of_Y (Queue6.theorem21InputsY_of_Z
        (theorem21InputsZ_hux h84 (theorem21InputsH_proved h84)))))

/-- **Theorem A(ii), the designed zeros at `1·log log`** (eq. (ampl) with the constant relative
amplitude `κ'_k = κ₀ = X₀⁻¹ ∈ [X₀⁻¹, Λ⁻⁵]`), from eq. (84) alone: for every
`θ ∈ [1/20, 1/2 - 10⁻⁴]` and every even `X₀ ≥ max(e^{10⁸}, X_Hux)`, on an event `G` of probability
`≥ 1 - 1.5/log X₀`, the zeta function of the realised system `P(ω)` continues to a punctured
half-plane `Re s > a`, `a < 1`, and has zeros `ρ_k` there with, along `x_k → ∞`,
`Re ρ_k = 1 - (log log x_k + O_{X₀}(1))/log x_k` and
`log Im ρ_k = (1 - θ) log x_k - log log x_k + O_{X₀}(1)` (so `x_k` is pinned by the height of
`ρ_k`, and `1 - Re ρ_k ≍ (1-θ) log log Im ρ_k / log Im ρ_k`). -/
theorem theoremA_ii_complete (h84 : BaseRange.Huxley84) :
    ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
      Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
        IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
        ∀ ω ∈ G, ∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, (P ω).IsZetaContinuation a F ∧
          ∃ (ρ : ℕ → ℂ) (xk : ℕ → ℝ) (C : ℝ), Filter.Tendsto xk Filter.atTop Filter.atTop ∧
            (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
            (∀ k, |(1 - (ρ k).re) * Real.log (xk k) - Real.log (Real.log (xk k))| ≤ C) ∧
            ∀ k, |Real.log (ρ k).im -
              ((1 - θ) * Real.log (xk k) - Real.log (Real.log (xk k)))| ≤ C := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := theorem21_complete h84 θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => (hP ω hω).2⟩

end BModel

end
