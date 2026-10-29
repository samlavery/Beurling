module

public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.BaseRange.RestBaseR
public import RequestProject.Beurling.BaseRange.HjbR
public import RequestProject.Beurling.Model.G1BQ6
public import RequestProject.Beurling.Model.G1BSec5
public import RequestProject.Beurling.Model.MarginH

/-!
# The top level: Corollary 2.2 from eq. (84) and the open inputs

The classical hypothesis is `BaseRange.Huxley84` (eq. (84), Heath-Brown's short-interval
theorem; §7.1). It gives `ShortIntervalPNT` (`shortIntervalPNT_of_huxley`) and, beyond a
threshold, the group `RestBase` (`huxley_threshold`). Proposition 5.33 (`j_{X₀} ≤ 0.4209`) is
`BaseRange.hjb_Rc`. The remaining open inputs are `RestRes` (Proposition 5.35, Lemma 5.34, the
margin identity) and `RestMargin` (Proposition 5.38, steps 1–6), owned by the other agents.

Main result: `corollary_2_2_hux : Huxley84 → Theorem21InputsH → ¬ QuestionQ`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR KR.TNP KR.Chain
  CaplLink Queue6

namespace BModel

/-- **The open inputs of Proposition 5.35(B)** at `(ω, b)` (the remaining inputs of
`RML10.sec5_of` at the Model's bounds, `g1Sec5_c`), at every range-(B) start `y ≤ b + H(b)`. -/
structure RestResH (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) where
  /-- §5: Propositions 5.26, 5.18(iii), (osc), 5.20 and Theorem 5.24 at the window heights
  (`KR.RML10.WinAt`) -/
  W : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b → (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y →
    ∀ s, y / 4 ≤ s → s ≤ KR.RML9.Ytop X₀ y (deltaB θ X₀ ω y) →
      KR.RML10.WinAt (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀ (TcR θ X₀ ω (jzX X₀)) s
  /-- Model (needs §5's Lemma 5.20 block sums of `s_η`): `S ≤ 10⁻²⁰` on `J` (first bullet of
  Lemma 5.34, (sw-sums)) -/
  hSb : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b → (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y →
    ∀ z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y), SK θ X₀ ω (Queue6.nbQ X₀) z ≤ 1 / 10 ^ 20
  /-- Model (idem): `G ≤ e^{-41} + 2·10⁻²²` on `J` (second bullet, (osc), (sw-sums)) -/
  hGbd : ∀ y, (X₀ : ℝ) ≤ y → y ≤ b + Queue6.Hc X₀ b → (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y →
    ∀ z ∈ KR.RML9.Jint y (deltaB θ X₀ ω y),
      Gsum θ X₀ ω (Queue6.nbQ X₀) z ≤ Real.exp (-41) + 2 / 10 ^ 22

variable (θ X₀) in
/-- **The open inputs** at `(ω, b)`: `RestResH` (Proposition 5.35(B)) and `RestMarginH`
(Proposition 5.38, Steps 4–6) at `ν̄ = nbQ`. -/
def OthersInputsH (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) (b : ℝ) : Prop :=
  Nonempty (RestResH θ X₀ ω b) ∧ Nonempty (RestMarginH θ X₀ ω b (Queue6.nbQ X₀))

/-- **Theorem 2.1, hypothesis**: for `X₀` beyond some threshold, a.s. on `Good(< b)` for every
admissible window `[a, b)`, the open inputs `OthersInputsH`. -/
def Theorem21InputsH : Prop :=
  ∀ θ ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000), ∃ X : ℝ, ∀ X₀ : ℕ, Even X₀ → X ≤ X₀ →
    ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → OthersInputsH θ X₀ ω b

/-- `Theorem21InputsH` implies `Theorem21InputsZ`, given eq. (84). -/
theorem theorem21InputsZ_hux (h84 : BaseRange.Huxley84) (h : Theorem21InputsH) :
    Theorem21InputsZ := by
  intro θ hθ
  obtain ⟨x₁, hx₁⟩ := BaseRange.shortIntervalPNT_of_huxley h84
  obtain ⟨XH, -, hXH⟩ := BaseRange.huxley_threshold h84
  obtain ⟨X, hX⟩ := h θ hθ
  refine ⟨max (max (max X XH) x₁) (Real.exp (10 ^ 8 + 1)), fun X₀ hev h1 h2 => ?_⟩
  have h2a : X ≤ X₀ := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans h2))
  have h2h : XH ≤ X₀ := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans h2))
  have h2b : x₁ ≤ X₀ := (le_max_right _ _).trans ((le_max_left _ _).trans h2)
  have h2c : Real.exp (10 ^ 8 + 1) ≤ X₀ := (le_max_right _ _).trans h2
  have hRest := hX X₀ hev h2a
  have hlog1 : 10 ^ 8 + 1 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h2c
    rwa [Real.log_exp] at this
  have hlog : 10 ^ 8 ≤ Real.log X₀ := by linarith
  have hc : Cond θ X₀ := ⟨hθ, hlog, hx₁.mono h2b⟩
  have hnice : ∀ᵐ ω ∂jitterMeasure, ω ∈ NiceEv θ X₀ := by
    have := niceEv_compl_null hc hev
    rw [ae_iff]; simpa using this
  have hR : ∀ (m : ℕ) (a b : ℤ), Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure,
      ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → Nonempty (RealMarginLoc hc ω (b : ℝ)) := by
    intro m a b hadm
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
    have hb : (X₀ : ℝ) ≤ b := (X₀_le_uS (X₀ := X₀) (by linarith) m).trans hadm.1
    filter_upwards [hRest m a b hadm, hnice, Queue6.hS2Epm_R hc hev, Queue6.nu522_tE2 hc hev,
      Queue6.nu522_point hc hev] with ω hω hN hEp hnu hpt hG
    have hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat := hG.1
    have hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n := fun n hn =>
      mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) hn
    obtain ⟨⟨Rh⟩, ⟨Rm⟩⟩ := hω hG
    have hbs := hbs_Zc hc hev hb hQC hE1 hN
    have hb0 : (0 : ℤ) ≤ b := by
      have : (0 : ℝ) ≤ b := le_trans hX0 hb
      exact_mod_cast this
    have hbt : (b : ℝ) ≤ ((tE2 b : ℕ) : ℝ) := by
      unfold tE2; rw [show ((b.toNat : ℕ) : ℝ) = (b : ℝ) by exact_mod_cast Int.toNat_of_nonneg hb0]
    have hOp := opR hc hev hbs hN.2.1 hlog1
    let Rs : RestRes θ X₀ ω b :=
      { g1Q := fun y hy hyb hyL => g1ResQueue6_c hc hev hb hG hbt hN hbs hlog1 hOp
          (fun r hr hrb => hpt _ hG hN hOp r hr (hrb.trans hbt)) hy hyb hyL
        g1S := fun y hy hyb hyL hO' => g1Sec5_c hc hev hb hG hbt hN hbs hlog1 (hnu b hG) hO'
          hy hyb hyL (Rh.W y hy hyb hyL) (Rh.hSb y hy hyb hyL) (Rh.hGbd y hy hyb hyL)
        nb := Queue6.nbQ X₀
        hnu := hnu b hG }
    have hO : OthersInputs θ X₀ ω b :=
      ⟨hXH X₀ h2h θ ω b, ⟨⟩, Rs, ⟨restMargin_of hc hev hb hN hbs hlog1 Rm⟩⟩
    exact realMarginLoc_of_others hc hev hG hN hbt hb hbs hlog1 (hEp _ hG hN)
      (fun hH => hin_R hc hev hbs hN.2.1 hlog1 hb hH)
      (fun hH => BaseRange.hjb_Rc hc hev hN.2.1 hlog1 hb hbs (by norm_num [epsH])
        (by norm_num [epsH]) (CapHSlopeProof.capHSlope (by linarith))
        (CapHDiffProof.capHDiff (by linarith)) hH (by norm_num [epsH, lamH])
        (by norm_num [lamH])) hO
  have hcore := s2Core hc hev
  exact ⟨{ compE3 := e3CompBound hc hev
           s2E3 := e3S2Bound_of hc hev hcore
           r1Ident := r1Ident_of_marginOn hc hev (e3Family θ X₀) (hPM_of_loc hc hev _ hR)
           s2E2 := e2S2Bound_of hc hev hcore }⟩

/-- **Corollary 2.2** from eq. (84) and the open inputs `Theorem21InputsH`. -/
theorem corollary_2_2_hux (h84 : BaseRange.Huxley84) (h : Theorem21InputsH) : ¬ QuestionQ :=
  corollary_2_2_of_Z (BaseRange.shortIntervalPNT_of_huxley h84) (theorem21InputsZ_hux h84 h)

end BModel

end
