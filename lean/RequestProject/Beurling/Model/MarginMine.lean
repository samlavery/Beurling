module

public import RequestProject.Beurling.Model.S2Hbs
public import RequestProject.Beurling.Noise.MarginRealLoc

/-!
# The Model fields of `RealMarginLoc`: (H_BS) on `Good(< b)`, the horizon `Z`, and the simple
fields

* `hbs_low` : (H_BS) on `[1, X₀⁻]` holds **surely** on `NiceEv` (the only height `≥ X₀⁻` read is
  `X₀⁻ < X₀`, where `N ≤ N(X₀) ≤ X₀ + X₀^{lag}` by the lag bound at `X₀`, whose queue is
  `Q_0 = 0`);
* `Zc X₀ b` : the horizon, `(b - 2)/4` for `b ≥ 4X₀ + 2` and `X₀⁻` below; `Zc_facts` :
  `X₀⁻ ≤ Z`, `2500 ≤ Z`, `18 (b + H(b)) ≤ Z²`, `2(b + H(b))/X₀⁻ ≤ Z`;
* `hbs_Zc` : (H_BS) on `[1, Zc b]` on `QC(< b) ∩ {E1 of time < b} ∩ NiceEv` (`hbs_QE` for
  `b ≥ 4X₀ + 2`, `hbs_low` below).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink QueueMono Absorbed Queue6 SlotModel

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section Low

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- **(H_BS) on `[1, X₀⁻]`, surely on `NiceEv`** (04a-setup.tex, (H_BS), at the bottom of the
range): below `X₀⁻` the realised system is `ℕ`, and at `X₀⁻ < X₀`,
`|N(X₀⁻) - ⌊X₀⁻⌋| ≤ ε₁(X₀⁻) X₀⁻` from `N(X₀) ≤ X₀ + X₀^{lag}` (the lag bound at `X₀`, where the
queue is `Q_0 = 0`). -/
theorem hbs_low {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) (h0 : Std θ X₀ ω) :
    (realisedSystem h0.limModel (capH X₀) ω).HBS (Xm X₀) (Xm X₀) (1 / 1000) (1 / 1000)
      (hbsEps X₀) := by
  obtain ⟨hU, -, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have hTX := h0.limModel_T_X₀
  -- the queue at the slot of `X₀` is `Q_0 = 0`
  have hidx : M.slotIdx X₀ = 0 := by
    unfold SlotModel.slotIdx
    rw [hMdef, hTX]
    apply Nat.floor_eq_zero.mpr
    have := h0.limModel.hϑ0
    linarith
  have hQ : (M.queue (M.slotIdx X₀) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx X₀)) := by
    rw [hidx]
    have h0q : M.queue 0 = 0 := rfl
    rw [h0q]
    push_cast
    unfold queueBScale
    exact queueB_nonneg hX0 hX (le_dyadicScale (by linarith) (le_max_left _ _))
  have hlag := lag_local M hc.hθ.1 hc.hθ.2 hX (realisedSystem M (capH X₀) ω).N Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) le_rfl hQ
  rw [hMdef, hTX] at hlag
  have hNX0 : (realisedSystem M (capH X₀) ω).N X₀ ≤ X₀ + (X₀ : ℝ) ^ lagExponent θ := by
    linarith [(abs_le.mp hlag).2]
  have h4H := four_capH_le hX0 hX (le_refl (X₀ : ℝ))
  have hH1 := capH_ge_one hX0 hX (le_refl (X₀ : ℝ))
  have hfl : ∀ w, 1 ≤ w → w < (X₀ : ℝ) - capH X₀ X₀ / 2 →
      (realisedSystem M (capH X₀) ω).N w = ⌊w⌋₊ :=
    fun w hw1 hw2 => realised_floor_eq hok hU hX h0.limModel_low hw1 hw2
  have hXmh : (X₀ : ℝ) / 2 ≤ X₀ - capH X₀ X₀ / 2 := Xm_half hc
  exact
    { X0m_ge := by
        have : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) / 2 := by
          have := Real.add_one_le_exp (Real.log X₀)
          rw [Real.exp_log (by linarith)] at this; linarith
        unfold Xm; linarith
      eta1_nonneg := by norm_num
      eta1_le := le_rfl
      eta2_nonneg := by norm_num
      eta2_le := le_rfl
      floor_eq := fun v h1 h2 _ => hfl v h1 h2
      err := fun v h1 h2 => by
        unfold Xm at h1 h2
        exact hbs_err_low hX hc.hθ.2 (realisedSystem M (capH X₀) ω).N_mono hfl hNX0 h1
          (by linarith)
      eta2 := fun v h1 _ => hbsEps_mul_log_le hX (by unfold Xm at h1; linarith)
      eta1 := fun x K w hw => hbsEps_dyadic_sum_le hX K w (fun k hk =>
        ⟨(hw k hk).1, (hw k hk).2.1, by unfold Xm at hw; linarith [(hw k hk).2.2.1]⟩) }

end Low

/-! ### The horizon -/

variable (X₀) in
/-- The horizon of (H_BS) on `Good(< b)`: `(b - 2)/4` for `b ≥ 4X₀ + 2`, `X₀⁻` below. -/
noncomputable def Zc (b : ℝ) : ℝ := if 4 * (X₀ : ℝ) + 2 ≤ b then (b - 2) / 4 else Xm X₀

section Hor

variable (hc : Cond θ X₀)
include hc

/-- **The horizon conditions**: `X₀⁻ ≤ Z`, `2500 ≤ Z`, `18 (b + H(b)) ≤ Z²` and
`2 (b + H(b))/X₀⁻ ≤ Z`, for `b ≥ X₀`. -/
theorem Zc_facts {b : ℝ} (hb : (X₀ : ℝ) ≤ b) :
    Xm X₀ ≤ Zc X₀ b ∧ 2500 ≤ Zc X₀ b ∧ 18 * (b + Queue6.Hc X₀ b) ≤ Zc X₀ b ^ 2 ∧
      2 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXmh := Xm_half hc
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_ge_one hX0 hc.hX (le_refl (X₀ : ℝ)); unfold Xm; linarith
  have hXm0 : 0 < Xm X₀ := by linarith
  have hH : Queue6.Hc X₀ b ≤ b / 4 := by
    unfold Queue6.Hc
    rw [max_eq_left hb]
    have := four_capH_le hX0 hc.hX hb
    linarith
  have hH0 : 0 ≤ Queue6.Hc X₀ b := by
    unfold Queue6.Hc; exact capH_nonneg _ _
  unfold Zc
  split_ifs with hbig
  · refine ⟨by linarith, by linarith, ?_, ?_⟩
    · nlinarith
    · rw [div_le_iff₀ hXm0]
      nlinarith
  · push_neg at hbig
    refine ⟨le_rfl, by linarith, ?_, ?_⟩
    · nlinarith
    · rw [div_le_iff₀ hXm0]
      nlinarith

/-- **The horizon condition of Lemma 5.20 in the form `18 y/X₀⁻ ≤ Z`** for `y ≤ b + H(b)`. -/
theorem Zc_18 {b : ℝ} (hb : (X₀ : ℝ) ≤ b) : 18 * (b + Queue6.Hc X₀ b) / Xm X₀ ≤ Zc X₀ b := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXb := X₀_ge_two_pow hc.hX
  have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
  have hXmh := Xm_half hc
  have hXmX : Xm X₀ ≤ X₀ := by
    have := capH_ge_one hX0 hc.hX (le_refl (X₀ : ℝ)); unfold Xm; linarith
  have hXm0 : 0 < Xm X₀ := by linarith
  have hH : Queue6.Hc X₀ b ≤ b / 4 := by
    unfold Queue6.Hc
    rw [max_eq_left hb]
    have := four_capH_le hX0 hc.hX hb
    linarith
  rw [div_le_iff₀ hXm0]
  unfold Zc
  split_ifs with hbig
  · nlinarith
  · push_neg at hbig
    nlinarith

variable (hev : Even X₀)
include hev

/-- **(H_BS) on `[1, Zc b]` on `QC(< b) ∩ {E1 of time < b} ∩ NiceEv`** (04a-setup.tex, (H_BS);
Remark *horizon*), for the realised system `PR θ X₀ ω`. -/
theorem hbs_Zc {b : ℤ} (hb : (X₀ : ℝ) ≤ b) {ω : JitterΩ}
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) b.toNat)
    (hE1 : ∀ n, tE1 X₀ n < b.toNat → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) :
    (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀) := by
  have hU := hN.1
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
  have e : PR θ X₀ ω = realisedSystem h0.limModel (capH X₀) ω := by
    show realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω) = _
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [e]
  unfold Zc
  split_ifs with hbig
  · have hb0 : (0 : ℤ) ≤ b := by
      have : (0 : ℝ) ≤ b := le_trans (Nat.cast_nonneg _) hb
      exact_mod_cast this
    have hbt : ((b.toNat : ℕ) : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb0
    exact hbs_QE hc hev hQC hE1 hN h0 (by linarith) (by rw [hbt]; linarith)
  · exact hbs_low hc hev hN h0

end Hor

end BModel
