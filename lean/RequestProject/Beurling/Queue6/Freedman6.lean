module

public import RequestProject.Beurling.Landing

/-!
# Freedman's inequality for bounded counts on a good event (proof of Theorem 6.6(i))

The proof of Theorem 6.6(i) applies Freedman's inequality (73) to counts `Y_k ∈ [0, b]`
(`Y_k = X̃_q(I)`, the truncated count of the prime decided at slot `k + 1`, `b = 2M₁`), in slot
order, with the deterministic pair `(a, v)` obtained after peeling over `ℓ_jit(I)`. The variance
bound `V ≤ b · Comp` is used only on the good event, where the compensator is bounded by R1′.

* `Queue6.condVar_le` : `E[(Y - E[Y|ℱ])² | ℱ] ≤ b E[Y | ℱ]` for `0 ≤ Y ≤ b`;
* `Queue6.freedman_good` : if `∑_{k<N} E[Y_k | ℱ_k] ≤ v/b` a.e. on a set `G` (any set), then
  `P({∑_{k<N} (Y_k - E[Y_k|ℱ_k]) ≥ √(2vλ) + 2bλ/3} ∩ G) ≤ e^{-λ}`;
* `Queue6.freedman_peel` : the peeling over a random integer `ℓ ≤ K` with deterministic
  `v_ℓ`: probability at most `(K + 1) e^{-λ}` (first item of the proof of Theorem 6.6(i));
* `Queue6.count_good` : the form used for part (b) of `Fr(I)` (indicators, `b = 1`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Freedman

namespace Queue6

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- The conditional mean clipped to `[0, b]`. -/
noncomputable def clipB (ℱ : Filtration ℕ m0) (μ : Measure Ω) (b : ℝ) (Y : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  max 0 (min b ((μ[Y k | ℱ k]) ω))

section Bounded

variable {Y : ℕ → Ω → ℝ} {b : ℝ}

omit [IsProbabilityMeasure μ] in
lemma clipB_bounds (hb : 0 ≤ b) (k : ℕ) (ω : Ω) :
    0 ≤ clipB ℱ μ b Y k ω ∧ clipB ℱ μ b Y k ω ≤ b :=
  ⟨le_max_left _ _, max_le hb (min_le_left _ _)⟩

omit [IsProbabilityMeasure μ] in
lemma stronglyMeasurable_clipB (k : ℕ) : StronglyMeasurable[ℱ k] (clipB ℱ μ b Y k) := by
  unfold clipB
  exact (measurable_const.max (measurable_const.min
    (stronglyMeasurable_condExp (m := ℱ k)).measurable)).stronglyMeasurable

lemma integrable_Y (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) (k : ℕ) : Integrable (Y k) μ :=
  Integrable.of_bound ((hmeas k).mono (ℱ.le (k + 1))).aestronglyMeasurable b
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hY0 k ω)]; exact hYb k ω)

lemma integrable_clipB (hb : 0 ≤ b) (k : ℕ) : Integrable (clipB ℱ μ b Y k) μ :=
  Integrable.of_bound ((stronglyMeasurable_clipB k).mono (ℱ.le k)).aestronglyMeasurable b
    (Eventually.of_forall fun ω => by
      have := clipB_bounds (ℱ := ℱ) (μ := μ) (Y := Y) hb k ω
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)

lemma clipB_ae_eq (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) (k : ℕ) :
    clipB ℱ μ b Y k =ᵐ[μ] μ[Y k | ℱ k] := by
  have h0 : 0 ≤ᵐ[μ] μ[Y k | ℱ k] := condExp_nonneg (Eventually.of_forall fun ω => hY0 k ω)
  have h1 : μ[Y k | ℱ k] ≤ᵐ[μ] μ[fun _ => b | ℱ k] :=
    condExp_mono (integrable_Y hY0 hYb hmeas k) (integrable_const b)
      (Eventually.of_forall fun ω => hYb k ω)
  rw [condExp_const (ℱ.le k)] at h1
  filter_upwards [h0, h1] with ω e0 e1
  simp only [clipB, Pi.zero_apply] at e0 e1 ⊢
  rw [min_eq_right e1, max_eq_right e0]

/-- The centred counts `Y_k - E[Y_k | ℱ_k]` are martingale differences bounded by `b`. -/
lemma martDiff_bounded (hb : 0 ≤ b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) :
    MartDiff ℱ μ (fun k ω => Y k ω - clipB ℱ μ b Y k ω) b b where
  meas k := (hmeas k).sub ((stronglyMeasurable_clipB k).mono (ℱ.mono (Nat.le_succ k)))
  le_b k ω := by linarith [hYb k ω, clipB_bounds (ℱ := ℱ) (μ := μ) (Y := Y) hb k ω]
  bdd k ω := by
    rw [abs_le]
    constructor <;> linarith [hY0 k ω, hYb k ω, clipB_bounds (ℱ := ℱ) (μ := μ) (Y := Y) hb k ω]
  mean_zero k := by
    have e1 := condExp_sub (m := ℱ k) (integrable_Y (μ := μ) hY0 hYb hmeas k)
      (integrable_clipB (ℱ := ℱ) (μ := μ) (Y := Y) hb k)
    rw [condExp_of_stronglyMeasurable (ℱ.le k) (stronglyMeasurable_clipB k)
      (integrable_clipB hb k)] at e1
    filter_upwards [e1, clipB_ae_eq (μ := μ) hY0 hYb hmeas k] with ω h1 h2
    change (μ[Y k - clipB ℱ μ b Y k | ℱ k]) ω = 0
    rw [h1, Pi.sub_apply, h2, sub_self]

/-- **The variance bound** `E[(Y - E[Y|ℱ])² | ℱ] ≤ b E[Y|ℱ]` for `0 ≤ Y ≤ b`. -/
lemma condVar_le (hb : 0 ≤ b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) (k : ℕ) :
    μ[fun ω => (Y k ω - clipB ℱ μ b Y k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun ω => b * clipB ℱ μ b Y k ω := by
  set c := clipB ℱ μ b Y k
  set g : Ω → ℝ := fun ω => -2 * c ω
  set q : Ω → ℝ := fun ω => c ω ^ 2
  set Y2 : Ω → ℝ := fun ω => Y k ω ^ 2
  have hcb := clipB_bounds (ℱ := ℱ) (μ := μ) (Y := Y) hb k
  have hc : StronglyMeasurable[ℱ k] c := stronglyMeasurable_clipB k
  have hg : StronglyMeasurable[ℱ k] g := hc.const_mul (-2)
  have hq : StronglyMeasurable[ℱ k] q := hc.pow 2
  have hYm : StronglyMeasurable[m0] (Y k) := (hmeas k).mono (ℱ.le (k + 1))
  have hYi := integrable_Y (μ := μ) hY0 hYb hmeas k
  have hY2 : Integrable Y2 μ :=
    Integrable.of_bound (hYm.pow 2).aestronglyMeasurable (b ^ 2)
      (Eventually.of_forall fun ω => by
        simp only [Y2, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hY0 k ω)]
        exact pow_le_pow_left₀ (hY0 k ω) (hYb k ω) 2)
  have hgY : Integrable (g * Y k) μ :=
    Integrable.of_bound ((hg.mono (ℱ.le k)).mul hYm).aestronglyMeasurable (2 * b * b)
      (Eventually.of_forall fun ω => by
        have h1 := hcb ω
        have hc0 : 0 ≤ c ω := h1.1
        have hcb' : c ω ≤ b := h1.2
        simp only [Pi.mul_apply, g, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hY0 k ω),
          abs_of_nonneg hc0]
        have := hYb k ω
        have := hY0 k ω
        norm_num
        nlinarith)
  have hqi : Integrable q μ :=
    Integrable.of_bound (hq.mono (ℱ.le k)).aestronglyMeasurable (b ^ 2)
      (Eventually.of_forall fun ω => by
        have h1 : 0 ≤ c ω ∧ c ω ≤ b := hcb ω
        simp only [q, Real.norm_eq_abs, abs_pow, abs_of_nonneg h1.1]
        exact pow_le_pow_left₀ h1.1 h1.2 2)
  have heq : (fun ω => (Y k ω - c ω) ^ 2) = Y2 + (g * Y k + q) := by
    funext ω; simp only [Pi.add_apply, Pi.mul_apply, g, q, Y2]; ring
  rw [heq]
  have e1 := condExp_add (m := ℱ k) hY2 (hgY.add hqi)
  have e2 := condExp_add (m := ℱ k) hgY hqi
  have e3 := condExp_mul_of_stronglyMeasurable_left (m := ℱ k) hg hgY hYi
  rw [condExp_of_stronglyMeasurable (ℱ.le k) hq hqi] at e2
  have e4 : μ[Y2 | ℱ k] ≤ᵐ[μ] μ[b • Y k | ℱ k] :=
    condExp_mono hY2 (hYi.smul b) (Eventually.of_forall fun ω => by
      simp only [Y2, Pi.smul_apply, smul_eq_mul]
      have := hY0 k ω; have := hYb k ω; nlinarith)
  have e5 := condExp_smul (μ := μ) b (Y k) (ℱ k)
  filter_upwards [e1, e2, e3, e4, e5, clipB_ae_eq (μ := μ) hY0 hYb hmeas k] with ω h1 h2 h3 h4
    h5 h6
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.mul_apply, ← h6]
  rw [h5, Pi.smul_apply, smul_eq_mul, ← h6] at h4
  simp only [g, q]
  nlinarith [sq_nonneg (c ω)]

/-- The numerical step of the proof of Theorem 6.6(i): with `a = √(2vλ) + 2bλ/3`,
`λ ≤ a² / (2v + 2ab/3)`. -/
lemma lam_le_b {v l b : ℝ} (hv : 0 < v) (hl : 0 < l) (hb : 0 ≤ b) :
    l ≤ (Real.sqrt (2 * v * l) + 2 * b * l / 3) ^ 2 /
      (2 * v + 2 * (Real.sqrt (2 * v * l) + 2 * b * l / 3) * b / 3) := by
  set s := Real.sqrt (2 * v * l)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * v * l := Real.sq_sqrt (by positivity)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hl.le hs0) hb]

/-- **Freedman's inequality (73) for bounded counts on a good event.** Let `0 ≤ Y_k ≤ b`
(`b > 0`) be `ℱ_{k+1}`-measurable, and let `G` be any set on which, almost surely,
`∑_{k<N} E[Y_k | ℱ_k] ≤ v / b`. Then
`P({∑_{k<N} (Y_k - E[Y_k|ℱ_k]) ≥ √(2vλ) + 2bλ/3} ∩ G) ≤ e^{-λ}`. -/
theorem freedman_good (hb : 0 < b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) {v l : ℝ} (hv : 0 < v) (hl : 0 < l)
    (N : ℕ) (G : Set Ω)
    (hG : ∀ᵐ ω ∂μ, ω ∈ G → ∑ k ∈ range N, (μ[Y k | ℱ k]) ω ≤ v / b) :
    μ ({ω | Real.sqrt (2 * v * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤ ENNReal.ofReal (Real.exp (-l)) := by
  set a := Real.sqrt (2 * v * l) + 2 * b * l / 3 with ha_def
  have ha : 0 < a := by positivity
  set ξ : ℕ → Ω → ℝ := fun k ω => Y k ω - clipB ℱ μ b Y k ω
  set E1 := {ω | ∃ n ≤ N, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v}
  have hc := ae_all_iff.mpr fun k => clipB_ae_eq (μ := μ) hY0 hYb hmeas k
  have hvar := ae_all_iff.mpr fun k => condVar_le (μ := μ) hb.le hY0 hYb hmeas k
  have hsub : ({ω | a ≤ ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G : Set Ω) ≤ᵐ[μ]
      (E1 : Set Ω) := by
    filter_upwards [hc, hvar, hG] with ω hcω hvω hGω
    rintro ⟨hS, hωG⟩
    change ω ∈ E1
    have hsum := hGω hωG
    refine ⟨N, le_rfl, ?_, ?_⟩
    · have : ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω) = S ξ N ω := by
        simp only [S, ξ]; exact sum_congr rfl fun k _ => by rw [hcω k]
      rw [← this]; exact hS
    · unfold V
      calc ∑ k ∈ range N, (μ[fun ω => ξ k ω ^ 2 | ℱ k]) ω
          ≤ ∑ k ∈ range N, b * (μ[Y k | ℱ k]) ω :=
            sum_le_sum fun k _ => by rw [← hcω k]; exact hvω k
        _ = b * ∑ k ∈ range N, (μ[Y k | ℱ k]) ω := by rw [mul_sum]
        _ ≤ b * (v / b) := mul_le_mul_of_nonneg_left hsum hb.le
        _ = v := by field_simp
  have hF := freedman (μ := μ) (ℱ := ℱ) (martDiff_bounded (μ := μ) hb.le hY0 hYb hmeas)
    hb.le ha hv N
  have hF' : μ.real E1 ≤ Real.exp (-l) :=
    hF.trans (Real.exp_le_exp.mpr (neg_le_neg (lam_le_b hv hl hb.le)))
  calc μ ({ω | a ≤ ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤ μ E1 :=
        measure_mono_ae hsub
    _ = ENNReal.ofReal (μ.real E1) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-l)) := ENNReal.ofReal_le_ofReal hF'

/-- **Peeling over `ℓ_jit(I)`** (first item of the proof of Theorem 6.6(i)): for a random integer
`ℓ`, deterministic `v_ℓ > 0`, and a set `G` on which a.s. `ℓ = l ≤ K` gives
`∑_{k<N} E[Y_k|ℱ_k] ≤ v_l / b`, the event "`ℓ ≤ K` and the centred sum is at least
`√(2 v_ℓ λ) + 2bλ/3`" meets `G` with probability at most `(K + 1) e^{-λ}`. -/
theorem freedman_peel (hb : 0 < b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) {l : ℝ} (hl : 0 < l) (N K : ℕ)
    (ℓ : Ω → ℕ) (v : ℕ → ℝ) (hv : ∀ j, 0 < v j) (G : Set Ω)
    (hG : ∀ j ≤ K, ∀ᵐ ω ∂μ, ω ∈ G → ℓ ω = j →
      ∑ k ∈ range N, (μ[Y k | ℱ k]) ω ≤ v j / b) :
    μ ({ω | ℓ ω ≤ K ∧ Real.sqrt (2 * v (ℓ ω) * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤
      ENNReal.ofReal ((K + 1) * Real.exp (-l)) := by
  have hsub : {ω | ℓ ω ≤ K ∧ Real.sqrt (2 * v (ℓ ω) * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G ⊆
      ⋃ j ∈ range (K + 1), ({ω | Real.sqrt (2 * v j * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ (G ∩ {ω | ℓ ω = j})) := by
    rintro ω ⟨⟨hK, hS⟩, hG'⟩
    exact Set.mem_biUnion (mem_range.mpr (Nat.lt_succ_of_le hK)) ⟨hS, hG', rfl⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ j ∈ range (K + 1), μ ({ω | Real.sqrt (2 * v j * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range N, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ (G ∩ {ω | ℓ ω = j}))
      ≤ ∑ _j ∈ range (K + 1), ENNReal.ofReal (Real.exp (-l)) := by
        refine sum_le_sum fun j hj => freedman_good hb hY0 hYb hmeas (hv j) hl N _ ?_
        have hj' : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hj)
        filter_upwards [hG j hj'] with ω h hω
        exact h hω.1 hω.2
    _ = ENNReal.ofReal ((K + 1) * Real.exp (-l)) := by
        rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        norm_cast

end Bounded

/-- **Part (b) of `Fr(I)`** (proof of Theorem 6.6(i), `b = 1`): for indicators `X_k ∈ [0, 1]`
whose conditional means sum to at most `μ̄` a.s. on `G`,
`P({∑_{k<N} X_k ≥ μ̄ + √(2μ̄λ) + 2λ/3} ∩ G) ≤ e^{-λ}`. -/
theorem count_good {X : ℕ → Ω → ℝ} (hX0 : ∀ k ω, 0 ≤ X k ω) (hX1 : ∀ k ω, X k ω ≤ 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) {μbar l : ℝ} (hμ : 0 < μbar)
    (hl : 0 < l) (N : ℕ) (G : Set Ω)
    (hG : ∀ᵐ ω ∂μ, ω ∈ G → ∑ k ∈ range N, (μ[X k | ℱ k]) ω ≤ μbar) :
    μ ({ω | μbar + (Real.sqrt (2 * μbar * l) + 2 * l / 3) ≤ ∑ k ∈ range N, X k ω} ∩ G) ≤
      ENNReal.ofReal (Real.exp (-l)) := by
  have h := freedman_good (μ := μ) (ℱ := ℱ) (b := 1) one_pos hX0 hX1 hmeas hμ hl N G
    (by simpa using hG)
  refine le_trans (measure_mono_ae ?_) h
  filter_upwards [hG] with ω hω
  rintro ⟨hS, hωG⟩
  refine ⟨?_, hωG⟩
  simp only [Set.mem_setOf_eq]
  have := hω hωG
  have hS' : μbar + (Real.sqrt (2 * μbar * l) + 2 * l / 3) ≤ ∑ k ∈ range N, X k ω := hS
  rw [sum_sub_distrib]
  simp only [mul_one]
  linarith

section AllTimes

variable {Y : ℕ → Ω → ℝ} {b : ℝ}

/-- `freedman_good` for all times: if a.s. on `G` every partial compensator is at most `v/b`, the
event "some partial centred sum is at least `√(2vλ) + 2bλ/3`" meets `G` with probability at most
`e^{-λ}`. -/
theorem freedman_good_all (hb : 0 < b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) {v l : ℝ} (hv : 0 < v) (hl : 0 < l)
    (G : Set Ω) (hG : ∀ᵐ ω ∂μ, ω ∈ G → ∀ n, ∑ k ∈ range n, (μ[Y k | ℱ k]) ω ≤ v / b) :
    μ ({ω | ∃ n, Real.sqrt (2 * v * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤ ENNReal.ofReal (Real.exp (-l)) := by
  set a := Real.sqrt (2 * v * l) + 2 * b * l / 3 with ha_def
  have ha : 0 < a := by positivity
  set ξ : ℕ → Ω → ℝ := fun k ω => Y k ω - clipB ℱ μ b Y k ω
  set E1 := {ω | ∃ n, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v}
  have hc := ae_all_iff.mpr fun k => clipB_ae_eq (μ := μ) hY0 hYb hmeas k
  have hvar := ae_all_iff.mpr fun k => condVar_le (μ := μ) hb.le hY0 hYb hmeas k
  have hsub : ({ω | ∃ n, a ≤ ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G : Set Ω) ≤ᵐ[μ]
      (E1 : Set Ω) := by
    filter_upwards [hc, hvar, hG] with ω hcω hvω hGω
    rintro ⟨⟨n, hS⟩, hωG⟩
    change ω ∈ E1
    have hsum := hGω hωG n
    refine ⟨n, ?_, ?_⟩
    · have : ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω) = S ξ n ω := by
        simp only [S, ξ]; exact sum_congr rfl fun k _ => by rw [hcω k]
      rw [← this]; exact hS
    · unfold V
      calc ∑ k ∈ range n, (μ[fun ω => ξ k ω ^ 2 | ℱ k]) ω
          ≤ ∑ k ∈ range n, b * (μ[Y k | ℱ k]) ω :=
            sum_le_sum fun k _ => by rw [← hcω k]; exact hvω k
        _ = b * ∑ k ∈ range n, (μ[Y k | ℱ k]) ω := by rw [mul_sum]
        _ ≤ b * (v / b) := mul_le_mul_of_nonneg_left hsum hb.le
        _ = v := by field_simp
  have hF := freedman_iUnion (μ := μ) (ℱ := ℱ) (martDiff_bounded (μ := μ) hb.le hY0 hYb hmeas)
    hb.le ha hv
  have hF' : μ.real E1 ≤ Real.exp (-l) :=
    hF.trans (Real.exp_le_exp.mpr (neg_le_neg (lam_le_b hv hl hb.le)))
  calc μ ({ω | ∃ n, a ≤ ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤ μ E1 :=
        measure_mono_ae hsub
    _ = ENNReal.ofReal (μ.real E1) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-l)) := ENNReal.ofReal_le_ofReal hF'

/-- Peeling over `ℓ_jit(I)`, all times. -/
theorem freedman_peel_all (hb : 0 < b) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYb : ∀ k ω, Y k ω ≤ b)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) {l : ℝ} (hl : 0 < l) (K : ℕ)
    (ℓ : Ω → ℕ) (v : ℕ → ℝ) (hv : ∀ j, 0 < v j) (G : Set Ω)
    (hG : ∀ j ≤ K, ∀ᵐ ω ∂μ, ω ∈ G → ℓ ω = j →
      ∀ n, ∑ k ∈ range n, (μ[Y k | ℱ k]) ω ≤ v j / b) :
    μ ({ω | ℓ ω ≤ K ∧ ∃ n, Real.sqrt (2 * v (ℓ ω) * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G) ≤
      ENNReal.ofReal ((K + 1) * Real.exp (-l)) := by
  have hsub : {ω | ℓ ω ≤ K ∧ ∃ n, Real.sqrt (2 * v (ℓ ω) * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ G ⊆
      ⋃ j ∈ range (K + 1), ({ω | ∃ n, Real.sqrt (2 * v j * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ (G ∩ {ω | ℓ ω = j})) := by
    rintro ω ⟨⟨hK, hS⟩, hG'⟩
    exact Set.mem_biUnion (mem_range.mpr (Nat.lt_succ_of_le hK)) ⟨hS, hG', rfl⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ j ∈ range (K + 1), μ ({ω | ∃ n, Real.sqrt (2 * v j * l) + 2 * b * l / 3 ≤
        ∑ k ∈ range n, (Y k ω - (μ[Y k | ℱ k]) ω)} ∩ (G ∩ {ω | ℓ ω = j}))
      ≤ ∑ _j ∈ range (K + 1), ENNReal.ofReal (Real.exp (-l)) := by
        refine sum_le_sum fun j hj => freedman_good_all hb hY0 hYb hmeas (hv j) hl _ ?_
        have hj' : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hj)
        filter_upwards [hG j hj'] with ω h hω
        exact h hω.1 hω.2
    _ = ENNReal.ofReal ((K + 1) * Real.exp (-l)) := by
        rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        norm_cast

end AllTimes

/-- Part (b) of `Fr(I)`, all times. -/
theorem count_good_all {X : ℕ → Ω → ℝ} (hX0 : ∀ k ω, 0 ≤ X k ω) (hX1 : ∀ k ω, X k ω ≤ 1)
    (hmeas : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k)) {μbar l : ℝ} (hμ : 0 < μbar)
    (hl : 0 < l) (G : Set Ω)
    (hG : ∀ᵐ ω ∂μ, ω ∈ G → ∀ n, ∑ k ∈ range n, (μ[X k | ℱ k]) ω ≤ μbar) :
    μ ({ω | ∃ n, μbar + (Real.sqrt (2 * μbar * l) + 2 * l / 3) ≤ ∑ k ∈ range n, X k ω} ∩ G) ≤
      ENNReal.ofReal (Real.exp (-l)) := by
  have h := freedman_good_all (μ := μ) (ℱ := ℱ) (b := 1) one_pos hX0 hX1 hmeas hμ hl G
    (by simpa using hG)
  refine le_trans (measure_mono_ae ?_) h
  filter_upwards [hG] with ω hω
  rintro ⟨⟨n, hS⟩, hωG⟩
  refine ⟨⟨n, ?_⟩, hωG⟩
  have := hω hωG n
  rw [sum_sub_distrib]
  simp only [mul_one]
  linarith

end Queue6

end
