module

public import RequestProject.Beurling.Noise.MarginRecStep

/-!
# Proposition 5.38, Steps 1–5, up to a height `T`

`variation_le_chain` (`MarginRecStep.lean`) assumes the inputs of the recursion at every height
`t ≥ T₀`. The recursion runs downwards (the neighbourhoods `N(t, w)` lie in `(-∞, t - 1]`), so
the bound at `t ≤ T` only reads the inputs at heights `≤ T`.

* `variation_le_chain_loc` : the same conclusion for `t ≤ T`, with every input assumed only at
  heights `T₀ ≤ t ≤ T` (and `T₀ ≤ T`).

The proof truncates `v` and `S` above `T` (`truncAt`) and checks the recursion for the truncated
functions; the super-solution and the induction are those of `MarginRecSuper.lean`.
-/

@[expose] public section

open Finset Real Set

namespace Margin.Rec

/-- `f` on `(-∞, T]`, `0` above. -/
noncomputable def truncAt (T : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ T then f t else 0

variable {P : BeurlingSystem} {p : CP} {H : ℝ → ℝ}

/-- The neighbourhoods of the recursion lie below `t - 1`. -/
lemma nbhd_le (h : ChainHyp P p H) {T0 : ℝ} (hT0 : p.cinf + p.Kc ≤ T0)
    (hT0wf : 2 ≤ T0 * (1 - p.θ0)) {t : ℝ} (ht : T0 ≤ t) {w : ℕ} (hw : w ∈ Fset P p t)
    {t' : ℝ} (ht' : t' ∈ Nbhd P H t w) : t' ≤ t - 1 := by
  have hXm := h.hXm
  obtain ⟨hwA, hw2⟩ := Finset.mem_filter.mp hw
  have hy : p.Xm / 2 ≤ t / Vv P w := ((mem_NAll_iff' (by linarith)).mp hwA).2
  have hrel := h.hrel _ hy
  have hV2 := two_le_Vv h.hp2 hw2
  have ht0 : 0 ≤ t := by
    have := cinf_gt_one h; linarith [h.hKc]
  have hy2 : t / Vv P w ≤ t / 2 := div_le_div_of_nonneg_left ht0 two_pos hV2
  have hθ0 := h.hθ0
  have := ht'.2
  have hT : 2 ≤ t * (1 - p.θ0) := le_trans hT0wf
    (mul_le_mul_of_nonneg_right ht (by linarith [h.hθ01]))
  nlinarith

lemma vSup_nonneg' (H m : ℝ → ℝ) (x : ℝ) : 0 ≤ vSup H m x :=
  Real.sSup_nonneg (fun _ ⟨_, _, hk⟩ => hk ▸ abs_nonneg _)

/-- **Proposition 5.38, Steps 1–5, up to the height `T`**: the conclusion of
`variation_le_chain` at `t ≤ T`, from the inputs at the heights `T₀ ≤ t ≤ T` only. -/
theorem variation_le_chain_loc (P : BeurlingSystem) (p : CP) (tw : ℕ → ℝ)
    {H Tp NT ρ err : ℝ → ℝ} {o η : ℝ → ℝ} {e : ℝ → ℕ → ℝ} {T0 T : ℝ}
    (h : ChainHyp P p H) (hε : p.ε ≤ 0.01) (hT0 : p.cinf + p.Kc ≤ T0)
    (hT0wf : 2 ≤ T0 * (1 - p.θ0)) (hT0T : T0 ≤ T) (hρ : ∀ z, z < p.Xm → ρ z = 0)
    (hT0' : ∀ t, T0 ≤ t → t ≤ T → 0 ≤ t ∧ 1.01 * H t ≤ t)
    (hgeom : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t,
      HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ (vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y)) err z' ∧
          err z' ≤ e t w)
    (he0 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t, 0 ≤ e t w)
    (hosc : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t → |Tp (t + hh) - Tp t| ≤ o t)
    (hsw : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t →
      |∑ w ∈ Fset P p t, (kap P tw (t + hh) w - kap P tw t w) *
          (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NT (t + hh) - NT t| ≤ 2 * η t)
    (hS4 : ∀ t, T0 ≤ t → t ≤ T →
      o t + 2 * η t + ∑ w ∈ Fset P p t, e t w / KR.Vl P w ≤ p.ES / Real.log t)
    (hbase : ∀ t, t < T0 →
      vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤ PhiC P p t 1)
    (t : ℝ) (htT : t ≤ T) :
    vSup H (fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤
      ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => cutL P p M ≤ t / Vv P M),
          Aw P p M * (p.ES / Real.log (t / Vv P M)) +
        p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter
          (fun M => |t / Vv P M - p.X0| ≤ p.R0), Aw P p M := by
  have hXm : 0 < p.Xm := by linarith [h.hXm]
  set m := fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y
  set v := vSup H m
  set S := fun t => o t + 2 * η t + ∑ w ∈ Fset P p t, e t w / KR.Vl P w
  set c := fun t w => 1.0101 * kap P tw t w * KR.Vl P w ^ (p.ε - 2)
  have hc0 : ∀ t w, 0 ≤ c t w := fun t w =>
    mul_nonneg (mul_nonneg (by norm_num) (kap_mem P tw t w).1)
      (Real.rpow_nonneg (Vv_pos (P := P) w).le _)
  have hv0 : ∀ x, 0 ≤ truncAt T v x := by
    intro x; unfold truncAt; split_ifs
    · exact vSup_nonneg' H m x
    · exact le_rfl
  have hrec : Var.RecIneq T0 (truncAt T v) (truncAt T S) (Fset P p) c (Nbhd P H) := by
    intro t ht b hb
    have hb0 : ∀ w ∈ Fset P p t, 0 ≤ b w := by
      intro w hw
      refine (hv0 _).trans (hb w hw (t / KR.Vl P w) ⟨?_, ?_⟩) <;>
        linarith [h.hH0 (t / KR.Vl P w)]
    by_cases htT : t ≤ T
    · simp only [truncAt, if_pos htT]
      have hb' : ∀ w ∈ Fset P p t, ∀ t' ∈ Nbhd P H t w, v t' ≤ b w := by
        intro w hw t' ht'
        have hle := nbhd_le h hT0 hT0wf ht hw ht'
        have := hb w hw t' ht'
        simp only [truncAt, if_pos (show t' ≤ T by linarith)] at this
        exact this
      obtain ⟨ht0, hHt⟩ := hT0' t ht htT
      apply vSup_le (h.hH0 t)
      intro hh hh1
      have hth : t + hh ≤ 2 * t := by
        have := (abs_le.mp hh1).2; linarith
      exact step3_pointwise P tw hXm hε h.hp2 hρ ht0 hth hh1 (e t) b (hgeom t ht htT)
        (hS2 t ht htT) (he0 t ht htT) (fun w hw x hx => hb' w hw x hx) hb0
        (hosc t ht htT hh hh1) (hsw t ht htT hh hh1)
    · simp only [truncAt, if_neg htT, zero_add]
      exact Finset.sum_nonneg fun w hw => mul_nonneg (hc0 t w) (hb0 w hw)
  have hS : ∀ t, T0 ≤ t → truncAt T S t ≤ p.ES / Real.log t := by
    intro t ht
    unfold truncAt
    split_ifs with htT
    · exact hS4 t ht htT
    · have h1 := cinf_gt_one h
      have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith [h.hKc])
      exact div_nonneg h.hES hl
  have hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2) := by
    intro t' _ w _
    have hk := kap_mem P tw t' w
    have hV := Real.rpow_nonneg (Vv_pos (P := P) w).le (p.ε - 2)
    refine ⟨hc0 t' w, ?_⟩
    have := mul_le_mul_of_nonneg_right hk.2 hV
    show 1.0101 * kap P tw t' w * KR.Vl P w ^ (p.ε - 2) ≤ 1.0101 * Vv P w ^ (p.ε - 2)
    nlinarith
  have hbase' : ∀ t, t < T0 → truncAt T v t ≤ PhiC P p t 1 := by
    intro t ht
    simp only [truncAt, if_pos (show t ≤ T by linarith)]
    exact hbase t ht
  have := v_le_chain h hT0 hT0wf hS hc hrec hbase' t
  simp only [truncAt, if_pos htT] at this
  exact this

end Margin.Rec

end
