module

public import RequestProject.Beurling.Noise.MarginChainLocRec
public import RequestProject.Beurling.Noise.MarginChainLin

/-!
# Proposition 5.38, Steps 3–5, with the filter kept on the Step 3 error terms

The paper's Step 3 (04g-margin.tex) writes
`S(t) = o_t + 2η(t) + 2 ∑_w (κ_w/w) ε(t/w)/H(t/w) + 1.0001 ∑_w (κ_w/w) δ(t/w)`, with
`κ_w = 1[τ_w < t/w]`: the Step 2 errors enter only through the cofactors that pass the filter.
`step3_term` (`MarginRecStep.lean`) drops the factor `κ_w ≤ 1` on the error, so the recursion of
`variation_le_chain_loc` has `S(t) = o_t + 2η(t) + ∑_{w ∈ F} e_w/w` over *all* cofactors. That
sum is not bounded by the filtered weights `ω_t(v)` of Lemma 5.21, so `log t · S(t)` is not
uniformly small (it grows like `log t · Λ⁻⁵`). Here the factor is kept:

* `step3_term_kap` : `κ |Δρ̃|/w ≤ 1.0101 κ w^{ε-2} b + κ e/w` for `κ ∈ {0, 1}`;
* `step3_pointwise_kap` : Step 3 pointwise with `∑_w κ_w e_w/w`;
* `variation_le_chain_loc_kap` : `variation_le_chain_loc` with Step 4 in the paper's form
  `o_t + 2η(t) + ∑_{w ∈ F} κ_w(t) e_w(t)/w ≤ E_S/log t`.
-/

@[expose] public section

open Finset Real Set

namespace Margin.Rec

lemma kap_cases (P : BeurlingSystem) (tw : ℕ → ℝ) (y : ℝ) (w : ℕ) :
    kap P tw y w = 0 ∨ kap P tw y w = 1 := by
  unfold kap; split_ifs <;> simp

/-- One cofactor of Step 3, with the filter on the error: for `κ ∈ {0, 1}`,
`κ |ρ̃(t'/w) - ρ̃(t/w)|/w ≤ 1.0101 κ w^{ε-2} b + κ e/w`. -/
lemma step3_term_kap {H ρ v err : ℝ → ℝ} {ε t hh y W b e κ : ℝ} (hε : ε ≤ 0.01) (hW : 2 ≤ W)
    (hy : y = t / W) (hg : HStep H ε t y W) (hh1 : |hh| ≤ 1.01 * H t)
    (hS2 : ∀ z', y - 0.52 * H y ≤ z' → z' ≤ y → Step2At H ρ v err z' ∧ err z' ≤ e)
    (hb : ∀ x ∈ Icc (y - 2.1 * H y) (y + 2.1 * H y), v x ≤ b) (hb0 : 0 ≤ b)
    (hκ : κ = 0 ∨ κ = 1) (he0 : 0 ≤ e) :
    κ * (|ρ ((t + hh) / W) - ρ (t / W)| / W) ≤
      1.0101 * κ * W ^ (ε - 2) * b + κ * (e / W) := by
  rcases hκ with h0 | h1
  · subst h0; simp
  · subst h1
    have := step3_term hε hW hy hg hh1 hS2 hb hb0 ⟨zero_le_one, le_rfl⟩ he0
    simpa using this

/-- **Step 3, pointwise, with the filter kept on the errors**: as `step3_pointwise`, with
`∑_w κ_w(t) e_w/w` in place of `∑_w e_w/w`. -/
theorem step3_pointwise_kap (P : BeurlingSystem) (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m)
    {H Tp NT ρ v err : ℝ → ℝ} {ε o η : ℝ} (hε : ε ≤ 0.01) (hp2 : ∀ i, 2 ≤ P.p i)
    (hρ : ∀ z, z < X0m → ρ z = 0) {t hh : ℝ} (ht0 : 0 ≤ t) (hth : t + hh ≤ 2 * t)
    (hh1 : |hh| ≤ 1.01 * H t) (e b : ℕ → ℝ)
    (hgeom : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
      HStep H ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ v err z' ∧ err z' ≤ e w)
    (he0 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), 0 ≤ e w)
    (hb : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), ∀ x ∈
      Icc (t / KR.Vl P w - 2.1 * H (t / KR.Vl P w)) (t / KR.Vl P w + 2.1 * H (t / KR.Vl P w)),
        v x ≤ b w)
    (hb0 : ∀ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·), 0 ≤ b w)
    (hosc : |Tp (t + hh) - Tp t| ≤ o)
    (hsw : |∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
        (kap P tw (t + hh) w - kap P tw t w) * (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| +
      |NT (t + hh) - NT t| ≤ 2 * η) :
    |(Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
        (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t)| ≤
      o + 2 * η + ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
          kap P tw t w * (e w / KR.Vl P w) +
        ∑ w ∈ (KR.NAll P t (X0m / 2)).filter (2 ≤ ·),
          1.0101 * kap P tw t w * KR.Vl P w ^ (ε - 2) * b w := by
  classical
  set F := (KR.NAll P t (X0m / 2)).filter (2 ≤ ·)
  have hK := Kpt_diff P tw hX hρ ht0 hth
  set A := ∑ w ∈ F, kap P tw t w * ((ρ ((t + hh) / KR.Vl P w) - ρ (t / KR.Vl P w)) /
    KR.Vl P w)
  set SW := ∑ w ∈ F, (kap P tw (t + hh) w - kap P tw t w) *
    (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)
  have hK' : KR.Sharp.Kpt P tw X0m ρ (t + hh) - KR.Sharp.Kpt P tw X0m ρ t = A + SW := by
    rw [hK]; rfl
  have hA : |A| ≤ ∑ w ∈ F, (1.0101 * kap P tw t w * KR.Vl P w ^ (ε - 2) * b w +
      kap P tw t w * (e w / KR.Vl P w)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w hw => ?_)
    have hw2 := (Finset.mem_filter.mp hw).2
    have hV2 := two_le_Vv hp2 hw2
    have hk := kap_mem P tw t w
    rw [abs_mul, abs_of_nonneg hk.1, abs_div, abs_of_pos (Vv_pos (P := P) w)]
    exact step3_term_kap hε hV2 rfl (hgeom w hw) hh1 (hS2 w hw) (hb w hw) (hb0 w hw)
      (kap_cases P tw t w) (he0 w hw)
  have e1 : (Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
      (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t) =
      (Tp (t + hh) - Tp t) - A - (SW + (NT (t + hh) - NT t)) := by
    rw [show (Tp (t + hh) - KR.Sharp.Kpt P tw X0m ρ (t + hh) - NT (t + hh)) -
      (Tp t - KR.Sharp.Kpt P tw X0m ρ t - NT t) = (Tp (t + hh) - Tp t) -
        (KR.Sharp.Kpt P tw X0m ρ (t + hh) - KR.Sharp.Kpt P tw X0m ρ t) -
        (NT (t + hh) - NT t) by ring, hK']
    ring
  rw [e1]
  have t1 := abs_sub (Tp (t + hh) - Tp t - A) (SW + (NT (t + hh) - NT t))
  have t2 := abs_sub (Tp (t + hh) - Tp t) A
  have t3 := abs_add_le SW (NT (t + hh) - NT t)
  rw [Finset.sum_add_distrib] at hA
  linarith

/-- **Proposition 5.38, Steps 1–5, up to the height `T`, with the paper's Step 4**: the
conclusion of `variation_le_chain_loc`, where Step 4 is assumed in the form
`o_t + 2η(t) + ∑_{w ∈ F} κ_w(t) e_w(t)/w ≤ E_S/log t` (filtered cofactors only). -/
theorem variation_le_chain_loc_kap (P : BeurlingSystem) (p : CP) (tw : ℕ → ℝ)
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
      o t + 2 * η t + ∑ w ∈ Fset P p t, kap P tw t w * (e t w / KR.Vl P w) ≤
        p.ES / Real.log t)
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
  set S := fun t => o t + 2 * η t + ∑ w ∈ Fset P p t, kap P tw t w * (e t w / KR.Vl P w)
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
      exact step3_pointwise_kap P tw hXm hε h.hp2 hρ ht0 hth hh1 (e t) b (hgeom t ht htT)
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

/-! ## The jump at `X₀` as a separate source (04g Step 3, base case; Step 5, `V_{X₀}`) -/

/-- The jump indicator `1[|t - X₀| ≤ 1.01 H(t)]`. -/
noncomputable def jumpI (H : ℝ → ℝ) (X0 t : ℝ) : ℝ := if |t - X0| ≤ 1.01 * H t then 1 else 0

lemma jumpI_nonneg (H : ℝ → ℝ) (X0 t : ℝ) : 0 ≤ jumpI H X0 t := by
  unfold jumpI; split_ifs <;> norm_num

/-- `|1_{[X₀,∞)}(t + h) - 1_{[X₀,∞)}(t)| ≤ 1[|t - X₀| ≤ 1.01 H(t)]` for `|h| ≤ 1.01 H(t)`. -/
lemma ind_jump_le {H : ℝ → ℝ} {X0 t hh : ℝ} (hh1 : |hh| ≤ 1.01 * H t) :
    |KR.Chain.ind X0 (t + hh) - KR.Chain.ind X0 t| ≤ jumpI H X0 t := by
  unfold jumpI
  by_cases hc : |t - X0| ≤ 1.01 * H t
  · rw [if_pos hc]
    unfold KR.Chain.ind
    simp only [Set.indicator, Set.mem_Ici]
    split_ifs <;> norm_num
  · rw [if_neg hc]
    have hlt : |hh| < |t - X0| := lt_of_le_of_lt hh1 (not_le.mp hc)
    have hn := neg_abs_le hh
    have hp := le_abs_self hh
    unfold KR.Chain.ind
    simp only [Set.indicator, Set.mem_Ici]
    by_cases ht : X0 ≤ t
    · rw [abs_of_nonneg (by linarith : 0 ≤ t - X0)] at hlt
      rw [if_pos (by linarith : X0 ≤ t + hh), if_pos ht]; norm_num
    · push_neg at ht
      rw [abs_of_neg (by linarith : t - X0 < 0)] at hlt
      rw [if_neg (by linarith : ¬ X0 ≤ t + hh), if_neg (not_le.mpr ht)]; norm_num

/-- **Proposition 5.38, Steps 1–5, with `T' = T_c + j₀ 1_{[X₀,∞)}`**: as
`variation_le_chain_loc_kap`, but the oscillation `o_t` is that of `T_c` alone, and the jump
enters the Step 3 source as `j₀ 1[|t - X₀| ≤ 1.01 H(t)]`, absorbed by the `j`-term of the
super-solution (`p.j ≥ j₀`, and the window `|t - X₀| ≤ 1.01 H(t)` lies in `|t - p.X₀| ≤ r(1)`). -/
theorem variation_le_chain_loc_kapJ (P : BeurlingSystem) (p : CP) (tw : ℕ → ℝ)
    {H Tc NT ρ err : ℝ → ℝ} {o η : ℝ → ℝ} {e : ℝ → ℕ → ℝ} {T0 T X0 j0 : ℝ}
    (h : ChainHyp P p H) (hε : p.ε ≤ 0.01) (hT0 : p.cinf + p.Kc ≤ T0)
    (hT0wf : 2 ≤ T0 * (1 - p.θ0)) (hT0T : T0 ≤ T) (hρ : ∀ z, z < p.Xm → ρ z = 0)
    (hT0' : ∀ t, T0 ≤ t → t ≤ T → 0 ≤ t ∧ 1.01 * H t ≤ t)
    (hgeom : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t,
      HStep H p.ε t (t / KR.Vl P w) (KR.Vl P w))
    (hS2 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t, ∀ z',
      t / KR.Vl P w - 0.52 * H (t / KR.Vl P w) ≤ z' → z' ≤ t / KR.Vl P w →
        Step2At H ρ (vSup H (fun y => (Tc y + j0 * KR.Chain.ind X0 y) -
          KR.Sharp.Kpt P tw p.Xm ρ y - NT y)) err z' ∧ err z' ≤ e t w)
    (he0 : ∀ t, T0 ≤ t → t ≤ T → ∀ w ∈ Fset P p t, 0 ≤ e t w)
    (hosc : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t → |Tc (t + hh) - Tc t| ≤ o t)
    (hj0 : 0 ≤ j0) (hjp : j0 ≤ p.j)
    (hJr : ∀ t, T0 ≤ t → t ≤ T → |t - X0| ≤ 1.01 * H t → |t - p.X0| ≤ radJ P p 1)
    (hsw : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t →
      |∑ w ∈ Fset P p t, (kap P tw (t + hh) w - kap P tw t w) *
          (ρ ((t + hh) / KR.Vl P w) / KR.Vl P w)| + |NT (t + hh) - NT t| ≤ 2 * η t)
    (hS4 : ∀ t, T0 ≤ t → t ≤ T →
      o t + 2 * η t + ∑ w ∈ Fset P p t, kap P tw t w * (e t w / KR.Vl P w) ≤
        p.ES / Real.log t)
    (hbase : ∀ t, t < T0 → vSup H (fun y => (Tc y + j0 * KR.Chain.ind X0 y) -
      KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤ PhiC P p t 1)
    (t : ℝ) (htT : t ≤ T) :
    vSup H (fun y => (Tc y + j0 * KR.Chain.ind X0 y) - KR.Sharp.Kpt P tw p.Xm ρ y - NT y) t ≤
      ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => cutL P p M ≤ t / Vv P M),
          Aw P p M * (p.ES / Real.log (t / Vv P M)) +
        p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter
          (fun M => |t / Vv P M - p.X0| ≤ p.R0), Aw P p M := by
  have hXm : 0 < p.Xm := by linarith [h.hXm]
  set Tp := fun y => Tc y + j0 * KR.Chain.ind X0 y
  set m := fun y => Tp y - KR.Sharp.Kpt P tw p.Xm ρ y - NT y
  set v := vSup H m
  set S := fun t => (o t + j0 * jumpI H X0 t) + 2 * η t +
    ∑ w ∈ Fset P p t, kap P tw t w * (e t w / KR.Vl P w)
  set c := fun t w => 1.0101 * kap P tw t w * KR.Vl P w ^ (p.ε - 2)
  have hc0 : ∀ t w, 0 ≤ c t w := fun t w =>
    mul_nonneg (mul_nonneg (by norm_num) (kap_mem P tw t w).1)
      (Real.rpow_nonneg (Vv_pos (P := P) w).le _)
  have hv0 : ∀ x, 0 ≤ truncAt T v x := by
    intro x; unfold truncAt; split_ifs
    · exact vSup_nonneg' H m x
    · exact le_rfl
  have hoscT : ∀ t, T0 ≤ t → t ≤ T → ∀ hh, |hh| ≤ 1.01 * H t →
      |Tp (t + hh) - Tp t| ≤ o t + j0 * jumpI H X0 t := by
    intro t ht htT hh hh1
    have e1 : Tp (t + hh) - Tp t = (Tc (t + hh) - Tc t) +
        j0 * (KR.Chain.ind X0 (t + hh) - KR.Chain.ind X0 t) := by
      simp only [Tp]; ring
    rw [e1]
    have h1 := hosc t ht htT hh hh1
    have h2 : |j0 * (KR.Chain.ind X0 (t + hh) - KR.Chain.ind X0 t)| ≤ j0 * jumpI H X0 t := by
      rw [abs_mul, abs_of_nonneg hj0]
      exact mul_le_mul_of_nonneg_left (ind_jump_le hh1) hj0
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
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
      exact step3_pointwise_kap P tw hXm hε h.hp2 hρ ht0 hth hh1 (e t) b (hgeom t ht htT)
        (hS2 t ht htT) (he0 t ht htT) (fun w hw x hx => hb' w hw x hx) hb0
        (hoscT t ht htT hh hh1) (hsw t ht htT hh hh1)
    · simp only [truncAt, if_neg htT, zero_add]
      exact Finset.sum_nonneg fun w hw => mul_nonneg (hc0 t w) (hb0 w hw)
  have hS : ∀ t, T0 ≤ t → truncAt T S t ≤
      p.ES / Real.log t + (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
    intro t ht
    have hjt : 0 ≤ (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
      split_ifs; exact h.hj; exact le_rfl
    by_cases htT : t ≤ T
    · simp only [truncAt, if_pos htT]
      have h4 := hS4 t ht htT
      have hJ : j0 * jumpI H X0 t ≤ (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
        by_cases h1 : |t - X0| ≤ 1.01 * H t
        · have h2 := hJr t ht htT h1
          simp only [jumpI, if_pos h1, if_pos h2, mul_one]; exact hjp
        · simp only [jumpI, if_neg h1, mul_zero]; exact hjt
      have eS : S t = (o t + j0 * jumpI H X0 t) + 2 * η t +
          ∑ w ∈ Fset P p t, kap P tw t w * (e t w / KR.Vl P w) := rfl
      rw [eS]; linarith
    · simp only [truncAt, if_neg htT]
      have h1 := cinf_gt_one h
      have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith [h.hKc])
      have := div_nonneg h.hES hl
      linarith
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
  have := v_le_chain_J h hT0 hT0wf hS hc hrec hbase' t
  simp only [truncAt, if_pos htT] at this
  exact this

end Margin.Rec

end
