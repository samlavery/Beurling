module

public import RequestProject.BSCert.Consts.PhiCover0
public import RequestProject.BSCert.Consts.PhiCover1
public import RequestProject.BSCert.Consts.PhiCover2
public import RequestProject.BSCert.Consts.PhiCover3
public import RequestProject.BSCert.Consts.PhiCover4
public import RequestProject.BSCert.Consts.PhiCover5
public import RequestProject.BSCert.Consts.PhiCover6
public import RequestProject.BSCert.Consts.PhiCover7
public import RequestProject.BSCert.Consts.PhiCover8
public import RequestProject.BSCert.Consts.PhiCover9
public import RequestProject.BSCert.Consts.PhiCover10
public import RequestProject.BSCert.Consts.PhiCover11
public import RequestProject.BSCert.Consts.PhiCover12
public import RequestProject.BSCert.Consts.PhiCover13
public import RequestProject.BSCert.Consts.PhiCover14
public import RequestProject.BSCert.Consts.PhiCover15
public import RequestProject.BSCert.Consts.PhiCover16
public import RequestProject.BSCert.Consts.PhiCover17
public import RequestProject.BSCert.Consts.PhiCover18
public import RequestProject.BSCert.Consts.PhiCover19
public import RequestProject.BSCert.Consts.PhiCover20
public import RequestProject.BSCert.Consts.PhiCover21
public import RequestProject.BSCert.Consts.PhiCover22
public import RequestProject.BSCert.Consts.PhiCover23

/-!
# `phi_bounds.py` (Appendix B.4): `‖ϕ''‖∞ ≤ 10` and `‖ϕ'‖∞ ≤ 2`

* On `[0.02, 0.98]`, `ϕ''` is enclosed on cells of width `10⁻³` (bisected when needed) from
  monotone enclosures of `g`, `q`, `q'` and `e^g` on the cell (`phiCell`).
* On `(0, 0.02]`, `|ϕ''| ≤ e^{-|g|}(q² + |q'|) ≤ 10` analytically (`abs_D2_le_small`); `[0.98, 1)`
  follows from `ϕ''(1 - t) = -ϕ''(t)`.
* Outside `[0, 1]`, `ϕ` is constant; at `0` and `1` the bounds follow by continuity of `ϕ'`,
  `ϕ''`.
* `0 ≤ ϕ' ≤ 2` is the analytic argument of (2) (`D1_le_two`), with equality at `1/2`.
-/

@[expose] public section

namespace BSCert.Consts

open Real BSCert

lemma glueQ {P : ℝ → Prop} {a b c : ℚ} (h1 : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → P x)
    (h2 : ∀ x : ℝ, (b : ℝ) ≤ x → x ≤ (c : ℝ) → P x) : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (c : ℝ) → P x := by
  intro x hx1 hx2
  rcases le_total x (b : ℝ) with h | h
  · exact h1 x hx1 h
  · exact h2 x h hx2

/-- The cover of `[0.02, 0.98]`, in 24 kernel-checked pieces (`PhiCover*`). -/
lemma phi_cover_sound : ∀ t : ℝ, ((2 / 100 : ℚ) : ℝ) ≤ t → t ≤ ((98 / 100 : ℚ) : ℝ) → |D2 t| ≤ 10 :=
  (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (glueQ (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi0)
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi1))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi2))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi3))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi4))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi5))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi6))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi7))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi8))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi9))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi10))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi11))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi12))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi13))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi14))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi15))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi16))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi17))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi18))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi19))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi20))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi21))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi22))
    (cover_sound (fun u => |D2 u| ≤ 10) phiCell phiCell_sound 10 (astep (1 / 1000)) 1000 _ _ check_phi23))

lemma abs_D2_le_ten {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : |D2 t| ≤ 10 := by
  by_cases ha : t ≤ 1 / 50
  · exact abs_D2_le_small h0 ha
  by_cases hb : 49 / 50 ≤ t
  · have := abs_D2_le_small (t := 1 - t) (by linarith) (by linarith)
    rwa [D2_symm, abs_neg] at this
  push_neg at ha hb
  exact phi_cover_sound t (by push_cast; linarith) (by push_cast; linarith)

/-- **`phi_bounds.py`.** `|ϕ''(t)| ≤ 10` for every real `t`. -/
theorem phiCut_deriv2_le (t : ℝ) : |deriv (deriv phiCut) t| ≤ 10 := by
  have hS : IsClosed {y : ℝ | |y| ≤ 10} := isClosed_le continuous_abs continuous_const
  refine mem_of_ne_zero_one continuous_deriv2_phiCut hS (fun t ht0 ht1 => ?_) t
  simp only [Set.mem_setOf_eq]
  rcases lt_or_gt_of_ne ht0 with h | h
  · rw [deriv2_phiCut_of_neg h]; norm_num
  rcases lt_or_gt_of_ne ht1 with h' | h'
  · rw [deriv2_phiCut_eq h h']; exact abs_D2_le_ten h h'
  · rw [deriv2_phiCut_of_gt h']; norm_num

/-- **(2).** `0 ≤ ϕ'(t) ≤ 2` for every real `t`. -/
theorem phiCut_deriv_mem (t : ℝ) : 0 ≤ deriv phiCut t ∧ deriv phiCut t ≤ 2 := by
  have hS : IsClosed (Set.Icc (0 : ℝ) 2) := isClosed_Icc
  refine mem_of_ne_zero_one continuous_deriv_phiCut hS (fun t ht0 ht1 => ?_) t
  rcases lt_or_gt_of_ne ht0 with h | h
  · rw [deriv_phiCut_of_neg h]; norm_num
  rcases lt_or_gt_of_ne ht1 with h' | h'
  · rw [deriv_phiCut_eq h h']; exact ⟨D1_nonneg h h', D1_le_two h h'⟩
  · rw [deriv_phiCut_of_gt h']; norm_num

/-- The bound `ϕ' ≤ 2` is attained at `t = 1/2`. -/
theorem phiCut_deriv_half : deriv phiCut (1 / 2) = 2 := by
  rw [deriv_phiCut_eq (by norm_num) (by norm_num), D1_half]

end BSCert.Consts
