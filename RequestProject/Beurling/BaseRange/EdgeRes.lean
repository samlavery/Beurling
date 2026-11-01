module

public import RequestProject.Beurling.BaseRange.ZeroBelow
public import RequestProject.Beurling.BaseRange.RatSys
public import RequestProject.Beurling.Noise.KptInv

/-!
# Lemma 7.3(d)(iii): the rational resolvent `g` and the resolvent identity

With the rational system `ratSys` (decided at the values, `t(p) = p`), the sharp latest-prime
operator with cut-off `X₀` is `K'_ℚ = K_pt(ratSys, t = id, X₀)` (`KQ'`), and
`g = (1 + K'_ℚ)⁻¹ μ_edge = R_sh(ratSys) μ_edge` (`gEdge`). This file proves:

* `abs_Rsh_le` : the Lemma M bound `|R_sh φ(x)| ≤ sup_{[X₀⁻, x]} |φ| · ∑_{e ≤ x/X₀⁻} 1/e`;
* `one_add_KQ'_g` : `(1 + K'_ℚ) g = μ_edge` everywhere;
* `rhoEdge_sub_g` : **the resolvent identity** `ρ_edge - g = (1 + K_pt)⁻¹ (K'_ℚ - K_pt) g`
  on `[X₀⁻, ∞)`.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-- The rational decision times `t(p) = p`. -/
noncomputable def tQ (n : ℕ) : ℝ := (n : ℝ)

/-- `K'_ℚ`, the sharp latest-prime operator of the rational system with cut-off `X₀`. -/
noncomputable def KQ' (X0 : ℕ) (h : ℝ → ℝ) (y : ℝ) : ℝ := KR.Sharp.Kpt ratSys tQ X0 h y

/-- `g = (1 + K'_ℚ)⁻¹ μ_edge`. -/
noncomputable def gEdge (X0 : ℕ) (y : ℝ) : ℝ :=
  KR.Sharp.Rsh ratSys tQ X0 (muEdge X0 (Construction.kappaParam X0)) y

variable (P : BeurlingSystem)

lemma Kpt_sub (tw : ℕ → ℝ) (X0m : ℝ) (g1 g2 : ℝ → ℝ) (y : ℝ) :
    KR.Sharp.Kpt P tw X0m (fun z => g1 z - g2 z) y =
      KR.Sharp.Kpt P tw X0m g1 y - KR.Sharp.Kpt P tw X0m g2 y := by
  classical
  unfold KR.Sharp.Kpt
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

lemma Rsh_congr_ge (tw : ℕ → ℝ) {X0m : ℝ} (hX : 0 < X0m) {f f' : ℝ → ℝ}
    (h : ∀ z, X0m ≤ z → f z = f' z) (y : ℝ) :
    KR.Sharp.Rsh P tw X0m f y = KR.Sharp.Rsh P tw X0m f' y := by
  unfold KR.Sharp.Rsh
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [KR.Sharp.mem_NAll_iff P hX] at hn
  rw [h _ ((KR.Sharp.le_div_iff_cut P hX).mp hn.2)]

/-- **The Lemma M bound**: `|R_sh φ(x)| ≤ S ∑_{e ≤ x/X₀⁻} 1/e` if `|φ| ≤ S` on `[X₀⁻, x]`. -/
theorem abs_Rsh_le (tw : ℕ → ℝ) (ht : ∀ p, p.Prime → 0 < tw p) {X0m : ℝ} (hX : 0 < X0m)
    {x : ℝ} (hx : X0m ≤ x) {φ : ℝ → ℝ} {S : ℝ} (hS : ∀ z, X0m ≤ z → z ≤ x → |φ z| ≤ S) :
    |KR.Sharp.Rsh P tw X0m φ x| ≤ S * ∑ e ∈ P.elems (x / X0m), 1 / P.val e := by
  classical
  unfold KR.Sharp.Rsh KR.NAll
  rw [Finset.sum_image (fun a _ b _ h => iota_injective h)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have hv := P.val_pos e
  have hV : KR.Vl P (iota e) = P.val e := P.valN_iota e
  rw [hV]
  have he' := P.mem_elems.mp he
  have h1 : X0m ≤ x / P.val e := by
    rw [le_div_iff₀ hv]; rw [le_div_iff₀ hX] at he'; linarith
  have h2 : x / P.val e ≤ x := div_le_self (by linarith) (P.one_le_val e)
  have hc := LemmaM.abs_coeff_le_one tw P.labelVal ht (fun r _ => P.one_le_labelVal r) hX.le hx
    (n := iota e) (iota_pos e)
  have hφ := hS _ h1 h2
  rw [abs_div, abs_mul, abs_of_pos hv]
  have : |((LemmaM.coeff tw P.labelVal X0m x (iota e) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hc
  calc |((LemmaM.coeff tw P.labelVal X0m x (iota e) : ℤ) : ℝ)| * |φ (x / P.val e)| / P.val e
      ≤ 1 * S / P.val e := by
        apply div_le_div_of_nonneg_right _ hv.le
        exact mul_le_mul this hφ (abs_nonneg _) zero_le_one
    _ = S * (1 / P.val e) := by ring

/-! ### The rational resolvent -/

lemma NAll_ratSys_empty {X0 : ℕ} (hX : 0 < (X0 : ℝ)) {y : ℝ} (hy : y < X0) :
    KR.NAll ratSys y X0 = ∅ := by
  unfold KR.NAll
  rw [ratSys.elems_eq_empty (by rw [div_lt_one hX]; exact hy), Finset.image_empty]

lemma gEdge_zero_below {X0 : ℕ} (hX : 0 < (X0 : ℝ)) {y : ℝ} (hy : y < X0) : gEdge X0 y = 0 := by
  unfold gEdge KR.Sharp.Rsh
  rw [NAll_ratSys_empty hX hy, Finset.sum_empty]

lemma KQ'_zero_below {X0 : ℕ} (hX : 0 < (X0 : ℝ)) (h : ℝ → ℝ) {y : ℝ} (hy : y < X0) :
    KQ' X0 h y = 0 := by
  classical
  unfold KQ' KR.Sharp.Kpt
  rw [NAll_ratSys_empty hX hy, Finset.filter_empty, Finset.sum_empty]

/-- `(1 + K'_ℚ) g = μ_edge` everywhere. -/
lemma one_add_KQ'_g {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (y : ℝ) :
    gEdge X0 y + KQ' X0 (gEdge X0) y = muEdge X0 (Construction.kappaParam X0) y := by
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  rcases lt_or_ge y X0 with hy | hy
  · rw [gEdge_zero_below hX0 hy, KQ'_zero_below hX0 _ hy, muEdge_zero_below hX hy]; ring
  · exact KR.Sharp.one_add_Kpt_Rsh ratSys tQ hX0 hy _

/-- **The resolvent identity** `ρ_edge - g = (1 + K_pt)⁻¹ (K'_ℚ - K_pt) g` on `[X₀⁻, ∞)`. -/
theorem rhoEdge_sub_g (tw : ℕ → ℝ) {X0m : ℝ} {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
    (hXm : 0 < X0m) {x : ℝ} (hx : X0m ≤ x) :
    KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x =
      KR.Sharp.Rsh P tw X0m
        (fun u => KQ' X0 (gEdge X0) u - KR.Sharp.Kpt P tw X0m (gEdge X0) u) x := by
  set ρ := KR.Sharp.rhoEdge P tw X0m X0
  set g := gEdge X0
  set hf : ℝ → ℝ := fun z => ρ z - g z
  have key : ∀ z, X0m ≤ z → hf z + KR.Sharp.Kpt P tw X0m hf z =
      KQ' X0 g z - KR.Sharp.Kpt P tw X0m g z := by
    intro z hz
    have h1 := KR.Sharp.one_add_Kpt_Rsh P tw hXm hz (muEdge X0 (Construction.kappaParam X0))
    have h2 := one_add_KQ'_g hX z
    simp only [hf]
    rw [Kpt_sub]
    change KR.Sharp.Rsh P tw X0m _ z + KR.Sharp.Kpt P tw X0m (KR.Sharp.Rsh P tw X0m _) z = _
      at h1
    have e1 : ρ z = KR.Sharp.Rsh P tw X0m (muEdge X0 (Construction.kappaParam X0)) z := rfl
    have e2 : KR.Sharp.Kpt P tw X0m ρ z =
        KR.Sharp.Kpt P tw X0m (KR.Sharp.Rsh P tw X0m (muEdge X0 (Construction.kappaParam X0)))
          z := rfl
    rw [e1, e2]
    linarith
  have h3 := KR.Sharp.Rsh_one_add_Kpt P tw hXm hx hf
  change hf x = _
  rw [← h3]
  exact Rsh_congr_ge P tw hXm key x

/-! ### Lemma 7.3(d)(iii) from the bounds on `g` and on `(K'_ℚ - K_pt) g` -/

/-- **Proof of (d)(iii), the bound on `g`**: `|g(x)| ≤ (1.0001/Λ)(κ + X₀/x)` for `x ≥ X₀` (each
`N`-term of `g` is at most `MA[ℙ](x/N)/N`, and `∑_{x/X₀ < N < (1+κ)x/X₀} 1/N ≤ κ + X₀/x`). -/
def GEdgeBound (X0 : ℕ) : Prop :=
  ∀ x : ℝ, (X0 : ℝ) ≤ x →
    |gEdge X0 x| ≤ 1.0001 / Real.log X0 * (Construction.kappaParam X0 + X0 / x)

/-- **Proof of (d)(iii), the telescoping with `g`**: `|(K'_ℚ - K_pt) g(u)| ≤ 4κ (log u)³` on
`[X₀, x_max]` (Step 3 of (b) with `f₀` replaced by the non-smooth `g`, and the decision-order
count with `sup |g| ≤ 0.51/Λ`). -/
def KDiffBound (tw : ℕ → ℝ) (X0m : ℝ) (X0 : ℕ) (xmax : ℝ) : Prop :=
  ∀ u : ℝ, (X0 : ℝ) ≤ u → u ≤ xmax →
    |KQ' X0 (gEdge X0) u - KR.Sharp.Kpt P tw X0m (gEdge X0) u| ≤
      4 * Construction.kappaParam X0 * Real.log u ^ 3

/-! #### Numerics of (d)(iii) -/

section numerics

variable {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
include hX

lemma X0_pos'' : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]

lemma exp_mul_101 : Real.exp (Real.log X0 * 1.01) = X0 * Real.exp (Real.log X0 * 0.01) := by
  rw [show Real.log X0 * 1.01 = Real.log X0 + Real.log X0 * 0.01 by ring, Real.exp_add,
    Real.exp_log (X0_pos'' hX)]

lemma X0_le_of_edge {x : ℝ} (hx : Real.exp (Real.log X0 * 1.01) / 2 ≤ x) : (X0 : ℝ) ≤ x := by
  have hX0 := X0_pos'' hX
  rw [exp_mul_101 hX] at hx
  have := Real.add_one_le_exp (Real.log X0 * 0.01)
  nlinarith

lemma edge_A {x : ℝ} (hx : Real.exp (Real.log X0 * 1.01) / 2 ≤ x) :
    (X0 : ℝ) / x * Real.log x ≤ 2.02 * Real.log X0 * Real.exp (Real.log X0 * (-0.01)) := by
  have hX0 := X0_pos'' hX
  set x0 := Real.exp (Real.log X0 * 1.01) / 2 with hx0def
  have hx0e : x0 = X0 * Real.exp (Real.log X0 * 0.01) / 2 := by rw [hx0def, exp_mul_101 hX]
  have hE := Real.add_one_le_exp (Real.log X0 * 0.01)
  have he1 : Real.exp 1 ≤ x0 := by
    have : Real.exp 1 ≤ X0 := by
      rw [← Real.exp_log hX0]; exact Real.exp_le_exp.mpr (by linarith)
    rw [hx0e]; nlinarith
  have hanti := Real.log_div_self_antitoneOn (Set.mem_setOf.mpr he1)
    (Set.mem_setOf.mpr (he1.trans hx)) hx
  simp only at hanti
  have hx0pos : 0 < x0 := by positivity
  have hlx0' : Real.log x0 ≤ Real.log X0 * 1.01 := by
    rw [hx0def, Real.log_div (by positivity) (by norm_num), Real.log_exp]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hXx0 : (X0 : ℝ) / x0 = 2 * Real.exp (Real.log X0 * (-0.01)) := by
    have h2 := Real.exp_pos (Real.log X0 * 0.01)
    rw [hx0e, show (X0 : ℝ) / (X0 * Real.exp (Real.log X0 * 0.01) / 2) =
      2 / Real.exp (Real.log X0 * 0.01) by field_simp,
      show Real.log X0 * (-0.01) = -(Real.log X0 * 0.01) by ring, Real.exp_neg, div_eq_mul_inv]
  have : (X0 : ℝ) / x * Real.log x = X0 * (Real.log x / x) := by ring
  rw [this]
  calc (X0 : ℝ) * (Real.log x / x) ≤ X0 * (Real.log x0 / x0) :=
        mul_le_mul_of_nonneg_left hanti hX0.le
    _ = X0 / x0 * Real.log x0 := by ring
    _ ≤ 2 * Real.exp (Real.log X0 * (-0.01)) * (Real.log X0 * 1.01) := by
        rw [hXx0]
        exact mul_le_mul_of_nonneg_left hlx0' (by positivity)
    _ = 2.02 * Real.log X0 * Real.exp (Real.log X0 * (-0.01)) := by ring

lemma edge_B {x : ℝ} (hx2 : Real.log x ≤ Real.exp (Real.log X0 * (1 / 100))) :
    Construction.kappaParam X0 * Real.log x ≤
      0.01 * Real.log X0 * Real.exp (Real.log X0 * (-0.01)) := by
  have hX0 := X0_pos'' hX
  have h1 : Construction.kappaParam X0 * Real.log x ≤
      Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) * Real.exp (Real.log X0 * (1 / 100)) := by
    rw [kappa_eq_exp hX0]; exact mul_le_mul_of_nonneg_left hx2 (Real.exp_pos _).le
  rw [← Real.exp_add] at h1
  have e : Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ)) + Real.log X0 * (1 / 100) =
      Real.log X0 * (-0.01) + (-(Real.log X0 * (113 / 300))) := by ring
  rw [e, Real.exp_add] at h1
  have h3 : Real.exp (-(Real.log X0 * (113 / 300))) ≤ 0.01 := by
    have := Real.add_one_le_exp (Real.log X0 * (113 / 300))
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have h5 := Real.exp_pos (Real.log X0 * (-0.01))
  have h6 : Real.exp (Real.log X0 * (-0.01)) * Real.exp (-(Real.log X0 * (113 / 300))) ≤
      Real.exp (Real.log X0 * (-0.01)) * 0.01 := mul_le_mul_of_nonneg_left h3 h5.le
  nlinarith

lemma edge_C {x : ℝ} (hlx0 : 0 ≤ Real.log x)
    (hx2 : Real.log x ≤ Real.exp (Real.log X0 * (1 / 100))) :
    4 * Construction.kappaParam X0 * Real.log x ^ 5 ≤ Real.exp (Real.log X0 * (-0.34)) := by
  have hX0 := X0_pos'' hX
  have h5 : Real.log x ^ 5 ≤ Real.exp (Real.log X0 * (1 / 100)) ^ 5 := pow_le_pow_left₀ hlx0 hx2 5
  rw [← Real.exp_nat_mul] at h5
  have h6 : 4 * Construction.kappaParam X0 * Real.log x ^ 5 ≤
      4 * Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) *
        Real.exp ((5 : ℕ) * (Real.log X0 * (1 / 100))) := by
    rw [kappa_eq_exp hX0]; exact mul_le_mul_of_nonneg_left h5 (by positivity)
  refine h6.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  have e : Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ)) + (5 : ℕ) * (Real.log X0 * (1 / 100)) =
      Real.log X0 * (-0.34) + (-(Real.log X0 * (1 / 150))) := by push_cast; ring
  rw [e, Real.exp_add]
  have h7 : Real.exp (-(Real.log X0 * (1 / 150))) ≤ 1 / 4 := by
    have := Real.add_one_le_exp (Real.log X0 * (1 / 150))
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have h8 := Real.exp_pos (Real.log X0 * (-0.34))
  nlinarith

end numerics

/-- **Lemma 7.3(d)(iii)** for `ρ_edge`, from `GEdgeBound`, `KDiffBound`, the resolvent identity
(`rhoEdge_sub_g`) and the Lemma M bound (`abs_Rsh_le`, with `∑ 1/e ≤ log + 1` under (HBS)). -/
theorem lemma73diii_of {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m) (hXm2 : X0m ≤ X0) {tw : ℕ → ℝ}
    (ht : ∀ p, p.Prime → 0 < tw p) {xmax : ℝ} (hZ : xmax / X0m ≤ Z)
    (hG : GEdgeBound X0) (hK : KDiffBound P tw X0m X0 xmax) :
    Lemma73diii X0 xmax (KR.Sharp.rhoEdge P tw X0m X0) := by
  intro x hx1 hx2 hx3
  have hX0 := X0_pos'' hX
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hXm0 : 0 < X0m := by linarith
  have hX7 := h.X0m_ge
  rw [Real.rpow_def_of_pos hX0] at hx1 hx2 ⊢
  rw [Real.rpow_def_of_pos hX0]
  have hXx := X0_le_of_edge hX hx1
  have hlx : Real.log X0 ≤ Real.log x := Real.log_le_log hX0 hXx
  have hlx0 : 0 ≤ Real.log x := by linarith
  have hΛ0 : 0 < Real.log X0 := by linarith
  -- (i) the bound on `g`
  have hgi : |gEdge X0 x| * Real.log x ≤ 2.04 * Real.exp (Real.log X0 * (-0.01)) := by
    have hg := hG x hXx
    have hA := edge_A hX hx1
    have hB := edge_B hX hx2
    have hE := Real.exp_pos (Real.log X0 * (-0.01))
    have h1 : |gEdge X0 x| * Real.log x ≤
        1.0001 / Real.log X0 * (Construction.kappaParam X0 * Real.log x + X0 / x * Real.log x) := by
      have := mul_le_mul_of_nonneg_right hg hlx0
      linarith [show 1.0001 / Real.log X0 * (Construction.kappaParam X0 + X0 / x) * Real.log x =
        1.0001 / Real.log X0 * (Construction.kappaParam X0 * Real.log x + X0 / x * Real.log x)
        by ring]
    have h2 : 1.0001 / Real.log X0 * (Construction.kappaParam X0 * Real.log x +
        X0 / x * Real.log x) ≤ 1.0001 / Real.log X0 *
          (2.03 * Real.log X0 * Real.exp (Real.log X0 * (-0.01))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 1.0001 / Real.log X0 * (2.03 * Real.log X0 * Real.exp (Real.log X0 * (-0.01))) =
        1.0001 * 2.03 * Real.exp (Real.log X0 * (-0.01)) := by field_simp
    linarith
  -- (ii) the resolvent identity and the Lemma M bound
  have hres := rhoEdge_sub_g P tw hX hXm0 (by linarith : X0m ≤ x)
  set φ : ℝ → ℝ := fun u => KQ' X0 (gEdge X0) u - KR.Sharp.Kpt P tw X0m (gEdge X0) u
  have hφ : ∀ z, X0m ≤ z → z ≤ x →
      |φ z| ≤ 4 * Construction.kappaParam X0 * Real.log x ^ 3 := by
    intro z hz1 hz2
    rcases lt_or_ge z X0 with hz | hz
    · have h1 := KQ'_zero_below hX0 (gEdge X0) hz
      have h2 := Kpt_zero_below' P tw X0m (fun w hw => gEdge_zero_below hX0 hw) hz
      simp only [φ, h1, h2, sub_zero, abs_zero]; positivity
    · refine (hK z hz (hz2.trans hx3)).trans ?_
      have hl1 : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
      have hl2 : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) hz2
      have := pow_le_pow_left₀ hl1 hl2 3
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ 4 * Construction.kappaParam X0 by
        positivity)
      linarith
  have hb := abs_Rsh_le P tw ht hXm0 (by linarith : X0m ≤ x) hφ
  have hx1' : 1 ≤ x / X0m := by rw [le_div_iff₀ hXm0]; linarith
  have hxZ : x / X0m ≤ Z := (div_le_div_of_nonneg_right hx3 hXm0.le).trans hZ
  have hharm := h.harm_le hx1' hxZ
  have hlXm : 1 ≤ Real.log X0m := by
    rw [Real.le_log_iff_exp_le hXm0]
    have := Real.exp_one_lt_d9; linarith
  have hlog : Real.log (x / X0m) + 1 ≤ Real.log x := by
    rw [Real.log_div (by linarith) (by linarith)]; linarith
  have hii : |KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x| * Real.log x ≤
      Real.exp (Real.log X0 * (-0.34)) := by
    rw [hres]
    have h1 : |KR.Sharp.Rsh P tw X0m φ x| ≤
        4 * Construction.kappaParam X0 * Real.log x ^ 3 * Real.log x := by
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_left (hharm.trans hlog)
      positivity
    have h2 := mul_le_mul_of_nonneg_right h1 hlx0
    have e : 4 * Construction.kappaParam X0 * Real.log x ^ 3 * Real.log x * Real.log x =
        4 * Construction.kappaParam X0 * Real.log x ^ 5 := by ring
    have h3 := edge_C hX hlx0 hx2
    linarith
  -- assemble
  have htri : |KR.Sharp.rhoEdge P tw X0m X0 x| ≤
      |gEdge X0 x| + |KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x| := by
    have := abs_add_le (gEdge X0 x) (KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x)
    rwa [add_sub_cancel] at this
  have h4 := mul_le_mul_of_nonneg_right htri hlx0
  have hpos := Real.exp_pos (Real.log X0 * (-0.01))
  have e2 : (|gEdge X0 x| + |KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x|) * Real.log x =
      |gEdge X0 x| * Real.log x + |KR.Sharp.rhoEdge P tw X0m X0 x - gEdge X0 x| * Real.log x := by
    ring
  linarith

end BaseRange
