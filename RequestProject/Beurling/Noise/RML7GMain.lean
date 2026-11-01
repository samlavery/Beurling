module

public import RequestProject.Beurling.Noise.RML7GScale
public import RequestProject.Beurling.Noise.MarginPoint

/-!
# Lemma 5.34, second bullet (correction #110): `GScaleBound` for `G = K_pt F`

* `decidedSmall_of` : the realised decision order (`TNP.Hyp.dec_hi`, `dec_lo`, `H ≤ y/10`) gives
  `DecidedSmall` (a prime decided before `2v` is `≤ 3v`) at every scale `v > 0`, for the decision
  times read on the indices, `tI tw j = tw(qp j)`.
* `gScaleBound_Kpt` : **`GScaleBound` for `G = K_pt F`** with
  `A = 70 ∑_{j<J} (log 3v_j)² M_j`, `v_j = X₀⁻ 2^j`, whenever `|F| ≤ M_j` on `[v_j, 2v_j)`
  below `(x + H(x)/2)/2`. This is the input `hGf` (third conjunct) of `BModel.RML7.hG_field`
  for `F = (1 - B)F_c`, once the block bounds `M_j` of `(1 - B)F_c` are given.
* `abs_one_sub_Bavg_le` : the block bound of `(1 - B)F_c` (correction #110):
  `|F(s) - B F(s)| ≤ o + 2 max(…)` for `F = O + R` with `|O(s) - O(r)| ≤ o` on the window and
  `|R| ≤ R̄` there.
-/

@[expose] public section

open Finset Real BeurlingSystem KR.Sharp KR.TNP

namespace KR.RML7G

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- **`DecidedSmall` from the realised decision order**: `t(p) < 2v ⟹ p ≤ 3v`. -/
lemma decidedSmall_of (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {v : ℝ} (hv : 0 < v) :
    P.DecidedSmall (tI tw) v := by
  intro j hj
  simp only [tI] at hj
  by_cases hp : X0m / 2 ≤ P.p j
  · have h1 := (abs_le.mp (h.dec_hi j hp)).1
    have h2 := h.width.small _ hp
    linarith
  · push_neg at hp
    have := h.dec_lo j hp
    linarith

/-- **`GScaleBound` for `G = K_pt F`** (Lemma 5.34, second bullet, correction #110). -/
theorem gScaleBound_Kpt (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (hO : KR.Ops.OpHyp P H X0m)
    {X0 x : ℝ} (hX0 : 12 ≤ X0) (Nf : ℝ → ℕ) (F : ℝ → ℝ) {J : ℕ}
    (hJ : x + H x / 2 ≤ X0m * 2 ^ J) (hx1 : 1 ≤ x - H x / 2)
    (hwin : ∀ y, x - H x / 2 ≤ y → y ≤ x + H x / 2 → 2 * y / X0m ≤ Z)
    (M : ℕ → ℝ) (hM0 : ∀ j, 0 ≤ M j)
    (hF : ∀ j < J, ∀ s, X0m * 2 ^ j ≤ s → s < 2 * (X0m * 2 ^ j) →
      s ≤ (x + H x / 2) / 2 → |F s| ≤ M j) :
    GScaleBound P H X0 (Kpt P tw X0m F) x
      (70 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j) Nf
      (fun y u => ∑ j ∈ range J, M j * Ssup (P := P) (tI tw) X0m y u (X0m * 2 ^ j)) := by
  have hX := h.width.X0m_pos
  have hXm := h.hXm
  have hp2 := hO.p2
  have hbs := h.hbs
  have hv0 : ∀ j : ℕ, 0 < X0m * 2 ^ j := fun j => by positivity
  have hvX : ∀ j : ℕ, X0m ≤ X0m * 2 ^ j := fun j => by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : ∀ j : ℕ, 100000000 ≤ Real.log (3 * (X0m * 2 ^ j)) := fun j =>
    hXm.trans (Real.log_le_log hX (by linarith [hvX j]))
  have hds : ∀ j : ℕ, P.DecidedSmall (tI tw) (X0m * 2 ^ j) := fun j => decidedSmall_of h (hv0 j)
  intro y hy1 hy2
  have hy0 : 1 ≤ y := by linarith
  have hZy := hwin y hy1 hy2
  have hyJ : y ≤ X0m * 2 ^ J := by linarith
  have hFy : ∀ j < J, ∀ s, X0m * 2 ^ j ≤ s → s < 2 * (X0m * 2 ^ j) → s ≤ y / 2 →
      |F s| ≤ M j := fun j hj s h1 h2 h3 => hF j hj s h1 h2 (by linarith)
  -- `t/v ≤ Z` below `y`
  have htZ : ∀ j : ℕ, ∀ t, 0 < t → t ≤ y → t / (X0m * 2 ^ j) ≤ Z := by
    intro j t ht hty
    have h1 : t / (X0m * 2 ^ j) ≤ t / X0m := div_le_div_of_nonneg_left ht.le hX (hvX j)
    have h2 : t / X0m ≤ 2 * y / X0m := div_le_div_of_nonneg_right (by linarith) hX.le
    linarith
  have hSs0 : ∀ u, ∀ j : ℕ, 0 ≤ Ssup (P := P) (tI tw) X0m y u (X0m * 2 ^ j) := fun u j =>
    Real.iSup_nonneg fun t => P.omegaW_nonneg _ _ _
  refine ⟨?_, ?_, ?_⟩
  · -- `log y · |G y| ≤ A`
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy0
    have hpt := abs_Kpt_le P tw hX hp2 F hyJ M hM0 hFy
    calc Real.log y * |Kpt P tw X0m F y|
        ≤ Real.log y * ∑ j ∈ range J, P.omegaW (tI tw) y (X0m * 2 ^ j) * M j :=
          mul_le_mul_of_nonneg_left hpt hly
      _ = ∑ j ∈ range J, (Real.log y * P.omegaW (tI tw) y (X0m * 2 ^ j)) * M j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j ∈ range J, (2.9 * Real.log (3 * (X0m * 2 ^ j))) * M j := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hM0 j)
          exact Margin.Var.logt_omega_le hbs (hds j) (hv0 j) (hL j) (by linarith)
            (htZ j y (by linarith) le_rfl)
      _ ≤ 70 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          have hl := hL j
          have : 2.9 * Real.log (3 * (X0m * 2 ^ j)) ≤
              70 * Real.log (3 * (X0m * 2 ^ j)) ^ 2 := by nlinarith
          nlinarith [hM0 j]
  · intro u hu
    have hupos : 3 ≤ u := by
      obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (hSs0 u j), ?_⟩
    intro n hn hn2 t ht
    by_cases ht2 : t < 2 * X0m
    · rw [KR.Ops.Kpt_zero_low hX hp2 F ht2, abs_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (hSs0 u j)
    push_neg at ht2
    obtain ⟨-, hnu1, hnu2⟩ := (mem_NW P (by linarith : (0 : ℝ) < u)).mp hn
    have hV2 : 2 ≤ Vl P n := KR.Ops.Vl_ge_two (P := P) hp2 hn2
    set s := posn P.labelVal y n with hs
    have hsdef : s = y / LemmaM.valN P.labelVal n := rfl
    have hsy : s ≤ y / 2 := by
      rw [hsdef]; exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hV2
    rw [← hsdef] at hnu1 hnu2
    have hsX : X0m / 2 ≤ s := by
      by_contra hc; push_neg at hc
      have := hO.low s hc
      have h1 := (abs_le.mp ht).2
      linarith
    have hHs := hO.small s hsX
    have hHs0 := (hO.pos s).le
    obtain ⟨ht1, ht1'⟩ := abs_le.mp ht
    have hT1 : 0.89 * u ≤ t := by linarith
    have hT2 : t ≤ 2.21 * u := by linarith
    have hT4 : t ≤ 0.56 * y := by linarith
    have ht0 : 0 < t := by linarith
    have htJ : t ≤ X0m * 2 ^ J := by linarith
    have hFt : ∀ j < J, ∀ s', X0m * 2 ^ j ≤ s' → s' < 2 * (X0m * 2 ^ j) → s' ≤ t / 2 →
        |F s'| ≤ M j := fun j hj s' h1 h2 h3 => hFy j hj s' h1 h2 (by linarith)
    refine (abs_Kpt_le P tw hX hp2 F htJ M hM0 hFt).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm (M j)]
    refine mul_le_mul_of_nonneg_right ?_ (hM0 j)
    unfold Ssup
    have hbdd : BddAbove (Set.range fun r : {r : ℝ // 0.89 * u ≤ r ∧ r ≤ 2.21 * u ∧
        2 * X0m ≤ r ∧ r ≤ 0.56 * y} => P.omegaW (tI tw) r (X0m * 2 ^ j)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨r, rfl⟩
      exact hbs.lemS_i _ (hv0 j) (htZ j r (by linarith [r.2.2.2.1]) (by linarith [r.2.2.2.2]))
    exact le_ciSup (f := fun r : {r : ℝ // 0.89 * u ≤ r ∧ r ≤ 2.21 * u ∧
        2 * X0m ≤ r ∧ r ≤ 0.56 * y} => P.omegaW (tI tw) r (X0m * 2 ^ j)) hbdd
      ⟨t, hT1, hT2, ht2, hT4⟩
  · -- the scale sum
    calc ∑ u ∈ dyScales X0 y (Nf y), Real.log (2 * u) *
          ∑ j ∈ range J, M j * Ssup (P := P) (tI tw) X0m y u (X0m * 2 ^ j)
        = ∑ j ∈ range J, M j * ∑ u ∈ dyScales X0 y (Nf y),
            Real.log (2 * u) * Ssup (P := P) (tI tw) X0m y u (X0m * 2 ^ j) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => by ring
      _ ≤ ∑ j ∈ range J, M j * (66 * Real.log (3 * (X0m * 2 ^ j)) ^ 2) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hM0 j)
          exact scale_sum_le hbs (tI tw) hX0 (hds j) (hvX j) hX (hL j) hZy
      _ ≤ 70 * ∑ j ∈ range J, Real.log (3 * (X0m * 2 ^ j)) ^ 2 * M j := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j _ => ?_
          have := hM0 j
          have := sq_nonneg (Real.log (3 * (X0m * 2 ^ j)))
          nlinarith

/-- **The block bound of `(1 - B)F_c`** (correction #110): if `F = O + R` near `s`, with
`|O(r) - O(s)| ≤ o` and `|R(r)| ≤ R̄` on the window `[s - H/2, s + H/2]`, then
`|F(s) - (B F)(s)| ≤ o + 2R̄`. -/
lemma abs_sub_Bavg_le {Hs s o Rb : ℝ} (hH : 0 < Hs) {F O R : ℝ → ℝ}
    (hFOR : ∀ r, F r = O r + R r)
    (hint : IntervalIntegrable F MeasureTheory.volume (s - Hs / 2) (s + Hs / 2))
    (hO : ∀ r, s - Hs / 2 ≤ r → r ≤ s + Hs / 2 → |O r - O s| ≤ o)
    (hR : ∀ r, s - Hs / 2 ≤ r → r ≤ s + Hs / 2 → |R r| ≤ Rb) :
    |F s - Margin.Bavg Hs F s| ≤ o + 2 * Rb := by
  have hab : s - Hs / 2 ≤ s + Hs / 2 := by linarith
  have hlen : |s + Hs / 2 - (s - Hs / 2)| = Hs := by rw [abs_of_pos (by linarith)]; ring
  have heq : F s - Margin.Bavg Hs F s =
      Hs⁻¹ * ∫ r in (s - Hs / 2)..(s + Hs / 2), (F s - F r) := by
    unfold Margin.Bavg
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const, smul_eq_mul, mul_sub]
    field_simp
    ring
  have hpt : ∀ r ∈ Set.uIoc (s - Hs / 2) (s + Hs / 2), ‖F s - F r‖ ≤ o + 2 * Rb := by
    intro r hr
    rw [Set.uIoc_of_le hab] at hr
    rw [Real.norm_eq_abs, hFOR s, hFOR r]
    have h1 := hO r hr.1.le hr.2
    have h2 := hR r hr.1.le hr.2
    have h3 := hR s (by linarith) (by linarith)
    calc |O s + R s - (O r + R r)| = |-(O r - O s) + R s - R r| := by ring_nf
      _ ≤ |-(O r - O s)| + |R s| + |R r| := by
          refine (abs_sub _ _).trans ?_
          linarith [abs_add_le (-(O r - O s)) (R s)]
      _ ≤ o + 2 * Rb := by rw [abs_neg]; linarith
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, hlen] at hI
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hH)]
  calc Hs⁻¹ * |∫ r in (s - Hs / 2)..(s + Hs / 2), (F s - F r)| ≤ Hs⁻¹ * ((o + 2 * Rb) * Hs) :=
        mul_le_mul_of_nonneg_left hI (inv_pos.mpr hH).le
    _ = o + 2 * Rb := by field_simp

end KR.RML7G

end
