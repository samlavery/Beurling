module

public import RequestProject.Beurling.Noise.KRHord
public import RequestProject.Beurling.Noise.KRWeightsMain
public import RequestProject.Beurling.Noise.BSL57Final

/-!
# Corollary 5.17(b) with `C_N`, under (HBS) and `λ₀ ≤ 1.001` only

* `cor_5_17_b_B` : Corollary 5.17(b) with the sums `A₀`, `A₁` read only up to `y/u`
  (`HordSumsB`; the proof is that of `cor_5_17_b`);
* `cor_5_17_b_full` : for a Beurling system satisfying (HBS) on `[1, Z]` with
  `log X₀⁻ ≥ 10⁸`, the paper's width hypotheses (`PaperWidth`), primes `≥ 2`, a decision order
  with `p ≤ 2t(p)`, and `1 + 2θ ≤ λ₀ ≤ 1.001`: for every start `y ≥ X₀⁻` and
  `X₀⁻/2 ≤ u ≤ y` with `2y/X₀⁻ ≤ Z` and `log X₀ ≤ log 2u`,
  `W^nom_y(u) ≤ C_N log(2u)/log y`, `C_N = C_S(2.04 + 4.71/log X₀)`.
  Corollary 5.9 (from Theorem 5.6, `theorem_5_6_hbs_full`), `hordSumsB` and the numerical
  conditions (`A₀ ≤ 2.0674`, `A₁ ≤ 9.4091`, correction #103) are all discharged.
-/

@[expose] public section

open BeurlingSystem

namespace KR

variable (P : BeurlingSystem)

/-- **Corollary 5.17(b)** with the ordered-factorisation sums read up to `y/u`. -/
theorem cor_5_17_b_B {H : ℝ → ℝ} {X0m ε θ lam0 CS A0 A1 : ℝ} {tw : ℕ → ℝ} {y u : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) (hy1 : 1 < y) (hu : X0m / 2 ≤ u)
    (huy : u ≤ y) (hCS : 0 ≤ CS) (hS : SaiasAt P tw X0m y CS) (hA : HordSumsB P ε A0 A1 (y / u))
    (hu1 : 1 / 2 ≤ u) :
    Wnom P H tw X0m y u ≤
      CS * ((1 + 1 / 2 * lam0 * A0) * Real.log (2 * u) + 1 / 2 * lam0 * A1) / Real.log y := by
  have hX := hP.X0m_pos
  have hu0 : 0 < u := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hl2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  have ha := cor_5_17_a hP hp2 ht hlam hy hu (P := P) (tw := tw) (u := u)
  have hMS : ∀ m ∈ MS P y u, 2 ≤ m := fun m hm => (Finset.mem_filter.mp hm).2
  have hMSB : ∀ m ∈ MS P y u, 2 ≤ m ∧ V m ≤ y / u := by
    intro m hm
    refine ⟨hMS m hm, ?_⟩
    obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    simp only [V]; rw [P.valN_iota]; exact P.mem_elems.mp he
  obtain ⟨hA0, hA1⟩ := hA (MS P y u) hMSB
  have hterm : ∀ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
      P.Wsh tw X0m y (u * V m) ≤ CS / Real.log y * ((BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) * Real.log (2 * u) + (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
          Real.log (V m)) := by
    intro m hm
    obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    have hVe : V (iota e) ≤ y / u := by
      simp only [V]; rw [P.valN_iota]; exact (P.mem_elems.mp he)
    have hV1 : 1 ≤ V (iota e) := LemmaM.one_le_valN _ fun r _ => P.one_le_labelVal r
    have hv1 : X0m / 2 ≤ u * V (iota e) := by nlinarith
    have hv2 : u * V (iota e) ≤ y := by rw [le_div_iff₀ hu0] at hVe; linarith
    have hw := hS _ hv1 hv2
    have hc0 : 0 ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) := by
      have := hV (iota e); positivity
    have e2 : Real.log (2 * (u * V (iota e))) = Real.log (2 * u) + Real.log (V (iota e)) := by
      rw [← mul_assoc, Real.log_mul (by positivity) (hV _).ne']
    calc (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          P.Wsh tw X0m y (u * V (iota e))
        ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          (CS * Real.log (2 * (u * V (iota e))) / Real.log y) :=
          mul_le_mul_of_nonneg_left hw hc0
      _ = _ := by rw [e2]; field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hW0 := hS u hu huy
  have hB : CS / Real.log y * ((∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) *
      Real.log (2 * u) + ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
        Real.log (V m)) ≤ CS / Real.log y * (A0 * Real.log (2 * u) + A1) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hCS hly.le)
    have := mul_le_mul_of_nonneg_right hA0 hl2u
    linarith
  calc Wnom P H tw X0m y u
      ≤ P.Wsh tw X0m y u + 1 / 2 * lam0 * ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) *
          V m ^ (ε - 2) * P.Wsh tw X0m y (u * V m) := ha
    _ ≤ CS * Real.log (2 * u) / Real.log y + 1 / 2 * lam0 *
          (CS / Real.log y * (A0 * Real.log (2 * u) + A1)) := by
        gcongr
        exact hsum.trans hB
    _ = _ := by field_simp; ring

/-- Theorem 5.6 on `[1, Z]` from (HBS). -/
theorem thm56_of_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) : P.Thm56 Z :=
  fun _ _ ht hτ htY hYZ => P.theorem_5_6_hbs_full h ht hτ htY hYZ

/-- **Corollary 5.17(b)** with `C_N = C_S(2.04 + 4.71/log X₀)`, under (HBS) and
`1 + 2θ ≤ λ₀ ≤ 1.001`; no other hypothesis on `𝒩`. -/
theorem cor_5_17_b_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {H : ℝ → ℝ} {ε θ lam0 : ℝ} {tw : ℕ → ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001) {X0 y u : ℝ} (hy : X0m ≤ y)
    (hu : X0m / 2 ≤ u) (huy : u ≤ y) (hZ : 2 * y / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0u : Real.log X0 ≤ Real.log (2 * u)) :
    Wnom P H tw X0m y u ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 *
      (2.04 + 4.71 / Real.log X0) * Real.log (2 * u) / Real.log y := by
  have hX := h.X0m_ge
  have hXp := h.X0m_pos
  have hy1 : 1 < y := by norm_num at hX; linarith
  have hu0 : 0 < u := by linarith
  have hCS : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_of_le_right (by norm_num)
  have hB : y / u ≤ Z := by
    refine le_trans ?_ hZ
    rw [div_le_div_iff₀ hu0 hXp]; nlinarith
  have hε : ε ≤ 0.03 := by have := hP.eps_le; linarith
  have hA := hordSumsB P h hXm hε hB
  have hb := cor_5_17_b_B P (lam0 := lam0) hP hp2 ht hlam hy hy1 hu huy hCS
    (saiasAt_of_hbs P h hXm (thm56_of_hbs P h) ht htv hy hZ) hA
    (by norm_num at hX; linarith)
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  refine cor_5_17_b_CN hCS hy1 hX0 hX0u ?_ ?_ hb
  · nlinarith
  · nlinarith

end KR

end
