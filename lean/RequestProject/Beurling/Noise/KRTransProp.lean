module

public import RequestProject.Beurling.Noise.KRTransMain
public import RequestProject.Beurling.Noise.KRTrueTerm

/-!
# Proposition 5.18 with the transfer bound and Corollary 5.17(b) discharged

* `nomWeights_full` : `NomWeights` (Corollary 5.17(b) at the scales) under (HBS),
  `λ₀ ≤ 1.001` and a scale family of dyadic type (`2u ≤ X₀⁻` or `2u ≥ X₀`), with
  `C_N = C_S(2.04 + 4.71/log X₀)`;
* `prop_5_18_hbs`, `prop_5_18_terminal_hbs` : the three window bounds of Proposition 5.18 with
  `NomWeights` and `TransferBound` proved (`transferBound`); the remaining inputs are those of
  Lemma 5.20 (`EtaBound`, `λ₀ C_N E_η ≤ ½`) and, for the terminal blocks, `EtaX0Sum`
  (step (iii)).
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem) {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m : ℝ}

/-- **Corollary 5.17(b) at the scales** (`NomWeights`) under (HBS). -/
theorem nomWeights_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) {X0 x : ℝ} (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z)
    (hX0 : 0 < Real.log X0) (hX0m : X0m ≤ X0) {Sc : Finset ℝ} (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) :
    NomWeights P H tw X0m x Sc
      (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) := by
  intro u hu
  have hX := h.X0m_ge
  have hx1 : 1 < x := by norm_num at hX; linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hu1 := hSc1 u hu
  have hu0 : 0 < u := by linarith
  have hCS : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_max_of_le_right (by norm_num)
  have hK0 : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0) *
      Real.log (2 * u) / Real.log x := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * u by linarith)
    positivity
  have hV1 : ∀ m, 1 ≤ LemmaM.valN P.labelVal m := KR.one_le_valN_label P
  rcases lt_or_ge x u with hxu | hux
  · have : NW P x u = ∅ := by
      ext m
      simp only [Finset.notMem_empty, iff_false]
      intro hm
      obtain ⟨-, h1, -⟩ := (mem_NW P hu0).mp hm
      have := div_le_self (by linarith : (0 : ℝ) ≤ x) (hV1 m)
      linarith
    rw [Wnom, this, Finset.sum_empty]; exact hK0
  rcases hSc u hu with hlow | hhigh
  · have : Wnom P H tw X0m x u = 0 := by
      rw [Wnom]
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨hm0, -, h2⟩ := (mem_NW P hu0).mp hm
      rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · obtain rfl : m = 1 := by omega
        rw [LemmaM.valN_one, div_one] at h2; linarith
      · rw [kN_eq_zero (P := P) hm2 (by linarith), eVariationOn_zero_fun, ENNReal.toReal_zero,
          zero_div]
    rw [this]; exact hK0
  · exact cor_5_17_b_full P h hXm hP hp2 ht htv hlam hlam1 hx (by linarith) hux hxZ hX0
      (Real.log_le_log (by linarith) hhigh)

/-- **Proposition 5.18 (true kernels), first two bounds**, under (HBS), with
`C_N = C_S(2.04 + 4.71/log X₀)`; the remaining inputs are Lemma 5.20 (`EtaBound`,
`λ₀ C_N E_η ≤ ½`). -/
theorem prop_5_18_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2) :
    ∀ u ∈ Sc, WopNT P H tw X0m x X0 u ≤
        2 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
          Real.log (2 * u) / Real.log x ∧
      (2 * X0 ≤ u → Wop P H tw X0m x u ≤
        2 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
          Real.log (2 * u) / Real.log x) := by
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hCN : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0) := by
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  exact prop_5_18 hP hX0e hp2 ht hlam hx hX1 hCN hcov hSc1 hEta hE
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc)
    (transferBound P h hXm hP hp2 ht htv hlam hlam1 hxZ hX0 hX0m hSc1 hSc)

/-- **Proposition 5.18, the terminal blocks** (`u ∈ {X₀/2, X₀}`), under (HBS); the remaining
inputs are Lemma 5.20 and `EtaX0Sum` (step (iii)). -/
theorem prop_5_18_terminal_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {ε θ lam0 X0 x : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r) (hlam : 1 + 2 * θ ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hx : X0m ≤ x) (hxZ : 2 * x / X0m ≤ Z) (hX0 : 0 < Real.log X0)
    (hX0m : X0m ≤ X0) {Sc : Finset ℝ} {s s0 : ℝ → ℝ}
    (hcov : ∀ d ∈ NAll P x X0m, ∃ v ∈ Sc, d ∈ NW P x v) (hSc1 : ∀ u ∈ Sc, 1 / 2 ≤ u)
    (hSc : ∀ u ∈ Sc, 2 * u ≤ X0m ∨ X0 ≤ 2 * u) (hEta : EtaBound P H tw X0m Sc s)
    (hE : lam0 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
      ∑ v ∈ Sc, Real.log (2 * v) * s v ≤ 1 / 2)
    (hX0s : EtaX0Sum P H X0m X0 Sc s0) {u : ℝ} (hu : u ∈ Sc)
    (hlog : 1.52 * Real.log (2 * X0) ≤ 1.53 * Real.log (2 * u)) :
    Wop P H tw X0m x u ≤
      5.1 * (max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0)) *
        Real.log (2 * u) / Real.log x := by
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  have hCN : 0 ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 * (2.04 + 4.71 / Real.log X0) := by
    have : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
      le_max_of_le_right (by norm_num)
    positivity
  exact prop_5_18_terminal hP hX0e hp2 ht hlam hx hX1 hCN hcov hSc1 hEta hE
    (nomWeights_full P h hXm hP hp2 ht htv hlam hlam1 hx hxZ hX0 hX0m hSc1 hSc)
    (transferBound P h hXm hP hp2 ht htv hlam hlam1 hxZ hX0 hX0m hSc1 hSc) hX0s hu hlog

end KR

end
