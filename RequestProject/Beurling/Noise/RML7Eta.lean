module

public import RequestProject.Beurling.Noise.TauNearLocMain
public import RequestProject.Beurling.Noise.RML6BridgeNum

/-!
# Lemma 5.20, last claim: `log y · η(y)` uniformly small (the field `hsη`)

`logy_eta_le` : at every height `y ≥ 1` with `9y ≤ Z²` (and `2500 ≤ Z`),

  `log y · η(y) = log y ∑_{w τ-near at y} 1/w ≤ 831200 Φ₂(X₀⁻/2)`,

uniformly in `y` (04k-kernels.tex, Lemma 5.20: `sup_y log y · η(y) ≤ e^{-0.99Λ}`). The proof is
the block bound of Lemma 5.20 with the constant weight `log y`: the cofactor `m` of a `τ`-near
`w = pm` at the block `P_k` is `3P_k`-smooth with `m > y/(4P_k²)`, so
`log y < log m + log(4P_k²)`, and the Euler bounds for `∑ 1/m` and `∑ log m/m` over the
smooth `m` (`smooth_harm_le_loc`, `smooth_logharm_le_loc`) give `≤ 7240 (log P_k + 2)²` per
block, which is `Φ₂`-summable (`decay_sum`).

`hsη_of` : the field `hsη` of `BModel.RealMarginLoc` for `η := etaG … (fun _ => 1)` (the
`τ`-near `η`) and `sη := 831200 Φ₂(X₀⁻/2)`; `sη_tiny` : `sη ≤ 831200 e^{-200}` under the width
bound `H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- The block sum with the weight `log y`: `∑_{m ∈ Sm_k(y)} log y/m ≤ 7240 (log P_k + 2)²`. -/
lemma sum_Sm_logy_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {y : ℝ} (hy : 1 ≤ y)
    (hZ0 : 2500 ≤ Z) (hZ : 9 * y ≤ Z ^ 2) (k : ℕ) :
    ∑ e ∈ Sm P X0m k y, Real.log y / P.val e ≤ 7240 * (Real.log (Pk X0m k) + 2) ^ 2 := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hk1 := Pk_ge_one hX h.hXm k
  have hk0 := Pk_pos hX k
  have hl3 := log_three_mul_le hX k
  have hl := log_Pk_ge hX h.hXm k
  set ℓ := Real.log (Pk X0m k)
  rcases (Sm P X0m k y).eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he, Finset.sum_empty]; positivity
  have hz : 3 * Pk X0m k ≤ Z := by
    simp only [Sm, Finset.mem_filter, mem_elems] at he0
    have h1 := (P.one_le_val e0).trans he0.1
    rw [le_div_iff₀ (by positivity)] at h1
    have hsq : (3 * Pk X0m k) ^ 2 ≤ Z ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).mp hsq
  have hsm : ∀ e ∈ Sm P X0m k y, ∀ i ∈ e.support, P.p i ≤ 3 * Pk X0m k := by
    intro e he i hi
    simp only [Sm, Finset.mem_filter] at he
    exact he.2.2 i hi
  have h1 := smooth_harm_le_loc h.hbs (by linarith) hz hZ0 _ hsm
  have h2 := smooth_logharm_le_loc h.hbs (by linarith) hz hZ0 _ hsm
  -- `log y < log m + log(4 P_k²)` on `Sm`
  have h4 : Real.log (4 * Pk X0m k ^ 2) = Real.log 4 + 2 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hl4 : Real.log 4 ≤ 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; have := Real.log_two_lt_d9; linarith
  have hpt : ∀ e ∈ Sm P X0m k y, Real.log y / P.val e ≤
      Real.log (P.val e) / P.val e + (Real.log 4 + 2 * ℓ) * (1 / P.val e) := by
    intro e he
    simp only [Sm, Finset.mem_filter] at he
    have hv := P.val_pos e
    have hlt : y < 4 * Pk X0m k ^ 2 * P.val e := by
      have := he.2.1; rw [div_lt_iff₀ (by positivity)] at this; linarith
    have hly : Real.log y ≤ Real.log (P.val e) + (Real.log 4 + 2 * ℓ) := by
      have := Real.log_le_log (by linarith) hlt.le
      rw [Real.log_mul (by positivity) hv.ne', h4] at this; linarith
    calc Real.log y / P.val e ≤ (Real.log (P.val e) + (Real.log 4 + 2 * ℓ)) / P.val e :=
          div_le_div_of_nonneg_right hly hv.le
      _ = _ := by field_simp
  calc ∑ e ∈ Sm P X0m k y, Real.log y / P.val e
      ≤ ∑ e ∈ Sm P X0m k y, (Real.log (P.val e) / P.val e +
          (Real.log 4 + 2 * ℓ) * (1 / P.val e)) := Finset.sum_le_sum hpt
    _ = (∑ e ∈ Sm P X0m k y, Real.log (P.val e) / P.val e) +
          (Real.log 4 + 2 * ℓ) * ∑ e ∈ Sm P X0m k y, 1 / P.val e := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 3620 * Real.log (3 * Pk X0m k) * (Real.log (3 * Pk X0m k) + 0.43) +
          (1.39 + 2 * ℓ) * (1810 * Real.log (3 * Pk X0m k)) := by
        have hL3 : 0 ≤ Real.log (3 * Pk X0m k) := Real.log_nonneg (by linarith)
        have hS0 : 0 ≤ ∑ e ∈ Sm P X0m k y, 1 / P.val e :=
          Finset.sum_nonneg fun e _ => (one_div_pos.mpr (P.val_pos e)).le
        have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        nlinarith
    _ ≤ 7240 * (ℓ + 2) ^ 2 := by
        have hL3 : 0 ≤ Real.log (3 * Pk X0m k) := Real.log_nonneg (by linarith)
        nlinarith

/-- **Lemma 5.20, last claim**: `log y · η(y) ≤ 831200 Φ₂(X₀⁻/2)` at every height `y ≥ 1` with
`9y ≤ Z²`, uniformly in `y`. -/
theorem logy_eta_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {y : ℝ} (hy : 1 ≤ y)
    (hZ0 : 2500 ≤ Z) (hZ : 9 * y ≤ Z ^ 2) :
    Real.log y * etaG P H tw X0m (fun _ => 1) y ≤ 831200 * Phi H 2 (X0m / 2) := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  obtain ⟨K, hK⟩ := exists_K hX (√y + 1)
  have hK' : √y < Pk X0m K := by linarith
  have heq : Real.log y * etaG P H tw X0m (fun _ => 1) y =
      etaG P H tw X0m (fun _ => Real.log y) y := by
    unfold etaG; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [heq]
  refine (etaG_le_blocks h (by linarith) hK' (Ψ := fun _ => Real.log y) (fun _ => hly)
    (fun _ _ _ _ _ => le_rfl)).trans ?_
  calc ∑ k ∈ range K, 56 * H (Pk X0m k) * Real.log y / Pk X0m k *
        ∑ e ∈ Sm P X0m k y, 1 / P.val e
      ≤ ∑ k ∈ range K, 405440 * Phi H 2 (Pk X0m k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk0 := Pk_pos hX k
        have hHk := hP.reg.pos (Pk X0m k)
        have hb := sum_Sm_logy_le h hy hZ0 hZ k
        have e1 : 56 * H (Pk X0m k) * Real.log y / Pk X0m k *
            ∑ e ∈ Sm P X0m k y, 1 / P.val e =
            56 * H (Pk X0m k) / Pk X0m k * ∑ e ∈ Sm P X0m k y, Real.log y / P.val e := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
        rw [e1]
        have hc : 0 ≤ 56 * H (Pk X0m k) / Pk X0m k := by positivity
        calc 56 * H (Pk X0m k) / Pk X0m k * ∑ e ∈ Sm P X0m k y, Real.log y / P.val e
            ≤ 56 * H (Pk X0m k) / Pk X0m k * (7240 * (Real.log (Pk X0m k) + 2) ^ 2) :=
              mul_le_mul_of_nonneg_left hb hc
          _ = 405440 * Phi H 2 (Pk X0m k) := by unfold Phi; ring
    _ ≤ 831200 * Phi H 2 (X0m / 2) := by
        rw [← Finset.mul_sum, ← Pk_zero]
        have := decay_sum hP h.hXm (a := 2) (by norm_num) K
        have := Phi_nonneg hP 2 (Pk_ge hX 0) (Pk_ge_one hX h.hXm 0)
        nlinarith

/-- **The field `hsη` of `BModel.RealMarginLoc`**, for `η := etaG … (fun _ => 1)` (the `τ`-near
`η(t) = ∑_{w τ-near at t} 1/w`) and `sη := 831200 Φ₂(X₀⁻/2)`: for every height `t ≤ b` with
`t ≥ 1` (in particular `t ≥ X₀^{1.01}`), given `2500 ≤ Z` and `9b ≤ Z²`. -/
theorem hsη_of (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {b X1 : ℝ} (hX1 : 1 ≤ X1)
    (hZ0 : 2500 ≤ Z) (hbZ : 9 * b ≤ Z ^ 2) :
    ∀ t, X1 ≤ t → t ≤ b →
      Real.log t * etaG P H tw X0m (fun _ => 1) t ≤ 831200 * Phi H 2 (X0m / 2) :=
  fun t ht htb => logy_eta_le h (hX1.trans ht) hZ0 (by linarith)

/-- The size of `sη`: `831200 Φ₂(X₀⁻/2) ≤ 831200 e^{-200}` (≤ `10⁻⁸⁰`) under the width bound
`H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}` (`Hc_Xm_half_le` for the realised width). -/
theorem sη_tiny (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) :
    831200 * Phi H 2 (X0m / 2) ≤ 831200 * Real.exp (-200) := by
  have := KR.WidthReal.Phi_tiny h hH (a := 2) (by norm_num)
  linarith

end KR.TNP

end
