module

public import RequestProject.Beurling.Noise.TauNearProofEuler

/-!
# Lemma 5.20: summation over the scales and the dyadic decay

* `card_window_le_three` : a `2`-separated family of scales has at most three members in any
  `[a, 8a)` (each pair `(P, m)` "occurs for at most three dyadic `v`");
* `decay_sum` : the dyadic decay `∑_{k<K} Φ(P_k) ≤ 2.05 Φ(P₀)` for
  `Φ_a(P) = H(P)(log P + 2)^a/P`, `a ≤ 3` (`(RH)`: ratio `≤ 0.51`, the paper's `0.52`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {X0m ε θ : ℝ}

/-- `2`-separated scales: `v < w ⇒ 2v ≤ w`. -/
def Sep (Sc : Finset ℝ) : Prop := ∀ v ∈ Sc, ∀ w ∈ Sc, v < w → 2 * v ≤ w

/-- A `2`-separated family has at most three members in `[a, 8a)`. -/
theorem card_window_le_three {Sc : Finset ℝ} (hS : Sep Sc) {a : ℝ} (ha : 0 < a) :
    (Sc.filter (fun v => a ≤ v ∧ v < 8 * a)).card ≤ 3 := by
  by_contra hc
  push_neg at hc
  set F := Sc.filter (fun v => a ≤ v ∧ v < 8 * a)
  -- four members `v₁ < v₂ < v₃ < v₄`
  obtain ⟨v1, hv1, hmin⟩ := F.exists_min_image id (Finset.card_pos.mp (by omega))
  set F1 := F.erase v1
  have hF1 : 3 ≤ F1.card := by rw [Finset.card_erase_of_mem hv1]; omega
  obtain ⟨v2, hv2, hmin2⟩ := F1.exists_min_image id (Finset.card_pos.mp (by omega))
  set F2 := F1.erase v2
  have hF2 : 2 ≤ F2.card := by rw [Finset.card_erase_of_mem hv2]; omega
  obtain ⟨v3, hv3, hmin3⟩ := F2.exists_min_image id (Finset.card_pos.mp (by omega))
  set F3 := F2.erase v3
  have hF3 : 1 ≤ F3.card := by rw [Finset.card_erase_of_mem hv3]; omega
  obtain ⟨v4, hv4⟩ := Finset.card_pos.mp (show 0 < F3.card by omega)
  have m2 := Finset.mem_of_mem_erase hv2
  have m3 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv3)
  have m4 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv4))
  have n12 : v2 ≠ v1 := Finset.ne_of_mem_erase hv2
  have n23 : v3 ≠ v2 := Finset.ne_of_mem_erase hv3
  have n34 : v4 ≠ v3 := Finset.ne_of_mem_erase hv4
  have h12 : v1 < v2 := lt_of_le_of_ne (hmin v2 m2) (Ne.symm n12)
  have h23 : v2 < v3 := lt_of_le_of_ne (hmin2 v3 (Finset.mem_of_mem_erase hv3)) (Ne.symm n23)
  have h34 : v3 < v4 := lt_of_le_of_ne (hmin3 v4 (Finset.mem_of_mem_erase hv4)) (Ne.symm n34)
  have s1 := (Finset.mem_filter.mp hv1)
  have s4 := (Finset.mem_filter.mp m4)
  have s2 := (Finset.mem_filter.mp m2)
  have s3 := (Finset.mem_filter.mp m3)
  have e1 := hS v1 s1.1 v2 s2.1 h12
  have e2 := hS v2 s2.1 v3 s3.1 h23
  have e3 := hS v3 s3.1 v4 s4.1 h34
  linarith [s1.2.1, s4.2.2]

/-- **Regrouping over the scales**: `∑_v L(v) ∑_{m ∈ B(v)} f(m) ≤ ∑_{m ∈ U} f(m) · max L ·
#{v : m ∈ B(v)}`, written as `∑_{m ∈ U} f(m) ∑_{v : m ∈ B(v)} L(v)`. -/
theorem sum_scales_swap {ι : Type*} [DecidableEq ι] (Sc : Finset ℝ) (B : ℝ → Finset ι)
    (f : ι → ℝ) (L : ℝ → ℝ) :
    ∑ v ∈ Sc, L v * ∑ m ∈ B v, f m =
      ∑ m ∈ Sc.biUnion B, f m * ∑ v ∈ Sc.filter (fun v => m ∈ B v), L v := by
  classical
  calc ∑ v ∈ Sc, L v * ∑ m ∈ B v, f m = ∑ v ∈ Sc, ∑ m ∈ B v, L v * f m :=
        Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]
    _ = ∑ m ∈ Sc.biUnion B, ∑ v ∈ Sc.filter (fun v => m ∈ B v), L v * f m := by
        apply Finset.sum_comm'
        intro v m
        simp only [Finset.mem_filter, Finset.mem_biUnion]
        constructor
        · rintro ⟨hv, hm⟩; exact ⟨⟨hv, hm⟩, v, hv, hm⟩
        · rintro ⟨⟨hv, hm⟩, -⟩; exact ⟨hv, hm⟩
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring

/-- `Φ_a(P) = H(P)(log P + 2)^a/P`. -/
noncomputable def Phi (H : ℝ → ℝ) (a : ℕ) (P : ℝ) : ℝ := H P * (Real.log P + 2) ^ a / P

lemma Phi_nonneg (hP : PaperWidth H X0m ε θ) (a : ℕ) {p : ℝ} (hp : X0m / 2 ≤ p) (hp1 : 1 ≤ p) :
    0 ≤ Phi H a p := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p + 2 := by have := Real.log_nonneg hp1; linarith
  unfold Phi
  have := hP.reg.pos p
  positivity

/-- **The dyadic decay**: `Φ_a(2P) ≤ 0.51 Φ_a(P)` for `P ≥ X₀⁻/2`, `log P ≥ 10⁷`, `a ≤ 3`. -/
theorem Phi_two_le (hP : PaperWidth H X0m ε θ) {a : ℕ} (ha : a ≤ 3) {p : ℝ}
    (hp : X0m / 2 ≤ p) (hl : 10000000 ≤ Real.log p) : Phi H a (2 * p) ≤ 0.51 * Phi H a p := by
  have hX := hP.X0m_pos
  have hp0 : 0 < p := by linarith
  have hRH := hP.RH p 2 hp (by norm_num)
  rw [mul_comm] at hRH
  have h2 := KR.two_rpow_le hP.eps_nonneg hP.eps_le
  have hHp := hP.reg.pos p
  have hH2 : H (2 * p) ≤ 1.001 * H p := by nlinarith
  have hlog2 : Real.log (2 * p) = Real.log 2 + Real.log p := Real.log_mul (by norm_num) hp0.ne'
  have hl2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlg : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.log (2 * p) + 2 ≤ (Real.log p + 2) * 1.0000001 := by rw [hlog2]; nlinarith
  have hb0 : 0 ≤ Real.log (2 * p) + 2 := by rw [hlog2]; linarith
  have hpow : (Real.log (2 * p) + 2) ^ a ≤ (Real.log p + 2) ^ a * 1.0000001 ^ 3 := by
    calc (Real.log (2 * p) + 2) ^ a ≤ ((Real.log p + 2) * 1.0000001) ^ a :=
          pow_le_pow_left₀ hb0 hb a
      _ = (Real.log p + 2) ^ a * 1.0000001 ^ a := mul_pow _ _ _
      _ ≤ (Real.log p + 2) ^ a * 1.0000001 ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) ha
  unfold Phi
  rw [div_le_iff₀ (by positivity)]
  have hA : 0 ≤ (Real.log p + 2) ^ a := by positivity
  have hB : 0 ≤ (Real.log (2 * p) + 2) ^ a := by positivity
  calc H (2 * p) * (Real.log (2 * p) + 2) ^ a ≤
        (1.001 * H p) * ((Real.log p + 2) ^ a * 1.0000001 ^ 3) :=
        mul_le_mul hH2 hpow hB (by positivity)
    _ ≤ 0.51 * (H p * (Real.log p + 2) ^ a / p) * (2 * p) := by
        rw [show 0.51 * (H p * (Real.log p + 2) ^ a / p) * (2 * p) =
          1.02 * (H p * (Real.log p + 2) ^ a) by field_simp; ring]
        nlinarith [mul_nonneg hHp.le hA]

/-- `∑_{k<K} Φ_a(P_k) ≤ 2.05 Φ_a(P₀)`. -/
theorem decay_sum (hP : PaperWidth H X0m ε θ) (hXm : 100000000 ≤ Real.log X0m) {a : ℕ}
    (ha : a ≤ 3) (K : ℕ) : ∑ k ∈ range K, Phi H a (Pk X0m k) ≤ 2.05 * Phi H a (Pk X0m 0) := by
  have hX := hP.X0m_pos
  have hPk : ∀ k, X0m / 2 ≤ Pk X0m k := fun k => by
    unfold Pk; have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); nlinarith
  have hlk : ∀ k, 10000000 ≤ Real.log (Pk X0m k) := fun k => by
    have h1 : Real.log (X0m / 2) ≤ Real.log (Pk X0m k) :=
      Real.log_le_log (by positivity) (hPk k)
    have h2 : Real.log (X0m / 2) = Real.log X0m - Real.log 2 :=
      Real.log_div hX.ne' (by norm_num)
    have := Real.log_two_lt_d9
    linarith
  have hPk1 : ∀ k, 1 ≤ Pk X0m k := fun k => by
    have := hPk k
    have : (10 : ℝ) ≤ X0m := by
      by_contra hc; push_neg at hc
      have := Real.log_le_log hX hc.le
      have : Real.log 10 < 3 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10 by norm_num)
        linarith
      linarith
    linarith
  have hgeo : ∀ k, Phi H a (Pk X0m k) ≤ 0.51 ^ k * Phi H a (Pk X0m 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Pk_succ, pow_succ]
      have := Phi_two_le hP ha (hPk k) (hlk k)
      nlinarith [Phi_nonneg hP a (hPk 0) (hPk1 0)]
  have hP0 := Phi_nonneg hP a (hPk 0) (hPk1 0)
  calc ∑ k ∈ range K, Phi H a (Pk X0m k) ≤ ∑ k ∈ range K, 0.51 ^ k * Phi H a (Pk X0m 0) :=
        Finset.sum_le_sum fun k _ => hgeo k
    _ = (∑ k ∈ range K, (0.51 : ℝ) ^ k) * Phi H a (Pk X0m 0) := by rw [Finset.sum_mul]
    _ ≤ 2.05 * Phi H a (Pk X0m 0) := by
        apply mul_le_mul_of_nonneg_right _ hP0
        have hcl : ∀ n : ℕ, (∑ k ∈ range n, (0.51 : ℝ) ^ k) * (1 - 0.51) = 1 - 0.51 ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
        have := hcl K
        have : 0 ≤ (0.51 : ℝ) ^ K := by positivity
        nlinarith

end KR.TNP

end
