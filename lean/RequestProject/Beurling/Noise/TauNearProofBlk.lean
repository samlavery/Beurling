module

public import RequestProject.Beurling.Noise.TauNearProofSum

/-!
# Lemma 5.20: the scale blocks

For a scale `v`, `SmB_k(v)` is the set of `3P_k`-smooth elements of `(v/(4P_k²), 2v/P_k²]`, and

  `blk K Ψ v = ∑_{k<K} 56 H(P_k) Ψ_k/P_k ∑_{m ∈ SmB_k(v)} 1/m`.

* `blk_ge` : `∑_{w τ-near at y} ψ(y/w)/w ≤ blk K Ψ v` for `y ∈ [v, 2v)`;
* `scale_sum` : for `2`-separated scales, `∑_v L(v) ∑_{m ∈ SmB_k(v)} 1/m ≤ 3 ∑_{m ∈ U_k} L̄(m)/m`
  with `L(v) ≤ L̄(m)` whenever `m ∈ SmB_k(v)`;
* `U_harm`, `U_logharm` : the Euler bounds on `U_k = ⋃_v SmB_k(v)`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- The `3P_k`-smooth elements of `(v/(4P_k²), 2v/P_k²]`. -/
noncomputable def SmB (P : BeurlingSystem) (X0m : ℝ) (k : ℕ) (v : ℝ) : Finset (ℕ →₀ ℕ) :=
  open scoped Classical in
  (P.elems (2 * v / Pk X0m k ^ 2)).filter (fun e => v / (4 * Pk X0m k ^ 2) < P.val e ∧
    ∀ i ∈ e.support, P.p i ≤ 3 * Pk X0m k)

/-- The scale block `∑_{k<K} 56 H(P_k) Ψ_k/P_k ∑_{m ∈ SmB_k(v)} 1/m`. -/
noncomputable def blk (P : BeurlingSystem) (H : ℝ → ℝ) (X0m : ℝ) (K : ℕ) (Ψ : ℕ → ℝ)
    (v : ℝ) : ℝ :=
  ∑ k ∈ range K, 56 * H (Pk X0m k) * Ψ k / Pk X0m k * ∑ e ∈ SmB P X0m k v, 1 / P.val e

lemma Sm_subset_SmB (hX : 0 < X0m) {k : ℕ} {v y : ℝ} (hvy : v ≤ y) (hy : y < 2 * v) :
    Sm P X0m k y ⊆ SmB P X0m k v := by
  intro e he
  simp only [Sm, SmB, Finset.mem_filter, mem_elems] at he ⊢
  have hk := Pk_pos hX k
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨h1.trans (div_le_div_of_nonneg_right (by linarith) (by positivity)), ?_, h3⟩
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hvy (by positivity)) h2

lemma blk_nonneg (hP : PaperWidth H X0m ε θ) (K : ℕ) {Ψ : ℕ → ℝ} (hΨ0 : ∀ k, 0 ≤ Ψ k)
    (v : ℝ) : 0 ≤ blk P H X0m K Ψ v := by
  have hX := hP.X0m_pos
  unfold blk
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (Finset.sum_nonneg fun e _ =>
    (one_div_pos.mpr (P.val_pos e)).le)
  have := hP.reg.pos (Pk X0m k); have := hΨ0 k; have := Pk_pos hX k
  positivity

/-- **The block bound on `[v, 2v)`.** -/
theorem blk_ge (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {ψ : ℝ → ℝ} {Ψ : ℕ → ℝ} {v y : ℝ}
    {K : ℕ} (hv : 0 < v) (hvy : v ≤ y) (hy : y < 2 * v) (hK : √(2 * v) ≤ Pk X0m K)
    (hΨ0 : ∀ k, 0 ≤ Ψ k)
    (hψ : ∀ k < K, ∀ c, 0.85 * Pk X0m k ≤ c → c ≤ 2.42 * Pk X0m k → ψ c ≤ Ψ k) :
    etaG P H tw X0m ψ y ≤ blk P H X0m K Ψ v := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hy0 : 0 < y := by linarith
  have hK' : √y < Pk X0m K := lt_of_lt_of_le (Real.sqrt_lt_sqrt hy0.le hy) hK
  refine (etaG_le_blocks h hy0 hK' hΨ0 hψ).trans ?_
  unfold blk
  refine Finset.sum_le_sum fun k _ => ?_
  have hc0 : 0 ≤ 56 * H (Pk X0m k) * Ψ k / Pk X0m k := by
    have := hP.reg.pos (Pk X0m k); have := hΨ0 k; have := Pk_pos hX k
    positivity
  apply mul_le_mul_of_nonneg_left _ hc0
  exact Finset.sum_le_sum_of_subset_of_nonneg (Sm_subset_SmB hX hvy hy)
    fun e _ _ => (one_div_pos.mpr (P.val_pos e)).le

/-- **Regrouping over `2`-separated scales**: each `m` lies in `SmB_k(v)` for at most three
scales `v`, all with `L(v) ≤ L̄(m)`. -/
theorem scale_sum (hX : 0 < X0m) {Sc : Finset ℝ} (hS : Sep Sc) (k : ℕ) {L Lb : ℝ → ℝ}
    (hL0 : ∀ v ∈ Sc, 0 ≤ L v)
    (hLb : ∀ v ∈ Sc, ∀ e ∈ SmB P X0m k v, L v ≤ Lb (P.val e)) :
    ∑ v ∈ Sc, L v * ∑ e ∈ SmB P X0m k v, 1 / P.val e ≤
      3 * ∑ e ∈ Sc.biUnion (SmB P X0m k), Lb (P.val e) / P.val e := by
  classical
  rw [sum_scales_swap, Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have hk := Pk_pos hX k
  have hve := P.val_pos e
  set a := P.val e * Pk X0m k ^ 2 / 2
  have ha : 0 < a := by positivity
  have hsub : Sc.filter (fun v => e ∈ SmB P X0m k v) ⊆
      Sc.filter (fun v => a ≤ v ∧ v < 8 * a) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    simp only [SmB, Finset.mem_filter, mem_elems] at hv2
    refine Finset.mem_filter.mpr ⟨hv1, ?_, ?_⟩
    · have := hv2.1
      rw [le_div_iff₀ (by positivity)] at this
      simp only [a]; linarith
    · have := hv2.2.1
      rw [div_lt_iff₀ (by positivity)] at this
      simp only [a]; linarith
  have hcard := (Finset.card_le_card hsub).trans (card_window_le_three hS ha)
  obtain ⟨v0, hv0, he0⟩ := Finset.mem_biUnion.mp he
  have hLb0 : 0 ≤ Lb (P.val e) := (hL0 v0 hv0).trans (hLb v0 hv0 e he0)
  calc 1 / P.val e * ∑ v ∈ Sc.filter (fun v => e ∈ SmB P X0m k v), L v
      ≤ 1 / P.val e * ∑ v ∈ Sc.filter (fun v => e ∈ SmB P X0m k v), Lb (P.val e) := by
        apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hve).le
        exact Finset.sum_le_sum fun v hv =>
          hLb v (Finset.mem_filter.mp hv).1 e (Finset.mem_filter.mp hv).2
    _ = 1 / P.val e * ((Sc.filter (fun v => e ∈ SmB P X0m k v)).card * Lb (P.val e)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / P.val e * (3 * Lb (P.val e)) := by
        apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hve).le
        apply mul_le_mul_of_nonneg_right _ hLb0
        exact_mod_cast hcard
    _ = 3 * (Lb (P.val e) / P.val e) := by ring

/-- The union `U_k` is `3P_k`-smooth, and if it is non-empty then `9P_k² ≤ Z` (from
`18 v ≤ Z`). -/
lemma U_smooth (hX : 0 < X0m) {Sc : Finset ℝ} (k : ℕ) :
    ∀ e ∈ Sc.biUnion (SmB P X0m k), ∀ i ∈ e.support, P.p i ≤ 3 * Pk X0m k := by
  intro e he i hi
  obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.mp he
  simp only [SmB, Finset.mem_filter] at hv
  exact hv.2.2 i hi

lemma U_horizon (hX : 0 < X0m) {Sc : Finset ℝ} (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) (k : ℕ)
    (hne : (Sc.biUnion (SmB P X0m k)).Nonempty) : (3 * Pk X0m k) ^ 2 ≤ Z := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv, hev⟩ := Finset.mem_biUnion.mp he
  simp only [SmB, Finset.mem_filter, mem_elems] at hev
  have hk := Pk_pos hX k
  have h1 := (P.one_le_val e).trans hev.1
  rw [le_div_iff₀ (by positivity)] at h1
  have := hZ v hv
  nlinarith

/-- `∑_{m ∈ U_k} 1/m ≤ 1810 log(3P_k)`. -/
theorem U_harm (h : P.HBS X0m Z η1 η2 ε1) (hP : PaperWidth H X0m ε θ) {Sc : Finset ℝ}
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) (k : ℕ) (hk1 : 1 ≤ Pk X0m k) :
    ∑ e ∈ Sc.biUnion (SmB P X0m k), 1 / P.val e ≤ 1810 * Real.log (3 * Pk X0m k) := by
  have hX := hP.X0m_pos
  rcases (Sc.biUnion (SmB P X0m k)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
  · exact smooth_harm_le h (by linarith) (U_horizon hX hZ k hne) _ (U_smooth hX k)

/-- `∑_{m ∈ U_k} log m/m ≤ 3620 log(3P_k)(log(3P_k) + 0.43)`. -/
theorem U_logharm (h : P.HBS X0m Z η1 η2 ε1) (hP : PaperWidth H X0m ε θ) {Sc : Finset ℝ}
    (hZ : ∀ v ∈ Sc, 18 * v ≤ Z) (k : ℕ) (hk1 : 1 ≤ Pk X0m k) :
    ∑ e ∈ Sc.biUnion (SmB P X0m k), Real.log (P.val e) / P.val e ≤
      3620 * Real.log (3 * Pk X0m k) * (Real.log (3 * Pk X0m k) + 0.43) := by
  have hX := hP.X0m_pos
  rcases (Sc.biUnion (SmB P X0m k)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * Pk X0m k by linarith); positivity
  · exact smooth_logharm_le h (by linarith) (U_horizon hX hZ k hne) _ (U_smooth hX k)

end KR.TNP

end
