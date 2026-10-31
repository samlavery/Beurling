module

public import RequestProject.Beurling.Queue6.Path
public import RequestProject.Beurling.Queue6.Adapted6

/-!
# The failure probabilities of Table 1 (Lemma 6.1, Theorem 6.6(i), Lemma 6.10)

* `Queue6.R1cond_ae` : on `Good(< max I)`, a.s., Corollary 5.40 (middle inequality) gives the
  drift bound in the form used by Theorem 6.6 (`ℓ_jit ≤ 1.01|I ∩ [X₀, ∞)| + 1`,
  `log max I ≤ 1.0001 L`);
* `Queue6.frE_fail` : **Theorem 6.6(i)** for one window of `𝓘_u`:
  `P(Fr(I)ᶜ ∩ Good(<b)) ≤ (K₀ + 7) e^{-4L}`;
* `Queue6.landE_fail` : **Lemma 6.1**: `P(Land(J)ᶜ) ≤ 2 e^{-λ_P}`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction BModel CaplLink QueueBound QueueMono
  Greedy QueueDet SlotModel

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-- The numerical step from the middle inequality of Corollary 5.40 to the form used in
Theorem 6.6. -/
lemma r1_numeric {ℓ len Lb Lq S : ℝ} (hlen : 0 ≤ len) (hℓ : ℓ ≤ 1.01 * len + 1)
    (hLq : 10 ^ 8 ≤ Lq) (hLb0 : 0 < Lb) (hLb : Lb ≤ 1.0001 * Lq)
    (h : 0.399 * len / Lb - 2 ≤ ℓ - S) : S ≤ ℓ * (1 - 0.15 / Lq) + 3 := by
  have hLq0 : 0 < Lq := by linarith
  have h1 : 0.1515 * len / Lq ≤ 0.399 * len / Lb := by
    rw [div_le_div_iff₀ hLq0 hLb0]; nlinarith
  have h2 : 0.15 * ℓ / Lq ≤ 0.1515 * len / Lq + 1 := by
    rw [div_add_one hLq0.ne', div_le_div_iff₀ hLq0 hLq0]
    nlinarith
  have e : ℓ * (1 - 0.15 / Lq) = ℓ - 0.15 * ℓ / Lq := by field_simp
  rw [e]; linarith

/-- Almost every `ω` has jitters in `[0, 1]` and no ties. -/
lemma ae_std (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) :
    ∀ᵐ ω ∂jitterMeasure, ∃ h : Std θ X₀ ω, TieFree (constructedModel θ X₀ ω) ω := by
  have h0 : jitterMeasure (tiesEvent θ X₀) = 0 := hnull θ hθ X₀ hev hX₀
  have h1 : ∀ᵐ ω ∂jitterMeasure, ω ∉ tiesEvent θ X₀ := measure_eq_zero_iff_ae_notMem.mp h0
  filter_upwards [ae_jitter_mem, h1] with ω hU ht
  have h : Std θ X₀ ω := ⟨hθ, hX, hU, hHB⟩
  refine ⟨h, ?_⟩
  by_contra hc; exact ht ⟨h, hc⟩

/-- **R1′ on `Good(< max I)` in the form of Theorem 6.6**, a.s., from Corollary 5.40. -/
theorem R1cond_ae (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueCore θ X₀) {m : ℕ} {a b : ℤ}
    (hadm : Adm X₀ m a b) :
    ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ Q.sec5 (tE2 b) → R1cond θ X₀ m a b ω := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  filter_upwards [Q.R1 m a b hadm, ae_std hθ hX hHB hnull hev hX₀] with ω hR ⟨h, ht⟩ hG n
  have hR := hR hG n
  have F : ExcFacts θ (CM θ X₀ ω) (Ucl ω) := by
    have hUe : Ucl ω = ω := Ucl_eq h.hU
    have hCM : CM θ X₀ ω = h.limModel := by
      show constructedModel θ X₀ (Ucl ω) = _; rw [hUe]; exact constructedModel_eq h
    rw [hCM, hUe]; rw [constructedModel_eq h] at ht; exact excFacts_of h hev ht
  obtain ⟨hub, hb3, hab, hW⟩ := hadm
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbX : (X₀ : ℝ) ≤ b := hu.trans hub
  have hℓ := ellI_le F hab' hbX
  have hlen : 0 ≤ (b : ℝ) - max (a : ℝ) X₀ := by have := max_le hab' hbX; linarith
  obtain ⟨hL1, hL2, hL3⟩ := Lq_bounds hX0 hX hu
  have hl := (logs_of_ge hX0 hX hu).1
  have hLb0 : 0 < Real.log b := Real.log_pos (by linarith)
  have hLb : Real.log b ≤ 1.0001 * Lq (uS X₀ m) := by
    have := Real.log_le_log (by linarith) hb3
    linarith
  exact r1_numeric hlen hℓ (Lq_big hX0 hX hu) hLb0 hLb hR

/-- **Theorem 6.6(i) for one window of `𝓘_u`.** -/
theorem frE_fail (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (hnull : TiesNull) (hev : Even X₀)
    (hX₀ : Real.exp (10 ^ 8) ≤ X₀) (Q : QueueCore θ X₀) (m : ℕ) (a b : ℤ) :
    jitterMeasure ((FrE θ X₀ m a b)ᶜ ∩ G0 θ X₀ Q.sec5 (tE2 b)) ≤
      ENNReal.ofReal ((K0 X₀ (uS X₀ m) + 7) * Real.exp (-(4 * Lq (uS X₀ m)))) := by
  classical
  unfold FrE
  split_ifs with hadm
  · have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := one_lt_of_logX hX0 hX
    have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
    have hM := Mq_ge_one hX0 hX hu
    have hL := Lq_big hX0 hX hu
    have h := frAll_fail (μ := jitterMeasure) (ℱ := jitterFiltration)
      (Xt := Xt θ X₀ m a b) (Ind2 := Ind2 θ X₀ a b) (L := Lq (uS X₀ m))
      (l := 4 * Lq (uS X₀ m))
      (by linarith : 0 < Mq X₀ (uS X₀ m)) (by linarith) (by linarith)
      (fun k ω => le_min (Nat.cast_nonneg _) (by linarith)) (fun k ω => min_le_right _ _)
      (fun k => Xt_adapted ⟨hθ, hX, hHB⟩ m a b k)
      (fun k ω => by unfold Ind2; split_ifs <;> norm_num)
      (fun k ω => by unfold Ind2; split_ifs <;> norm_num)
      (fun k => Ind2_adapted ⟨hθ, hX, hHB⟩ a b k) (ellIo θ X₀ a b) (K0 X₀ (uS X₀ m) + 5)
      (G0 θ X₀ Q.sec5 (tE2 b)) (R1cond_ae hθ hX hHB hnull hev hX₀ Q hadm)
      (Q.comp2 m a b hadm)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    push_cast; nlinarith [Real.exp_pos (-(4 * Lq (uS X₀ m)))]
  · simp

/-- `μ̄(J) > 0`. -/
lemma muBar_pos (hX : 10 ^ 8 ≤ Real.log X₀) {m i j : ℕ} (hij : i < j) : 0 < muBar X₀ m i j := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  have hJ : (0 : ℝ) < ((j : ℝ) - i) / 2 := by
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  have hH8 : 0 < capH X₀ (8 * uS X₀ m) := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  have hH2 : 0 < capH X₀ (uS X₀ m / 2) := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  unfold muBar
  exact mul_pos (by linarith) (lt_min one_pos (div_pos hJ hH2))

/-- **Lemma 6.1 (landing count)**: `P(Land(J)ᶜ) ≤ 2 e^{-λ_P}`, with no conditioning. -/
theorem landE_fail (hθ : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hHB : ShortIntervalPNTFrom X₀) (Q : QueueCore θ X₀) (m i j : ℕ) :
    jitterMeasure (LandE θ X₀ m i j)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-(4 * Real.log (uS X₀ m)))) := by
  classical
  unfold LandE
  split_ifs with hJ
  · have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := one_lt_of_logX hX0 hX
    have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
    have hl := (logs_of_ge hX0 hX hu).1
    have h := Freedman.landing_count (μ := jitterMeasure) (ℱ := jitterFiltration)
      (landInd θ X₀ m i j) (fun k ω => by unfold landInd; split_ifs <;> simp)
      (fun k => landInd_adapted ⟨hθ, hX, hHB⟩ m i j k) (muBar_pos hX hJ.1)
      (by linarith : 0 < 4 * Real.log (uS X₀ m))
      (Q.land m i j hJ)
    have hsub : {ω | ∀ n, |∑ k ∈ Finset.range n, (landInd θ X₀ m i j k ω -
        (jitterMeasure[landInd θ X₀ m i j k | jitterFiltration k]) ω)| <
          Real.sqrt (2 * muBar X₀ m i j * (4 * Real.log (uS X₀ m))) +
            2 * (4 * Real.log (uS X₀ m)) / 3}ᶜ ⊆
        {ω | ∃ n, Real.sqrt (2 * muBar X₀ m i j * (4 * Real.log (uS X₀ m))) +
          2 * (4 * Real.log (uS X₀ m)) / 3 ≤ |∑ k ∈ Finset.range n, (landInd θ X₀ m i j k ω -
            (jitterMeasure[landInd θ X₀ m i j k | jitterFiltration k]) ω)|} := by
      intro ω hω
      simp only [mem_compl_iff, mem_setOf_eq, not_forall, not_lt] at hω
      exact hω
    calc jitterMeasure _ ≤ jitterMeasure _ := measure_mono hsub
      _ = ENNReal.ofReal (jitterMeasure.real _) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  · simp

end Queue6

end
