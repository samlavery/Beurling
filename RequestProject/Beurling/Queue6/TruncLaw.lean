module

public import RequestProject.Beurling.RankFull.MRFinal

/-!
# The position cut-off of (S3)(d): the truncated jitter law

Lemma A.6 (S3)(d) and Lemma A.3 bound the Euler product over the primes decided before a slot
`u ≤ s_max`, where `s_max ≤ 2z + H(2z)` is a *position* (§A, proof of Lemma A.3: every pivot
value is `≤ 2z + 1`, so every slot label is `≤ s_max`). The window model indexes the decisions
by the slot index; the position cut-off is the `F_n`-measurable condition
`c_n - H_n/2 ≤ b` (`b = 2z + 1`) on the box of the decision `n`. Removing the other decisions
does not change any window set `S(J)` with `J ⊆ (-∞, b]`, since a prime dividing an element of
`J` has value `≤ b` and lies in its box.

* `truncLaw J b` : the jitter law with `A'_n = A_n ∩ {c_n - H_n/2 ≤ b}` ((F1), (F2) inherited);
* `windowElems_trunc`, `windowVecs_trunc` : the window sets of `J ⊆ (-∞, b]` are unchanged;
* `card_dec_trunc_le` : the decided indices before `n` only decrease.
-/

@[expose] public section

open Set MeasureTheory Finset
open scoped ENNReal

namespace RankFull

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {θE : ℝ≥0∞}

/-- The position cut-off `{ω | c_n(ω) - H_n(ω)/2 ≤ b}`. -/
def cutSet (J : JitterLaw Ω P θE) (b : ℝ) (n : ℕ) : Set Ω := {ω | J.c n ω - J.H n ω / 2 ≤ b}

lemma cutSet_meas (J : JitterLaw Ω P θE) (b : ℝ) (n : ℕ) :
    MeasurableSet[J.F n] (cutSet J b n) := by
  have hf : Measurable[J.F n] (fun ω => J.c n ω - J.H n ω / 2) :=
    (J.c_meas n).sub ((J.H_meas n).div_const 2)
  exact hf measurableSet_Iic

/-- **The truncated jitter law**: the decisions `n` with `c_n - H_n/2 ≤ b` only. -/
noncomputable def truncLaw (J : JitterLaw Ω P θE) (b : ℝ) : JitterLaw Ω P θE where
  F := J.F
  F_mono := J.F_mono
  F_le := J.F_le
  A n := J.A n ∩ cutSet J b n
  q := J.q
  c := J.c
  H := J.H
  A_meas n := (J.A_meas n).inter (cutSet_meas J b n)
  q_meas := J.q_meas
  c_meas := J.c_meas
  H_meas := J.H_meas
  H_pos := J.H_pos
  dens n Φ hΦ := by
    classical
    set S := cutSet J b n with hSdef
    set Φ' : Ω × ℝ → ℝ≥0∞ := fun x => if x.1 ∈ S then Φ x else 0 with hΦ'def
    have hΦ' : JMeas (J.F n) Φ' := by
      unfold JMeas at hΦ ⊢
      have hS : @MeasurableSet (Ω × ℝ) (@Prod.instMeasurableSpace Ω ℝ (J.F n) _)
          {x : Ω × ℝ | x.1 ∈ S} :=
        @measurable_fst Ω ℝ (J.F n) _ S (cutSet_meas J b n)
      exact Measurable.ite (p := fun x : Ω × ℝ => x.1 ∈ S) hS hΦ measurable_const
    have h := J.dens n Φ' hΦ'
    have e1 : (J.A n ∩ S).indicator (fun ω => Φ (ω, J.q n ω)) =
        (J.A n).indicator (fun ω => Φ' (ω, J.q n ω)) := by
      funext ω
      by_cases hA : ω ∈ J.A n <;> by_cases hS : ω ∈ S <;>
        simp [Set.indicator, hA, hS, Φ']
    have e2 : (J.A n ∩ S).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
        ∫⁻ t in box (J.c n ω) (J.H n ω), Φ (ω, t)) =
        (J.A n).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
          ∫⁻ t in box (J.c n ω) (J.H n ω), Φ' (ω, t)) := by
      funext ω
      by_cases hA : ω ∈ J.A n <;> by_cases hS : ω ∈ S <;>
        simp [Set.indicator, hA, hS, Φ']
    show ∫⁻ ω, (J.A n ∩ S).indicator (fun ω => Φ (ω, J.q n ω)) ω ∂P ≤
      ∫⁻ ω, (J.A n ∩ S).indicator (fun ω => ENNReal.ofReal (J.H n ω)⁻¹ *
        ∫⁻ t in box (J.c n ω) (J.H n ω), Φ (ω, t)) ω ∂P
    rw [e1, e2]
    exact h
  slots ω t := by
    refine le_trans (ENNReal.tsum_le_tsum fun n => ?_) (J.slots ω t)
    exact Set.indicator_le_indicator_of_subset Set.inter_subset_left (fun _ => zero_le) ω

lemma truncLaw_A (J : JitterLaw Ω P θE) (b : ℝ) (n : ℕ) :
    (truncLaw J b).A n = J.A n ∩ cutSet J b n := rfl

lemma truncLaw_q (J : JitterLaw Ω P θE) (b : ℝ) : (truncLaw J b).q = J.q := rfl

namespace Config

variable {N : ℕ}

lemma decOf_trunc_subset (J : JitterLaw Ω P θE) (b : ℝ) (ω : Ω) :
    decOf (N := N) (truncLaw J b) ω ⊆ decOf (N := N) J ω := by
  intro n hn
  simp only [decOf, Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
  exact hn.1

lemma card_dec_trunc_le (J : JitterLaw Ω P θE) (b : ℝ) (ω : Ω) (n : Fin N) :
    ((decOf (N := N) (truncLaw J b) ω).filter (· < n)).card ≤
      ((decOf (N := N) J ω).filter (· < n)).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (decOf_trunc_subset J b ω))

/-- **The window elements are unchanged by the cut-off** for a window `J ⊆ (-∞, b]`, when the
decided values are `≥ 1` and lie above the left end of their box. -/
theorem windowElems_trunc (J : JitterLaw Ω P θE) (b : ℝ) (ω : Ω)
    (hq1 : ∀ n : Fin N, ω ∈ J.A n → 1 ≤ J.q n ω)
    (hbox : ∀ n : Fin N, ω ∈ J.A n → J.c n ω - J.H n ω / 2 ≤ J.q n ω)
    (X₀ D Dmax : ℕ) {Jw : Set ℝ} (hJw : Jw ⊆ Iic b) :
    windowElems (decOf (N := N) (truncLaw J b) ω) (qOf (truncLaw J b) ω) X₀ D Dmax Jw =
      windowElems (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw := by
  classical
  have hqq : qOf (N := N) (truncLaw J b) ω = qOf J ω := rfl
  rw [hqq]
  unfold windowElems
  refine Finset.filter_congr fun p hp => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun n hn => decOf_trunc_subset J b ω (h1 n hn), h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun n hn => ?_, h2, h3⟩
    have hnA : ω ∈ J.A n := by
      have := h1 n hn
      simpa [decOf] using this
    -- `q_n ≤ value ≤ b`
    have hd : 1 ≤ p.2 := by
      have := (Finset.mem_product.mp hp).2
      rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers] at this
      exact Nat.one_le_iff_ne_zero.mpr this.2.1
    have hq1' : ∀ m, p.1 m ≠ 0 → 1 ≤ qOf J ω m := fun m hm => by
      have hmA : ω ∈ J.A m := by
        have := h1 m hm
        simpa [decOf] using this
      exact hq1 m hmA
    have hqn : qOf J ω n ≤ ∏ m, qOf J ω m ^ p.1 m := by
      have hle : ∀ m ∈ (univ : Finset (Fin N)),
          (if m = n then qOf J ω n ^ p.1 n else 1) ≤ qOf J ω m ^ p.1 m := by
        intro m _
        by_cases hmn : m = n
        · subst hmn; simp
        · rw [if_neg hmn]
          by_cases h0 : p.1 m = 0
          · simp [h0]
          · exact one_le_pow₀ (hq1' m h0)
      have h := Finset.prod_le_prod₀ (s := univ)
        (fun m _ => by
          by_cases hmn : m = n
          · rw [if_pos hmn]; exact pow_nonneg (by linarith [hq1' n hn]) _
          · rw [if_neg hmn]; exact zero_le_one) hle
      rw [Finset.prod_ite_eq' univ n (fun m => qOf J ω n ^ p.1 n)] at h
      simp only [Finset.mem_univ, if_true] at h
      refine le_trans ?_ h
      have h1q := hq1' n hn
      calc qOf J ω n = qOf J ω n ^ 1 := (pow_one _).symm
        _ ≤ qOf J ω n ^ p.1 n := pow_le_pow_right₀ h1q (Nat.one_le_iff_ne_zero.mpr hn)
    have hval := hJw h3
    simp only [elemVal, Set.mem_Iic] at hval
    have hd' : (1 : ℝ) ≤ p.2 := by exact_mod_cast hd
    have hP0 : 0 ≤ ∏ m, qOf J ω m ^ p.1 m := le_trans (by linarith [hq1' n hn]) hqn
    have hqb : J.q n ω ≤ b := by
      have : ∏ m, qOf J ω m ^ p.1 m ≤ (p.2 : ℝ) * ∏ m, qOf J ω m ^ p.1 m := by nlinarith
      have : qOf J ω n ≤ b := by linarith
      exact this
    have hcut : ω ∈ cutSet J b n := by
      show J.c n ω - J.H n ω / 2 ≤ b
      linarith [hbox n hnA]
    simp only [decOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hnA, hcut⟩

/-- **The window sets are unchanged by the cut-off** for a window `J ⊆ (-∞, b]`. -/
theorem windowVecs_trunc (J : JitterLaw Ω P θE) (b : ℝ) (ω : Ω)
    (hq1 : ∀ n : Fin N, ω ∈ J.A n → 1 ≤ J.q n ω)
    (hbox : ∀ n : Fin N, ω ∈ J.A n → J.c n ω - J.H n ω / 2 ≤ J.q n ω)
    (X₀ D Dmax : ℕ) {Jw : Set ℝ} (hJw : Jw ⊆ Iic b) :
    windowVecs (decOf (N := N) (truncLaw J b) ω) (qOf (truncLaw J b) ω) X₀ D Dmax Jw =
      windowVecs (decOf (N := N) J ω) (qOf J ω) X₀ D Dmax Jw := by
  unfold windowVecs
  rw [windowElems_trunc J b ω hq1 hbox X₀ D Dmax hJw]

end Config

end RankFull

end
