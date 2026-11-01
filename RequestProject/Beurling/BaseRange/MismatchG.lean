module

public import RequestProject.Beurling.BaseRange.Mismatch
public import RequestProject.Beurling.BaseRange.Step3Gen

/-!
# The decision-order mismatch for a bounded function (proof of Lemma 7.3(d)(iii))

`kpt_sub_kvalG_le` : for `h` vanishing below `X₀` with `|h| ≤ A₀`, the decision-order operator
`K_pt h` and the value-order operator with the strict filter `P⁺(e) e < u` differ by at most
`56 A₀ η_H H_b` ("the decision-order count holds with `sup |g| ≤ 0.51/Λ`").
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

variable (P : BeurlingSystem)

/-- **Where the two strict filters differ**: some prime `p ∣ e`, `p ≥ X₀⁻/2`, has
`|p - u/e| ≤ H(p)`. -/
lemma mismatch_close_strict (tw : ℕ → ℝ) (H : ℝ → ℝ) {X0m X0 u : ℝ} (hXm : 0 < X0m)
    (hXmX : X0m ≤ X0)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j) {e : ℕ →₀ ℕ}
    (heu : X0 ≤ u / P.val e)
    (hne : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ ¬ (S3.maxV P e * P.val e < u)) :
    ∃ j ∈ e.support, X0m / 2 ≤ P.p j ∧ |P.p j - u / P.val e| ≤ H (P.p j) := by
  have hv := P.val_pos e
  have hu : 0 < u := by
    have : 0 < u / P.val e := by linarith
    exact (div_pos_iff_of_pos_right hv).mp this
  have hval : S3.maxV P e * P.val e < u ↔ ∀ j ∈ e.support, P.p j < u / P.val e := by
    rw [← lt_div_iff₀ hv]
    unfold S3.maxV
    rw [Finset.fold_max_lt]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by positivity, h⟩
  have hdec : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔
      ∀ j ∈ e.support, tw (qp j) < u / P.val e := by
    constructor
    · intro h j hj; rw [lt_div_iff₀ hv]; exact h j hj
    · intro h j hj; rw [← lt_div_iff₀ hv]; exact h j hj
  rw [hval, hdec] at hne
  set c := u / P.val e
  by_cases hd : ∀ j ∈ e.support, tw (qp j) < c
  · -- decision passes, value fails
    have := hne.mp hd
    push_neg at this
    obtain ⟨j, hj, hjc⟩ := this
    have htj := hd j hj
    by_cases hp : P.p j < X0m / 2
    · rw [hdlo j hp] at htj; linarith
    · push_neg at hp
      refine ⟨j, hj, hp, ?_⟩
      have := hdhi j hp
      rw [abs_le] at this ⊢
      constructor <;> linarith
  · -- value passes, decision fails
    have hvp : ∀ j ∈ e.support, P.p j < c := by
      by_contra h; exact hd (hne.mpr h)
    push_neg at hd
    obtain ⟨j, hj, hjc⟩ := hd
    have hpc := hvp j hj
    by_cases hp : P.p j < X0m / 2
    · rw [hdlo j hp] at hjc; linarith
    · push_neg at hp
      refine ⟨j, hj, hp, ?_⟩
      have := hdhi j hp
      rw [abs_le] at this ⊢
      constructor <;> linarith

/-- `K_pt h(u)` as a sum over the elements of value `≤ u/X₀`, for `h = 0` below `X₀`. -/
lemma kpt_h_eq (tw : ℕ → ℝ) {X0 : ℕ} {X0m u : ℝ} (hXm : 0 < X0m) (hXmX : X0m ≤ X0)
    (hu : 0 < u) (h : ℝ → ℝ) (hh0 : ∀ z : ℝ, z < X0 → h z = 0) :
    KR.Sharp.Kpt P tw X0m h u =
      ∑ e ∈ (P.elems (u / X0)).filter (· ≠ 0),
        (open scoped Classical in if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
          h (u / P.val e) / P.val e else 0) := by
  classical
  have hX0 : (0 : ℝ) < X0 := lt_of_lt_of_le hXm hXmX
  rw [kpt_eq]
  have hsub : (P.elems (u / X0)).filter (· ≠ 0) ⊆ (P.elems (u / X0m)).filter (· ≠ 0) := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨P.mem_elems.mpr ?_, h2⟩
    exact (P.mem_elems.mp h1).trans (div_le_div_of_nonneg_left hu.le hXm hXmX)
  symm
  apply Finset.sum_subset hsub
  intro e he0 he
  have hv := P.val_pos e
  have hlt : u / P.val e < X0 := by
    have : ¬ P.val e ≤ u / X0 := fun h' => he (Finset.mem_filter.mpr
      ⟨P.mem_elems.mpr h', (Finset.mem_filter.mp he0).2⟩)
    push_neg at this
    rw [div_lt_iff₀ hv]; rw [div_lt_iff₀ hX0] at this; linarith
  simp [hh0 _ hlt]

/-- **The decision-order mismatch for a bounded `h` vanishing below `X₀`**:
`|K_pt h(u) - K^val_pt h(u)| ≤ 56 A₀ η_H H_b` (strict filters). -/
theorem kpt_sub_kvalG_le (tw : ℕ → ℝ) (H : ℝ → ℝ) {X0 : ℕ} {X0m u ηH Hb A0 : ℝ}
    (hX0e : Real.exp 1 ≤ X0) (hXm : 0 < X0m) (hXmX : X0m ≤ X0) (hu : 0 < u)
    (h : ℝ → ℝ) (hh0 : ∀ z : ℝ, z < X0 → h z = 0) (hA0 : ∀ z, |h z| ≤ A0)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη : 0 ≤ ηH)
    (hHb : ∑ e ∈ P.elems (u / X0), 1 / P.val e ≤ Hb) :
    |KR.Sharp.Kpt P tw X0m h u -
        S3.KvalG P (u / X0) (fun t M => if M * t < u then h (u / t) / t else 0)| ≤
      56 * A0 * ηH * Hb := by
  classical
  set x := u / X0 with hx
  have hX1 : (1 : ℝ) < X0 := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX0e
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hA00 : 0 ≤ A0 := (abs_nonneg _).trans (hA0 0)
  set E := (P.elems x).filter (· ≠ 0)
  set cl : ℕ → (ℕ →₀ ℕ) → Prop := fun j e' => X0m / 2 ≤ P.p j ∧
    |P.p j - u / (P.p j * P.val e')| ≤ H (P.p j) ∧ P.p j * P.val e' ≤ u / X0
  rw [kpt_h_eq P tw hXm hXmX hu h hh0]
  unfold S3.KvalG
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- per element
  have hper : ∀ e ∈ E, |(if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
      h (u / P.val e) / P.val e else 0) -
        (fun t M => if M * t < u then h (u / t) / t else 0) (P.val e) (S3.maxV P e)| ≤
      A0 * ∑ j ∈ P.primesLe x, if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0 := by
    intro e he
    have h1 := P.mem_elems.mp (Finset.mem_filter.mp he).1
    have hv := P.val_pos e
    have hF1 : |h (u / P.val e) / P.val e| ≤ A0 * (1 / P.val e) := by
      rw [abs_div, abs_of_pos hv]
      calc |h (u / P.val e)| / P.val e ≤ A0 / P.val e :=
            div_le_div_of_nonneg_right (hA0 _) hv.le
        _ = A0 * (1 / P.val e) := by ring
    have hnn : 0 ≤ ∑ j ∈ P.primesLe x, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    have heu : (X0 : ℝ) ≤ u / P.val e := by
      rw [le_div_iff₀ hv]; rw [le_div_iff₀ hX0] at h1; linarith
    simp only
    rw [mul_comm (S3.maxV P e) (P.val e)]
    by_cases hiff : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ P.val e * S3.maxV P e < u
    · rw [if_congr hiff rfl rfl, sub_self, abs_zero]; positivity
    · have hne : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ ¬ (S3.maxV P e * P.val e < u) := by
        rw [mul_comm]; tauto
      obtain ⟨j, hj, hj2, hj3⟩ := mismatch_close_strict P tw H hXm hXmX hdhi hdlo heu hne
      have hjL : j ∈ P.primesLe x :=
        P.mem_primesLe.mpr ((S3.p_le_val P hj).trans h1)
      have hge : 1 / P.val e ≤ ∑ j ∈ P.primesLe x, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
          |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0) := by
        have := Finset.single_le_sum (f := fun j => if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
          |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0)
          (fun j _ => by (try simp only); split_ifs <;> positivity) hjL
        try simp only at this
        rwa [if_pos ⟨hj, hj2, hj3⟩] at this
      have hne' : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔
          ¬ (P.val e * S3.maxV P e < u) := by rw [mul_comm]; exact hne
      have habs : |(if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
          h (u / P.val e) / P.val e else 0) - (if P.val e * S3.maxV P e < u then
          h (u / P.val e) / P.val e else 0)| ≤ |h (u / P.val e) / P.val e| := by
        by_cases hd : ∀ j ∈ e.support, tw (qp j) * P.val e < u
        · rw [if_pos hd, if_neg (hne'.mp hd), sub_zero]
        · rw [if_neg hd, if_pos (by by_contra h'; exact hd (hne'.mpr h')), zero_sub, abs_neg]
      refine habs.trans (hF1.trans ?_)
      exact mul_le_mul_of_nonneg_left hge hA00
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- per prime: peel `j` off
  have hpj : ∀ j ∈ P.primesLe x, ∑ e ∈ E, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
      |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0) ≤
      ∑ e' ∈ P.elems x, 1 / P.val e' * (if cl j e' then 1 / P.p j else 0) := by
    intro j _
    rw [← Finset.sum_filter]
    set Fj := E.filter (fun e => j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
      |P.p j - u / P.val e| ≤ H (P.p j))
    set φ : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) := fun e => e - Finsupp.single j 1
    have hdec : ∀ e ∈ Fj, φ e + Finsupp.single j 1 = e := fun e he =>
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp he).2.1)))
    have hval : ∀ e ∈ Fj, P.val e = P.p j * P.val (φ e) := by
      intro e he
      conv_lhs => rw [← hdec e he]
      rw [P.val_add, P.val_single, pow_one, mul_comm]
    have hinj : Set.InjOn φ Fj := by
      intro e he e' he' h
      rw [← hdec e he, ← hdec e' he']
      rw [show φ e = φ e' from h]
    have hnn : ∀ e' ∈ P.elems x, 0 ≤ 1 / P.val e' * (if cl j e' then 1 / P.p j else 0) :=
      fun e' _ => by have := P.val_pos e'; have := P.p_pos j; split_ifs <;> positivity
    calc ∑ e ∈ Fj, 1 / P.val e = ∑ e ∈ Fj, 1 / P.val (φ e) * (if cl j (φ e) then 1 / P.p j
          else 0) := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨he1, -, hc2, hc3⟩ := Finset.mem_filter.mp he
          have h1 := P.mem_elems.mp (Finset.mem_filter.mp he1).1
          rw [if_pos ⟨hc2, by rw [← hval e he]; exact hc3, by rw [← hval e he]; exact h1⟩,
            hval e he]
          have := P.val_pos (φ e); have := P.p_pos j
          field_simp
      _ = ∑ e' ∈ Fj.image φ, 1 / P.val e' * (if cl j e' then 1 / P.p j else 0) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ e' ∈ P.elems x, 1 / P.val e' * (if cl j e' then 1 / P.p j else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun e' he' _ => hnn e' he')
          intro e' he'
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
          have h1 := P.mem_elems.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
          rw [hval e he] at h1
          have := P.val_pos (φ e)
          have : 1 ≤ P.p j := (P.one_lt j).le
          exact P.mem_elems.mpr (by nlinarith)
  have hinner : ∀ e' ∈ P.elems x, ∑ j ∈ P.primesLe x,
      1 / P.val e' * (if cl j e' then 1 / P.p j else 0) ≤ 1 / P.val e' * (56 * ηH) := by
    intro e' _
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    exact mul_le_mul_of_nonneg_left (close_sum_le P H hXm hXmX (P.val_pos e') hu hlip hsmall
      hcount hrat hη (P.primesLe x)) (by have := P.val_pos e'; positivity)
  have htot2 : ∑ e' ∈ P.elems x, 1 / P.val e' * (56 * ηH) ≤ Hb * (56 * ηH) := by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hHb (by positivity)
  calc A0 * ∑ j ∈ P.primesLe x, ∑ e ∈ E, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0)
      ≤ A0 * (Hb * (56 * ηH)) := by
        apply mul_le_mul_of_nonneg_left _ hA00
        refine (Finset.sum_le_sum hpj).trans ?_
        rw [Finset.sum_comm]
        exact (Finset.sum_le_sum hinner).trans htot2
    _ = 56 * A0 * ηH * Hb := by ring

end BaseRange
