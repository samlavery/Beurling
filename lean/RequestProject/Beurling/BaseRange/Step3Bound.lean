module

public import RequestProject.Beurling.BaseRange.Step3Core

/-!
# Step 3 of the proof of Lemma 7.3(b): the bound for two systems

`kval_diff_le`: for two Beurling systems with the same small primes,

  `|Kval_P(u) - Kval_Q(u)| ≤ (12 B log² x D₀/Λ) e^S + (D₀/Λ) Q e^S + 2 Q H/Λ`

(`x = u/X₀`, `Λ = log X₀`), the three terms being the symmetric telescoping over the tuples of
large primes, the tuples with a repeated prime, and the elements with a repeated large prime.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange.S3

/-! ### The exponential sums -/

lemma sum_tele_exp {S : ℝ} (hS : 0 ≤ S) (R : ℕ) :
    ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (r * S ^ (r - 1)) ≤ Real.exp S := by
  have hg : ∀ r : ℕ, 0 ≤ (1 / (r.factorial : ℝ)) * (r * S ^ (r - 1)) := fun r => by positivity
  calc ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (r * S ^ (r - 1))
      ≤ ∑ r ∈ range (R + 1), (1 / (r.factorial : ℝ)) * (r * S ^ (r - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
        · intro r _ _; exact hg r
    _ = ∑ i ∈ range R, S ^ i / (i.factorial : ℝ) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.factorial_succ, Nat.add_sub_cancel]
        push_cast
        have : (i.factorial : ℝ) ≠ 0 := by positivity
        field_simp
    _ ≤ Real.exp S := Real.sum_le_exp_of_nonneg hS R

lemma sum_nonInj_exp {S : ℝ} (hS : 0 ≤ S) (R : ℕ) :
    ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S ^ (r - 2)) ≤
      Real.exp S / 2 := by
  have hg : ∀ r : ℕ, 0 ≤ (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S ^ (r - 2)) :=
    fun r => by positivity
  calc ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S ^ (r - 2))
      ≤ ∑ r ∈ range (R + 2), (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S ^ (r - 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
        · intro r _ _; exact hg r
    _ = (∑ i ∈ range R, S ^ i / (i.factorial : ℝ)) / 2 := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_div]
        have e1 : (1 / ((0 + 1).factorial : ℝ)) * (((0 + 1).choose 2 : ℕ) * S ^ (0 + 1 - 2)) = 0 :=
          by simp
        have e0 : (1 / ((0 : ℕ).factorial : ℝ)) * (((0 : ℕ).choose 2 : ℕ) * S ^ (0 - 2)) = 0 :=
          by simp
        rw [e1, e0, add_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.cast_choose_two, Nat.factorial_succ, Nat.factorial_succ,
          show i + 1 + 1 - 2 = i by omega]
        push_cast
        have : (i.factorial : ℝ) ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ Real.exp S / 2 := by
        have := Real.sum_le_exp_of_nonneg hS R; linarith

/-! ### One system -/

open Classical in
/-- The element sum of one system, with the squarefree large parts as tuples. -/
lemma kval_eq (S : BeurlingSystem) (J1 : ℕ) {X0 κ u X0m : ℝ}
    (hsmall : ∀ j < J1, S.p j < X0m) (hlarge : ∀ j, J1 ≤ j → X0m ≤ S.p j) {R : ℕ}
    (hR : (Lg S J1 (u / X0)).card ≤ R) :
    Kval S X0 κ u =
      ∑ d ∈ (Drig S J1 (u / X0)).filter (· ≠ 0), Gu κ u (S.val d) (maxV S d) +
      ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) *
        (Tele.tsumR S.p (Lg S J1 (u / X0)) r (Tele.kern (PsiD S J1 (u / X0) (Gu κ u)) 1 0) -
          ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 (u / X0))).filter
            (fun f => ¬ Function.Injective f),
            Tele.kern (PsiD S J1 (u / X0) (Gu κ u)) 1 0 (S.p ∘ f)) +
      ∑ e ∈ (S.elems (u / X0)).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e),
        Gu κ u (S.val e) (maxV S e) := by
  unfold Kval
  rw [decomp S J1 _ _ hsmall hlarge, sum_powerset_nonempty _ _ hR]
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  exact sum_powersetCard_eq_tuples S _ r _

/-- `|G(t, M)| ≤ 1/(Λ t)` on `0 < t ≤ x`. -/
lemma abs_Gu_le {X0 κ u t M : ℝ} (hX0 : Real.exp 1 ≤ X0) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (ht : 0 < t) (htx : t ≤ u / X0) : |Gu κ u t M| ≤ 1 / Real.log X0 * (1 / t) := by
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  unfold Gu
  split_ifs
  · obtain ⟨h0, h1⟩ := Fu_bounds hX0 hκ hκ1 ht htx
    rw [abs_of_nonneg h0]
    refine h1.trans (le_of_eq ?_)
    field_simp
  · simp; positivity

open Classical in
/-- **The elements with a repeated large prime**: `|∑| ≤ Q H/Λ`. -/
lemma abs_NS_le (S : BeurlingSystem) (J1 : ℕ) {X0 κ u Q2 H : ℝ} (hX0 : Real.exp 1 ≤ X0)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hQ : ∑ j ∈ Lg S J1 (u / X0), 1 / S.p j ^ 2 ≤ Q2)
    (hH : ∑ e ∈ S.elems (u / X0), 1 / S.val e ≤ H) :
    |∑ e ∈ (S.elems (u / X0)).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e),
        Gu κ u (S.val e) (maxV S e)| ≤ Q2 * H / Real.log X0 := by
  classical
  set x := u / X0
  set bad := (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e)
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  have hH0 : 0 ≤ H := (Finset.sum_nonneg fun e _ => (one_div_pos.mpr (S.val_pos e)).le).trans hH
  have hp0 : ∀ j, 0 < S.p j := fun j => by linarith [S.one_lt j]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ e ∈ bad, |Gu κ u (S.val e) (maxV S e)| ≤
      1 / Real.log X0 * ∑ e ∈ bad, 1 / S.val e := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    exact abs_Gu_le hX0 hκ hκ1 (S.val_pos e)
      (S.mem_elems.mp (Finset.mem_filter.mp he).1)
  refine h1.trans ?_
  -- each bad element has a large prime with exponent `≥ 2`
  have h2 : ∑ e ∈ bad, 1 / S.val e ≤
      ∑ e ∈ bad, ∑ j ∈ Lg S J1 x, if 2 ≤ e j then 1 / S.val e else 0 := by
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨he1, -, he3⟩ := Finset.mem_filter.mp he
    unfold SqfL at he3
    push_neg at he3
    obtain ⟨j, hj1, hj2⟩ := he3
    have hjL : j ∈ Lg S J1 x := by
      refine Finset.mem_filter.mpr ⟨S.mem_primesLe.mpr ?_, hj1⟩
      have := p_le_val S (Finsupp.mem_support_iff.mpr (by omega : e j ≠ 0))
      exact this.trans (S.mem_elems.mp he1)
    have hnn : ∀ i ∈ Lg S J1 x, 0 ≤ (if 2 ≤ e i then 1 / S.val e else 0) := fun i _ => by
      split_ifs
      · exact (one_div_pos.mpr (S.val_pos e)).le
      · exact le_rfl
    calc 1 / S.val e = if 2 ≤ e j then 1 / S.val e else 0 := by rw [if_pos (by omega)]
      _ ≤ _ := Finset.single_le_sum hnn hjL
  rw [Finset.sum_comm] at h2
  have h3 : ∀ j ∈ Lg S J1 x, ∑ e ∈ bad, (if 2 ≤ e j then 1 / S.val e else 0) ≤
      1 / S.p j ^ 2 * H := by
    intro j _
    rw [← Finset.sum_filter]
    set F := bad.filter (fun e => 2 ≤ e j)
    set φ : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) := fun e => e - Finsupp.single j 2
    have hdec : ∀ e ∈ F, φ e + Finsupp.single j 2 = e := fun e he =>
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Finset.mem_filter.mp he).2)
    have hval : ∀ e ∈ F, S.val e = S.val (φ e) * S.p j ^ 2 := by
      intro e he
      conv_lhs => rw [← hdec e he]
      rw [S.val_add, S.val_single]
    have hinj : Set.InjOn φ F := by
      intro e he e' he' h
      rw [← hdec e he, ← hdec e' he']
      rw [h]
    calc ∑ e ∈ F, 1 / S.val e = ∑ e ∈ F, 1 / S.p j ^ 2 * (1 / S.val (φ e)) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [hval e he]
          have := S.val_pos (φ e); have := hp0 j
          field_simp
      _ = 1 / S.p j ^ 2 * ∑ e' ∈ F.image φ, 1 / S.val e' := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
      _ ≤ 1 / S.p j ^ 2 * ∑ e' ∈ S.elems x, 1 / S.val e' := by
          apply mul_le_mul_of_nonneg_left _ (by have := hp0 j; positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e' he'
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
            have h1 := S.mem_elems.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
            rw [hval e he] at h1
            have : 1 ≤ S.p j ^ 2 := one_le_pow₀ (S.one_lt j).le
            have := S.val_pos (φ e)
            exact S.mem_elems.mpr (by nlinarith)
          · intro e' _ _; exact (one_div_pos.mpr (S.val_pos e')).le
      _ ≤ 1 / S.p j ^ 2 * H := mul_le_mul_of_nonneg_left hH (by have := hp0 j; positivity)
  have h4 := h2.trans (Finset.sum_le_sum h3)
  rw [← Finset.sum_mul] at h4
  have h5 : ∑ e ∈ bad, 1 / S.val e ≤ Q2 * H := h4.trans (mul_le_mul_of_nonneg_right hQ hH0)
  calc 1 / Real.log X0 * ∑ e ∈ bad, 1 / S.val e ≤ 1 / Real.log X0 * (Q2 * H) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = Q2 * H / Real.log X0 := by ring

open Classical in
/-- **The tuples with a repeated prime**:
`|∑_{f ¬inj} kern Ψ (p ∘ f)| ≤ (D₀/Λ) C(r,2) Q S^{r-2}`. -/
lemma abs_NI_le (S T : BeurlingSystem) (J1 : ℕ) {X0 κ u D0 Q2 S1 : ℝ}
    (hX0 : Real.exp 1 ≤ X0) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hD : ∑ d ∈ Drig T J1 (u / X0), 1 / T.val d ≤ D0)
    (hQ : ∑ j ∈ Lg S J1 (u / X0), 1 / S.p j ^ 2 ≤ Q2)
    (hS : ∑ j ∈ Lg S J1 (u / X0), 1 / S.p j ≤ S1) (r : ℕ) :
    |∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 (u / X0))).filter
        (fun f => ¬ Function.Injective f),
        Tele.kern (PsiD T J1 (u / X0) (Gu κ u)) 1 0 (S.p ∘ f)| ≤
      D0 / Real.log X0 * ((r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2)) := by
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  have hp0 : ∀ j, 0 < S.p j := fun j => by linarith [S.one_lt j]
  have hD0 : 0 ≤ D0 :=
    (Finset.sum_nonneg fun d _ => (one_div_pos.mpr (T.val_pos d)).le).trans hD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 (u / X0))).filter
      (fun f => ¬ Function.Injective f),
      |Tele.kern (PsiD T J1 (u / X0) (Gu κ u)) 1 0 (S.p ∘ f)| ≤
        D0 / Real.log X0 * ∏ k, (1 / S.p (f k)) := by
    intro f _
    unfold Tele.kern
    have hpos : 0 < 1 * ∏ i, (S.p ∘ f) i := by
      rw [one_mul]; exact Finset.prod_pos fun i _ => hp0 _
    refine (abs_PsiD_le T J1 hX0 hκ hκ1 hD hpos).trans (le_of_eq ?_)
    rw [one_mul, Finset.prod_div_distrib, Finset.prod_const_one]
    simp only [Function.comp]
    field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Tele.nonInj_le S.p (Lg S J1 (u / X0)) (fun j _ => hp0 j) r).trans ?_
  have hS0 : 0 ≤ ∑ j ∈ Lg S J1 (u / X0), 1 / S.p j :=
    Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hp0 j)).le
  have hQ0 : 0 ≤ ∑ j ∈ Lg S J1 (u / X0), 1 / S.p j ^ 2 :=
    Finset.sum_nonneg fun j _ => (one_div_pos.mpr (pow_pos (hp0 j) 2)).le
  have := pow_le_pow_left₀ hS0 hS (r - 2)
  have hc : (0 : ℝ) ≤ r.choose 2 := by positivity
  calc (r.choose 2 : ℝ) * (∑ j ∈ Lg S J1 (u / X0), 1 / S.p j ^ 2) *
        (∑ j ∈ Lg S J1 (u / X0), 1 / S.p j) ^ (r - 2)
      ≤ (r.choose 2 : ℝ) * Q2 * (∑ j ∈ Lg S J1 (u / X0), 1 / S.p j) ^ (r - 2) := by
        gcongr
    _ ≤ (r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2) := by
        gcongr
        exact mul_nonneg hc (hQ0.trans hQ)

/-! ### Two systems -/

open Classical in
/-- **Step 3 of the proof of Lemma 7.3(b)**: two systems with the same small primes. -/
theorem kval_diff_le {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j)
    {X0 κ u X0m B D0 S1 Q2 H : ℝ} (hX0 : Real.exp 1 ≤ X0) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hu : 0 < u) (hXm : Real.exp 1 ≤ X0m / 2) (hB : 0 ≤ B)
    (hsP : ∀ j < J1, P.p j < X0m) (hlP : ∀ j, J1 ≤ j → X0m ≤ P.p j)
    (hsQ : ∀ j < J1, Q.p j < X0m) (hlQ : ∀ j, J1 ≤ j → X0m ≤ Q.p j)
    (hΔ : ∀ s ∈ Set.Icc (X0m / 2) (u / X0),
      |thetaF P.p (Lg P J1 (u / X0)) s - thetaF Q.p (Lg Q J1 (u / X0)) s| ≤
        B * s * (Real.log s + 1) ^ 2)
    (hD : ∑ d ∈ Drig P J1 (u / X0), 1 / P.val d ≤ D0)
    (hSP : ∑ j ∈ Lg P J1 (u / X0), 1 / P.p j ≤ S1) (hSQ : ∑ j ∈ Lg Q J1 (u / X0), 1 / Q.p j ≤ S1)
    (hQP : ∑ j ∈ Lg P J1 (u / X0), 1 / P.p j ^ 2 ≤ Q2)
    (hQQ : ∑ j ∈ Lg Q J1 (u / X0), 1 / Q.p j ^ 2 ≤ Q2)
    (hHP : ∑ e ∈ P.elems (u / X0), 1 / P.val e ≤ H)
    (hHQ : ∑ e ∈ Q.elems (u / X0), 1 / Q.val e ≤ H) :
    |Kval P X0 κ u - Kval Q X0 κ u| ≤
      12 * B * Real.log (u / X0) ^ 2 * D0 / Real.log X0 * Real.exp S1 +
        D0 / Real.log X0 * Q2 * Real.exp S1 + 2 * (Q2 * H / Real.log X0) := by
  set x := u / X0 with hx
  set R := (Lg P J1 x).card + (Lg Q J1 x).card
  set Ψ := PsiD P J1 x (Gu κ u) with hΨ
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  have hp0 : ∀ (S : BeurlingSystem) j, 0 < S.p j := fun S j => by linarith [S.one_lt j]
  have hD0 : 0 ≤ D0 :=
    (Finset.sum_nonneg fun d _ => (one_div_pos.mpr (P.val_pos d)).le).trans hD
  have hS0 : 0 ≤ S1 :=
    (Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hp0 P j)).le).trans hSP
  have hQ0 : 0 ≤ Q2 :=
    (Finset.sum_nonneg fun j _ => (one_div_pos.mpr (pow_pos (hp0 P j) 2)).le).trans hQP
  have eP := kval_eq P J1 (X0 := X0) (u := u) (κ := κ) hsP hlP (R := R) (Nat.le_add_right _ _)
  have eQ := kval_eq Q J1 (X0 := X0) (u := u) (κ := κ) hsQ hlQ (R := R) (Nat.le_add_left _ _)
  rw [← PsiD_eq hpq] at eQ
  have hrig : ∑ d ∈ (Drig P J1 x).filter (· ≠ 0), Gu κ u (P.val d) (maxV P d) =
      ∑ d ∈ (Drig Q J1 x).filter (· ≠ 0), Gu κ u (Q.val d) (maxV Q d) := by
    rw [← Drig_eq hpq x]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
    rw [val_eq_of_small hpq hd', maxV_eq_of_small hpq hd']
  rw [eP, eQ, ← hrig]
  set TP : ℕ → ℝ := fun r => Tele.tsumR P.p (Lg P J1 x) r (Tele.kern Ψ 1 0)
  set TQ : ℕ → ℝ := fun r => Tele.tsumR Q.p (Lg Q J1 x) r (Tele.kern Ψ 1 0)
  set NP : ℕ → ℝ := fun r => ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg P J1 x)).filter
    (fun f => ¬ Function.Injective f), Tele.kern Ψ 1 0 (P.p ∘ f)
  set NQ : ℕ → ℝ := fun r => ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg Q J1 x)).filter
    (fun f => ¬ Function.Injective f), Tele.kern Ψ 1 0 (Q.p ∘ f)
  set MP := ∑ e ∈ (P.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e), Gu κ u (P.val e) (maxV P e)
  set MQ := ∑ e ∈ (Q.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e), Gu κ u (Q.val e) (maxV Q e)
  set c := 12 * B * Real.log x ^ 2 * D0 / Real.log X0
  have hc : 0 ≤ c := by positivity
  -- the telescoping
  have hT : |∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r)| ≤ c * Real.exp S1 := by
    have hone := hone_PsiD (κ := κ) (D0 := D0) hX0 hκ hκ1 hu hXm hB
      (fun j hj => hlP j (Finset.mem_filter.mp hj).2)
      (fun j hj => hlQ j (Finset.mem_filter.mp hj).2) hΔ hD
    have htele := Tele.tele P.p Q.p (Lg P J1 x) (Lg Q J1 x) (fun j _ => hp0 P j)
      (fun j _ => hp0 Q j) Ψ hc hS0 hone hSP hSQ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ Icc 1 R, |(1 / (r.factorial : ℝ)) * (TP r - TQ r)|
        ≤ ∑ r ∈ Icc 1 R, c * ((1 / (r.factorial : ℝ)) * (r * S1 ^ (r - 1))) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul, abs_of_pos (by positivity)]
          have := htele r 1 one_pos 0
          rw [div_one] at this
          calc 1 / (r.factorial : ℝ) * |TP r - TQ r| ≤
                1 / (r.factorial : ℝ) * (c * r * S1 ^ (r - 1)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      _ = c * ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (r * S1 ^ (r - 1)) := by
          rw [Finset.mul_sum]
      _ ≤ c * Real.exp S1 := mul_le_mul_of_nonneg_left (sum_tele_exp hS0 R) hc
  -- the repeated tuples
  have hN : ∀ (S : BeurlingSystem) (N : ℕ → ℝ), (∀ r, |N r| ≤
      D0 / Real.log X0 * ((r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2))) →
      |∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * N r| ≤
        D0 / Real.log X0 * Q2 * (Real.exp S1 / 2) := by
    intro _ N hNr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ Icc 1 R, |(1 / (r.factorial : ℝ)) * N r|
        ≤ ∑ r ∈ Icc 1 R, D0 / Real.log X0 * Q2 *
            ((1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S1 ^ (r - 2))) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul, abs_of_pos (by positivity)]
          calc 1 / (r.factorial : ℝ) * |N r| ≤
                1 / (r.factorial : ℝ) * (D0 / Real.log X0 * ((r.choose 2 : ℝ) * Q2 *
                  S1 ^ (r - 2))) := mul_le_mul_of_nonneg_left (hNr r) (by positivity)
            _ = _ := by ring
      _ = D0 / Real.log X0 * Q2 *
            ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S1 ^ (r - 2)) := by
          rw [Finset.mul_sum]
      _ ≤ D0 / Real.log X0 * Q2 * (Real.exp S1 / 2) :=
          mul_le_mul_of_nonneg_left (sum_nonInj_exp hS0 R) (by positivity)
  have hNP := hN P NP (fun r => abs_NI_le P P J1 hX0 hκ hκ1 hD hQP hSP r)
  have hNQ := hN Q NQ (fun r => abs_NI_le Q P J1 hX0 hκ hκ1 hD hQQ hSQ r)
  have hMP := abs_NS_le P J1 (κ := κ) hX0 hκ hκ1 hQP hHP
  have hMQ := abs_NS_le Q J1 (κ := κ) hX0 hκ hκ1 hQQ hHQ
  have e : (∑ d ∈ (Drig P J1 x).filter (· ≠ 0), Gu κ u (P.val d) (maxV P d) +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - NP r) + MP) -
      (∑ d ∈ (Drig P J1 x).filter (· ≠ 0), Gu κ u (P.val d) (maxV P d) +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TQ r - NQ r) + MQ) =
      ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r) -
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NP r +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NQ r + MP - MQ := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [e]
  have := abs_sub (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r) -
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NP r +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NQ r + MP) MQ
  have := abs_add_le (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r) -
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NP r +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NQ r) MP
  have := abs_add_le (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r) -
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NP r)
        (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NQ r)
  have := abs_sub (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r))
        (∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * NP r)
  linarith

end BaseRange.S3
