module

public import RequestProject.Beurling.BaseRange.Step3Bound

/-!
# Step 3 of the proof of Lemma 7.3(b) for a general kernel

The bound of `Step3Bound` for an arbitrary summand `G(t, M)` with `|G(t, M)| ≤ A₀/t` on
`(0, x]`, given the one-replacement bound for the rigid-part kernel `Ψ = PsiD` as a hypothesis:

  `|K^G_P - K^G_Q| ≤ c e^S + A₀ D₀ Q e^S + 2 A₀ Q H`  (`kval_diffG`).

This is the form used for Lemma 7.3(d)(iii), "the telescoping of Step 3 of (b) applies with `f₀`
replaced by `g`".
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange.S3

/-- **The value-order operator** with summand `G(value, largest prime)` on `1 < e ≤ x`. -/
noncomputable def KvalG (S : BeurlingSystem) (x : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∑ e ∈ (S.elems x).filter (· ≠ 0), G (S.val e) (maxV S e)

/-- The kernel bound: `|Ψ(P', M)| ≤ A₀ D₀/P'`. -/
lemma abs_PsiDG_le (S : BeurlingSystem) (J1 : ℕ) (x : ℝ) (G : ℝ → ℝ → ℝ) {A0 D0 : ℝ}
    (hA0 : 0 ≤ A0) (hG : ∀ t M, 0 < t → t ≤ x → |G t M| ≤ A0 / t)
    (hD : ∑ d ∈ Drig S J1 x, 1 / S.val d ≤ D0) {P' M : ℝ} (hP : 0 < P') :
    |PsiD S J1 x G P' M| ≤ A0 * D0 / P' := by
  unfold PsiD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d ∈ Drig S J1 x, |if S.val d * P' ≤ x then G (S.val d * P') M else 0| ≤
      A0 / P' * (1 / S.val d) := by
    intro d _
    have hv := S.val_pos d
    split_ifs with h
    · refine (hG _ _ (mul_pos hv hP) h).trans (le_of_eq ?_)
      field_simp
    · simp; positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  calc A0 / P' * ∑ d ∈ Drig S J1 x, 1 / S.val d ≤ A0 / P' * D0 :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = A0 * D0 / P' := by ring

open Classical in
/-- The element sum of one system, with the squarefree large parts as tuples. -/
lemma kvalG_eq (S : BeurlingSystem) (J1 : ℕ) (x : ℝ) (G : ℝ → ℝ → ℝ) {X0m : ℝ}
    (hsmall : ∀ j < J1, S.p j < X0m) (hlarge : ∀ j, J1 ≤ j → X0m ≤ S.p j) {R : ℕ}
    (hR : (Lg S J1 x).card ≤ R) :
    KvalG S x G =
      ∑ d ∈ (Drig S J1 x).filter (· ≠ 0), G (S.val d) (maxV S d) +
      ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) *
        (Tele.tsumR S.p (Lg S J1 x) r (Tele.kern (PsiD S J1 x (G)) 1 0) -
          ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 x)).filter
            (fun f => ¬ Function.Injective f),
            Tele.kern (PsiD S J1 x (G)) 1 0 (S.p ∘ f)) +
      ∑ e ∈ (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e),
        G (S.val e) (maxV S e) := by
  unfold KvalG
  rw [decomp S J1 _ _ hsmall hlarge, sum_powerset_nonempty _ _ hR]
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  exact sum_powersetCard_eq_tuples S _ r _

open Classical in
/-- **The elements with a repeated large prime**: `|∑| ≤ A₀ Q H`. -/
lemma abs_NSG_le (S : BeurlingSystem) (J1 : ℕ) (x : ℝ) (G : ℝ → ℝ → ℝ) {A0 Q2 H : ℝ}
    (hA0 : 0 ≤ A0) (hG : ∀ t M, 0 < t → t ≤ x → |G t M| ≤ A0 / t)
    (hQ : ∑ j ∈ Lg S J1 x, 1 / S.p j ^ 2 ≤ Q2)
    (hH : ∑ e ∈ S.elems x, 1 / S.val e ≤ H) :
    |∑ e ∈ (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e),
        G (S.val e) (maxV S e)| ≤ A0 * (Q2 * H) := by
  classical
  set bad := (S.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e)
  have hH0 : 0 ≤ H := (Finset.sum_nonneg fun e _ => (one_div_pos.mpr (S.val_pos e)).le).trans hH
  have hp0 : ∀ j, 0 < S.p j := fun j => by linarith [S.one_lt j]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ e ∈ bad, |G (S.val e) (maxV S e)| ≤
      A0 * ∑ e ∈ bad, 1 / S.val e := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    refine (hG _ _ (S.val_pos e) (S.mem_elems.mp (Finset.mem_filter.mp he).1)).trans
      (le_of_eq ?_)
    ring
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
  exact mul_le_mul_of_nonneg_left h5 hA0

open Classical in
/-- **The tuples with a repeated prime**: `|∑_{f ¬inj} kern Ψ (p ∘ f)| ≤ A₀ D₀ C(r,2) Q S^{r-2}`. -/
lemma abs_NIG_le (S T : BeurlingSystem) (J1 : ℕ) (x : ℝ) (G : ℝ → ℝ → ℝ) {A0 D0 Q2 S1 : ℝ}
    (hA0 : 0 ≤ A0) (hG : ∀ t M, 0 < t → t ≤ x → |G t M| ≤ A0 / t)
    (hD : ∑ d ∈ Drig T J1 x, 1 / T.val d ≤ D0)
    (hQ : ∑ j ∈ Lg S J1 x, 1 / S.p j ^ 2 ≤ Q2)
    (hS : ∑ j ∈ Lg S J1 x, 1 / S.p j ≤ S1) (r : ℕ) :
    |∑ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 x)).filter
        (fun f => ¬ Function.Injective f),
        Tele.kern (PsiD T J1 x G) 1 0 (S.p ∘ f)| ≤
      A0 * D0 * ((r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2)) := by
  have hp0 : ∀ j, 0 < S.p j := fun j => by linarith [S.one_lt j]
  have hD0 : 0 ≤ D0 :=
    (Finset.sum_nonneg fun d _ => (one_div_pos.mpr (T.val_pos d)).le).trans hD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ f ∈ (Fintype.piFinset (fun _ : Fin r => Lg S J1 x)).filter
      (fun f => ¬ Function.Injective f),
      |Tele.kern (PsiD T J1 x G) 1 0 (S.p ∘ f)| ≤
        A0 * D0 * ∏ k, (1 / S.p (f k)) := by
    intro f _
    unfold Tele.kern
    have hpos : 0 < 1 * ∏ i, (S.p ∘ f) i := by
      rw [one_mul]; exact Finset.prod_pos fun i _ => hp0 _
    refine (abs_PsiDG_le T J1 x G hA0 hG hD hpos).trans (le_of_eq ?_)
    rw [one_mul, Finset.prod_div_distrib, Finset.prod_const_one]
    simp only [Function.comp]
    field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Tele.nonInj_le S.p (Lg S J1 x) (fun j _ => hp0 j) r).trans ?_
  have hS0 : 0 ≤ ∑ j ∈ Lg S J1 x, 1 / S.p j :=
    Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hp0 j)).le
  have hQ0 : 0 ≤ ∑ j ∈ Lg S J1 x, 1 / S.p j ^ 2 :=
    Finset.sum_nonneg fun j _ => (one_div_pos.mpr (pow_pos (hp0 j) 2)).le
  have := pow_le_pow_left₀ hS0 hS (r - 2)
  have hc : (0 : ℝ) ≤ r.choose 2 := by positivity
  calc (r.choose 2 : ℝ) * (∑ j ∈ Lg S J1 x, 1 / S.p j ^ 2) *
        (∑ j ∈ Lg S J1 x, 1 / S.p j) ^ (r - 2)
      ≤ (r.choose 2 : ℝ) * Q2 * (∑ j ∈ Lg S J1 x, 1 / S.p j) ^ (r - 2) := by
        gcongr
    _ ≤ (r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2) := by
        gcongr
        exact mul_nonneg hc (hQ0.trans hQ)

/-- **Step 3 for a general kernel**: two systems with the same small primes. -/
theorem kval_diffG {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j)
    (x : ℝ) (G : ℝ → ℝ → ℝ) {X0m A0 c D0 S1 Q2 H : ℝ} (hA0 : 0 ≤ A0) (hc : 0 ≤ c)
    (hG : ∀ t M, 0 < t → t ≤ x → |G t M| ≤ A0 / t)
    (hsP : ∀ j < J1, P.p j < X0m) (hlP : ∀ j, J1 ≤ j → X0m ≤ P.p j)
    (hsQ : ∀ j < J1, Q.p j < X0m) (hlQ : ∀ j, J1 ≤ j → X0m ≤ Q.p j)
    (hone : ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      |∑ j ∈ Lg P J1 x, PsiD P J1 x G (a * P.p j) (max b (P.p j)) -
        ∑ j ∈ Lg Q J1 x, PsiD P J1 x G (a * Q.p j) (max b (Q.p j))| ≤ c / a)
    (hD : ∑ d ∈ Drig P J1 x, 1 / P.val d ≤ D0)
    (hSP : ∑ j ∈ Lg P J1 x, 1 / P.p j ≤ S1) (hSQ : ∑ j ∈ Lg Q J1 x, 1 / Q.p j ≤ S1)
    (hQP : ∑ j ∈ Lg P J1 x, 1 / P.p j ^ 2 ≤ Q2)
    (hQQ : ∑ j ∈ Lg Q J1 x, 1 / Q.p j ^ 2 ≤ Q2)
    (hHP : ∑ e ∈ P.elems x, 1 / P.val e ≤ H)
    (hHQ : ∑ e ∈ Q.elems x, 1 / Q.val e ≤ H) :
    |KvalG P x G - KvalG Q x G| ≤
      c * Real.exp S1 + A0 * D0 * Q2 * Real.exp S1 + 2 * (A0 * (Q2 * H)) := by
  classical
  set R := (Lg P J1 x).card + (Lg Q J1 x).card
  set Ψ := PsiD P J1 x G with hΨ
  have hp0 : ∀ (S : BeurlingSystem) j, 0 < S.p j := fun S j => by linarith [S.one_lt j]
  have hD0 : 0 ≤ D0 :=
    (Finset.sum_nonneg fun d _ => (one_div_pos.mpr (P.val_pos d)).le).trans hD
  have hS0 : 0 ≤ S1 :=
    (Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hp0 P j)).le).trans hSP
  have hQ0 : 0 ≤ Q2 :=
    (Finset.sum_nonneg fun j _ => (one_div_pos.mpr (pow_pos (hp0 P j) 2)).le).trans hQP
  have eP := kvalG_eq P J1 x G hsP hlP (R := R) (Nat.le_add_right _ _)
  have eQ := kvalG_eq Q J1 x G hsQ hlQ (R := R) (Nat.le_add_left _ _)
  rw [← PsiD_eq hpq] at eQ
  have hrig : ∑ d ∈ (Drig P J1 x).filter (· ≠ 0), G (P.val d) (maxV P d) =
      ∑ d ∈ (Drig Q J1 x).filter (· ≠ 0), G (Q.val d) (maxV Q d) := by
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
  set MP := ∑ e ∈ (P.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e), G (P.val e) (maxV P e)
  set MQ := ∑ e ∈ (Q.elems x).filter (fun e => e ≠ 0 ∧ ¬ SqfL J1 e), G (Q.val e) (maxV Q e)
  -- the telescoping
  have hT : |∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - TQ r)| ≤ c * Real.exp S1 := by
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
  have hN : ∀ (N : ℕ → ℝ), (∀ r, |N r| ≤ A0 * D0 * ((r.choose 2 : ℝ) * Q2 * S1 ^ (r - 2))) →
      |∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * N r| ≤ A0 * D0 * Q2 * (Real.exp S1 / 2) := by
    intro N hNr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ Icc 1 R, |(1 / (r.factorial : ℝ)) * N r|
        ≤ ∑ r ∈ Icc 1 R, A0 * D0 * Q2 *
            ((1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S1 ^ (r - 2))) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [abs_mul, abs_of_pos (by positivity)]
          calc 1 / (r.factorial : ℝ) * |N r| ≤
                1 / (r.factorial : ℝ) * (A0 * D0 * ((r.choose 2 : ℝ) * Q2 *
                  S1 ^ (r - 2))) := mul_le_mul_of_nonneg_left (hNr r) (by positivity)
            _ = _ := by ring
      _ = A0 * D0 * Q2 *
            ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * ((r.choose 2 : ℝ) * S1 ^ (r - 2)) := by
          rw [Finset.mul_sum]
      _ ≤ A0 * D0 * Q2 * (Real.exp S1 / 2) :=
          mul_le_mul_of_nonneg_left (sum_nonInj_exp hS0 R) (by positivity)
  have hNP := hN NP (fun r => abs_NIG_le P P J1 x G hA0 hG hD hQP hSP r)
  have hNQ := hN NQ (fun r => abs_NIG_le Q P J1 x G hA0 hG hD hQQ hSQ r)
  have hMP := abs_NSG_le P J1 x G hA0 hG hQP hHP
  have hMQ := abs_NSG_le Q J1 x G hA0 hG hQQ hHQ
  have e : (∑ d ∈ (Drig P J1 x).filter (· ≠ 0), G (P.val d) (maxV P d) +
        ∑ r ∈ Icc 1 R, (1 / (r.factorial : ℝ)) * (TP r - NP r) + MP) -
      (∑ d ∈ (Drig P J1 x).filter (· ≠ 0), G (P.val d) (maxV P d) +
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
