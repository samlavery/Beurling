module

public import RequestProject.Beurling.BaseRange.Step3Decomp

/-!
# Step 3 of the proof of Lemma 7.3(b): two systems compared

Two Beurling systems `P`, `Q` with the same small primes (`p_j = q_j` for `j < J₁`, all `< X₀⁻`)
and large primes `≥ X₀⁻` (`j ≥ J₁`). For the value-order sharp operator on `f₀` (`Kval`),

  `Kval_S(u) = ∑_{e ∈ S, 1 < e ≤ u/X₀, P⁺(e) e ≤ u} f₀(u/e)/e`,

this file proves the bound of Step 3 (`kval_diff_le`):

  `|Kval_P(u) - Kval_Q(u)| ≤ (12 B log² x D₀/Λ) e^S + (D₀/Λ) Q e^S + (Q/Λ)(H_P + H_Q)`,

with `x = u/X₀`, `Λ = log X₀`, `D₀ = ∑_{d rigid} 1/d`, `S`, `Q` bounds for `∑ 1/p`, `∑ 1/p²` over
the large primes `≤ x` of either system, `H_S = ∑_{e ≤ x} 1/e`, given
`|θ_P - θ_Q| ≤ B s (log s + 1)²` for the large primes on `[X₀⁻/2, x]`. The three terms are:
the symmetric telescoping over the `r`-tuples of large primes (`Tele.tele`, `one_replacement`),
the tuples with a repeated prime (`Tele.nonInj_le`), and the elements with a repeated large
prime.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange.S3

/-- `F(t) = f₀(u/t)/t`. -/
noncomputable def Fu (κ u t : ℝ) : ℝ := f0s κ (u / t) / t

/-- The summand of the value-order sharp operator. -/
noncomputable def Gu (κ u : ℝ) (t M : ℝ) : ℝ := if M * t ≤ u then Fu κ u t else 0

/-- **The value-order sharp operator** on `f₀` for a system `S`. -/
noncomputable def Kval (S : BeurlingSystem) (X0 κ u : ℝ) : ℝ :=
  ∑ e ∈ (S.elems (u / X0)).filter (· ≠ 0), Gu κ u (S.val e) (maxV S e)

lemma Fu_bounds {X0 κ u t : ℝ} (hX0 : Real.exp 1 ≤ X0) (hκ : 0 < κ) (_hκ1 : κ ≤ 1)
    (ht : 0 < t) (htx : t ≤ u / X0) :
    0 ≤ Fu κ u t ∧ Fu κ u t ≤ 1 / (Real.log X0 * t) := by
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hq : X0 ≤ u / t := by
    rw [le_div_iff₀ ht]; rw [le_div_iff₀ hX00] at htx; linarith
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  obtain ⟨h0, h1, -⟩ := f0s_bounds hκ (hX0.trans hq)
  have hlq : Real.log X0 ≤ Real.log (u / t) := Real.log_le_log hX00 hq
  unfold Fu
  refine ⟨div_nonneg h0 ht.le, ?_⟩
  rw [div_le_iff₀ ht]
  have : f0s κ (u / t) ≤ 1 / Real.log X0 := h1.trans (one_div_le_one_div_of_le (by linarith) hlq)
  calc f0s κ (u / t) ≤ 1 / Real.log X0 := this
    _ = 1 / (Real.log X0 * t) * t := by field_simp

/-! ### The common rigid part -/

lemma val_eq_of_small {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j)
    {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < J1) : P.val d = Q.val d := by
  unfold BeurlingSystem.val
  exact Finsupp.prod_congr fun j hj => by rw [hpq j (hd j hj)]

lemma maxV_eq_of_small {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j)
    {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < J1) : maxV P d = maxV Q d := by
  unfold maxV
  exact Finset.fold_congr fun j hj => hpq j (hd j hj)

lemma Drig_eq {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j) (x : ℝ) :
    Drig P J1 x = Drig Q J1 x := by
  ext d
  simp only [Drig, Finset.mem_filter, P.mem_elems, Q.mem_elems]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [← val_eq_of_small hpq h2], h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rwa [val_eq_of_small hpq h2], h2⟩

lemma PsiD_eq {P Q : BeurlingSystem} {J1 : ℕ} (hpq : ∀ j < J1, P.p j = Q.p j) (x : ℝ)
    (G : ℝ → ℝ → ℝ) : PsiD P J1 x G = PsiD Q J1 x G := by
  funext a b
  unfold PsiD
  rw [Drig_eq hpq x]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [val_eq_of_small hpq (Finset.mem_filter.mp hd).2]

/-! ### The powerset by cardinality -/

lemma sum_powerset_nonempty {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : Finset ι → ℝ) {R : ℕ}
    (hR : s.card ≤ R) :
    ∑ T ∈ s.powerset.filter (·.Nonempty), g T = ∑ r ∈ Icc 1 R, ∑ T ∈ s.powersetCard r, g T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s.powerset.filter (·.Nonempty)) (t := Icc 1 R)
    (g := Finset.card) ?_]
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hr1 := (Finset.mem_Icc.mp hr).1
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, Finset.card_pos.mp (by omega)⟩, h2⟩
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hT.2, (Finset.card_le_card hT.1).trans hR⟩

/-! ### One system: tuples -/

open Classical in
/-- The sum over the squarefree large parts with `r` primes, as `1/r!` times the tuple sum minus
the tuples with a repeated coordinate. -/
lemma sum_powersetCard_eq_tuples (S : BeurlingSystem) (L : Finset ℕ) (r : ℕ)
    (Ψ : ℝ → ℝ → ℝ) :
    ∑ T ∈ L.powersetCard r, Ψ (∏ j ∈ T, S.p j) (T.fold max 0 S.p) =
      (1 / (r.factorial : ℝ)) * (Tele.tsumR S.p L r (Tele.kern Ψ 1 0) -
        ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => L)).filter (fun f => ¬ Function.Injective f),
          Tele.kern Ψ 1 0 (S.p ∘ f)) := by
  have hinj := Tele.sum_inj_eq L r (fun T => Ψ (∏ j ∈ T, S.p j) (T.fold max 0 S.p))
  have hk : ∀ f ∈ (Fintype.piFinset (fun _ : Fin r => L)).filter Function.Injective,
      Tele.kern Ψ 1 0 (S.p ∘ f) = Ψ (∏ j ∈ Finset.univ.image f, S.p j)
        ((Finset.univ.image f).fold max 0 S.p) := by
    intro f hf
    rw [Tele.kern_eq_image S.p Ψ 1 0 (Finset.mem_filter.mp hf).2, one_mul]
  unfold Tele.tsumR
  rw [← Finset.sum_filter_add_sum_filter_not (Fintype.piFinset (fun _ : Fin r => L))
    Function.Injective, add_sub_cancel_right, Finset.sum_congr rfl hk, hinj]
  have : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The kernel bound: `|Ψ(P', M)| ≤ D₀/(Λ P')`. -/
lemma abs_PsiD_le (S : BeurlingSystem) (J1 : ℕ) {X0 κ u : ℝ} (hX0 : Real.exp 1 ≤ X0)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {D0 : ℝ} (hD : ∑ d ∈ Drig S J1 (u / X0), 1 / S.val d ≤ D0)
    {P' M : ℝ} (hP : 0 < P') :
    |PsiD S J1 (u / X0) (Gu κ u) P' M| ≤ D0 / (Real.log X0 * P') := by
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  unfold PsiD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d ∈ Drig S J1 (u / X0), |if S.val d * P' ≤ u / X0 then
      Gu κ u (S.val d * P') M else 0| ≤ 1 / (Real.log X0 * P') * (1 / S.val d) := by
    intro d _
    have hv := S.val_pos d
    split_ifs with h
    · unfold Gu
      split_ifs
      · obtain ⟨h0, h1⟩ := Fu_bounds hX0 hκ hκ1 (mul_pos hv hP) h
        rw [abs_of_nonneg h0]
        refine h1.trans (le_of_eq ?_)
        field_simp
      · simp; positivity
    · simp; positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  calc 1 / (Real.log X0 * P') * ∑ d ∈ Drig S J1 (u / X0), 1 / S.val d ≤
        1 / (Real.log X0 * P') * D0 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = D0 / (Real.log X0 * P') := by ring

/-- The cut `max(b, t) m t ≤ u` is an interval `t ≤ β₁` in `t > 0`. -/
lemma cut_iff {b m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 < t) :
    max b t * (m * t) ≤ u ↔
      t ≤ (if (max b 0) ^ 2 * m ≤ u then Real.sqrt (u / m) else u / (max b 0 * m)) := by
  set b' := max b 0 with hb'
  have hb'0 : 0 ≤ b' := le_max_right _ _
  have hmax : max b t = max b' t := by
    rcases le_total b 0 with h | h
    · rw [hb', max_eq_right h, max_eq_right (h.trans ht.le), max_eq_right ht.le]
    · rw [hb', max_eq_left h]
  rw [hmax]
  have hsq : ∀ y : ℝ, 0 ≤ y → (y ≤ Real.sqrt (u / m) ↔ m * y ^ 2 ≤ u) := by
    intro y hy
    rw [Real.le_sqrt hy (by positivity), le_div_iff₀ hm]; constructor <;> intro h <;> linarith
  split_ifs with hc
  · rw [hsq t ht.le]
    rcases le_total t b' with htb | htb
    · rw [max_eq_left htb]
      constructor
      · intro _; nlinarith
      · intro _; nlinarith
    · rw [max_eq_right htb]; constructor <;> intro h <;> nlinarith
  · push_neg at hc
    have hb0 : 0 < b' := by
      by_contra h; push_neg at h
      have : b' = 0 := le_antisymm h hb'0
      rw [this] at hc; simp at hc; linarith
    rw [le_div_iff₀ (by positivity)]
    rcases le_total t b' with htb | htb
    · rw [max_eq_left htb]; constructor <;> intro h <;> nlinarith
    · rw [max_eq_right htb]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith

/-- The cut of one replacement as a single threshold `β'`. -/
lemma term_eq {κ u x m b p : ℝ} (hm : 0 < m) (hu : 0 < u) (hp : 0 < p) (hpx : p ≤ x) :
    (if m * p ≤ x then (if max b p * (m * p) ≤ u then Fu κ u (m * p) else 0) else 0) =
      if p ≤ min (min (x / m) (if (max b 0) ^ 2 * m ≤ u then Real.sqrt (u / m) else
        u / (max b 0 * m))) x then Fu κ u (m * p) else 0 := by
  have hcut := cut_iff (b := b) hm hu hp
  have hxm : m * p ≤ x ↔ p ≤ x / m := by rw [le_div_iff₀ hm]; constructor <;> intro h <;> linarith
  by_cases h1 : m * p ≤ x
  · rw [if_pos h1]
    by_cases h2 : max b p * (m * p) ≤ u
    · rw [if_pos h2, if_pos (le_min (le_min (hxm.mp h1) (hcut.mp h2)) hpx)]
    · rw [if_neg h2, if_neg]
      intro h; exact h2 (hcut.mpr (h.trans ((min_le_left _ _).trans (min_le_right _ _))))
  · rw [if_neg h1, if_neg]
    intro h; exact h1 (hxm.mpr (h.trans ((min_le_left _ _).trans (min_le_left _ _))))

/-- **One replacement for the kernel `Ψ`** (the hypothesis of `Tele.tele`). -/
theorem hone_PsiD {P Q : BeurlingSystem} {J1 : ℕ}
    {X0 κ u X0m B D0 : ℝ} (hX0 : Real.exp 1 ≤ X0) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hu : 0 < u)
    (hXm : Real.exp 1 ≤ X0m / 2) (hB : 0 ≤ B)
    (hlP : ∀ j ∈ Lg P J1 (u / X0), X0m ≤ P.p j) (hlQ : ∀ j ∈ Lg Q J1 (u / X0), X0m ≤ Q.p j)
    (hΔ : ∀ s ∈ Set.Icc (X0m / 2) (u / X0),
      |thetaF P.p (Lg P J1 (u / X0)) s - thetaF Q.p (Lg Q J1 (u / X0)) s| ≤
        B * s * (Real.log s + 1) ^ 2)
    (hD : ∑ d ∈ Drig P J1 (u / X0), 1 / P.val d ≤ D0) :
    ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      |∑ j ∈ Lg P J1 (u / X0), PsiD P J1 (u / X0) (Gu κ u) (a * P.p j) (max b (P.p j)) -
        ∑ j ∈ Lg Q J1 (u / X0), PsiD P J1 (u / X0) (Gu κ u) (a * Q.p j) (max b (Q.p j))| ≤
      12 * B * Real.log (u / X0) ^ 2 * D0 / Real.log X0 / a := by
  classical
  intro a ha b
  set x := u / X0 with hx
  have hX00 : 0 < X0 := lt_of_lt_of_le (Real.exp_pos 1) hX0
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX00]; exact hX0
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set βf : ℝ → ℝ := fun m => min (min (x / m) (if (max b 0) ^ 2 * m ≤ u then Real.sqrt (u / m)
    else u / (max b 0 * m))) x with hβf
  have hLp : ∀ (S : BeurlingSystem) (j : ℕ), j ∈ Lg S J1 x → 0 < S.p j ∧ S.p j ≤ x := by
    intro S j hj
    exact ⟨by linarith [S.one_lt j], S.mem_primesLe.mp (Finset.mem_filter.mp hj).1⟩
  -- per rigid part `d`
  have hper : ∀ (S : BeurlingSystem), ∀ d ∈ Drig P J1 x,
      ∑ j ∈ Lg S J1 x, (if P.val d * (a * S.p j) ≤ x then
        Gu κ u (P.val d * (a * S.p j)) (max b (S.p j)) else 0) =
      ∑ j ∈ (Lg S J1 x).filter (fun j => S.p j ≤ βf (P.val d * a)),
        f0s κ (u / ((P.val d * a) * S.p j)) / ((P.val d * a) * S.p j) := by
    intro S d _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hp, hpx⟩ := hLp S j hj
    have hm : 0 < P.val d * a := mul_pos (P.val_pos d) ha
    have e1 : P.val d * (a * S.p j) = (P.val d * a) * S.p j := by ring
    rw [e1]
    have := term_eq (κ := κ) (b := b) hm hu hp hpx
    unfold Gu at this ⊢
    rw [this]
    rfl
  -- the difference per `d`
  have hd_le : ∀ d ∈ Drig P J1 x,
      |∑ j ∈ (Lg P J1 x).filter (fun j => P.p j ≤ βf (P.val d * a)),
          f0s κ (u / ((P.val d * a) * P.p j)) / ((P.val d * a) * P.p j) -
        ∑ j ∈ (Lg Q J1 x).filter (fun j => Q.p j ≤ βf (P.val d * a)),
          f0s κ (u / ((P.val d * a) * Q.p j)) / ((P.val d * a) * Q.p j)| ≤
      12 * B * Real.log x ^ 2 / Real.log X0 / a * (1 / P.val d) := by
    intro d _
    set m := P.val d * a with hmdef
    have hm : 0 < m := mul_pos (P.val_pos d) ha
    set β := βf m
    have hrhs : 0 ≤ 12 * B * Real.log x ^ 2 / Real.log X0 / a * (1 / P.val d) := by
      have := P.val_pos d; positivity
    rcases lt_or_ge β (X0m / 2) with hlt | hge
    · -- both sums are empty
      have e1 : (Lg P J1 x).filter (fun j => P.p j ≤ β) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj h; have := hlP j hj; have : 0 < X0m := by linarith [Real.exp_pos 1]
        linarith
      have e2 : (Lg Q J1 x).filter (fun j => Q.p j ≤ β) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj h; have := hlQ j hj; have : 0 < X0m := by linarith [Real.exp_pos 1]
        linarith
      rw [e1, e2]; simp only [Finset.sum_empty, sub_self, abs_zero]; exact hrhs
    · have hβx : β ≤ x := min_le_right _ _
      have hβxm : β ≤ u / (X0 * m) := by
        have : β ≤ x / m := (min_le_left _ _).trans (min_le_left _ _)
        rw [hx, div_div] at this; exact this
      have hXa : ∀ j ∈ Lg P J1 x, X0m / 2 < P.p j := fun j hj => by
        have := hlP j hj; linarith [Real.exp_pos 1]
      have hYa : ∀ j ∈ Lg Q J1 x, X0m / 2 < Q.p j := fun j hj => by
        have := hlQ j hj; linarith [Real.exp_pos 1]
      have h := one_replacement P.p Q.p (Lg P J1 x) (Lg Q J1 x) hX0 hκ hκ1 hm hu hXm hge hβxm
        hB hXa hYa (fun s hs => hΔ s ⟨hs.1, hs.2.trans hβx⟩)
      refine h.trans ?_
      have hβ1 : 1 ≤ β := by linarith
      have hlβ : 0 ≤ Real.log β := Real.log_nonneg hβ1
      have hlβx : Real.log β ≤ Real.log x := Real.log_le_log (by linarith) hβx
      have hsq : Real.log β ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ hlβ hlβx 2
      have hv := P.val_pos d
      calc 12 * B * Real.log β ^ 2 / (Real.log X0 * m) ≤
            12 * B * Real.log x ^ 2 / (Real.log X0 * m) :=
            div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = 12 * B * Real.log x ^ 2 / Real.log X0 / a * (1 / P.val d) := by
            rw [hmdef]; field_simp
  -- assemble
  unfold PsiD
  rw [Finset.sum_comm, Finset.sum_comm (s := Lg Q J1 x), ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ Drig P J1 x, |∑ j ∈ Lg P J1 x, (if P.val d * (a * P.p j) ≤ x then
          Gu κ u (P.val d * (a * P.p j)) (max b (P.p j)) else 0) -
        ∑ j ∈ Lg Q J1 x, (if P.val d * (a * Q.p j) ≤ x then
          Gu κ u (P.val d * (a * Q.p j)) (max b (Q.p j)) else 0)|
      ≤ ∑ d ∈ Drig P J1 x, 12 * B * Real.log x ^ 2 / Real.log X0 / a * (1 / P.val d) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [hper P d hd, hper Q d hd]
        exact hd_le d hd
    _ = 12 * B * Real.log x ^ 2 / Real.log X0 / a * ∑ d ∈ Drig P J1 x, 1 / P.val d := by
        rw [Finset.mul_sum]
    _ ≤ 12 * B * Real.log x ^ 2 / Real.log X0 / a * D0 := by
        apply mul_le_mul_of_nonneg_left hD; positivity
    _ = 12 * B * Real.log (u / X0) ^ 2 * D0 / Real.log X0 / a := by ring

end BaseRange.S3
