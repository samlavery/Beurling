module

public import RequestProject.Beurling.Model.G1BStep3

/-!
# The field `hdec34` of `G1BInputs` (Proposition 5.35(B), Step 3)

04f-bridge.tex, proof of Proposition 5.35, range (B), Step 3. From the exact decomposition
`rhoSh_sub_eq` (`G1BStep3.lean`):

* `thrPart_le` : the threshold changes are at most `3 thrS` (`|T'| ≤ 3`, Lemma 5.5 and
  `tauIn_of_chi`: a coefficient that changes between `z` and `y` has `τ ∈ [y(1-2δ), y)`, so it
  is counted by `threshSum tJ y (2δ)`, Lemma 5.23 at `2δ`);
* `abs_rhoSh_jF_le` : the jump part is at most `jS`;
* `bdd_detF`, `bdd_oscF`, `bdd_sigF` : the suprema `detS`, `oscS`, `sigS` are finite;
* `hdec34_R` : **the field `hdec34`**: `ρ^sh(z) - ρ^sh(y) ≤ 4 thrS + j₀ jS + detS + othS` on `J`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- The labels of the realised system carry the decision times `tJ`. -/
lemma twR_qp (ω : JitterΩ) (j : ℕ) : twR θ X₀ ω (qp j) = Queue6.tJ θ X₀ ω j := by
  unfold twR
  rw [if_pos (qp_prime j)]
  simp only [Nat.count_nth_of_infinite Nat.infinite_setOf_prime]
  rfl

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- `|T'| ≤ 3` below the horizon. -/
lemma abs_TpR_le (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {u : ℝ} (huZ : u / Xm X₀ ≤ Z) : |TpR θ X₀ ω u| ≤ 3 := by
  have h1 := TcR_abs_le hc hev ω hT huZ
  have hj0 := jzX_nonneg hc
  have hj1 := jzX_le_one (θ := θ) (X₀ := X₀) hc
  have hi0 : 0 ≤ KR.Chain.ind X₀ u := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hi1 : KR.Chain.ind X₀ u ≤ 1 := Set.indicator_le_self' (fun _ _ => zero_le_one) _
  unfold TpR
  have : jzX X₀ * KR.Chain.ind X₀ u ≤ 1 := by nlinarith
  have : 0 ≤ jzX X₀ * KR.Chain.ind X₀ u := mul_nonneg hj0 hi0
  have := abs_le.mp h1
  rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **Threshold changes** (Step 3, first bullet): `A(z) ≤ 3 threshSum(tJ, y, 2δ)` for
`z ∈ [y(1-2δ), y]`. -/
theorem thrPart_le (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y z δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyZ : y / Xm X₀ ≤ Z) (hz1 : y * (1 - 2 * δ) ≤ z)
    (hzy : z ≤ y) :
    thrPart θ X₀ ω y z ≤ 3 * thrS θ X₀ ω y δ := by
  classical
  set P := PR θ X₀ ω with hP
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hdec := KR.Chain.dec_R hT
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  set cond : (ℕ →₀ ℕ) → Prop := fun e => (X₀ : ℝ) ≤ z / P.val e ∧
    LemmaM.chi (twR θ X₀ ω) P.labelVal y (iota e) ∧
      ¬ LemmaM.chi (twR θ X₀ ω) P.labelVal z (iota e) with hcond
  have hterm : ∀ e ∈ P.elems (y / Xm X₀),
      (cN P (twR θ X₀ ω) (Xm X₀) z (iota e) - cN P (twR θ X₀ ω) (Xm X₀) y (iota e)) *
        TpR θ X₀ ω (z / P.val e) / P.val e ≤ if cond e then 3 * (1 / P.val e) else 0 := by
    intro e _
    have hv := P.val_pos e
    have hv1 := P.one_le_val e
    by_cases hlow : z / P.val e < X₀
    · rw [TpR_low hc ω hlow, mul_zero, zero_div]
      split_ifs <;> positivity
    push_neg at hlow
    have hz0 : 0 ≤ z := by
      have h := (le_div_iff₀ hv).mp hlow
      nlinarith [Nat.cast_nonneg (α := ℝ) X₀]
    have hzV : z / P.val e ≤ y := le_trans (div_le_self hz0 hv1) hzy
    have hTb := abs_TpR_le hc hev ω hT (u := z / P.val e)
      (le_trans (div_le_div_of_nonneg_right hzV hXm.le) hyZ)
    have hXz : Xm X₀ ≤ z := by
      have : z / P.val e ≤ z := div_le_self hz0 hv1
      linarith
    have hn : 1 ≤ iota e := iota_pos e
    have hcz := KR.mass_eq_moebius P.labelVal z hdec.1 hval hXm.le hXz hn
    have hcy := KR.mass_eq_moebius P.labelVal y hdec.1 hval hXm.le (hXz.trans hzy) hn
    have hcutz : Xm X₀ ≤ z / LemmaM.valN P.labelVal (iota e) := by
      rw [P.valN_iota]; linarith
    have hcuty : Xm X₀ ≤ y / LemmaM.valN P.labelVal (iota e) :=
      le_trans hcutz (div_le_div_of_nonneg_right hzy (KR.valN_labelVal_pos P _).le)
    rw [if_pos hcutz] at hcz
    rw [if_pos hcuty] at hcy
    have hcz' : cN P (twR θ X₀ ω) (Xm X₀) z (iota e) = _ := hcz
    have hcy' : cN P (twR θ X₀ ω) (Xm X₀) y (iota e) = _ := hcy
    rw [hcz', hcy']
    have hmu : |((ArithmeticFunction.moebius (iota e) : ℤ) : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or (iota e) with h | h | h <;> simp [h]
    by_cases hχ : cond e
    · rw [if_pos hχ]
      obtain ⟨-, hχy, hχz⟩ := hχ
      rw [if_neg hχz, if_pos hχy]
      have hT3 := abs_le.mp hTb
      have hm := abs_le.mp hmu
      rw [div_le_iff₀ hv]
      have e1 : 3 * (1 / P.val e) * P.val e = 3 := by field_simp
      rw [e1]
      nlinarith
    · rw [if_neg hχ]
      have hiff : LemmaM.chi (twR θ X₀ ω) P.labelVal z (iota e) ↔
          LemmaM.chi (twR θ X₀ ω) P.labelVal y (iota e) := by
        constructor
        · exact chi_mono hzy
        · intro h
          by_contra h'
          exact hχ ⟨hlow, h, h'⟩
      simp only [hiff, sub_self, mul_one, zero_mul, zero_div, le_refl]
  -- the sum
  have hsub : (P.elems (y / Xm X₀)).filter cond ⊆ (P.elems y).filter
      (fun e => Sqf e ∧ P.TauIn (Queue6.tJ θ X₀ ω) (y * (1 - 2 * δ)) y e) := by
    intro e he
    obtain ⟨-, hlow, hχy, hχz⟩ := Finset.mem_filter.mp he
    have hv := P.val_pos e
    refine Finset.mem_filter.mpr ⟨?_, fun j => squarefree_iota hχy.1 j, ?_⟩
    · rw [mem_elems]
      have hX1 : (1 : ℝ) ≤ X₀ := (QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hc.hX).le
      rw [le_div_iff₀ hv] at hlow
      nlinarith
    · exact P.tauIn_of_chi (twR_qp ω) (fun j => lt_of_lt_of_le one_pos (Queue6.t_ge_R hc ω j))
        hχy hχz hz1
  calc thrPart θ X₀ ω y z ≤ ∑ e ∈ P.elems (y / Xm X₀), if cond e then 3 * (1 / P.val e) else 0 :=
        Finset.sum_le_sum hterm
    _ = 3 * ∑ e ∈ (P.elems (y / Xm X₀)).filter cond, 1 / P.val e := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
    _ ≤ 3 * thrS θ X₀ ω y δ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        unfold thrS threshSum
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ =>
          div_nonneg zero_le_one (P.val_pos e).le
        convert! hsub using 2

/-- **The jump at `X₀`** (Step 3, second bullet): `|∑_n c_n(y) 1[z/n < X₀ ≤ y/n]/n| ≤ jS` for
`r ≥ 1 - 2δ`. -/
theorem abs_rhoSh_jF_le (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y δ r : ℝ} (hy : (X₀ : ℝ) ≤ y) (hr : 1 - 2 * δ ≤ r) :
    |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (jF X₀ r)| ≤ jS θ X₀ ω y δ := by
  classical
  set P := PR θ X₀ ω with hP
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hdec := KR.Chain.dec_R hT
  rw [G1.rhoSh_eq_elems]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold jS
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun e _ => ?_
  have hv := P.val_pos e
  have hcb := G1.abs_cN_le_one (P := P) hdec.1 hXm.le (hXmX.trans hy) (iota e) (iota_pos e)
  unfold jF
  by_cases h : (X₀ : ℝ) ≤ y / P.val e ∧ r * (y / P.val e) < X₀
  · rw [if_pos h]
    have hv0 : 0 ≤ y / P.val e := le_trans (Nat.cast_nonneg _) h.1
    rw [if_pos ⟨h.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hr hv0) h.2⟩]
    rw [mul_one, abs_div, abs_of_pos hv]
    exact div_le_div_of_nonneg_right hcb hv.le
  · rw [if_neg h, mul_zero, zero_div, abs_zero]
    split_ifs <;> positivity

omit hev in
/-- `|ρ_det| ≤ 1.01` on `[X₀, ∞)`. -/
lemma abs_rhoDet_le {u : ℝ} (hu : (X₀ : ℝ) ≤ u) :
    |Target.rhoDet X₀ (kappaParam X₀) u| ≤ 1.01 := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hκ0 := (kappa_facts hc.hX).1
  have hu0 : 0 < u := by linarith
  have h0 := rhoDet_nonneg X₀ hκ0 hu0.le
  have h1 := (BaseRange.rhoDet_le_one_add X₀ hκ0 hu0).trans
    (by linarith [inv_kappa_le hc hu] : 1 + 1 / (kappaParam X₀ * u) ≤ 1 + 1 / 100)
  rw [abs_of_nonneg h0]; linarith

omit hev in
lemma abs_RpR_le (ω : JitterΩ) {u : ℝ} (hu : (X₀ : ℝ) ≤ u) : |RpR θ X₀ ω u| ≤ 1 := by
  have hR := abs_deriv_osc_le hc.hθ hc.hX (gammaD_range (θ := θ) hc.hX (DF θ X₀ ω)) hu
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hL : 10 ^ 8 ≤ Real.log u := hc.hX.trans (Real.log_le_log (by linarith) hu)
  have : 0.02 / Real.log u ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  unfold RpR alphaD
  exact hR.trans this

lemma abs_sigR_le (ω : JitterΩ) {u Y : ℝ} (hu : (X₀ : ℝ) ≤ u) (huY : u ≤ Y) :
    |sigR θ X₀ ω u| ≤ (∑ w ∈ KR.NAll (PR θ X₀ ω) Y (Xm X₀), 2 / Vl (PR θ X₀ ω) w) + 1 := by
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hu0 : 0 < u := by linarith
  have hLu : 10 ^ 8 ≤ Real.log u := hc.hX.trans (Real.log_le_log (by linarith) hu)
  have hρ2 : ∀ z, |rhoT θ X₀ ω z| ≤ 2 := fun z => by
    rw [abs_of_nonneg (rhoT_nonneg ω z)]; exact rhoT_le_two hc hev ω z
  have hK := KAbsR_abs_le hc ω hρ2 huY
  have hA1 : absorbedDensityCap (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) u ≤ 1 := by
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  have hA0 : 0 ≤ absorbedDensityCap (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) u := by
    refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) (by linarith))
    unfold absorbedBump
    split_ifs
    · by_cases hm : u ∈ Icc (uA θ a) a
      · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos hu0 _).le
      · rw [Set.indicator_of_notMem hm]
    · exact le_rfl
  unfold sigR
  have := abs_le.mp hK
  rw [abs_le]; constructor <;> linarith

omit hc hev in
/-- For `r ≤ 1`, `v ≥ X₀`: `X₀ ≤ max(rv, X₀) ≤ v`. -/
lemma max_mem {r v : ℝ} (hr1 : r ≤ 1) (hv : (X₀ : ℝ) ≤ v) :
    (X₀ : ℝ) ≤ max (r * v) X₀ ∧ max (r * v) X₀ ≤ v := by
  have hv0 : 0 ≤ v := le_trans (Nat.cast_nonneg _) hv
  exact ⟨le_max_right _ _, max_le (by nlinarith) hv⟩

variable (θ X₀) in
/-- The crude bound of the `σ_𝒜` change at heights `≤ y`. -/
noncomputable def sigM (ω : JitterΩ) (y : ℝ) : ℝ :=
  2 * ((∑ w ∈ KR.NAll (PR θ X₀ ω) y (Xm X₀), 2 / Vl (PR θ X₀ ω) w) + 1)

/-- The three changes are bounded on `[X₀, y]`, uniformly in `r ∈ [0, 1]`. -/
lemma abs_F_le (ω : JitterΩ) {r v y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hvy : v ≤ y) :
    |detF X₀ r v| ≤ 3 ∧ |oscF θ X₀ ω r v| ≤ 2 ∧ |sigF θ X₀ ω r v| ≤ sigM θ X₀ ω y := by
  have hM0 : 0 ≤ sigM θ X₀ ω y := by
    unfold sigM
    have : 0 ≤ ∑ w ∈ KR.NAll (PR θ X₀ ω) y (Xm X₀), 2 / Vl (PR θ X₀ ω) w :=
      Finset.sum_nonneg fun w _ => div_nonneg (by norm_num) (KR.Sharp.Vl_pos _ w).le
    linarith
  unfold detF oscF sigF
  by_cases hv : (X₀ : ℝ) ≤ v
  · obtain ⟨h1, h2⟩ := max_mem hr1 hv
    rw [if_pos hv, if_pos hv, if_pos hv]
    refine ⟨?_, ?_, ?_⟩
    · have := abs_rhoDet_le hc hv
      have := abs_rhoDet_le hc h1
      calc _ ≤ |Target.rhoDet X₀ (kappaParam X₀) v| +
            |Target.rhoDet X₀ (kappaParam X₀) (max (r * v) X₀)| := abs_sub _ _
        _ ≤ 3 := by linarith
    · have := abs_RpR_le hc ω hv
      have := abs_RpR_le hc ω h1
      calc _ ≤ |RpR θ X₀ ω (max (r * v) X₀)| + |RpR θ X₀ ω v| := abs_sub _ _
        _ ≤ 2 := by linarith
    · have := abs_sigR_le hc hev ω hv hvy
      have := abs_sigR_le hc hev ω h1 (h2.trans hvy)
      unfold sigM
      calc _ ≤ |sigR θ X₀ ω (max (r * v) X₀)| + |sigR θ X₀ ω v| := abs_sub _ _
        _ ≤ _ := by linarith
  · rw [if_neg hv, if_neg hv, if_neg hv, abs_zero]
    exact ⟨by norm_num, by norm_num, hM0⟩

/-- The suprema `detS`, `oscS`, `sigS` are over bounded families. -/
lemma bdd_F (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    BddAbove (Set.range fun z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)) =>
        |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ (z / y))|) ∧
      BddAbove (Set.range fun z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)) =>
        |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y))|) ∧
      BddAbove (Set.range fun z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)) =>
        |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω (z / y))|) := by
  set P := PR θ X₀ ω with hP
  have hXm := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hdec := KR.Chain.dec_R hT
  have hy0 : 0 < y := by
    linarith [QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX]
  have hr : ∀ z : Icc (y * (1 - 2 * δ)) (y * (1 - δ)), 0 ≤ (z : ℝ) / y ∧ (z : ℝ) / y ≤ 1 := by
    rintro ⟨z, hz1, hz2⟩
    refine ⟨div_nonneg (le_trans (by nlinarith) hz1) hy0.le, (div_le_one hy0).mpr ?_⟩
    nlinarith
  have hvy : ∀ e : ℕ →₀ ℕ, y / P.val e ≤ y := fun e =>
    div_le_self hy0.le (P.one_le_val e)
  set S := ∑ e ∈ P.elems (y / Xm X₀), 1 / P.val e
  refine ⟨⟨3 * S, ?_⟩, ⟨2 * S, ?_⟩, ⟨sigM θ X₀ ω y * S, ?_⟩⟩ <;>
  · rintro _ ⟨z, rfl⟩
    refine abs_rhoSh_le_of hdec.1 hXm (hXmX.trans hy) fun e _ => ?_
    have h := abs_F_le hc hev ω (hr z).1 (hr z).2 (hvy e)
    first | exact h.1 | exact h.2.1 | exact h.2.2

set_option maxHeartbeats 1000000 in
/-- **The field `hdec34`** (Proposition 5.35(B), Step 3): for `z ∈ J = [y(1-2δ), y(1-δ)]`,
`ρ^sh(z) - ρ^sh(y) ≤ 4 thrS + j₀ jS + detS + othS`. -/
theorem hdec34_R (ω : JitterΩ) {Z η1 η2 ε ϑ : ℝ} {ε1 : ℝ → ℝ}
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε ϑ)
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyZ : y / Xm X₀ ≤ Z) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
      rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) z
          (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) -
        rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y
          (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) ≤
        4 * thrS θ X₀ ω y δ + jzX X₀ * jS θ X₀ ω y δ + detS θ X₀ ω y δ + othS θ X₀ ω y δ := by
  intro z hz
  have hy0 : 0 < y := by
    linarith [QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX]
  have hz0 : 0 ≤ z := le_trans (by nlinarith) hz.1
  have hzy : z ≤ y := by nlinarith [hz.2]
  have hid := rhoSh_sub_eq hc ω hy0 hz0 hzy
  have hTp : (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) = TpR θ X₀ ω := rfl
  rw [hTp, hid]
  obtain ⟨hb1, hb2, hb3⟩ := bdd_F hc hev ω hT hy hδ0 hδ
  set zz : Icc (y * (1 - 2 * δ)) (y * (1 - δ)) := ⟨z, hz⟩
  have hD := le_ciSup hb1 zz
  have hO := le_ciSup hb2 zz
  have hS := le_ciSup hb3 zz
  have hA := thrPart_le hc hev ω hT hy hyZ hz.1 hzy
  have hr : 1 - 2 * δ ≤ z / y := by rw [le_div_iff₀ hy0]; nlinarith [hz.1]
  have hJ := abs_rhoSh_jF_le hc hev ω hT hy hr
  have hj0 := jzX_nonneg hc
  have hthr0 : 0 ≤ thrS θ X₀ ω y δ := by
    unfold thrS threshSum
    exact Finset.sum_nonneg fun e _ => div_nonneg zero_le_one ((PR θ X₀ ω).val_pos e).le
  unfold detS othS oscS sigS
  have h1 := le_abs_self (rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (detF X₀ (z / y)))
  have h2 := le_abs_self (rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y)))
  have h3 := le_abs_self (rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω (z / y)))
  have h4 := neg_abs_le (rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (jF X₀ (z / y)))
  have h5 : -(jzX X₀ * rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (jF X₀ (z / y))) ≤
      jzX X₀ * jS θ X₀ ω y δ := by nlinarith
  linarith

end

end BModel

end
