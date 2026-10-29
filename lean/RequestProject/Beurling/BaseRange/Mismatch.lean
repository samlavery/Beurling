module

public import RequestProject.Beurling.BaseRange.RatSys

/-!
# The decision-order mismatch (proof of Lemma 7.3(b), "the rest")

`K_pt` (Noise) filters an element `w` by the decision times of its primes, `t(p) w < u` for all
`p ∣ w`; the value-order operator `K^val_pt` (`S3.Kval`) by `P⁺(w) w ≤ u`. The filters differ
only if some prime `p ∣ w` has `|p - u/w| ≤ H(p)` (`mismatch_close`, from `|t(p) - p| ≤ H(p)` and
`t(p) = p` below `X₀⁻/2`). Writing `w = p w'`, such a `p` lies within `0.52 H(s)` of
`s = √(u/w')`, so there are at most `46 H(s)` of them (Corollary 6.3(ii)), each `≥ 0.82 s`; with
`H(s)/s ≤ η_H` and `∑ 1/w' ≤ H_b` the mismatch is `≤ 56 η_H H_b/Λ` (`kpt_sub_kval_le`).
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

variable (P : BeurlingSystem)

/-- `K_pt(f₀ 1_{[X₀,∞)})(u)` as a sum over the elements of value `≤ u/X₀`. -/
lemma kpt_f0cut_eq (tw : ℕ → ℝ) {X0 : ℕ} {X0m u : ℝ} (hX : 1 < (X0 : ℝ)) (hXm : 0 < X0m)
    (hXmX : X0m ≤ X0) (hu : 0 < u) (hκ : 0 < Construction.kappaParam X0) :
    KR.Sharp.Kpt P tw X0m (f0cut X0) u =
      ∑ e ∈ (P.elems (u / X0)).filter (· ≠ 0),
        (open scoped Classical in if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
          S3.Fu (Construction.kappaParam X0) u (P.val e) else 0) := by
  classical
  have hX0 : (0 : ℝ) < X0 := by linarith
  rw [kpt_eq]
  have hsub : (P.elems (u / X0)).filter (· ≠ 0) ⊆ (P.elems (u / X0m)).filter (· ≠ 0) := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨P.mem_elems.mpr ?_, h2⟩
    exact (P.mem_elems.mp h1).trans (div_le_div_of_nonneg_left hu.le hXm hXmX)
  symm
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e he => ?_
    have h1 := P.mem_elems.mp (Finset.mem_filter.mp he).1
    have hv := P.val_pos e
    have hq : (X0 : ℝ) ≤ u / P.val e := by
      rw [le_div_iff₀ hv]; rw [le_div_iff₀ hX0] at h1; linarith
    unfold S3.Fu f0cut
    rw [if_pos hq, f0s_eq hX hκ hq]
  · intro e he0 he
    have hv := P.val_pos e
    have hlt : u / P.val e < X0 := by
      have : ¬ P.val e ≤ u / X0 := fun h => he (Finset.mem_filter.mpr
        ⟨P.mem_elems.mpr h, (Finset.mem_filter.mp he0).2⟩)
      push_neg at this
      rw [div_lt_iff₀ hv]; rw [div_lt_iff₀ hX0] at this; linarith
    unfold f0cut
    rw [if_neg (not_le.mpr hlt)]
    simp

/-- **Where the two filters differ**: some prime `p ∣ e`, `p ≥ X₀⁻/2`, has `|p - u/e| ≤ H(p)`. -/
lemma mismatch_close (tw : ℕ → ℝ) (H : ℝ → ℝ) {X0m X0 u : ℝ} (hXm : 0 < X0m) (hXmX : X0m ≤ X0)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j) {e : ℕ →₀ ℕ}
    (heu : X0 ≤ u / P.val e)
    (hne : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ ¬ (S3.maxV P e * P.val e ≤ u)) :
    ∃ j ∈ e.support, X0m / 2 ≤ P.p j ∧ |P.p j - u / P.val e| ≤ H (P.p j) := by
  have hv := P.val_pos e
  have hu : 0 < u := by
    have : 0 < u / P.val e := by linarith
    exact (div_pos_iff_of_pos_right hv).mp this
  have hval : S3.maxV P e * P.val e ≤ u ↔ ∀ j ∈ e.support, P.p j ≤ u / P.val e := by
    rw [← le_div_iff₀ hv]
    unfold S3.maxV
    rw [S3.fold_max_le_iff]
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
    have hvp : ∀ j ∈ e.support, P.p j ≤ c := by
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

/-- **The count near `√(u/w')`**: the primes `p ≥ X₀⁻/2` with `|p - u/(p w')| ≤ H(p)` and
`p w' ≤ u/X₀` have `∑ 1/p ≤ 56 η_H`, given Corollary 6.3(ii) (`hcount`), `H` `10⁻²`-Lipschitz and
`≤ y/10` on `[X₀⁻/2, ∞)`, and `H(s) ≤ η_H s` there. -/
lemma close_sum_le (H : ℝ → ℝ) {X0m X0 u v ηH : ℝ} (hXm : 0 < X0m) (hXmX : X0m ≤ X0)
    (hv : 0 < v) (hu : 0 < u)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη : 0 ≤ ηH) (L : Finset ℕ) :
    ∑ j ∈ L.filter (fun j => X0m / 2 ≤ P.p j ∧ |P.p j - u / (P.p j * v)| ≤ H (P.p j) ∧
      P.p j * v ≤ u / X0), 1 / P.p j ≤ 56 * ηH := by
  classical
  set F := L.filter (fun j => X0m / 2 ≤ P.p j ∧ |P.p j - u / (P.p j * v)| ≤ H (P.p j) ∧
      P.p j * v ≤ u / X0) with hF
  rcases F.eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]; positivity
  set s := Real.sqrt (u / v) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = u / v := Real.sq_sqrt (by positivity)
  have hX0 : 0 < X0 := by linarith
  -- the facts at one prime of `F`
  have hfact : ∀ j ∈ F, X0m / 2 ≤ s ∧ 0.9 * P.p j ≤ s ∧
      |P.p j - s| ≤ 0.53 * H s := by
    intro j hj
    obtain ⟨-, hp2, hpc, hpv⟩ := Finset.mem_filter.mp hj
    set p := P.p j
    have hp0 : 0 < p := P.p_pos j
    set c := u / (p * v) with hc
    have hpcs : p * c = s ^ 2 := by
      rw [hc, hs2]; field_simp
    have hcX : X0 ≤ c := by
      rw [hc, le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hX0] at hpv; linarith
    have hHp := hsmall p hp2
    have hpc' := abs_le.mp hpc
    have hc1 : c ≤ 1.1 * p := by linarith
    have hc2 : 0.9 * p ≤ c := by linarith
    have hsX : X0m / 2 ≤ s := by
      have : (X0m / 2) ^ 2 ≤ s ^ 2 := by
        rw [← hpcs]
        have : X0m ≤ c := hXmX.trans hcX
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp this
    have hsp : 0.9 * p ≤ s := by
      have : (0.9 * p) ^ 2 ≤ s ^ 2 := by rw [← hpcs]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp this
    have key : |p - s| * (p + s) = p * |p - c| := by
      rw [← abs_of_pos (show 0 < p + s by linarith), ← abs_mul, ← abs_of_pos hp0, ← abs_mul,
        abs_of_pos hp0]
      congr 1
      nlinarith [hpcs]
    have h1 : |p - s| * 1.9 ≤ H p := by
      have : p * |p - c| ≤ p * H p := mul_le_mul_of_nonneg_left hpc hp0.le
      have h0 : 0 ≤ |p - s| := abs_nonneg _
      nlinarith
    have hl := hlip p s hp2 hsX
    have hl' := (abs_le.mp hl).2
    refine ⟨hsX, hsp, ?_⟩
    have h0 : 0 ≤ |p - s| := abs_nonneg _
    nlinarith
  obtain ⟨j0, hj0⟩ := h
  have hsX := (hfact j0 hj0).1
  have hHs := hsmall s hsX
  have hspos : 0 < s := by linarith
  -- `F` is inside the count window at `s`
  have hsub : F ⊆ (P.primesLe (s + 1.71 * H s)).filter (fun j => s - 1.71 * H s ≤ P.p j) := by
    intro j hj
    obtain ⟨-, -, h3⟩ := hfact j hj
    have h3' := abs_le.mp h3
    have hH0 : 0 ≤ H s := by have := (abs_nonneg (P.p j - s)).trans h3; linarith
    refine Finset.mem_filter.mpr ⟨P.mem_primesLe.mpr (by linarith), by linarith⟩
  have hcard := (Finset.card_le_card hsub)
  have hcnt := hcount s hsX
  have hcardR : (F.card : ℝ) ≤ 46 * H s := (by exact_mod_cast hcard : (F.card : ℝ) ≤ _).trans hcnt
  have hterm : ∀ j ∈ F, 1 / P.p j ≤ 1.06 / s := by
    intro j hj
    obtain ⟨-, -, h3⟩ := hfact j hj
    have h3' := abs_le.mp h3
    have : 0.94 * s ≤ P.p j := by linarith
    rw [div_le_div_iff₀ (P.p_pos j) hspos]
    linarith
  calc ∑ j ∈ F, 1 / P.p j ≤ ∑ j ∈ F, 1.06 / s := Finset.sum_le_sum hterm
    _ = F.card * (1.06 / s) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 46 * H s * (1.06 / s) := mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ ≤ 46 * (ηH * s) * (1.06 / s) := by
        gcongr; exact hrat s hsX
    _ = 48.76 * ηH := by field_simp; ring
    _ ≤ 56 * ηH := by linarith

/-- **The decision-order mismatch**: `|K_pt(f₀1)(u) - K^val_pt(f₀1)(u)| ≤ 56 η_H H_b/Λ`. -/
theorem kpt_sub_kval_le (tw : ℕ → ℝ) (H : ℝ → ℝ) {X0 : ℕ} {X0m u ηH Hb : ℝ}
    (hX0e : Real.exp 1 ≤ X0) (hXm : 0 < X0m) (hXmX : X0m ≤ X0) (hu : 0 < u)
    (hκ : 0 < Construction.kappaParam X0) (hκ1 : Construction.kappaParam X0 ≤ 1)
    (hdhi : ∀ j, X0m / 2 ≤ P.p j → |tw (qp j) - P.p j| ≤ H (P.p j))
    (hdlo : ∀ j, P.p j < X0m / 2 → tw (qp j) = P.p j)
    (hlip : ∀ y z, X0m / 2 ≤ y → X0m / 2 ≤ z → |H y - H z| ≤ 1 / 100 * |y - z|)
    (hsmall : ∀ y, X0m / 2 ≤ y → H y ≤ y / 10)
    (hcount : ∀ p0, X0m / 2 ≤ p0 →
      ((((P.primesLe (p0 + 1.71 * H p0)).filter
        (fun j => p0 - 1.71 * H p0 ≤ P.p j)).card : ℕ) : ℝ) ≤ 46 * H p0)
    (hrat : ∀ s, X0m / 2 ≤ s → H s ≤ ηH * s) (hη : 0 ≤ ηH)
    (hHb : ∑ e ∈ P.elems (u / X0), 1 / P.val e ≤ Hb) :
    |KR.Sharp.Kpt P tw X0m (f0cut X0) u - S3.Kval P X0 (Construction.kappaParam X0) u| ≤
      56 * ηH * Hb / Real.log X0 := by
  classical
  set κ := Construction.kappaParam X0
  set x := u / X0 with hx
  have hX1 : (1 : ℝ) < X0 := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX0e
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ : 1 ≤ Real.log X0 := by rw [Real.le_log_iff_exp_le hX0]; exact hX0e
  set E := (P.elems x).filter (· ≠ 0)
  set cl : ℕ → (ℕ →₀ ℕ) → Prop := fun j e' => X0m / 2 ≤ P.p j ∧
    |P.p j - u / (P.p j * P.val e')| ≤ H (P.p j) ∧ P.p j * P.val e' ≤ u / X0
  rw [kpt_f0cut_eq P tw hX1 hXm hXmX hu hκ]
  unfold S3.Kval
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- per element
  have hper : ∀ e ∈ E, |(if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
      S3.Fu κ u (P.val e) else 0) - S3.Gu κ u (P.val e) (S3.maxV P e)| ≤
      1 / Real.log X0 * ∑ j ∈ P.primesLe x, if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0 := by
    intro e he
    have h1 := P.mem_elems.mp (Finset.mem_filter.mp he).1
    have hv := P.val_pos e
    obtain ⟨hF0, hF1⟩ := S3.Fu_bounds hX0e hκ hκ1 hv h1
    have hnn : 0 ≤ ∑ j ∈ P.primesLe x, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    have heu : (X0 : ℝ) ≤ u / P.val e := by
      rw [le_div_iff₀ hv]; rw [le_div_iff₀ hX0] at h1; linarith
    unfold S3.Gu
    by_cases hiff : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ S3.maxV P e * P.val e ≤ u
    · rw [if_congr hiff rfl rfl, sub_self, abs_zero]; positivity
    · have hne : (∀ j ∈ e.support, tw (qp j) * P.val e < u) ↔ ¬ (S3.maxV P e * P.val e ≤ u) := by
        tauto
      obtain ⟨j, hj, hj2, hj3⟩ := mismatch_close P tw H hXm hXmX hdhi hdlo heu hne
      have hjL : j ∈ P.primesLe x :=
        P.mem_primesLe.mpr ((S3.p_le_val P hj).trans h1)
      have hge : 1 / P.val e ≤ ∑ j ∈ P.primesLe x, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
          |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0) := by
        have := Finset.single_le_sum (f := fun j => if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
          |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0)
          (fun j _ => by simp only; split_ifs <;> positivity) hjL
        simp only at this
        rwa [if_pos ⟨hj, hj2, hj3⟩] at this
      have habs : |(if ∀ j ∈ e.support, tw (qp j) * P.val e < u then
          S3.Fu κ u (P.val e) else 0) - (if S3.maxV P e * P.val e ≤ u then
          S3.Fu κ u (P.val e) else 0)| ≤ S3.Fu κ u (P.val e) := by
        by_cases hd : ∀ j ∈ e.support, tw (qp j) * P.val e < u
        · rw [if_pos hd, if_neg (hne.mp hd), sub_zero, abs_of_nonneg hF0]
        · rw [if_neg hd, if_pos (by by_contra h; exact hd (hne.mpr h)), zero_sub, abs_neg,
            abs_of_nonneg hF0]
      refine habs.trans (hF1.trans ?_)
      calc 1 / (Real.log X0 * P.val e) = 1 / Real.log X0 * (1 / P.val e) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
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
  calc 1 / Real.log X0 * ∑ j ∈ P.primesLe x, ∑ e ∈ E, (if j ∈ e.support ∧ X0m / 2 ≤ P.p j ∧
        |P.p j - u / P.val e| ≤ H (P.p j) then 1 / P.val e else 0)
      ≤ 1 / Real.log X0 * (Hb * (56 * ηH)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.sum_le_sum hpj).trans ?_
        rw [Finset.sum_comm]
        exact (Finset.sum_le_sum hinner).trans htot2
    _ = 56 * ηH * Hb / Real.log X0 := by ring

end BaseRange
