module

public import RequestProject.Beurling.RankFull.RunSum

/-!
# Lemma A.6 (S3): the block bound with variable content, and the end step

This file proves the deterministic part of Lemma A.6 (S3) of Appendix A (the version corrected
in entries #48 and #55 of `CORRECTIONS-vs-v3.md`: the bound (a) sums over **every** non-empty
content of the block, not over one free structure at a time).

Setting of (S3)(a), stated for one block `F_t` and one `ω`:
* the realised primes with slots in `[s_{t+1}, s_max]` are listed in slot order as
  `p 0, p 1, …, p (N-1)`, all `> 1`;
* `Ea = Eu_s(s_{t+1}) > 0`, and, since there is one prime per slot,
  `Eu_s(slot of p i) = euAt Ea p i := Ea ∏_{i' < i} (1 - 1/p i')⁻¹` and
  `Eu_s(u) = euAt Ea p (i+1)` for the first slot `u` after the slot of `p i`;
* a content of `F_t` is a non-empty set `S` of these primes (its latest prime `f_t` is
  `p (S.sup id)`) with, for each `g ∈ S`, a non-zero exponent vector in the `K = K_t` chain rows;
  summing `g^{-a_g}` over the non-zero exponent vectors gives `(1 - 1/g)^{-K} - 1`
  (`tsum_exponents`);
* `χ_t ∈ [0,1]` depends on the content only through `u_t`, and `χ_t > 0` forces
  `Eu_s(u_t) ≤ A_top` (this is how the sure top bound (S3)(d) enters; we keep it as this
  hypothesis);
* `Φ_{t-1}(u) = G_{t-1}(Eu_s(u))/Eu_s(u)^{K_{t-1}}`, with `G_{t-1} ≥ 0` non-increasing on `(0,∞)`.

Main results:
* `RankFull.prime_step` : the per-prime inequality of the proof of (S3)(a);
* `RankFull.block_bound` : **Lemma A.6 (S3)(a)**;
* `RankFull.GRun_nonneg`, `RankFull.GRun_antitone` : each `G_t` is `≥ 0` and non-increasing;
* `RankFull.end_step` : the algebra of **(S3)(c)**;
* `RankFull.finG_le_zero_runs`, `RankFull.finG_le_cover` : the chain bound of the proof of
  Proposition 6.19 (Cover Bound): `Fin ≤ (1 + κλ)^{s_R} (κ^κ/κ!) A^κ`.
-/

@[expose] public section

open Finset Real intervalIntegral

namespace RankFull

/-! ## The sum over exponent vectors -/

/-- `∑_{v ∈ ℕ^K} ∏_i x^{v_i} = (∑_n x^n)^K` in `ℝ≥0∞`. -/
lemma tsum_prod_pow (x : ENNReal) : ∀ K : ℕ,
    ∑' v : Fin K → ℕ, ∏ i, x ^ v i = (∑' n : ℕ, x ^ n) ^ K
  | 0 => by simp
  | K + 1 => by
    rw [← (Fin.consEquiv (fun _ : Fin (K + 1) => ℕ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, tsum_prod_pow x K]
    rw [ENNReal.tsum_mul_right, pow_succ']

/-- **The sum over exponent vectors** (proof of Lemma A.6 (S3)(a)): for a realised prime `g > 1`,
the sum of `g^{-a}` over its non-zero exponent vectors in `K` chain rows (`a` the total exponent)
is `(1 - 1/g)^{-K} - 1`; with the zero vector (`g` absent) it is `(1 - 1/g)^{-K}`. -/
theorem tsum_exponents {g : ℝ} (hg : 1 < g) (K : ℕ) :
    ∑' v : Fin K → ℕ, ENNReal.ofReal (g⁻¹ ^ (∑ i, v i)) = ENNReal.ofReal ((1 - g⁻¹)⁻¹ ^ K) ∧
    ∑' v : Fin K → ℕ, (if v = 0 then 0 else ENNReal.ofReal (g⁻¹ ^ (∑ i, v i))) =
      ENNReal.ofReal ((1 - g⁻¹)⁻¹ ^ K - 1) := by
  have hg0 : 0 < g⁻¹ := inv_pos.mpr (by linarith)
  have hg1 : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ hg
  have hterm : ∀ v : Fin K → ℕ, ENNReal.ofReal (g⁻¹ ^ (∑ i, v i)) =
      ∏ i, (ENNReal.ofReal g⁻¹) ^ v i := by
    intro v
    rw [← Finset.prod_pow_eq_pow_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    simp_rw [ENNReal.ofReal_pow hg0.le]
  have hgeom : ∑' n : ℕ, (ENNReal.ofReal g⁻¹) ^ n = ENNReal.ofReal ((1 - g⁻¹)⁻¹) := by
    rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hg0.le,
      ENNReal.ofReal_inv_of_pos (by linarith)]
  have h1 : ∑' v : Fin K → ℕ, ENNReal.ofReal (g⁻¹ ^ (∑ i, v i)) =
      ENNReal.ofReal ((1 - g⁻¹)⁻¹ ^ K) := by
    simp_rw [hterm]
    rw [tsum_prod_pow, hgeom, ENNReal.ofReal_pow (by have := sub_pos.mpr hg1; positivity)]
  refine ⟨h1, ?_⟩
  have hsplit := ENNReal.tsum_eq_add_tsum_ite (f := fun v : Fin K → ℕ =>
    ENNReal.ofReal (g⁻¹ ^ (∑ i, v i))) 0
  simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero, ENNReal.ofReal_one] at hsplit
  rw [h1] at hsplit
  have hge : (1 : ℝ) ≤ (1 - g⁻¹)⁻¹ ^ K :=
    one_le_pow₀ (one_le_inv₀ (by linarith) |>.mpr (by linarith))
  rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one, hsplit, ENNReal.add_sub_cancel_left
    ENNReal.one_ne_top]
  exact tsum_congr fun v => by by_cases h : v = 0 <;> simp [h]

/-! ## The per-prime inequality -/

/-- `G_t` from `G_{t-1}` by (A.Grec): `G_t(E) = ∫_E^A K x^{j-1} G_{t-1}(x) dx` for `E < A`,
`0` for `E ≥ A`. -/
noncomputable def Gnext (A : ℝ) (K j : ℕ) (G : ℝ → ℝ) (E : ℝ) : ℝ :=
  if E < A then ∫ x in E..A, (K : ℝ) * x ^ ((j : ℤ) - 1) * G x else 0

lemma GRun_cons (A : ℝ) (j : ℕ) (l : List ℕ) :
    GRun A (j :: l) = Gnext A (j + l.sum) j (GRun A l) := rfl

lemma intervalIntegrable_chain {K j : ℕ} {G : ℝ → ℝ} (hGanti : AntitoneOn G (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x => (K : ℝ) * x ^ ((j : ℤ) - 1) * G x) MeasureTheory.volume a b := by
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    intro x hx
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
  have hG : IntervalIntegrable G MeasureTheory.volume a b := (hGanti.mono hsub).intervalIntegrable
  have hc : ContinuousOn (fun x : ℝ => (K : ℝ) * x ^ ((j : ℤ) - 1)) (Set.uIcc a b) := by
    refine continuousOn_const.mul ?_
    exact ContinuousOn.zpow₀ continuousOn_id _ fun x hx => Or.inl (ne_of_gt (hsub hx))
  exact hG.continuousOn_mul hc

/-- **The per-prime inequality** in the proof of Lemma A.6 (S3)(a). With `K = m + j`,
`0 < x < 1`, `E₁ > 0`, `E₂ = E₁/(1-x)` and `G ≥ 0` non-increasing on `(0,∞)`:
`E₁^K ((1-x)^{-K} - 1) G(E₂)/E₂^m ≤ ∫_{E₁}^{E₂} K y^{j-1} G(y) dy`. -/
theorem prime_step {K m j : ℕ} (hK : K = m + j) {E₁ x : ℝ} (hE₁ : 0 < E₁) (hx0 : 0 < x)
    (hx1 : x < 1) {G : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ G y) (hGanti : AntitoneOn G (Set.Ioi 0)) :
    E₁ ^ K * ((1 - x)⁻¹ ^ K - 1) * (G (E₁ / (1 - x)) / (E₁ / (1 - x)) ^ m) ≤
      ∫ y in E₁..E₁ / (1 - x), (K : ℝ) * y ^ ((j : ℤ) - 1) * G y := by
  set r := 1 - x with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by linarith
  set E₂ := E₁ / r with hE₂
  have hE₂0 : 0 < E₂ := div_pos hE₁ hr0
  have hE12 : E₁ ≤ E₂ := by rw [hE₂, le_div_iff₀ hr0]; nlinarith
  have hGE₂ := hG0 E₂ hE₂0
  -- the left side is `E₁^j (r^{-j} - r^m) G(E₂)`
  have hlhs : E₁ ^ K * (r⁻¹ ^ K - 1) * (G E₂ / E₂ ^ m) =
      E₁ ^ j * (r⁻¹ ^ j - r ^ m) * G E₂ := by
    rw [hE₂, hK, div_pow, pow_add, pow_add, inv_pow, inv_pow]
    field_simp
  rw [hlhs]
  -- lower bound for the integral: `G(E₂) ∫_{E₁}^{E₂} K y^{j-1} dy`
  have hint_lower : G E₂ * ∫ y in E₁..E₂, (K : ℝ) * y ^ ((j : ℤ) - 1) ≤
      ∫ y in E₁..E₂, (K : ℝ) * y ^ ((j : ℤ) - 1) * G y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hE12
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (continuousOn_const.mul ?_)
      refine ContinuousOn.zpow₀ continuousOn_id _ fun y hy => Or.inl ?_
      rw [Set.uIcc_of_le hE12] at hy; exact ne_of_gt (lt_of_lt_of_le hE₁ hy.1)
    · exact intervalIntegrable_chain hGanti hE₁ hE₂0
    · intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hE₁ hy.1
      have : G E₂ ≤ G y := hGanti hy0 hE₂0 hy.2
      have : 0 ≤ (K : ℝ) * y ^ ((j : ℤ) - 1) := by positivity
      nlinarith
  refine le_trans ?_ hint_lower
  rw [mul_comm (G E₂)]
  refine mul_le_mul_of_nonneg_right ?_ hGE₂
  -- Bernoulli: `1 - r^m ≤ m x`
  have hbern : 1 - r ^ m ≤ m * x := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) m
    rw [show (1 : ℝ) + -x = 1 - x by ring] at this
    rw [hr]; linarith
  rcases Nat.eq_zero_or_pos j with hj | hj
  · -- `j = 0`: `1 - r^m ≤ m x ≤ m log(E₂/E₁) = ∫ m/y`
    subst hj
    simp only [pow_zero, Nat.cast_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one, one_mul,
      add_zero] at hK ⊢
    have hint : ∫ y in E₁..E₂, (K : ℝ) * y⁻¹ = K * Real.log (E₂ / E₁) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hE₁ hE₂0]
    rw [hint]
    have hlog : x ≤ Real.log (E₂ / E₁) := by
      rw [hE₂, div_div_cancel_left' hE₁.ne', Real.log_inv]
      have := Real.log_le_sub_one_of_pos hr0
      linarith
    rw [hK]
    have : (0 : ℝ) ≤ m := by positivity
    nlinarith
  · -- `j ≥ 1`
    have hint : ∫ y in E₁..E₂, (K : ℝ) * y ^ ((j : ℤ) - 1) = K / j * (E₂ ^ j - E₁ ^ j) := by
      have hz : ∀ y : ℝ, y ^ ((j : ℤ) - 1) = y ^ (j - 1) := by
        intro y; rw [show ((j : ℤ) - 1) = ((j - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      simp_rw [hz]
      rw [intervalIntegral.integral_const_mul, integral_pow, Nat.sub_add_cancel hj]
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
      rw [show ((j - 1 : ℕ) : ℝ) + 1 = j by rw [Nat.cast_sub hj]; push_cast; ring]
      field_simp
    rw [hint]
    have hE₂j : E₂ ^ j = E₁ ^ j * r⁻¹ ^ j := by rw [hE₂, div_eq_mul_inv, mul_pow]
    rw [hE₂j]
    have hu : 1 ≤ r⁻¹ := one_le_inv₀ hr0 |>.mpr hr1.le
    -- `r^{-j} - 1 ≥ j (r^{-1} - 1) ≥ j x`
    have hbern2 : 1 + j * (r⁻¹ - 1) ≤ r⁻¹ ^ j := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ r⁻¹ - 1 by linarith) j
      simpa using this
    have hux : x ≤ r⁻¹ - 1 := by
      rw [hr, le_sub_iff_add_le, le_inv_comm₀ (by linarith) (by linarith)]
      rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
      nlinarith
    have hjr : (j : ℝ) ≥ 1 := by exact_mod_cast hj
    -- `r^{-j} - r^m ≤ (K/j)(r^{-j} - 1)`
    have key : r⁻¹ ^ j - r ^ m ≤ K / j * (r⁻¹ ^ j - 1) := by
      have hKj : (K : ℝ) / j = 1 + m / j := by
        rw [hK]; push_cast; field_simp; ring
      rw [hKj]
      have h1 : (m : ℝ) / j * (j * x) ≤ (m : ℝ) / j * (r⁻¹ ^ j - 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      have h2 : (m : ℝ) / j * (j * x) = m * x := by field_simp
      nlinarith
    have hE1j : 0 ≤ E₁ ^ j := by positivity
    calc E₁ ^ j * (r⁻¹ ^ j - r ^ m) ≤ E₁ ^ j * (K / j * (r⁻¹ ^ j - 1)) :=
          mul_le_mul_of_nonneg_left key hE1j
      _ = K / j * (E₁ ^ j * r⁻¹ ^ j - E₁ ^ j) := by ring

/-! ## Chains of intervals -/

lemma ae_nonneg_Ioc {f : ℝ → ℝ} (hf0 : ∀ y, 0 < y → 0 ≤ f y) {c d : ℝ} (hc : 0 < c) :
    0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc c d)] f := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
  exact hf0 y (hc.trans hy.1)

/-- The intervals `[e_i, e_{i+1}]` of a non-decreasing chain, weighted by `χ_i ∈ [0,1]`, where
`χ_i > 0` forces `e_{i+1} ≤ A`, have total integral at most `∫_{e_0}^A f` (for `f ≥ 0`). -/
lemma sum_chi_integral_le {N : ℕ} {e : ℕ → ℝ} (he0 : 0 < e 0)
    (hmono : ∀ i < N, e i ≤ e (i + 1)) {χ : ℕ → ℝ} (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ 1)
    {A : ℝ} (hχA : ∀ i < N, 0 < χ i → e (i + 1) ≤ A) {f : ℝ → ℝ}
    (hf0 : ∀ y, 0 < y → 0 ≤ f y)
    (hfi : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f MeasureTheory.volume a b) :
    ∑ i ∈ range N, χ i * ∫ x in e i..e (i + 1), f x ≤
      (if e 0 < A then ∫ x in e 0..A, f x else 0) := by
  have hle : ∀ a b, a ≤ b → b ≤ N → e a ≤ e b := by
    intro a b hab hbN
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact (ih (by omega)).trans (hmono b (by omega))
  have hpos : ∀ i ≤ N, 0 < e i := fun i hi => he0.trans_le (hle 0 i (Nat.zero_le _) hi)
  split_ifs with h0A
  · have key : ∀ n ≤ N, ∑ i ∈ range n, χ i * ∫ x in e i..e (i + 1), f x ≤
        ∫ x in e 0..min (e n) A, f x := by
      intro n
      induction n with
      | zero => intro _; simp [min_eq_left h0A.le]
      | succ n ih =>
        intro hn
        rw [Finset.sum_range_succ]
        have ihn := ih (by omega)
        have hen : e 0 ≤ e n := hle 0 n (Nat.zero_le _) (by omega)
        have hmin_pos : 0 < min (e n) A := lt_min (hpos n (by omega)) (he0.trans h0A)
        by_cases hχ : 0 < χ n
        · have hA' := hχA n (by omega) hχ
          have hnA : e n ≤ A := (hmono n (by omega)).trans hA'
          rw [min_eq_left hnA] at ihn
          rw [min_eq_left hA']
          have hI0 : 0 ≤ ∫ x in e n..e (n + 1), f x :=
            intervalIntegral.integral_nonneg (hmono n (by omega))
              fun y hy => hf0 y ((hpos n (by omega)).trans_le hy.1)
          have := intervalIntegral.integral_add_adjacent_intervals
            (hfi (e 0) (e n) he0 (hpos n (by omega)))
            (hfi (e n) (e (n + 1)) (hpos n (by omega)) (hpos (n + 1) hn))
          have : χ n * ∫ x in e n..e (n + 1), f x ≤ ∫ x in e n..e (n + 1), f x := by
            nlinarith [hχ1 n]
          linarith
        · have : χ n = 0 := le_antisymm (not_lt.mp hχ) (hχ0 n)
          rw [this, zero_mul, add_zero]
          refine ihn.trans ?_
          apply intervalIntegral.integral_mono_interval le_rfl (le_min hen h0A.le)
            (min_le_min_right _ (hmono n (by omega)))
          · exact ae_nonneg_Ioc hf0 he0
          · exact hfi _ _ he0 (lt_min (hpos (n + 1) hn) (he0.trans h0A))
    refine (key N le_rfl).trans ?_
    have hm : 0 < min (e N) A := lt_min (hpos N le_rfl) (he0.trans h0A)
    apply intervalIntegral.integral_mono_interval le_rfl
      (le_min (hle 0 N (Nat.zero_le _) le_rfl) h0A.le) (min_le_right _ _)
    · exact ae_nonneg_Ioc hf0 he0
    · exact hfi _ _ he0 (he0.trans h0A)
  · apply Finset.sum_nonpos
    intro i hi
    have hiN : i < N := by simpa using hi
    by_cases hχ : 0 < χ i
    · have hA' := hχA i hiN hχ
      have h1 : e (i + 1) ≤ e i := by
        have := hle 0 i (Nat.zero_le _) hiN.le
        linarith [not_lt.mp h0A]
      have h2 := hmono i hiN
      rw [le_antisymm h1 h2, intervalIntegral.integral_same, mul_zero]
    · rw [le_antisymm (not_lt.mp hχ) (hχ0 i), zero_mul]

/-! ## Lemma A.6 (S3)(a) -/

/-- `Eu_s` at the slot of the `i`-th realised prime of the block range (one prime per slot):
`Eu_s(a) ∏_{i' < i} (1 - 1/p_{i'})⁻¹`. -/
noncomputable def euAt (Ea : ℝ) (p : ℕ → ℝ) (i : ℕ) : ℝ := Ea * ∏ i' ∈ range i, (1 - (p i')⁻¹)⁻¹

lemma euAt_zero (Ea : ℝ) (p : ℕ → ℝ) : euAt Ea p 0 = Ea := by simp [euAt]

lemma euAt_succ (Ea : ℝ) (p : ℕ → ℝ) (i : ℕ) :
    euAt Ea p (i + 1) = euAt Ea p i / (1 - (p i)⁻¹) := by
  simp only [euAt, Finset.prod_range_succ]; ring

lemma one_sub_inv_pos {g : ℝ} (hg : 1 < g) : 0 < 1 - g⁻¹ :=
  sub_pos.mpr (inv_lt_one_of_one_lt₀ hg)

lemma euAt_pos {Ea : ℝ} (hEa : 0 < Ea) {p : ℕ → ℝ} {N : ℕ} (hp : ∀ i < N, 1 < p i) :
    ∀ i ≤ N, 0 < euAt Ea p i := by
  intro i hi
  unfold euAt
  refine mul_pos hEa (Finset.prod_pos fun i' hi' => ?_)
  exact inv_pos.mpr (one_sub_inv_pos (hp i' (by simp at hi'; omega)))

lemma euAt_le_succ {Ea : ℝ} (hEa : 0 < Ea) {p : ℕ → ℝ} {N : ℕ} (hp : ∀ i < N, 1 < p i) :
    ∀ i < N, euAt Ea p i ≤ euAt Ea p (i + 1) := by
  intro i hi
  rw [euAt_succ]
  have h0 := euAt_pos hEa hp i hi.le
  have h1 := one_sub_inv_pos (hp i hi)
  rw [le_div_iff₀ h1]
  have : 0 < (p i)⁻¹ := inv_pos.mpr (by linarith [hp i hi])
  nlinarith

/-- Decomposition of the non-empty subsets of `{0, …, N-1}` by their largest element. -/
lemma sum_nonempty_powerset (N : ℕ) (F : Finset ℕ → ℝ) :
    ∑ S ∈ (range N).powerset with S.Nonempty, F S =
      ∑ i ∈ range N, ∑ S ∈ (range i).powerset, F (insert i S) := by
  induction N with
  | zero => simp [Finset.filter_singleton]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.range_add_one, Finset.powerset_insert,
      Finset.filter_union]
    rw [Finset.sum_union]
    · congr 1
      rw [Finset.filter_true_of_mem (fun S hS => by
        obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS; exact Finset.insert_nonempty _ _)]
      rw [Finset.sum_image]
      intro S hS T hT hST
      have hNS : N ∉ S := fun h => by
        have := Finset.mem_powerset.mp (Finset.mem_coe.mp hS) h; simp at this
      have hNT : N ∉ T := fun h => by
        have := Finset.mem_powerset.mp (Finset.mem_coe.mp hT) h; simp at this
      rw [← Finset.erase_insert hNS, ← Finset.erase_insert hNT]
      exact congrArg (fun U => U.erase N) hST
    · rw [Finset.disjoint_left]
      intro S hS hS'
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hS').1
      have := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 (Finset.mem_insert_self N T)
      simp at this

/-- **Lemma A.6 (S3)(a), the block bound with variable content.** On every `ω`, the sum over
every non-empty content `S` of the block (latest prime `p (S.sup id)`, all exponent vectors
already summed: weight `(1 - 1/g)^{-K} - 1` per prime, `tsum_exponents`) of
`χ_t ∏_{g ∈ S} g^{-a_g} Φ_{t-1}(u_t)` is at most
`Φ_t(s_{t+1}) = G_t(Eu_s(s_{t+1}))/Eu_s(s_{t+1})^K`.
Here `K = K_t = m + j`, `m = K_{t-1}`, `j = j_t` (`j = 0` allowed), `Ea = Eu_s(s_{t+1})`,
`Φ_{t-1}(u) = G(Eu_s(u))/Eu_s(u)^m`, and `G_t = Gnext A K j G` is (A.Grec) with top `A = A_top`. -/
theorem block_bound {N K m j : ℕ} (hK : K = m + j) {A Ea : ℝ} (hEa : 0 < Ea)
    {p : ℕ → ℝ} (hp : ∀ i < N, 1 < p i) {χ : ℕ → ℝ} (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ 1)
    (hχA : ∀ i < N, 0 < χ i → euAt Ea p (i + 1) ≤ A)
    {G : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ G y) (hGanti : AntitoneOn G (Set.Ioi 0)) :
    ∑ S ∈ (range N).powerset with S.Nonempty,
        χ (S.sup id) * (∏ g ∈ S, ((1 - (p g)⁻¹)⁻¹ ^ K - 1)) *
          (G (euAt Ea p (S.sup id + 1)) / euAt Ea p (S.sup id + 1) ^ m) ≤
      Gnext A K j G Ea / Ea ^ K := by
  set f : ℝ → ℝ := fun y => (K : ℝ) * y ^ ((j : ℤ) - 1) * G y with hf
  have hf0 : ∀ y, 0 < y → 0 ≤ f y := fun y hy => by
    have := hG0 y hy; simp only [hf]; positivity
  rw [sum_nonempty_powerset]
  -- each latest prime `i`
  have hterm : ∀ i ∈ range N,
      ∑ S ∈ (range i).powerset, χ ((insert i S).sup id) *
          (∏ g ∈ insert i S, ((1 - (p g)⁻¹)⁻¹ ^ K - 1)) *
          (G (euAt Ea p ((insert i S).sup id + 1)) / euAt Ea p ((insert i S).sup id + 1) ^ m) ≤
        χ i / Ea ^ K * ∫ y in euAt Ea p i..euAt Ea p (i + 1), f y := by
    intro i hi
    have hiN : i < N := by simpa using hi
    have hsup : ∀ S ∈ (range i).powerset, (insert i S).sup id = i := by
      intro S hS
      rw [Finset.sup_insert]
      have : S.sup id ≤ i := Finset.sup_le fun b hb => by
        have := Finset.mem_powerset.mp hS hb; simp at this; simp; omega
      simpa using this
    have hnot : ∀ S ∈ (range i).powerset, i ∉ S := fun S hS h => by
      have := Finset.mem_powerset.mp hS h; simp at this
    rw [Finset.sum_congr rfl fun S hS => by
      rw [hsup S hS, Finset.prod_insert (hnot S hS)]]
    have hfac : ∀ S ∈ (range i).powerset,
        χ i * (((1 - (p i)⁻¹)⁻¹ ^ K - 1) * ∏ g ∈ S, ((1 - (p g)⁻¹)⁻¹ ^ K - 1)) *
          (G (euAt Ea p (i + 1)) / euAt Ea p (i + 1) ^ m) =
        (χ i * ((1 - (p i)⁻¹)⁻¹ ^ K - 1) * (G (euAt Ea p (i + 1)) / euAt Ea p (i + 1) ^ m)) *
          ∏ g ∈ S, ((1 - (p g)⁻¹)⁻¹ ^ K - 1) := fun S _ => by ring
    rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
    -- `∑_{S ⊆ [0,i)} ∏_{g∈S} w_g = ∏_{g<i} (1 + w_g) = (Eu_i/Ea)^K`
    have hprod : ∑ S ∈ (range i).powerset, ∏ g ∈ S, ((1 - (p g)⁻¹)⁻¹ ^ K - 1) =
        (euAt Ea p i / Ea) ^ K := by
      rw [← Finset.prod_one_add]
      simp only [add_sub_cancel]
      rw [euAt, mul_div_cancel_left₀ _ hEa.ne', Finset.prod_pow]
    rw [hprod]
    have hE1 := euAt_pos hEa hp i hiN.le
    have hx0 : 0 < (p i)⁻¹ := inv_pos.mpr (by linarith [hp i hiN])
    have hx1 : (p i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hp i hiN)
    have hstep := prime_step hK hE1 hx0 hx1 hG0 hGanti
    rw [← euAt_succ] at hstep
    have hEaK : 0 < Ea ^ K := pow_pos hEa K
    calc χ i * ((1 - (p i)⁻¹)⁻¹ ^ K - 1) *
          (G (euAt Ea p (i + 1)) / euAt Ea p (i + 1) ^ m) * (euAt Ea p i / Ea) ^ K
        = χ i / Ea ^ K * (euAt Ea p i ^ K * ((1 - (p i)⁻¹)⁻¹ ^ K - 1) *
            (G (euAt Ea p (i + 1)) / euAt Ea p (i + 1) ^ m)) := by
          rw [div_pow]; field_simp
      _ ≤ χ i / Ea ^ K * ∫ y in euAt Ea p i..euAt Ea p (i + 1), f y :=
          mul_le_mul_of_nonneg_left hstep (div_nonneg (hχ0 i) hEaK.le)
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum := sum_chi_integral_le (N := N) (e := euAt Ea p) (by rw [euAt_zero]; exact hEa)
    (euAt_le_succ hEa hp) hχ0 hχ1 (A := A) hχA hf0
    (fun a b ha hb => intervalIntegrable_chain hGanti ha hb)
  rw [euAt_zero] at hsum
  have hEaK : 0 < Ea ^ K := pow_pos hEa K
  calc ∑ i ∈ range N, χ i / Ea ^ K * ∫ y in euAt Ea p i..euAt Ea p (i + 1), f y
      = (∑ i ∈ range N, χ i * ∫ y in euAt Ea p i..euAt Ea p (i + 1), f y) / Ea ^ K := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ Gnext A K j G Ea / Ea ^ K := by
        apply div_le_div_of_nonneg_right _ hEaK.le
        simpa [Gnext, hf] using hsum

/-! ## Each `G_t` is non-negative and non-increasing -/

lemma Gnext_nonneg {A : ℝ} {K j : ℕ} {G : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ G y) {E : ℝ}
    (hE : 0 < E) : 0 ≤ Gnext A K j G E := by
  unfold Gnext
  split_ifs with h
  · refine intervalIntegral.integral_nonneg h.le fun y hy => ?_
    have := hG0 y (hE.trans_le hy.1)
    have : 0 < y := hE.trans_le hy.1
    positivity
  · exact le_rfl

lemma Gnext_antitone {A : ℝ} {K j : ℕ} {G : ℝ → ℝ} (hG0 : ∀ y, 0 < y → 0 ≤ G y)
    (hGanti : AntitoneOn G (Set.Ioi 0)) : AntitoneOn (Gnext A K j G) (Set.Ioi 0) := by
  intro E hE E' hE' hEE'
  by_cases h' : E' < A
  · have h : E < A := lt_of_le_of_lt hEE' h'
    simp only [Gnext, if_pos h, if_pos h']
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_chain (K := K) (j := j) hGanti (a := E) (b := E') hE hE')
      (intervalIntegrable_chain (K := K) (j := j) hGanti (a := E') (b := A) hE' (hE.trans h))
    have h0 : 0 ≤ ∫ x in E..E', (K : ℝ) * x ^ ((j : ℤ) - 1) * G x :=
      intervalIntegral.integral_nonneg hEE' fun y hy => by
        have : 0 < y := lt_of_lt_of_le hE hy.1
        have := hG0 y this
        positivity
    linarith
  · simp only [Gnext, if_neg h']
    exact Gnext_nonneg hG0 hE

/-- Each `G_t` of (A.Grec) is `≥ 0` and non-increasing on `(0,∞)` (Lemma A.6 (S3)). -/
theorem GRun_nonneg_antitone (A : ℝ) : ∀ l : List ℕ,
    (∀ E, 0 < E → 0 ≤ GRun A l E) ∧ AntitoneOn (GRun A l) (Set.Ioi 0)
  | [] => ⟨fun _ _ => zero_le_one, fun _ _ _ _ _ => le_rfl⟩
  | j :: l => by
    obtain ⟨h0, ha⟩ := GRun_nonneg_antitone A l
    rw [GRun_cons]
    exact ⟨fun E hE => Gnext_nonneg h0 hE, Gnext_antitone h0 ha⟩

/-- **Lemma A.6 (S3)(a) for the chain recursion**: the same bound with `G_{t-1} = GRun A l` and
`G_t = GRun A (j :: l)`, `K_t = j + l.sum`, `K_{t-1} = l.sum`. -/
theorem block_bound_GRun {N : ℕ} (j : ℕ) (l : List ℕ) {A Ea : ℝ} (hEa : 0 < Ea)
    {p : ℕ → ℝ} (hp : ∀ i < N, 1 < p i) {χ : ℕ → ℝ} (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ 1)
    (hχA : ∀ i < N, 0 < χ i → euAt Ea p (i + 1) ≤ A) :
    ∑ S ∈ (range N).powerset with S.Nonempty,
        χ (S.sup id) * (∏ g ∈ S, ((1 - (p g)⁻¹)⁻¹ ^ (j + l.sum) - 1)) *
          (GRun A l (euAt Ea p (S.sup id + 1)) / euAt Ea p (S.sup id + 1) ^ l.sum) ≤
      GRun A (j :: l) Ea / Ea ^ (j + l.sum) := by
  obtain ⟨h0, ha⟩ := GRun_nonneg_antitone A l
  rw [GRun_cons]
  exact block_bound (by ring) hEa hp hχ0 hχ1 hχA h0 ha

/-! ## Lemma A.6 (S3)(c): the end step -/

/-- **Lemma A.6 (S3)(c)** (the algebra of the end step). Let `Eu = Eu_rat > 0`. If the non-empty
contents of the early block contribute `S ≤ G_T(Eu)/Eu^{K_T}` (by (a) with `s_{T+1} = X₀`), the
empty content contributes `χ_T Φ_{T-1}(X₀) = χ_T G_{T-1}(Eu)/Eu^{K_{T-1}}` with `χ_T ∈ [0,1]`, and
the tails of the `K_T` chain rows contribute `∑_d 1/d = Eu` each, then the total is at most
`G_T(Eu) + Eu^{j_T} G_{T-1}(Eu)`. -/
theorem end_step {K m j : ℕ} (hK : K = m + j) {Eu S χ GT GT1 : ℝ} (hEu : 0 < Eu)
    (hS : S ≤ GT / Eu ^ K) (hχ1 : χ ≤ 1) (hG1 : 0 ≤ GT1) :
    (S + χ * (GT1 / Eu ^ m)) * Eu ^ K ≤ GT + Eu ^ j * GT1 := by
  have hEuK : 0 < Eu ^ K := pow_pos hEu K
  have h1 : S * Eu ^ K ≤ GT := by rwa [le_div_iff₀ hEuK] at hS
  have h2 : χ * (GT1 / Eu ^ m) * Eu ^ K ≤ Eu ^ j * GT1 := by
    rw [hK, pow_add]
    have : GT1 / Eu ^ m * (Eu ^ m * Eu ^ j) = Eu ^ j * GT1 := by
      field_simp
    calc χ * (GT1 / Eu ^ m) * (Eu ^ m * Eu ^ j) = χ * (Eu ^ j * GT1) := by rw [mul_assoc, this]
      _ ≤ 1 * (Eu ^ j * GT1) := mul_le_mul_of_nonneg_right hχ1 (by positivity)
      _ = Eu ^ j * GT1 := one_mul _
  nlinarith

/-! ## The chain bound of the Cover Bound (Proposition 6.19) -/

lemma filter_cons_zero (l : List ℕ) : (0 :: l).filter (· ≠ 0) = l.filter (· ≠ 0) := by
  simp

lemma filter_cons_ne {j : ℕ} (hj : j ≠ 0) (l : List ℕ) :
    (j :: l).filter (· ≠ 0) = j :: l.filter (· ≠ 0) := by
  simp [hj]

lemma sum_filter_ne_zero : ∀ l : List ℕ, (l.filter (· ≠ 0)).sum = l.sum
  | [] => rfl
  | j :: l => by
    by_cases hj : j = 0
    · subst hj; rw [filter_cons_zero, List.sum_cons, sum_filter_ne_zero l, zero_add]
    · rw [filter_cons_ne hj, List.sum_cons, List.sum_cons, sum_filter_ne_zero l]

/-- **Stages at which no row of `C` joins** (proof of Proposition 6.19): for `E ∈ [Eu, A]`,
`λ ≥ log(A/Eu)` and `K_T = l.sum ≤ κ`, each stage with `j_t = 0` costs at most a factor `κλ`:
`G_T(E) ≤ (κλ)^{#{t : j_t = 0}} G̃_T(E)`, where `G̃` is the recursion for the composition formed
by the non-zero `j_t` (with the same `K_t`). -/
theorem GRun_le_filter {A Eu lam κ : ℝ} (hA : 0 < A) (hEu : 0 < Eu)
    (hlam : Real.log (A / Eu) ≤ lam) : ∀ l : List ℕ, (l.sum : ℝ) ≤ κ →
      ∀ E ∈ Set.Icc Eu A, GRun A l E ≤ (κ * lam) ^ l.count 0 * GRun A (l.filter (· ≠ 0)) E
  | [] => by intros; simp
  | j :: l => by
    intro hsum E hE
    have hE0 : 0 < E := hEu.trans_le hE.1
    have hl : (l.sum : ℝ) ≤ κ := by
      simp only [List.sum_cons, Nat.cast_add] at hsum; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have ih := GRun_le_filter hA hEu hlam l hl
    obtain ⟨h0l, hal⟩ := GRun_nonneg_antitone A l
    obtain ⟨h0f, haf⟩ := GRun_nonneg_antitone A (l.filter (· ≠ 0))
    have hlam0 : 0 ≤ lam := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hEu]; linarith [hE.2,
      hE.1])) hlam
    have hκ0 : 0 ≤ κ := le_trans (Nat.cast_nonneg _) hl
    by_cases hj : j = 0
    · subst hj
      rw [List.count_cons_self, filter_cons_zero, pow_succ, GRun_cons]
      simp only [zero_add]
      unfold Gnext
      split_ifs with hEA
      · -- `∫_E^A K/x G(x) dx ≤ K log(A/E) G(E) ≤ κλ G(E)`
        have hint : ∫ x in E..A, ((l.sum : ℕ) : ℝ) * x ^ (((0 : ℕ) : ℤ) - 1) * GRun A l x ≤
            ∫ x in E..A, ((l.sum : ℕ) : ℝ) * x⁻¹ * GRun A l E := by
          apply intervalIntegral.integral_mono_on hEA.le
          · exact intervalIntegrable_chain hal hE0 (hE0.trans hEA)
          · refine ContinuousOn.intervalIntegrable ?_
            refine (continuousOn_const.mul (continuousOn_inv₀.mono ?_)).mul continuousOn_const
            intro y hy
            rw [Set.uIcc_of_le hEA.le] at hy
            exact ne_of_gt (hE0.trans_le hy.1)
          · intro y hy
            have hy0 : 0 < y := hE0.trans_le hy.1
            simp only [Nat.cast_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one]
            have := hal hE0 hy0 hy.1
            have : 0 ≤ ((l.sum : ℕ) : ℝ) * y⁻¹ := by positivity
            nlinarith
        have hcalc : ∫ x in E..A, ((l.sum : ℕ) : ℝ) * x⁻¹ * GRun A l E =
            (l.sum : ℝ) * Real.log (A / E) * GRun A l E := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
            integral_inv_of_pos hE0 (hE0.trans hEA)]
        have hlog : Real.log (A / E) ≤ lam := by
          refine le_trans (Real.log_le_log (div_pos hA hE0) ?_) hlam
          exact div_le_div_of_nonneg_left hA.le hEu hE.1
        have hlogE : 0 ≤ Real.log (A / E) :=
          Real.log_nonneg (by rw [le_div_iff₀ hE0]; linarith)
        have hG := h0l E hE0
        have hfac : (l.sum : ℝ) * Real.log (A / E) ≤ κ * lam :=
          mul_le_mul hl hlog hlogE hκ0
        have hih := ih E hE
        have hpow : 0 ≤ (κ * lam) ^ l.count 0 := pow_nonneg (mul_nonneg hκ0 hlam0) _
        calc _ ≤ (l.sum : ℝ) * Real.log (A / E) * GRun A l E := hint.trans hcalc.le
          _ ≤ κ * lam * GRun A l E := mul_le_mul_of_nonneg_right hfac hG
          _ ≤ κ * lam * ((κ * lam) ^ l.count 0 * GRun A (l.filter (· ≠ 0)) E) :=
              mul_le_mul_of_nonneg_left hih (mul_nonneg hκ0 hlam0)
          _ = _ := by ring
      · have := h0f E hE0
        have hpow : 0 ≤ (κ * lam) ^ l.count 0 := pow_nonneg (mul_nonneg hκ0 hlam0) _
        positivity
    · have hcount : (j :: l).count 0 = l.count 0 := by
        rw [List.count_cons]; simp [hj]
      rw [hcount, filter_cons_ne hj, GRun_cons, GRun_cons, sum_filter_ne_zero]
      unfold Gnext
      split_ifs with hEA
      · rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_mono_on hEA.le
        · exact intervalIntegrable_chain hal hE0 (hE0.trans hEA)
        · exact (intervalIntegrable_chain haf hE0 (hE0.trans hEA)).const_mul _
        · intro y hy
          have hy0 : 0 < y := hE0.trans_le hy.1
          have := ih y ⟨hE.1.trans hy.1, hy.2⟩
          have : 0 ≤ ((j + l.sum : ℕ) : ℝ) * y ^ ((j : ℤ) - 1) := by positivity
          nlinarith
      · simp

lemma GRun_le_finG {A : ℝ} : ∀ (l : List ℕ) {E : ℝ}, 0 < E → GRun A l E ≤ finG A l E
  | [], _, _ => le_rfl
  | j :: l, E, hE => by
    simp only [finG]
    have := (GRun_nonneg_antitone A l).1 E hE
    have : 0 ≤ E ^ j * GRun A l E := by positivity
    linarith

lemma finG_nonneg {A : ℝ} : ∀ (l : List ℕ) {E : ℝ}, 0 < E → 0 ≤ finG A l E
  | [], _, _ => zero_le_one
  | j :: l, E, hE => by
    simp only [finG]
    have := (GRun_nonneg_antitone A (j :: l)).1 E hE
    have := (GRun_nonneg_antitone A l).1 E hE
    positivity

/-- The end value: `Fin ≤ (1 + κλ)^{s_R} Fiñ`, with `s_R` the number of stages at which no row of
`C` joins and `Fiñ` the end value of the compressed composition (proof of Proposition 6.19). -/
theorem finG_le_zero_runs {A Eu lam κ : ℝ} (hA : 0 < A) (hEu : 0 < Eu) (hEuA : Eu ≤ A)
    (hlam : Real.log (A / Eu) ≤ lam) (l : List ℕ) (hsum : (l.sum : ℝ) ≤ κ) :
    finG A l Eu ≤ (1 + κ * lam) ^ l.count 0 * finG A (l.filter (· ≠ 0)) Eu := by
  have hlam0 : 0 ≤ lam := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hEu]; linarith)) hlam
  have hEuI : Eu ∈ Set.Icc Eu A := ⟨le_rfl, hEuA⟩
  cases l with
  | nil => simp
  | cons j l =>
    have hl : (l.sum : ℝ) ≤ κ := by
      simp only [List.sum_cons, Nat.cast_add] at hsum; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have hκ0 : 0 ≤ κ := le_trans (Nat.cast_nonneg _) hl
    have hκl : 0 ≤ κ * lam := mul_nonneg hκ0 hlam0
    have hmono : ∀ n : ℕ, (κ * lam) ^ n ≤ (1 + κ * lam) ^ n :=
      fun n => pow_le_pow_left₀ hκl (by linarith) n
    have hf0 := finG_nonneg (A := A) (l.filter (· ≠ 0)) hEu
    by_cases hj : j = 0
    · subst hj
      rw [List.count_cons_self, filter_cons_zero]
      simp only [finG, pow_zero, one_mul]
      have h1 := GRun_le_filter hA hEu hlam (0 :: l) hsum Eu hEuI
      rw [List.count_cons_self, filter_cons_zero] at h1
      have h2 := GRun_le_filter hA hEu hlam l hl Eu hEuI
      have h3 := GRun_le_finG (A := A) (l.filter (· ≠ 0)) hEu
      have hG0 := (GRun_nonneg_antitone A (l.filter (· ≠ 0))).1 Eu hEu
      have hp := hmono (l.count 0)
      have hp0 : 0 ≤ (κ * lam) ^ l.count 0 := pow_nonneg hκl _
      calc GRun A (0 :: l) Eu + GRun A l Eu
          ≤ (κ * lam) ^ (l.count 0 + 1) * GRun A (l.filter (· ≠ 0)) Eu +
              (κ * lam) ^ l.count 0 * GRun A (l.filter (· ≠ 0)) Eu := add_le_add h1 h2
        _ = (1 + κ * lam) * ((κ * lam) ^ l.count 0 * GRun A (l.filter (· ≠ 0)) Eu) := by ring
        _ ≤ (1 + κ * lam) * ((1 + κ * lam) ^ l.count 0 * finG A (l.filter (· ≠ 0)) Eu) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact mul_le_mul hp h3 hG0 (pow_nonneg (by linarith) _)
        _ = (1 + κ * lam) ^ (l.count 0 + 1) * finG A (l.filter (· ≠ 0)) Eu := by ring
    · have hcount : (j :: l).count 0 = l.count 0 := by
        rw [List.count_cons]; simp [hj]
      rw [hcount, filter_cons_ne hj]
      simp only [finG]
      have h1 := GRun_le_filter hA hEu hlam (j :: l) hsum Eu hEuI
      rw [hcount, filter_cons_ne hj] at h1
      have h2 := GRun_le_filter hA hEu hlam l hl Eu hEuI
      have hp := hmono (l.count 0)
      have hg1 := (GRun_nonneg_antitone A (j :: l.filter (· ≠ 0))).1 Eu hEu
      have hg2 := (GRun_nonneg_antitone A (l.filter (· ≠ 0))).1 Eu hEu
      have hEj : 0 ≤ Eu ^ j := by positivity
      calc GRun A (j :: l) Eu + Eu ^ j * GRun A l Eu
          ≤ (κ * lam) ^ l.count 0 * GRun A (j :: l.filter (· ≠ 0)) Eu +
              Eu ^ j * ((κ * lam) ^ l.count 0 * GRun A (l.filter (· ≠ 0)) Eu) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hEj)
        _ = (κ * lam) ^ l.count 0 * (GRun A (j :: l.filter (· ≠ 0)) Eu +
              Eu ^ j * GRun A (l.filter (· ≠ 0)) Eu) := by ring
        _ ≤ (1 + κ * lam) ^ l.count 0 * (GRun A (j :: l.filter (· ≠ 0)) Eu +
              Eu ^ j * GRun A (l.filter (· ≠ 0)) Eu) :=
            mul_le_mul_of_nonneg_right hp (by positivity)

/-- **The chain bound of Proposition 6.19 (Cover Bound)**: for a run-increment list `l` of the
cover rows (earliest run first, `j_t = 0` allowed) with `K_T = l.sum = κ ≥ 1`, top `A > 0`,
`0 < Eu = Eu_rat ≤ A` and `λ ≥ log(A/Eu)`,
`Fin = G_T(Eu) + Eu^{j_T} G_{T-1}(Eu) ≤ (1 + κλ)^{s_R} (κ^κ/κ!) A^κ`, `s_R = #{t : j_t = 0}`. -/
theorem finG_le_cover {A Eu lam : ℝ} (hA : 0 < A) (hEu : 0 < Eu) (hEuA : Eu ≤ A)
    (hlam : Real.log (A / Eu) ≤ lam) (l : List ℕ) (hκ : 1 ≤ l.sum) :
    finG A l Eu ≤ (1 + l.sum * lam) ^ l.count 0 *
      (A ^ l.sum * ((l.sum : ℝ) ^ l.sum / (l.sum).factorial)) := by
  have hlam0 : 0 ≤ lam := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hEu]; linarith)) hlam
  refine (finG_le_zero_runs hA hEu hEuA hlam l le_rfl).trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) _)
  have hmem : l.filter (· ≠ 0) ∈ comps l.sum := by
    rw [mem_comps]
    refine ⟨fun j hj => ?_, sum_filter_ne_zero l⟩
    have := (List.mem_filter.mp hj).2
    simp at this; omega
  have hsingle := Finset.single_le_sum (f := fun l' => finG A l' Eu)
    (fun l' _ => finG_nonneg l' hEu) hmem
  exact hsingle.trans (sum_comps_finG_le l.sum hκ hA hEu.le hEuA)

end RankFull
