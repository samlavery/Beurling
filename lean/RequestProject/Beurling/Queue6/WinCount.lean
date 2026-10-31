module

public import RequestProject.Beurling.Queue6.X0SHyp
public import RequestProject.Beurling.Queue6.S2E2

/-!
# Proposition 5.18, step (iii): the window count on `Good(< t)`

For `X₀²/2 < y ≤ b + H(b)` the `w`-window of `η_{X₀}(y)` (`KR.X0S.Win`: the elements `w ≥ 2`
of `P(ω)` with `|y - w X₀⁻| ≤ 1.02 H(y)`) holds at most
`4.21 H(y)/X₀ + 2 H(y/X₀) + 4 + 2 (y/X₀)^{θ'/2}` elements, for `θ ≤ θ'`, on `Good(< t)` (any
`t ≥ b`) off `NiceEvᶜ` (`winCount_G0`). The window lies in a short interval `(α, β]` of length
`< 2` at the height `≈ y/X₀`, far below the horizon of `Good(< t)`, and:

* the lag `|N - T| ≤ B(x) + B(X₀) + H(x) + H(X₀) + 5` at its ends (Corollary 3.8:
  `Landing.toSlotData_loc … .two_sided`, or `LandingInit.abs_le_loc` near `X₀`), with the queue
  bound `queue_of_G0` (`lag_G0`);
* the target increment `T(x') - T(x) ≤ 5.0001 + #(𝒜 ∩ [x, x'])` (the split `T = X₀ + J + C`:
  the `X₀`-smooth count, the absorbed count, and `contD_upper_log`) (`T_incr`);
* the absorbed count of Lemma 6.26 (`lemma626_G0`) (`LC_G0`);
* `N = ⌊·⌋` below `X₀⁻` (`realised_floor_eq`).

All terms but the absorbed one are `≤ e^{O(√log u)} ≤ u^{1/8}` (`capM1_le_sqrt`,
`queueBound75_le`), and the absorbed one is `≤ u^{θ/2}`; so the count is `≤ 2 u^{θ'/2}`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono SlotModel Absorbed

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### `Good(< t)` is decreasing in `t` -/

lemma G0_anti (D : Sec5Family) {s t : ℕ} (hst : s ≤ t) : G0 θ X₀ D t ⊆ G0 θ X₀ D s := by
  intro ω hω
  refine ⟨QC_anti _ _ hst hω.1, ?_⟩
  have h2 := hω.2
  simp only [goodBefore, mem_iInter] at h2 ⊢
  exact fun i hi => h2 i (lt_of_lt_of_le hi hst)

section Model

variable (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- **The lag at one height** on `Good(< t)` off `NiceEvᶜ` (Corollary 3.8). -/
theorem lag_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀) {x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxt : x + 26 * Real.log x + 2 < t) :
    |(PR θ X₀ ω).N x - (Mcl θ X₀ ω).T x| ≤
      queueB X₀ x + queueB X₀ X₀ + capH X₀ x + capH X₀ X₀ + 5 := by
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  have hQ := queue_of_G0 D hc hω h0 hx hxt
  have hPe : PR θ X₀ ω = realisedSystem M (capH X₀) ω := by
    show realisedSystem (Mcl θ X₀ ω) (capH X₀) (Ucl ω) = _
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  have hMe : Mcl θ X₀ ω = M := Mcl_eq_lim hc h0
  rw [hPe, hMe]
  have hB0 := queueB_nonneg hX0 hX hx
  have hB0' := queueB_nonneg hX0 hX (le_refl (X₀ : ℝ))
  have hH0 := capH_nonneg (X₀ : ℝ) x
  have hH0' := capH_nonneg (X₀ : ℝ) X₀
  have hlx : Real.log x ≠ 0 := by have := (logs_of_ge hX0 hX hx).1; linarith
  have hlX : Real.log X₀ ≠ 0 := by linarith
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · have hl := landing_of_linked L S hreg hok hx
    have h12 := (Landing.toSlotData_loc M hX hx hQ hl).two_sided
    rw [div_self hlx] at h12
    rw [abs_le]; constructor <;> linarith [h12.1, h12.2]
  · have hl := landingInit_of_linked L S hreg hok hx hearly
    have h := LandingInit.abs_le_loc M hX hx hearly hQ hl
    rw [div_self hlX] at h
    linarith

include hc in
/-- **The target increment** over `[x, x'] ⊆ [X₀, ∞)`:
`T(x') - T(x) ≤ 2.00005 (x' - x) + 1 + #(𝒜 ∩ [x, x'])`. -/
theorem T_incr (ω : JitterΩ) {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxx : x ≤ x') :
    (Mcl θ X₀ ω).T x' - (Mcl θ X₀ ω).T x ≤
      2.00005 * (x' - x) + 1 + (localCountA (absSet X₀ (DF θ X₀ ω)) x x' : ℝ) := by
  classical
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set h0 := hc.std ω
  have hMe : Mcl θ X₀ ω = h0.limModel := Mcl_eq hc ω
  have hDF : DF θ X₀ ω = DM h0.limModel (Ucl ω) := by unfold DF; rw [hMe]
  rw [hDF, hMe, h0.limModel_T_eq, h0.limModel_T_eq, targetD_split θ _ hx,
    targetD_split θ _ (hx.trans hxx)]
  set Dm := DM h0.limModel (Ucl ω)
  have hD : LocFinD Dm := locFinD_DM hX h0.hU h0.limModel
  have hA := absSet_locFin (X₀ := X₀) hD
  -- the continuous part
  have hC := contD_upper_log hc.hθ hX Dm hD hx hxx
  have hlx : 10 ^ 8 ≤ Real.log x := (logs_of_ge hX0 hX hx).1
  have hcoef : 0.02 / Real.log x ≤ 0.00005 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hC' : contD θ X₀ Dm x' - contD θ X₀ Dm x ≤ 1.00005 * (x' - x) := by
    have : (1 + 0.02 / Real.log x) * (x' - x) ≤ 1.00005 * (x' - x) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  -- the smooth count
  have hS : ((Rankin.smoothCount X₀ x' : ℕ) : ℝ) - Rankin.smoothCount X₀ x ≤ (x' - x) + 1 := by
    unfold Rankin.smoothCount
    set n := ⌊x⌋₊
    set n' := ⌊x'⌋₊
    have hnn : n ≤ n' := Nat.floor_mono hxx
    have hn' : (n' : ℝ) ≤ n + (x' - x) + 1 := by
      have h1 := Nat.floor_le (show 0 ≤ x' by linarith)
      have h2 := Nat.lt_floor_add_one x
      linarith
    have hsub : Nat.smoothNumbersUpTo n' X₀ ⊆
        Nat.smoothNumbersUpTo n X₀ ∪ Finset.Ioc n n' := by
      intro k hk
      rw [Nat.mem_smoothNumbersUpTo] at hk
      rcases le_or_gt k n with h | h
      · exact Finset.mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨h, hk.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨h, hk.1⟩)
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Nat.card_Ioc] at hc1
    have : ((Nat.smoothNumbersUpTo n' X₀).card : ℝ) ≤
        (Nat.smoothNumbersUpTo n X₀).card + ((n' - n : ℕ) : ℝ) := by exact_mod_cast hc1
    rw [Nat.cast_sub hnn] at this
    linarith
  -- the absorbed count
  have hAc : countA (absSet X₀ Dm) x' - countA (absSet X₀ Dm) x ≤
      (localCountA (absSet X₀ Dm) x x' : ℝ) := by
    unfold countA localCountA
    set A := absSet X₀ Dm
    have hsub : A ∩ Icc 1 x' ⊆ (A ∩ Icc 1 x) ∪ (A ∩ Icc x x') := by
      rintro a ⟨ha, h1, h2⟩
      rcases le_or_gt a x with h | h
      · exact Or.inl ⟨ha, h1, h⟩
      · exact Or.inr ⟨ha, h.le, h2⟩
    have hfin : ((A ∩ Icc 1 x) ∪ (A ∩ Icc x x')).Finite := by
      refine (hA x').subset fun a h => ?_
      rcases h with ⟨ha, -, h⟩ | ⟨ha, -, h⟩
      · exact ⟨ha, show a ≤ x' by linarith⟩
      · exact ⟨ha, show a ≤ x' from h⟩
    have h1 := Set.ncard_le_ncard hsub hfin
    have h2 := Set.ncard_union_le (A ∩ Icc 1 x) (A ∩ Icc x x')
    have : ((A ∩ Icc 1 x').ncard : ℝ) ≤ (A ∩ Icc 1 x).ncard + (A ∩ Icc x x').ncard := by
      exact_mod_cast h1.trans h2
    linarith
  unfold jumpD jumpPart
  linarith

end Model

/-! ### Numerics -/

lemma log_sq_le_sqrt {K : ℝ} (hK : 1 ≤ K) : Real.log K ^ 2 ≤ 16 * Real.sqrt K := by
  set z := Real.sqrt (Real.sqrt K)
  have hz1 : 1 ≤ z := by
    show 1 ≤ Real.sqrt (Real.sqrt K)
    rw [show (1 : ℝ) = Real.sqrt (Real.sqrt 1) by simp]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hK)
  have hz4 : z ^ 4 = K := by
    show Real.sqrt (Real.sqrt K) ^ 4 = K
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith)]
  have hz2 : z ^ 2 = Real.sqrt K := by
    show Real.sqrt (Real.sqrt K) ^ 2 = Real.sqrt K
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hlog : Real.log K = 4 * Real.log z := by rw [← hz4, Real.log_pow]; push_cast; ring
  have h1 : Real.log z ≤ z := by
    have := Real.log_le_sub_one_of_pos (show 0 < z by linarith); linarith
  have h0 : 0 ≤ Real.log z := Real.log_nonneg hz1
  rw [hlog, ← hz2]
  nlinarith

lemma sqrt_le_div {K : ℝ} (hK : 10 ^ 8 ≤ K) : Real.sqrt K ≤ K / 10000 := by
  have h1 : (10000 : ℝ) ≤ Real.sqrt K := by
    rw [show (10000 : ℝ) = Real.sqrt (10 ^ 8) by
      rw [show (10 : ℝ) ^ 8 = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hK
  have h2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  rw [le_div_iff₀ (by norm_num)]; nlinarith

lemma exp_le_tenth {a K : ℝ} (h : a + Real.log 10 ≤ K / 40) :
    Real.exp a ≤ Real.exp (K / 40) / 10 := by
  rw [le_div_iff₀ (by norm_num)]
  have : Real.exp a * 10 = Real.exp (a + Real.log 10) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [this]; exact Real.exp_le_exp.mpr h

lemma log10_le : Real.log 10 ≤ 2.31 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.31 by norm_num)
  have h2 : Real.exp 2.31 = Real.exp 2 * Real.exp 0.31 := by rw [← Real.exp_add]; norm_num
  have h7 : (7.389 : ℝ) ≤ Real.exp 2 := by rw [e2]; nlinarith
  nlinarith

/-- `max(e^{8 (log K)²}, 4 e^{2√K}) ≤ e^{K/40}/10` for `K ≥ 10⁸`. -/
lemma capBound_le {K : ℝ} (hK : 10 ^ 8 ≤ K) :
    max (Real.exp (8 * Real.log K ^ 2)) (4 * Real.exp (2 * Real.sqrt K)) ≤
      Real.exp (K / 40) / 10 := by
  have hs := sqrt_le_div hK
  have hl := log_sq_le_sqrt (show (1 : ℝ) ≤ K by linarith)
  have h10 := log10_le
  refine max_le (exp_le_tenth (by nlinarith)) ?_
  have e : 4 * Real.exp (2 * Real.sqrt K) = Real.exp (2 * Real.sqrt K + Real.log 4) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
  rw [e]
  have h4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  exact exp_le_tenth (by linarith)

/-- `68 e^{√K} (K + 1.4)² ≤ e^{K/40}/10` for `K ≥ 10⁸`. -/
lemma queueBound_le {K : ℝ} (hK : 10 ^ 8 ≤ K) :
    68 * Real.exp (Real.sqrt K) * (K + 1.4) ^ 2 ≤ Real.exp (K / 40) / 10 := by
  have hs := sqrt_le_div hK
  have h10 := log10_le
  have hK0 : 0 < K + 1.4 := by linarith
  have hl : Real.log (K + 1.4) ≤ 0.7 + 4 * Real.sqrt K := by
    have h1 : Real.log (K + 1.4) ≤ Real.log (2 * K) := Real.log_le_log hK0 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 := log_sq_le_sqrt (show (1 : ℝ) ≤ K by linarith)
    have h3 : Real.log K ≤ 4 * Real.sqrt K := by
      have hs1 : 1 ≤ Real.sqrt K := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
      have h0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
      nlinarith
    linarith [Real.log_two_lt_d9]
  have e : 68 * Real.exp (Real.sqrt K) * (K + 1.4) ^ 2 =
      Real.exp (Real.sqrt K + Real.log 68 + 2 * Real.log (K + 1.4)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
      show 2 * Real.log (K + 1.4) = Real.log ((K + 1.4) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
    ring
  rw [e]
  have h68 : Real.log 68 ≤ 4.3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
    have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.3 by norm_num)
    have h2 : Real.exp 4.3 = Real.exp 4 * Real.exp 0.3 := by rw [← Real.exp_add]; norm_num
    have h54 : (54 : ℝ) ≤ Real.exp 4 := by rw [e4]; nlinarith
    nlinarith
  exact exp_le_tenth (by linarith)

/-! ### Sizes of `H` and `B` -/

section Sizes

variable (hc : Cond θ X₀)
include hc

lemma capH_le_K {z K : ℝ} (hz : (X₀ : ℝ) ≤ z) (hK : Real.log z ≤ K) :
    capH X₀ z ≤ max (Real.exp (8 * Real.log K ^ 2)) (4 * Real.exp (2 * Real.sqrt K)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hlz, -, hll⟩ := logs_of_ge hX0 hc.hX hz
  have hM := capM1_le_sqrt hX0 hc.hX hz
  have hM0 : 0 ≤ capM1 X₀ z := by linarith [QueueBound.one_le_capM1 hX0 hc.hX hz]
  unfold capH
  refine max_le_max ?_ ?_
  · apply Real.exp_le_exp.mpr
    have h1 : Real.log (Real.log z) ≤ Real.log K := Real.log_le_log (by linarith) hK
    have : Real.log (Real.log z) ^ 2 ≤ Real.log K ^ 2 := pow_le_pow_left₀ hll.le h1 2
    linarith
  · have h1 : capM1 X₀ z ^ 2 ≤ (2 * Real.exp (Real.sqrt (Real.log z))) ^ 2 :=
      pow_le_pow_left₀ hM0 hM 2
    have h2 : (2 * Real.exp (Real.sqrt (Real.log z))) ^ 2 =
        4 * Real.exp (2 * Real.sqrt (Real.log z)) := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    have h3 : Real.sqrt (Real.log z) ≤ Real.sqrt K := Real.sqrt_le_sqrt hK
    have h4 := Real.exp_le_exp.mpr (show 2 * Real.sqrt (Real.log z) ≤ 2 * Real.sqrt K by
      linarith)
    linarith

lemma queueB_le_K {z K : ℝ} (hz : (X₀ : ℝ) ≤ z) (hK : Real.log z ≤ K) :
    queueB X₀ z ≤ 68 * Real.exp (Real.sqrt K) * (K + 1.4) ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hlz := (logs_of_ge hX0 hc.hX hz).1
  have hM := capM1_le_sqrt hX0 hc.hX hz
  have hM1 := QueueBound.one_le_capM1 hX0 hc.hX hz
  obtain ⟨hq1, hq2, hq3⟩ := Lq_bounds hX0 hc.hX hz
  have hLq : 10 ^ 8 ≤ Real.log (2 * z + 12 * Real.log z + 2) := by
    unfold Lq at hq1; linarith
  have hB := (QueueBound.queueBound75_le hM1 hLq hc.hX)
  unfold queueB
  refine (hB.1.trans hB.2).trans ?_
  have hLqK : Real.log (2 * z + 12 * Real.log z + 2) ≤ K + 1.4 := by
    unfold Lq at hq2; linarith
  have hLq0 : 0 ≤ Real.log (2 * z + 12 * Real.log z + 2) := by linarith
  have h1 : Real.log (2 * z + 12 * Real.log z + 2) ^ 2 ≤ (K + 1.4) ^ 2 :=
    pow_le_pow_left₀ hLq0 hLqK 2
  have h2 : capM1 X₀ z ≤ 2 * Real.exp (Real.sqrt K) :=
    hM.trans (by gcongr)
  have hM0 : 0 ≤ capM1 X₀ z := by linarith
  calc 34 * capM1 X₀ z * Real.log (2 * z + 12 * Real.log z + 2) ^ 2
      ≤ 34 * (2 * Real.exp (Real.sqrt K)) * (K + 1.4) ^ 2 := by gcongr
    _ = 68 * Real.exp (Real.sqrt K) * (K + 1.4) ^ 2 := by ring

end Sizes

/-! ### Lemma 6.26, the floor, and the window -/

section Count

variable (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- **Lemma 6.26 on `Good(< t)`** for a window `[x, x']`, `x' ≤ x + x^{θ/2}`, `2x + 2X₀ + 4 ≤ t`. -/
theorem LC_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀) {x x' : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hxx : x' ≤ x + x ^ (thetaB θ)) (ht : 2 * x + 2 * X₀ + 4 ≤ t) :
    (localCountA (absSet X₀ (DF θ X₀ ω)) x x' : ℝ) ≤ x ^ (thetaB θ) * Real.log x ^ (-4 : ℤ) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hex : ∃ n, 2 ≤ n ∧ x + 1 ≤ 2 ^ n * (X₀ : ℝ) / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((x + 1) * 2 / X₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n + 2, by omega, ?_⟩
    rw [div_lt_iff₀ hX0p] at hn
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  set n₀ := Nat.find hex
  obtain ⟨hn2, hn⟩ := Nat.find_spec hex
  have hup : 2 ^ n₀ * (X₀ : ℝ) / 2 ≤ 2 * x + 2 * X₀ + 2 := by
    rcases Nat.lt_or_ge 2 n₀ with h3 | h3
    · have hmin := Nat.find_min hex (show n₀ - 1 < n₀ by omega)
      push_neg at hmin
      have hlt := hmin (by omega)
      have e : (2 : ℝ) ^ n₀ = 2 * 2 ^ (n₀ - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e]; nlinarith
    · have : n₀ = 2 := le_antisymm h3 hn2
      rw [this]; norm_num; nlinarith
  have htt : ttB X₀ n₀ ≤ t := by
    unfold ttB
    have h1 : (⌈2 ^ n₀ * (X₀ : ℝ) / 2⌉₊ : ℝ) < 2 ^ n₀ * (X₀ : ℝ) / 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have : ((⌈2 ^ n₀ * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) ≤ t := by push_cast; linarith
    exact_mod_cast this
  have hω' := G0_anti D htt hω
  have h := lemma626_G0 D hc hev hn2 hω' hN hn hx (by linarith : x < x + 1)
  refine le_trans ?_ h
  have hU : ∀ j, Ucl ω j ∈ Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  have hA := absSet_locFin (X₀ := X₀) (locFinD_DM hc.hX hU (Mcl θ X₀ ω))
  unfold localCountA
  have hsub : absSet X₀ (DF θ X₀ ω) ∩ Icc x x' ⊆
      absSet X₀ (DF θ X₀ ω) ∩ Icc x (x + x ^ (thetaB θ)) :=
    Set.inter_subset_inter_right _ (Set.Icc_subset_Icc le_rfl hxx)
  have hfin : (absSet X₀ (DF θ X₀ ω) ∩ Icc x (x + x ^ (thetaB θ))).Finite :=
    (hA (x + x ^ (thetaB θ))).subset fun a ha => ⟨ha.1, ha.2.2⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

include hc in
/-- **`N = ⌊·⌋` below `X₀⁻`**: `N(w) ≥ min(w, X₀⁻ - 1/2) - 1` for `w ≥ 1`. -/
lemma N_low (ω : JitterΩ) {w : ℝ} (hw : 1 ≤ w) :
    min w (Xm X₀ - 1 / 2) - 1 ≤ (PR θ X₀ ω).N w := by
  have hstd := hc.std ω
  have hU : ∀ j, Ucl ω j ∈ Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  have hTlow : ∀ x : ℝ, x < X₀ → (Mcl θ X₀ ω).T x = ⌊x⌋₊ := by
    rw [Mcl_eq hc]; exact hstd.limModel_low
  have hXm := Xm_pos hc
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hXm2 : (X₀ : ℝ) / 2 ≤ Xm X₀ := by
    have h1 := InitialRange.capH_le_rpow hX0 hc.hX le_rfl
    have h4 := four_capH_le hX0 hc.hX le_rfl
    unfold Xm; linarith
  have h16 := X₀_ge_two_pow hc.hX
  set v := min w (Xm X₀ - 1 / 2)
  have hv1 : 1 ≤ v := le_min hw (by linarith)
  have hvX : v < (X₀ : ℝ) - capH X₀ X₀ / 2 := by
    have : v ≤ Xm X₀ - 1 / 2 := min_le_right _ _
    unfold Xm at this; linarith
  have hfl := realised_floor_eq (hokR hc ω) hU hc.hX hTlow hv1 hvX
  have hmono : (PR θ X₀ ω).N v ≤ (PR θ X₀ ω).N w :=
    BeurlingSystem.N_mono _ (min_le_left _ _)
  have h1 : (v : ℝ) - 1 ≤ ⌊v⌋₊ := by
    have := Nat.lt_floor_add_one v; linarith
  show v - 1 ≤ (PR θ X₀ ω).N w
  rw [show (PR θ X₀ ω).N v = _ from hfl] at hmono
  linarith

/-- **The window in a short interval**: `#Win(y) ≤ N(β) - N(α')` for
`α' < (y - 1.02H(y))/X₀⁻`, `β = (y + 1.02H(y))/X₀⁻`. -/
lemma win_card_le (P : BeurlingSystem) (H : ℝ → ℝ) {X0m y α' : ℝ} (hXm : 0 < X0m)
    (hα : α' < (y - 1.02 * H y) / X0m) (hαβ : α' ≤ (y + 1.02 * H y) / X0m) :
    ((KR.X0S.Win P H X0m y).card : ℝ) ≤ P.N ((y + 1.02 * H y) / X0m) - P.N α' := by
  classical
  set β := (y + 1.02 * H y) / X0m
  set S := (P.elems β).filter (fun e => α' < P.val e)
  have hsub : KR.X0S.Win P H X0m y ⊆ S.image BeurlingSystem.iota := by
    intro m hm
    unfold KR.X0S.Win KR.CofH at hm
    simp only [Finset.mem_filter, Finset.mem_image] at hm
    obtain ⟨⟨⟨e, he, rfl⟩, -⟩, hw⟩ := hm
    have hV : KR.Vl P (BeurlingSystem.iota e) = P.val e := P.valN_iota e
    rw [hV, abs_le] at hw
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rw [Finset.mem_filter, BeurlingSystem.mem_elems]
    constructor
    · rw [le_div_iff₀ hXm]; linarith
    · have : (y - 1.02 * H y) / X0m ≤ P.val e := by rw [div_le_iff₀ hXm]; linarith
      linarith
  have h1 : (KR.X0S.Win P H X0m y).card ≤ S.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hs : P.elems α' ⊆ P.elems β := P.elems_mono hαβ
  have h2 : S ⊆ P.elems β \ P.elems α' := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_sdiff, BeurlingSystem.mem_elems, BeurlingSystem.mem_elems]
    exact ⟨(BeurlingSystem.mem_elems P).mp he.1, by linarith [he.2]⟩
  rw [P.N_eq_card, P.N_eq_card]
  have h3 := Finset.card_sdiff_of_subset hs
  have h5 : ((P.elems β \ P.elems α').card : ℝ) = (P.elems β).card - (P.elems α').card := by
    rw [h3, Nat.cast_sub (Finset.card_le_card hs)]
  have : ((KR.X0S.Win P H X0m y).card : ℝ) ≤ ((P.elems β \ P.elems α').card : ℝ) := by
    exact_mod_cast h1.trans (Finset.card_le_card h2)
  linarith

end Count

/-- `y^{1/8} ≤ y/10⁷` for `y ≥ 10⁸`. -/
lemma rpow_eighth_le {y : ℝ} (hy : 10 ^ 8 ≤ y) : y ^ (1 / 8 : ℝ) ≤ y / 10 ^ 7 := by
  have hy0 : 0 ≤ y := by linarith
  have hsq : y ^ (1 / 8 : ℝ) * y ^ (7 / 8 : ℝ) = y := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h78 : (10 : ℝ) ^ 7 ≤ y ^ (7 / 8 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hy (show (0 : ℝ) ≤ 7 / 8 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at this
    norm_num at this ⊢; linarith
  have hp : 0 ≤ y ^ (1 / 8 : ℝ) := by positivity
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- `capH X₀ x ≤ x/10⁷` for `x ≥ X₀`. -/
lemma capH_le_div {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    capH X₀ x ≤ x / 10 ^ 7 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h1 := InitialRange.capH_le_rpow hX0 hX hx
  have hXb : (10 : ℝ) ^ 8 ≤ X₀ := by
    have hX1 := one_lt_of_logX hX0 hX
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X₀)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  exact h1.trans (rpow_eighth_le (by linarith))

/-- `x^{1/8} ≥ e^{(log v)/8}` for `x ≥ v > 0`. -/
lemma rpow_eighth_ge {x v : ℝ} (hv : 0 < v) (hxv : v ≤ x) :
    Real.exp (Real.log v / 8) ≤ x ^ (1 / 8 : ℝ) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have := Real.log_le_log hv hxv
  linarith


section Main

variable (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)

include hc in
/-- `N(w) ≤ w` below `X₀⁻`. -/
lemma N_high (ω : JitterΩ) {w : ℝ} (hw : 1 ≤ w) (hwX : w < Xm X₀) : (PR θ X₀ ω).N w ≤ w := by
  have hstd := hc.std ω
  have hU : ∀ j, Ucl ω j ∈ Icc (0 : ℝ) 1 := fun j => clamp01_mem _
  have hTlow : ∀ x : ℝ, x < X₀ → (Mcl θ X₀ ω).T x = ⌊x⌋₊ := by
    rw [Mcl_eq hc]; exact hstd.limModel_low
  have hvX : w < (X₀ : ℝ) - capH X₀ X₀ / 2 := by unfold Xm at hwX; linarith
  have hfl := realised_floor_eq (hokR hc ω) hU hc.hX hTlow hw hvX
  show (PR θ X₀ ω).N w ≤ w
  rw [show (PR θ X₀ ω).N w = _ from hfl]
  exact Nat.floor_le (by linarith)

include hc in
/-- The lag terms at a height `x ∈ [X₀, e^{L+1}]`. -/
lemma lagBound_le {x L : ℝ} (hx : (X₀ : ℝ) ≤ x) (hxL : Real.log x ≤ L + 1)
    (hXL : Real.log X₀ ≤ L + 1) (hL : 10 ^ 8 - 1 ≤ L) :
    queueB X₀ x + queueB X₀ X₀ + capH X₀ x + capH X₀ X₀ + 5 ≤
      0.4 * Real.exp ((L + 1) / 40) + 5 := by
  have hK : 10 ^ 8 ≤ L + 1 := by linarith
  have h1 := (queueB_le_K hc hx hxL).trans (queueBound_le hK)
  have h2 := (queueB_le_K hc (le_refl (X₀ : ℝ)) hXL).trans (queueBound_le hK)
  have h3 := (capH_le_K hc hx hxL).trans (capBound_le hK)
  have h4 := (capH_le_K hc (le_refl (X₀ : ℝ)) hXL).trans (capBound_le hK)
  linarith

/-- The geometry of the window: `α' = (y - 1.02H)/X₀⁻ - 1/2`, `β = (y + 1.02H)/X₀⁻`. -/
lemma win_geom {X0 Xm Hy y u : ℝ} (hX0 : 10 ^ 8 ≤ X0) (hXmlo : 0.99 * X0 ≤ Xm)
    (hXmhi : Xm ≤ X0) (huy : u * X0 = y) (hu : 100 ≤ u) (hHy0 : 0 ≤ Hy)
    (hHyy : Hy ≤ y / 10 ^ 7) :
    0.99 * u ≤ (y - 1.02 * Hy) / Xm - 1 / 2 ∧ (y + 1.02 * Hy) / Xm ≤ 2 * u ∧
      (y - 1.02 * Hy) / Xm - 1 / 2 < (y - 1.02 * Hy) / Xm ∧
      (y - 1.02 * Hy) / Xm - 1 / 2 ≤ (y + 1.02 * Hy) / Xm ∧
      (y + 1.02 * Hy) / Xm - ((y - 1.02 * Hy) / Xm - 1 / 2) = 2.04 * Hy / Xm + 1 / 2 := by
  have hXmp : 0 < Xm := by linarith
  have hX0p : 0 < X0 := by linarith
  have hy0 : 0 ≤ y := by rw [← huy]; positivity
  have hux : 0.99 * (u * X0) ≤ u * Xm := by nlinarith
  refine ⟨?_, ?_, by linarith, ?_, by field_simp; ring⟩
  · have h1 : 0.998 * u ≤ (y - 1.02 * Hy) / Xm := by
      rw [le_div_iff₀ hXmp]
      have : u * Xm ≤ u * X0 := by nlinarith
      nlinarith
    linarith
  · rw [div_le_iff₀ hXmp]; nlinarith
  · have : (y - 1.02 * Hy) / Xm ≤ (y + 1.02 * Hy) / Xm :=
      div_le_div_of_nonneg_right (by linarith) hXmp.le
    linarith

/-- `max(e^{8 (log K)²}, 4 e^{2√K}) ≤ e^{K/50}/10` for `K ≥ 10⁸`. -/
lemma capBound_le100 {K : ℝ} (hK : 10 ^ 8 ≤ K) :
    max (Real.exp (8 * Real.log K ^ 2)) (4 * Real.exp (2 * Real.sqrt K)) ≤
      Real.exp (K / 50) / 10 := by
  have hs := sqrt_le_div hK
  have hl := log_sq_le_sqrt (show (1 : ℝ) ≤ K by linarith)
  have h10 := log10_le
  have key : ∀ a : ℝ, a + Real.log 10 ≤ K / 50 → Real.exp a ≤ Real.exp (K / 50) / 10 := by
    intro a h
    rw [le_div_iff₀ (by norm_num)]
    have : Real.exp a * 10 = Real.exp (a + Real.log 10) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    rw [this]; exact Real.exp_le_exp.mpr h
  refine max_le (key _ (by nlinarith)) ?_
  have e : 4 * Real.exp (2 * Real.sqrt K) = Real.exp (2 * Real.sqrt K + Real.log 4) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
  rw [e]
  have h4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  exact key _ (by linarith)

/-- `2.04 H/X₀⁻ + 1/2 ≤ e^{(L - 0.02)/20}` for `H ≤ e^{(2L+1)/50}/10`. -/
lemma win_len {X0 Xm Hy L : ℝ} (hX0 : 10 ^ 8 ≤ X0) (hXmlo : 0.99 * X0 ≤ Xm) (hHy0 : 0 ≤ Hy)
    (hHyb : Hy ≤ Real.exp ((2 * L + 1) / 50) / 10) (hL : 10 ^ 8 - 1 ≤ L) :
    2.04 * Hy / Xm + 1 / 2 ≤ Real.exp ((L - 0.02) / 20) := by
  have hXmp : 0 < Xm := by linarith
  have h1 : 2.04 * Hy / Xm ≤ Real.exp ((2 * L + 1) / 50) := by
    rw [div_le_iff₀ hXmp]
    have he := Real.exp_pos ((2 * L + 1) / 50)
    nlinarith
  have h4 : Real.exp ((2 * L + 1) / 50) * 2 ≤ Real.exp ((L - 0.02) / 20) := by
    rw [show (L - 0.02) / 20 = (2 * L + 1) / 50 + ((L - 0.02) / 20 - (2 * L + 1) / 50) by ring,
      Real.exp_add]
    have : (2 : ℝ) ≤ Real.exp ((L - 0.02) / 20 - (2 * L + 1) / 50) := by
      have := Real.add_one_le_exp ((L - 0.02) / 20 - (2 * L + 1) / 50)
      linarith
    have he := Real.exp_pos ((2 * L + 1) / 50)
    nlinarith
  have h5 : (1 : ℝ) ≤ Real.exp ((2 * L + 1) / 50) := Real.one_le_exp (by linarith)
  linarith

/-- `e^{(L - 0.02)/20} ≤ x^{θ_b}` for `x ≥ 0.99 e^L`, `θ ≥ 1/20`. -/
lemma win_base {u x θ : ℝ} (hu : 1 ≤ u) (hθ : 1 / 20 ≤ θ) (hx : 0.99 * u ≤ x) (hx1 : 1 ≤ x) :
    Real.exp ((Real.log u - 0.02) / 20) ≤ x ^ (thetaB θ) := by
  have hu0 : 0 < u := by linarith
  have h3 : Real.exp (Real.log (0.99 * u) / 20) ≤ x ^ (1 / 20 : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have := Real.log_le_log (by positivity) hx
    linarith
  have h4 : x ^ (1 / 20 : ℝ) ≤ x ^ (thetaB θ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (thetaB_ge hθ)
  have h5 : (Real.log u - 0.02) / 20 ≤ Real.log (0.99 * u) / 20 := by
    rw [Real.log_mul (by norm_num) hu0.ne']
    have : -0.02 ≤ Real.log 0.99 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h6 : Real.exp (-0.02) ≤ 1 / (1 + 0.02) := by
        rw [Real.exp_neg, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have := Real.add_one_le_exp (0.02 : ℝ); linarith
      linarith
    linarith
  have h6 := Real.exp_le_exp.mpr h5
  linarith

/-- `0.9 e^{(L+1)/40} + 20 ≤ u^{θ'_b}` for `L = log u ≥ 10⁸ - 1`, `θ' ≥ 1/20`. -/
lemma win_small {u θo : ℝ} (hu : 1 ≤ u) (hθo : 1 / 20 ≤ θo) (hL : 10 ^ 8 - 1 ≤ Real.log u) :
    0.9 * Real.exp ((Real.log u + 1) / 40) + 20 ≤ u ^ (thetaB θo) := by
  have hu0 : 0 < u := by linarith
  set L := Real.log u
  have h1 : u ^ (1 / 20 : ℝ) ≤ u ^ (thetaB θo) :=
    Real.rpow_le_rpow_of_exponent_le hu (thetaB_ge hθo)
  have h2 : Real.exp (L / 20) = u ^ (1 / 20 : ℝ) := by
    rw [Real.rpow_def_of_pos hu0]; congr 1; ring
  have h3 : 0.9 * Real.exp ((L + 1) / 40) + 20 ≤ Real.exp (L / 20) := by
    rw [show L / 20 = (L + 1) / 40 + (L / 20 - (L + 1) / 40) by ring, Real.exp_add]
    have : (21 : ℝ) ≤ Real.exp (L / 20 - (L + 1) / 40) := by
      have := Real.add_one_le_exp (L / 20 - (L + 1) / 40); linarith
    have he := Real.exp_pos ((L + 1) / 40)
    have h5 : (1 : ℝ) ≤ Real.exp ((L + 1) / 40) := Real.one_le_exp (by linarith)
    nlinarith
  linarith

/-- `x^{θ_b} (log x)^{-4} ≤ u^{θ'_b}` for `x ≤ 2u`, `log x ≥ 10⁸`, `θ ≤ θ'`. -/
lemma win_LC {u x θ θo : ℝ} (hu : 1 ≤ u) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθo : θ ≤ θo)
    (hx2 : x ≤ 2 * u) (hx0 : 0 ≤ x) (hlx : 10 ^ 8 ≤ Real.log x) :
    x ^ (thetaB θ) * Real.log x ^ (-4 : ℤ) ≤ u ^ (thetaB θo) := by
  have hu0 : 0 < u := by linarith
  have hl4 : Real.log x ^ (-4 : ℤ) ≤ 1 / 2 := by
    rw [zpow_neg, zpow_ofNat]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have : (10 : ℝ) ^ 8 ≤ Real.log x ^ 4 := hlx.trans (le_self_pow₀ (by linarith) (by norm_num))
    linarith
  have hx2u : x ^ (thetaB θ) ≤ (2 * u) ^ (thetaB θ) :=
    Real.rpow_le_rpow hx0 hx2 (thetaB_nonneg hθ)
  have h2u : (2 * u) ^ (thetaB θ) = 2 ^ (thetaB θ) * u ^ (thetaB θ) := Real.mul_rpow (by norm_num) hu0.le
  have h22 : (2 : ℝ) ^ (thetaB θ) ≤ 2 := by
    calc (2 : ℝ) ^ (thetaB θ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (thetaB_le_one (by linarith))
      _ = 2 := Real.rpow_one 2
  have huθ : u ^ (thetaB θ) ≤ u ^ (thetaB θo) :=
    Real.rpow_le_rpow_of_exponent_le hu (thetaB_mono hθo)
  have hp0 : 0 ≤ x ^ (thetaB θ) := by positivity
  have hpu : 0 ≤ u ^ (thetaB θ) := by positivity
  calc x ^ (thetaB θ) * Real.log x ^ (-4 : ℤ) ≤ x ^ (thetaB θ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hl4 hp0
    _ ≤ (2 * u) ^ (thetaB θ) * (1 / 2) := by gcongr
    _ = 2 ^ (thetaB θ) * u ^ (thetaB θ) / 2 := by rw [h2u]; ring
    _ ≤ 2 * u ^ (thetaB θ) / 2 := by gcongr
    _ = u ^ (thetaB θ) := by ring
    _ ≤ u ^ (thetaB θo) := huθ

/-- The time `t ≥ b` is beyond the heights `x ≤ 2u` (`u = y/X₀`, `y ≤ 1.0000001 b`). -/
lemma win_time {X0 u b t x : ℝ} (hX0 : 10 ^ 8 ≤ X0) (hub : u * X0 ≤ 1.0000001 * b)
    (hXu : X0 ≤ 2 * u) (hbt : b ≤ t) (hx1 : 1 ≤ x) (hx2 : x ≤ 2 * u) :
    x + 26 * Real.log x + 2 < t ∧ 2 * x + 2 * X0 + 4 ≤ t := by
  have hlx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < x by linarith); linarith
  have hu0 : 0 ≤ u := by linarith
  have hX2 : X0 * X0 ≤ 2.0000002 * b := by nlinarith
  have hu2 : u * 10 ^ 8 ≤ 1.0000001 * b := by nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
include hc hev in
/-- **Proposition 5.18, step (iii), the window count on `Good(< t)`**: for `t ≥ b`,
`θ ≤ θ'`, and `X₀²/2 < y ≤ b + H(b)`, off `NiceEvᶜ`,
`#Win(y) ≤ 4.21 H(y)/X₀ + 2H(y/X₀) + 4 + 2(y/X₀)^{θ'/2}`. -/
theorem winCount_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {b : ℝ} (hbt : b ≤ t) {θo : ℝ} (hθo : θ ≤ θo) {y : ℝ} (hy1 : (X₀ : ℝ) ^ 2 / 2 < y)
    (hy2 : y ≤ b + Hc X₀ b) :
    ((KR.X0S.Win (PR θ X₀ ω) (Hc X₀) (Xm X₀) y).card : ℝ) ≤
      4.21 * Hc X₀ y / X₀ + 2 * Hc X₀ (y / X₀) + 4 + 2 * (y / X₀) ^ (thetaB θo) := by
  classical
  obtain ⟨hθ1, hθ2⟩ := hc.hθ
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXb := X0_ge_1e8 hc
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hX le_rfl
  have hHX0 := capH_nonneg (X₀ : ℝ) X₀
  have hXme : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
  have hXmlo : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by rw [hXme]; linarith
  have hXmhi : Xm X₀ ≤ X₀ := by rw [hXme]; linarith
  have hXmp : 0 < Xm X₀ := by linarith
  have hXX : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 2 / 2 := by nlinarith
  have hyX : (X₀ : ℝ) ≤ y := by linarith
  have hHy : Hc X₀ y = capH X₀ y := by unfold Hc; rw [max_eq_left hyX]
  have hHy0 : 0 ≤ Hc X₀ y := by rw [hHy]; exact capH_nonneg _ _
  have hHyy : Hc X₀ y ≤ y / 10 ^ 7 := by rw [hHy]; exact capH_le_div hX hyX
  -- `u = y/X₀`, `L = log u`
  set u := y / (X₀ : ℝ) with hudef
  have huy : u * X₀ = y := by rw [hudef]; field_simp
  have hu : (X₀ : ℝ) / 2 ≤ u := by rw [hudef, le_div_iff₀ hX0p]; nlinarith
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hl2 := Real.log_two_lt_d9
  have hLX : Real.log X₀ - 0.7 ≤ Real.log u := by
    have h1 := Real.log_le_log (by positivity) hu
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith
  have hL8 : 10 ^ 8 - 1 ≤ Real.log u := by linarith
  have hXL : Real.log X₀ ≤ Real.log u + 1 := by linarith
  have hlogy : Real.log y ≤ 2 * Real.log u + 1 := by
    rw [← huy, Real.log_mul hu0.ne' hX0p.ne']; linarith
  -- the window
  obtain ⟨hαu, hβu, hα'α, hαβ, hℓe⟩ :=
    win_geom hXb hXmlo hXmhi huy (by linarith) hHy0 hHyy
  set α' := (y - 1.02 * Hc X₀ y) / Xm X₀ - 1 / 2 with hα'def
  set β := (y + 1.02 * Hc X₀ y) / Xm X₀ with hβdef
  have hα'1 : 1 ≤ α' := by linarith
  have hHyb' : Hc X₀ y ≤ Real.exp ((2 * Real.log u + 1) / 50) / 10 := by
    rw [hHy]; exact (capH_le_K hc hyX hlogy).trans (capBound_le100 (by linarith))
  have hℓ : β - α' ≤ Real.exp ((Real.log u - 0.02) / 20) := by
    rw [hℓe]; exact win_len hXb hXmlo hHy0 hHyb' hL8
  -- `b ≥ X₀`, `y ≤ 1.0000001 b`
  have hbX : (X₀ : ℝ) ≤ b := by
    by_contra hlt
    push_neg at hlt
    have : Hc X₀ b = capH X₀ X₀ := by unfold Hc; rw [max_eq_right hlt.le]
    rw [this] at hy2
    nlinarith
  have hHb : Hc X₀ b ≤ b / 10 ^ 7 := by
    unfold Hc; rw [max_eq_left hbX]; exact capH_le_div hX hbX
  have hub : u * X₀ ≤ 1.0000001 * b := by rw [huy]; linarith
  have hbig : ∀ x : ℝ, 1 ≤ x → x ≤ 2 * u →
      x + 26 * Real.log x + 2 < t ∧ 2 * x + 2 * X₀ + 4 ≤ t := fun x hx1 hx2 =>
    win_time hXb hub (by linarith) hbt hx1 hx2
  -- the lag terms
  have hlagb : ∀ x : ℝ, (X₀ : ℝ) ≤ x → x ≤ 2 * u →
      |(PR θ X₀ ω).N x - (Mcl θ X₀ ω).T x| ≤
        0.4 * Real.exp ((Real.log u + 1) / 40) + 5 := by
    intro x hx1 hx2
    have h := lag_G0 D hc hev hω hN hx1 (hbig x (by linarith) hx2).1
    have hlx : Real.log x ≤ Real.log u + 1 := by
      have := Real.log_le_log (by linarith) hx2
      rw [Real.log_mul (by norm_num) hu0.ne'] at this
      linarith
    exact h.trans (lagBound_le hc hx1 hlx hXL hL8)
  -- the absorbed count
  have hLCb : ∀ x x' : ℝ, 0.99 * u ≤ x → (X₀ : ℝ) ≤ x → x ≤ 2 * u → x' ≤ x + (β - α') →
      (localCountA (absSet X₀ (DF θ X₀ ω)) x x' : ℝ) ≤ u ^ (thetaB θo) := by
    intro x x' h1 h2 h3 h4
    have hx1 : (1 : ℝ) ≤ x := by linarith only [h2, hX1]
    have h5 := win_base hu1 hθ1 h1 hx1
    have hxx : x' ≤ x + x ^ (thetaB θ) := by linarith only [h4, hℓ, h5]
    have h := LC_G0 D hc hev hω hN h2 hxx (hbig x hx1 h3).2
    exact h.trans (win_LC hu1 (by linarith only [hθ1]) (by linarith only [hθ2]) hθo h3
      (by linarith only [hx1]) (logs_of_ge hX0 hX h2).1)
  have hsmall := win_small (θo := θo) hu1 (by linarith only [hθ1, hθo]) hL8
  have hHX40 : capH X₀ X₀ ≤ Real.exp ((Real.log u + 1) / 40) / 10 :=
    (capH_le_K hc (le_refl (X₀ : ℝ)) hXL).trans (capBound_le (by linarith))
  -- the count
  have hwin := win_card_le (PR θ X₀ ω) (Hc X₀) hXmp hα'α hαβ
  rw [← hβdef] at hwin
  have hcont : 2.00005 * (2.04 * Hc X₀ y / Xm X₀) ≤ 4.21 * Hc X₀ y / X₀ := by
    rw [mul_div_assoc', div_le_div_iff₀ hXmp hX0p]; nlinarith
  have hcont0 : 0 ≤ 2.04 * Hc X₀ y / Xm X₀ := by positivity
  have hHq : 0 ≤ Hc X₀ u := by unfold Hc; exact capH_nonneg _ _
  have hu2 : 0 ≤ u ^ (thetaB θo) := by positivity
  have hT0 : (Mcl θ X₀ ω).T X₀ = X₀ := by rw [Mcl_eq hc]; exact (hc.std ω).limModel_T_X₀
  have hE0 := Real.exp_pos ((Real.log u + 1) / 40)
  rcases lt_or_ge β (Xm X₀) with hβXm | hβXm
  · -- (i) the window is below `X₀⁻`: `N = ⌊·⌋`
    have h1 := N_high hc ω (by linarith) hβXm
    have h2 := N_low hc ω hα'1
    have h3 : α' - 3 / 2 ≤ min α' (Xm X₀ - 1 / 2) - 1 := by
      rcases le_total α' (Xm X₀ - 1 / 2) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    linarith
  rcases lt_or_ge α' (X₀ : ℝ) with hα'X | hα'X
  · -- (ii) the window meets `[X₀⁻, X₀)`
    obtain ⟨βs, hβsdef⟩ : ∃ z : ℝ, z = max β (X₀ : ℝ) := ⟨_, rfl⟩
    have hβs1 : (X₀ : ℝ) ≤ βs := by rw [hβsdef]; exact le_max_right _ _
    have hβs2 : βs ≤ 2 * u := by rw [hβsdef]; exact max_le hβu (by linarith)
    have hNβ : (PR θ X₀ ω).N β ≤ (PR θ X₀ ω).N βs :=
      BeurlingSystem.N_mono _ (by rw [hβsdef]; exact le_max_left _ _)
    have hlag := (abs_le.mp (hlagb βs hβs1 hβs2)).2
    have hTi := T_incr hc ω (le_refl (X₀ : ℝ)) hβs1
    have hβsX : βs - X₀ ≤ β - α' := by
      rcases le_total β (X₀ : ℝ) with h | h
      · rw [hβsdef, max_eq_right h]; linarith
      · rw [hβsdef, max_eq_left h]; linarith
    have hLC := hLCb X₀ βs (by linarith) le_rfl (by linarith) (by linarith)
    have h2 := N_low hc ω hα'1
    have h3 : α' - capH X₀ X₀ / 2 - 3 / 2 ≤ min α' (Xm X₀ - 1 / 2) - 1 := by
      rcases le_total α' (Xm X₀ - 1 / 2) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h, hXme]; linarith
    have hgeo : (X₀ : ℝ) - α' + 2.00005 * (βs - X₀) ≤
        2.00005 * (β - α') + capH X₀ X₀ / 2 := by
      rcases le_total β (X₀ : ℝ) with h | h
      · rw [hβsdef, max_eq_right h]
        have : (X₀ : ℝ) - α' ≤ (X₀ - Xm X₀) + (β - α') := by linarith
        rw [hXme] at this
        have : (0 : ℝ) ≤ β - α' := by linarith
        linarith
      · rw [hβsdef, max_eq_left h]
        have : (0 : ℝ) ≤ X₀ - α' := by linarith
        linarith
    rw [hℓe] at hgeo
    linarith
  · -- (iii) the window lies in `[X₀, ∞)`
    have hlagβ := (abs_le.mp (hlagb β (hα'X.trans hαβ) hβu)).2
    have hlagα := (abs_le.mp (hlagb α' hα'X (by linarith))).1
    have hTi := T_incr hc ω hα'X hαβ
    have hLC := hLCb α' β hαu hα'X (by linarith) (by linarith)
    rw [hℓe] at hTi
    linarith

include hc hev in
/-- **`KR.X0S.Hyp` for the realised system on `Good(< t)`**, `Y = b + H(b)`, `t ≥ b`, off
`NiceEvᶜ`: the window count `winCount_G0` with `x0sHyp_R`. -/
theorem x0sHyp_G0 {t : ℕ} {ω : JitterΩ} (hω : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {b : ℝ} (hbt : b ≤ t) {Z η1 η2 θo : ℝ} {ε1 : ℝ → ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) Z η1 η2 ε1) (hZ : Xm X₀ ≤ Z) (hθo : θ ≤ θo)
    (hθ1 : θo ≤ 1 / 2) :
    KR.X0S.Hyp (PR θ X₀ ω) (Hc X₀) (Xm X₀) X₀ Z η1 η2 ε1 θo (b + Hc X₀ b) :=
  x0sHyp_R hc hbs hZ (by linarith [hc.hθ.1]) hθ1
    (fun _ h1 h2 => winCount_G0 D hc hev hω hN hbt hθo h1 h2)

end Main

end Queue6

end
