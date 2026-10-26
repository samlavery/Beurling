module

public import RequestProject.Beurling.Decomp.Mellin
public import RequestProject.Beurling.ZBIdentity

/-!
# The transform of the base part of the target

For `x ≥ X₀` the base part of the target (6) minus `x` is the rigid error
`E_rig(x) = Ψ(x, X₀) - Ψ(X₀, X₀) - ∫_{X₀}^x ρ_det`, and for `1 ≤ x < X₀` it is `⌊x⌋ - x`
(`baseErr`). We prove, for `Re s > 0`, `s ≠ 1` and `X₀` an `X₀`-smooth integer (for instance
`X₀` even, `X₀ ≥ 4`):

  `s ∫_1^∞ baseErr(x) x^{-s-1} dx = Z_B(s) - s/(s-1)`     (`mellin_baseErr`)

with `Z_B = ZBcont` the base factor of (14)–(15). This is the base-factor part of the
decomposition (14), valid on all of `σ > 0` (the paper states (14) for `σ > 1`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Remark12 BaseFactor Target Rankin

namespace Decomp

/-- The base part of the target minus `x`: `⌊x⌋ - x` below `X₀`, `E_rig(x)` from `X₀` on. -/
noncomputable def baseErr (X₀ : ℕ) (κ x : ℝ) : ℝ :=
  if x < X₀ then (⌊x⌋₊ : ℝ) - x else rigidErr X₀ κ x

/-- The auxiliary function `J(x) = x` below `X₀` and `X₀ + ∫_{X₀}^x ρ_det` from `X₀` on, so that
`baseErr = Ψ(·, X₀) - J`. -/
noncomputable def baseJ (X₀ : ℕ) (κ x : ℝ) : ℝ :=
  if x < X₀ then x else X₀ + ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u

/-- The `X₀`-smooth numbers up to `N` are `1, …, N` when `N < X₀`, or `N = X₀` is smooth. -/
lemma smoothNumbersUpTo_eq_Icc {X₀ N : ℕ} (hN : N < X₀ ∨ (N = X₀ ∧ X₀ ∈ X₀.smoothNumbers)) :
    Nat.smoothNumbersUpTo N X₀ = Finset.Icc 1 N := by
  ext n
  rw [Nat.mem_smoothNumbersUpTo, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h2), h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases hN with hN | ⟨rfl, hX⟩
    · exact Nat.mem_smoothNumbers_of_lt h1 (by omega)
    · rcases h2.lt_or_eq with h | h
      · exact Nat.mem_smoothNumbers_of_lt h1 h
      · rw [h]; exact hX

/-- Below `X₀` every positive integer is `X₀`-smooth, so `Ψ(x, X₀) = ⌊x⌋`. -/
lemma smoothCount_eq_floor {X₀ : ℕ} {x : ℝ} (hx : x < X₀) : smoothCount X₀ x = ⌊x⌋₊ := by
  unfold smoothCount
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
  · rw [h0]
    apply Finset.card_eq_zero.mpr
    ext n
    simp only [Nat.mem_smoothNumbersUpTo, Finset.notMem_empty, iff_false, not_and]
    intro hn hs
    have : n = 0 := by omega
    exact Nat.ne_zero_of_mem_smoothNumbers hs this
  · have hx0 : 0 ≤ x := by
      by_contra h; push_neg at h; rw [Nat.floor_of_nonpos h.le] at hpos; omega
    have hlt : ⌊x⌋₊ < X₀ := by
      have := Nat.floor_le hx0
      exact_mod_cast lt_of_le_of_lt this hx
    rw [smoothNumbersUpTo_eq_Icc (Or.inl hlt), Nat.card_Icc]
    omega

/-- If `X₀` is itself `X₀`-smooth, `Ψ(X₀, X₀) = X₀`. -/
lemma smoothCount_self {X₀ : ℕ} (hX : X₀ ∈ X₀.smoothNumbers) :
    smoothCount X₀ (X₀ : ℝ) = X₀ := by
  unfold smoothCount
  rw [Nat.floor_natCast, smoothNumbersUpTo_eq_Icc (Or.inr ⟨rfl, hX⟩), Nat.card_Icc]
  omega

lemma baseErr_eq {X₀ : ℕ} (hX : X₀ ∈ X₀.smoothNumbers) (κ x : ℝ) :
    baseErr X₀ κ x = smoothCount X₀ x - baseJ X₀ κ x := by
  unfold baseErr baseJ
  split_ifs with h
  · rw [smoothCount_eq_floor h]
  · unfold rigidErr
    rw [smoothCount_self hX]
    ring

/-- **Partial summation for the rigid set**: `s ∫_1^∞ Ψ(x, X₀) x^{-s-1} dx = Z_∞(s)` for
`σ > 0`. -/
lemma mellin_smoothCount (X₀ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((smoothCount X₀ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (fun x => (smoothCount X₀ x : ℝ)) s = Zinf X₀ s := by
  classical
  set c : ℝ := s.re / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcs : c < s.re := by rw [hc]; linarith
  have hbound : ∀ x ≥ (1 : ℝ), |(smoothCount X₀ x : ℝ)| ≤ rankinConst X₀ c * x ^ c := by
    intro x hx
    rw [abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
    exact smoothCount_le_rankin X₀ hc0 (by linarith)
  have hmono : Monotone (fun x : ℝ => (smoothCount X₀ x : ℝ)) := fun x y hxy => by
    simp only; exact_mod_cast smoothCount_mono X₀ hxy
  refine ⟨tailMellin_integrable hmono.locallyIntegrable hbound hcs, ?_⟩
  -- partial summation with `t n = n + 1`, `w n = 1_{n+1 smooth}`
  set t : ℕ → ℝ := fun n => (n : ℝ) + 1 with ht
  set w : ℕ → ℝ := fun n => if n + 1 ∈ X₀.smoothNumbers then 1 else 0 with hw
  have hcnt : ∀ x : ℝ, 0 ≤ x → AbelMellin.cnt t w x = smoothCount X₀ x := by
    intro x hx
    unfold AbelMellin.cnt
    rw [tsum_eq_sum (s := Finset.range ⌊x⌋₊)]
    · have e : ∀ n ∈ Finset.range ⌊x⌋₊, (if t n ≤ x then w n else 0) =
          (fun m => if m ∈ X₀.smoothNumbers then (1 : ℝ) else 0) (n + 1) := by
        intro n hn
        rw [Finset.mem_range] at hn
        have : t n ≤ x := by
          simp only [ht]
          have h1 : ((n + 1 : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
          push_cast at h1
          exact h1.trans (Nat.floor_le hx)
        rw [if_pos this]
      rw [Finset.sum_congr rfl e]
      have h0 : (if (0 : ℕ) ∈ X₀.smoothNumbers then (1 : ℝ) else 0) = 0 := by
        simp [Nat.smoothNumbers]
      have := Finset.sum_range_succ' (fun m => if m ∈ X₀.smoothNumbers then (1 : ℝ) else 0)
        ⌊x⌋₊
      rw [h0, add_zero] at this
      simp only
      rw [← this, Finset.sum_boole]
      unfold smoothCount Nat.smoothNumbersUpTo
      simp
    · intro n hn
      rw [Finset.mem_range, not_lt] at hn
      have : ¬ t n ≤ x := by
        simp only [ht, not_le]
        have h1 : (⌊x⌋₊ : ℝ) ≤ n := by exact_mod_cast hn
        linarith [Nat.lt_floor_add_one x]
      rw [if_neg this]
  have hH : AbelMellin.Hyp t w c := by
    refine ⟨fun n => ?_, fun n => ?_, fun x => ?_, ?_⟩
    · simp only [ht]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    · simp only [hw]; split_ifs <;> norm_num
    · refine summable_of_ne_finset_zero (s := Finset.range (⌊x⌋₊ + 1)) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      have : ¬ t n ≤ x := by
        simp only [ht, not_le]
        rcases le_or_gt 0 x with hx | hx
        · have h1 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
          push_cast at h1
          linarith [Nat.lt_floor_add_one x]
        · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      rw [if_neg this]
    · refine ⟨rankinConst X₀ c, fun x hx => ?_⟩
      rw [hcnt x (by linarith)]
      have := hbound x hx
      rwa [abs_of_nonneg (Nat.cast_nonneg _)] at this
  have hsum := AbelMellin.hasSum_cpow hH (s := s) hs hcs
  have hZ : HasSum (fun n : ℕ => ((w n : ℝ) : ℂ) * ((t n : ℝ) : ℂ) ^ (-s)) (Zinf X₀ s) := by
    have h1 := hasSum_smooth_cpow X₀ hs
    rw [← hasSum_nat_add_iff' 1] at h1
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h1
    have h0 : (if (0 : ℕ) ∈ X₀.smoothNumbers then ((0 : ℝ) : ℂ) ^ (-s) else 0) = 0 := by
      simp [Nat.smoothNumbers]
    rw [h0, sub_zero] at h1
    refine h1.congr_fun fun n => ?_
    simp only [hw, ht]
    split_ifs <;> push_cast <;> simp
  have := hsum.unique hZ
  rw [← this]
  unfold tailMellin
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only
  rw [hcnt x (by linarith [show (1 : ℝ) < x from hx])]

/-- The transform of `J`. -/
lemma mellin_baseJ {X₀ : ℕ} (hX1 : 1 ≤ X₀) {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (baseJ X₀ κ) s =
        s / (s - 1) - ((X₀ : ℝ) : ℂ) ^ (1 - s) / (s - 1) +
          (Wfac κ s * (Zinf X₀ s - headSum X₀ s) - boundary X₀ κ s) := by
  have hX1' : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1' : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hs1'' : s - 1 ≠ 0 := fun h => hs1 (by linear_combination h)
  set σ := s.re
  -- the rigid density: integrability and its transform (as in the proof of (15))
  have heq : ∀ z : ℂ, EqOn (fun x : ℝ => (x : ℂ) ^ (-z) * (rhoDet X₀ κ x : ℂ))
      (fun x => ∑' d, ramp X₀ κ z d x) (Ioi (X₀ : ℝ)) := fun z x hx =>
    (hasSum_ramp X₀ hκ z (lt_trans hX0 hx)).tsum_eq.symm
  have hrho0 : ∀ x : ℝ, 0 < x → 0 ≤ rhoDet X₀ κ x := fun x hx =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ.le hx.le)
  have hg : IntegrableOn (fun u => rhoDet X₀ κ u * u ^ (-σ)) (Ioi (X₀ : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(σ : ℂ)) * (rhoDet X₀ κ x : ℂ))
        (Ioi (X₀ : ℝ)) := by
      refine (integrable_tsum_ramp X₀ hκ (s := (σ : ℂ)) (by simpa using hs)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (heq _ hx).symm
    refine h1.norm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans hX0 hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hrho0 x hx0)]
    simp [mul_comm]
  have hIρ : ∫ u in Ioi (X₀ : ℝ), (rhoDet X₀ κ u : ℂ) * (u : ℂ) ^ (-s) =
      Wfac κ s * (Zinf X₀ s - headSum X₀ s) - boundary X₀ κ s := by
    have e : ∀ u : ℝ, (rhoDet X₀ κ u : ℂ) * (u : ℂ) ^ (-s) =
        (u : ℂ) ^ (-s) * (rhoDet X₀ κ u : ℂ) := fun u => mul_comm _ _
    simp_rw [e]
    rw [setIntegral_congr_fun measurableSet_Ioi (heq s),
      ← integral_tsum_of_summable_integral_norm (integrable_ramp X₀ hκ s)
        (summable_integral_norm_ramp X₀ hκ hs)]
    simp_rw [integral_ramp X₀ hX1 hκ hs]
    exact (hasSum_rampVal X₀ hs).tsum_eq
  obtain ⟨hPint, hPval⟩ := mellin_primitive hX0 hs hg
  -- the pieces on `(1, X₀]` and on `(X₀, ∞)`
  have hlow : ∀ x ∈ Ioc (1 : ℝ) X₀, ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      (x : ℂ) ^ (-s) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith [hx.1])
    have hJ : baseJ X₀ κ x = x := by
      unfold baseJ
      rcases hx.2.lt_or_eq with h | h
      · rw [if_pos h]
      · rw [if_neg (not_lt.mpr h.ge), h, intervalIntegral.integral_same, add_zero]
    rw [hJ, Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  have hhigh : ∀ x ∈ Ioi (X₀ : ℝ), ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      (X₀ : ℂ) * (x : ℂ) ^ (-s - 1) +
        ((∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    have hJ : baseJ X₀ κ x = X₀ + ∫ u in (X₀ : ℝ)..x, rhoDet X₀ κ u := by
      unfold baseJ; rw [if_neg (not_lt.mpr (le_of_lt hx))]
    rw [hJ]; push_cast; ring
  have hint_low : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioc 1 (X₀ : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX1').mp
      (intervalIntegral.intervalIntegrable_cpow (Or.inr (by
        rw [uIcc_of_le hX1']; intro h; linarith [h.1])))
  have hint_c : IntegrableOn (fun x : ℝ => (X₀ : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi (X₀ : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hX0).const_mul _
  have hint1 : IntegrableOn (fun x : ℝ => ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioc 1 (X₀ : ℝ)) :=
    hint_low.congr_fun (fun x hx => (hlow x hx).symm) measurableSet_Ioc
  have hint2 : IntegrableOn (fun x : ℝ => ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi (X₀ : ℝ)) :=
    IntegrableOn.congr_fun (hint_c.add hPint) (fun x hx => (hhigh x hx).symm) measurableSet_Ioi
  have hunion : Ioc (1 : ℝ) X₀ ∪ Ioi (X₀ : ℝ) = Ioi 1 := Ioc_union_Ioi_eq_Ioi hX1'
  refine ⟨hunion ▸ hint1.union hint2, ?_⟩
  unfold tailMellin
  rw [← hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2,
    setIntegral_congr_fun measurableSet_Ioc hlow, setIntegral_congr_fun measurableSet_Ioi hhigh,
    integral_add hint_c hPint, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) hX0,
    ← intervalIntegral.integral_of_le hX1',
    integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), by
      rw [uIcc_of_le hX1']; intro h; linarith [h.1]⟩)]
  rw [mul_add, mul_add, hPval, hIρ]
  have e2 : ((X₀ : ℝ) : ℂ) ^ (1 - s) = (X₀ : ℂ) * ((X₀ : ℝ) : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast hX0.ne'),
      Complex.cpow_one]
    push_cast; ring
  rw [show -s - 1 + 1 = -s by ring, show -s + 1 = 1 - s by ring, e2]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hns : -s ≠ 0 := neg_ne_zero.mpr hs0
  field_simp
  ring

/-- **The base factor in the decomposition (14)**: for `σ > 0`, `s ≠ 1`,
`s ∫_1^∞ (T_base(x) - x) x^{-s-1} dx = Z_B(s) - s/(s-1)`, where `T_base` is the base part of the
target (`⌊x⌋` below `X₀`, `X₀ + Ψ(x,X₀) - Ψ(X₀,X₀) + ∫_{X₀}^x (1 - ρ_det)` above). -/
theorem mellin_baseErr {X₀ : ℕ} (hX : X₀ ∈ X₀.smoothNumbers) {κ : ℝ} (hκ : 0 < κ) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => ((baseErr X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
      s * tailMellin (baseErr X₀ κ) s = ZBcont X₀ κ s - s / (s - 1) := by
  have hX1 : 1 ≤ X₀ := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hX)
  obtain ⟨hi1, he1⟩ := mellin_smoothCount X₀ hs
  obtain ⟨hi2, he2⟩ := mellin_baseJ hX1 hκ hs hs1
  have heq : (fun x : ℝ => ((baseErr X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ((smoothCount X₀ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) -
        ((baseJ X₀ κ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    funext x; rw [baseErr_eq hX]; push_cast; ring
  refine ⟨heq ▸ hi1.sub hi2, ?_⟩
  unfold tailMellin at he1 he2 ⊢
  rw [heq, integral_sub hi1 hi2, mul_sub, he1, he2]
  unfold ZBcont
  ring

end Decomp

end
