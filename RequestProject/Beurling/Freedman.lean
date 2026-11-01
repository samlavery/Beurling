module

public import Mathlib

/-!
# Freedman's inequality (73)

Section 6 of the paper applies Freedman's inequality in the form (73):

  `P(∃ n : S_n ≥ a, V_n ≤ v) ≤ exp(-a² / (2v + 2ab/3))`

for a martingale `S_n` with increments at most `b` and predictable quadratic variation `V_n`.

Here `S_n = ∑_{k<n} ξ_k`, where `ξ_k` is `ℱ_{k+1}`-measurable, `E[ξ_k | ℱ_k] = 0`, `ξ_k ≤ b`
(and, for integrability, `|ξ_k| ≤ C`), and `V_n = ∑_{k<n} E[ξ_k² | ℱ_k]`.

* `Freedman.exp_le_quad` : `e^{λx} ≤ 1 + λx + ψ x²` for `x ≤ b`, `0 ≤ λ`, `λb < 3`, with
  `ψ = λ²/(2(1 - λb/3))` (Bernstein's bound on the exponential series);
* `Freedman.supermartingale_expMart` : `exp(λ S_n - ψ V_n)` is a supermartingale;
* `Freedman.max_ineq` : the maximal inequality for a nonnegative supermartingale,
  `c · P(∃ n ≤ N, M_n ≥ c) ≤ E[M_0]` (by decomposing at the first hitting time);
* `Freedman.freedman` : **Freedman's inequality (73)**, for every horizon `N`, and
  `Freedman.freedman_iUnion` : for all `n` at once.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Nat

namespace Freedman

/-! ### The exponential bound -/

/-- `e^y ≤ 1 + y + y²/2` for `y ≤ 0`. -/
lemma exp_le_quad_of_nonpos {y : ℝ} (hy : y ≤ 0) : Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have hanti : AntitoneOn (fun t : ℝ => 1 + t + t ^ 2 / 2 - Real.exp t) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · fun_prop
    · fun_prop
    · intro t ht
      rw [interior_Iic] at ht
      have : deriv (fun t : ℝ => 1 + t + t ^ 2 / 2 - Real.exp t) t = 1 + t - Real.exp t := by
        have h : HasDerivAt (fun t : ℝ => 1 + t + t ^ 2 / 2 - Real.exp t)
            (1 + t - Real.exp t) t := by
          convert! (((hasDerivAt_id t).const_add 1).add
            ((hasDerivAt_pow 2 t).div_const 2)).sub (Real.hasDerivAt_exp t) using 1
          simp
        exact h.deriv
      rw [this]
      linarith [Real.add_one_le_exp t]
  have := hanti hy (Set.self_mem_Iic) hy
  simp at this
  linarith

/-- `(n+2)! ≥ 2 · 3^n`. -/
lemma two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2)! := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

/-- **Bernstein's bound**: `e^y ≤ 1 + y + y²/(2(1 - y/3))` for `0 ≤ y < 3`. -/
lemma exp_le_bernstein {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
  have hs : Summable fun n : ℕ => y ^ n / n ! := Real.summable_pow_div_factorial y
  have he : Real.exp y = ∑' n : ℕ, y ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs2 : Summable fun n : ℕ => y ^ (n + 2) / (n + 2)! :=
    (summable_nat_add_iff 2).mpr hs
  have h2 : ∑' n : ℕ, y ^ n / n ! = 1 + y + ∑' n : ℕ, y ^ (n + 2) / (n + 2)! := by
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
      Nat.factorial_one]
    ring_nf
  have hr : y / 3 < 1 := by linarith
  have hr0 : 0 ≤ y / 3 := by linarith
  have hg : Summable fun n : ℕ => y ^ 2 / 2 * (y / 3) ^ n :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hle : ∀ n : ℕ, y ^ (n + 2) / (n + 2)! ≤ y ^ 2 / 2 * (y / 3) ^ n := by
    intro n
    have hf : (2 * 3 ^ n : ℝ) ≤ (n + 2)! := by exact_mod_cast two_mul_three_pow_le_factorial n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    rw [div_le_iff₀ (by positivity), div_pow, pow_add]
    have : y ^ 2 / 2 * (y ^ n / 3 ^ n) * (n + 2)! ≥ y ^ 2 / 2 * (y ^ n / 3 ^ n) * (2 * 3 ^ n) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    have e : y ^ 2 / 2 * (y ^ n / 3 ^ n) * (2 * 3 ^ n) = y ^ n * y ^ 2 := by
      field_simp
    linarith
  have h3 : ∑' n : ℕ, y ^ (n + 2) / (n + 2)! ≤ ∑' n : ℕ, y ^ 2 / 2 * (y / 3) ^ n :=
    hs2.tsum_le_tsum hle hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr] at h3
  have e : y ^ 2 / 2 * (1 - y / 3)⁻¹ = y ^ 2 / (2 * (1 - y / 3)) := by
    field_simp
  rw [he, h2]
  linarith

/-- **The exponential bound** used for Freedman's inequality: for `x ≤ b`, `0 ≤ λ` and
`λ b < 3` (`b ≥ 0`), `e^{λx} ≤ 1 + λx + ψ x²` with `ψ = λ² / (2(1 - λb/3))`. -/
lemma exp_le_quad {b l x : ℝ} (hb : 0 ≤ b) (hl : 0 ≤ l) (hlb : l * b < 3) (hx : x ≤ b) :
    Real.exp (l * x) ≤ 1 + l * x + l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
  have hd : 0 < 1 - l * b / 3 := by linarith
  rcases le_total x 0 with hx0 | hx0
  · have h1 := exp_le_quad_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hl hx0)
    have h2 : (l * x) ^ 2 / 2 ≤ l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
      have hlb' : 1 - l * b / 3 ≤ 1 := by nlinarith
      rw [mul_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      have : 0 ≤ l ^ 2 * x ^ 2 := by positivity
      nlinarith
    linarith
  · have hy0 : 0 ≤ l * x := mul_nonneg hl hx0
    have hyb : l * x ≤ l * b := mul_le_mul_of_nonneg_left hx hl
    have h1 := exp_le_bernstein hy0 (by linarith)
    have h2 : (l * x) ^ 2 / (2 * (1 - l * x / 3)) ≤ l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
      rw [mul_pow, div_mul_eq_mul_div]
      apply div_le_div₀ (by positivity) (by ring_nf; rfl) (by positivity)
      linarith
    linarith

/-! ### The maximal inequality for a nonnegative supermartingale -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- "Not hit before `k`": `M_j < c` for all `j < k`. -/
def notHit (M : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) : Set Ω :=
  ⋂ j ∈ range k, {ω | M j ω < c}

lemma measurableSet_notHit {M : ℕ → Ω → ℝ} (hM : StronglyAdapted ℱ M) (c : ℝ) {k n : ℕ}
    (hkn : k ≤ n + 1) : MeasurableSet[ℱ n] (notHit M c k) := by
  unfold notHit
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hj' : j ≤ n := by rw [mem_range] at hj; omega
  exact measurableSet_lt ((hM j).mono (ℱ.mono hj')).measurable measurable_const

lemma notHit_succ (M : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) :
    notHit M c (k + 1) = notHit M c k \ {ω | c ≤ M k ω} := by
  ext ω
  simp only [notHit, mem_range, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_diff, not_le]
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact h1 j h
    · rw [h]; exact h2

/-- **Maximal inequality for a nonnegative supermartingale**:
`c · P(∃ n ≤ N, M_n ≥ c) ≤ E[M_0]` for `c > 0`. -/
theorem max_ineq {M : ℕ → Ω → ℝ} (hM : Supermartingale M ℱ μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    c * μ.real {ω | ∃ n ≤ N, c ≤ M n ω} ≤ ∫ ω, M 0 ω ∂μ := by
  set D := notHit M c
  set B : ℕ → Set Ω := fun k => D k ∩ {ω | c ≤ M k ω}
  have hmeasM : ∀ k, Measurable[m0] (M k) := fun k =>
    ((hM.1 k).mono (ℱ.le k)).measurable
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (ℱ.le k _ (measurableSet_notHit hM.1 c (by omega))).inter
      (measurableSet_le measurable_const (hmeasM k))
  -- the telescoping claim
  have claim : ∀ n, ∑ k ∈ range n, ∫ ω in B k, M k ω ∂μ + ∫ ω in D n, M n ω ∂μ ≤
      ∫ ω, M 0 ω ∂μ := by
    intro n
    induction n with
    | zero => simp [D, notHit]
    | succ n ih =>
      have h1 : ∫ ω in D n, M n ω ∂μ =
          ∫ ω in B n, M n ω ∂μ + ∫ ω in D (n + 1), M n ω ∂μ := by
        rw [show D (n + 1) = D n \ {ω | c ≤ M n ω} from notHit_succ M c n]
        exact (integral_inter_add_diff (measurableSet_le measurable_const (hmeasM n))
          (hM.integrable n).integrableOn).symm
      have h2 : ∫ ω in D (n + 1), M (n + 1) ω ∂μ ≤ ∫ ω in D (n + 1), M n ω ∂μ :=
        hM.setIntegral_le (Nat.le_succ n) (measurableSet_notHit hM.1 c le_rfl)
      rw [sum_range_succ]
      linarith
  have hA : {ω | ∃ n ≤ N, c ≤ M n ω} ⊆ ⋃ k ∈ range (N + 1), B k := by
    intro ω h
    obtain ⟨n, hn, hc'⟩ := h
    have hex : ∃ n, c ≤ M n ω := ⟨n, hc'⟩
    set k := Nat.find hex
    have hk : k ≤ n := Nat.find_min' hex hc'
    simp only [Set.mem_iUnion, mem_range]
    refine ⟨k, by omega, ?_, Nat.find_spec hex⟩
    simp only [D, notHit, Set.mem_iInter, mem_range, Set.mem_setOf_eq]
    intro j hj
    exact not_le.mp (Nat.find_min hex hj)
  have hmeas : μ.real {ω | ∃ n ≤ N, c ≤ M n ω} ≤ ∑ k ∈ range (N + 1), μ.real (B k) :=
    (measureReal_mono hA (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
  have hB : ∀ k, c * μ.real (B k) ≤ ∫ ω in B k, M k ω ∂μ := fun k =>
    setIntegral_ge_of_const_le_real (hBm k) (measure_ne_top _ _)
      (fun ω hω => hω.2) (hM.integrable k).integrableOn
  have hlast : 0 ≤ ∫ ω in D (N + 1), M (N + 1) ω ∂μ :=
    setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun ω => hnn _ ω)
  have hsum := sum_le_sum fun k (_ : k ∈ range (N + 1)) => hB k
  rw [← mul_sum] at hsum
  have := claim (N + 1)
  nlinarith [mul_le_mul_of_nonneg_left hmeas hc.le]

/-! ### The exponential supermartingale -/

/-- Martingale differences `ξ_n` (`ℱ_{n+1}`-measurable, `E[ξ_n | ℱ_n] = 0`) bounded above by `b`
and, for integrability, bounded in absolute value by `C`. -/
structure MartDiff (ℱ : Filtration ℕ m0) (μ : Measure Ω) (ξ : ℕ → Ω → ℝ) (b C : ℝ) :
    Prop where
  meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ n)
  le_b : ∀ n ω, ξ n ω ≤ b
  bdd : ∀ n ω, |ξ n ω| ≤ C
  mean_zero : ∀ n, μ[ξ n | ℱ n] =ᵐ[μ] 0

/-- The martingale `S_n = ∑_{k<n} ξ_k`. -/
def S (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ range n, ξ k ω

/-- The predictable quadratic variation `V_n = ∑_{k<n} E[ξ_k² | ℱ_k]`. -/
noncomputable def V (ℱ : Filtration ℕ m0) (μ : Measure Ω) (ξ : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ range n, (μ[fun ω => ξ k ω ^ 2 | ℱ k]) ω

/-- The exponential process `exp(λ S_n - ψ V_n)`. -/
noncomputable def expMart (ℱ : Filtration ℕ m0) (μ : Measure Ω) (ξ : ℕ → Ω → ℝ)
    (l ψ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (l * S ξ n ω - ψ * V ℱ μ ξ n ω)

variable {ξ : ℕ → Ω → ℝ} {b C : ℝ}

omit [IsProbabilityMeasure μ] in
lemma measurable_S (h : MartDiff ℱ μ ξ b C) (n : ℕ) : Measurable[ℱ n] (S ξ n) := by
  unfold S
  refine Finset.measurable_sum _ fun k hk => ?_
  rw [mem_range] at hk
  exact ((h.meas k).mono (ℱ.mono (by omega))).measurable

omit [IsProbabilityMeasure μ] in
lemma measurable_V (n : ℕ) : Measurable[ℱ n] (V ℱ μ ξ n) := by
  unfold V
  refine Finset.measurable_sum _ fun k hk => ?_
  rw [mem_range] at hk
  exact (stronglyMeasurable_condExp.mono (ℱ.mono (by omega))).measurable

omit [IsProbabilityMeasure μ] in
lemma measurable_expMart (h : MartDiff ℱ μ ξ b C) (l ψ : ℝ) (n : ℕ) :
    Measurable[ℱ n] (expMart ℱ μ ξ l ψ n) := by
  unfold expMart
  exact (((measurable_S h n).const_mul l).sub ((measurable_V n).const_mul ψ)).exp

omit [IsProbabilityMeasure μ] in
lemma condSq_nonneg (n : ℕ) : 0 ≤ᵐ[μ] μ[fun ω => ξ n ω ^ 2 | ℱ n] :=
  condExp_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma V_nonneg (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ V ℱ μ ξ n ω := by
  have : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ (μ[fun ω => ξ k ω ^ 2 | ℱ k]) ω :=
    ae_all_iff.mpr fun k => condSq_nonneg k
  filter_upwards [this] with ω hω
  exact Finset.sum_nonneg fun k _ => hω k

omit [IsProbabilityMeasure μ] in
lemma abs_S_le (h : MartDiff ℱ μ ξ b C) (n : ℕ) (ω : Ω) : |S ξ n ω| ≤ n * C := by
  unfold S
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range n, |ξ k ω| ≤ ∑ k ∈ range n, C := sum_le_sum fun k _ => h.bdd k ω
    _ = n * C := by simp

lemma integrable_expMart (h : MartDiff ℱ μ ξ b C) {l ψ : ℝ} (hl : 0 ≤ l) (hψ : 0 ≤ ψ)
    (n : ℕ) : Integrable (expMart ℱ μ ξ l ψ n) μ := by
  refine Integrable.of_bound ((measurable_expMart h l ψ n).mono (ℱ.le n) le_rfl).aestronglyMeasurable
    (Real.exp (l * (n * C))) ?_
  filter_upwards [V_nonneg (μ := μ) (ℱ := ℱ) (ξ := ξ) n] with ω hω
  unfold expMart
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 := (abs_le.mp (abs_S_le h n ω)).2
  have h2 : 0 ≤ ψ * V ℱ μ ξ n ω := mul_nonneg hψ hω
  nlinarith

omit [IsProbabilityMeasure μ] in
lemma expMart_succ (l ψ : ℝ) (n : ℕ) (ω : Ω) :
    expMart ℱ μ ξ l ψ (n + 1) ω = (expMart ℱ μ ξ l ψ n ω *
      Real.exp (-ψ * (μ[fun ω => ξ n ω ^ 2 | ℱ n]) ω)) * Real.exp (l * ξ n ω) := by
  unfold expMart S V
  rw [sum_range_succ, sum_range_succ, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-- **The exponential supermartingale**: for `0 ≤ λ`, `λ b < 3` and `ψ = λ²/(2(1 - λb/3))`,
`exp(λ S_n - ψ V_n)` is a supermartingale. -/
theorem supermartingale_expMart (h : MartDiff ℱ μ ξ b C) (hb : 0 ≤ b) {l : ℝ} (hl : 0 ≤ l)
    (hlb : l * b < 3) :
    Supermartingale (expMart ℱ μ ξ l (l ^ 2 / (2 * (1 - l * b / 3)))) ℱ μ := by
  set ψ := l ^ 2 / (2 * (1 - l * b / 3)) with hψdef
  have hd : 0 < 1 - l * b / 3 := by linarith
  have hψ : 0 ≤ ψ := by positivity
  refine supermartingale_nat (fun n => (measurable_expMart h l ψ n).stronglyMeasurable)
    (fun n => integrable_expMart h hl hψ n) fun n => ?_
  set D := μ[fun ω => ξ n ω ^ 2 | ℱ n]
  set F : Ω → ℝ := fun ω => expMart ℱ μ ξ l ψ n ω * Real.exp (-ψ * D ω)
  set G : Ω → ℝ := fun ω => Real.exp (l * ξ n ω)
  have hmeasξ : Measurable[m0] (ξ n) := ((h.meas n).mono (ℱ.le (n + 1))).measurable
  have hFm : StronglyMeasurable[ℱ n] F :=
    ((measurable_expMart h l ψ n).mul
      ((stronglyMeasurable_condExp (m := ℱ n)).measurable.const_mul (-ψ)).exp).stronglyMeasurable
  have hG : Integrable G μ := by
    refine Integrable.of_bound (hmeasξ.const_mul l).exp.aestronglyMeasurable
      (Real.exp (l * C)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (h.bdd n ω)).2
    nlinarith
  have hFG_eq : F * G = expMart ℱ μ ξ l ψ (n + 1) := by
    funext ω; simp only [Pi.mul_apply, F, G, D]; rw [expMart_succ]
  have hFG : Integrable (F * G) μ := by rw [hFG_eq]; exact integrable_expMart h hl hψ _
  set Q : Ω → ℝ := fun ω => 1 + l * ξ n ω + ψ * ξ n ω ^ 2
  have hξin : Integrable (ξ n) μ :=
    Integrable.of_bound hmeasξ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h.bdd n ω)
  have hξ2in : Integrable (fun ω => ξ n ω ^ 2) μ :=
    Integrable.of_bound (hmeasξ.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (h.bdd n ω) 2)
  have hQin : Integrable Q μ :=
    ((integrable_const 1).add (hξin.const_mul l)).add (hξ2in.const_mul ψ)
  -- `E[e^{λξ} | ℱ_n] ≤ E[Q | ℱ_n] = 1 + ψ D`
  have h1 : μ[G | ℱ n] ≤ᵐ[μ] μ[Q | ℱ n] :=
    condExp_mono hG hQin (Filter.Eventually.of_forall fun ω =>
      exp_le_quad hb hl hlb (h.le_b n ω))
  have h2 : μ[Q | ℱ n] =ᵐ[μ] fun ω => 1 + ψ * D ω := by
    have e1 : Q = (fun _ => (1 : ℝ)) + (l • ξ n + ψ • fun ω => ξ n ω ^ 2) := by
      funext ω; simp only [Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1]
    have ha := condExp_add (m := ℱ n) (integrable_const (1 : ℝ))
      ((hξin.smul l).add (hξ2in.smul ψ))
    have hb' := condExp_add (m := ℱ n) (hξin.smul l) (hξ2in.smul ψ)
    have hc1 := condExp_smul (μ := μ) l (ξ n) (ℱ n)
    have hc2 := condExp_smul (μ := μ) ψ (fun ω => ξ n ω ^ 2) (ℱ n)
    rw [condExp_const (ℱ.le n)] at ha
    filter_upwards [ha, hb', hc1, hc2, h.mean_zero n] with ω h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h5 ⊢
    rw [h5]; simp [D]
  have h3 := condExp_mul_of_stronglyMeasurable_left hFm hFG hG
  rw [hFG_eq] at h3
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e3, Pi.mul_apply]
  have hF0 : 0 ≤ F ω := by simp only [F, expMart]; positivity
  calc F ω * μ[G | ℱ n] ω ≤ F ω * (1 + ψ * D ω) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        rw [← e2]; exact e1
    _ ≤ F ω * Real.exp (ψ * D ω) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (ψ * D ω)]) hF0
    _ = expMart ℱ μ ξ l ψ n ω := by
        simp only [F]
        rw [mul_assoc, ← Real.exp_add]
        simp

/-- **Freedman's inequality (73)** (finite horizon): for `a > 0`, `v > 0`, `b ≥ 0`,
`P(∃ n ≤ N, S_n ≥ a ∧ V_n ≤ v) ≤ exp(-a² / (2v + 2ab/3))`. -/
theorem freedman (h : MartDiff ℱ μ ξ b C) (hb : 0 ≤ b) {a v : ℝ} (ha : 0 < a) (hv : 0 < v)
    (N : ℕ) :
    μ.real {ω | ∃ n ≤ N, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * v + 2 * a * b / 3))) := by
  set w := v + a * b / 3 with hw
  have hw0 : 0 < w := by positivity
  set l := a / w with hl
  have hl0 : 0 ≤ l := by positivity
  have hlb : l * b < 3 := by
    rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hw0]; nlinarith
  set ψ := l ^ 2 / (2 * (1 - l * b / 3)) with hψ
  have h1 : 1 - l * b / 3 = v / w := by
    rw [hl]; field_simp; rw [hw]; ring
  have hψ' : ψ = a ^ 2 / (2 * v * w) := by
    rw [hψ, h1, hl]; field_simp
  have hψ0 : 0 ≤ ψ := by rw [hψ']; positivity
  set t := a ^ 2 / (2 * w) with ht
  have hkey : l * a - ψ * v = t := by
    rw [hψ', hl, ht]; field_simp; ring
  have hden : 2 * v + 2 * a * b / 3 = 2 * w := by rw [hw]; ring
  rw [hden, ← ht]
  have hM := supermartingale_expMart h hb hl0 hlb
  have hmax := max_ineq hM (fun n ω => (Real.exp_pos _).le) (Real.exp_pos t) N
  have h0 : ∫ ω, expMart ℱ μ ξ l ψ 0 ω ∂μ = 1 := by
    simp [expMart, S, V]
  rw [h0] at hmax
  have hsub : {ω | ∃ n ≤ N, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v} ⊆
      {ω | ∃ n ≤ N, Real.exp t ≤ expMart ℱ μ ξ l ψ n ω} := by
    rintro ω ⟨n, hn, hS, hV⟩
    refine ⟨n, hn, ?_⟩
    unfold expMart
    apply Real.exp_le_exp.mpr
    rw [← hkey]
    nlinarith [mul_le_mul_of_nonneg_left hS hl0, mul_le_mul_of_nonneg_left hV hψ0]
  have hmono := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  change Real.exp t * μ.real {ω | ∃ n ≤ N, Real.exp t ≤ expMart ℱ μ ξ l ψ n ω} ≤ 1 at hmax
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos t)]
  nlinarith [Real.exp_pos t]

/-- **Freedman's inequality (73)** (all times): for `a > 0`, `v > 0`, `b ≥ 0`,
`P(∃ n, S_n ≥ a ∧ V_n ≤ v) ≤ exp(-a² / (2v + 2ab/3))`. -/
theorem freedman_iUnion (h : MartDiff ℱ μ ξ b C) (hb : 0 ≤ b) {a v : ℝ} (ha : 0 < a)
    (hv : 0 < v) :
    μ.real {ω | ∃ n, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * v + 2 * a * b / 3))) := by
  set A : ℕ → Set Ω := fun N => {ω | ∃ n ≤ N, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v}
  have hA : {ω | ∃ n, a ≤ S ξ n ω ∧ V ℱ μ ξ n ω ≤ v} = ⋃ N, A N := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, A]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  have hmono : Monotone A := fun N M hNM ω ⟨n, hn, h'⟩ => ⟨n, hn.trans hNM, h'⟩
  rw [hA, measureReal_def, hmono.measure_iUnion]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (iSup_le fun N => ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (A N))]
  exact ENNReal.ofReal_le_ofReal (freedman h hb ha hv N)

end Freedman

end
