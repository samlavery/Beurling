module

public import RequestProject.Beurling.RankFull.PILOneRun
public import RequestProject.Beurling.RankFull.BlockModel
public import RequestProject.Beurling.RankFull.MRRuns

/-!
# Lemma A.5 + Theorem A.10 for several runs: the pivot-by-pivot recursion

The window model over a jitter process, for a skeleton `(E_P, l)` with any run structure `l`.
The pivots are processed latest first, one at a time (`JitterLaw.pil_chain`). At the level with
`u` unprocessed pivot columns `0, …, u-1` (earliest first), the pending quantity `ZM u` is a sum
over the labels (slots) `λ : Fin u → ℕ` of the unprocessed pivots and over the contents `c` of the
blocks not yet summed (and the tails), of
`∏ 1_{A λ_j} · 1(contents decided) · 1(G_{<λ_{u-1}}) · Φ_{t-1}(λ_{first of run}) ·
 ∏_j q_{λ_j}^{-1} · ∫ L(z, log q_λ, c) dz · W_τ`,
the integral being over the log coordinates `z` of the processed pivots, with
`L = ∏_y e^{⟨E_y, x⟩} 1(c_y e^{⟨E_y, x⟩} ∈ J)` (`Lcore`). The caps `q_j ≥ τ_j` have been replaced
by the weight `∏_j (q_j/τ_j)^{s_j - 1} = W_τ ∏_y (n_y/c_y) ∏_j q_j^{-1}` (Lemma A.2).

At the last pivot of a run `P_t` the content of the block `F_t` (the slots after the next run) is
removed from all rows by the shift of the processed log-pivots (FAC, `lintegral_Lcore_shift`),
which produces its weight `∏_g q_g^{-a_g}`; the sum over the block content is then bounded by
(S3)(a) (`blockSum_le`), giving `Φ_t` at the first label of the next run.
-/

@[expose] public section

open Finset MeasureTheory RankFull.Runs
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θE : ℝ≥0∞}

/-- `1(t > 0)/t`. -/
noncomputable def invq (t : ℝ) : ℝ≥0∞ := (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹) t

/-- The span of the pivot columns of `P` (real coefficients), as a set of exponent columns. -/
def SpanSet {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (P : Set (Fin K)) : Set (Fin K → ℕ) :=
  {w | ∃ v : Fin K → ℝ, (∀ j, j ∉ P → v j = 0) ∧ ∀ y, (w y : ℝ) = ∑ j, (E y j : ℝ) * v j}

/-- The exponent column of slot `g` in a content. -/
def colC {K : ℕ} (c : Fin K → (Fin N → ℕ) × ℕ) (g : Fin N) : Fin K → ℕ := fun y => (c y).1 g

section Defs

variable (J : JitterLaw Ω P θE) {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (l : List ℕ)
  (τ : Fin K → ℝ) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (G : ℕ → Set Ω) (A Eu : ℝ)

/-- The slot-indexed Euler product at `ω`. -/
noncomputable def EuSω (ω : Ω) (u : ℕ) : ℝ :=
  EuS (fun n : Fin N => ω ∈ J.A n) (fun n => J.q n ω) Eu u

/-- The carried function `Φ_{t-1}(u) = G_{t-1}(Eu_s(u))/Eu_s(u)^{K_{t-1}}`, for the column of
run index `r` (the completed runs are those after `r`). -/
noncomputable def PhiC (r : ℕ) (ω : Ω) (u : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (GRun A (l.drop (r + 1)) (EuSω (N := N) J Eu ω u) /
    EuSω (N := N) J Eu ω u ^ (l.drop (r + 1)).sum)

/-- The cofactor values of a content. -/
noncomputable def cvs {K : ℕ} (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ) : Fin K → ℝ :=
  fun y => cval (fun n => J.q n ω) (c y)

/-- The log-values of the unprocessed pivots `0, …, m-1` (labels `λ`) and of the current
column `m` (value `x`). -/
noncomputable def uvecX {K : ℕ} (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (x : ℝ) : Fin K → ℝ :=
  fun j => if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω)
    else if (j : ℕ) = m then x else 0

/-- The log-values of the unprocessed pivots `0, …, m-1`. -/
noncomputable def uvec {K : ℕ} (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) : Fin K → ℝ :=
  fun j => if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0

/-- The integral over the processed pivots, with the current column at log-value `x`. -/
noncomputable def IzX (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ)
    (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Fin (K - (m + 1)) → ℝ, Lcore E Jw (cvs J ω c) (mergeL (K - (m + 1)) z (uvecX J m lab ω x))

/-- The integral over the processed pivots at the level with `m` unprocessed pivots. -/
noncomputable def IzM (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ℝ≥0∞ :=
  ∫⁻ z : Fin (K - m) → ℝ, Lcore E Jw (cvs J ω c) (mergeL (K - m) z (uvec J m lab ω))

/-- The constraints on the labels and contents at the level with `u` unprocessed pivots. -/
def ConsM (u : ℕ) (lab : Fin u → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) : Prop :=
  StrictMono lab ∧ (∀ j, lab j < N ∧ lab j ≤ smax) ∧
  (∀ y g, (c y).1 g ≠ 0 →
    (∀ h : 0 < u, (g : ℕ) < lab ⟨runFirst l (u - 1),
      lt_of_le_of_lt (runFirst_le l (u - 1)) (by omega)⟩) ∧
    (∀ j j' : Fin u, runNum l j = runNum l j' → ¬ (lab j ≤ g ∧ (g : ℕ) ≤ lab j')) ∧
    colC c g ∈ SpanSet E {j | u ≤ (j : ℕ) ∨ ∃ h : (j : ℕ) < u, (g : ℕ) < lab ⟨j, h⟩}) ∧
  (∀ j : Fin u, 1 ≤ (j : ℕ) → runFirst l j = j →
    ∃ y g, (c y).1 g ≠ 0 ∧ lab ⟨(j : ℕ) - 1, by omega⟩ < g ∧ (g : ℕ) < lab j)

/-- The term of `ZM (m+1)` (and of `ΦM m n`) for the labels `snoc lab n`, the current column at
value `t`. -/
noncomputable def Ffull (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (n : ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) (t : ℝ) : ℝ≥0∞ :=
  (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω * (G n).indicator 1 ω *
    PhiC (N := N) J l A Eu (runNum l m) ω ((Fin.snoc lab n : Fin (m + 1) → ℕ)
      ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) *
    (∏ j, invq (J.q (lab j) ω)) * invq t * IzX J E Jw m lab ω c (Real.log t) *
    ENNReal.ofReal (patternWeight τ E)

/-- The good-event and carried factor after the pivot at column `m` (label replacement). -/
noncomputable def GammaBar (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ℝ≥0∞ :=
  if h : runFirst l m < m then
    (G (lab ⟨m - 1, by omega⟩)).indicator 1 ω *
      PhiC (N := N) J l A Eu (runNum l m) ω (lab ⟨runFirst l m, h⟩)
  else
    (if h1 : 1 ≤ m then (G (lab ⟨m - 1, by omega⟩)).indicator 1 ω else 1) *
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uOf c)) *
      PhiC (N := N) J l A Eu (runNum l m) ω (uOf c)

/-- The dominating term (independent of the label of column `m`). -/
noncomputable def Fbar (m : ℕ) (ω : Ω) (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
    GammaBar J l smax G A Eu m ω lab c *
    (∏ j, invq (J.q (lab j) ω)) * invq t * IzX J E Jw m lab ω c (Real.log t) *
    ENNReal.ofReal (patternWeight τ E)

/-- The adapted integrand at the pivot of column `m` with label `n`. -/
noncomputable def PhiM (m n : ℕ) (x : Ω × ℝ) : ℝ≥0∞ :=
  ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ConsM E l smax (m + 1) (Fin.snoc lab n) c then Ffull J E l τ Jw G A Eu m x.1 lab n c x.2
    else 0

/-- The dominating integrand at the pivot of column `m`. -/
noncomputable def PhiBarM (m : ℕ) (x : Ω × ℝ) : ℝ≥0∞ :=
  ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ∃ n, ConsM E l smax (m + 1) (Fin.snoc lab n) c then
      Fbar J E l τ Jw smax G A Eu m x.1 lab c x.2 else 0

/-- The pending quantity with `m + 1` unprocessed pivots. -/
noncomputable def ZS (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑' lab : Fin (m + 1) → ℕ, ∑ c ∈ contents K N D Dmax X₀,
    if ConsM E l smax (m + 1) lab c then
      (J.A (lab (Fin.last m))).indicator 1 ω *
        Ffull J E l τ Jw G A Eu m ω (Fin.init lab) (lab (Fin.last m)) c (J.q (lab (Fin.last m)) ω)
    else 0

end Defs

/-! ## The pivot step (`hstep`) and the domination (`hdom`) -/

section Steps

variable (J : JitterLaw Ω P θE) {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) (l : List ℕ)
  (τ : Fin K → ℝ) (Jw : Set ℝ) (D Dmax X₀ smax : ℕ) (G : ℕ → Set Ω) (A Eu : ℝ)

/-- **The pivot step**: `ZS m` is the label sum over the column `m`. -/
theorem ZS_eq (m : ℕ) (ω : Ω) :
    ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m ω = ∑' n, (J.A n).indicator
      (fun ω => PhiM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m n (ω, J.q n ω)) ω := by
  unfold ZS
  rw [← (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun n => ?_
  by_cases hA : ω ∈ J.A n
  · rw [Set.indicator_of_mem hA]
    unfold PhiM
    refine tsum_congr fun lab => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ) (n, lab) = Fin.snoc lab n from rfl]
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs
    · rw [Set.indicator_of_mem hA, Pi.one_apply, one_mul]
    · rfl
  · rw [Set.indicator_of_notMem hA]
    refine ENNReal.tsum_eq_zero.mpr fun lab => Finset.sum_eq_zero fun c _ => ?_
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => ℕ) (n, lab) = Fin.snoc lab n from rfl]
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs
    · rw [Set.indicator_of_notMem hA, zero_mul]
    · rfl

variable {J E l τ Jw D Dmax X₀ smax G A Eu}

lemma EuSω_pos (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu) (ω : Ω)
    (u : ℕ) : 0 < EuSω (N := N) J Eu ω u :=
  EuS_pos (fun g hg => hq ω g hg) hEu u

lemma EuSω_mono (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu) (ω : Ω)
    {u u' : ℕ} (h : u ≤ u') : EuSω (N := N) J Eu ω u ≤ EuSω (N := N) J Eu ω u' := by
  unfold EuSω EuS
  refine mul_le_mul_of_nonneg_left ?_ hEu.le
  have hsub : univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u) ⊆
      univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u') := by
    intro g hg
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, by omega⟩
  have hge : ∀ g ∈ univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u'),
      1 ≤ (1 - (J.q g ω)⁻¹)⁻¹ := by
    intro g hg
    have h1 := hq ω g (Finset.mem_filter.mp hg).2.1
    have h2 := one_sub_inv_pos h1
    rw [one_le_inv₀ h2]
    linarith [inv_pos.mpr (show (0 : ℝ) < J.q g ω by linarith)]
  rw [← Finset.prod_sdiff hsub]
  have h1 : 1 ≤ ∏ g ∈ univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u') \
      univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u), (1 - (J.q g ω)⁻¹)⁻¹ := by
    have := Finset.prod_le_prod₀ (s := univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u') \
      univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u)) (f := fun _ => (1 : ℝ))
      (fun _ _ => zero_le_one) (fun g hg => hge g (Finset.mem_sdiff.mp hg).1)
    simpa using this
  have h2 : 0 ≤ ∏ g ∈ univ.filter (fun g : Fin N => ω ∈ J.A g ∧ (g : ℕ) < u),
      (1 - (J.q g ω)⁻¹)⁻¹ := Finset.prod_nonneg fun g hg =>
    (inv_pos.mpr (one_sub_inv_pos (hq ω g (Finset.mem_filter.mp hg).2.1))).le
  nlinarith

/-- `Φ` is non-increasing in the slot. -/
lemma PhiC_anti (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu) (r : ℕ)
    (ω : Ω) {u u' : ℕ} (h : u ≤ u') :
    PhiC (N := N) J l A Eu r ω u' ≤ PhiC (N := N) J l A Eu r ω u := by
  unfold PhiC
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨h0, ha⟩ := GRun_nonneg_antitone A (l.drop (r + 1))
  have hE := EuSω_pos (N := N) hq hEu ω u
  have hE' := EuSω_pos (N := N) hq hEu ω u'
  have hm := EuSω_mono (N := N) hq hEu ω h
  have hG : GRun A (l.drop (r + 1)) (EuSω (N := N) J Eu ω u') ≤
      GRun A (l.drop (r + 1)) (EuSω (N := N) J Eu ω u) := ha hE hE' hm
  exact div_le_div₀ (h0 _ hE) hG (pow_pos hE _) (pow_le_pow_left₀ hE.le hm _)

/-- **Label replacement** (step (i) of Lemma A.5), for the column `m`. -/
lemma gamma_le (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) {m n : ℕ} {lab : Fin m → ℕ}
    {c : Fin K → (Fin N → ℕ) × ℕ} (hC : ConsM E l smax (m + 1) (Fin.snoc lab n) c) (ω : Ω) :
    (G n).indicator 1 ω * PhiC (N := N) J l A Eu (runNum l m) ω
      ((Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) ≤
      GammaBar J l smax G A Eu m ω lab c := by
  obtain ⟨hmono, hlab, hc, -⟩ := hC
  have hlast : (Fin.snoc lab n : Fin (m + 1) → ℕ) (Fin.last m) = n := Fin.snoc_last _ _
  -- the previous label is before `n`
  have hprev : ∀ h : 1 ≤ m, lab ⟨m - 1, by omega⟩ < n := by
    intro h
    have := hmono (show (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) < Fin.last m from
      Fin.castSucc_lt_last _)
    rw [Fin.snoc_castSucc, hlast] at this
    exact this
  unfold GammaBar
  by_cases hω : ω ∈ G n
  · rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul]
    split_ifs with h1 h2
    · have hmem : ω ∈ G (lab ⟨m - 1, by omega⟩) := hG _ _ (hprev (by omega)).le hω
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      have : (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
          (runFirst_le l m)⟩ = lab ⟨runFirst l m, h1⟩ := by
        have := Fin.snoc_castSucc (α := fun _ => ℕ) (p := lab) (x := n) ⟨runFirst l m, h1⟩
        simpa using this
      rw [this]
    all_goals
      have hfirst : runFirst l m = m := le_antisymm (runFirst_le l m) (not_lt.mp h1)
      have hn : (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
          (runFirst_le l m)⟩ = n := by
        rw [← hlast]; congr 1; exact Fin.ext (by simp [hfirst])
      have hu : uOf c ≤ n := by
        rw [uOf_le_iff]
        intro y g hg
        have := (hc y g hg).1 (Nat.succ_pos m)
        simp only [Nat.add_sub_cancel] at this
        rwa [hn] at this
      have hns : n ≤ smax := by
        have := (hlab (Fin.last m)).2; rwa [hlast] at this
      have hchi : chiB smax (fun u => ω ∈ G u) (uOf c) = 1 := by
        unfold chiB; rw [if_pos ⟨hu.trans hns, hG _ _ hu hω⟩]
      rw [hn, hchi, ENNReal.ofReal_one, mul_one]
    · have hmem : ω ∈ G (lab ⟨m - 1, by omega⟩) := hG _ _ (hprev h2).le hω
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      exact PhiC_anti hq hEu _ ω hu
    · rw [one_mul]
      exact PhiC_anti hq hEu _ ω hu
  · rw [Set.indicator_of_notMem hω, zero_mul]; exact zero_le

/-- **Domination** of the adapted integrands by the label-free one. -/
theorem PhiM_le (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hG : ∀ u u', u ≤ u' → G u' ⊆ G u) (m n : ℕ) (x : Ω × ℝ) :
    PhiM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m n x ≤
      PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m x := by
  unfold PhiM PhiBarM
  refine ENNReal.tsum_le_tsum fun lab => Finset.sum_le_sum fun c _ => ?_
  by_cases hC : ConsM E l smax (m + 1) (Fin.snoc lab n) c
  · rw [if_pos hC, if_pos ⟨n, hC⟩]
    unfold Ffull Fbar
    have hγ := gamma_le (A := A) hq hEu hG hC x.1
    calc (∏ j, (J.A (lab j)).indicator 1 x.1) * (decSet J c).indicator 1 x.1 *
          (G n).indicator 1 x.1 *
          PhiC (N := N) J l A Eu (runNum l m) x.1 ((Fin.snoc lab n : Fin (m + 1) → ℕ)
            ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩) *
          (∏ j, invq (J.q (lab j) x.1)) * invq x.2 * IzX J E Jw m lab x.1 c (Real.log x.2) *
          ENNReal.ofReal (patternWeight τ E)
        = (∏ j, (J.A (lab j)).indicator 1 x.1) * (decSet J c).indicator 1 x.1 *
          ((G n).indicator 1 x.1 *
          PhiC (N := N) J l A Eu (runNum l m) x.1 ((Fin.snoc lab n : Fin (m + 1) → ℕ)
            ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩)) *
          (∏ j, invq (J.q (lab j) x.1)) * invq x.2 * IzX J E Jw m lab x.1 c (Real.log x.2) *
          ENNReal.ofReal (patternWeight τ E) := by ring
      _ ≤ _ := by gcongr
  · rw [if_neg hC]; exact zero_le

end Steps

/-! ## Measurability -/

section Meas

lemma measurable_invq : Measurable invq :=
  (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Ioi

lemma measurable_Lcore2 {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ) {Jw : Set ℝ}
    (hJw : MeasurableSet Jw) :
    Measurable fun p : (Fin K → ℝ) × (Fin K → ℝ) => Lcore E Jw p.1 p.2 := by
  unfold Lcore
  refine Finset.measurable_prod _ fun y _ => ?_
  have hr : Measurable fun p : (Fin K → ℝ) × (Fin K → ℝ) => rowLog E p.2 y :=
    Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hr)).mul
    ((measurable_one.indicator hJw).comp
      (((measurable_pi_apply y).comp measurable_fst).mul (Real.measurable_exp.comp hr)))

lemma measurable_mergeL2 {K : ℕ} (i : ℕ) :
    Measurable fun p : (Fin i → ℝ) × (Fin K → ℝ) => mergeL i p.1 p.2 := by
  rw [measurable_pi_iff]
  intro j
  unfold mergeL
  split_ifs
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd

/-- The generic measurability of an integrand `a(ω) · 1(t>0)/t · ∫ L(z, (u(ω), log t)) dz`. -/
lemma measurable_core {α : Type*} [MeasurableSpace α] {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (a : α → ℝ≥0∞) (ha : Measurable a)
    (cv : α → Fin K → ℝ) (hcv : ∀ y, Measurable fun ω => cv ω y) (m : ℕ) (u : α → Fin K → ℝ)
    (hu : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => u ω j) (i : ℕ) :
    Measurable fun x : α × ℝ => a x.1 * invq x.2 * ∫⁻ z : Fin i → ℝ, Lcore E Jw (cv x.1)
      (mergeL i z (fun j => if (j : ℕ) = m then Real.log x.2 else u x.1 j)) := by
  set U : α × ℝ → Fin K → ℝ :=
    fun x j => if (j : ℕ) = m then Real.log x.2 else u x.1 j with hUdef
  have hU : Measurable U := by
    rw [measurable_pi_iff]
    intro j
    simp only [hUdef]
    split_ifs with h
    · exact Real.measurable_log.comp measurable_snd
    · exact (hu j h).comp measurable_fst
  have hcv' : Measurable fun x : α × ℝ => cv x.1 := by
    rw [measurable_pi_iff]; intro y; exact (hcv y).comp measurable_fst
  set F : (α × ℝ) × (Fin i → ℝ) → ℝ≥0∞ :=
    fun p => Lcore E Jw (cv p.1.1) (mergeL i p.2 (U p.1)) with hFdef
  have hF : Measurable F := by
    have h1 : Measurable fun p : (α × ℝ) × (Fin i → ℝ) => (cv p.1.1, mergeL i p.2 (U p.1)) :=
      (hcv'.comp measurable_fst).prodMk
        ((measurable_mergeL2 (K := K) i).comp (measurable_snd.prodMk (hU.comp measurable_fst)))
    have h2 := (measurable_Lcore2 E hJw).comp h1
    exact h2
  have hI : Measurable fun x : α × ℝ => ∫⁻ z : Fin i → ℝ, F (x, z) :=
    Measurable.lintegral_prod_right' hF
  have h3 := ((ha.comp measurable_fst).mul (measurable_invq.comp measurable_snd)).mul hI
  exact h3

lemma measurable_tsum_sum_ite {α ι κ : Type*} [MeasurableSpace α] [Countable ι] (s : Finset κ)
    (p : ι → κ → Prop) (f : ι → κ → α → ℝ≥0∞) (hf : ∀ i k, p i k → Measurable (f i k)) :
    Measurable fun a => ∑' i, ∑ k ∈ s, if p i k then f i k a else 0 := by
  refine Measurable.ennreal_tsum fun i => Finset.measurable_sum _ fun k _ => ?_
  by_cases h : p i k
  · simp only [if_pos h]; exact hf i k h
  · simp only [if_neg h]; exact measurable_const

end Meas

section MeasGen

variable {α : Type*} [MeasurableSpace α]

lemma measurable_EuS_gen (okS : Fin N → Set α) (qf : Fin N → α → ℝ) (Eu : ℝ) (u : ℕ)
    (hok : ∀ g : Fin N, (g : ℕ) < u → MeasurableSet (okS g))
    (hqf : ∀ g : Fin N, (g : ℕ) < u → Measurable (qf g)) :
    Measurable fun a => EuS (fun g => a ∈ okS g) (fun g => qf g a) Eu u := by
  have : (fun a => EuS (fun g => a ∈ okS g) (fun g => qf g a) Eu u) = fun a =>
      Eu * ∏ g ∈ univ.filter (fun g : Fin N => (g : ℕ) < u),
        (if a ∈ okS g then (1 - (qf g a)⁻¹)⁻¹ else 1) := by
    funext a
    unfold EuS
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_filter]
    congr 1
    ext g; simp [and_comm]
  rw [this]
  refine measurable_const.mul (Finset.measurable_prod _ fun g hg => ?_)
  have hgu := (Finset.mem_filter.mp hg).2
  exact Measurable.ite (hok g hgu) (((hqf g hgu).inv.const_sub 1).inv) measurable_const

lemma EuS_ge (ok : Fin N → Prop) (q : Fin N → ℝ) (hq : ∀ g, ok g → 1 < q g) {Eu : ℝ}
    (hEu : 0 < Eu) (u : ℕ) : Eu ≤ EuS ok q Eu u := by
  unfold EuS
  have h1 : 1 ≤ ∏ g ∈ univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < u), (1 - (q g)⁻¹)⁻¹ := by
    have := Finset.prod_le_prod₀ (s := univ.filter (fun g : Fin N => ok g ∧ (g : ℕ) < u))
      (f := fun _ => (1 : ℝ)) (g := fun g => (1 - (q g)⁻¹)⁻¹) (fun _ _ => zero_le_one)
      (fun g hg => by
        have h1 := hq g (Finset.mem_filter.mp hg).2.1
        have h2 := one_sub_inv_pos h1
        rw [one_le_inv₀ h2]
        linarith [inv_pos.mpr (show (0 : ℝ) < q g by linarith)])
    simpa using this
  nlinarith

lemma measurable_PhiC_gen (okS : Fin N → Set α) (qf : Fin N → α → ℝ)
    (hq : ∀ a g, a ∈ okS g → 1 < qf g a) {Eu : ℝ} (hEu : 0 < Eu) (u : ℕ)
    (hok : ∀ g : Fin N, (g : ℕ) < u → MeasurableSet (okS g))
    (hqf : ∀ g : Fin N, (g : ℕ) < u → Measurable (qf g)) (A : ℝ) (l' : List ℕ) (k : ℕ) :
    Measurable fun a => ENNReal.ofReal
      (GRun A l' (EuS (fun g => a ∈ okS g) (fun g => qf g a) Eu u) /
        EuS (fun g => a ∈ okS g) (fun g => qf g a) Eu u ^ k) := by
  set e := fun a => EuS (fun g => a ∈ okS g) (fun g => qf g a) Eu u with he
  have hem : Measurable e := measurable_EuS_gen okS qf Eu u hok hqf
  have hge : ∀ a, Eu ≤ e a := fun a => EuS_ge _ _ (fun g hg => hq a g hg) hEu u
  obtain ⟨-, hanti⟩ := GRun_nonneg_antitone A l'
  set Gt : ℝ → ℝ := fun E => GRun A l' (max E Eu) with hGt
  have hGtA : Antitone Gt := by
    intro x y hxy
    simp only [hGt]
    exact hanti (show (0 : ℝ) < max x Eu from lt_max_of_lt_right hEu)
      (show (0 : ℝ) < max y Eu from lt_max_of_lt_right hEu) (max_le_max hxy le_rfl)
  have heq : (fun a => GRun A l' (e a)) = fun a => Gt (e a) := by
    funext a; simp only [hGt, max_eq_left (hge a)]
  have h1 : Measurable fun a => GRun A l' (e a) := by
    rw [heq]; exact hGtA.measurable.comp hem
  exact ENNReal.measurable_ofReal.comp (h1.div (hem.pow_const k))

lemma measurable_mul5 {f₁ f₂ f₃ f₄ f₅ : α → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    (h₃ : Measurable f₃) (h₄ : Measurable f₄) (h₅ : Measurable f₅) :
    Measurable fun a => f₁ a * f₂ a * f₃ a * f₄ a * f₅ a :=
  (((h₁.mul h₂).mul h₃).mul h₄).mul h₅

lemma measurable_prod_ind {ι : Type*} [Fintype ι] (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i)) :
    Measurable fun a => ∏ i, (S i).indicator (1 : α → ℝ≥0∞) a :=
  Finset.measurable_prod _ fun i _ => measurable_one.indicator (hS i)

lemma measurable_prod_invq {ι : Type*} [Fintype ι] (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => ∏ i, invq (f i a) :=
  Finset.measurable_prod _ fun i _ => measurable_invq.comp (hf i)

lemma measurable_ind (S : Set α) (hS : MeasurableSet S) :
    Measurable (S.indicator (1 : α → ℝ≥0∞)) := measurable_one.indicator hS

lemma measurable_core' {K : ℕ} (E : Matrix (Fin K) (Fin K) ℕ)
    {Jw : Set ℝ} (hJw : MeasurableSet Jw) (a : α → ℝ≥0∞) (ha : Measurable a)
    (cv : α → Fin K → ℝ) (hcv : ∀ y, Measurable fun ω => cv ω y) (m : ℕ) (u : α → Fin K → ℝ)
    (hu : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => u ω j) (i : ℕ) (W : ℝ≥0∞) :
    Measurable fun x : α × ℝ => a x.1 * invq x.2 * (∫⁻ z : Fin i → ℝ, Lcore E Jw (cv x.1)
      (mergeL i z (fun j => if (j : ℕ) = m then Real.log x.2 else u x.1 j))) * W :=
  (measurable_core E hJw a ha cv hcv m u hu i).mul_const W

end MeasGen

section MeasSpecific

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma uvecX_eq (m : ℕ) (lab : Fin m → ℕ) (ω : Ω) (x : ℝ) :
    uvecX (K := K) J m lab ω x = fun j : Fin K => if (j : ℕ) = m then x else
      (if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0) := by
  funext j
  unfold uvecX
  by_cases h1 : (j : ℕ) < m
  · rw [dif_pos h1, if_neg (by omega), dif_pos h1]
  · rw [dif_neg h1, dif_neg h1]

/-- The facts used for the adaptedness, from the constraints. -/
lemma cons_facts {m n : ℕ} {lab : Fin m → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hC : ConsM E l smax (m + 1) (Fin.snoc lab n) c) :
    (∀ j, lab j < n) ∧ uOf c ≤ n ∧
      (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩ ≤ n
      := by
  obtain ⟨hmono, -, hc, -⟩ := hC
  have hlast : (Fin.snoc lab n : Fin (m + 1) → ℕ) (Fin.last m) = n := Fin.snoc_last _ _
  have hle : ∀ j : Fin (m + 1), (Fin.snoc lab n : Fin (m + 1) → ℕ) j ≤ n := fun j =>
    (hmono.monotone (Fin.le_last j)).trans hlast.le
  refine ⟨fun j => ?_, ?_, hle _⟩
  · have := hmono (Fin.castSucc_lt_last j)
    rw [Fin.snoc_castSucc, hlast] at this; exact this
  · rw [uOf_le_iff]
    intro y g hg
    have := (hc y g hg).1 (Nat.succ_pos m)
    simp only [Nat.add_sub_cancel] at this
    exact lt_of_lt_of_le this (hle _)

/-- **Adaptedness** of the integrand at the pivot of column `m` with label `n`. -/
theorem PhiM_jmeas (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hJw : MeasurableSet Jw) (m n : ℕ) :
    JMeas (J.F n) (PhiM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m n) := by
  unfold JMeas PhiM
  refine @measurable_tsum_sum_ite (Ω × ℝ) _ _ (@Prod.instMeasurableSpace Ω ℝ (J.F n) _) _
    (contents K N D Dmax X₀) _ _ ?_
  intro lab c hC
  obtain ⟨hlab, hu, hu0⟩ := cons_facts hC
  set u0 := (Fin.snoc lab n : Fin (m + 1) → ℕ) ⟨runFirst l m, Nat.lt_succ_of_le
    (runFirst_le l m)⟩ with hu0def
  set a : Ω → ℝ≥0∞ := fun ω => (∏ j, (J.A (lab j)).indicator 1 ω) *
    (decSet J c).indicator 1 ω * (G n).indicator 1 ω *
    PhiC (N := N) J l A Eu (runNum l m) ω u0 * (∏ j, invq (J.q (lab j) ω)) with ha
  set uu : Ω → Fin K → ℝ := fun ω j =>
    if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0 with huu
  have hform : (fun x : Ω × ℝ => Ffull J E l τ Jw G A Eu m x.1 lab n c x.2) = fun x =>
      a x.1 * invq x.2 * (∫⁻ z : Fin (K - (m + 1)) → ℝ, Lcore E Jw (cvs J x.1 c)
        (mergeL (K - (m + 1)) z (fun j => if (j : ℕ) = m then Real.log x.2 else uu x.1 j))) *
        ENNReal.ofReal (patternWeight τ E) := by
    funext x
    simp only [Ffull, IzX, uvecX_eq, ha, huu, hu0def]
  rw [hform]
  have hFn : ∀ g, (g : ℕ) < n → J.F (g + 1) ≤ J.F n := fun g hg => J.F_mono (by omega)
  have hqm : ∀ g : ℕ, g < n → Measurable[J.F n] (J.q g) := fun g hg =>
    (J.q_meas g).mono (hFn g hg) le_rfl
  have hAm : ∀ g : ℕ, g ≤ n → MeasurableSet[J.F n] (J.A g) := fun g hg =>
    J.F_mono hg _ (J.A_meas g)
  have ha_m : Measurable[J.F n] a := by
    refine @measurable_mul5 Ω (J.F n) _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · exact @measurable_prod_ind Ω (J.F n) _ _ (fun j => J.A (lab j))
        (fun j => hAm _ (hlab j).le)
    · exact @measurable_ind Ω (J.F n) _ (J.F_mono hu _ (measurableSet_decSet J c _ le_rfl))
    · exact @measurable_ind Ω (J.F n) _ (hGm n)
    · exact @measurable_PhiC_gen N Ω (J.F n) (fun g => J.A g) (fun g ω => J.q g ω)
        (fun ω g h => hq ω g h) Eu hEu u0 (fun g hg => hAm _ (by omega))
        (fun g hg => hqm _ (by omega)) A _ _
    · exact @measurable_prod_invq Ω (J.F n) _ _ (fun j ω => J.q (lab j) ω)
        (fun j => hqm _ (hlab j))
  have hcv : ∀ y, Measurable[J.F n] fun ω => cvs J ω c y := by
    intro y
    have : (fun ω => cvs J ω c y) = fun ω => cvalLt J n ω (c y) := by
      funext ω; simp only [cvs]; rw [cvalLt_eq hu y]
    rw [this]
    exact @measurable_cvalLt N Ω (J.F n) (fun g ω => J.q g ω) n
      (fun g hg => hqm _ hg) (c y)
  have hum : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable[J.F n] fun ω => uu ω j := by
    intro j _
    simp only [huu]
    split_ifs with h
    · exact @Measurable.comp Ω ℝ ℝ (J.F n) _ _ _ _ Real.measurable_log (hqm _ (hlab _))
    · exact @measurable_const ℝ Ω _ (J.F n) 0
  exact @measurable_core' Ω (J.F n) K E Jw hJw a ha_m (fun ω => cvs J ω c) hcv m uu hum
    (K - (m + 1)) _

lemma measurable_PhiC (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (r u : ℕ) : Measurable fun ω => PhiC (N := N) J l A Eu r ω u :=
  measurable_PhiC_gen (fun g => J.A g) (fun g ω => J.q g ω) (fun ω g h => hq ω g h) hEu u
    (fun g _ => J.A_meas' _) (fun g _ => J.q_meas' _) A _ _

lemma measurable_GammaBar (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (m : ℕ) (lab : Fin m → ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) :
    Measurable fun ω => GammaBar J l smax G A Eu m ω lab c := by
  have hG' : ∀ u, MeasurableSet (G u) := fun u => J.F_le u _ (hGm u)
  unfold GammaBar
  split_ifs with h h1
  · exact (measurable_ind _ (hG' _)).mul (measurable_PhiC hq hEu _ _)
  · refine ((measurable_ind _ (hG' _)).mul ?_).mul (measurable_PhiC hq hEu _ _)
    refine ENNReal.measurable_ofReal.comp ?_
    unfold chiB
    by_cases hs : uOf c ≤ smax
    · have : (fun ω => if uOf c ≤ smax ∧ ω ∈ G (uOf c) then (1 : ℝ) else 0) =
          (G (uOf c)).indicator 1 := by
        funext ω; by_cases hω : ω ∈ G (uOf c) <;> simp [hs, hω]
      rw [this]; exact measurable_one.indicator (hG' _)
    · simp only [hs, false_and, if_false]; exact measurable_const
  · refine (measurable_const.mul ?_).mul (measurable_PhiC hq hEu _ _)
    refine ENNReal.measurable_ofReal.comp ?_
    unfold chiB
    by_cases hs : uOf c ≤ smax
    · have : (fun ω => if uOf c ≤ smax ∧ ω ∈ G (uOf c) then (1 : ℝ) else 0) =
          (G (uOf c)).indicator 1 := by
        funext ω; by_cases hω : ω ∈ G (uOf c) <;> simp [hs, hω]
      rw [this]; exact measurable_one.indicator (hG' _)
    · simp only [hs, false_and, if_false]; exact measurable_const

/-- The dominating integrand is measurable. -/
theorem PhiBarM_meas (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hJw : MeasurableSet Jw) (m : ℕ) :
    Measurable (PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m) := by
  unfold PhiBarM
  refine measurable_tsum_sum_ite (contents K N D Dmax X₀) _ _ ?_
  intro lab c _
  set a : Ω → ℝ≥0∞ := fun ω => (∏ j, (J.A (lab j)).indicator 1 ω) *
    (decSet J c).indicator 1 ω * GammaBar J l smax G A Eu m ω lab c *
      (∏ j, invq (J.q (lab j) ω)) with ha
  set uu : Ω → Fin K → ℝ := fun ω j =>
    if h : (j : ℕ) < m then Real.log (J.q (lab ⟨j, h⟩) ω) else 0 with huu
  have hform : (fun x : Ω × ℝ => Fbar J E l τ Jw smax G A Eu m x.1 lab c x.2) = fun x =>
      a x.1 * invq x.2 * (∫⁻ z : Fin (K - (m + 1)) → ℝ, Lcore E Jw (cvs J x.1 c)
        (mergeL (K - (m + 1)) z (fun j => if (j : ℕ) = m then Real.log x.2 else uu x.1 j))) *
        ENNReal.ofReal (patternWeight τ E) := by
    funext x
    simp only [Fbar, IzX, uvecX_eq, ha, huu]
  rw [hform]
  have ha_m : Measurable a := by
    refine (((measurable_prod_ind _ fun j => J.A_meas' _).mul
      (measurable_ind _ (J.F_le _ _ (measurableSet_decSet J c _ le_rfl)))).mul
      (measurable_GammaBar hq hEu hGm m lab c)).mul ?_
    exact measurable_prod_invq _ fun j => J.q_meas' _
  have hcv : ∀ y, Measurable fun ω => cvs J ω c y := by
    intro y
    unfold cvs cval
    exact measurable_const.mul (Finset.measurable_prod _ fun g _ => (J.q_meas' _).pow_const _)
  have hum : ∀ j : Fin K, (j : ℕ) ≠ m → Measurable fun ω => uu ω j := by
    intro j _
    simp only [huu]
    split_ifs with h
    · exact Real.measurable_log.comp (J.q_meas' _)
    · exact measurable_const
  exact measurable_core' E hJw a ha_m (fun ω => cvs J ω c) hcv m uu hum (K - (m + 1)) _

end MeasSpecific

/-! ## The integral over the current pivot -/

section Integral

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma mergeL_cons {m p : ℕ} (hK : K = m + 1 + p) (x : ℝ) (z : Fin p → ℝ) (lab : Fin m → ℕ)
    (ω : Ω) : mergeL (K := K) (p + 1) (Fin.cons x z) (uvec J m lab ω) =
      mergeL (K := K) p z (uvecX J m lab ω x) := by
  funext j
  unfold mergeL uvec uvecX
  by_cases h1 : m + 1 ≤ (j : ℕ)
  · rw [dif_pos (by omega), dif_pos (by omega)]
    have : (⟨(j : ℕ) - (K - (p + 1)), by omega⟩ : Fin (p + 1)) =
        Fin.succ ⟨(j : ℕ) - (K - p), by omega⟩ := Fin.ext (by simp; omega)
    rw [this, Fin.cons_succ]
  · by_cases h2 : (j : ℕ) = m
    · have a1 : K - (p + 1) ≤ (j : ℕ) := by omega
      have a2 : ¬ (K - p ≤ (j : ℕ)) := by omega
      have a3 : ¬ ((j : ℕ) < m) := by omega
      rw [dif_pos a1, dif_neg a2, dif_neg a3, if_pos h2]
      have : (⟨(j : ℕ) - (K - (p + 1)), by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp; omega)
      rw [this, Fin.cons_zero]
    · have h3 : (j : ℕ) < m := by omega
      have a1 : ¬ (K - (p + 1) ≤ (j : ℕ)) := by omega
      have a2 : ¬ (K - p ≤ (j : ℕ)) := by omega
      rw [dif_neg a1, dif_neg a2, dif_pos h3, dif_pos h3]

lemma measurable_IzX (hJw : MeasurableSet Jw) (m : ℕ) (lab : Fin m → ℕ) (ω : Ω)
    (c : Fin K → (Fin N → ℕ) × ℕ) : Measurable fun x => IzX J E Jw m lab ω c x := by
  unfold IzX
  have hU : Measurable fun x : ℝ => uvecX (K := K) J m lab ω x := by
    rw [measurable_pi_iff]; intro j
    unfold uvecX
    split_ifs
    · exact measurable_const
    · exact measurable_id
    · exact measurable_const
  have hF : Measurable fun p : ℝ × (Fin (K - (m + 1)) → ℝ) =>
      Lcore E Jw (cvs J ω c) (mergeL (K - (m + 1)) p.2 (uvecX J m lab ω p.1)) := by
    have h1 : Measurable fun p : ℝ × (Fin (K - (m + 1)) → ℝ) =>
        (cvs J ω c, mergeL (K - (m + 1)) p.2 (uvecX J m lab ω p.1)) :=
      measurable_const.prodMk ((measurable_mergeL2 (K := K) _).comp
        (measurable_snd.prodMk (hU.comp measurable_fst)))
    have h2 := (measurable_Lcore2 E hJw).comp h1
    exact h2
  exact hF.lintegral_prod_right'

/-- The integral over the current pivot (in log coordinates) adds it to the processed pivots. -/
lemma lintegral_IzX (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (lab : Fin m → ℕ)
    (ω : Ω) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ∫⁻ t, invq t * IzX J E Jw m lab ω c (Real.log t) = IzM J E Jw m lab ω c := by
  have h1 : (fun t => invq t * IzX J E Jw m lab ω c (Real.log t)) =
      (Set.Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹ * IzX J E Jw m lab ω c
        (Real.log t)) := by
    funext t
    unfold invq
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [h1, lintegral_log_subst]
  obtain ⟨p, hp⟩ : ∃ p, K = m + 1 + p := ⟨K - (m + 1), by omega⟩
  have hKm : K - m = p + 1 := by omega
  have hKm1 : K - (m + 1) = p := by omega
  unfold IzM IzX
  rw [hKm, hKm1]
  have hmeas : Measurable fun s : Fin (p + 1) → ℝ =>
      Lcore E Jw (cvs J ω c) (mergeL (K := K) (p + 1) s (uvec J m lab ω)) :=
    (measurable_Lcore E hJw _).comp (measurable_mergeL _ _)
  rw [lintegral_fin_succ _ hmeas]
  refine lintegral_congr fun x => lintegral_congr fun z => ?_
  rw [mergeL_cons hp]

lemma measurable_Fbar_t (hJw : MeasurableSet Jw) (m : ℕ) (ω : Ω) (lab : Fin m → ℕ)
    (c : Fin K → (Fin N → ℕ) × ℕ) :
    Measurable fun t => Fbar J E l τ Jw smax G A Eu m ω lab c t := by
  unfold Fbar
  exact (((measurable_const.mul (measurable_invq)).mul
    ((measurable_IzX hJw m lab ω c).comp Real.measurable_log)).mul measurable_const)

lemma lintegral_Fbar (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (ω : Ω)
    (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    ∫⁻ t, Fbar J E l τ Jw smax G A Eu m ω lab c t =
      (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
        GammaBar J l smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) *
        IzM J E Jw m lab ω c * ENNReal.ofReal (patternWeight τ E) := by
  set a := (∏ j, (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω) * (decSet J c).indicator 1 ω *
    GammaBar J l smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) with ha
  have : (fun t => Fbar J E l τ Jw smax G A Eu m ω lab c t) = fun t =>
      (a * ENNReal.ofReal (patternWeight τ E)) * (invq t * IzX J E Jw m lab ω c (Real.log t)) := by
    funext t; simp only [Fbar, ha]; ring
  have hf : Measurable fun t => invq t * IzX J E Jw m lab ω c (Real.log t) :=
    measurable_invq.mul ((measurable_IzX hJw m lab ω c).comp Real.measurable_log)
  rw [this, lintegral_const_mul _ hf, lintegral_IzX hJw hm, ha]
  ring

/-- `∫ Φ̄_m(ω, t) dt` as a sum over the labels and contents. -/
lemma lintegral_PhiBarM (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 1 ≤ K) (ω : Ω) :
    ∫⁻ t, PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m (ω, t) =
      ∑' lab : Fin m → ℕ, ∑ c ∈ contents K N D Dmax X₀,
        if ∃ n, ConsM E l smax (m + 1) (Fin.snoc lab n) c then
          (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
            GammaBar J l smax G A Eu m ω lab c * (∏ j, invq (J.q (lab j) ω)) *
            IzM J E Jw m lab ω c * ENNReal.ofReal (patternWeight τ E)
        else 0 := by
  unfold PhiBarM
  have hterm : ∀ (lab : Fin m → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ), Measurable fun t =>
      (if ∃ n, ConsM E l smax (m + 1) (Fin.snoc lab n) c then
        Fbar J E l τ Jw smax G A Eu m ω lab c t else 0) := by
    intro lab c
    split_ifs
    · exact measurable_Fbar_t hJw m ω lab c
    · exact measurable_const
  rw [lintegral_tsum fun lab => (Finset.measurable_sum _ fun c _ => hterm lab c).aemeasurable]
  refine tsum_congr fun lab => ?_
  rw [lintegral_finset_sum _ fun c _ => hterm lab c]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · exact lintegral_Fbar hJw hm ω lab c
  · exact lintegral_zero

end Integral

/-! ## The step at a pivot which is not the last of its run -/

section NonLast

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma SpanSet_mono {P P' : Set (Fin K)} (h : P ⊆ P') : SpanSet E P ⊆ SpanSet E P' := by
  rintro w ⟨v, hv0, hv⟩
  exact ⟨v, fun j hj => hv0 j fun hjP => hj (h hjP), hv⟩

/-- The constraints pass to the next level inside a run. -/
lemma cons_nonlast {m n : ℕ} {lab : Fin m → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hnl : runFirst l m < m) (hC : ConsM E l smax (m + 1) (Fin.snoc lab n) c) :
    ConsM E l smax m lab c := by
  obtain ⟨hmono, hlab, hc, h7⟩ := hC
  have hsc : ∀ j : Fin m, (Fin.snoc lab n : Fin (m + 1) → ℕ) (Fin.castSucc j) = lab j :=
    fun j => Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _
  refine ⟨fun a b hab => ?_, fun j => ?_, fun y g hg => ?_, fun j hj1 hj2 => ?_⟩
  · have := hmono (Fin.castSucc_lt_castSucc_iff.mpr hab); rwa [hsc, hsc] at this
  · have := hlab (Fin.castSucc j); rwa [hsc] at this
  · obtain ⟨h4, h5, h6⟩ := hc y g hg
    refine ⟨fun hm => ?_, fun j j' hjj => ?_, ?_⟩
    · have := h4 (Nat.succ_pos m)
      simp only [Nat.add_sub_cancel] at this
      have hrf := (runNum_pred_of_not_first l hnl).2
      have e1 : (⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩ : Fin (m + 1)) =
          Fin.castSucc ⟨runFirst l m, hnl⟩ := rfl
      rw [e1, hsc] at this
      have e2 : (⟨runFirst l (m - 1), lt_of_le_of_lt (runFirst_le l (m - 1)) (by omega)⟩ :
          Fin m) = ⟨runFirst l m, hnl⟩ := Fin.ext hrf
      rw [e2]; exact this
    · have := h5 (Fin.castSucc j) (Fin.castSucc j') hjj
      rwa [hsc, hsc] at this
    · refine SpanSet_mono (fun j hj => ?_) h6
      rcases hj with hj | ⟨hjm, hgj⟩
      · exact Or.inl (by omega)
      · by_cases hjm' : (j : ℕ) < m
        · refine Or.inr ⟨hjm', ?_⟩
          have e : (⟨j, hjm⟩ : Fin (m + 1)) = Fin.castSucc ⟨j, hjm'⟩ := rfl
          rw [e, hsc] at hgj; exact hgj
        · exact Or.inl (by omega)
  · obtain ⟨y, g, hg, h1, h2⟩ := h7 (Fin.castSucc j) hj1 hj2
    refine ⟨y, g, hg, ?_, ?_⟩
    · have e : (⟨(Fin.castSucc j : ℕ) - 1, by simp; omega⟩ : Fin (m + 1)) =
          Fin.castSucc ⟨(j : ℕ) - 1, by omega⟩ := rfl
      rw [e, hsc] at h1; exact h1
    · rwa [hsc] at h2

lemma uvecX_init (m : ℕ) (lab : Fin (m + 1) → ℕ) (ω : Ω) :
    uvecX (K := K) J m (Fin.init lab) ω (Real.log (J.q (lab (Fin.last m)) ω)) =
      uvec J (m + 1) lab ω := by
  funext j
  unfold uvecX uvec
  by_cases h1 : (j : ℕ) < m
  · rw [dif_pos h1, dif_pos (by omega)]; rfl
  · rw [dif_neg h1]
    by_cases h2 : (j : ℕ) = m
    · rw [if_pos h2, dif_pos (by omega)]
      congr 3; exact Fin.ext (by simp [h2])
    · rw [if_neg h2, dif_neg (by omega)]

/-- **The step at a pivot which is not the last of its run** (Fubini only). -/
theorem hnext_nonlast (hJw : MeasurableSet Jw) {m : ℕ} (hm : m + 2 ≤ K)
    (hnl : runFirst l (m + 1) < m + 1) (ω : Ω) :
    ∫⁻ t, PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (m + 1) (ω, t) ≤
      ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m ω := by
  rw [lintegral_PhiBarM hJw (by omega)]
  unfold ZS
  refine ENNReal.tsum_le_tsum fun lab => Finset.sum_le_sum fun c _ => ?_
  by_cases hC : ∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c
  · obtain ⟨n, hn⟩ := hC
    have hC' := cons_nonlast hnl hn
    rw [if_pos ⟨n, hn⟩, if_pos hC']
    refine le_of_eq ?_
    unfold Ffull GammaBar
    rw [dif_pos hnl]
    have hrn := runNum_pred_of_not_first l hnl
    simp only [Nat.add_sub_cancel] at hrn
    have e1 : (Fin.snoc (Fin.init lab) (lab (Fin.last m)) : Fin (m + 1) → ℕ) = lab :=
      Fin.snoc_init_self lab
    have e2 : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    rw [e1, e2, hrn.1]
    have e3 : ∀ h, lab ⟨runFirst l m, h⟩ = lab ⟨runFirst l (m + 1), hnl⟩ :=
      fun h => congrArg lab (Fin.ext hrn.2)
    simp only [e3]
    have hIz : IzX J E Jw m (Fin.init lab) ω c (Real.log (J.q (lab (Fin.last m)) ω)) =
        IzM J E Jw (m + 1) lab ω c := by
      unfold IzX IzM; rw [uvecX_init]
    rw [hIz, Fin.prod_univ_castSucc (fun j => (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω),
      Fin.prod_univ_castSucc (fun j => invq (J.q (lab j) ω))]
    simp only [Fin.init]
    ring
  · rw [if_neg hC]; exact zero_le

end NonLast

/-! ## Splitting a content at a slot -/

section Split

variable {K : ℕ}

/-- The part of a content before slot `b0` (with the tails). -/
def loC (b0 : ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) : Fin K → (Fin N → ℕ) × ℕ :=
  fun y => (fun g => if (g : ℕ) < b0 then (c y).1 g else 0, (c y).2)

/-- The part of a content after slot `b0` (the block). -/
def hiC (b0 : ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) : Fin K → Fin N → ℕ :=
  fun y g => if b0 < (g : ℕ) then (c y).1 g else 0

lemma split_inj {b0 : ℕ} {c c' : Fin K → (Fin N → ℕ) × ℕ}
    (hc : ∀ y g, (c y).1 g ≠ 0 → (g : ℕ) ≠ b0) (hc' : ∀ y g, (c' y).1 g ≠ 0 → (g : ℕ) ≠ b0)
    (hlo : loC b0 c = loC b0 c') (hhi : hiC b0 c = hiC b0 c') : c = c' := by
  funext y
  have h1 := congrFun hlo y
  ext g
  · have hl := congrFun (congrArg Prod.fst h1) g
    have hh := congrFun (congrFun hhi y) g
    simp only [loC, hiC] at hl hh
    by_cases hlt : (g : ℕ) < b0
    · rw [if_pos hlt, if_pos hlt] at hl; exact hl
    · by_cases hgt : b0 < (g : ℕ)
      · rw [if_pos hgt, if_pos hgt] at hh; exact hh
      · have heq : (g : ℕ) = b0 := by omega
        have e1 : (c y).1 g = 0 := by by_contra h; exact hc y g h heq
        have e2 : (c' y).1 g = 0 := by by_contra h; exact hc' y g h heq
        rw [e1, e2]
  · have := congrArg Prod.snd h1
    simpa [loC] using this

lemma cval_split (q : Fin N → ℝ) {b0 : ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hc : ∀ y g, (c y).1 g ≠ 0 → (g : ℕ) ≠ b0) (y : Fin K) :
    cval q (c y) = cval q (loC b0 c y) * ∏ g ∈ suppW (hiC b0 c), q g ^ (hiC b0 c y g) := by
  unfold cval
  have hsplit : ∀ g, q g ^ (c y).1 g = q g ^ (loC b0 c y).1 g * q g ^ (hiC b0 c y g) := by
    intro g
    rw [← pow_add]
    congr 1
    simp only [loC, hiC]
    by_cases hlt : (g : ℕ) < b0
    · rw [if_pos hlt, if_neg (by omega), add_zero]
    · by_cases hgt : b0 < (g : ℕ)
      · rw [if_neg hlt, if_pos hgt, zero_add]
      · have heq : (g : ℕ) = b0 := by omega
        have e1 : (c y).1 g = 0 := by by_contra h; exact hc y g h heq
        rw [if_neg hlt, if_neg hgt, e1]
  rw [Finset.prod_congr rfl fun g _ => hsplit g, Finset.prod_mul_distrib]
  have hhi : ∏ g, q g ^ (hiC b0 c y g) = ∏ g ∈ suppW (hiC b0 c), q g ^ (hiC b0 c y g) := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
    have : hiC b0 c y g = 0 := by
      by_contra h; exact hg (mem_suppW.mpr ⟨y, h⟩)
    rw [this, pow_zero]
  rw [hhi]
  simp only [loC]
  ring

lemma prod_inv_eq_supp (q : Fin N → ℝ) (W : Fin K → Fin N → ℕ) :
    ∏ g, (q g)⁻¹ ^ (∑ y, W y g) = ∏ g ∈ suppW W, (q g)⁻¹ ^ (∑ y, W y g) := by
  refine (Finset.prod_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
  have : ∑ y, W y g = 0 := Finset.sum_eq_zero fun y _ => by
    by_contra h; exact hg (mem_suppW.mpr ⟨y, h⟩)
  rw [this, pow_zero]

end Split

/-! ## The constraints at the last pivot of a run -/

section LastCons

variable {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ} {smax : ℕ}

variable {m n : ℕ} {lab : Fin (m + 1) → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}

lemma snoc_cs (j : Fin (m + 1)) :
    (Fin.snoc lab n : Fin (m + 1 + 1) → ℕ) (Fin.castSucc j) = lab j :=
  Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _

lemma last_ne (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) :
    ∀ y g, (c y).1 g ≠ 0 → (g : ℕ) ≠ lab (Fin.last m) := by
  intro y g hg heq
  have h5 := ((hC.2.2.1 y g hg).2.1) (Fin.castSucc (Fin.last m)) (Fin.castSucc (Fin.last m)) rfl
  rw [snoc_cs] at h5
  exact h5 ⟨heq.symm.le, heq.le⟩

lemma last_lo (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) :
    ConsM E l smax (m + 1) lab (loC (lab (Fin.last m)) c) := by
  obtain ⟨hmono, hlab, hc, h7⟩ := hC
  refine ⟨fun a b hab => ?_, fun j => ?_, fun y g hg => ?_, fun j hj1 hj2 => ?_⟩
  · have := hmono (Fin.castSucc_lt_castSucc_iff.mpr hab); rwa [snoc_cs, snoc_cs] at this
  · have := hlab (Fin.castSucc j); rwa [snoc_cs] at this
  · simp only [loC] at hg
    by_cases hlt : (g : ℕ) < lab (Fin.last m)
    · rw [if_pos hlt] at hg
      obtain ⟨-, h5, h6⟩ := hc y g hg
      refine ⟨fun _ => ?_, fun j j' hjj => ?_, ?_⟩
      · -- before the first label of the run of column `m`
        have hrun := runNum_eq_of_between l (j := m) (j' := runFirst l m) le_rfl
          (runFirst_le l m)
        have := h5 (Fin.castSucc ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩)
          (Fin.castSucc (Fin.last m)) (by simpa using hrun.1)
        rw [snoc_cs, snoc_cs] at this
        simp only [Nat.add_sub_cancel]
        by_contra hge
        push_neg at hge
        exact this ⟨hge, hlt.le⟩
      · have := h5 (Fin.castSucc j) (Fin.castSucc j') (by simpa using hjj)
        rwa [snoc_cs, snoc_cs] at this
      · have hcol : colC (loC (lab (Fin.last m)) c) g = colC c g := by
          funext y'; simp [colC, loC, hlt]
        rw [hcol]
        refine SpanSet_mono (fun j hj => ?_) h6
        rcases hj with hj | ⟨hjm, hgj⟩
        · exact Or.inl (by omega)
        · by_cases hjm' : (j : ℕ) < m + 1
          · refine Or.inr ⟨hjm', ?_⟩
            have e : (⟨j, hjm⟩ : Fin (m + 1 + 1)) = Fin.castSucc ⟨j, hjm'⟩ := rfl
            rw [e, snoc_cs] at hgj; exact hgj
          · exact Or.inl (by omega)
    · rw [if_neg hlt] at hg; exact absurd rfl hg
  · obtain ⟨y, g, hg, h1, h2⟩ := h7 (Fin.castSucc j) hj1 hj2
    refine ⟨y, g, ?_, ?_, ?_⟩
    · have hgl : (g : ℕ) < lab (Fin.last m) := by
        rw [snoc_cs] at h2
        have hmo := hmono.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
        rw [snoc_cs, snoc_cs] at hmo
        exact lt_of_lt_of_le h2 hmo
      simp only [loC, if_pos hgl]; exact hg
    · have e : (⟨(Fin.castSucc j : ℕ) - 1, by simp; omega⟩ : Fin (m + 1 + 1)) =
          Fin.castSucc ⟨(j : ℕ) - 1, by omega⟩ := rfl
      rw [e, snoc_cs] at h1; exact h1
    · rwa [snoc_cs] at h2

lemma mem_suppW_hiC {b0 : ℕ} {g : Fin N} :
    g ∈ suppW (hiC b0 c) ↔ b0 < (g : ℕ) ∧ ∃ y, (c y).1 g ≠ 0 := by
  rw [mem_suppW]
  simp only [hiC]
  constructor
  · rintro ⟨y, hy⟩
    by_cases h : b0 < (g : ℕ)
    · rw [if_pos h] at hy; exact ⟨h, y, hy⟩
    · rw [if_neg h] at hy; exact absurd rfl hy
  · rintro ⟨h, y, hy⟩; exact ⟨y, by rw [if_pos h]; exact hy⟩

lemma last_hi_ne (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) :
    (suppW (hiC (lab (Fin.last m)) c)).Nonempty := by
  obtain ⟨y, g, hg, h1, -⟩ := hC.2.2.2 (Fin.last (m + 1)) (by simp) (by simpa using hfirst)
  refine ⟨g, mem_suppW_hiC.mpr ⟨?_, y, hg⟩⟩
  have e : (⟨((Fin.last (m + 1) : Fin (m + 1 + 1)) : ℕ) - 1, by simp⟩ : Fin (m + 1 + 1)) =
      Fin.castSucc (Fin.last m) := Fin.ext (by simp)
  rw [e, snoc_cs] at h1; exact h1

lemma last_hi_mem (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) {g : Fin N}
    (hg : g ∈ suppW (hiC (lab (Fin.last m)) c)) :
    lab ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩ ≤ (g : ℕ) ∧
      colW (hiC (lab (Fin.last m)) c) g ∈ SpanSet E {j | m + 1 ≤ (j : ℕ)} := by
  obtain ⟨hb, y, hy⟩ := mem_suppW_hiC.mp hg
  obtain ⟨hmono, -, hc, -⟩ := hC
  have hle : ∀ j : Fin (m + 1), lab j ≤ lab (Fin.last m) := fun j => by
    have := hmono.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
    rwa [snoc_cs, snoc_cs] at this
  refine ⟨(hle _).trans hb.le, ?_⟩
  have hcol : colW (hiC (lab (Fin.last m)) c) g = colC c g := by
    funext y'; simp [colW, colC, hiC, hb]
  rw [hcol]
  refine SpanSet_mono (fun j hj => ?_) (hc y g hy).2.2
  rcases hj with hj | ⟨hjm, hgj⟩
  · show m + 1 ≤ (j : ℕ); omega
  · show m + 1 ≤ (j : ℕ)
    by_contra hlt
    push_neg at hlt
    have e : (⟨j, hjm⟩ : Fin (m + 1 + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    rw [e, snoc_cs] at hgj
    have := hle ⟨j, hlt⟩
    omega

lemma last_uOf (hfirst : runFirst l (m + 1) = m + 1)
    (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) :
    uOf c = uW (hiC (lab (Fin.last m)) c) := by
  have hne := last_hi_ne hfirst hC
  have hnb := last_ne hC
  apply le_antisymm
  · rw [uOf_le_iff]
    intro y g hg
    by_cases hgt : lab (Fin.last m) < (g : ℕ)
    · have hmem : g ∈ suppW (hiC (lab (Fin.last m)) c) := mem_suppW_hiC.mpr ⟨hgt, y, hg⟩
      have := Finset.le_sup (f := fun g : Fin N => (g : ℕ) + 1) hmem
      simp only [uW]; omega
    · have hlt : (g : ℕ) < lab (Fin.last m) := by
        have := hnb y g hg; omega
      obtain ⟨g', hg'⟩ := hne
      have h1 := (mem_suppW_hiC.mp hg').1
      have := Finset.le_sup (f := fun g : Fin N => (g : ℕ) + 1) hg'
      simp only [uW]; omega
  · refine Finset.sup_le fun g hg => ?_
    obtain ⟨-, y, hy⟩ := mem_suppW_hiC.mp hg
    exact Finset.le_sup (f := fun g : Fin N => (g : ℕ) + 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy⟩)

end LastCons

/-! ## Stage rows for the processed pivots -/

section StageRowsR

variable {K : ℕ}

lemma card_ge (p : ℕ) : Fintype.card {j : Fin K // p ≤ (j : ℕ)} = K - p := by
  rw [Fintype.card_subtype]
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin K)))
    (fun j : Fin K => (j : ℕ) < p)
  have h2 : (univ.filter fun j : Fin K => (j : ℕ) < p).card = min K p := Fin.card_filter_val_lt
  have h3 : (univ.filter fun j : Fin K => ¬ (j : ℕ) < p) =
      univ.filter fun j : Fin K => p ≤ (j : ℕ) := by
    ext j; simp
  rw [h3, h2, Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- **Stage rows** for the pivots `≥ p`: a column in the span of these pivots is determined by
its entries in `K - p` rows. -/
theorem stage_rows (E : Matrix (Fin K) (Fin K) ℕ) (hE : (Ereal E).det ≠ 0) (p : ℕ) :
    ∃ R : Finset (Fin K), R.card = K - p ∧
      ∀ w ∈ SpanSet E {j | p ≤ (j : ℕ)}, ∀ w' ∈ SpanSet E {j | p ≤ (j : ℕ)},
        (∀ y ∈ R, w y = w' y) → w = w' := by
  set M : Matrix (Fin K) {j : Fin K // p ≤ (j : ℕ)} ℝ := fun y j => (E y j : ℝ) with hM
  have hli : LinearIndependent ℝ M.col := by
    have hcols : LinearIndependent ℝ (Ereal E).col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hE))
    have := hcols.comp (Subtype.val : {j : Fin K // p ≤ (j : ℕ)} → Fin K) Subtype.val_injective
    convert! this using 1
  obtain ⟨R, hR, hinj⟩ := RankFull.exists_rows_inj M hli
  refine ⟨R, by rw [hR, card_ge], ?_⟩
  rintro w ⟨v, hv0, hv⟩ w' ⟨v', hv0', hv'⟩ hR'
  have hβ := hinj (fun j => v j - v' j) (fun y hy => by
    have h1 := hv y
    have h2 := hv' y
    have h3 : (w y : ℝ) = w' y := by exact_mod_cast hR' y hy
    have hs : ∀ (u : Fin K → ℝ), (∀ j, j ∉ {j : Fin K | p ≤ (j : ℕ)} → u j = 0) →
        ∑ j, (E y j : ℝ) * u j = ∑ j : {j : Fin K // p ≤ (j : ℕ)}, M y j * u j := by
      intro u hu
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin K => p ≤ (j : ℕ))]
      have h0 : ∑ j ∈ univ.filter (fun j : Fin K => ¬ p ≤ (j : ℕ)), (E y j : ℝ) * u j = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [hu j (by simpa using (Finset.mem_filter.mp hj).2), mul_zero]
      rw [h0, add_zero]
      exact Finset.sum_subtype _ (fun j => by simp) _
    have hd : ∀ j, j ∉ {j : Fin K | p ≤ (j : ℕ)} → v j - v' j = 0 := fun j hj => by
      rw [hv0 j hj, hv0' j hj, sub_zero]
    rw [← hs _ hd]
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith)
  funext y
  have hvv : ∀ j, v j = v' j := by
    intro j
    by_cases hj : p ≤ (j : ℕ)
    · have := congrFun hβ ⟨j, hj⟩; simp at this; linarith
    · rw [hv0 j hj, hv0' j hj]
  have : (w y : ℝ) = w' y := by rw [hv, hv']; simp_rw [hvv]
  exact_mod_cast this

lemma zero_mem_SpanSet (E : Matrix (Fin K) (Fin K) ℕ) (P : Set (Fin K)) :
    (0 : Fin K → ℕ) ∈ SpanSet E P := ⟨0, fun _ _ => rfl, fun y => by simp⟩

end StageRowsR

/-! ## The FAC shift of the block of the run just completed -/

section Harvest

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {Jw : Set ℝ} {smax : ℕ}

/-- A coefficient vector of a column in the span (or `0`). -/
noncomputable def vch (E : Matrix (Fin K) (Fin K) ℕ) (P : Set (Fin K)) (w : Fin K → ℕ) :
    Fin K → ℝ :=
  if h : w ∈ SpanSet E P then Classical.choose h else 0

lemma vch_spec {P : Set (Fin K)} {w : Fin K → ℕ} (h : w ∈ SpanSet E P) :
    (∀ j, j ∉ P → vch E P w j = 0) ∧ ∀ y, (w y : ℝ) = ∑ j, (E y j : ℝ) * vch E P w j := by
  unfold vch; rw [dif_pos h]; exact Classical.choose_spec h

/-- **The harvest of the block** `F_t` at the last pivot of the run `P_t`. -/
theorem IzM_split (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    {m n : ℕ} (hmK : m + 1 ≤ K) {lab : Fin (m + 1) → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hC : ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) {ω : Ω} (hω : ω ∈ decSet J c) :
    IzM J E Jw (m + 1) lab ω c =
      ENNReal.ofReal (∏ g ∈ suppW (hiC (lab (Fin.last m)) c),
        (J.q g ω)⁻¹ ^ (∑ y, hiC (lab (Fin.last m)) c y g)) *
      IzM J E Jw (m + 1) lab ω (loC (lab (Fin.last m)) c) := by
  set b0 := lab (Fin.last m) with hb0
  set S := suppW (hiC b0 c) with hS
  set Pset : Set (Fin K) := {j | m + 1 ≤ (j : ℕ)} with hP
  set v : Fin N → Fin K → ℝ := fun g => vch E Pset (colW (hiC b0 c) g) with hv
  have hmem : ∀ g ∈ S, colW (hiC b0 c) g ∈ SpanSet E Pset := fun g hg =>
    (last_hi_mem hC hg).2
  have hQ : ∀ g ∈ S, 0 < J.q g ω := by
    intro g hg
    obtain ⟨-, y, hy⟩ := mem_suppW_hiC.mp hg
    linarith [hq ω g (hω y g hy)]
  have hvW : ∀ g ∈ S, ∀ y, (hiC b0 c y g : ℝ) = ∑ j, (E y j : ℝ) * v g j := by
    intro g hg y
    exact (vch_spec (hmem g hg)).2 y
  have hsupp : ∀ g ∈ S, ∀ j : Fin K, (j : ℕ) < K - (K - (m + 1)) → v g j = 0 := by
    intro g hg j hj
    exact (vch_spec (hmem g hg)).1 j (by simp only [hP, Set.mem_setOf_eq]; omega)
  have hcv : cvs J ω c = fun y => cvs J ω (loC b0 c) y *
      ∏ g ∈ S, J.q g ω ^ (hiC b0 c y g) := by
    funext y
    exact cval_split (fun g => J.q g ω) (last_ne hC) y
  unfold IzM
  rw [hcv]
  exact lintegral_Lcore_shift E hJw (by omega) (uvec J (m + 1) lab ω) S (fun g => J.q g ω) hQ v
    (hiC b0 c) hvW hsupp (cvs J ω (loC b0 c))

end Harvest

/-! ## The step at the last pivot of a run -/

section Last

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

lemma sumE_comp_le_of_injOn {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (φ : ι → κ) (hφ : ∀ i ∈ s, φ i ∈ t) (hinj : Set.InjOn φ s) (F : κ → ℝ≥0∞) :
    ∑ i ∈ s, F (φ i) ≤ ∑ k ∈ t, F k := by
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset fun k hk => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk; exact hφ i hi

lemma loC_mem {b0 : ℕ} {c : Fin K → (Fin N → ℕ) × ℕ} (hc : c ∈ contents K N D Dmax X₀) :
    loC b0 c ∈ contents K N D Dmax X₀ := by
  rw [contents, Fintype.mem_piFinset] at hc ⊢
  intro y
  have h := hc y
  rw [rowSet, Finset.mem_product] at h ⊢
  refine ⟨?_, h.2⟩
  rw [Fintype.mem_piFinset] at h ⊢
  intro g
  have := h.1 g
  simp only [loC, Finset.mem_range] at this ⊢
  split_ifs <;> omega

lemma hiC_mem {b0 : ℕ} {c : Fin K → (Fin N → ℕ) × ℕ} (hc : c ∈ contents K N D Dmax X₀) :
    hiC b0 c ∈ Wset K N D := by
  rw [contents, Fintype.mem_piFinset] at hc
  rw [Wset, Fintype.mem_piFinset]
  intro y
  have h := hc y
  rw [rowSet, Finset.mem_product, Fintype.mem_piFinset] at h
  rw [Fintype.mem_piFinset]
  intro g
  have := h.1 g
  simp only [hiC, Finset.mem_range] at this ⊢
  split_ifs <;> omega

/-- The term of `ZS m` in the product form. -/
lemma ZS_term_eq (m : ℕ) (ω : Ω) (lab : Fin (m + 1) → ℕ) (c : Fin K → (Fin N → ℕ) × ℕ) :
    (J.A (lab (Fin.last m))).indicator 1 ω *
      Ffull J E l τ Jw G A Eu m ω (Fin.init lab) (lab (Fin.last m)) c (J.q (lab (Fin.last m)) ω) =
    (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
      ((G (lab (Fin.last m))).indicator 1 ω * PhiC (N := N) J l A Eu (runNum l m) ω
        (lab ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩)) *
      (∏ j, invq (J.q (lab j) ω)) * IzM J E Jw (m + 1) lab ω c *
      ENNReal.ofReal (patternWeight τ E) := by
  unfold Ffull
  have e1 : (Fin.snoc (Fin.init lab) (lab (Fin.last m)) : Fin (m + 1) → ℕ) = lab :=
    Fin.snoc_init_self lab
  have hIz : IzX J E Jw m (Fin.init lab) ω c (Real.log (J.q (lab (Fin.last m)) ω)) =
      IzM J E Jw (m + 1) lab ω c := by
    unfold IzX IzM; rw [uvecX_init]
  rw [e1, hIz, Fin.prod_univ_castSucc (fun j => (J.A (lab j)).indicator (1 : Ω → ℝ≥0∞) ω),
    Fin.prod_univ_castSucc (fun j => invq (J.q (lab j) ω))]
  simp only [Fin.init]
  ring

/-- **(S3)(a)** for a block whose columns are in the span of the pivots `≥ p`, completing the
run `r` (general form). -/
theorem blockSumE_gen [NeZero N] (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (p r : ℕ) (hrlen : r < l.length)
    (hdsum : (l.drop r).sum = K - p) (ω : Ω)
    (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) (b : ℕ) :
    ∑ W ∈ Wset K N D, (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
        (SpanSet E {j | p ≤ (j : ℕ)}) W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J l A Eu r ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g)) else 0) ≤
      ENNReal.ofReal (GRun A (l.drop r) (EuSω (N := N) J Eu ω b) /
        EuSω (N := N) J Eu ω b ^ (l.drop r).sum) := by
  obtain ⟨R, hR, hinj⟩ := stage_rows E hE p
  have hdrop : l.drop r = l[r] :: l.drop (r + 1) := List.drop_eq_getElem_cons hrlen
  have hcard : R.card = (l.drop (r + 1)).sum + l[r] := by
    rw [hR, ← hdsum, hdrop, List.sum_cons]; ring
  obtain ⟨hG0, hGanti⟩ := GRun_nonneg_antitone A (l.drop (r + 1))
  have bs := blockSum_le D R (SpanSet E {j | p ≤ (j : ℕ)}) hinj (zero_mem_SpanSet E _)
    (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) (fun g hg => hq ω g hg) hEu b smax
    (fun u => ω ∈ G u) hS3 hcard hG0 hGanti
  -- the left side as `ofReal` of the real sum
  have hterm : ∀ W ∈ Wset K N D, (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
      (SpanSet E {j | p ≤ (j : ℕ)}) W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J l A Eu r ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g)) else 0) =
      ENNReal.ofReal (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
        (SpanSet E {j | p ≤ (j : ℕ)}) W then
        chiB smax (fun u => ω ∈ G u) (uW W) *
          (GRun A (l.drop (r + 1)) (EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W)) /
            EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W) ^
              (l.drop (r + 1)).sum) *
          ∏ g : Fin N, (J.q g ω)⁻¹ ^ (∑ y, W y g) else 0) := by
    intro W _
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      have hc0 : 0 ≤ chiB smax (fun u => ω ∈ G u) (uW W) := by
        unfold chiB; split_ifs <;> norm_num
      have hp0 : 0 ≤ ∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g) :=
        Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
          linarith [hq ω g (hB.2 g hg).1])) _
      rw [prod_inv_eq_supp (fun g => J.q g ω) W, PhiC, EuSω]
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (mul_nonneg hc0
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _)))]
    · simp
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun W _ => by
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      refine mul_nonneg (mul_nonneg (by unfold chiB; split_ifs <;> norm_num)
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _))) ?_
      rw [prod_inv_eq_supp (fun g => J.q g ω) W]
      exact Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
        linarith [hq ω g (hB.2 g hg).1])) _
    · exact le_rfl)]
  unfold EuSω
  rw [hdrop, GRun_cons, List.sum_cons]
  refine ENNReal.ofReal_le_ofReal (le_trans bs (le_of_eq ?_))
  rw [hcard]
  ring_nf

/-- **(S3)(a)** for the block of the run just completed, in the form used by the recursion. -/
theorem blockSumE_le [NeZero N] (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K)
    {m : ℕ} (hm : m + 2 ≤ K) (hfirst : runFirst l (m + 1) = m + 1) (ω : Ω)
    (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) (b : ℕ) :
    ∑ W ∈ Wset K N D, (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
        (SpanSet E {j | m + 1 ≤ (j : ℕ)}) W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J l A Eu (runNum l (m + 1)) ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g)) else 0) ≤
      PhiC (N := N) J l A Eu (runNum l m) ω b := by
  obtain ⟨R, hR, hinj⟩ := stage_rows E hE (m + 1)
  set r := runNum l (m + 1) with hr
  have hr' : runNum l m + 1 = r := by
    have := runNum_pred_of_first l (j := m + 1) (by omega) (by omega) hfirst hpos
    simpa using this
  have hrlen : r < l.length := runNum_lt_length l (by omega)
  have hdrop : l.drop r = l[r] :: l.drop (r + 1) := List.drop_eq_getElem_cons hrlen
  have hdsum : (l.drop r).sum = K - (m + 1) := by
    rw [sum_drop_runNum l (by omega), hfirst, hsum]
  have hcard : R.card = (l.drop (r + 1)).sum + l[r] := by
    rw [hR, ← hdsum, hdrop, List.sum_cons]; ring
  obtain ⟨hG0, hGanti⟩ := GRun_nonneg_antitone A (l.drop (r + 1))
  have bs := blockSum_le D R (SpanSet E {j | m + 1 ≤ (j : ℕ)}) hinj (zero_mem_SpanSet E _)
    (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) (fun g hg => hq ω g hg) hEu b smax
    (fun u => ω ∈ G u) hS3 hcard hG0 hGanti
  -- the left side as `ofReal` of the real sum
  have hterm : ∀ W ∈ Wset K N D, (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
      (SpanSet E {j | m + 1 ≤ (j : ℕ)}) W then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW W)) *
        PhiC (N := N) J l A Eu r ω (uW W) *
        ENNReal.ofReal (∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g)) else 0) =
      ENNReal.ofReal (if BlockOK (fun g : Fin N => ω ∈ J.A g) b
        (SpanSet E {j | m + 1 ≤ (j : ℕ)}) W then
        chiB smax (fun u => ω ∈ G u) (uW W) *
          (GRun A (l.drop (r + 1)) (EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W)) /
            EuS (fun g : Fin N => ω ∈ J.A g) (fun g => J.q g ω) Eu (uW W) ^
              (l.drop (r + 1)).sum) *
          ∏ g : Fin N, (J.q g ω)⁻¹ ^ (∑ y, W y g) else 0) := by
    intro W _
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      have hc0 : 0 ≤ chiB smax (fun u => ω ∈ G u) (uW W) := by
        unfold chiB; split_ifs <;> norm_num
      have hp0 : 0 ≤ ∏ g ∈ suppW W, (J.q g ω)⁻¹ ^ (∑ y, W y g) :=
        Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
          linarith [hq ω g (hB.2 g hg).1])) _
      rw [prod_inv_eq_supp (fun g => J.q g ω) W, PhiC, EuSω]
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (mul_nonneg hc0
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _)))]
    · simp
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun W _ => by
    split_ifs with hB
    · have hE0 := EuS_pos (fun g (hg : ω ∈ J.A g) => hq ω g hg) hEu (uW W)
      refine mul_nonneg (mul_nonneg (by unfold chiB; split_ifs <;> norm_num)
        (div_nonneg (hG0 _ hE0) (pow_nonneg hE0.le _))) ?_
      rw [prod_inv_eq_supp (fun g => J.q g ω) W]
      exact Finset.prod_nonneg fun g hg => pow_nonneg (inv_nonneg.mpr (by
        linarith [hq ω g (hB.2 g hg).1])) _
    · exact le_rfl)]
  unfold PhiC EuSω
  rw [hr', hdrop, GRun_cons, List.sum_cons]
  refine ENNReal.ofReal_le_ofReal (le_trans bs (le_of_eq ?_))
  rw [hcard]
  ring_nf

/-- **The step at the last pivot of a run** (not the last run): FAC shift of the block, then
(S3)(a). -/
theorem hnext_last (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K)
    {m : ℕ} (hm : m + 2 ≤ K) (hfirst : runFirst l (m + 1) = m + 1) (ω : Ω)
    (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A) :
    ∫⁻ t, PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (m + 1) (ω, t) ≤
      ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu m ω := by
  rw [lintegral_PhiBarM hJw (by omega)]
  unfold ZS
  refine ENNReal.tsum_le_tsum fun lab => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- no slots: no admissible labels
    refine le_of_eq_of_le (Finset.sum_eq_zero fun c _ => ?_) (zero_le)
    rw [if_neg]
    rintro ⟨n, hn⟩
    have := (hn.2.1 0).1
    omega
  haveI : NeZero N := ⟨by omega⟩
  set b0 := lab (Fin.last m) with hb0
  set b := lab ⟨runFirst l m, Nat.lt_succ_of_le (runFirst_le l m)⟩ with hb
  set W := ENNReal.ofReal (patternWeight τ E) with hW
  set Col := SpanSet E {j : Fin K | m + 1 ≤ (j : ℕ)} with hCol
  set X : (Fin K → (Fin N → ℕ) × ℕ) → ℝ≥0∞ := fun c' =>
    (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c').indicator 1 ω *
      (G b0).indicator 1 ω * (∏ j, invq (J.q (lab j) ω)) * IzM J E Jw (m + 1) lab ω c' * W
    with hX
  set Y : (Fin K → Fin N → ℕ) → ℝ≥0∞ := fun Wc =>
    if BlockOK (fun g : Fin N => ω ∈ J.A g) b Col Wc then
      ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW Wc)) *
        PhiC (N := N) J l A Eu (runNum l (m + 1)) ω (uW Wc) *
        ENNReal.ofReal (∏ g ∈ suppW Wc, (J.q g ω)⁻¹ ^ (∑ y, Wc y g)) else 0 with hY
  set sC := (contents K N D Dmax X₀).filter (ConsM E l smax (m + 1) lab) with hsC
  -- each term factors through the split
  have hfac : ∀ c ∈ contents K N D Dmax X₀,
      (if ∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c then
        (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
          GammaBar J l smax G A Eu (m + 1) ω lab c * (∏ j, invq (J.q (lab j) ω)) *
          IzM J E Jw (m + 1) lab ω c * W else 0) ≤
      if (∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c then
        X (loC b0 c) * Y (hiC b0 c) else 0 := by
    intro c _
    by_cases hC : ∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c
    · obtain ⟨n, hn⟩ := hC
      rw [if_pos ⟨n, hn⟩]
      by_cases hω : ω ∈ decSet J c
      · rw [if_pos ⟨⟨n, hn⟩, hω⟩]
        have hωlo : ω ∈ decSet J (loC b0 c) := by
          intro y g hg
          simp only [loC] at hg
          split_ifs at hg with h
          · exact hω y g hg
          · exact absurd rfl hg
        have hBlk : BlockOK (fun g : Fin N => ω ∈ J.A g) b Col (hiC b0 c) := by
          refine ⟨last_hi_ne hfirst hn, fun g hg => ?_⟩
          obtain ⟨hb1, hcol⟩ := last_hi_mem hn hg
          obtain ⟨-, y, hy⟩ := mem_suppW_hiC.mp hg
          exact ⟨hω y g hy, hb1, hcol⟩
        have hnot : ¬ runFirst l (m + 1) < m + 1 := by omega
        unfold GammaBar
        rw [dif_neg hnot, dif_pos (by omega), IzM_split hJw hq (by omega) hn hω,
          last_uOf hfirst hn]
        simp only [hX, hY, if_pos hBlk, Set.indicator_of_mem hω, Set.indicator_of_mem hωlo]
        have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
        rw [e]
        refine le_of_eq ?_
        ring
      · rw [if_neg (fun h => hω h.2), Set.indicator_of_notMem hω]; simp
    · rw [if_neg hC]; exact zero_le
  refine (Finset.sum_le_sum hfac).trans ?_
  -- the injection into pairs
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun c => (loC b0 c, hiC b0 c))
      (↑((contents K N D Dmax X₀).filter fun c =>
        (∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c) :
          Set (Fin K → (Fin N → ℕ) × ℕ)) := by
    intro c hc c' hc' h
    obtain ⟨⟨n, hn⟩, -⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨⟨n', hn'⟩, -⟩ := (Finset.mem_filter.mp hc').2
    exact split_inj (last_ne hn) (last_ne hn') (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hmaps : ∀ c ∈ (contents K N D Dmax X₀).filter (fun c =>
      (∃ n, ConsM E l smax (m + 1 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c),
      (loC b0 c, hiC b0 c) ∈ sC ×ˢ Wset K N D := by
    intro c hc
    obtain ⟨hc1, ⟨n, hn⟩, -⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨loC_mem hc1, last_lo hfirst hn⟩,
      hiC_mem hc1⟩
  have h1 := sumE_comp_le_of_injOn _ _ _ hmaps hinj (fun p => X p.1 * Y p.2)
  refine h1.trans ?_
  rw [Finset.sum_product]
  have hblk : ∑ Wc ∈ Wset K N D, Y Wc ≤ PhiC (N := N) J l A Eu (runNum l m) ω b :=
    blockSumE_le hq hEu hE hpos hsum hm hfirst ω hS3 b
  calc ∑ c' ∈ sC, ∑ Wc ∈ Wset K N D, X (c', Wc).1 * Y (c', Wc).2
      = ∑ c' ∈ sC, X c' * ∑ Wc ∈ Wset K N D, Y Wc := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ c' ∈ sC, X c' * PhiC (N := N) J l A Eu (runNum l m) ω b :=
        Finset.sum_le_sum fun c' _ => mul_le_mul_right hblk _
    _ = _ := by
        rw [hsC, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c' _ => ?_
        split_ifs
        · rw [ZS_term_eq, hX]
          ring
        · rfl

end Last

/-! ## The end step (the earliest pivot, the early block and the tails) -/

section Final

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

/-- The free part of a content (all slots). -/
def freeW (c : Fin K → (Fin N → ℕ) × ℕ) : Fin K → Fin N → ℕ := fun y g => (c y).1 g

/-- The tails of a content. -/
def tailsC (c : Fin K → (Fin N → ℕ) × ℕ) : Fin K → ℕ := fun y => (c y).2

lemma mergeL_full (z : Fin (K - 0) → ℝ) (u : Fin K → ℝ) : mergeL (K := K) (K - 0) z u = z := by
  funext j
  unfold mergeL
  rw [dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp)

lemma lintegral_Lcore_full (hE : (Ereal E).det ≠ 0) (hJw : MeasurableSet Jw) (d : Fin K → ℝ)
    (hd : ∀ y, 0 < d y) (u : Fin K → ℝ) :
    ∫⁻ z : Fin (K - 0) → ℝ, Lcore E Jw d (mergeL (K - 0) z u) ≤
      ENNReal.ofReal |(Ereal E).det⁻¹| *
        ∏ y, (ENNReal.ofReal (d y)⁻¹ * MeasureTheory.volume Jw) := by
  simp_rw [mergeL_full]
  have := final_volume (Ereal E) hE d hd hJw
  unfold Lcore rowLog
  simpa [Ereal] using this

/-- The FAC shift of all the free slots, at the end. -/
theorem IzM_final (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    {lab : Fin 0 → ℕ} {c : Fin K → (Fin N → ℕ) × ℕ}
    (hspan : ∀ g ∈ suppW (freeW c), colW (freeW c) g ∈ SpanSet E {j | 0 ≤ (j : ℕ)})
    {ω : Ω} (hω : ω ∈ decSet J c) :
    IzM J E Jw 0 lab ω c = ENNReal.ofReal (∏ g ∈ suppW (freeW c),
        (J.q g ω)⁻¹ ^ (∑ y, freeW c y g)) *
      ∫⁻ z : Fin (K - 0) → ℝ, Lcore E Jw (fun y => (tailsC c y : ℝ))
        (mergeL (K - 0) z (uvec J 0 lab ω)) := by
  set S := suppW (freeW c) with hS
  set v : Fin N → Fin K → ℝ := fun g => vch E {j | 0 ≤ (j : ℕ)} (colW (freeW c) g) with hv
  have hQ : ∀ g ∈ S, 0 < J.q g ω := by
    intro g hg
    obtain ⟨y, hy⟩ := mem_suppW.mp hg
    linarith [hq ω g (hω y g hy)]
  have hvW : ∀ g ∈ S, ∀ y, (freeW c y g : ℝ) = ∑ j, (E y j : ℝ) * v g j := fun g hg y =>
    (vch_spec (hspan g hg)).2 y
  have hcv : cvs J ω c = fun y => (tailsC c y : ℝ) * ∏ g ∈ S, J.q g ω ^ (freeW c y g) := by
    funext y
    unfold cvs cval
    congr 1
    refine (Finset.prod_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
    have : (c y).1 g = 0 := by by_contra h; exact hg (mem_suppW.mpr ⟨y, h⟩)
    simp [freeW, this]
  unfold IzM
  rw [hcv]
  exact lintegral_Lcore_shift E hJw (by omega) (uvec J 0 lab ω) S (fun g => J.q g ω) hQ v
    (freeW c) hvW (fun g _ j hj => by omega) (fun y => (tailsC c y : ℝ))


/-- **The end step**: the last pivot (column `0`), then the FAC shift of all the free slots, the
Volume Lemma in log coordinates, the early block and the tails ((S3)(c), `end_step`). -/
theorem hnext_final (hJw : MeasurableSet Jw) (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω)
    (hEu : 0 < Eu) (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K)
    (hK : 1 ≤ K) (ω : Ω) (hS3 : ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) (htail : tailSum Dmax X₀ ≤ Eu)
    (hτ1 : ∀ j, 1 ≤ τ j) :
    ∫⁻ t, PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu 0 (ω, t) ≤
      ENNReal.ofReal (finG A l Eu * δ ^ K * patternWeight τ E) := by
  rw [lintegral_PhiBarM hJw (by omega)]
  rw [tsum_eq_single (Fin.elim0 : Fin 0 → ℕ) (fun b hb => absurd (Subsingleton.elim b _) hb)]
  set lab : Fin 0 → ℕ := Fin.elim0
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun c _ => ?_) (zero_le)
    rw [if_neg]
    rintro ⟨n, hn⟩
    have := (hn.2.1 0).1
    omega
  haveI : NeZero N := ⟨by omega⟩
  set W := ENNReal.ofReal (patternWeight τ E) with hW
  set Col := SpanSet E {j : Fin K | 0 ≤ (j : ℕ)} with hCol
  set Ywt : (Fin K → Fin N → ℕ) → ℝ≥0∞ := fun Wc =>
    ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW Wc)) *
      PhiC (N := N) J l A Eu 0 ω (uW Wc) *
      ENNReal.ofReal (∏ g ∈ suppW Wc, (J.q g ω)⁻¹ ^ (∑ y, Wc y g)) with hYwt
  set Zt : (Fin K → ℕ) → ℝ≥0∞ := fun d =>
    ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (ENNReal.ofReal ((d y : ℝ))⁻¹ *
      MeasureTheory.volume Jw) with hZt
  set WF := (Wset K N D).filter fun Wc => Wc = 0 ∨ BlockOK (fun g : Fin N => ω ∈ J.A g) 0 Col Wc
    with hWF
  set TS := Fintype.piFinset fun _ : Fin K => Nat.smoothNumbersUpTo Dmax X₀ with hTS
  have hrn0 : runNum l 0 = 0 := runNum_zero l hpos
  -- each term is bounded through the split into the free part and the tails
  have hfac : ∀ c ∈ contents K N D Dmax X₀,
      (if ∃ n, ConsM E l smax (0 + 1) (Fin.snoc lab n) c then
        (∏ j, (J.A (lab j)).indicator 1 ω) * (decSet J c).indicator 1 ω *
          GammaBar J l smax G A Eu 0 ω lab c * (∏ j, invq (J.q (lab j) ω)) *
          IzM J E Jw 0 lab ω c * W else 0) ≤
      if (∃ n, ConsM E l smax (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c then
        Ywt (freeW c) * Zt (tailsC c) * W else 0 := by
    intro c hc
    by_cases hC : ∃ n, ConsM E l smax (0 + 1) (Fin.snoc lab n) c
    · obtain ⟨n, hn⟩ := hC
      rw [if_pos ⟨n, hn⟩]
      by_cases hω : ω ∈ decSet J c
      · rw [if_pos ⟨⟨n, hn⟩, hω⟩]
        have hspan : ∀ g ∈ suppW (freeW c), colW (freeW c) g ∈ Col := by
          intro g hg
          obtain ⟨y, hy⟩ := mem_suppW.mp hg
          exact SpanSet_mono (fun j _ => Nat.zero_le _) ((hn.2.2.1 y g hy).2.2)
        have hd : ∀ y, 0 < (tailsC c y : ℝ) := by
          intro y
          rw [contents, Fintype.mem_piFinset] at hc
          have := (Finset.mem_product.mp (hc y)).2
          exact_mod_cast smooth_pos this
        unfold GammaBar
        rw [dif_neg (by omega), dif_neg (by omega), IzM_final hJw hq hspan hω, hrn0]
        simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, mul_one,
          Set.indicator_of_mem hω, Pi.one_apply, hYwt, hZt]
        have huw : uOf c = uW (freeW c) := rfl
        rw [huw]
        have hint := lintegral_Lcore_full hE hJw (fun y => (tailsC c y : ℝ)) hd
          (uvec J 0 lab ω)
        calc ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW (freeW c))) *
              PhiC (N := N) J l A Eu 0 ω (uW (freeW c)) *
              (ENNReal.ofReal (∏ g ∈ suppW (freeW c), (J.q g ω)⁻¹ ^ (∑ y, freeW c y g)) *
                ∫⁻ z : Fin (K - 0) → ℝ, Lcore E Jw (fun y => (tailsC c y : ℝ))
                  (mergeL (K - 0) z (uvec J 0 lab ω))) * W
            ≤ ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) (uW (freeW c))) *
              PhiC (N := N) J l A Eu 0 ω (uW (freeW c)) *
              (ENNReal.ofReal (∏ g ∈ suppW (freeW c), (J.q g ω)⁻¹ ^ (∑ y, freeW c y g)) *
                (ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (ENNReal.ofReal ((tailsC c y : ℝ))⁻¹ *
                  MeasureTheory.volume Jw))) * W := by gcongr
          _ = _ := by ring
      · rw [if_neg (fun h => hω h.2), Set.indicator_of_notMem hω]; simp
    · rw [if_neg hC]; exact zero_le
  refine (Finset.sum_le_sum hfac).trans ?_
  rw [← Finset.sum_filter]
  -- the injection into pairs (free part, tails)
  have hinj : Set.InjOn (fun c => (freeW c, tailsC c))
      (↑((contents K N D Dmax X₀).filter fun c =>
        (∃ n, ConsM E l smax (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c) :
          Set (Fin K → (Fin N → ℕ) × ℕ)) := by
    intro c _ c' _ h
    funext y
    have h1 := congrFun (congrArg Prod.fst h) y
    have h2 := congrFun (congrArg Prod.snd h) y
    exact Prod.ext (funext fun g => congrFun h1 g) h2
  have hmaps : ∀ c ∈ (contents K N D Dmax X₀).filter (fun c =>
      (∃ n, ConsM E l smax (0 + 1) (Fin.snoc lab n) c) ∧ ω ∈ decSet J c),
      (freeW c, tailsC c) ∈ WF ×ˢ TS := by
    intro c hc
    obtain ⟨hc1, ⟨n, hn⟩, hω⟩ := Finset.mem_filter.mp hc
    rw [contents, Fintype.mem_piFinset] at hc1
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Wset, Fintype.mem_piFinset]
      intro y
      have := (Finset.mem_product.mp (hc1 y)).1
      rw [Fintype.mem_piFinset] at this ⊢
      exact this
    · by_cases h0 : freeW c = 0
      · exact Or.inl h0
      · refine Or.inr ⟨?_, fun g hg => ?_⟩
        · by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          apply h0
          funext y g
          by_contra h
          have : g ∈ suppW (freeW c) := mem_suppW.mpr ⟨y, h⟩
          rw [hne] at this; exact absurd this (Finset.notMem_empty _)
        · obtain ⟨y, hy⟩ := mem_suppW.mp hg
          exact ⟨hω y g hy, Nat.zero_le _,
            SpanSet_mono (fun j _ => Nat.zero_le _) ((hn.2.2.1 y g hy).2.2)⟩
    · rw [hTS, Fintype.mem_piFinset]
      intro y
      exact (Finset.mem_product.mp (hc1 y)).2
  have h1 := sumE_comp_le_of_injOn _ _ _ hmaps hinj (fun p => Ywt p.1 * Zt p.2 * W)
  refine h1.trans ?_
  rw [Finset.sum_product]
  have hsplit : ∑ Wc ∈ WF, ∑ d ∈ TS, Ywt (Wc, d).1 * Zt (Wc, d).2 * W =
      (∑ Wc ∈ WF, Ywt Wc) * (∑ d ∈ TS, Zt d) * W := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Wc _ => ?_
    rw [Finset.sum_mul]
  rw [hsplit]
  -- the tails
  have hdet : ENNReal.ofReal |(Ereal E).det⁻¹| ≤ 1 := by
    have := RankFull.Config.one_le_abs_det hE
    rw [abs_inv]
    exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ this)
  have hvol : MeasureTheory.volume Jw ≤ ENNReal.ofReal δ := by
    calc MeasureTheory.volume Jw ≤ MeasureTheory.volume (Set.Ico a (a + δ)) :=
          MeasureTheory.measure_mono hJ
      _ = ENNReal.ofReal δ := by rw [Real.volume_Ico]; congr 1; ring
  have htails : ∑ d ∈ TS, Zt d ≤ (ENNReal.ofReal Eu * ENNReal.ofReal δ) ^ K := by
    calc ∑ d ∈ TS, Zt d ≤ ∑ d ∈ TS, ∏ y, (ENNReal.ofReal ((d y : ℝ))⁻¹ * ENNReal.ofReal δ) := by
          refine Finset.sum_le_sum fun d _ => ?_
          simp only [hZt]
          calc ENNReal.ofReal |(Ereal E).det⁻¹| * ∏ y, (ENNReal.ofReal ((d y : ℝ))⁻¹ *
                MeasureTheory.volume Jw)
              ≤ 1 * ∏ y, (ENNReal.ofReal ((d y : ℝ))⁻¹ * ENNReal.ofReal δ) := by gcongr
            _ = _ := one_mul _
      _ = (∑ e ∈ Nat.smoothNumbersUpTo Dmax X₀, ENNReal.ofReal ((e : ℝ))⁻¹ *
            ENNReal.ofReal δ) ^ K := by
          rw [hTS, ← Finset.prod_univ_sum (t := fun _ : Fin K => Nat.smoothNumbersUpTo Dmax X₀)
            (f := fun _ e => ENNReal.ofReal ((e : ℝ))⁻¹ * ENNReal.ofReal δ),
            Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (ENNReal.ofReal (tailSum Dmax X₀) * ENNReal.ofReal δ) ^ K := by
          rw [← Finset.sum_mul, tailSum, ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
      _ ≤ (ENNReal.ofReal Eu * ENNReal.ofReal δ) ^ K := by
          gcongr
  -- the free part: the empty content and the non-empty contents
  have h0mem : (0 : Fin K → Fin N → ℕ) ∈ Wset K N D := by
    rw [Wset, Fintype.mem_piFinset]; intro y; rw [Fintype.mem_piFinset]; intro g; simp
  have hsupp0 : suppW (0 : Fin K → Fin N → ℕ) = ∅ := by
    ext g; simp [mem_suppW]
  have hnot0 : ¬ BlockOK (fun g : Fin N => ω ∈ J.A g) 0 Col (0 : Fin K → Fin N → ℕ) := by
    rintro ⟨hne, -⟩; rw [hsupp0] at hne; exact Finset.not_nonempty_empty hne
  have hWF : WF = insert 0 ((Wset K N D).filter
      (BlockOK (fun g : Fin N => ω ∈ J.A g) 0 Col)) := by
    ext Wc
    simp only [hWF, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hm, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hm, h⟩
    · rintro (rfl | ⟨hm, h⟩)
      · exact ⟨h0mem, Or.inl rfl⟩
      · exact ⟨hm, Or.inr h⟩
  have hnotin : (0 : Fin K → Fin N → ℕ) ∉ (Wset K N D).filter
      (BlockOK (fun g : Fin N => ω ∈ J.A g) 0 Col) := fun h =>
    hnot0 (Finset.mem_filter.mp h).2
  rw [hWF, Finset.sum_insert hnotin]
  have hEu0 : EuSω (N := N) J Eu ω 0 = Eu := by
    simp [EuSω, EuS]
  have hblk := blockSumE_gen (D := D) (G := G) (A := A) (smax := smax) hq hEu hE 0 0
    (by rw [show l.length = l.length from rfl]; cases l with
      | nil => simp at hsum; omega
      | cons a l' => simp)
    (by simp [hsum]) ω hS3 0
  rw [← Finset.sum_filter] at hblk
  have hY0 : Ywt 0 = ENNReal.ofReal (chiB smax (fun u => ω ∈ G u) 0) *
      ENNReal.ofReal (GRun A (l.drop 1) Eu / Eu ^ (l.drop 1).sum) := by
    simp only [hYwt, uW, hsupp0, Finset.sup_empty, Finset.prod_empty, ENNReal.ofReal_one,
      mul_one, PhiC, zero_add]
    rw [show (⊥ : ℕ) = 0 from rfl, hEu0]
  rw [hY0]
  rw [hEu0] at hblk
  simp only [List.drop_zero] at hblk
  -- the end step
  obtain ⟨j, rest, rfl⟩ : ∃ j rest, l = j :: rest := by
    cases l with
    | nil => simp at hsum; omega
    | cons j rest => exact ⟨j, rest, rfl⟩
  simp only [List.drop_succ_cons, List.drop_zero] at hY0 ⊢
  set χ0 := chiB smax (fun u => ω ∈ G u) 0 with hχ0
  set GT := GRun A (j :: rest) Eu with hGT
  set GT1 := GRun A rest Eu with hGT1
  have hχ01 : 0 ≤ χ0 ∧ χ0 ≤ 1 := by
    simp only [hχ0, chiB]; split_ifs <;> norm_num
  obtain ⟨hG0, -⟩ := GRun_nonneg_antitone A rest
  obtain ⟨hG0', -⟩ := GRun_nonneg_antitone A (j :: rest)
  have hGT1 : 0 ≤ GT1 := hG0 _ hEu
  have hGT0 : 0 ≤ GT := hG0' _ hEu
  have hsum' : K = rest.sum + j := by simp at hsum; omega
  have hend := end_step (K := K) (m := rest.sum) (j := j) hsum' hEu
    (S := GT / Eu ^ K) le_rfl hχ01.2 hGT1
  have hpw : 0 ≤ patternWeight τ E := Finset.prod_nonneg fun j _ =>
    pow_nonneg (inv_nonneg.mpr (by linarith [hτ1 j])) _
  have hfin : finG A (j :: rest) Eu = GT + Eu ^ j * GT1 := rfl
  calc (ENNReal.ofReal χ0 * ENNReal.ofReal (GT1 / Eu ^ rest.sum) +
          ∑ Wc ∈ (Wset K N D).filter (BlockOK (fun g : Fin N => ω ∈ J.A g) 0 Col), Ywt Wc) *
        (∑ d ∈ TS, Zt d) * W
      ≤ (ENNReal.ofReal χ0 * ENNReal.ofReal (GT1 / Eu ^ rest.sum) +
          ENNReal.ofReal (GT / Eu ^ (j + rest.sum))) *
        (ENNReal.ofReal Eu * ENNReal.ofReal δ) ^ K * W := by
        refine mul_le_mul_left (mul_le_mul' (add_le_add_right ?_ _) htails) _
        convert! hblk using 2
    _ = ENNReal.ofReal ((χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ K) * Eu ^ K * δ ^ K *
          patternWeight τ E) := by
        rw [show j + rest.sum = K by omega]
        rw [← ENNReal.ofReal_mul hχ01.1, ← ENNReal.ofReal_add (mul_nonneg hχ01.1
          (div_nonneg hGT1 (pow_nonneg hEu.le _))) (div_nonneg hGT0 (pow_nonneg hEu.le _)),
          ← ENNReal.ofReal_mul hEu.le, ← ENNReal.ofReal_pow (mul_nonneg hEu.le hδ), hW,
          ← ENNReal.ofReal_mul (add_nonneg (mul_nonneg hχ01.1 (div_nonneg hGT1
            (pow_nonneg hEu.le _))) (div_nonneg hGT0 (pow_nonneg hEu.le _))),
          ← ENNReal.ofReal_mul]
        · congr 1; ring
        · exact mul_nonneg (add_nonneg (mul_nonneg hχ01.1 (div_nonneg hGT1
            (pow_nonneg hEu.le _))) (div_nonneg hGT0 (pow_nonneg hEu.le _)))
            (pow_nonneg (mul_nonneg hEu.le hδ) _)
    _ ≤ ENNReal.ofReal (finG A (j :: rest) Eu * δ ^ K * patternWeight τ E) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hfin]
        have : (χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ K) * Eu ^ K ≤ GT + Eu ^ j * GT1 := by
          have := hend; linarith
        have hδK : 0 ≤ δ ^ K := pow_nonneg hδ _
        calc (χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ K) * Eu ^ K * δ ^ K * patternWeight τ E
            = ((χ0 * (GT1 / Eu ^ rest.sum) + GT / Eu ^ K) * Eu ^ K) * (δ ^ K *
                patternWeight τ E) := by ring
          _ ≤ (GT + Eu ^ j * GT1) * (δ ^ K * patternWeight τ E) :=
              mul_le_mul_of_nonneg_right this (mul_nonneg hδK hpw)
          _ = _ := by ring

end Final

/-! ## The recursion of Lemma A.5 for several runs -/

section Chain

variable {J : JitterLaw Ω P θE} {K : ℕ} {E : Matrix (Fin K) (Fin K) ℕ} {l : List ℕ}
  {τ : Fin K → ℝ} {Jw : Set ℝ} {D Dmax X₀ smax : ℕ} {G : ℕ → Set Ω} {A Eu : ℝ}

/-- **Lemma A.5 + Theorem A.10, the recursion over all `K` pivots** (any run structure):
`E[Z_0] ≤ θ^K Fin(A, l, Eu) δ^K ∏_j τ_j^{-(s_j - 1)}`, where `Z_0 = ZS (K-1)` is the labelled
sum over all pivots, contents and tails. -/
theorem multiRun_chain [IsProbabilityMeasure P] (hJw : MeasurableSet Jw)
    (hq : ∀ ω, ∀ n : Fin N, ω ∈ J.A n → 1 < J.q n ω) (hEu : 0 < Eu)
    (hE : (Ereal E).det ≠ 0) (hpos : ∀ a ∈ l, 1 ≤ a) (hsum : l.sum = K) (hK : 1 ≤ K)
    (hGm : ∀ u, MeasurableSet[J.F u] (G u)) (hG : ∀ u u', u ≤ u' → G u' ⊆ G u)
    (hS3 : ∀ ω, ∀ u ≤ smax, ω ∈ G u → EuSω (N := N) J Eu ω u ≤ A)
    {a δ : ℝ} (hJ : Jw ⊆ Set.Ico a (a + δ)) (hδ : 0 ≤ δ) (htail : tailSum Dmax X₀ ≤ Eu)
    (hτ1 : ∀ j, 1 ≤ τ j) :
    ∫⁻ ω, ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (K - 1) ω ∂P ≤
      θE ^ K * ENNReal.ofReal (finG A l Eu * δ ^ K * patternWeight τ E) := by
  set C := ENNReal.ofReal (finG A l Eu * δ ^ K * patternWeight τ E) with hC
  set Z : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    if i < K then ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (K - 1 - i) ω else C with hZ
  set Φ : ℕ → ℕ → Ω × ℝ → ℝ≥0∞ := fun i n =>
    PhiM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (K - 1 - i) n with hΦ
  set Φbar : ℕ → Ω × ℝ → ℝ≥0∞ := fun i =>
    PhiBarM (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (K - 1 - i) with hΦbar
  have h := J.pil_chain K Z Φ (fun i n => PhiM_jmeas hq hEu hGm hJw _ n) Φbar
    (fun i => PhiBarM_meas hq hEu hGm hJw _) (fun i n x => PhiM_le hq hEu hG _ n x)
    (fun i hi ω => by
      simp only [hZ, if_pos hi, hΦ]
      exact (ZS_eq J E l τ Jw D Dmax X₀ smax G A Eu _ ω).le)
    (fun i hi ω => by
      simp only [hΦbar, hZ]
      by_cases hi1 : i + 1 < K
      · rw [if_pos hi1]
        obtain ⟨m, hm⟩ : ∃ m, K - 1 - i = m + 1 := ⟨K - 2 - i, by omega⟩
        have hm' : K - 1 - (i + 1) = m := by omega
        rw [hm, hm']
        by_cases hnl : runFirst l (m + 1) < m + 1
        · exact hnext_nonlast hJw (by omega) hnl ω
        · exact hnext_last hJw hq hEu hE hpos hsum (by omega)
            (le_antisymm (runFirst_le l _) (not_lt.mp hnl)) ω (hS3 ω)
      · rw [if_neg hi1]
        have h0 : K - 1 - i = 0 := by omega
        rw [h0]
        exact hnext_final hJw hq hEu hE hpos hsum hK ω (hS3 ω) hJ hδ htail hτ1)
  have hZ0 : Z 0 = fun ω => ZS (N := N) J E l τ Jw D Dmax X₀ smax G A Eu (K - 1) ω := by
    funext ω; simp [hZ, show 0 < K by omega]
  have hZK : Z K = fun _ => C := by funext ω; simp [hZ]
  rw [hZ0, hZK] at h
  simpa [lintegral_const, measure_univ] using h

end Chain

end RankFull.Config
