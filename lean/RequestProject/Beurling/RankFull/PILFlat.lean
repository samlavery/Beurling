module

public import RequestProject.Beurling.RankFull.PIL

/-!
# The labelled pivot sum `Zs` in flat form

`RankFull.JitterLaw.Zs_eq` : the nested labelled sum `Zs k b Ψ` of Lemma A.5 (one run) is the
flat sum over the strictly decreasing label tuples `b > n₀ > n₁ > ⋯ > n_{k-1}` (latest first) of
`∏_i 1_{A n_i} · Ψ_{n_{k-1}}(q_{n_0}, …, q_{n_{k-1}})`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace RankFull

/-- Strictly decreasing labels below `b` (latest first). -/
def ChainOK {k : ℕ} (b : ℕ) (ns : Fin k → ℕ) : Prop := StrictAnti ns ∧ ∀ i, ns i < b

/-- The earliest label (or `b` if there is none). -/
def lastOf {k : ℕ} (b : ℕ) (ns : Fin k → ℕ) : ℕ := if h : 0 < k then ns ⟨k - 1, by omega⟩ else b

lemma chainOK_cons {k : ℕ} (b n : ℕ) (ns : Fin k → ℕ) :
    ChainOK b (Fin.cons n ns : Fin (k + 1) → ℕ) ↔ n < b ∧ ChainOK n ns := by
  constructor
  · rintro ⟨hanti, hb⟩
    refine ⟨by simpa using hb 0, fun i j hij => ?_, fun i => ?_⟩
    · have := hanti (Fin.succ_lt_succ_iff.mpr hij); simpa using this
    · have := hanti (Fin.succ_pos i); simpa using this
  · rintro ⟨hnb, hanti, hn⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ j =>
        induction i using Fin.cases with
        | zero => simpa using hn j
        | succ i => simpa using hanti (Fin.succ_lt_succ_iff.mp hij)
    · induction i using Fin.cases with
      | zero => simpa using hnb
      | succ i => simpa using (hn i).trans hnb

lemma lastOf_cons {k : ℕ} (b n : ℕ) (ns : Fin k → ℕ) :
    lastOf b (Fin.cons n ns : Fin (k + 1) → ℕ) = lastOf n ns := by
  unfold lastOf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [dif_pos (Nat.succ_pos k), dif_pos hk]
    have : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.succ ⟨k - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [this, Fin.cons_succ]

namespace JitterLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θ : ℝ≥0∞}
  (J : JitterLaw Ω P θ)

/-- **`Zs` in flat form.** -/
theorem Zs_eq : ∀ (k : ℕ) {Par : Type} (b : ℕ) (Ψ : ℕ → Ω → Par → (Fin k → ℝ) → ℝ≥0∞)
    (ω : Ω) (p : Par), J.Zs k b Ψ ω p = ∑' ns : Fin k → ℕ,
      if ChainOK b ns then (∏ i, (J.A (ns i)).indicator (1 : Ω → ℝ≥0∞) ω) *
        Ψ (lastOf b ns) ω p (fun i => J.q (ns i) ω) else 0
  | 0, Par, b, Ψ, ω, p => by
    rw [tsum_fintype, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Zs, lastOf,
      lt_irrefl, dite_false]
    split_ifs with h
    · congr 1
      funext i; exact Fin.elim0 i
    · exact absurd ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩ h
  | k + 1, Par, b, Ψ, ω, p => by
    simp only [Zs]
    have hih : ∀ n, J.Zs k n (fun m ω (pt : Par × ℝ) t' => Ψ m ω pt.1 (Fin.cons pt.2 t')) ω
        (p, J.q n ω) = ∑' ns : Fin k → ℕ, if ChainOK n ns then
          (∏ i, (J.A (ns i)).indicator (1 : Ω → ℝ≥0∞) ω) *
            Ψ (lastOf n ns) ω p (Fin.cons (J.q n ω) fun i => J.q (ns i) ω) else 0 :=
      fun n => Zs_eq k n _ ω (p, J.q n ω)
    rw [← (Fin.consEquiv fun _ => ℕ).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun n => ?_
    by_cases hn : n < b
    · rw [if_pos hn]
      by_cases hA : ω ∈ J.A n
      · rw [Set.indicator_of_mem hA, hih]
        refine tsum_congr fun ns => ?_
        rw [show (Fin.consEquiv fun _ => ℕ) (n, ns) = Fin.cons n ns from rfl]
        rw [chainOK_cons, lastOf_cons, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Set.indicator_of_mem hA, Pi.one_apply,
          one_mul, hn, true_and]
        congr 3
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ i => simp
      · rw [Set.indicator_of_notMem hA]
        symm
        refine ENNReal.tsum_eq_zero.mpr fun ns => ?_
        rw [show (Fin.consEquiv fun _ => ℕ) (n, ns) = Fin.cons n ns from rfl]
        simp only [Fin.prod_univ_succ, Fin.cons_zero,
          Set.indicator_of_notMem hA, zero_mul, ite_self]
    · rw [if_neg hn]
      symm
      refine ENNReal.tsum_eq_zero.mpr fun ns => ?_
      rw [show (Fin.consEquiv fun _ => ℕ) (n, ns) = Fin.cons n ns from rfl]
      simp only [chainOK_cons, hn, false_and, if_false]

end JitterLaw

end RankFull
