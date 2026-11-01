module

public import RequestProject.Beurling.RankFull.PIL

/-!
# Lemma A.5 (Pivot-Integration Lemma): the multi-run recursion, probabilistic skeleton

The recursion of Lemma A.5 processes the `k` pivots latest first. At each pivot `p` with label
(slot) `s`:
* the pending integrand, as a function of the position `q_p` and of the data decided before `s`,
  is adapted (`F s ⊗ Borel`-measurable);
* at the last pivot of a run, **step (i)** replaces the label `s_t` by `u_t` (the first slot after
  the latest block prime `f_t`): all `s`-dependent factors are non-increasing in `s`, the order
  constraint is `u_t ≤ s ≤ s_max`, and the good events are nested, so pathwise
  `1(G_{<s}) Ψ(s) ≤ χ_t Ψ(u_t)`, `χ_t = 1(u_t ≤ s_max) 1(G_{<u_t})` (`label_replace`); this is the
  dominating integrand of `pivot_step`, which need not be adapted;
* **step (iii)**: after the integral, the sum over the block contents is replaced by a pathwise
  bound adapted to the next pivot (e.g. `block_bound_GRun`).

Corrections #48/#55: the label sum comes first, then the integrals, then the block bound, and
the block bound sums over every content.

* `RankFull.label_replace` : the pathwise domination of step (i).
* `RankFull.JitterLaw.pil_chain` : **the recursion of Lemma A.5**: if level `i` is a pivot step
  (`Z i ≤ ∑_n 1_{A n} Φ_i n (·, q n)`, adapted `Φ_i n` dominated by `Φ̄_i`) and, pathwise,
  `∫ Φ̄_i(ω, t) dt ≤ Z (i+1) ω` (integral, then block bound), then
  `E[Z 0] ≤ θ^k E[Z k]`. With `Z 0 ≥ X_𝔰 1(Good(<t_J))` and `Z k` the deterministic envelope, this
  is the conclusion `E[X_𝔰; Good] ≤ θ^k S̄_𝔰`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace RankFull

/-- **Step (i) of Lemma A.5** (label replacement), pathwise: with nested good events
(`G s' ⊆ G s` for `s ≤ s'`) and a non-increasing label dependence `Ψ`, every admissible label
`u ≤ s ≤ s_max` satisfies `1(G_{<s}) Ψ(s) ≤ χ Ψ(u)`, `χ = 1(u ≤ s_max) 1(G_{<u})`. -/
theorem label_replace {Ω : Type*} (G : ℕ → Set Ω) (hG : ∀ s s', s ≤ s' → G s' ⊆ G s)
    (Ψ : ℕ → ℝ≥0∞) (hΨ : Antitone Ψ) {u s smax : ℕ} (hus : u ≤ s) (hs : s ≤ smax) (ω : Ω) :
    (G s).indicator 1 ω * Ψ s ≤
      ((if u ≤ smax then (G u).indicator (1 : Ω → ℝ≥0∞) ω else 0) * Ψ u) := by
  rw [if_pos (hus.trans hs)]
  by_cases hω : ω ∈ G s
  · have hω' : ω ∈ G u := hG u s hus hω
    simp only [Set.indicator_of_mem hω, Set.indicator_of_mem hω', Pi.one_apply, one_mul]
    exact hΨ hus
  · simp [Set.indicator_of_notMem hω]

namespace JitterLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {θ : ℝ≥0∞}
  (J : JitterLaw Ω P θ)

/-- **The recursion of Lemma A.5**, probabilistic skeleton: a chain of `k` pivot steps, each
followed by a pathwise bound (integral, then block bound). -/
theorem pil_chain (k : ℕ) (Z : ℕ → Ω → ℝ≥0∞) (Φ : ℕ → ℕ → Ω × ℝ → ℝ≥0∞)
    (hΦ : ∀ i n, JMeas (J.F n) (Φ i n)) (Φbar : ℕ → Ω × ℝ → ℝ≥0∞)
    (hbar : ∀ i, Measurable (Φbar i)) (hdom : ∀ i n x, Φ i n x ≤ Φbar i x)
    (hstep : ∀ i < k, ∀ ω, Z i ω ≤ ∑' n, (J.A n).indicator (fun ω => Φ i n (ω, J.q n ω)) ω)
    (hnext : ∀ i < k, ∀ ω, ∫⁻ t, Φbar i (ω, t) ≤ Z (i + 1) ω) :
    ∫⁻ ω, Z 0 ω ∂P ≤ θ ^ k * ∫⁻ ω, Z k ω ∂P := by
  -- `E[Z i] ≤ θ^{k-i} E[Z k]`, by downward induction
  have key : ∀ j, j ≤ k → ∫⁻ ω, Z (k - j) ω ∂P ≤ θ ^ j * ∫⁻ ω, Z k ω ∂P := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hi : k - (j + 1) < k := by omega
      have h1 := J.pivot_step (Φ (k - (j + 1))) (hΦ _) (Φbar (k - (j + 1))) (hbar _)
        (hdom _)
      have h2 : ∫⁻ ω, Z (k - (j + 1)) ω ∂P ≤
          ∫⁻ ω, ∑' n, (J.A n).indicator (fun ω => Φ (k - (j + 1)) n (ω, J.q n ω)) ω ∂P :=
        lintegral_mono fun ω => hstep _ hi ω
      have h3 : ∫⁻ ω, (∫⁻ t, Φbar (k - (j + 1)) (ω, t)) ∂P ≤ ∫⁻ ω, Z (k - j) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        have := hnext _ hi ω
        rwa [show k - (j + 1) + 1 = k - j by omega] at this
      calc ∫⁻ ω, Z (k - (j + 1)) ω ∂P
          ≤ θ * ∫⁻ ω, (∫⁻ t, Φbar (k - (j + 1)) (ω, t)) ∂P := h2.trans h1
        _ ≤ θ * ∫⁻ ω, Z (k - j) ω ∂P := by gcongr
        _ ≤ θ * (θ ^ j * ∫⁻ ω, Z k ω ∂P) := by gcongr; exact ih (by omega)
        _ = θ ^ (j + 1) * ∫⁻ ω, Z k ω ∂P := by rw [← mul_assoc, ← pow_succ']
  simpa using key k le_rfl

end JitterLaw

end RankFull
