module

public import RequestProject.Beurling.Construction.Greedy
public import RequestProject.Beurling.Construction.RankinBeurling
public import RequestProject.Beurling.Construction.YBounds

/-!
# Lemma 6.26, step (i): the elements of `A` are `2y`-smooth (the decision order)

The realised primes of the construction are of two kinds: the rational primes below `X₀`, and the
jittered primes, the prime decided at relative slot `k + 1` landing at `s + H(s)(U - 1/2)`,
`s = s_{k+1}` (`primeValueOf`). A `PrimeOrigin` records, for each prime index `j` of the system,
which kind it is (`src j = none`: rational; `src j = some k`: decided at relative slot `k + 1`).

The **decision order** puts all rational primes first and the jittered primes in slot order
(`decisionKey`). The **latest prime** of an element `e` is a prime of `e` that is last in this
order (`latestIdx`, `latestPrime`).

Step (i) of Lemma 6.26 (`PrimeOrigin.smooth_of_latest`): if the jitters lie in `[0, 1]`,
`H ≥ 0` is non-decreasing on `[X₀, ∞)` with `4 H(v) ≤ v` there, and the latest prime `r` of `e`
satisfies `r < y` and `r ≥ X₀ - H(X₀)/2`, then every prime of `e` is `< 2y`. (The paper has
`p ≤ (1 + e^{-10⁶}) r`; here `p ≤ 9r/7` from `4H(v) ≤ v`, which is all `p < 2y` needs.)
For the paper's `H = max(H_std, M̄₁²)` the conditions on `H` are proved
(`capH_monotoneOn`, `four_capH_le`).
-/

@[expose] public section

open Set CaplLink QueueMono

namespace Construction

/-- **The origin of the realised primes**: each prime index `j` of `P` is either a rational prime
`< X₀` (`src j = none`) or the prime placed by the greedy rule at relative slot `k + 1`
(`src j = some k`), with value `primeValueOf M H U k`. -/
structure PrimeOrigin (P : BeurlingSystem) {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ)
    (U : ℕ → ℝ) where
  /-- the origin of the prime `p_j` -/
  src : ℕ → Option ℕ
  rational_lt : ∀ j, src j = none → P.p j < X₀
  jittered_eq : ∀ j k, src j = some k → placedAt M k ∧ P.p j = primeValueOf M H U k

namespace PrimeOrigin

variable {P : BeurlingSystem} {X₀ : ℕ} {M : SlotModel X₀} {H : ℝ → ℝ} {U : ℕ → ℝ}
  (O : PrimeOrigin P M H U)

/-- **The decision order**: rational primes first (key `0`), then the jittered primes in slot
order (key `k + 1` for the prime decided at relative slot `k + 1`). -/
def decisionKey (j : ℕ) : ℕ :=
  match O.src j with
  | none => 0
  | some k => k + 1

/-- **The latest-prime map** (index): a prime of `e` that is last in the decision order
(`0` for `e = 0`). -/
noncomputable def latestIdx (e : ℕ →₀ ℕ) : ℕ :=
  if h : e.support.Nonempty then (e.support.exists_max_image O.decisionKey h).choose else 0

/-- **The latest prime** `r` of an element `e`. -/
noncomputable def latestPrime (e : ℕ →₀ ℕ) : ℝ := P.p (O.latestIdx e)

lemma latestIdx_spec {e : ℕ →₀ ℕ} (he : e.support.Nonempty) :
    O.latestIdx e ∈ e.support ∧ ∀ j ∈ e.support, O.decisionKey j ≤ O.decisionKey (O.latestIdx e) := by
  unfold latestIdx
  rw [dif_pos he]
  exact (e.support.exists_max_image O.decisionKey he).choose_spec

/-- **Step (i) of Lemma 6.26 (smoothness from the decision order)**. Suppose the jitters lie in
`[0, 1]`, `H ≥ 0` is non-decreasing on `[X₀, ∞)` with `4 H(v) ≤ v` there, and the latest prime
`r` of `e` satisfies `X₀ - H(X₀)/2 ≤ r < y`. Then every prime of `e` is `< 2y`: `e` is a
`2y`-smooth element. -/
theorem smooth_of_latest (R : GreedyRun X₀) (O : PrimeOrigin P R.M R.H R.U)
    (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1) (hH0 : ∀ v, 0 ≤ R.H v)
    (hHmono : MonotoneOn R.H (Ici (X₀ : ℝ))) (hHle : ∀ v ≥ (X₀ : ℝ), 4 * R.H v ≤ v)
    (hX : 0 < X₀) {e : ℕ →₀ ℕ} {y : ℝ}
    (hr0 : (X₀ : ℝ) - R.H X₀ / 2 ≤ O.latestPrime e) (hry : O.latestPrime e < y) :
    e ∈ P.smoothElems (2 * y) := by
  intro j hj
  have hne : e.support.Nonempty := ⟨j, hj⟩
  obtain ⟨-, hmax⟩ := O.latestIdx_spec hne
  have hkey := hmax j hj
  set jr := O.latestIdx e with hjr
  have hX0 : (0 : ℝ) < X₀ := by exact_mod_cast hX
  have hHX := hHle X₀ le_rfl
  -- the latest prime is above `X₀/2`
  have hr_half : (X₀ : ℝ) < 2 * O.latestPrime e := by linarith [hH0 X₀]
  unfold latestPrime at hr_half hry
  rw [← hjr] at hr_half hry
  cases hsj : O.src j with
  | none =>
    have := O.rational_lt j hsj
    linarith
  | some kp =>
    cases hsr : O.src jr with
    | none =>
      exfalso
      simp only [decisionKey, hsj, hsr] at hkey
      omega
    | some kr =>
      have hk : kp ≤ kr := by
        simp only [decisionKey, hsj, hsr] at hkey
        omega
      obtain ⟨-, hpv⟩ := O.jittered_eq j kp hsj
      obtain ⟨-, hrv⟩ := O.jittered_eq jr kr hsr
      set sp := R.M.slot (kp + 1)
      set sr := R.M.slot (kr + 1)
      have hsp : (X₀ : ℝ) ≤ sp := R.slot_ge _
      have hsr' : (X₀ : ℝ) ≤ sr := R.slot_ge _
      have hspr : sp ≤ sr := R.M.slot_mono (by omega)
      have hHspr : R.H sp ≤ R.H sr := hHmono (mem_Ici.mpr hsp) (mem_Ici.mpr hsr') hspr
      have hp := (landing_mem_box (s := sp) (hH0 sp) (hU (kp + 1))).2
      have hr := (landing_mem_box (s := sr) (hH0 sr) (hU (kr + 1))).1
      have hHsr := hHle sr hsr'
      unfold primeValueOf at hpv hrv
      rw [← hpv] at hp
      rw [← hrv] at hr
      linarith

end PrimeOrigin

end Construction

end
