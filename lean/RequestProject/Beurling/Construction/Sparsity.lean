module

public import RequestProject.Beurling.Construction.Fix
public import RequestProject.Beurling.Construction.StepOne
public import RequestProject.Beurling.Construction.Window
public import RequestProject.Beurling.Construction.Cond81
public import RequestProject.Beurling.Construction.RealisedPrimes

/-!
# Lemma 6.26 and the Rankin bound for `A`, for the construction

Here the two inputs that `Theorem21InputsFix` takes about the absorbed set `A` are derived:

* **Lemma 6.26** (`lemma626_construction`): `#(A ∩ [v, v + v^{θ/2}]) ≤ v^{θ/2} (log v)^{-4}` for
  every `v ≥ X₀`;
* **the Rankin bound for `A`** (`rankinA_construction`, proof of Lemma 4.4):
  `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` for `log x > (log X₀)²`;

from
* the **coupling** of `A` with the construction (`AbsorbedCoupling`): the origin of every realised
  prime (rational `< X₀`, or the prime decided at a slot of the greedy run with jitter width `H`),
  `A ⊆` the absorbed set (5) for the latest-prime map `latest`, and `latest n` being the latest
  prime (in the decision order) of an element of value `n`;
* the hypothesis **(HBS)** for the realised system (at every height), with `log X₀⁻ ≥ 100` and
  `X₀⁻ ≥ X₀/2 + 1`;
* the **cluster event** (Proposition 6.11): at every `v ≥ X₀`, every grid window at a dyadic
  height `X₀/2 ≤ z ≤ 4v/(log v)^{11}` holds at most `M̄₁(v)` elements of `N`.

Step (i) is `PrimeOrigin.smooth_of_latest`, step (iv) is `window_count_divisor`, condition (81) and
`(∗)` are `cond81_window` / `rankin_conditions` (Theorem 6.23(b)), and steps (ii), (iii), (v), (vi)
are `BeurlingSystem.HBS.lemma626` / `HBS.countA_le_sigmaStar`. The threshold `y` of Lemma 6.26 at
`u` is `y(2u)` (it bounds `y(n)` for every `n ≤ 2u`, `y` being non-decreasing), and
`C_d = M̄₁(u) (log u)^6/2` (`capCd`).
-/

@[expose] public section

open Set CaplLink QueueMono InitialRange AbsorbEmpty

namespace Construction

/-- **The coupling of the absorbed set with the construction**: the origin of the realised primes
(for the greedy run `R`), `A ⊆` the absorbed set (5) for the latest-prime map `latest`, and every
`n ∈ A` is the value of an element whose latest prime (in the decision order) is `latest n`. -/
structure AbsorbedCoupling (P : BeurlingSystem) {X₀ : ℕ} (M : SlotModel X₀) (H : ℝ → ℝ)
    (U : ℕ → ℝ) (A : Set ℝ) (latest : ℝ → ℝ) where
  /-- the origin of every realised prime -/
  origin : PrimeOrigin P M H U
  rule : A ⊆ absorbedRule (10 ^ 7) (jitteredPrimesOf M H U) latest (absorbY X₀)
  rep : ∀ n ∈ A, ∃ e, P.val e = n ∧ latest n = origin.latestPrime e

section

variable {P : BeurlingSystem} {X₀ : ℕ} {R : GreedyRun X₀} {A : Set ℝ} {latest : ℝ → ℝ}

/-- `y(n) ≤ y(x)` for `n ≤ x`, `X₀ ≤ x`. -/
lemma absorbY_le_absorbYAt {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) {n : ℝ}
    (hnx : (n : ℝ) ≤ x) (hx : X₀ ≤ x) : absorbY X₀ n ≤ absorbYAt X₀ x := by
  have hX1 := one_lt_of_logX hX0 hX
  unfold absorbY
  have h1 : X₀ ≤ dyadicScale X₀ (max X₀ n) := le_dyadicScale (by linarith) (le_max_left _ _)
  have h2 : dyadicScale X₀ (max X₀ n) ≤ max X₀ n :=
    dyadicScale_le (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  exact absorbYAt_mono hX0 hX h1 (h2.trans (max_le hx hnx))

variable (C : AbsorbedCoupling P R.M R.H R.U A latest)

include C in
/-- **`A` is locally finite**: its members are values of elements of the semigroup, and there are
finitely many elements of value below any bound. -/
lemma AbsorbedCoupling.locFin : Absorbed.LocFin A := fun x =>
  ((P.finite_val_le x).image P.val).subset fun n hn => by
    obtain ⟨e, hev, -⟩ := C.rep n hn.1
    exact ⟨e, by rw [Set.mem_setOf_eq, hev]; exact hn.2, hev⟩

include C in
/-- The latest prime of `n ∈ A` is `≥ X₀⁻ = X₀ - H(X₀)/2`. -/
lemma AbsorbedCoupling.latest_ge (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) {n : ℝ} (hn : n ∈ A) :
    (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ latest n := by
  have h := GreedyRun.jittered_ge_of_floor R hU (by rw [hRH]; exact capH_nonneg X₀)
    (fun s hs => by rw [hRH]; exact JitterFloor.capH_floor (Nat.cast_nonneg _) hX hs)
  rw [hRH] at h
  exact h _ (C.rule hn).2.1

include C in
/-- `2y(x) > X₀` if `A` has an element `≤ x` (`X₀ ≤ x`). -/
lemma AbsorbedCoupling.two_y_gt (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) {n : ℝ} (hn : n ∈ A) {x : ℝ} (hnx : (n : ℝ) ≤ x)
    (hx : (X₀ : ℝ) ≤ x) : (X₀ : ℝ) < 2 * absorbYAt X₀ x := by
  have h1 := C.latest_ge hRH hU hX hn
  have h2 := (C.rule hn).2.2
  have h3 := absorbY_le_absorbYAt (Nat.cast_nonneg _) hX hnx hx
  have h4 := four_capH_le (Nat.cast_nonneg _) hX (le_refl (X₀ : ℝ))
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) hX
  linarith

include C in
/-- **Step (i) for `A`**: every `n ∈ A` with `n ≤ x` (`X₀ ≤ x`) is the value of a
`2y(x)`-smooth element. -/
lemma AbsorbedCoupling.smooth (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hX : 10 ^ 8 ≤ Real.log X₀) {n : ℝ} (hn : n ∈ A) {x : ℝ} (hnx : (n : ℝ) ≤ x)
    (hx : (X₀ : ℝ) ≤ x) : ∃ e ∈ P.smoothElems (2 * absorbYAt X₀ x), P.val e = n := by
  obtain ⟨e, hev, hlat⟩ := C.rep n hn
  refine ⟨e, ?_, hev⟩
  have hX0 : 0 < X₀ := by
    have := one_lt_of_logX (Nat.cast_nonneg _) hX
    exact_mod_cast (show (0 : ℝ) < X₀ by linarith)
  have h1 := C.latest_ge hRH hU hX hn
  have h2 := (C.rule hn).2.2
  have h3 := absorbY_le_absorbYAt (Nat.cast_nonneg _) hX hnx hx
  rw [hlat] at h1 h2
  refine C.origin.smooth_of_latest R hU (by rw [hRH]; exact capH_nonneg X₀)
    (by rw [hRH]; exact capH_monotoneOn (Nat.cast_nonneg _) hX)
    (fun v hv => by rw [hRH]; exact four_capH_le (Nat.cast_nonneg _) hX hv) hX0
    (by have := congrFun hRH (X₀ : ℝ); rw [this]; exact h1) (lt_of_lt_of_le h2 h3)

end

/-- `(log v)^{11} ≤ v^{θ_b}` for `v > 0`, `log v ≥ 10⁸`, `θ ≥ 1/20`. -/
lemma log_pow_le_rpow {v θ : ℝ} (hv0 : 0 < v) (hv : 10 ^ 8 ≤ Real.log v) (hθ : 1 / 20 ≤ θ) :
    Real.log v ^ 11 ≤ v ^ (thetaB θ) := by
  set L := Real.log v with hL
  have hv1 : 1 ≤ v := by
    by_contra hc; push_neg at hc
    have := Real.log_nonpos hv0.le hc.le; linarith
  have h1 : v ^ (1 / 20 : ℝ) ≤ v ^ (thetaB θ) :=
    Real.rpow_le_rpow_of_exponent_le hv1 (thetaB_ge hθ)
  have h2 : v ^ (1 / 20 : ℝ) = Real.exp (L / 220) ^ 11 := by
    rw [Real.rpow_def_of_pos hv0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : L ≤ Real.exp (L / 220) := by
    have := Real.pow_div_factorial_le_exp (L / 220) (by positivity) 2
    simp [Nat.factorial] at this
    nlinarith
  have h4 : L ^ 11 ≤ Real.exp (L / 220) ^ 11 := pow_le_pow_left₀ (by linarith) h3 11
  linarith

/-- No element of `A` in `[v, w]`: the local count vanishes. -/
lemma localCountA_eq_zero {A : Set ℝ} {v w : ℝ} (_hw : 0 ≤ w)
    (h : ∀ n ∈ A, ¬ (v ≤ n ∧ (n : ℝ) ≤ w)) : Absorbed.localCountA A v w = 0 := by
  unfold Absorbed.localCountA
  suffices hE : A ∩ Set.Icc v w = ∅ by rw [hE]; simp
  exact Set.eq_empty_of_forall_notMem fun n ⟨hnA, hn⟩ => h n hnA hn

/-- No element of `A` up to `x`: the count vanishes. -/
lemma countA_eq_zero {A : Set ℝ} {x : ℝ} (_hx : 0 ≤ x) (h : ∀ n ∈ A, ¬ (n : ℝ) ≤ x) :
    Absorbed.countA A x = 0 := by
  unfold Absorbed.countA
  suffices hE : A ∩ Set.Icc 1 x = ∅ by rw [hE]; simp
  exact Set.eq_empty_of_forall_notMem fun n ⟨hnA, hn⟩ => h n hnA hn.2

/-- **Lemma 6.26 for the construction.** Let `log X₀ ≥ 10⁸`, `θ ∈ [1/20, 1/2]`, `R` a greedy run
with jitter width `H = max(H_std, M̄₁²)` and jitters in `[0, 1]`, coupled with `A` and the
latest-prime map (`AbsorbedCoupling`). Suppose the realised system satisfies (HBS) at every height
(with `log X₀⁻ ≥ 100`, `X₀⁻ ≥ X₀/2 + 1`) and the cluster event holds at every `v ≥ X₀` (grid windows
at dyadic heights `≤ 4v/(log v)^{11}` hold at most `M̄₁(v)` elements). Then for every `v ≥ X₀`,
`#(A ∩ [v, v + v^{θ/2}]) ≤ v^{θ/2} (log v)^{-4}`. -/
theorem lemma626_construction {P : BeurlingSystem} {X₀ : ℕ} {R : GreedyRun X₀} {A : Set ℝ}
    {latest : ℝ → ℝ} (C : AbsorbedCoupling P R.M R.H R.U A latest) {θ X0m η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (hθ1 : 1 / 20 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hHBS : ∀ z, P.HBS X0m z η1 η2 ε1) (hX0m : 100 ≤ Real.log X0m)
    (hX0mX : (X₀ : ℝ) / 2 + 1 ≤ X0m)
    (hcl : ∀ v ≥ (X₀ : ℝ), ClusterUpTo P X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v)) :
    ∀ v ≥ (X₀ : ℝ),
      (Absorbed.localCountA A v (v + v ^ (thetaB θ)) : ℝ) ≤ v ^ (thetaB θ) * Real.log v ^ (-4 : ℤ) := by
  intro v hv
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  obtain ⟨hv0, hL, hl, -⟩ := height_facts hX0 hX hv
  set h := v ^ (thetaB θ) with hh
  set L := Real.log v with hLdef
  have hv1 : 1 < v := by linarith
  have h1 : 1 ≤ h := Real.one_le_rpow hv1.le (thetaB_pos (by linarith)).le
  have hlt : h < v := by
    have := Real.rpow_lt_rpow_of_exponent_lt hv1 (show thetaB θ < 1 from (thetaB_le_quarter (by linarith)).trans_lt (by norm_num))
    rwa [Real.rpow_one] at this
  by_cases hne : ∃ n ∈ A, v ≤ n ∧ (n : ℝ) ≤ v + h
  swap
  · push_neg at hne
    rw [localCountA_eq_zero (by linarith) (fun n hn hc => absurd hc.2 (not_le.mpr (hne n hn hc.1)))]
    push_cast
    have : 0 < L ^ (-4 : ℤ) := zpow_pos (by linarith) _
    positivity
  obtain ⟨n0, hn0, -, hn0v⟩ := hne
  have h2v : (X₀ : ℝ) ≤ 2 * v := by linarith
  have hy := C.two_y_gt hRH hU hX hn0 (x := 2 * v) (by linarith) h2v
  obtain ⟨hus, hll, hη, hu01, hu0, h81⟩ := cond81_window hX0 hX hθ1 hθ2 hv (by linarith) le_rfl hy
  set y := absorbYAt X₀ (2 * v) with hydef
  have hy4 : 4 ≤ y := by
    have := exp_le_absorbYAt hX0 hX h2v
    obtain ⟨-, -, hl2, -⟩ := height_facts hX0 hX h2v
    have h4 : (4 : ℝ) ≤ Real.exp (8 * Real.log (Real.log (2 * v)) ^ 2) := by
      have := Real.add_one_le_exp (8 * Real.log (Real.log (2 * v)) ^ 2)
      nlinarith
    linarith
  have hCd0 : 0 < capCd X₀ v := by
    unfold capCd; have := one_le_capM1 hX0 hX hv; positivity
  refine BeurlingSystem.HBS.lemma626 (hHBS (2 * y)) hX0m h1 hlt hy4 le_rfl hCd0 (by linarith)
    ?_ ?_ hus hll hη hu01 hu0 h81
  · intro n hn hun hnu
    exact C.smooth hRH hU hX hn (by linarith) h2v
  · intro d hd hdh hdle
    have hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊ :=
      fun w hw1 hw2 => (hHBS w).floor_eq w hw1 hw2 le_rfl
    have hhL := log_pow_le_rpow hv0 hL hθ1
    rw [← hh] at hhL
    have hL11 : 0 < L ^ 11 := by positivity
    have huZ : v + h ≤ h * (4 * v / L ^ 11) := by
      rw [show h * (4 * v / L ^ 11) = 4 * v * (h / L ^ 11) by ring]
      have : 1 ≤ h / L ^ 11 := by rw [le_div_iff₀ hL11]; linarith
      nlinarith
    have he2 : 2 * Real.exp 2 ≤ (X₀ : ℝ) := by
      have h7 : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have : (16 : ℝ) ≤ X₀ := by
        have := Real.add_one_le_exp (Real.log X₀)
        rw [Real.exp_log (by linarith)] at this; linarith
      linarith
    have hM1 := one_le_capM1 hX0 hX hv
    refine (window_count_divisor P he2 hX0mX hfl (hcl v hv) (by linarith) h1 (by linarith)
      huZ d hdh).trans ?_
    exact window_const_le hM1 hv0 (by linarith) (by linarith) hlt.le

/-- **The Rankin bound for `A` for the construction** (proof of Lemma 4.4), under the hypotheses of
`lemma626_construction` other than the cluster event: for `x ≥ 1` with `log x > (log X₀)²`,
`#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}`. -/
theorem rankinA_construction {P : BeurlingSystem} {X₀ : ℕ} {R : GreedyRun X₀} {A : Set ℝ}
    {latest : ℝ → ℝ} (C : AbsorbedCoupling P R.M R.H R.U A latest) {X0m η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hHBS : ∀ z, P.HBS X0m z η1 η2 ε1) (hX0m : 100 ≤ Real.log X0m) :
    ∀ x ≥ (1 : ℝ), Real.log X₀ ^ 2 < Real.log x →
      Absorbed.countA A x ≤ x * Real.exp (-RankinMinorant.sigmaStar (Real.log X₀) (Real.log x)) := by
  intro x hx1 hlog
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  by_cases hne : ∃ n ∈ A, (n : ℝ) ≤ x
  swap
  · push_neg at hne
    rw [countA_eq_zero (by linarith) (fun n hn hc => absurd hc (not_le.mpr (hne n hn)))]
    positivity
  obtain ⟨n0, hn0, hn0x⟩ := hne
  have hxX : (X₀ : ℝ) ≤ x := by
    by_contra hc; push_neg at hc
    have h1 := Real.log_le_log (by linarith) hc.le
    have : Real.log X₀ < Real.log X₀ ^ 2 := by nlinarith
    linarith
  have hy := C.two_y_gt hRH hU hX hn0 hn0x hxX
  obtain ⟨hu, hll, hη, hlam⟩ := rankin_conditions hX0 hX hxX hy
  have hy4 : 4 ≤ absorbYAt X₀ x := by
    have := exp_le_absorbYAt hX0 hX hxX
    have h4 : (4 : ℝ) ≤ Real.exp (8 * Real.log (Real.log x) ^ 2) := by
      have := Real.add_one_le_exp (8 * Real.log (Real.log x) ^ 2)
      obtain ⟨-, -, hl2, -⟩ := height_facts hX0 hX hxX
      nlinarith
    linarith
  exact BeurlingSystem.HBS.countA_le_sigmaStar (hHBS (2 * absorbYAt X₀ x)) hX0m hy4 le_rfl hx1
    (fun n hn hnx => C.smooth hRH hU hX hn hnx hxX) hu hll hη hlam

end Construction

end
