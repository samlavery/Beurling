module

public import RequestProject.Beurling.Model.TBound
public import RequestProject.Beurling.Construction.HBSDerive
public import RequestProject.Beurling.Construction.LandingDerive

/-!
# (HBS) and Lemma 6.26 on `Good(< t)` (Remark *horizon*)

The whole-path derivation of (HBS) (`Construction.sparsityInputs_of_cluster`) reads the queue
bound of Theorem 6.6(ii) at every slot and the cluster event at every height. Here the same
induction on the height is run **up to a horizon `Z`**, reading

* the queue bound `Q_j ≤ B(s_j)` only at the slots `j = slotIdx v`, `v ≤ Z` (`lag_local`:
  Corollary 3.8 needs the queue only at the slot of `x`);
* the cluster event only at the heights `v ≤ Z` (`lemma626_at`: Lemma 6.26 at `v` needs it only
  at `v`).

On `Good(< t)` these are among the queue constraints and events of time `< t` (strictly earlier
than the horizon), as in Remark *horizon* of the paper.
-/

@[expose] public section

open MeasureTheory Set Real Oscillation Absorbed Target CaplLink QueueMono InitialRange
  Construction SlotModel LagSplit QueueBound Bookkeeping

namespace BModel

section Lag

variable {X₀ : ℕ} (M : SlotModel X₀)

/-- `Landing.toSlotData` with the queue bound read only at the slot of `x`. -/
theorem Landing.toSlotData_loc (hX : 10 ^ 8 ≤ Real.log X₀) {N W x : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hQ : (M.queue (M.slotIdx x) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx x)))
    (h : M.Landing N W x) : SlotData N (M.T x) (queueB X₀ x) W x := by
  have hX₀ : 1 ≤ X₀ := by
    have := one_lt_of_logX (Nat.cast_nonneg _) hX
    exact_mod_cast this.le
  obtain ⟨C, Ep, Em, ε, c, lp, lm, F, Sp, Sm, hF, hN, hC0, hCA, hlp, hlm, hSp, hSm, hgp, hgm,
    hcp, hcm, hEp0, hEp, hEm0, hEm, hWp, hWm, hε⟩ := h
  obtain ⟨hs1, -, hT1, hT2⟩ := M.mem_slot hX₀ hx
  set k := M.slotIdx x
  have hV := M.count_identity k
  have hQA := M.queue_sub_slotArr k
  have hQB : (M.queue k : ℝ) ≤ queueB X₀ x :=
    hQ.trans (queueBScale_le (Nat.cast_nonneg _) hX hx hs1)
  refine ⟨(X₀ : ℝ) - 1 + k, M.queue k, M.slotArr k, C, Ep, Em, M.ϑ, ε, c, lp, lm, F, Sp, Sm,
    hF, ?_, hT1, hT2, M.hϑ0, M.hϑ, hC0, hCA, by exact_mod_cast hQA,
    hQB, hlp, hlm, hSp, hSm, hgp, hgm, hcp, hcm, hEp0, hEp, hEm0,
    hEm, hWp, hWm, hε⟩
  rw [hN, hV]; push_cast; ring

/-- `LandingInit.abs_le` with the queue bound read only at the slot of `x`. -/
theorem LandingInit.abs_le_loc (hX : 10 ^ 8 ≤ Real.log X₀) {N W x : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hearly : x < (X₀ : ℝ) + 2 * capH X₀ x)
    (hQ : (M.queue (M.slotIdx x) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx x)))
    (h : M.LandingInit N W x) : |N - M.T x| ≤ queueB X₀ X₀ + W + 5 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX₀ : 1 ≤ X₀ := by exact_mod_cast hX1.le
  obtain ⟨C, Ep, Em, ε, c, lp, lm, F, Sp, Sm, hF, hN, hC0, hCA, hlp, hlm, hSp, hSm, hgp, hgm,
    hcp, hcm, hEp0, hEp, hEm0, hEm, hWp, hWm, hε⟩ := h
  obtain ⟨hs1, -, hT1, hT2⟩ := M.mem_slot hX₀ hx
  set k := M.slotIdx x
  have hV := M.count_identity k
  have hQA := M.queue_sub_slotArr k
  have h2 := lt_two_mul_of_initial hX0 hX hx hearly
  have hQ' : (M.queue k : ℝ) ≤ queueB X₀ X₀ := by
    rwa [queueBScale_eq_init (by linarith) (lt_of_le_of_lt hs1 h2)] at hQ
  have hB0 := queueB_nonneg hX0 hX (le_refl (X₀ : ℝ))
  have hN' : N = (((X₀ : ℝ) - 1 + k) + 1 + (M.queue k : ℝ)) - C + Ep - Em := by
    rw [hN, hV]; push_cast; ring
  have := initial_lag_of_slots F hF Sp Sm hN' hT1 hT2 M.hϑ0 M.hϑ hC0 hCA
    (by exact_mod_cast hQA) hQ' hlp hlm hSp hSm hgp hgm hcp hcm hEp0 hEp hEm0 hEm hWp hWm hε
  rw [_root_.abs_le]; constructor <;> linarith [this.1, this.2]

/-- **The lag bound at one height** (Corollary 3.8 / Proposition 4.1, `lag_of_slotData`), from
the landing data at `x` and the queue bound at the slot of `x` only. -/
theorem lag_local {θ : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2 - 1 / 10000)
    (hX : 10 ^ 8 ≤ Real.log X₀) (N : ℝ → ℝ) (κp : ℝ → ℝ)
    (hκp : ∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x)
    (hland : ∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing (N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x)
    (hinit : ∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit (N x) (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)
    {x : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hQ : (M.queue (M.slotIdx x) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx x))) :
    |N x - M.T x| ≤ x ^ lagExponent θ := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rcases le_or_gt ((X₀ : ℝ) + 2 * capH X₀ x) x with hlate | hearly
  · have hLx : 0 < Real.log x := by
      have h1 := one_lt_of_logX hX0 hX
      have := Real.log_le_log (by linarith) hx
      linarith
    obtain ⟨-, hstd, -⟩ := capH_conditions hX0 hX hx
    have hH : 1 ≤ capH X₀ x := le_trans (Real.one_le_exp (by positivity)) hstd
    have h12 := (Landing.toSlotData_loc M hX hx hQ (hland x hx hlate)).two_sided
    have e : -(capH X₀ x / 2 * (1 + κp x / Real.log x)) =
        -(capH X₀ x / 2) * (1 + κp x / Real.log x) := by ring
    rw [e] at h12
    have hB0 := queueB_nonneg hX0 hX hx
    exact lag_rpow_of_queue hθ1 hθ2 hX0 hX hx
      (abs_lag_le_of_two_sided hLx (hκp x hx).1 (hκp x hx).2 hH hB0 le_rfl h12.1 h12.2)
  · exact lag_rpow_initial hθ1 hθ2 hX0 hX hx (hκp X₀ le_rfl).1 (hκp X₀ le_rfl).2
      (LandingInit.abs_le_loc M hX hx hearly hQ (hinit x hx hearly))

end Lag

section L626

open BSCert.Capl AbsorbEmpty

/-- **Lemma 6.26 at one height, reading the cluster event only at that height**: as
`Construction.lemma626_local`, with the cluster event `ClusterUpTo P X₀ (4v/log¹¹ v) M̄₁(v)` at
`v` only (Lemma 6.26 depends on Proposition 6.11 at the height `v` and (HBS) up to `2y(2v)`). -/
theorem lemma626_at {P : BeurlingSystem} {X₀ : ℕ} {R : GreedyRun X₀} {A : Set ℝ}
    {latest : ℝ → ℝ} (C : AbsorbedCoupling P R.M R.H R.U A latest) {θ X0m η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hX0m : 100 ≤ Real.log X0m) (hX0mX : (X₀ : ℝ) / 2 + 1 ≤ X0m)
    (hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊)
    {v : ℝ} (hv : (X₀ : ℝ) ≤ v)
    (hclv : ClusterUpTo P X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v))
    (hHBS : P.HBS X0m (2 * absorbYAt X₀ (2 * v)) η1 η2 ε1) :
      (Absorbed.localCountA A v (v + v ^ (θ / 2)) : ℝ) ≤ v ^ (θ / 2) * Real.log v ^ (-4 : ℤ) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  obtain ⟨hv0, hL, hl, -⟩ := height_facts hX0 hX hv
  set h := v ^ (θ / 2) with hh
  set L := Real.log v with hLdef
  have hv1 : 1 < v := by linarith
  have h1 : 1 ≤ h := Real.one_le_rpow hv1.le (by linarith)
  have hlt : h < v := by
    have := Real.rpow_lt_rpow_of_exponent_lt hv1 (show θ / 2 < 1 by linarith)
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
    unfold capCd; have := Construction.one_le_capM1 hX0 hX hv; positivity
  refine BeurlingSystem.HBS.lemma626 hHBS hX0m h1 hlt hy4 le_rfl hCd0 (by linarith)
    ?_ ?_ hus hll hη hu01 hu0 h81
  · intro n hn hun hnu
    exact C.smooth hRH hU hX hn (by linarith) h2v
  · intro d hd hdh hdle
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
    have hM1 := Construction.one_le_capM1 hX0 hX hv
    refine (window_count_divisor P he2 hX0mX hfl hclv (by linarith) h1 (by linarith)
      huZ d hdh).trans ?_
    exact window_const_le hM1 hv0 (by linarith) (by linarith) hlt.le


end L626

section HBS

open AbsorbEmpty

/-- **(HBS) up to a horizon** (Remark *horizon*): the induction of
`Construction.sparsityInputs_of_cluster`, reading the queue bound only at the slots of the heights
`v ≤ Z` and the cluster event only at the heights `v ≤ Z`. -/
theorem hbs_local {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (M : SlotModel X₀) (ω : JitterΩ)
    (hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1) (hinf : {k | placedAt M k}.Infinite) (a : ℕ → ℝ)
    (hT : ∀ x, M.T x = target X₀ (kappaParam X₀) (countA (realisedA M (capH X₀) ω))
      (absorbedDensityCap (θ / 2) (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n))
      (osc θ (designedAlpha (realisedSystem M (capH X₀) ω) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a)
        (designedGamma (realisedSystem M (capH X₀) ω) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x)
    (κp : ℝ → ℝ) (hκp : ∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x)
    (hland : ∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing ((realisedSystem M (capH X₀) ω).N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x)
    (hinit : ∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit ((realisedSystem M (capH X₀) ω).N x)
        (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)
    {Z : ℝ} (hZ : (X₀ : ℝ) ≤ Z)
    (hQ : ∀ x, (X₀ : ℝ) ≤ x → x ≤ Z →
      (M.queue (M.slotIdx x) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx x)))
    (hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z → ClusterUpTo (realisedSystem M (capH X₀) ω) X₀
      (4 * v / Real.log v ^ 11) (capM1 X₀ v)) :
    ∀ v, (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ v → v ≤ Z →
      |(realisedSystem M (capH X₀) ω).N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
  set P := realisedSystem M (capH X₀) ω with hP
  set A := realisedA M (capH X₀) ω with hAdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hok := realisedOK_of M hω hX hTlow hinf
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C : AbsorbedCoupling P R.M R.H R.U A (realisedLatest M (capH X₀) ω) :=
    realisedCoupling hok
  set X0m : ℝ := (X₀ : ℝ) - capH X₀ X₀ / 2 with hX0mdef
  have h4H := four_capH_le hX0 hX (le_refl (X₀ : ℝ))
  have hX0m2 : (X₀ : ℝ) / 2 + 1 ≤ X0m := by
    have : (8 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀)
      rw [Real.exp_log (by linarith)] at this; linarith
    linarith
  have hX0mlog : 100 ≤ Real.log X0m := by
    have h1 : Real.log ((X₀ : ℝ) / 2) ≤ Real.log X0m :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have := Real.log_two_lt_d9
    linarith
  have hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊ :=
    fun w hw1 hw2 => realised_floor_eq hok hω hX hTlow hw1 hw2
  have hlag : ∀ x, (X₀ : ℝ) ≤ x → x ≤ Z → |P.N x - M.T x| ≤ x ^ lagExponent θ :=
    fun x hx hxZ => lag_local M hθ.1 hθ.2 hX P.N κp hκp hland hinit hx (hQ x hx hxZ)
  have hAu := realisedU_spec hok hω hX hTlow (θ := θ) (by linarith [hθ.1]) (by linarith [hθ.2])
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  -- (HBS) up to `z` from the error bound up to `z`
  have hHBS_of : ∀ z, (∀ v, X0m ≤ v → v ≤ z → |P.N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v) →
      P.HBS X0m z (1 / 1000) (1 / 1000) (hbsEps X₀) := by
    intro z herr
    exact
      { X0m_ge := by
          have : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) / 2 := by
            have := Real.add_one_le_exp (Real.log X₀)
            rw [Real.exp_log (by linarith)] at this; linarith
          linarith
        eta1_nonneg := by norm_num
        eta1_le := le_rfl
        eta2_nonneg := by norm_num
        eta2_le := le_rfl
        floor_eq := fun v h1 h2 _ => hfl v h1 h2
        err := fun v h1 h2 => herr v h1 h2
        eta2 := fun v h1 _ => hbsEps_mul_log_le hX (by linarith)
        eta1 := fun x K w hw => hbsEps_dyadic_sum_le hX K w (fun k hk =>
          ⟨(hw k hk).1, (hw k hk).2.1, by linarith [(hw k hk).2.2.1]⟩) }
  -- `T(X₀) = X₀`
  have hTX0 : M.T X₀ = X₀ := by
    rw [hT X₀]
    have hcA : countA A X₀ = 0 := countA_eq_zero hX0 (fun n hn hc => by
      have := (realisedA_large hok hω hX hTlow hn).2
      linarith)
    simp only [target, lt_irrefl, if_false, sub_self, intervalIntegral.integral_same, hcA]
    ring
  have hNX0 : P.N X₀ ≤ X₀ + (X₀ : ℝ) ^ lagExponent θ := by
    have := hlag X₀ le_rfl hZ
    rw [hTX0] at this
    linarith [(abs_le.mp this).2]
  -- the error bound, by induction on `⌊v⌋`
  have main : ∀ n : ℕ, ∀ v : ℝ, ⌊v⌋₊ = n → X0m ≤ v → v ≤ Z →
      |P.N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro v hvn hv hvZ
    rcases lt_or_ge v X₀ with hlow | hhigh
    · exact hbs_err_low hX hθ.2 P.N_mono hfl hNX0 hv hlow
    · have hv0 : 0 < v := by linarith
      have hvfl : (v : ℝ) < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
      have hdens : ∀ u, (X₀ : ℝ) ≤ u → u ≤ v →
          absorbedDensity (θ / 2) A (fun n => solveU (θ / 2) n) u ≤
            Real.log u ^ (-4 : ℤ) := by
        intro u hu huv
        have hHBSu : P.HBS X0m (2 * absorbYAt X₀ (2 * u)) (1 / 1000) (1 / 1000) (hbsEps X₀) := by
          refine hHBS_of _ (fun w hw1 hw2 => IH ⌊w⌋₊ ?_ w rfl hw1 ?_)
          have hw0 : 0 ≤ w := by linarith
          have hlt : (⌊w⌋₊ : ℝ) < ⌊v⌋₊ := by
            have h1 : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hw0
            rcases two_absorbYAt_two_le hX0 hX hu with hy | hy
            · have : (X₀ : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast Nat.le_floor hhigh
              linarith
            · linarith
          · rw [← hvn]; exact_mod_cast hlt
          · have h1 : 2 * absorbYAt X₀ (2 * u) ≤ v := by
              rcases two_absorbYAt_two_le hX0 hX hu with hy | hy <;> linarith
            linarith
        have hloc := lemma626_at C hX hθ.1 (by linarith [hθ.2]) rfl hω hX0mlog hX0m2 hfl hu
          (hcl u hu (huv.trans hvZ)) hHBSu
        exact absorbedDensity_le_of_localCount hb (by linarith) hAu C.locFin hu hloc
      have hW : AbsorbedWindowHyp (θ / 2) X₀ A (fun n => solveU (θ / 2) n) :=
        ⟨hb, by linarith [hθ.2], hX1.le, fun a ha => (hAu a ha).1, fun a ha => (hAu a ha).2,
          C.locFin⟩
      have hEA := absorbed_target_error_cap_loc hW (by linarith) hhigh hdens
      have hsp := switchOn_spacing (X₀ : ℝ)
      have hα : ∀ k, |designedAlpha P θ X₀ (kappaParam X₀) A (fun n => solveU (θ / 2) n)
          kappa0Param (switchOn X₀) a k| ≤ 2 := by
        intro k
        have hm := designedAlpha_mem P θ X₀ (kappaParam X₀) A (fun n => solveU (θ / 2) n)
          kappa0Param (switchOn X₀) a (heightScale_switchOn_pos θ hX1.le) k
        rw [abs_of_nonneg (by linarith [hm.1])]
        exact hm.2
      have hR := abs_osc_le (θ := θ) (γ := designedGamma P θ X₀ (kappaParam X₀) A
        (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a) hsp hα (x := v) (by linarith)
      have hR0 := osc_eq_zero_of_le (θ := θ) (α := designedAlpha P θ X₀ (kappaParam X₀) A
        (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a) (γ := designedGamma P θ X₀
        (kappaParam X₀) A (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a) hsp
        (by linarith : (0 : ℝ) < X₀) (switchOn_zero_ge _)
      have hl := hlag v hhigh hvZ
      rw [hT v] at hl
      exact hbs_err_high hX hθ.2 hhigh hl hEA hR hR0
  exact fun v h1 h2 => main ⌊v⌋₊ v rfl h1 h2

/-- **Lemma 6.26 up to a horizon** (Lemma 6.26 on `Good(< t)`): at every height `u ≥ X₀` with
`2y(2u) ≤ Z`, from the queue bound and the cluster event at heights `≤ Z` and the cluster event
at `u`. -/
theorem lemma626_horizon {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (M : SlotModel X₀) (ω : JitterΩ)
    (hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1) (hinf : {k | placedAt M k}.Infinite) (a : ℕ → ℝ)
    (hT : ∀ x, M.T x = target X₀ (kappaParam X₀) (countA (realisedA M (capH X₀) ω))
      (absorbedDensityCap (θ / 2) (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n))
      (osc θ (designedAlpha (realisedSystem M (capH X₀) ω) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a)
        (designedGamma (realisedSystem M (capH X₀) ω) θ X₀ (kappaParam X₀)
          (realisedA M (capH X₀) ω) (fun n => solveU (θ / 2) n) kappa0Param (switchOn X₀) a)
        (switchOn X₀)) x)
    (κp : ℝ → ℝ) (hκp : ∀ x ≥ (X₀ : ℝ), 0 ≤ κp x ∧ κp x ≤ Real.log x)
    (hland : ∀ x ≥ (X₀ : ℝ), (X₀ : ℝ) + 2 * capH X₀ x ≤ x →
      M.Landing ((realisedSystem M (capH X₀) ω).N x) (capH X₀ x / 2 * (1 + κp x / Real.log x)) x)
    (hinit : ∀ x ≥ (X₀ : ℝ), x < (X₀ : ℝ) + 2 * capH X₀ x →
      M.LandingInit ((realisedSystem M (capH X₀) ω).N x)
        (capH X₀ X₀ / 2 * (1 + κp X₀ / Real.log X₀)) x)
    {Z : ℝ} (hZ : (X₀ : ℝ) ≤ Z)
    (hQ : ∀ x, (X₀ : ℝ) ≤ x → x ≤ Z →
      (M.queue (M.slotIdx x) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx x)))
    (hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z → ClusterUpTo (realisedSystem M (capH X₀) ω) X₀
      (4 * v / Real.log v ^ 11) (capM1 X₀ v)) :
    ∀ u, (X₀ : ℝ) ≤ u → 2 * absorbYAt X₀ (2 * u) ≤ Z →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * u / Real.log u ^ 11) (capM1 X₀ u) →
      (Absorbed.localCountA (realisedA M (capH X₀) ω) u (u + u ^ (θ / 2)) : ℝ) ≤
        u ^ (θ / 2) * Real.log u ^ (-4 : ℤ) := by
  set P := realisedSystem M (capH X₀) ω with hP
  set A := realisedA M (capH X₀) ω with hAdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := by
    intro x hx
    rw [hT x]
    simp only [target, if_pos hx]
  have hok := realisedOK_of M hω hX hTlow hinf
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C : AbsorbedCoupling P R.M R.H R.U A (realisedLatest M (capH X₀) ω) :=
    realisedCoupling hok
  set X0m : ℝ := (X₀ : ℝ) - capH X₀ X₀ / 2 with hX0mdef
  have h4H := four_capH_le hX0 hX (le_refl (X₀ : ℝ))
  have hX0m2 : (X₀ : ℝ) / 2 + 1 ≤ X0m := by
    have : (8 : ℝ) ≤ X₀ := by
      have := Real.add_one_le_exp (Real.log X₀)
      rw [Real.exp_log (by linarith)] at this; linarith
    linarith
  have hX0mlog : 100 ≤ Real.log X0m := by
    have h1 : Real.log ((X₀ : ℝ) / 2) ≤ Real.log X0m :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have := Real.log_two_lt_d9
    linarith
  have hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊ :=
    fun w hw1 hw2 => realised_floor_eq hok hω hX hTlow hw1 hw2
  have hlag : ∀ x, (X₀ : ℝ) ≤ x → x ≤ Z → |P.N x - M.T x| ≤ x ^ lagExponent θ :=
    fun x hx hxZ => lag_local M hθ.1 hθ.2 hX P.N κp hκp hland hinit hx (hQ x hx hxZ)
  have hAu := realisedU_spec hok hω hX hTlow (θ := θ) (by linarith [hθ.1]) (by linarith [hθ.2])
  have hb : 0 < θ / 2 := by linarith [hθ.1]
  -- (HBS) up to `z` from the error bound up to `z`
  have hHBS_of : ∀ z, (∀ v, X0m ≤ v → v ≤ z → |P.N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v) →
      P.HBS X0m z (1 / 1000) (1 / 1000) (hbsEps X₀) := by
    intro z herr
    exact
      { X0m_ge := by
          have : (10 : ℝ) ^ 7 ≤ (X₀ : ℝ) / 2 := by
            have := Real.add_one_le_exp (Real.log X₀)
            rw [Real.exp_log (by linarith)] at this; linarith
          linarith
        eta1_nonneg := by norm_num
        eta1_le := le_rfl
        eta2_nonneg := by norm_num
        eta2_le := le_rfl
        floor_eq := fun v h1 h2 _ => hfl v h1 h2
        err := fun v h1 h2 => herr v h1 h2
        eta2 := fun v h1 _ => hbsEps_mul_log_le hX (by linarith)
        eta1 := fun x K w hw => hbsEps_dyadic_sum_le hX K w (fun k hk =>
          ⟨(hw k hk).1, (hw k hk).2.1, by linarith [(hw k hk).2.2.1]⟩) }
  have hmain := hbs_local hθ hX M ω hω hinf a hT κp hκp hland hinit hZ hQ hcl
  intro u hu huZ hclu
  have hHBSu : P.HBS X0m (2 * absorbYAt X₀ (2 * u)) (1 / 1000) (1 / 1000) (hbsEps X₀) :=
    hHBS_of _ (fun w hw1 hw2 => hmain w hw1 (hw2.trans huZ))
  exact lemma626_at C hX hθ.1 (by linarith [hθ.2]) rfl hω hX0mlog hX0m2 hfl hu hclu hHBSu

end HBS

end BModel
