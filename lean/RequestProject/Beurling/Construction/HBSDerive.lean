module

public import RequestProject.Beurling.Construction.HBSEps

/-!
# (HBS) for the realised system, derived

The hypothesis (HBS) (`BeurlingSystem.HBS`) for the realised system was an input of
`Theorem21InputsK` (inside `SparsityInputs`). Here it is **derived** from the other inputs: the
slot data (`PartIRestJ`: the target formula, the queue data and the landing data) and the cluster
event. The parameters are `X₀⁻ = X₀ - H(X₀)/2`, `η₁ = η₂ = 10⁻³` and the error profile
`ε₁ = hbsEps X₀`.

The argument is an induction on the height `v`:

* below `X₀⁻`, `N(v) = ⌊v⌋` (`realised_floor_eq`);
* on `[X₀⁻, X₀)`, `N(v)` is squeezed between `N(X₀⁻ - 1/2) = ⌊X₀⁻ - 1/2⌋` and
  `N(X₀) ≤ T(X₀) + X₀^η = X₀ + X₀^η` (`hbs_err_low`);
* for `v ≥ X₀`, `N(v) - ⌊v⌋ = (N - T) + E_rig + E_A + R(v) + (v - ⌊v⌋)` with the lag bound
  `|N - T| ≤ v^η` (`lag_of_slotData`), the fine rigid bound, `|R(v)| ≤ 2 v^θ log* v` and the
  absorbed bound `|E_A| ≤ 2 v^{θ/2}` (`hbs_err_high`). The absorbed bound needs
  `ρ_A ≤ (log u)^{-4}` on `[X₀, v]`, i.e. Lemma 6.26 at the heights `u ≤ v`
  (`lemma626_local`), which needs (HBS) only up to `2y(2u)`; since `2y(2u) < X₀` or
  `2y(2u) ≤ u/2` (`two_absorbYAt_two_le`), this is the induction hypothesis.

`Theorem21InputsL` is `Theorem21InputsK` with (HBS) removed (only the cluster event remains), and
`corollary_2_2_of_L` derives Corollary 2.2 from it.
-/

@[expose] public section

open MeasureTheory Set Real Oscillation Absorbed Target CaplLink QueueMono InitialRange
  AbsorbEmpty SlotModel

namespace Construction

lemma hbsEps_mul_self {X₀ : ℕ} {v : ℝ} (hv : 0 < v) :
    hbsEps X₀ v * v = 10 * v ^ (0.6 : ℝ) +
      min (kappaParam X₀ * v + kappaParam X₀ * X₀ + 1) (Rankin.smoothCount X₀ (2 * v) : ℝ) := by
  unfold hbsEps
  rw [add_mul, min_mul_of_nonneg _ _ hv.le]
  have h1 : 10 * v ^ (-(2 / 5 : ℝ)) * v = 10 * v ^ (0.6 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add_one hv.ne']; norm_num
  have h2 : (kappaParam (X₀ : ℝ) + (kappaParam X₀ * X₀ + 1) / v) * v =
      kappaParam X₀ * v + kappaParam X₀ * X₀ + 1 := by field_simp; ring
  have h3 : (Rankin.smoothCount X₀ (2 * v) : ℝ) / v * v = Rankin.smoothCount X₀ (2 * v) := by
    field_simp
  rw [h1, h2, h3]

/-- **The error at heights `v ≥ X₀`**: from the lag bound, the absorbed bound and the oscillation
bound, `|N - ⌊v⌋| ≤ ε₁(v) v`. -/
theorem hbs_err_high {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {θ : ℝ}
    (hθ2 : θ ≤ 1 / 2 - 1 / 10000) {cntA rhoA R : ℝ → ℝ} {N v : ℝ} (hv : (X₀ : ℝ) ≤ v)
    (hlag : |N - target X₀ (kappaParam X₀) cntA rhoA R v| ≤ v ^ lagExponent θ)
    (hA : |cntA v - ∫ u in (X₀ : ℝ)..v, rhoA u| ≤ 2 * v ^ (θ / 2))
    (hR : |R v| ≤ 2 * v ^ θ * (logStar v : ℝ)) (hR0 : R X₀ = 0) :
    |N - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hv1 : 1 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hκ0 := kappa_pos_aux hX
  have hκ1 : kappaParam (X₀ : ℝ) ≤ 1 := (kappa_le_aux hX).trans (by
    rw [div_le_one (by nlinarith)]; nlinarith)
  have hT : target X₀ (kappaParam X₀) cntA rhoA R v =
      v + rigidErr X₀ (kappaParam X₀) v + (cntA v - ∫ u in (X₀ : ℝ)..v, rhoA u) + R v := by
    simp only [target, if_neg (not_lt.mpr hv), rigidErr, hR0]; ring
  rw [hT] at hlag
  have hfl1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0.le
  have hfl2 : v < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
  have hr1 := abs_rigidErr_le_fine X₀ hκ0 hX1n hv
  have hr2 := Target.abs_rigidErr_le X₀ hκ0 hκ1 hX1n hv
  have hrig := le_min hr1 hr2
  have hη : lagExponent θ ≤ 0.6 := by
    unfold lagExponent; have := min_le_left θ (1 / 2 - θ); linarith
  have p1 : v ^ lagExponent θ ≤ v ^ (0.6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv1 hη
  have p2 : v ^ (θ / 2) ≤ v ^ (0.6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)
  have p3 : 1 ≤ v ^ (0.6 : ℝ) := Real.one_le_rpow hv1 (by norm_num)
  have hls := logStar_le_rpow hv1 (show (0 : ℝ) < 0.05 by norm_num)
  have hbig := rpow_ge_of_half hX (v := v) (by linarith) (show (0 : ℝ) ≤ 0.05 by norm_num)
  have h55 : 0 < v ^ (0.55 : ℝ) := by positivity
  have p4 : v ^ θ * (logStar v : ℝ) ≤ 3 * v ^ (0.6 : ℝ) := by
    calc v ^ θ * (logStar v : ℝ) ≤ v ^ θ * ((1 / 0.05 + 1) * v ^ (0.05 : ℝ)) := by gcongr
      _ = 21 * v ^ (θ + 0.05) := by rw [Real.rpow_add hv0]; ring
      _ ≤ 21 * v ^ (0.55 : ℝ) := by
          have := Real.rpow_le_rpow_of_exponent_le hv1 (show θ + 0.05 ≤ (0.55 : ℝ) by linarith)
          linarith
      _ ≤ 3 * v ^ (0.6 : ℝ) := by
          rw [show (0.6 : ℝ) = 0.55 + 0.05 by norm_num, Real.rpow_add hv0]
          nlinarith
  rw [hbsEps_mul_self hv0]
  have e := abs_le.mp hlag
  have a1 := abs_le.mp hA
  have a2 := abs_le.mp hR
  have a3 := abs_le.mp hrig
  rw [abs_le]; constructor <;> nlinarith

/-- **The error on `[X₀⁻, X₀)`**: squeezed between `N(X₀⁻ - 1/2)` and `N(X₀)`. -/
theorem hbs_err_low {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {θ : ℝ}
    (hθ2 : θ ≤ 1 / 2 - 1 / 10000) {N : ℝ → ℝ} (hmono : Monotone N)
    (hfl : ∀ w, 1 ≤ w → w < (X₀ : ℝ) - capH X₀ X₀ / 2 → N w = ⌊w⌋₊)
    (hX0 : N X₀ ≤ X₀ + (X₀ : ℝ) ^ lagExponent θ) {v : ℝ}
    (hv1 : (X₀ : ℝ) - capH X₀ X₀ / 2 ≤ v) (hv2 : v < X₀) :
    |N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
  have hXn : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hXn hX
  have hH := InitialRange.capH_le_rpow hXn hX (le_refl (X₀ : ℝ))
  have h4H := four_capH_le hXn hX (le_refl (X₀ : ℝ))
  have hH0 := capH_nonneg (X₀ : ℝ) X₀
  have hX8 : (8 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log (by linarith)] at this; linarith
  have hvh : (X₀ : ℝ) / 2 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  set w := (X₀ : ℝ) - capH X₀ X₀ / 2 - 1 / 2 with hw
  have hNw := hfl w (by linarith) (by linarith)
  have hwv : N w ≤ N v := hmono (by linarith)
  have hvX : N v ≤ N X₀ := hmono hv2.le
  have hw0 : 0 ≤ w := by linarith
  have hflw : w - 1 < (⌊w⌋₊ : ℝ) := by have := Nat.lt_floor_add_one w; linarith
  have hfl1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0.le
  have hfl2 : v < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
  -- powers
  have hη : lagExponent θ ≤ 1 / 4 := by
    unfold lagExponent; have := min_le_left θ (1 / 2 - θ); linarith
  have hX1' : (1 : ℝ) ≤ X₀ := hX1.le
  have q1 : (X₀ : ℝ) ^ lagExponent θ ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1' hη
  have q2 : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1' (by norm_num)
  have q3 : (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * v ^ (0.6 : ℝ) := by
    have hv1 : 1 ≤ v := by linarith
    calc (X₀ : ℝ) ^ (1 / 4 : ℝ) ≤ (2 * v) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hXn (by linarith) (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * v ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hv0.le
      _ ≤ 2 * v ^ (0.6 : ℝ) := by
          apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num))
            (by positivity) (by norm_num)
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have q4 : 1 ≤ v ^ (0.6 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hmin0 : 0 ≤ min (kappaParam (X₀ : ℝ) * v + kappaParam X₀ * X₀ + 1)
      (Rankin.smoothCount X₀ (2 * v) : ℝ) :=
    le_min (by have := kappa_pos_aux hX; positivity) (Nat.cast_nonneg _)
  rw [hbsEps_mul_self hv0, abs_le]
  constructor <;> nlinarith

/-- **(HBS) for the realised system, derived from the slot data and the cluster event.** -/
theorem sparsityInputs_of_cluster {θ : ℝ} (hθ : θ ∈ Icc (1 / 4 : ℝ) (1 / 2 - 1 / 10000))
    {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (M : SlotModel X₀) (ω : JitterΩ)
    (hω : ∀ j, ω j ∈ Icc (0 : ℝ) 1) (hinf : {k | placedAt M k}.Infinite) (a : ℕ → ℝ)
    (hI : PartIRestJ θ X₀ (realisedSystem M (capH X₀) ω) (realisedA M (capH X₀) ω)
      (fun n => solveU (θ / 2) n) a M)
    (hcl : ∀ v ≥ (X₀ : ℝ), ClusterUpTo (realisedSystem M (capH X₀) ω) X₀
      (4 * v / Real.log v ^ 11) (capM1 X₀ v)) :
    SparsityInputs X₀ (realisedSystem M (capH X₀) ω) := by
  set P := realisedSystem M (capH X₀) ω with hP
  set A := realisedA M (capH X₀) ω with hAdef
  obtain ⟨hT, hq, κp, hκp, hland, hinit⟩ := hI
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
  have hlag := lag_of_slotData hθ.1 hθ.2 hX M P.N hq κp hκp hland hinit
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
    have := hlag X₀ le_rfl
    rw [hTX0] at this
    linarith [(abs_le.mp this).2]
  -- the error bound, by induction on `⌊v⌋`
  have main : ∀ n : ℕ, ∀ v : ℝ, ⌊v⌋₊ = n → X0m ≤ v → |P.N v - ⌊v⌋₊| ≤ hbsEps X₀ v * v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    intro v hvn hv
    rcases lt_or_ge v X₀ with hlow | hhigh
    · exact hbs_err_low hX hθ.2 P.N_mono hfl hNX0 hv hlow
    · have hv0 : 0 < v := by linarith
      have hvfl : (v : ℝ) < ⌊v⌋₊ + 1 := Nat.lt_floor_add_one v
      have hdens : ∀ u, (X₀ : ℝ) ≤ u → u ≤ v →
          absorbedDensity (θ / 2) A (fun n => solveU (θ / 2) n) u ≤
            Real.log u ^ (-4 : ℤ) := by
        intro u hu huv
        have hHBSu : P.HBS X0m (2 * absorbYAt X₀ (2 * u)) (1 / 1000) (1 / 1000) (hbsEps X₀) := by
          refine hHBS_of _ (fun w hw1 hw2 => IH ⌊w⌋₊ ?_ w rfl hw1)
          have hw0 : 0 ≤ w := by linarith
          have hlt : (⌊w⌋₊ : ℝ) < ⌊v⌋₊ := by
            have h1 : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hw0
            rcases two_absorbYAt_two_le hX0 hX hu with hy | hy
            · have : (X₀ : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast Nat.le_floor hhigh
              linarith
            · linarith
          rw [← hvn]; exact_mod_cast hlt
        have hloc := lemma626_local C hX hθ.1 (by linarith [hθ.2]) rfl hω hX0mlog hX0m2 hfl hcl hu
          hHBSu
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
      have hl := hlag v hhigh
      rw [hT v] at hl
      exact hbs_err_high hX hθ.2 hhigh hl hEA hR hR0
  exact ⟨X0m, 1 / 1000, 1 / 1000, hbsEps X₀, hX0mlog, hX0m2,
    fun z => hHBS_of z (fun v h1 _ => main ⌊v⌋₊ v rfl h1), hcl⟩

end Construction

end
