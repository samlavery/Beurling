module

public import RequestProject.Beurling.Model.MarginComplete

/-!
# Theorem A′ (§8 of the paper): a single discrete `[1, 0]`-system

The construction of Theorem A is indexed by the design `θ ∈ [0, 1/2 - 10⁻⁴]`. The design `θ = 0`
is the construction of §8: the `k`-th oscillation has the per-zero exponent
`θ_k = thK 0 x⁺_k = 9 ℓ_k² / L_k` (`L_k = log x⁺_k`, `ℓ_k = log L_k`) and is switched off at
`(x⁺_k)²` (`Oscillation.oscK`). Every step of the proof of Theorem A that reads the oscillation is
proved for every design (the inputs `Theorem21InputsTarget` quantify over `θ ∈ [0, 1/2 - 10⁻⁴]`),
so the chain that proves Theorem A also proves, at `θ = 0`:

* (i) `N(x) = x + O_ε(x^ε)` for every `ε > 0`: `|N - x| ≤ |N - T| + |T - x - R| + |R|`, where the
  lag bound `D_max`, the absorbed error `2h(x)` and the rigid error (Rankin with any exponent
  `ε > 0`) are `x^{o(1)}`, and `|R(x)| ≤ 2 e^{27 (log log x)²}` (`abs_osc_zero_le`: one oscillation
  at a time, `θ_k log x ≤ 27 ℓ_k²` on its window);
* (ii) zeros `ρ_k` with `|(1 - Re ρ_k) log x_k - log log x_k| ≤ C` and
  `|log Im ρ_k - (log x_k - 9 (log log x_k)² - log log x_k)| ≤ C`.

Main results: `BModel.theoremAprime` and `BModel.one_zero_system_exists`.
-/

@[expose] public section

open Set Real Filter Topology MeasureTheory BeurlingSystem Target Oscillation Construction

namespace OneZero

/-! ### `exp(c (log log x)²) = x^{o(1)}` -/

/-- `exp(c (log log x)²)` is `x^{o(1)}` on `[e, ∞)`. -/
theorem subPow_exp_loglog {c X : ℝ} (hc : 0 ≤ c) (hX : Real.exp 1 ≤ X) :
    SubPow (fun x => Real.exp (c * Real.log (Real.log x) ^ 2)) X := by
  intro ε hε
  refine ⟨Real.exp ((16 * c) ^ 2 / (4 * ε)), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) (hX.trans hx)
  have hy1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hX.trans hx
  set y := Real.log x with hy
  have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  -- `log y ≤ 4 y^{1/4}`, so `(log y)² ≤ 16 √y`
  have h1 : Real.log y ≤ y ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : (y ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]; norm_num
  have h2 : Real.log y ^ 2 ≤ 16 * Real.sqrt y := by
    have := pow_le_pow_left₀ hl0 h1 2
    rw [div_pow, hq] at this
    norm_num at this ⊢; linarith
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  -- `16 c √y ≤ ε y + (16c)²/(4ε)`
  have h3 : 16 * c * Real.sqrt y ≤ ε * y + (16 * c) ^ 2 / (4 * ε) := by
    have h4ε : 0 < 4 * ε := by positivity
    have hsq : 0 ≤ (2 * ε * Real.sqrt y - 16 * c) ^ 2 := sq_nonneg _
    have key : 16 * c * Real.sqrt y * (4 * ε) ≤ ε * y * (4 * ε) + (16 * c) ^ 2 := by
      have e2 : (2 * ε * Real.sqrt y - 16 * c) ^ 2 =
          4 * ε ^ 2 * Real.sqrt y ^ 2 - 64 * ε * c * Real.sqrt y + 256 * c ^ 2 := by ring
      rw [e2, hsy] at hsq
      nlinarith
    have e : ε * y + (16 * c) ^ 2 / (4 * ε) = (ε * y * (4 * ε) + (16 * c) ^ 2) / (4 * ε) := by
      field_simp
    rw [e, le_div_iff₀ h4ε]; exact key
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, Real.exp_le_exp, ← hy]
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-! ### The oscillation of the design `θ = 0` -/

/-- The switched-off oscillation vanishes beyond `e (x⁺)²`. -/
lemma oscTermS_eq_zero_of_ge {t α γ xp x : ℝ} (hxp : 1 ≤ xp)
    (hx : Real.exp 1 * xp ^ 2 ≤ x) : oscTermS t α γ xp x = 0 := by
  have hxp0 : 0 < xp := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : 1 ≤ Real.log (x / xp ^ 2) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; exact hx
  have h2 : 1 ≤ Real.log (x / xp) := by
    refine h1.trans (Real.log_le_log (by positivity) ?_)
    apply div_le_div_of_nonneg_left hx0.le hxp0 (by nlinarith)
  rw [oscTermS_eq hxp, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]
  ring

/-- **The size of the oscillation of the design `θ = 0`**: for switch-on points with
`x⁺_0 ≥ 20` and `|α_k| ≤ 2`, `|R(x)| ≤ 2 e^{27 (log log x)²}` for `x ≥ 1`. At most
one oscillation is non-zero at `x` (the windows `(x⁺_k, e (x⁺_k)²)` are disjoint, as
`e (x⁺_k)² ≤ e^{x⁺_k} ≤ x⁺_{k+1}`), and on the `k`-th window `θ_k log x ≤ 27 ℓ_k²`. -/
theorem abs_osc_zero_le {α γ xp : ℕ → ℝ} (hsp : Spacing xp) (h4 : 20 ≤ xp 0) (hα : ∀ k, |α k| ≤ 2) {x : ℝ} (hx : 1 ≤ x) :
    |osc 0 α γ xp x| ≤ 2 * Real.exp (27 * Real.log (Real.log x) ^ 2) := by
  classical
  set E := 2 * Real.exp (27 * Real.log (Real.log x) ^ 2) with hE
  have hE0 : 0 ≤ E := by positivity
  have hmono := hsp.strictMono
  have hxp4 : ∀ k, 20 ≤ xp k := fun k => h4.trans (hmono.monotone (Nat.zero_le k))
  -- the active windows
  set act : ℕ → Prop := fun k => xp k < x ∧ x < Real.exp 1 * xp k ^ 2 with hact
  have hterm : ∀ k, |oscK 0 (α k) (γ k) (xp k) x| ≤ if act k then E else 0 := by
    intro k
    have hxk1 : 1 ≤ xp k := by linarith [hxp4 k]
    rw [oscK_zero]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have hx0 : 0 < x := by linarith
      have hb := abs_oscK_le (θ := 0) (α := α k) (γ := γ k) hxk1 hx0
      rw [oscK_zero] at hb
      refine hb.trans ?_
      have hL : 1 ≤ Real.log (xp k) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9; linarith [hxp4 k]
      set L := Real.log (xp k) with hLdef
      have hLx : L ≤ Real.log x := Real.log_le_log (by linarith) h1.le
      have hx3 : Real.log x ≤ 3 * L := by
        have := Real.log_lt_log hx0 h2
        rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow] at this
        push_cast at this; linarith
      have hℓk : 0 ≤ Real.log L := Real.log_nonneg hL
      have hℓx : Real.log L ≤ Real.log (Real.log x) := Real.log_le_log (by linarith) hLx
      have ht : thK 0 (xp k) * Real.log x ≤ 27 * Real.log (Real.log x) ^ 2 := by
        rw [thK_zero, ← hLdef]
        have h9 : 9 * Real.log L ^ 2 / L * Real.log x ≤ 9 * Real.log L ^ 2 / L * (3 * L) :=
          mul_le_mul_of_nonneg_left hx3 (by positivity)
        have e : 9 * Real.log L ^ 2 / L * (3 * L) = 27 * Real.log L ^ 2 := by
          field_simp; ring
        have hsq : Real.log L ^ 2 ≤ Real.log (Real.log x) ^ 2 := pow_le_pow_left₀ hℓk hℓx 2
        linarith
      have hpow : x ^ thK 0 (xp k) ≤ Real.exp (27 * Real.log (Real.log x) ^ 2) := by
        rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp]; linarith
      have := hα k
      have h0 := Real.rpow_nonneg hx0.le (thK 0 (xp k))
      nlinarith
    · simp only [hact, not_and_or, not_lt] at h
      rcases h with h | h
      · rw [oscTermS_eq_zero_of_le (by linarith) h, abs_zero]
      · rw [oscTermS_eq_zero_of_ge hxk1 h, abs_zero]
  -- at most one active window
  have hone : ∀ i j, act i → act j → i = j := by
    intro i j hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : Real.exp 1 * xp i ^ 2 ≤ xp j := by
        have h2 : Real.exp 1 * xp i ^ 2 ≤ Real.exp (xp i) := by
          have h4' := hxp4 i
          have := Real.exp_one_lt_d9
          have h3 : xp i ^ 4 / 24 ≤ Real.exp (xp i) := by
            have := Real.pow_div_factorial_le_exp (xp i) (by linarith) 4
            norm_num [Nat.factorial] at this; linarith
          have hx2 : 400 ≤ xp i ^ 2 := by nlinarith
          have h5 : Real.exp 1 * xp i ^ 2 ≤ xp i ^ 4 / 24 := by
            nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg (xp i))]
          linarith
        exact h2.trans ((hsp.exp_le i).trans (hmono.monotone (by omega)))
      linarith [hi.2, hj.1]
    · have h1 : Real.exp 1 * xp j ^ 2 ≤ xp i := by
        have h2 : Real.exp 1 * xp j ^ 2 ≤ Real.exp (xp j) := by
          have h4' := hxp4 j
          have := Real.exp_one_lt_d9
          have h3 : xp j ^ 4 / 24 ≤ Real.exp (xp j) := by
            have := Real.pow_div_factorial_le_exp (xp j) (by linarith) 4
            norm_num [Nat.factorial] at this; linarith
          have hx2 : 400 ≤ xp j ^ 2 := by nlinarith
          have h5 : Real.exp 1 * xp j ^ 2 ≤ xp j ^ 4 / 24 := by
            nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg (xp j))]
          linarith
        exact h2.trans ((hsp.exp_le j).trans (hmono.monotone (by omega)))
      linarith [hj.2, hi.1]
  rw [osc_eq_sum hsp hx]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range (logStar x)).filter act).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj =>
      hone i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hc' : (((Finset.range (logStar x)).filter act).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

end OneZero

namespace BModel

open OneZero

/-- **The conclusions of Theorem A′** for one realised system `P`:

(i) `N_P(x) = x + O_ε(x^ε)` for every `ε > 0`;

(ii) `ζ_P` continues analytically to a punctured half-plane `Re s > a` (`a < 1`) and has zeros
`ρ_k` there, along `x_k → ∞`, with `Re ρ_k = 1 - (log log x_k + O(1)) / log x_k` and the height
relation `log Im ρ_k = log x_k - 9 (log log x_k)² - log log x_k + O(1)` (the per-zero exponent
`θ_k = 9 (log log x_k)²/log x_k`, so `(1 - θ_k) log x_k = log x_k - 9 (log log x_k)²`). -/
def TheoremAprimeConclusion (P : BeurlingSystem) : Prop :=
  (∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ ε) ∧
  (∃ a < (1 : ℝ), ∃ F : ℂ → ℂ, P.IsZetaContinuation a F ∧
    ∃ (ρ : ℕ → ℂ) (xk : ℕ → ℝ) (C : ℝ), Tendsto xk atTop atTop ∧
      (∀ k, ρ k ∈ puncturedHalfPlane a ∧ F (ρ k) = 0) ∧
      (∀ k, |(1 - (ρ k).re) * Real.log (xk k) - Real.log (Real.log (xk k))| ≤ C) ∧
      ∀ k, |Real.log (ρ k).im - (Real.log (xk k) - 9 * Real.log (Real.log (xk k)) ^ 2 -
        Real.log (Real.log (xk k)))| ≤ C)

/-- **The inputs of Theorem 4.10 with the concrete target, for every design**, from eq. (84):
the chain of `theoremA_full` stops at `Theorem21InputsTarget`, which quantifies over
`θ ∈ [0, 1/2 - 10⁻⁴]`. -/
theorem theorem21InputsTarget_hux (h84 : BaseRange.Huxley84) : Theorem21InputsTarget := by
  have hHB := BaseRange.shortIntervalPNT_of_huxley h84
  have hX := Queue6.theorem21InputsX_of_Y (Queue6.theorem21InputsY_of_Z
    (theorem21InputsZ_hux h84 (theorem21InputsH_proved h84)))
  exact theorem21InputsTarget_of_paper (theorem21InputsPaper_of_absorbed
    (theorem21InputsAbsorbed_of_base (theorem21InputsBase_of_mertens
    (theorem21InputsMertens_of_ZB (theorem21InputsZB_of_ZB48 (theorem21InputsZB48_of_split
    (theorem21InputsSplit_of_slotModel (theorem21InputsSlotModel_of_initSize
    (theorem21InputsInitSize_of_abs (Decomp.theorem21InputsAbs_of_dec
    (theorem21InputsDec_of_fixP (theorem21InputsFixP_of_K (theorem21InputsK_of_L
    (theorem21InputsL_of_M (theorem21InputsM_of_N (theorem21InputsN_of_O (theorem21InputsO_of_P
    (theorem21InputsP_of_Q hHB tiesNull (theorem21InputsQ_of_S hHB tiesNull
    (Queue6.theorem21InputsS_of_X hHB hX))))))))))))))))))))

/-- **Theorem A′(i) from the target data of the design `θ = 0`**: the lag bound, the absorbed
error `2h`, the rigid error (Rankin, with any exponent `ε > 0`) and the oscillation
(`abs_osc_zero_le`) are all `x^{o(1)}`. -/
theorem N_bound_zero {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {P : BeurlingSystem}
    (h : PartIInputsTarget 0 X₀ P) :
    ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ ε := by
  obtain ⟨κ, cntA, rhoA, α, γ, xp, Dm, hκ, hκ1, hsp, hα, hxp, hA, hD, hDm⟩ := h
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hXe : Real.exp 1 ≤ (X₀ : ℝ) := by
    have : (1 : ℝ) ≤ Real.log X₀ := by linarith
    rwa [Real.le_log_iff_exp_le (by linarith)] at this
  have hX20 : (20 : ℝ) ≤ X₀ := by
    have := Real.add_one_le_exp (Real.log X₀)
    rw [Real.exp_log (by linarith)] at this; linarith
  have hR0 : osc 0 α γ xp X₀ = 0 := osc_eq_zero_of_le hsp (by linarith) hxp
  -- the bound on `[X₀, ∞)`
  have hsplit : ∀ x ≥ (X₀ : ℝ), |P.N x - x| ≤ Dm x + |rigidErr X₀ κ x| +
      2 * Absorbed.winH X₀ x + 2 * Real.exp (27 * Real.log (Real.log x) ^ 2) := by
    intro x hx
    have e := target_sub_eq X₀ κ cntA rhoA (osc 0 α γ xp) hx
    rw [hR0, sub_zero] at e
    have h1 := hD x hx
    have h2 := hA x hx
    have h3 := abs_osc_zero_le (γ := γ) hsp (hX20.trans hxp) hα (x := x) (by linarith)
    set T := target X₀ κ cntA rhoA (osc 0 α γ xp) x
    have : P.N x - x = (P.N x - T) + (rigidErr X₀ κ x + (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u)) +
        osc 0 α γ xp x := by rw [← e]; ring
    rw [this]
    calc _ ≤ |P.N x - T| + |rigidErr X₀ κ x + (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u)| +
          |osc 0 α γ xp x| := abs_add_three _ _ _
      _ ≤ _ := by
          have := abs_add_le (rigidErr X₀ κ x) (cntA x - ∫ u in (X₀ : ℝ)..x, rhoA u)
          linarith
  -- each term is `x^{o(1)}`
  have hrig : SubPow (fun x => |rigidErr X₀ κ x|) X₀ := fun ε hε =>
    ⟨2 ^ ε * Rankin.rankinConst X₀ ε, fun x hx => by
      have := abs_rigidErr_le_rankin X₀ hκ hκ1 hX1n hx hε
      rw [Real.mul_rpow (by norm_num) (by linarith)] at this
      linarith⟩
  have hsub : SubPow (fun x => Dm x + |rigidErr X₀ κ x| + 2 * Absorbed.winH X₀ x +
      2 * Real.exp (27 * Real.log (Real.log x) ^ 2)) X₀ :=
    ((hDm.add hrig).add ((subPow_winH hX _ hX1.le).const_mul 2 (by norm_num))).add
      ((subPow_exp_loglog (by norm_num) hXe).const_mul 2 (by norm_num))
  intro ε hε
  obtain ⟨C, hC⟩ := hsub ε hε
  refine ⟨|C| + (P.N X₀ + X₀), fun x hx => ?_⟩
  have hxε : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hB : 0 ≤ P.N X₀ + X₀ := add_nonneg (Nat.cast_nonneg _) hX0
  rcases le_or_gt (X₀ : ℝ) x with hxX | hxX
  · have := (hsplit x hxX).trans (hC x hxX)
    have h1 : C * x ^ ε ≤ |C| * x ^ ε :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    nlinarith
  · have hN0 : 0 ≤ P.N x := Nat.cast_nonneg _
    have hNX : P.N x ≤ P.N X₀ := BeurlingSystem.N_mono P hxX.le
    have h1 : |P.N x - x| ≤ P.N X₀ + X₀ := by
      rw [abs_le]; constructor <;> linarith
    have h2 : 0 ≤ |C| * x ^ ε := by positivity
    nlinarith

/-- `(1 - θ_k) log x = log x - 9 (log log x)²` for the per-zero exponent of the design `0`. -/
lemma one_sub_thK_zero_mul (x : ℝ) :
    (1 - thK 0 x) * Real.log x = Real.log x - 9 * Real.log (Real.log x) ^ 2 := by
  rw [thK_zero]
  by_cases hL : Real.log x = 0
  · rw [hL]; simp
  · field_simp

/-- **Theorem A′** (§8 of the paper), from eq. (84): there is `X_Hux` such that for every even
`X₀ ≥ max(e^{10⁸}, X_Hux)` the random system of the design `θ = 0` (per-zero exponents
`θ_k = 9 (log log x⁺_k)²/log x⁺_k`, oscillations switched off at `(x⁺_k)²`) satisfies, on an event
of probability `≥ 1 - 1.5/log X₀`: (i) `N(x) = x + O_ε(x^ε)` for every `ε > 0`, and (ii) zeros
`ρ_k` with `|(1 - Re ρ_k) log x_k - log log x_k| ≤ C` and
`|log Im ρ_k - (log x_k - 9 (log log x_k)² - log log x_k)| ≤ C` (`TheoremAprimeConclusion`). -/
theorem theoremAprime (h84 : BaseRange.Huxley84) :
    ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ → Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
        IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
        ∀ ω ∈ G, TheoremAprimeConclusion (P ω) := by
  obtain ⟨XHux, hT⟩ := theorem21InputsTarget_hux h84
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hT 0 ⟨le_rfl, by norm_num⟩ X₀ hev h1 h2
  have hX : 10 ^ 8 ≤ Real.log X₀ := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => ?_⟩
  obtain ⟨hI, a, ha0, ha1, h410⟩ := hP ω hω
  have hN := N_bound_zero hX hI
  refine ⟨hN, a, ha1, (P ω).zetaCont 1, ?_⟩
  obtain ⟨C, hC⟩ := hN a ha0
  have hcont := (P ω).zetaCont_isZetaContinuation (A := 1) ha1
    (fun x hx => by rw [one_mul]; exact hC x hx)
  refine ⟨hcont, ?_⟩
  obtain ⟨ρ, xk, C', hx, hz, hre, him⟩ := theorem_4_10 hcont h410
  refine ⟨ρ, xk, C', hx, hz, hre, fun k => ?_⟩
  have := him k
  rw [one_sub_thK_zero_mul] at this
  exact this

/-- **A discrete `[1, 0]`-system exists** (Corollary `onezero` of the paper), from eq. (84): a
Beurling system with `N(x) = x + O_ε(x^ε)` for every `ε > 0` whose `ζ` has no zero-free
half-plane `Re s > 1 - ε` (for any continuation). -/
theorem one_zero_system_exists (h84 : BaseRange.Huxley84) :
    ∃ P : BeurlingSystem, (∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), |P.N x - x| ≤ C * x ^ ε) ∧
      ¬ P.HasZeroFreeHalfPlane := by
  obtain ⟨XHux, hX⟩ := theoremAprime h84
  set n : ℕ := ⌈max (Real.exp (10 ^ 8)) XHux⌉₊
  have hn : max (Real.exp (10 ^ 8)) XHux ≤ ((2 * n : ℕ) : ℝ) := by
    have := Nat.le_ceil (max (Real.exp (10 ^ 8)) XHux)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast; linarith
  have h1 : Real.exp (10 ^ 8) ≤ ((2 * n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  obtain ⟨Ω, _, μ, P, G, -, hG, hP⟩ :=
    hX (2 * n) (even_two_mul n) h1 ((le_max_right _ _).trans hn)
  have hlog : (10 : ℝ) ^ 8 ≤ Real.log ((2 * n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hpos : 0 < 1 - 1.5 / Real.log ((2 * n : ℕ) : ℝ) := by
    have hl : 0 < Real.log ((2 * n : ℕ) : ℝ) := by linarith [show (0:ℝ) < 10 ^ 8 by norm_num]
    rw [sub_pos, div_lt_one hl]
    linarith [show (1.5 : ℝ) < 10 ^ 8 by norm_num]
  have hμ : μ G ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hG)
  obtain ⟨ω, hω⟩ := MeasureTheory.nonempty_of_measure_ne_zero hμ
  obtain ⟨hN, a, ha, F, hF, ρ, xk, C, hx, hz, hb, -⟩ := hP ω hω
  refine ⟨P ω, hN, ?_⟩
  rintro ⟨ε, hε, F', hF', hnz⟩
  have hre := tendsto_one_of_log_asymptotic (fun k => (ρ k).re) xk C hx hb
  have hb' : max (1 - ε) a < 1 := max_lt (by linarith) ha
  obtain ⟨k, hk⟩ := (hre.eventually (lt_mem_nhds hb')).exists
  have hmem : ρ k ∈ puncturedHalfPlane (max (1 - ε) a) := ⟨hk, (hz k).1.2⟩
  have heq := hF'.eqOn hF hmem
  exact hnz (ρ k) (puncturedHalfPlane_mono (le_max_left _ _) hmem) (heq.trans (hz k).2)

end BModel

end
