module

public import RequestProject.Beurling.Construction.Main

/-!
# The recursive choice of the heights `γ_k` and the parameters of Section 2.2

**The heights.** In Lemma 4.8 the height `γ_k` is chosen by an explicit rule from `D̂_{<a_k}`, the
early transform of the lag `D = N - T` on `(1, a_k]`, and `α_k` is then determined by `γ_k`. The
target `T` itself contains the oscillation `R = ∑_j R_j`, which depends on all `γ_j, α_j`. The
formalization so far assumed a *fixed-point condition* (`γ_k = designGamma … (D̂_{<a_·}) …`). Here
it is **proved** that the rule defines the heights by recursion: on `(1, a_k]` (with
`a_k ≤ x⁺_k`) only the terms `R_j`, `j < k`, are switched on, so `D̂_{<a_k}` reads only
`γ_j, α_j` for `j < k` (`earlyOf_congr`). `designedGamma` is the resulting sequence, and
`designedGamma_fixed` is the fixed-point condition.

**The parameters of Section 2.2.** `κ = X₀^{-5/12 + 2ε_κ}` with `ε_κ = 0.01`, `κ₀ = X₀⁻¹`, and the
switch-on points `x⁺_0 = exp(S²)`, `x⁺_{k+1} = exp(x⁺_k)` with the seed `S = max(X₀, 1000/θ)`
(`swS`; `S = X₀` unless `θ < 1000/X₀`). Their required properties are proved (`kappaParam_*`,
`switchOn_*`), including the switch-on condition `θ log y ≥ 16 (log log y)² + 2Λ + 10` for
`log y ≥ log x⁺_0 - 1` (`switchOn_cond`; the paper asks `θ log x₁ ≥ 9 (log log x₁)²`).
-/

@[expose] public section

open MeasureTheory Set Oscillation Decomp

namespace Construction

/-! ## Locality of the target -/

/-- On `(0, x⁺_k]` the oscillation only reads `α_j, γ_j` for `j < k`. -/
lemma osc_congr_lt {θ : ℝ} {α γ α' γ' xp : ℕ → ℝ} (hsp : Spacing xp) {k : ℕ}
    (hα : ∀ j < k, α j = α' j) (hγ : ∀ j < k, γ j = γ' j) {x : ℝ} (hx : 0 < x)
    (hxk : x ≤ xp k) : osc θ α γ xp x = osc θ α' γ' xp x := by
  unfold osc
  congr 1
  funext j
  rcases lt_or_ge j k with h | h
  · rw [hα j h, hγ j h]
  · have : x ≤ xp j := hxk.trans (hsp.strictMono.monotone h)
    rw [oscTerm_eq_zero_of_le hx this, oscTerm_eq_zero_of_le hx this]

/-- On `(0, x⁺_k]` the lag only reads `α_j, γ_j` for `j < k`. -/
lemma lagOf_congr_lt (P : BeurlingSystem) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}
    {α γ α' γ' xp : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀) (hxp : (X₀ : ℝ) ≤ xp 0) {k : ℕ}
    (hα : ∀ j < k, α j = α' j) (hγ : ∀ j < k, γ j = γ' j) {x : ℝ} (hx : 0 < x)
    (hxk : x ≤ xp k) : lagOf P θ X₀ κ A u α γ xp x = lagOf P θ X₀ κ A u α' γ' xp x := by
  have hX0 : (0 : ℝ) < X₀ := by exact_mod_cast hX1
  have hXk : (X₀ : ℝ) ≤ xp k := hxp.trans (hsp.strictMono.monotone (Nat.zero_le k))
  unfold lagOf targetOf Target.target
  rw [osc_congr_lt hsp hα hγ hx hxk, osc_congr_lt hsp hα hγ hX0 hXk]

/-- `D̂_{<a}` only reads `D` on `(0, a]`. -/
lemma earlyNoise_congr {D D' : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : ∀ x, 0 < x → x ≤ a → D x = D' x) : earlyNoise D a = earlyNoise D' a := by
  funext s
  unfold earlyNoise
  rw [h a ha le_rfl]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  rw [h x (by linarith [hx.1]) hx.2]

/-- **Locality of `D̂_{<a_k}`**: if `0 < a_k ≤ x⁺_k`, then `D̂_{<a_k}` only reads `α_j, γ_j` for
`j < k`. -/
lemma earlyOf_congr (P : BeurlingSystem) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}
    {α γ α' γ' xp a : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀) (hxp : (X₀ : ℝ) ≤ xp 0) {k : ℕ}
    (ha0 : 0 < a k) (hak : a k ≤ xp k)
    (hα : ∀ j < k, α j = α' j) (hγ : ∀ j < k, γ j = γ' j) :
    earlyOf P θ X₀ κ A u α γ xp a k = earlyOf P θ X₀ κ A u α' γ' xp a k := by
  unfold earlyOf
  exact earlyNoise_congr ha0 (fun x hx hxa =>
    lagOf_congr_lt P hsp hX1 hxp hα hγ hx (hxa.trans hak))

/-! ## The recursive choice of the heights -/

/-- The amplitudes `α_j = κ₀ (x⁺_j)^{1-θ} / (γ_j log x⁺_j)` for the heights `g`. -/
noncomputable def amplitudes (θ κ₀ : ℝ) (xp g : ℕ → ℝ) : ℕ → ℝ :=
  fun j => DesignedZero.amplitudeOf θ κ₀ (g j) (xp j)

/-- One step of the rule of Lemma 4.8: the height chosen at `k` when the heights so far are `g`
(and the amplitudes are determined by them). -/
noncomputable def stepGamma (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  DesignedZero.designGamma X₀ κ θ κ₀ (earlyOf P θ X₀ κ A u (amplitudes θ κ₀ xp g) g xp a) xp k

/-- **The designed heights** `γ_k`, by recursion on `k`: `γ_k` is the height chosen by the rule of
Lemma 4.8 from `D̂_{<a_k}` computed with `γ_0, …, γ_{k-1}`. -/
noncomputable def designedGamma (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) : ℕ → ℝ :=
  fun k => Nat.strongRecOn (motive := fun _ => ℝ) k
    (fun k IH => stepGamma P θ X₀ κ A u κ₀ xp a (fun j => if h : j < k then IH j h else 0) k)

/-- The designed amplitudes `α_k`. -/
noncomputable def designedAlpha (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) : ℕ → ℝ :=
  amplitudes θ κ₀ xp (designedGamma P θ X₀ κ A u κ₀ xp a)

/-- **The fixed-point condition holds for the designed heights**: `γ_k` is the height chosen by
the rule of Lemma 4.8 from `D̂_{<a_k}` of the lag of the target built with all the designed
`γ_j, α_j`. -/
theorem designedGamma_fixed (P : BeurlingSystem) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ}
    {u : ℝ → ℝ} {κ₀ : ℝ} {xp a : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀)
    (hxp : (X₀ : ℝ) ≤ xp 0) (ha : ∀ k, 0 < a k ∧ a k ≤ xp k) (k : ℕ) :
    designedGamma P θ X₀ κ A u κ₀ xp a k =
      DesignedZero.designGamma X₀ κ θ κ₀
        (earlyOf P θ X₀ κ A u (designedAlpha P θ X₀ κ A u κ₀ xp a)
          (designedGamma P θ X₀ κ A u κ₀ xp a) xp a) xp k := by
  set g := designedGamma P θ X₀ κ A u κ₀ xp a with hg
  have hrec : g k = stepGamma P θ X₀ κ A u κ₀ xp a
      (fun j => if h : j < k then g j else 0) k := by
    rw [hg]
    unfold designedGamma
    rw [Nat.strongRecOn_eq]
  rw [hrec]
  unfold stepGamma DesignedZero.designGamma designedAlpha
  have hagree : ∀ j < k, (fun j => if h : j < k then g j else 0) j = g j := by
    intro j hj; simp [hj]
  rw [earlyOf_congr P hsp hX1 hxp (ha k).1 (ha k).2 (α' := amplitudes θ κ₀ xp g) (γ' := g)
    (fun j hj => by simp only [amplitudes, dif_pos hj]) hagree]

/-- The designed heights lie in `[Γ_k, 2Γ_k]`. -/
lemma designedGamma_mem (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) (hΓ : ∀ k, 0 ≤ DesignedZero.heightScale θ κ₀ (xp k))
    (k : ℕ) :
    designedGamma P θ X₀ κ A u κ₀ xp a k ∈
      Icc (DesignedZero.heightScale θ κ₀ (xp k)) (2 * DesignedZero.heightScale θ κ₀ (xp k)) := by
  have hrec : designedGamma P θ X₀ κ A u κ₀ xp a k = stepGamma P θ X₀ κ A u κ₀ xp a
      (fun j => if h : j < k then designedGamma P θ X₀ κ A u κ₀ xp a j else 0) k := by
    unfold designedGamma
    rw [Nat.strongRecOn_eq]
  rw [hrec]
  unfold stepGamma DesignedZero.designGamma
  exact DesignedZero.chooseHeight_mem _ _ _ (hΓ k)

/-- The designed amplitudes satisfy `1 ≤ α_k ≤ 2` (as `α_k γ_k = 2 Γ_k` and `γ_k ∈ [Γ_k, 2Γ_k]`),
when `Γ_k > 0`. -/
lemma designedAlpha_mem (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) (hΓ : ∀ k, 0 < DesignedZero.heightScale θ κ₀ (xp k))
    (k : ℕ) : designedAlpha P θ X₀ κ A u κ₀ xp a k ∈ Icc (1 : ℝ) 2 := by
  have hm := designedGamma_mem P θ X₀ κ A u κ₀ xp a (fun k => (hΓ k).le) k
  set γ := designedGamma P θ X₀ κ A u κ₀ xp a k
  set Γ := DesignedZero.heightScale θ κ₀ (xp k) with hΓdef
  have hΓk := hΓ k
  have hγ : 0 < γ := lt_of_lt_of_le hΓk hm.1
  have hL : Real.log (xp k) ≠ 0 := by
    intro h0
    have : Γ = 0 := by rw [hΓdef]; unfold DesignedZero.heightScale; rw [h0]; simp
    linarith
  have e : designedAlpha P θ X₀ κ A u κ₀ xp a k = 2 * Γ / γ := by
    show κ₀ * xp k ^ (1 - θ) / Real.log (xp k) / γ = 2 * Γ / γ
    rw [hΓdef]; unfold DesignedZero.heightScale
    congr 1
    field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ hγ]; linarith [hm.2]
  · rw [div_le_iff₀ hγ]; nlinarith [hm.1]

/-! ## The parameters of Section 2.2 -/

/-- `κ = X₀^{-5/12 + 2 ε_κ}` with `ε_κ = 0.01`. -/
noncomputable def kappaParam (X₀ : ℝ) : ℝ := X₀ ^ (-5 / 12 + 2 * (0.01 : ℝ))

/-- `κ₀ = X₀⁻¹` (eq. (ampl): the constant relative amplitude `κ'_k = κ₀ ∈ [X₀⁻¹, Λ⁻⁵]`). -/
noncomputable def kappa0Param (X₀ : ℝ) : ℝ := 1 / X₀

/-- The switch-on points `x⁺_0 = exp(X₀²)`, `x⁺_{k+1} = exp(x⁺_k)`. -/
noncomputable def switchOn (X₀ : ℝ) : ℕ → ℝ
  | 0 => Real.exp (X₀ ^ 2)
  | k + 1 => Real.exp (switchOn X₀ k)

/-- **The switch-on seed** `S = max(X₀, 1000/θ)`: the switch-on points are `switchOn S`, with
`x⁺_0 = exp(S²)`. It depends on `θ` only for `θ < 1000/X₀`; `X₀` does not depend on `θ`. -/
noncomputable def swS (θ X₀ : ℝ) : ℝ := max X₀ (1000 / θ)

lemma le_swS (θ X₀ : ℝ) : X₀ ≤ swS θ X₀ := le_max_left _ _

lemma log_le_log_swS {θ X₀ : ℝ} (hX0 : 0 < X₀) : Real.log X₀ ≤ Real.log (swS θ X₀) :=
  Real.log_le_log hX0 (le_swS θ X₀)

lemma logX_swS {θ X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    10 ^ 8 ≤ Real.log (swS θ X₀) := by
  have hX1 : 0 < X₀ := by
    rcases hX0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hX; norm_num at hX
  exact hX.trans (log_le_log_swS hX1)

lemma kappaParam_pos {X₀ : ℝ} (hX : 0 < X₀) : 0 < kappaParam X₀ := Real.rpow_pos_of_pos hX _

lemma kappaParam_le_one {X₀ : ℝ} (hX : 1 ≤ X₀) : kappaParam X₀ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)

lemma kappaParam_ge {X₀ : ℝ} (hX : 1 ≤ X₀) : Real.exp (-Real.log X₀) ≤ kappaParam X₀ := by
  have hX0 : 0 < X₀ := by linarith
  rw [Real.exp_neg, Real.exp_log hX0, kappaParam, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

lemma kappa0Param_ge {X₀ : ℝ} (hX : 4 ≤ X₀) : Real.exp (-Real.log X₀) ≤ kappa0Param X₀ := by
  rw [Real.exp_neg, Real.exp_log (by linarith), kappa0Param, inv_eq_one_div]

lemma kappa0Param_pos {X₀ : ℝ} (hX : 0 < X₀) : 0 < kappa0Param X₀ := one_div_pos.mpr hX

lemma kappa0Param_le {X₀ : ℝ} (hX : 4 ≤ X₀) : kappa0Param X₀ ≤ 1 / 4 :=
  one_div_le_one_div_of_le (by norm_num) hX

lemma switchOn_spacing (X₀ : ℝ) : Spacing (switchOn X₀) where
  one_le := Real.one_le_exp (sq_nonneg _)
  exp_le _ := le_rfl

lemma switchOn_zero_ge (X₀ : ℝ) : X₀ ≤ switchOn X₀ 0 := by
  show X₀ ≤ Real.exp (X₀ ^ 2)
  have := Real.add_one_le_exp (X₀ ^ 2)
  nlinarith [sq_nonneg (X₀ - 1 / 2)]

lemma switchOn_zero_ge_swS (θ X₀ : ℝ) : X₀ ≤ switchOn (swS θ X₀) 0 :=
  (le_swS θ X₀).trans (switchOn_zero_ge _)

lemma log_switchOn_zero (X₀ : ℝ) : Real.log (switchOn X₀ 0) = X₀ ^ 2 := by
  show Real.log (Real.exp (X₀ ^ 2)) = X₀ ^ 2
  exact Real.log_exp _

lemma switchOn_pos (X₀ : ℝ) (k : ℕ) : 0 < switchOn X₀ k := by
  cases k <;> exact Real.exp_pos _

lemma switchOn_gt_one (X₀ : ℝ) (k : ℕ) : 1 < switchOn X₀ (k + 1) := by
  show 1 < Real.exp (switchOn X₀ k)
  exact Real.one_lt_exp_iff.mpr (switchOn_pos X₀ k)

/-- **The switch-on condition, strong form**: with the seed `S = max(X₀, 1000/θ)`, every `y`
with `log y ≥ log x⁺_0 - 3 = S² - 3` has `16 ℓ² + 4 ℓ + 2 log X₀ + 10 ≤ θ log y`,
`ℓ = log log y`. -/
theorem switchOn_cond' {θ X₀ : ℝ} (hθ : 0 < θ) (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    ∀ y : ℝ, Real.log (switchOn (swS θ X₀) 0) - 3 ≤ Real.log y →
      16 * Real.log (Real.log y) ^ 2 + 4 * Real.log (Real.log y) + 2 * Real.log X₀ + 10 ≤
        θ * Real.log y := by
  intro y hy
  set S := swS θ X₀ with hS
  rw [log_switchOn_zero] at hy
  have hX1 : 1 < X₀ := by
    by_contra hc; push_neg at hc; linarith [Real.log_nonpos hX0 hc]
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX8 : (10 : ℝ) ^ 8 ≤ X₀ := by linarith
  have hSX : X₀ ≤ S := le_swS θ X₀
  have hθS : 1000 ≤ θ * S := by
    have : 1000 / θ ≤ S := le_max_right _ _
    rw [div_le_iff₀ hθ] at this; linarith
  set L := Real.log y with hL
  have hL0 : 0 < L := by nlinarith
  set q := L ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hL0 _
  have hq4 : q ^ 4 = L := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlog := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 4 by norm_num)
  rw [← hq] at hlog
  -- `q² ≥ S/2`
  have hq2 : S / 2 ≤ q ^ 2 := by
    have h1 : (S / 2) ^ 2 ≤ (q ^ 2) ^ 2 := by
      rw [← pow_mul]; norm_num; rw [hq4]; nlinarith
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have hq1 : 1 ≤ q := by nlinarith
  -- `(log L)² ≤ 16 q²`, `log L ≤ 4 q ≤ 4 q²`
  have h0 : 0 ≤ Real.log L := Real.log_nonneg (by nlinarith)
  have hsq : Real.log L ^ 2 ≤ 16 * q ^ 2 := by nlinarith
  have hlin : Real.log L ≤ 4 * q ^ 2 := by nlinarith
  have hθL : θ * S / 2 * q ^ 2 ≤ θ * L := by
    rw [← hq4]
    have := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ θ * q ^ 2 by positivity)
    nlinarith
  nlinarith

/-- **The switch-on condition** (Theorem A: `θ log x₁ ≥ 9 (log log x₁)²`, here in the stronger
form used by the late noise and step 6 of Lemma 4.6): with the seed `S = max(X₀, 1000/θ)`, every
`y` with `log y ≥ log x⁺_0 - 1 = S² - 1` has `16 (log log y)² + 2 log X₀ + 10 ≤ θ log y`. -/
theorem switchOn_cond {θ X₀ : ℝ} (hθ : 0 < θ) (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    ∀ y : ℝ, Real.log (switchOn (swS θ X₀) 0) - 1 ≤ Real.log y →
      16 * Real.log (Real.log y) ^ 2 + 2 * Real.log X₀ + 10 ≤ θ * Real.log y := by
  intro y hy
  have h := switchOn_cond' hθ hX0 hX y (by linarith)
  -- `log log y ≥ 0`
  have hS := le_swS θ X₀
  have hX1 : 1 < X₀ := by
    by_contra hc; push_neg at hc; linarith [Real.log_nonpos hX0 hc]
  rw [log_switchOn_zero] at hy
  have hlogX : Real.log X₀ ≤ X₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hL : 1 ≤ Real.log y := by nlinarith
  have := Real.log_nonneg hL
  linarith

end Construction

export Construction (swS le_swS logX_swS switchOn_zero_ge_swS switchOn_cond switchOn_cond')

end
