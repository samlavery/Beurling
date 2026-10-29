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

**The parameters of Section 2.2.** `κ = X₀^{-5/12 + 2ε_κ}` with `ε_κ = 0.01`, `κ₀ = 1/4`, and the
switch-on points `x⁺_0 = exp(X₀²)`, `x⁺_{k+1} = exp(x⁺_k)` (the least admissible choice). Their
required properties are proved (`kappaParam_*`, `switchOn_*`).
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

/-- The amplitudes `α_j = κ₀ (x⁺_j)^{1-θ} / ((log x⁺_j)³ γ_j)` for the heights `g`. -/
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
  fun k => Nat.strongRecOn' (P := fun _ => ℝ) k
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
    rw [Nat.strongRecOn'_beta]
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
    rw [Nat.strongRecOn'_beta]
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
  have hL : Real.log (xp k) ^ 3 ≠ 0 := by
    intro h0
    have : Γ = 0 := by rw [hΓdef]; unfold DesignedZero.heightScale; rw [h0]; simp
    linarith
  have e : designedAlpha P θ X₀ κ A u κ₀ xp a k = 2 * Γ / γ := by
    show κ₀ * xp k ^ (1 - θ) / Real.log (xp k) ^ 3 / γ = 2 * Γ / γ
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

/-- `κ₀ = 1/4`. -/
noncomputable def kappa0Param : ℝ := 1 / 4

/-- The switch-on points `x⁺_0 = exp(X₀²)`, `x⁺_{k+1} = exp(x⁺_k)`. -/
noncomputable def switchOn (X₀ : ℝ) : ℕ → ℝ
  | 0 => Real.exp (X₀ ^ 2)
  | k + 1 => Real.exp (switchOn X₀ k)

lemma kappaParam_pos {X₀ : ℝ} (hX : 0 < X₀) : 0 < kappaParam X₀ := Real.rpow_pos_of_pos hX _

lemma kappaParam_le_one {X₀ : ℝ} (hX : 1 ≤ X₀) : kappaParam X₀ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)

lemma kappaParam_ge {X₀ : ℝ} (hX : 1 ≤ X₀) : Real.exp (-Real.log X₀) ≤ kappaParam X₀ := by
  have hX0 : 0 < X₀ := by linarith
  rw [Real.exp_neg, Real.exp_log hX0, kappaParam, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

lemma kappa0Param_ge {X₀ : ℝ} (hX : 4 ≤ X₀) : Real.exp (-Real.log X₀) ≤ kappa0Param := by
  rw [Real.exp_neg, Real.exp_log (by linarith), kappa0Param]
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hX

lemma switchOn_spacing (X₀ : ℝ) : Spacing (switchOn X₀) where
  one_le := Real.one_le_exp (sq_nonneg _)
  exp_le _ := le_rfl

lemma switchOn_zero_ge (X₀ : ℝ) : X₀ ≤ switchOn X₀ 0 := by
  show X₀ ≤ Real.exp (X₀ ^ 2)
  have := Real.add_one_le_exp (X₀ ^ 2)
  nlinarith [sq_nonneg (X₀ - 1 / 2)]

lemma log_switchOn_zero (X₀ : ℝ) : Real.log (switchOn X₀ 0) = X₀ ^ 2 := by
  show Real.log (Real.exp (X₀ ^ 2)) = X₀ ^ 2
  exact Real.log_exp _

lemma switchOn_pos (X₀ : ℝ) (k : ℕ) : 0 < switchOn X₀ k := by
  cases k <;> exact Real.exp_pos _

lemma switchOn_gt_one (X₀ : ℝ) (k : ℕ) : 1 < switchOn X₀ (k + 1) := by
  show 1 < Real.exp (switchOn X₀ k)
  exact Real.one_lt_exp_iff.mpr (switchOn_pos X₀ k)

end Construction

end
