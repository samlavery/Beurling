module

public import RequestProject.Beurling.BaseRange.Huxley

/-!
# The fresh-prime window density `MA[ℙ]` and Lemma 7.3(a)

With `κ = X₀^{-5/12 + 2ε_κ}` (`Construction.kappaParam`, `ε_κ = 0.01`), §7.2 puts

  `MA[ℙ](q) = MA_{κq}[rational primes ≥ X₀](q) = #{p ≥ X₀ prime : q ≤ p ≤ (1+κ)q}/(κq)`.

* `MAP` : `MA[ℙ]`; `MAP_eq` : for `q ≥ X₀` it is `π([q, (1+κ)q])/(κq)`;
* `lemma_7_3_a` : **Lemma 7.3(a)**, for `q ≥ X₀` with `X₀` beyond `X_Hux` (`HuxleyFrom X₀`):
  `1 - 10⁻²⁰ ≤ MA[ℙ](q) log q ≤ 1 + (log q)^{-3}`; with `lemma_7_3_a_099` (`≥ 0.99`) and
  `lemma_7_3_a_tendsto` (the left side tends to `1`);
* `rigid_add_new_le`, `rhoDet_le_one_add` : **Lemma 7.1(1)**, `ρ_det ≤ 1 + 1/(κu)`; with
  `one_sub_rhoDet_ge` (`1 - ρ_det(t) ≥ MA[ℙ](t) - 1/(κt)`, the integers in the window that are
  not `X₀`-smooth include every prime there) and `one_sub_rhoDet_ge_099`
  (`1 - ρ_det(t) ≥ (0.99 - 10⁻⁹)/log t`, used in Step 6(c) of Proposition 5.38);
* `jz_le` : `j_{X₀} = 1 - ρ_det(X₀) ≤ 1.0001/log X₀` (§5.6 notation, and Lemma XB), which uses
  the *upper* half of (84).

The lower bound `1 - ρ_det(u) ≥ 0.99/log u - 1/(κu)` of Lemma 7.1(1) is `BModel.rhoDet_le`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace BaseRange

/-- The number of new primes (rational primes `≥ X₀`) in `[a, b]`. -/
noncomputable def newPrimeCount (X0 : ℕ) (a b : ℝ) : ℕ :=
  {p : ℕ | p.Prime ∧ X0 ≤ p ∧ a ≤ p ∧ (p : ℝ) ≤ b}.ncard

/-- `MA[ℙ](q) = MA_{κq}[rational primes ≥ X₀](q)` (§7.2). -/
noncomputable def MAP (X0 : ℕ) (κ q : ℝ) : ℝ := newPrimeCount X0 q ((1 + κ) * q) / (κ * q)

lemma newPrimeCount_eq {X0 : ℕ} {a b : ℝ} (ha : (X0 : ℝ) ≤ a) :
    newPrimeCount X0 a b = primeCount a b := by
  unfold newPrimeCount primeCount
  congr 1
  ext p
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨h1, -, h3, h4⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    exact ⟨h1, by exact_mod_cast ha.trans h3, h3, h4⟩

lemma MAP_eq {X0 : ℕ} {κ q : ℝ} (hq : (X0 : ℝ) ≤ q) :
    MAP X0 κ q = primeCount q ((1 + κ) * q) / (κ * q) := by
  rw [MAP, newPrimeCount_eq hq]

lemma MAP_nonneg (X0 : ℕ) {κ q : ℝ} (hκ : 0 ≤ κ) (hq : 0 ≤ q) : 0 ≤ MAP X0 κ q :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg hκ hq)

/-! ### The size of `κ` -/

/-- `κ = exp((-5/12 + 2ε_κ) log X₀)`. -/
lemma kappa_eq_exp {X0 : ℝ} (hX : 0 < X0) :
    Construction.kappaParam X0 = Real.exp (Real.log X0 * (-5 / 12 + 2 * (0.01 : ℝ))) := by
  rw [Construction.kappaParam, Real.rpow_def_of_pos hX]

lemma exp_neg_100_le : Real.exp (-100) ≤ 1 / 10 ^ 21 := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : (2 : ℝ) ^ 100 ≤ Real.exp 1 ^ 100 := pow_le_pow_left₀ (by norm_num) h1 _
  rw [Real.exp_one_pow] at h2
  have : (10 : ℝ) ^ 21 ≤ 2 ^ 100 := by norm_num
  calc (10 : ℝ) ^ 21 ≤ 2 ^ 100 := this
    _ ≤ Real.exp ((100 : ℕ) : ℝ) := h2
    _ = Real.exp 100 := by norm_num

/-- `κ ≤ e^{-100} ≤ 10⁻²¹` for `log X₀ ≥ 10⁸`. -/
lemma kappa_le_tiny {X0 : ℝ} (hX0 : 0 < X0) (hX : 10 ^ 8 ≤ Real.log X0) :
    Construction.kappaParam X0 ≤ 1 / 10 ^ 21 := by
  rw [kappa_eq_exp hX0]
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_100_le
  nlinarith

/-! ### Lemma 7.3(a) -/

lemma one_lt_of_log {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) : 1 < (X0 : ℝ) :=
  QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX

lemma log_ge_of_ge {X0 : ℕ} {q : ℝ} (hX : 10 ^ 8 ≤ Real.log X0) (hq : (X0 : ℝ) ≤ q) :
    10 ^ 8 ≤ Real.log q :=
  hX.trans (Real.log_le_log (by linarith [one_lt_of_log hX]) hq)

lemma zpow_neg3_le {L : ℝ} (hL : 10 ^ 8 ≤ L) : L ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := by
  rw [zpow_neg, zpow_ofNat, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  calc (10 : ℝ) ^ 24 = (10 ^ 8) ^ 3 := by norm_num
    _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3

lemma zpow_neg3_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ L ^ (-3 : ℤ) := zpow_nonneg hL _

/-- The window `[q, (1+κ)q]`, `q ≥ X₀`, is admissible in (84). -/
lemma window_admissible {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {q : ℝ} (hq : (X0 : ℝ) ≤ q) :
    Admissible q q ((1 + Construction.kappaParam X0) * q) := by
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hq0 : 0 < q := by linarith [one_lt_of_log hX]
  refine ⟨le_rfl, by nlinarith, ?_⟩
  have := BModel.window_long hX hq
  have e : (1 + Construction.kappaParam X0) * q - q = Construction.kappaParam X0 * q := by ring
  rw [e]; exact this

/-- The two-sided bound behind Lemma 7.3(a): for `q ≥ X₀`, with `L = log q`,
`(1 - L⁻³) L/(L + κ) ≤ MA[ℙ](q) L ≤ 1 + L⁻³`. -/
theorem MAP_log_bounds {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq : (X0 : ℝ) ≤ q) :
    (1 - Real.log q ^ (-3 : ℤ)) * (Real.log q / (Real.log q + Construction.kappaParam X0)) ≤
        MAP X0 (Construction.kappaParam X0) q * Real.log q ∧
      MAP X0 (Construction.kappaParam X0) q * Real.log q ≤ 1 + Real.log q ^ (-3 : ℤ) := by
  set κ := Construction.kappaParam X0 with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hL := log_ge_of_ge hX hq
  have hL0 : 0 < Real.log q := by linarith
  have hadm := window_admissible hX hq
  have hX2 : (2 : ℝ) ≤ X0 := by
    have := Real.add_one_le_exp (10 ^ 8 : ℝ)
    have h2 : Real.exp (10 ^ 8) ≤ X0 := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < X0)]; exact Real.exp_le_exp.mpr hX
    linarith
  have hlo := count_ge hH hX2 hq hadm
  have hhi := count_le hH hX2 hq hadm
  have hb : q < (1 + κ) * q := by nlinarith
  have hli_ge := liI_ge hq1 hb.le
  have hli_le := liI_le hq1 hb.le
  have hκq : 0 < κ * q := mul_pos hκ0 hq0
  have e1 : (1 + κ) * q - q = κ * q := by ring
  rw [e1] at hli_ge hli_le
  have hlogb : Real.log ((1 + κ) * q) ≤ Real.log q + κ := by
    rw [Real.log_mul (by linarith) hq0.ne']
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + κ)
    linarith
  have hlogb0 : 0 < Real.log ((1 + κ) * q) := Real.log_pos (by nlinarith)
  have hε0 := zpow_neg3_nonneg hL0.le (L := Real.log q)
  have hε1 : Real.log q ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hL
  rw [MAP_eq hq]
  constructor
  · -- lower bound
    have h1 : κ * q / (Real.log q + κ) ≤ liI q ((1 + κ) * q) := by
      refine le_trans ?_ hli_ge
      exact div_le_div_of_nonneg_left hκq.le hlogb0 hlogb
    have h2 : (1 - Real.log q ^ (-3 : ℤ)) * (κ * q / (Real.log q + κ)) ≤
        primeCount q ((1 + κ) * q) :=
      (mul_le_mul_of_nonneg_left h1 (by linarith)).trans hlo
    rw [div_mul_eq_mul_div, le_div_iff₀ hκq]
    have e : (1 - Real.log q ^ (-3 : ℤ)) * (Real.log q / (Real.log q + κ)) * (κ * q) =
        (1 - Real.log q ^ (-3 : ℤ)) * (κ * q / (Real.log q + κ)) * Real.log q := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h2 hL0.le
  · -- upper bound
    have h2 : (primeCount q ((1 + κ) * q) : ℝ) ≤
        (1 + Real.log q ^ (-3 : ℤ)) * (κ * q / Real.log q) :=
      hhi.trans (mul_le_mul_of_nonneg_left hli_le (by linarith))
    rw [div_mul_eq_mul_div, div_le_iff₀ hκq]
    have e : (1 + Real.log q ^ (-3 : ℤ)) * (κ * q / Real.log q) * Real.log q =
        (1 + Real.log q ^ (-3 : ℤ)) * (κ * q) := by
      field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_right h2 hL0.le

/-- **Lemma 7.3(a)** (Huxley part): for every `q ≥ X₀` (with `X₀ ≥ X_Hux`, i.e. (84) from `X₀`
on, and `log X₀ ≥ 10⁸`), `1 - 10⁻²⁰ ≤ MA[ℙ](q) log q ≤ 1 + (log q)^{-3}`. -/
theorem lemma_7_3_a {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq : (X0 : ℝ) ≤ q) :
    1 - 1 / 10 ^ 20 ≤ MAP X0 (Construction.kappaParam X0) q * Real.log q ∧
      MAP X0 (Construction.kappaParam X0) q * Real.log q ≤ 1 + Real.log q ^ (-3 : ℤ) := by
  obtain ⟨h1, h2⟩ := MAP_log_bounds hX hH hq
  refine ⟨le_trans ?_ h1, h2⟩
  set κ := Construction.kappaParam X0
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hκs : κ ≤ 1 / 10 ^ 21 := kappa_le_tiny (by linarith [one_lt_of_log hX]) hX
  have hL := log_ge_of_ge hX hq
  have hL0 : 0 < Real.log q := by linarith
  have hε0 := zpow_neg3_nonneg hL0.le (L := Real.log q)
  have hε1 : Real.log q ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hL
  have hr : 1 - κ / Real.log q ≤ Real.log q / (Real.log q + κ) := by
    rw [le_div_iff₀ (by linarith)]
    have : (1 - κ / Real.log q) * (Real.log q + κ) = Real.log q - κ ^ 2 / Real.log q := by
      field_simp; ring
    rw [this]
    have : 0 ≤ κ ^ 2 / Real.log q := by positivity
    linarith
  have hκL : κ / Real.log q ≤ 1 / 10 ^ 21 := by
    rw [div_le_iff₀ hL0]
    nlinarith
  have hr0 : 0 ≤ 1 - κ / Real.log q := by linarith
  calc 1 - 1 / 10 ^ 20 ≤ (1 - Real.log q ^ (-3 : ℤ)) * (1 - κ / Real.log q) := by
        nlinarith [mul_nonneg hε0 (div_nonneg hκ0.le hL0.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by linarith)

/-- Lemma 7.3(a), the form used throughout: `MA[ℙ](q) log q ≥ 0.99` for `q ≥ X₀`. -/
theorem lemma_7_3_a_099 {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {q : ℝ}
    (hq : (X0 : ℝ) ≤ q) : 0.99 ≤ MAP X0 (Construction.kappaParam X0) q * Real.log q := by
  have := (lemma_7_3_a hX hH hq).1
  linarith

/-- Lemma 7.3(a): `MA[ℙ](q) log q → 1` as `q → ∞`. -/
theorem lemma_7_3_a_tendsto {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) :
    Tendsto (fun q => MAP X0 (Construction.kappaParam X0) q * Real.log q) atTop (𝓝 1) := by
  set κ := Construction.kappaParam X0
  have hε : Tendsto (fun q : ℝ => Real.log q ^ (-3 : ℤ)) atTop (𝓝 0) := by
    have : Tendsto (fun q : ℝ => (Real.log q ^ 3)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
    refine this.congr fun q => ?_
    rw [zpow_neg, zpow_ofNat]
  have hδ : Tendsto (fun q : ℝ => κ * (Real.log q)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul κ
    simpa using this
  have hlow : Tendsto (fun q : ℝ => 1 - Real.log q ^ (-3 : ℤ) - κ * (Real.log q)⁻¹) atTop
      (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hε |>.sub hδ
    simpa using this
  have hhigh : Tendsto (fun q : ℝ => 1 + Real.log q ^ (-3 : ℤ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop (X0 : ℝ)] with q hq
    obtain ⟨h1, -⟩ := MAP_log_bounds hX hH hq
    obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
    have hL := log_ge_of_ge hX hq
    have hL0 : 0 < Real.log q := by linarith
    have hε0 := zpow_neg3_nonneg hL0.le (L := Real.log q)
    have hε1 : Real.log q ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hL
    have hr : 1 - κ * (Real.log q)⁻¹ ≤ Real.log q / (Real.log q + κ) := by
      rw [le_div_iff₀ (by linarith)]
      have : (1 - κ * (Real.log q)⁻¹) * (Real.log q + κ) = Real.log q - κ ^ 2 / Real.log q := by
        field_simp; ring
      rw [this]
      have : 0 ≤ κ ^ 2 / Real.log q := by positivity
      linarith
    have hd0 : 0 ≤ κ * (Real.log q)⁻¹ := by positivity
    calc 1 - Real.log q ^ (-3 : ℤ) - κ * (Real.log q)⁻¹
        ≤ (1 - Real.log q ^ (-3 : ℤ)) * (1 - κ * (Real.log q)⁻¹) := by nlinarith
      _ ≤ _ := (mul_le_mul_of_nonneg_left hr (by linarith)).trans h1
  · filter_upwards [eventually_ge_atTop (X0 : ℝ)] with q hq
    exact (MAP_log_bounds hX hH hq).2

/-! ### Lemma 7.1(1): the rigid density -/

/-- The integers of `[u, (1+κ)u]`. -/
noncomputable def windowInts (κ u : ℝ) : Finset ℕ := Finset.Icc ⌈u⌉₊ ⌊(1 + κ) * u⌋₊

lemma windowInts_card_le {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) :
    ((windowInts κ u).card : ℝ) ≤ κ * u + 1 := by
  rw [windowInts, Nat.card_Icc]
  set b := (1 + κ) * u
  have hc : ⌈u⌉₊ ≤ ⌊b⌋₊ + 1 := by
    have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu.le
    have h2 : b - 1 < (⌊b⌋₊ : ℝ) := Nat.sub_one_lt_floor b
    have : (⌈u⌉₊ : ℝ) < ⌊b⌋₊ + 1 + 1 := by
      have : u ≤ b := by simp only [b]; nlinarith
      linarith
    exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
  rw [Nat.cast_sub hc]
  push_cast
  have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by simp only [b]; positivity)
  have : b = κ * u + u := by simp only [b]; ring
  linarith

/-- The rigid integers of the window as a finset. -/
noncomputable def rigidSet (X0 : ℕ) (κ u : ℝ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo ⌊(1 + κ) * u⌋₊ X0).filter fun n : ℕ => u ≤ (n : ℝ)

/-- The new primes of the window as a finset. -/
noncomputable def newSet (X0 : ℕ) (κ u : ℝ) : Finset ℕ :=
  (windowInts κ u).filter fun n => n.Prime ∧ X0 ≤ n

lemma rigidCount_eq (X0 : ℕ) (κ u : ℝ) :
    Target.rigidCount X0 u ((1 + κ) * u) = (rigidSet X0 κ u).card := rfl

lemma newPrimeCount_eq_card (X0 : ℕ) {κ u : ℝ} (hb : 0 ≤ (1 + κ) * u) :
    newPrimeCount X0 u ((1 + κ) * u) = (newSet X0 κ u).card := by
  unfold newPrimeCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [mem_setOf_eq, newSet, windowInts, Finset.coe_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hX, h1, h2⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp, hX⟩
  · rintro ⟨⟨h1, h2⟩, hp, hX⟩
    exact ⟨hp, hX, Nat.ceil_le.mp h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le hb)⟩

lemma rigidSet_subset (X0 : ℕ) (κ u : ℝ) : rigidSet X0 κ u ⊆ windowInts κ u := by
  intro n hn
  simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo] at hn
  exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hn.2, hn.1.1⟩

lemma disjoint_rigid_new (X0 : ℕ) (κ u : ℝ) : Disjoint (rigidSet X0 κ u) (newSet X0 κ u) := by
  rw [Finset.disjoint_left]
  intro n hnS hnP
  simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers]
    at hnS
  simp only [newSet, Finset.mem_filter] at hnP
  have hmem : n ∈ n.primeFactorsList := by
    rw [Nat.primeFactorsList_prime hnP.2.1]; simp
  have := hnS.1.2.2 n hmem
  omega

/-- Rigid integers and new primes are disjoint sets of integers of the window:
`Ψ([u,(1+κ)u], X₀) + #{new primes in the window} ≤ κu + 1`. -/
lemma rigid_add_new_le (X0 : ℕ) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) :
    (Target.rigidCount X0 u ((1 + κ) * u) : ℝ) + newPrimeCount X0 u ((1 + κ) * u) ≤
      κ * u + 1 := by
  rw [rigidCount_eq, newPrimeCount_eq_card X0 (by positivity)]
  have h1 : (rigidSet X0 κ u).card + (newSet X0 κ u).card ≤ (windowInts κ u).card := by
    rw [← Finset.card_union_of_disjoint (disjoint_rigid_new X0 κ u)]
    exact Finset.card_le_card (Finset.union_subset (rigidSet_subset X0 κ u)
      (Finset.filter_subset _ _))
  have h2 := windowInts_card_le hκ hu
  have : ((rigidSet X0 κ u).card : ℝ) + (newSet X0 κ u).card ≤ (windowInts κ u).card := by
    exact_mod_cast h1
  linarith

/-- **Lemma 7.1(1)**, upper bound: `ρ_det(u) ≤ 1 + 1/(κu)`. -/
theorem rhoDet_le_one_add (X0 : ℕ) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) :
    Target.rhoDet X0 κ u ≤ 1 + 1 / (κ * u) := by
  have h := rigid_add_new_le X0 hκ hu
  have h0 : (0 : ℝ) ≤ newPrimeCount X0 u ((1 + κ) * u) := Nat.cast_nonneg _
  unfold Target.rhoDet
  rw [div_le_iff₀ (mul_pos hκ hu)]
  have : (1 + 1 / (κ * u)) * (κ * u) = κ * u + 1 := by field_simp
  rw [this]; linarith

/-- `1 - ρ_det(t) ≥ MA[ℙ](t) - 1/(κt)`: the integers of the window that are not `X₀`-smooth
include every new prime there. -/
theorem one_sub_rhoDet_ge (X0 : ℕ) {κ t : ℝ} (hκ : 0 < κ) (ht : 0 < t) :
    MAP X0 κ t - 1 / (κ * t) ≤ 1 - Target.rhoDet X0 κ t := by
  have h := rigid_add_new_le X0 hκ ht
  have hκt := mul_pos hκ ht
  unfold Target.rhoDet MAP
  have e : (1 : ℝ) = (κ * t) / (κ * t) := (div_self hκt.ne').symm
  rw [div_sub_div_same, sub_div' hκt.ne', div_le_div_iff_of_pos_right hκt]
  linarith

/-- `1 - ρ_det(t) ≥ (0.99 - 10⁻⁹)/log t` for `t ≥ X₀` (Step 6(c) of Proposition 5.38). -/
theorem one_sub_rhoDet_ge_099 {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0)
    {t : ℝ} (ht : (X0 : ℝ) ≤ t) :
    (0.99 - 1 / 10 ^ 9) / Real.log t ≤ 1 - Target.rhoDet X0 (Construction.kappaParam X0) t := by
  set κ := Construction.kappaParam X0
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have ht0 : 0 < t := by linarith
  have hL := log_ge_of_ge hX ht
  have hL0 : 0 < Real.log t := by linarith
  have ha := lemma_7_3_a_099 hX hH ht
  have hg := one_sub_rhoDet_ge X0 hκ0 ht0
  -- `log t/(κt) ≤ 10⁻⁹`
  have hw := BModel.window_long hX ht
  have hsmall : Real.log t / (κ * t) ≤ 1 / 10 ^ 9 := by
    have hlog : Real.log t ≤ t ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div ht0.le (by norm_num)
    have hpos : 0 < (2 * t) ^ (7 / 12 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have h2t : t ^ (7 / 12 : ℝ) ≤ (2 * t) ^ (7 / 12 : ℝ) :=
      Real.rpow_le_rpow ht0.le (by linarith) (by norm_num)
    have hsplit : t ^ (7 / 12 : ℝ) = t ^ (1 / 2 : ℝ) * t ^ (1 / 12 : ℝ) := by
      rw [← Real.rpow_add ht0]; norm_num
    have hbig : 2 * 10 ^ 9 ≤ t ^ (1 / 12 : ℝ) := by
      have hE : Real.exp (10 ^ 8 / 12) ≤ t ^ (1 / 12 : ℝ) := by
        rw [Real.rpow_def_of_pos ht0]
        exact Real.exp_le_exp.mpr (by linarith)
      refine le_trans ?_ hE
      have h1 := Real.add_one_le_exp (10 ^ 8 / 24 : ℝ)
      have h2 : Real.exp (10 ^ 8 / 12) = Real.exp (10 ^ 8 / 24) * Real.exp (10 ^ 8 / 24) := by
        rw [← Real.exp_add]; norm_num
      rw [h2]
      nlinarith
    have hs0 : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    rw [div_le_iff₀ (mul_pos hκ0 ht0)]
    calc Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by linarith
      _ ≤ 1 / 10 ^ 9 * (t ^ (1 / 2 : ℝ) * t ^ (1 / 12 : ℝ)) := by nlinarith
      _ = 1 / 10 ^ 9 * t ^ (7 / 12 : ℝ) := by rw [hsplit]
      _ ≤ 1 / 10 ^ 9 * (κ * t) := by nlinarith
  rw [div_le_iff₀ hL0]
  have h3 : 1 / (κ * t) * Real.log t ≤ 1 / 10 ^ 9 := by
    rw [one_div_mul_eq_div]; exact hsmall
  nlinarith

/-- Every integer of `[X₀, (1+κ)X₀]`, `κ < 1`, is `X₀`-smooth or a new prime. -/
lemma windowInts_subset {X0 : ℕ} {κ : ℝ} (hX : 1 ≤ X0) (hκ0 : 0 < κ) (hκ : κ < 1) :
    windowInts κ X0 ⊆ rigidSet X0 κ X0 ∪ newSet X0 κ X0 := by
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  rw [Nat.ceil_natCast] at hn'
  have hnb : (n : ℝ) ≤ (1 + κ) * X0 :=
    (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by positivity))
  have hX0n : X0 ≤ n := hn'.1
  by_cases hs : ∀ p ∈ n.primeFactorsList, p < X0
  · refine Finset.mem_union_left _ ?_
    simp only [rigidSet, Finset.mem_filter, Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers]
    exact ⟨⟨hn'.2, by omega, hs⟩, by exact_mod_cast hX0n⟩
  · push_neg at hs
    obtain ⟨p, hp, hpX⟩ := hs
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_primeFactorsList hp
    have hk : k = 1 := by
      by_contra hk1
      have hk0 : k ≠ 0 := by rintro rfl; simp at hX0n; omega
      have hk2 : 2 ≤ k := by omega
      have h1 : (2 * X0 : ℝ) ≤ ((p * k : ℕ) : ℝ) := by
        push_cast
        have : (X0 : ℝ) ≤ p := by exact_mod_cast hpX
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith
      have hX0r : (1 : ℝ) ≤ X0 := by exact_mod_cast hX
      nlinarith
    subst hk
    refine Finset.mem_union_right _ ?_
    simp only [newSet, Finset.mem_filter, mul_one]
    exact ⟨by simpa using hn, hpp, hpX⟩

/-- `j_{X₀} = 1 - ρ_det(X₀) ≤ MA[ℙ](X₀)` (the window `[X₀, (1+κ)X₀]` holds at least `κX₀`
integers, each `X₀`-smooth or a new prime). -/
lemma jz_le_MAP {X0 : ℕ} {κ : ℝ} (hX : 1 ≤ X0) (hκ0 : 0 < κ) (hκ : κ < 1) :
    1 - Target.rhoDet X0 κ X0 ≤ MAP X0 κ X0 := by
  have hX0 : (0 : ℝ) < X0 := by exact_mod_cast hX
  have hκX := mul_pos hκ0 hX0
  have hcard : (windowInts κ X0).card ≤ (rigidSet X0 κ X0).card + (newSet X0 κ X0).card :=
    (Finset.card_le_card (windowInts_subset hX hκ0 hκ)).trans (Finset.card_union_le _ _)
  have hlow : κ * X0 ≤ ((windowInts κ X0).card : ℝ) := by
    rw [windowInts, Nat.card_Icc, Nat.ceil_natCast]
    have h2 : (1 + κ) * X0 - 1 < (⌊(1 + κ) * (X0 : ℝ)⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hle : X0 ≤ ⌊(1 + κ) * (X0 : ℝ)⌋₊ := Nat.le_floor (by nlinarith)
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hc : (κ * X0 : ℝ) ≤ (rigidSet X0 κ X0).card + (newSet X0 κ X0).card := by
    refine hlow.trans ?_; exact_mod_cast hcard
  unfold Target.rhoDet MAP
  rw [rigidCount_eq, newPrimeCount_eq_card X0 (by positivity)]
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hκX, one_mul]
  linarith

/-- `j_{X₀} = 1 - ρ_det(X₀) ≤ 1.0001/log X₀`, by the upper half of (84). -/
theorem jz_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) :
    1 - Target.rhoDet X0 (Construction.kappaParam X0) X0 ≤ 1.0001 / Real.log X0 := by
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hκ1 : Construction.kappaParam X0 < 1 :=
    (kappa_le_tiny (by linarith) hX).trans_lt (by norm_num)
  have hX1n : 1 ≤ X0 := by exact_mod_cast hX1.le
  have h1 := jz_le_MAP hX1n hκ0 hκ1
  have h2 := (lemma_7_3_a hX hH le_rfl).2
  have hL0 : 0 < Real.log X0 := by linarith
  have hε1 : Real.log X0 ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hX
  rw [le_div_iff₀ hL0]
  nlinarith

end BaseRange
