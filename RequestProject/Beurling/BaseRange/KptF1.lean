module

public import RequestProject.Beurling.BaseRange.EulerR
public import RequestProject.Beurling.BaseRange.KshQSecond

/-!
# Lemma 7.3(c): the `K_pt` half (`KR.Sharp.KptF1Bound`)

For the realised operator `K_pt` (`KR.Sharp.Kpt`) acting on `f₁ 1_{[X₀,∞)}`, on `[X₀, xmax]`:

  `|K_pt(f₁ 1_{[X₀,∞)})(x)| ≤ Λ⁻³(log v + 0.01)`, and for `v ≥ 4` it is at most
  `(U/log x)³ (log U + 1.01) + 2e^γ e^{Ein(2)} (v/U) v⁻⁴ Λ⁻³`,

following bullets 1–3 of the proof of Lemma 7.3(c) for the realised system:

* bullet 1 (and 3): the cofactor sum `∑_{1 < w ≤ b} 1/(w log(x/w)) ≤ log(log x/log(x/b))
  + 1.01/log(x/b)` (`HBS.cofactor_sum_le`, from the two-sided harmonic bound under (HBS));
* bullet 2: the filter `τ_w < x/w` of `K_pt` and the decision-order bound `p ≤ 2 t(p)` put the
  primes of the cofactor below `Y = 2y`; Rankin's bound over the elements (`rankin_elems`) and
  the realised Euler product (`HBS.realProd_le`, `HBS.zinf_le`) give
  `∑ 1/w ≤ v⁻⁴ · 2e^γ e^{Ein(2)} log y`.

Hypotheses: (HBS) on `[1, Z]` with `xmax/X₀ ≤ Z` (on `Good(<xmax)` this is `hbs_local`),
`X₀/2 ≤ X₀⁻ ≤ X₀`, `log X₀ ≥ 10⁸`, (84) from `X₀` on, and the decision order satisfies
`labelVal p ≤ 2 t(p)` for every prime label `p` (a prime is decided no later than its value plus
half a jitter width, and the width is below the height). The paper's count "at most `2.01 H(y)`
realised primes in `(y, y + H(y)]`" is not needed: Lemma 5.1(iv) for the realised primes up to
`2y` replaces it.

* `kptF1Bound` : **`KR.Sharp.KptF1Bound P tw X₀⁻ X₀ xmax`**.
-/

@[expose] public section

open Real Finset BSCert.Consts BSCert.EiFn BeurlingSystem

namespace BaseRange

variable (P : BeurlingSystem)

lemma iota_zero : iota 0 = 1 := by simp [iota]

lemma two_le_iota_iff (e : ℕ →₀ ℕ) : 2 ≤ iota e ↔ e ≠ 0 := by
  constructor
  · rintro h rfl; rw [iota_zero] at h; omega
  · intro he
    have h1 := iota_pos e
    by_contra hc
    have : iota e = 1 := by omega
    exact he (iota_injective (this.trans iota_zero.symm))

/-- `K_pt g` as a sum over the elements `e ≠ 0` of value `≤ x/X₀⁻`. -/
lemma kpt_eq (tw : ℕ → ℝ) (X0m : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    KR.Sharp.Kpt P tw X0m g x = ∑ e ∈ (P.elems (x / X0m)).filter (· ≠ 0),
      (open scoped Classical in
        if ∀ j ∈ e.support, tw (qp j) * P.val e < x then g (x / P.val e) / P.val e else 0) := by
  classical
  unfold KR.Sharp.Kpt KR.NAll
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => iota_injective h)]
  apply Finset.sum_congr
  · ext e; simp only [Finset.mem_filter, two_le_iota_iff]
  · intro e _
    simp only [KR.Vl, P.valN_iota]
    have : (∀ p ∈ (iota e).primeFactors, tw p * P.val e < x) ↔
        (∀ j ∈ e.support, tw (qp j) * P.val e < x) := by
      rw [primeFactors_iota]
      simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    simp only [this]

/-- `|f₁ 1_{[X₀,∞)}(q)| ≤ 1[q ≥ X₀] (log q)⁻³/log q`. -/
lemma abs_f1cut_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (q : ℝ) :
    |KR.Sharp.f1cut X0 q| ≤
      if (X0 : ℝ) ≤ q then 1 / Real.log q ^ 3 * (1 / Real.log q) else 0 := by
  unfold KR.Sharp.f1cut
  split_ifs with hq
  · have hX1 := one_lt_of_log hX
    have hlq : Real.log X0 ≤ Real.log q := Real.log_le_log (by linarith) hq
    have hlq0 : 0 < Real.log q := by linarith
    have h1 := abs_f1_le hX hH hq
    have h2 := f0_le hX1 (BModel.kappa_facts hX).1 hq
    rw [zpow_neg, zpow_ofNat, ← one_div] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  · simp

/-- The primes of value `≤ Y` are the first `J` primes. -/
lemma primesLe_eq_range (Y : ℝ) : ∃ J : ℕ, ∀ j, P.p j ≤ Y ↔ j < J := by
  classical
  have hex : ∃ j, Y < P.p j := by
    obtain ⟨j, hj⟩ := (P.tendsto.eventually (Filter.eventually_gt_atTop Y)).exists
    exact ⟨j, hj⟩
  refine ⟨Nat.find hex, fun j => ?_⟩
  constructor
  · intro hj
    by_contra hc
    push_neg at hc
    have := P.mono hc
    have := Nat.find_spec hex
    linarith
  · intro hj
    have := Nat.find_min hex hj
    push_neg at this
    exact this

lemma log_le_div_e {v : ℝ} (hv : 0 < v) : Real.log v ≤ v / Real.exp 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hv (Real.exp_pos 1))
  rw [Real.log_div hv.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
  linarith

set_option maxHeartbeats 3200000 in
/-- **The `K_pt` half of Lemma 7.3(c)** (`KR.Sharp.KptF1Bound`). -/
theorem kptF1Bound {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {X0 : ℕ}
    (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) (hXm1 : (X0 : ℝ) / 2 ≤ X0m)
    (hXm2 : X0m ≤ X0) {tw : ℕ → ℝ} (hdec2 : ∀ p, p.Prime → P.labelVal p ≤ 2 * tw p)
    {xmax : ℝ} (hZ : xmax / X0 ≤ Z) :
    KR.Sharp.KptF1Bound P tw X0m X0 xmax := by
  classical
  intro x hx hxm
  set κ := Construction.kappaParam X0
  set Λ := Real.log X0 with hΛdef
  set L := Real.log x with hLdef
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hx0 : 0 < x := by linarith
  have hLΛ : Λ ≤ L := Real.log_le_log hX0 hx
  have hL0 : 0 < L := by linarith
  have hX0m : 0 < X0m := by linarith
  -- the sum over elements
  set E := (P.elems (x / X0m)).filter (· ≠ 0)
  set T : (ℕ →₀ ℕ) → ℝ := fun e => if ∀ j ∈ e.support, tw (qp j) * P.val e < x then
    KR.Sharp.f1cut X0 (x / P.val e) / P.val e else 0 with hT
  have hK : KR.Sharp.Kpt P tw X0m (KR.Sharp.f1cut X0) x = ∑ e ∈ E, T e := kpt_eq P tw X0m _ x
  -- each term vanishes unless `val e ≤ x/X₀`, and then `|T e| ≤ (log(x/val e))⁻⁴/val e`
  have hTb : ∀ e ∈ E, |T e| ≤ if P.val e ≤ x / X0 then
      1 / Real.log (x / P.val e) ^ 3 * (1 / (P.val e * Real.log (x / P.val e))) else 0 := by
    intro e _
    have hv0 := P.val_pos e
    simp only [hT]
    refine (abs_ite_le _ _).trans ?_
    rw [abs_div, abs_of_pos hv0]
    have hf := abs_f1cut_le hX hH (x / P.val e)
    have hiff : (X0 : ℝ) ≤ x / P.val e ↔ P.val e ≤ x / X0 := by
      rw [le_div_iff₀ hv0, le_div_iff₀ hX0, mul_comm]
    by_cases hc : P.val e ≤ x / X0
    · rw [if_pos (hiff.mpr hc)] at hf
      rw [if_pos hc, div_le_iff₀ hv0]
      refine hf.trans (le_of_eq ?_)
      have : Real.log (x / P.val e) ≠ 0 := by
        have := Real.log_le_log hX0 (hiff.mpr hc); linarith
      field_simp
    · rw [if_neg (fun h' => hc (hiff.mp h'))] at hf
      rw [if_neg hc]
      have : |KR.Sharp.f1cut X0 (x / P.val e)| = 0 := le_antisymm hf (abs_nonneg _)
      rw [this, zero_div]
  -- the cofactors with `val e ≤ x/X₀`
  have hEsub : ∀ b, b ≤ x / X0 →
      (P.elems b).filter (· ≠ 0) = E.filter (fun e => P.val e ≤ b) := by
    intro b hb
    ext e
    simp only [E, Finset.mem_filter, P.mem_elems]
    have : x / X0 ≤ x / X0m := div_le_div_of_nonneg_left hx0.le hX0m hXm2
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have hb0 : (1 : ℝ) ≤ x / X0 := by rw [le_div_iff₀ hX0]; linarith
  have hbx : x / X0 < x := div_lt_self hx0 hX1
  have hbZ : x / X0 ≤ Z := (div_le_div_of_nonneg_right hxm hX0.le).trans hZ
  rw [hK]
  -- a general bound for a sub-sum with `log(x/val e) ≥ ℓ`
  have hpart : ∀ (S : Finset (ℕ →₀ ℕ)) (ℓ : ℝ), 0 < ℓ → S ⊆ E →
      (∀ e ∈ S, P.val e ≤ x / X0 → ℓ ≤ Real.log (x / P.val e)) →
      ∑ e ∈ S, |T e| ≤ 1 / ℓ ^ 3 * ∑ e ∈ S.filter (fun e => P.val e ≤ x / X0),
        1 / (P.val e * Real.log (x / P.val e)) := by
    intro S ℓ hℓ hS hl
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not S (fun e => P.val e ≤ x / X0)]
    have h0 : ∑ e ∈ S.filter (fun e => ¬ P.val e ≤ x / X0), |T e| = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      have := hTb e (hS he1)
      rw [if_neg he2] at this
      exact le_antisymm this (abs_nonneg _)
    rw [h0, add_zero]
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    have hb := hTb e (hS he1)
    rw [if_pos he2] at hb
    refine hb.trans ?_
    have hle := hl e he1 he2
    have hv0 := P.val_pos e
    have : 1 / Real.log (x / P.val e) ^ 3 ≤ 1 / ℓ ^ 3 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hℓ.le hle 3)
    exact mul_le_mul_of_nonneg_right this (by
      have : 0 < Real.log (x / P.val e) := by linarith
      positivity)
  have hlogq : ∀ e ∈ E, P.val e ≤ x / X0 → Λ ≤ Real.log (x / P.val e) := by
    intro e _ he
    have hv0 := P.val_pos e
    apply Real.log_le_log hX0
    rw [le_div_iff₀ hv0]; rw [le_div_iff₀ hX0] at he; linarith
  have hcof1 := h.cofactor_sum_le hb0 hbZ hbx
  have hxb : x / (x / X0) = X0 := by field_simp
  rw [hxb] at hcof1
  constructor
  · -- the first bound
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (hpart E Λ hΛ0 (subset_refl _) hlogq).trans ?_
    rw [← hEsub (x / X0) le_rfl]
    have h1 : Real.log (L / Λ) + 1.01 / Λ ≤ Real.log (L / Λ) + 0.01 := by
      have : 1.01 / Λ ≤ 0.01 := by rw [div_le_iff₀ hΛ0]; linarith
      linarith
    exact mul_le_mul_of_nonneg_left (hcof1.trans h1) (by positivity)
  · -- the second bound
    intro hv
    set v := L / Λ with hvdef
    set U := Uf v with hUdef
    have hv0 : 0 < v := by linarith
    have hU1 : 1 ≤ U := Uf_ge_one (by linarith)
    have hU0 : 0 < U := by linarith
    have hUv : U ≤ v := by
      simp only [hUdef, Uf]
      have := log_le_div_e hv0
      have he := Real.exp_one_gt_d9
      have : v / Real.exp 1 ≤ v * 0.37 := by
        rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
      nlinarith
    set ly := L / U with hly
    have hlyΛ : Λ ≤ ly := by
      rw [hly, le_div_iff₀ hU0]
      have : L = Λ * v := by rw [hvdef]; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left hUv hΛ0.le
    have hly0 : 0 < ly := by linarith
    have hlyL : ly ≤ L / 3.77 := by
      rw [hly]
      apply div_le_div_of_nonneg_left hL0.le (by norm_num)
      simp only [hUdef, Uf]
      have : Real.log 4 ≤ Real.log v := Real.log_le_log (by norm_num) hv
      have h4 : (1.386 : ℝ) ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9; push_cast; linarith
      linarith
    set y := Real.exp ly with hy
    have hy0 : 0 < y := Real.exp_pos _
    have hlogy : Real.log y = ly := Real.log_exp ly
    have hXy : (X0 : ℝ) ≤ y := by
      rw [hy, ← Real.exp_log hX0]; exact Real.exp_le_exp.mpr hlyΛ
    set σ := 2 / ly with hσ
    have hσ0 : 0 < σ := by positivity
    have hσs : σ ≤ 1 / 10 ^ 7 := by rw [hσ, div_le_iff₀ hly0]; nlinarith
    set Y := 2 * y with hYdef
    have hlogY : Real.log Y = ly + Real.log 2 := by
      rw [hYdef, Real.log_mul (by norm_num) hy0.ne', hlogy]; ring
    have hl2 := Real.log_two_lt_d9
    have hl2' := Real.log_two_gt_d9
    have hΛ4 : Λ ≤ L / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      have : L = Λ * v := by rw [hvdef]; field_simp
      rw [this]; nlinarith
    have hkey : Real.log 2 + ly + Λ ≤ L := by
      have h1 : L / 3.77 ≤ 0.2653 * L := by rw [div_le_iff₀ (by norm_num)]; nlinarith
      have h2 : L / 4 = 0.25 * L := by ring
      linarith
    have hYx : Y ≤ x / X0 := by
      rw [le_div_iff₀ hX0]
      have e : Y * X0 = Real.exp (Real.log 2 + ly + Λ) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hX0, hYdef, hy]
      rw [e, ← Real.exp_log hx0, ← hLdef]
      exact Real.exp_le_exp.mpr hkey
    have hYZ : Y ≤ Z := hYx.trans hbZ
    have hX2 : (2 : ℝ) ≤ X0 := by
      have := Real.add_one_le_exp (Real.log X0); rw [Real.exp_log hX0] at this; linarith
    have hZ3 : 3 ≤ Z := by rw [hYdef] at hYZ; linarith
    have hXmY : X0m ≤ Y := by rw [hYdef]; linarith
    have hσY : σ * Real.log Y ≤ 2.01 := by
      rw [hlogY, hσ, div_mul_eq_mul_div, div_le_iff₀ hly0]; nlinarith
    -- split the cofactors at `x/y`
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not E (fun e => P.val e ≤ x / y)]
    -- bullet 1
    have hxy : x / y ≤ x / X0 := div_le_div_of_nonneg_left hx0.le hX0 hXy
    have hB1 : ∑ e ∈ E.filter (fun e => P.val e ≤ x / y), |T e| ≤
        (U / L) ^ 3 * (Real.log U + 1.01) := by
      have hl : ∀ e ∈ E.filter (fun e => P.val e ≤ x / y), P.val e ≤ x / X0 →
          ly ≤ Real.log (x / P.val e) := by
        intro e he _
        have hv0 := P.val_pos e
        have he2 := (Finset.mem_filter.mp he).2
        rw [← hlogy]
        apply Real.log_le_log hy0
        rw [le_div_iff₀ hv0]; rw [le_div_iff₀ hy0] at he2; linarith
      refine (hpart _ ly hly0 (Finset.filter_subset _ _) hl).trans ?_
      have hfil : (E.filter (fun e => P.val e ≤ x / y)).filter (fun e => P.val e ≤ x / X0) =
          (P.elems (x / y)).filter (· ≠ 0) := by
        rw [hEsub (x / y) hxy, Finset.filter_filter]
        apply Finset.filter_congr
        intro e _
        constructor
        · rintro ⟨h1, -⟩; exact h1
        · intro h1; exact ⟨h1, h1.trans hxy⟩
      rw [hfil]
      have hb1 : (1 : ℝ) ≤ x / y := by
        rw [le_div_iff₀ hy0, one_mul, ← Real.exp_log hx0, hy]
        exact Real.exp_le_exp.mpr (by linarith [div_le_self hL0.le hU1])
      have hcof := h.cofactor_sum_le hb1 (hxy.trans hbZ) (div_lt_self hx0 (by
        rw [hy]; have := Real.add_one_lt_exp hly0.ne'; linarith))
      have hxy' : x / (x / y) = y := by field_simp
      rw [hxy', hlogy] at hcof
      have hlU : Real.log (L / ly) = Real.log U := by rw [hly]; congr 1; field_simp
      rw [hlU] at hcof
      have hU3 : (U / L) ^ 3 = 1 / ly ^ 3 := by rw [hly]; field_simp
      rw [hU3]
      have : 1.01 / ly ≤ 1.01 := by
        rw [div_le_iff₀ hly0]; nlinarith
      exact mul_le_mul_of_nonneg_left (hcof.trans (by linarith)) (by positivity)
    -- bullet 2
    obtain ⟨J, hJ⟩ := primesLe_eq_range P Y
    have hB2 : ∑ e ∈ E.filter (fun e => ¬ P.val e ≤ x / y), |T e| ≤
        1 / Λ ^ 4 * Real.exp (-(σ * (L - ly))) *
          ∏ j ∈ Finset.range J, (1 - P.p j ^ (-(1 - σ)))⁻¹ := by
      set S := (E.filter (fun e => ¬ P.val e ≤ x / y)).filter (fun e =>
        (∀ j ∈ e.support, tw (qp j) * P.val e < x) ∧ P.val e ≤ x / X0) with hS
      have hsplit : ∑ e ∈ E.filter (fun e => ¬ P.val e ≤ x / y), |T e| = ∑ e ∈ S, |T e| := by
        rw [hS]
        refine (Finset.sum_filter_of_ne ?_).symm
        intro e he hne
        refine ⟨?_, ?_⟩
        · by_contra hc
          apply hne
          simp only [hT]
          rw [if_neg hc]
          simp
        · by_contra hc
          apply hne
          have := hTb e (Finset.mem_filter.mp he).1
          rw [if_neg hc] at this
          exact le_antisymm this (abs_nonneg _)
      rw [hsplit]
      have hθ : 0 < 1 - σ := by linarith
      have hterm : ∀ e ∈ S, |T e| ≤ 1 / Λ ^ 4 * (Real.exp (-(σ * (L - ly))) *
          P.val e ^ (-(1 - σ))) := by
        intro e he
        obtain ⟨he1', ⟨hfilt, hvX⟩⟩ := Finset.mem_filter.mp he
        obtain ⟨he1, hvy⟩ := Finset.mem_filter.mp he1'
        have hv0 := P.val_pos e
        have hb := hTb e he1
        rw [if_pos hvX] at hb
        have hlq := hlogq e he1 hvX
        have hlq0 : 0 < Real.log (x / P.val e) := by linarith
        have h4 : 1 / Real.log (x / P.val e) ^ 3 * (1 / (P.val e * Real.log (x / P.val e))) ≤
            1 / Λ ^ 4 * (1 / P.val e) := by
          have e1 : 1 / Real.log (x / P.val e) ^ 3 * (1 / (P.val e * Real.log (x / P.val e))) =
              1 / Real.log (x / P.val e) ^ 4 * (1 / P.val e) := by field_simp
          rw [e1]
          exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ hΛ0.le hlq 4)) (by positivity)
        have hxy0 : 0 < x / y := div_pos hx0 hy0
        have hmxy : x / y < P.val e := lt_of_not_ge hvy
        have hr : 1 / P.val e ≤ Real.exp (-(σ * (L - ly))) * P.val e ^ (-(1 - σ)) := by
          have e1 : Real.exp (-(σ * (L - ly))) = (x / y) ^ (-σ) := by
            rw [Real.rpow_def_of_pos hxy0, Real.log_div hx0.ne' hy0.ne', hlogy, ← hLdef]
            congr 1; ring
          rw [e1]
          have h5 : (P.val e) ^ (-σ) * (P.val e) ^ (-(1 - σ)) ≤
              (x / y) ^ (-σ) * (P.val e) ^ (-(1 - σ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact Real.rpow_le_rpow_of_nonpos hxy0 hmxy.le (by linarith)
          have h6 : (P.val e) ^ (-σ) * (P.val e) ^ (-(1 - σ)) = 1 / P.val e := by
            rw [← Real.rpow_add hv0, show -σ + -(1 - σ) = (-1 : ℝ) by ring, Real.rpow_neg_one,
              one_div]
          linarith
        exact hb.trans (h4.trans (mul_le_mul_of_nonneg_left hr (by positivity)))
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply rankin_elems P hθ S
      intro e he j hj
      obtain ⟨he1', ⟨hfilt, hvX⟩⟩ := Finset.mem_filter.mp he
      obtain ⟨he1, hvy⟩ := Finset.mem_filter.mp he1'
      have hv0 := P.val_pos e
      have hmxy : x / y < P.val e := lt_of_not_ge hvy
      have htw : tw (qp j) < y := by
        have := hfilt j hj
        have h2 : tw (qp j) < x / P.val e := by rw [lt_div_iff₀ hv0]; exact this
        have h3 : x / P.val e < y := by
          rw [div_lt_iff₀ hv0]; rw [div_lt_iff₀ hy0] at hmxy; linarith
        linarith
      have hval := hdec2 (qp j) (qp_prime j)
      rw [P.labelVal_qp] at hval
      exact (hJ j).mp (by rw [hYdef]; linarith)
    -- the Euler product
    have hprimes : ∏ j ∈ Finset.range J, (1 - P.p j ^ (-(1 - σ)))⁻¹ =
        ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹ := by
      congr 1; ext j; rw [Finset.mem_range, mem_primesLe, hJ]
    rw [hprimes] at hB2
    have hY2 : 2 ≤ Y := by
      rw [hYdef]; linarith [Real.add_one_le_exp ly, show (1 : ℝ) ≤ X0 by linarith]
    have hR := h.realProd_le hZ3 hσ0 (by linarith) hY2 hYZ hσY
    have hXm4 : 10 ^ 4 ≤ Real.log X0m := by
      have h1 : Real.log ((X0 : ℝ) / 2) ≤ Real.log X0m := Real.log_le_log (by positivity) hXm1
      rw [Real.log_div hX0.ne' (by norm_num)] at h1
      linarith
    have hZ1 := h.zinf_le hZ3 hXm4 hXmY hYZ
    -- the numerics
    have hexp : Real.exp (-(σ * (L - ly))) = 1 / v ^ 4 := by
      have e1 : σ * (L - ly) = 2 * (U - 1) := by rw [hσ, hly]; field_simp
      have e2 : 2 * (U - 1) = 4 * Real.log v := by simp only [hUdef, Uf]; ring
      rw [e1, e2, show -(4 * Real.log v) = Real.log v * (-4 : ℝ) by ring,
        ← Real.rpow_def_of_pos hv0, Real.rpow_neg hv0.le, one_div]
      norm_num
    -- `∏ ≤ 2 e^γ e^{Ein 2} log y`
    have hEin : Ein (σ * Real.log Y) ≤ Ein 2 + 1 / 10 ^ 6 := by
      rcases le_or_gt (σ * Real.log Y) 2 with hle | hgt
      · have := SmoothTails.Ein_mono (mul_nonneg hσ0.le (by rw [hlogY]; linarith)) hle
        linarith
      · have h1 := ein_upper (by norm_num : (0 : ℝ) < 2) hgt.le
        have h2 := ph_mono (by norm_num : (0 : ℝ) < 2) hgt.le
        have h3 : ph (σ * Real.log Y) ≤ 4 := by
          have := ph_mono (by linarith) hσY
          refine this.trans ?_
          unfold ph
          have h := Real.exp_one_lt_d9
          have e : Real.exp 2.01 = Real.exp 1 * Real.exp 1 * Real.exp 0.01 := by
            simp only [← Real.exp_add]; norm_num
          have h4 : Real.exp 0.01 ≤ 1.0102 := by
            have := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.01)
              (by norm_num)
            norm_num at this ⊢; linarith
          rw [e, div_le_iff₀ (by norm_num)]
          have h1 : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
          nlinarith [Real.exp_pos 1, Real.exp_pos 0.01]
        have h5 : σ * Real.log Y - 2 ≤ 1 / (4 * 10 ^ 6) := by
          rw [hlogY, hσ]
          have : 2 / ly * (ly + Real.log 2) - 2 = 2 * Real.log 2 / ly := by field_simp; ring
          rw [this, div_le_div_iff₀ hly0 (by norm_num)]
          nlinarith
        have : (σ * Real.log Y - 2) * ph (σ * Real.log Y) ≤ 1 / 10 ^ 6 := by
          have h0 : 0 ≤ σ * Real.log Y - 2 := by linarith
          nlinarith [ph_pos (show (0:ℝ) < 2 by norm_num)]
        linarith
    have hgY : 2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) ≤ 1 / 10 ^ 6 := by
      have hlY0 : 0 < Real.log Y := by rw [hlogY]; linarith
      have h1 : Real.exp (σ * Real.log Y) ≤ Real.exp 2.01 := Real.exp_le_exp.mpr hσY
      have h2 : Real.exp 2.01 ≤ 8 := by
        have h := Real.exp_one_lt_d9
        have e : Real.exp 2.01 = Real.exp 1 * Real.exp 1 * Real.exp 0.01 := by
          simp only [← Real.exp_add]; norm_num
        have h4 : Real.exp 0.01 ≤ 1.0102 := by
          have := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.01)
            (by norm_num)
          norm_num at this ⊢; linarith
        rw [e]
        have h1 : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith [Real.exp_pos 1]
        nlinarith [Real.exp_pos 1, Real.exp_pos 0.01]
      have h3 : (Real.exp (σ * Real.log Y) - 1) / Real.log Y ≤ 8 / Real.log Y :=
        div_le_div_of_nonneg_right (by linarith) hlY0.le
      have h4 : 8 / Real.log Y ≤ 8 / 10 ^ 8 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); rw [hlogY]; linarith
      nlinarith
    have hXm : (X0 : ℝ) / 2 ≤ X0m := hXm1
    have hlogXm : Real.log (⌈X0m⌉₊ : ℝ) / Real.log (X0m / 2) ≤ 1.0001 := by
      have hc : (⌈X0m⌉₊ : ℝ) ≤ 2 * X0m := by
        have := Nat.ceil_lt_add_one hX0m.le
        have : (1 : ℝ) ≤ X0m := by linarith [h.X0m_ge]
        linarith
      have h1 : Real.log (⌈X0m⌉₊ : ℝ) ≤ Real.log X0m + Real.log 2 := by
        rw [← Real.log_mul hX0m.ne' (by norm_num)]
        exact Real.log_le_log (by positivity) (by linarith)
      have h2 : Real.log (X0m / 2) = Real.log X0m - Real.log 2 :=
        Real.log_div hX0m.ne' (by norm_num)
      have hXmΛ : Λ - 1 ≤ Real.log X0m := by
        have h1 : Real.log ((X0 : ℝ) / 2) ≤ Real.log X0m := Real.log_le_log (by positivity) hXm1
        rw [Real.log_div hX0.ne' (by norm_num)] at h1
        linarith
      rw [h2, div_le_iff₀ (by linarith)]
      linarith
    have hsm : Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) *
        Real.exp (Ein (σ * Real.log Y) + 2.2 * ((Real.exp (σ * Real.log Y) - 1) /
          Real.log Y) + 1076 * σ) ≤ 1.002 * Real.exp (Ein 2) := by
      rw [← Real.exp_add]
      have h2 : Real.log (X0m / 2) = Real.log X0m - Real.log 2 :=
        Real.log_div hX0m.ne' (by norm_num)
      have hXmΛ : Λ - 1 ≤ Real.log X0m := by
        have h1 : Real.log ((X0 : ℝ) / 2) ≤ Real.log X0m := Real.log_le_log (by positivity) hXm1
        rw [Real.log_div hX0.ne' (by norm_num)] at h1
        linarith
      have ha : 2.2 / Real.log (X0m / 2) ≤ 1 / 10 ^ 3 := by
        rw [h2, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hb : 25.6 / X0m ≤ 1 / 10 ^ 5 := by
        rw [div_le_div_iff₀ hX0m (by norm_num)]; linarith [h.X0m_ge]
      have hc : 1076 * σ ≤ 2 / 10 ^ 4 := by linarith
      have hsum : 2.2 / Real.log (X0m / 2) + 25.6 / X0m + (Ein (σ * Real.log Y) +
          2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) + 1076 * σ) ≤
          Ein 2 + 1 / 10 ^ 3 + 1 / 10 ^ 5 + 1 / 10 ^ 6 + 1 / 10 ^ 6 + 2 / 10 ^ 4 := by linarith
      refine (Real.exp_le_exp.mpr hsum).trans ?_
      rw [show Ein 2 + 1 / 10 ^ 3 + 1 / 10 ^ 5 + 1 / 10 ^ 6 + 1 / 10 ^ 6 + 2 / 10 ^ 4 =
        (1 / 10 ^ 3 + 1 / 10 ^ 5 + 1 / 10 ^ 6 + 1 / 10 ^ 6 + 2 / 10 ^ 4) + Ein 2 by ring,
        Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have := Real.exp_bound_div_one_sub_of_interval
        (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 3 + 1 / 10 ^ 5 + 1 / 10 ^ 6 + 1 / 10 ^ 6 + 2 / 10 ^ 4)
        (by norm_num)
      norm_num at this ⊢; linarith
    have hprod : ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹ ≤
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly := by
      have hZ0 : 0 ≤ ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 : ℝ)))⁻¹ :=
        Finset.prod_nonneg fun j _ => by
          have := h.two_le_p hZ3 j
          apply inv_nonneg.mpr
          have : P.p j ^ (-(1 : ℝ)) < 1 :=
            Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
          linarith
      have hlX2 : 0 < Real.log (X0m / 2) := Real.log_pos (by linarith [h.X0m_ge])
      have hlY : Real.log Y ≤ 1.0001 * ly := by rw [hlogY]; linarith
      have hA : 1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2)) ≤
          1.8 * 1.0001 * (1.0001 * ly) := by
        have e : 1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2)) =
            1.8 * (Real.log (⌈X0m⌉₊ : ℝ) / Real.log (X0m / 2)) * Real.log Y := by
          field_simp
        rw [e]
        have hlY0 : 0 ≤ Real.log Y := by rw [hlogY]; linarith
        have hc0 : 0 ≤ Real.log (⌈X0m⌉₊ : ℝ) / Real.log (X0m / 2) :=
          div_nonneg (Real.log_nonneg (by
            have := Nat.le_ceil X0m; linarith [h.X0m_ge])) hlX2.le
        calc 1.8 * (Real.log (⌈X0m⌉₊ : ℝ) / Real.log (X0m / 2)) * Real.log Y
            ≤ 1.8 * 1.0001 * Real.log Y := by
              apply mul_le_mul_of_nonneg_right _ hlY0; linarith
          _ ≤ 1.8 * 1.0001 * (1.0001 * ly) := by linarith
      have hA0 : 0 ≤ 1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2)) := by
        have := Nat.le_ceil X0m
        have hlY0 : 0 ≤ Real.log Y := by rw [hlogY]; linarith
        apply mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [h.X0m_ge])))
        exact div_nonneg hlY0 hlX2.le
      have hg := two_exp_gamma_ge
      have hE := Real.exp_pos (Ein 2)
      calc ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹
          ≤ (∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 : ℝ)))⁻¹) *
            Real.exp (Ein (σ * Real.log Y) +
              2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) + 1076 * σ) := hR
        _ ≤ (1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2)) *
              Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m)) *
            Real.exp (Ein (σ * Real.log Y) +
              2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) + 1076 * σ) :=
            mul_le_mul_of_nonneg_right hZ1 (Real.exp_pos _).le
        _ = (1.8 * Real.log (⌈X0m⌉₊ : ℝ) * (Real.log Y / Real.log (X0m / 2))) *
            (Real.exp (2.2 / Real.log (X0m / 2) + 25.6 / X0m) *
              Real.exp (Ein (σ * Real.log Y) +
                2.2 * ((Real.exp (σ * Real.log Y) - 1) / Real.log Y) + 1076 * σ)) := by ring
        _ ≤ (1.8 * 1.0001 * (1.0001 * ly)) * (1.002 * Real.exp (Ein 2)) :=
            mul_le_mul hA hsm (by positivity) (by positivity)
        _ ≤ 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly := by
            have : 1.8 * 1.0001 * (1.0001 * ly) * (1.002 * Real.exp (Ein 2)) =
                (1.8 * 1.0001 * 1.0001 * 1.002) * ly * Real.exp (Ein 2) := by ring
            rw [this]
            have : 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly =
                (2 * Real.exp Real.eulerMascheroniConstant) * ly * Real.exp (Ein 2) := by ring
            rw [this]
            apply mul_le_mul_of_nonneg_right _ hE.le
            apply mul_le_mul_of_nonneg_right _ hly0.le
            linarith
    have hfinal : 1 / Λ ^ 4 * Real.exp (-(σ * (L - ly))) *
        ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹ ≤
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / U) / v ^ 4 /
          Λ ^ 3 := by
      rw [hexp]
      have h0 : 0 ≤ 1 / Λ ^ 4 * (1 / v ^ 4) := by positivity
      calc 1 / Λ ^ 4 * (1 / v ^ 4) * ∏ j ∈ P.primesLe Y, (1 - P.p j ^ (-(1 - σ)))⁻¹
          ≤ 1 / Λ ^ 4 * (1 / v ^ 4) *
              (2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * ly) :=
            mul_le_mul_of_nonneg_left hprod h0
        _ = 2 * Real.exp Real.eulerMascheroniConstant * Real.exp (Ein 2) * (v / U) / v ^ 4 /
              Λ ^ 3 := by
            rw [hly]
            have : L = Λ * v := by rw [hvdef]; field_simp
            rw [this]
            field_simp
    unfold KR.Sharp.secondHalf
    rw [← hLdef, ← hΛdef, ← hvdef, ← hUdef]
    linarith

end BaseRange
