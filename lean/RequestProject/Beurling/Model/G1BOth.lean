module

public import RequestProject.Beurling.Model.G1BDet

/-!
# The `R'` and `σ_𝒜` changes in Steps 3–4 of Proposition 5.35(B): the field `hoth`

04f-bridge.tex, proof of Proposition 5.35, range (B).

* **`σ_𝒜`** (Step 3, last bullet): `|σ_𝒜| ≤ L_v⁻⁴` (Lemma 6.27(a), (b): `rhoCap_le_L4`,
  `KAbsR_le_L4`), vanishing unless `log v > L_*` (`rhoA_eq_zero_of_small`,
  `KAbsR_eq_zero_of_small`); with Corollary 5.9 in the dyadic form and the telescoping sum
  `sum_term_le` this gives `log y · sigS ≤ 77 · 4.04/(δ₂ (L_* - 3δ₂)²) ≤ 10⁻³⁰`
  (`log_mul_sigS_le`).
* **`R'`** (Step 3, "Resolvable `R'_j`, smooth change", and Step 4, "Pointwise", for the current
  oscillation if it is not resolvable): the named input `RprimeChangeR`, the bound of these two
  steps as tallied in Step 5 (`≤ log⁻² x` from the resolvable `R'_j`, `≤ 3000 κ₀` from the
  pointwise bound (Corollary 5.9) of the current oscillation, `κ₀ = X₀⁻¹` the constant relative
  amplitude of eq. (ampl)). It holds
  outright below `x₁ = e^{X₀²}` (`rprimeChange_of_lt`: `R' = 0` there; Step 4 is void).
* `hoth_R` : **the field `hoth`**: `log y · othS ≤ 10⁻²⁷`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

variable (θ X₀) in
/-- **The `R'` change of Steps 3–4** (04f-bridge.tex, Proposition 5.35(B), Step 3 "Resolvable
`R'_j`, smooth change" and Step 4 "Pointwise"; sizes as in Step 5): for every `z ∈ J`,
`log y · |∑_n c_n(y) (R'(max(z/n, X₀)) - R'(y/n))/n| ≤ 2 log⁻² y + 3000 κ₀`. -/
def RprimeChangeR (ω : JitterΩ) (y δ : ℝ) : Prop :=
  ∀ z ∈ Icc (y * (1 - 2 * δ)) (y * (1 - δ)),
    Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y))| ≤
      2 / Real.log y ^ 2 + 3000 * Construction.kappa0Param X₀

/-- **Step 4 is void below `x₁`**: if `y < x₁ = e^{X₀²}`, then `R' = 0` on `[1, y]` and
`RprimeChangeR` holds. -/
theorem rprimeChange_of_lt (hc : Cond θ X₀) (ω : JitterΩ) {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyx : y < switchOn X₀ 0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) :
    RprimeChangeR θ X₀ ω y δ := by
  intro z hz
  have hX1 := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hy0 : 0 < y := by linarith
  have hr0 : 0 ≤ z / y := div_nonneg (le_trans (by nlinarith) hz.1) hy0.le
  have hr1 : z / y ≤ 1 := (div_le_one hy0).mpr (by nlinarith [hz.2])
  have h0 : rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y)) = 0 := by
    rw [G1.rhoSh_eq_elems]
    refine Finset.sum_eq_zero fun e _ => ?_
    have hv1 := (PR θ X₀ ω).one_le_val e
    have hvy : y / (PR θ X₀ ω).val e ≤ y := div_le_self hy0.le hv1
    unfold oscF
    split_ifs with hv
    · obtain ⟨h1, h2⟩ := max_mem hr1 hv
      unfold RpR
      rw [deriv_osc_low _ _ (by linarith) (lt_of_le_of_lt (h2.trans hvy) hyx),
        deriv_osc_low _ _ (by linarith) (lt_of_le_of_lt hvy hyx)]
      ring
    · ring
  rw [h0, abs_zero, mul_zero]
  unfold Construction.kappa0Param
  positivity

section

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1000000 in
/-- **`|σ_𝒜(w)| ≤ L_w⁻⁴`**, and `σ_𝒜(w) = 0` for `log w ≤ L_*`, at `X₀ ≤ w ≤ 2(b + H(b))`
on `Good(< t)` (Lemma 6.27(a), (b)). -/
theorem sigR_bound {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {w : ℝ} (hwX : (X₀ : ℝ) ≤ w) (hw2 : w ≤ 2 * (b + Queue6.Hc X₀ b)) :
    |sigR θ X₀ ω w| ≤ (Real.log w ^ 4)⁻¹ ∧ (Real.log w ≤ Lstar X₀ → sigR θ X₀ ω w = 0) := by
  have hX1' := QueueMono.one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hw0 : 0 < w := by linarith
  have hLw0 : 0 < Real.log w := by
    linarith [Real.log_le_log (by linarith) hwX, hc.hX]
  have hK0 : 0 ≤ KAbsR θ X₀ ω (rhoT θ X₀ ω) w := KAbsR_nonneg ω (rhoT_nonneg ω) w
  have hA0 : 0 ≤ absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) w := by
    refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) hLw0.le)
    unfold absorbedBump
    split_ifs
    · by_cases hm : w ∈ Icc (uA θ a) a
      · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos hw0 _).le
      · rw [Set.indicator_of_notMem hm]
    · exact le_rfl
  have hXm0 := Xm_pos' hc
  have hwZ : w / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ (Zc_facts hc hb).2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have hKb := KAbsR_le_L4 hc ω hT (rhoT_nonneg ω) (rhoT_le_two hc hev ω) hwZ
  rw [zpow_neg, zpow_ofNat] at hKb
  have hAb := rhoCap_le_L4 hc hev hb hbt hQC hE1 hN hwX hw2
  unfold sigR
  refine ⟨?_, fun hsmall => ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · have hK : KAbsR θ X₀ ω (rhoT θ X₀ ω) w = 0 :=
      KAbsR_eq_zero_of_small hc ω _ (by unfold Lstar at hsmall; linarith)
    have hA : absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) w = 0 := by
      unfold absorbedDensityCap
      rw [rhoA_eq_zero_of_small hc ω hsmall]
      exact min_eq_left (div_nonneg (by norm_num) hLw0.le)
    rw [hK, hA]; ring

set_option maxHeartbeats 4000000 in
/-- **The `σ_𝒜` change** (Step 3, last bullet): for `r ∈ [1/2, 1]`, on `Good(< t)`,
`log y |∑_n c_n(y)(σ_𝒜(max(ry/n, X₀)) - σ_𝒜(y/n))/n| ≤ 10⁻³⁰`. -/
theorem log_mul_abs_rhoSh_sigF_le {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ}
    (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y r : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b) (hr0 : 1 / 2 ≤ r)
    (hr1 : r ≤ 1) :
    Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω r)| ≤
      1 / 10 ^ 30 := by
  classical
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hdec := KR.Chain.dec_R hT
  have hXm0 := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hZ := Zc_facts hc hb
  have hy0 : 0 < y := by linarith
  set Λ := Real.log X₀ with hΛdef
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hLs : (3.9 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  have hHb0 : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
  -- the block bounds
  set bj : ℕ → ℝ := fun j => if (2 : ℝ) ^ j * X₀ ≤ y then
    (if Lstar X₀ < Real.log (2 * (2 ^ j * X₀)) then 2 * ((Λ + (j - 1 : ℝ) * δ) ^ 4)⁻¹ else 0)
    else sigM θ X₀ ω (2 * (2 ^ j * X₀)) with hbj
  have hsigM0 : ∀ Y, 0 ≤ sigM θ X₀ ω Y := fun Y => by
    unfold sigM
    have : 0 ≤ ∑ w ∈ KR.NAll (PR θ X₀ ω) Y (Xm X₀), 2 / Vl (PR θ X₀ ω) w :=
      Finset.sum_nonneg fun w _ => div_nonneg (by norm_num) (KR.Sharp.Vl_pos _ w).le
    linarith
  have hm0 : ∀ j : ℕ, 1000 ≤ Λ + (j - 1 : ℝ) * δ := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have hb0 : ∀ j, 0 ≤ bj j := by
    intro j; simp only [hbj]
    split_ifs
    · have := hm0 j; positivity
    · exact le_rfl
    · exact hsigM0 _
  have hg0 : ∀ u : ℝ, u < X₀ → sigF θ X₀ ω r u = 0 := fun u hu => by
    unfold sigF; rw [if_neg (not_le.mpr hu)]
  have hblk : ∀ (j : ℕ) (u : ℝ), 2 ^ j * (X₀ : ℝ) ≤ u → u ≤ 2 * (2 ^ j * X₀) →
      |sigF θ X₀ ω r u| ≤ bj j := by
    intro j u h1 h2
    have hj1 : (X₀ : ℝ) ≤ 2 ^ j * X₀ := le_mul_of_one_le_left hX0 (one_le_pow₀ (by norm_num))
    have huX : (X₀ : ℝ) ≤ u := hj1.trans h1
    have hu0 : 0 < u := by linarith
    by_cases hjy : (2 : ℝ) ^ j * X₀ ≤ y
    · simp only [hbj, if_pos hjy]
      have hu2 : u ≤ 2 * (b + Queue6.Hc X₀ b) := by linarith
      obtain ⟨hm1, hm2⟩ := max_mem hr1 huX
      set w := max (r * u) X₀
      have hw2 : w ≤ 2 * (b + Queue6.Hc X₀ b) := hm2.trans hu2
      have hwl : 2 ^ j * (X₀ : ℝ) / 2 ≤ w := le_trans (by nlinarith) (le_max_left _ _)
      obtain ⟨hs1, hs2⟩ := sigR_bound hc hev hb hbt hQC hE1 hN hT hm1 hw2
      obtain ⟨hu1, hu2'⟩ := sigR_bound hc hev hb hbt hQC hE1 hN hT huX hu2
      have hmj : Real.log (2 ^ j * (X₀ : ℝ) / 2) = Λ + (j - 1 : ℝ) * δ := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hXp.ne',
          Real.log_pow]; ring
      have hlogw : Λ + (j - 1 : ℝ) * δ ≤ Real.log w := by
        rw [← hmj]; exact Real.log_le_log (by positivity) hwl
      have hlogu : Λ + (j - 1 : ℝ) * δ ≤ Real.log u := by
        rw [← hmj]; exact Real.log_le_log (by positivity) (by linarith)
      have hm := hm0 j
      have hinvw : (Real.log w ^ 4)⁻¹ ≤ ((Λ + (j - 1 : ℝ) * δ) ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlogw 4)
      have hinvu : (Real.log u ^ 4)⁻¹ ≤ ((Λ + (j - 1 : ℝ) * δ) ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlogu 4)
      unfold sigF
      rw [if_pos huX]
      split_ifs with hbig
      · calc _ ≤ |sigR θ X₀ ω w| + |sigR θ X₀ ω u| := abs_sub _ _
          _ ≤ _ := by linarith
      · push_neg at hbig
        have hu2j : Real.log u ≤ Real.log (2 * (2 ^ j * X₀)) := Real.log_le_log hu0 h2
        have hw2j : Real.log w ≤ Real.log (2 * (2 ^ j * X₀)) :=
          Real.log_le_log (by linarith) (hm2.trans h2)
        rw [hs2 (hw2j.trans hbig), hu2' (hu2j.trans hbig)]; simp
    · simp only [hbj, if_neg hjy]
      exact (abs_F_le hc hev ω (by linarith) hr1 h2).2.2
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, y < 2 ^ J * X₀ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (y / X₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨J, by rw [div_lt_iff₀ hXp] at hJ; linarith⟩
  have hZy : 2 * y / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have hR := KR.G1.log_mul_abs_rhoSh_le (P := PR θ X₀ ω) (tw := twR θ X₀ ω) hT.hbs hT.hXm
    hdec.1 hdec.2 hXmX (hXmX.trans hy) hZy (g := sigF θ X₀ ω r) hg0 hb0 hblk hJ
  -- the dyadic sum
  have hsum : ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j ≤
        4 * (1.01 / δ * ((Lstar X₀ - δ - 2 * δ) ^ 2)⁻¹) := by
    have hS := sum_term_le (L := Lstar X₀ - δ) (δ := δ) (Λ := Λ - δ) (by linarith) hδ7
      (by linarith) (by linarith) J ((Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y))
      (Finset.filter_subset _ _)
    refine le_trans (Finset.sum_le_sum (g := fun j : ℕ => 4 * (if Lstar X₀ - δ <
        (Λ - δ + j * δ) + δ then ((Λ - δ + j * δ) + δ) * ((Λ - δ + j * δ) ^ 4)⁻¹ else 0))
      fun j hj => ?_) ?_
    swap
    · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hS (by norm_num)
    have hjy := (Finset.mem_filter.mp hj).2
    have e2 : Real.log (2 * (2 ^ j * (X₀ : ℝ))) = Λ + (j + 1) * δ := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hXp.ne',
        Real.log_pow]; ring
    simp only [hbj, if_pos hjy, e2]
    have hm := hm0 j
    have e3 : Λ - δ + j * δ = Λ + (j - 1 : ℝ) * δ := by ring
    rw [e3]
    split_ifs with h1 h2 h2
    · have hpos : 0 < ((Λ + (j - 1 : ℝ) * δ) ^ 4)⁻¹ := by positivity
      have : Λ + (j + 1) * δ ≤ 2 * (Λ + (j - 1 : ℝ) * δ + δ) := by nlinarith
      nlinarith
    · exfalso; apply h2; linarith
    · simp only [mul_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) (inv_nonneg.mpr (by positivity)))
    · simp
  have hCS := BeurlingSystem.CS_le
  have hlogy : 0 ≤ Real.log y := by linarith [Real.log_le_log hXp hy]
  have hS0 : 0 ≤ ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j := Finset.sum_nonneg fun j _ => by
    have : (1 : ℝ) ≤ 2 * (2 ^ j * (X₀ : ℝ)) := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    exact mul_nonneg (Real.log_nonneg this) (hb0 j)
  have hfin : 77 * (4 * (1.01 / δ * ((Lstar X₀ - δ - 2 * δ) ^ 2)⁻¹)) ≤ 1 / 10 ^ 30 := by
    have hM : (3.9 : ℝ) * 10 ^ 18 - 3 ≤ Lstar X₀ - δ - 2 * δ := by linarith
    have hM2 : ((3.9 : ℝ) * 10 ^ 18 - 3) ^ 2 ≤ (Lstar X₀ - δ - 2 * δ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hM 2
    have hinv : ((Lstar X₀ - δ - 2 * δ) ^ 2)⁻¹ ≤ (((3.9 : ℝ) * 10 ^ 18 - 3) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hM2
    have h1 : 1.01 / δ ≤ 1.01 / 0.69 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hδ0
    have h2 : 77 * (4 * (1.01 / δ * ((Lstar X₀ - δ - 2 * δ) ^ 2)⁻¹)) ≤
        77 * (4 * (1.01 / 0.69 * (((3.9 : ℝ) * 10 ^ 18 - 3) ^ 2)⁻¹)) := by
      gcongr
    refine h2.trans ?_
    norm_num
  calc Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (sigF θ X₀ ω r)|
      ≤ _ := hR
    _ ≤ 77 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
        Real.log (2 * (2 ^ j * X₀)) * bj j := mul_le_mul_of_nonneg_right hCS hS0
    _ ≤ 77 * (4 * (1.01 / δ * ((Lstar X₀ - δ - 2 * δ) ^ 2)⁻¹)) := by linarith
    _ ≤ 1 / 10 ^ 30 := hfin

end

end BModel

end
