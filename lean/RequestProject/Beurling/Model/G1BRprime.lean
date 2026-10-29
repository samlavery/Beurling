module

public import RequestProject.Beurling.Model.G1BOth
public import RequestProject.Beurling.Model.G1BDelta
public import RequestProject.Beurling.Model.OscD2

/-!
# The `R'` change of Proposition 5.35(B), Steps 3–4: `RprimeChangeR` for every start

04f-bridge.tex, proof of Proposition 5.35 for range (B): Step 3 "Resolvable `R'_j`, smooth
change", Step 4 "Pointwise", sizes as in Step 5. We prove the named input `RprimeChangeR`
(Model/G1BOth.lean) for **every** start `y ≥ X₀` and every `0 ≤ δ ≤ 1/4`, on (H_BS) only.

The route is the pointwise bound of Step 4 for **every** oscillation `R_k` (resolvable or not),
fed into Corollary 5.9 in the dyadic form (`KR.G1.log_mul_abs_rhoSh_le`, `C_S ≤ 77`) instead of
the crude weight `∑ μ²(n)/n`:

* `|R_k'(w)| ≤ (x_k/w)^{1-θ}/(2 L_k³) ≤ (x_k/w)^{1/2}/(2 L_k³)` for `w ≥ x_k`, `L_k = log x_k`
  (`abs_deriv_oscTerm_le'`; from `|R_k'| ≤ α_k w^{θ-1}(θ + γ_k + 2)`, `α_k γ_k = κ₀ x_k^{1-θ}/L_k³`,
  eq. (ampl)), and `R_k' = 0` on `(0, x_k]`;
* on the block `[2ʲX₀, 2^{j+1}X₀]` the change `R'(max(rv, X₀)) - R'(v)` reads `R'` on
  `[2^{j-1}X₀, 2^{j+1}X₀]`, so it is `≤ 2 ∑_k 1[x_k < 2^{j+1}X₀] (2x_k/2ʲX₀)^{1/2}/(2L_k³)`;
* for each `k` the dyadic sum `∑_j log(2^{j+1}X₀) 1[x_k < 2^{j+1}X₀] (2x_k/2ʲX₀)^{1/2}` is
  `≤ 7.2 log(2x_k)` (`tele_sum`: the terms decay by `2^{-1/2}` from the first block on), so the
  `k`-th oscillation contributes `≤ 7.21/L_k² ≤ 7.21 · 4⁻ᵏ X₀⁻⁴` (`L_k ≥ 2ᵏX₀²`).

In total `log y · |∑_n c_n(y)(R'(max(z/n, X₀)) - R'(y/n))/n| ≤ 77 · 9.62 X₀⁻⁴`, well inside the
Step 5 tally `log⁻² y + 2·10⁴ Λ² X₀⁻²` (`rprimeChange_c`). No resolvability of `γ_k` is used (the
`k`-sum converges since `L_k ≥ 2ᵏX₀²`); in particular the case analysis of Step 4 (`x ≤ x_k²`,
`x_k² < x < exp(C' log² x_k)`, resolvable beyond) is not needed in this form.
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR QueueMono BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### One oscillation -/

/-- `e^{L/2} ≥ 20 L³` for `L ≥ 10⁴`. -/
lemma exp_half_ge {L : ℝ} (hL : 10000 ≤ L) : 20 * L ^ 3 ≤ Real.exp (L / 2) := by
  have h := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 4
  have e4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [e4] at h
  have hL3 : 0 < L ^ 3 := by positivity
  nlinarith

/-- **The pointwise bound of one oscillation** (Step 4, "Pointwise"; eq. (ampl)): for
`w ≥ x_k`, `|R_k'(w)| ≤ (x_k/w)^{1/2}/(2 L_k³)`. -/
lemma abs_deriv_oscTerm_le' {θ γ xk w : ℝ} (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hxk : 0 < xk) (hL : 10000 ≤ Real.log xk)
    (hγ : γ ∈ Icc (DesignedZero.heightScale θ Construction.kappa0Param xk)
      (2 * DesignedZero.heightScale θ Construction.kappa0Param xk)) (hw : xk ≤ w) :
    |deriv (Oscillation.oscTerm θ (DesignedZero.amplitudeOf θ Construction.kappa0Param γ xk) γ xk)
      w| ≤ Real.sqrt (xk / w) / (2 * Real.log xk ^ 3) := by
  set L := Real.log xk with hLdef
  have hw0 : 0 < w := lt_of_lt_of_le hxk hw
  have hL0 : 0 < L := by linarith
  set Γ := DesignedZero.heightScale θ Construction.kappa0Param xk with hΓ
  have hxkθ : 0 < xk ^ (1 - θ) := Real.rpow_pos_of_pos hxk _
  have hΓ0 : 0 < Γ := by
    rw [hΓ]; unfold DesignedZero.heightScale Construction.kappa0Param; positivity
  have hγ0 : 0 < γ := lt_of_lt_of_le hΓ0 hγ.1
  set α := DesignedZero.amplitudeOf θ Construction.kappa0Param γ xk with hα
  have hαγ : α * γ = xk ^ (1 - θ) / (4 * L ^ 3) := by
    rw [hα]; unfold DesignedZero.amplitudeOf Construction.kappa0Param
    rw [← hLdef]; field_simp
  have h2Γ : 2 * Γ = xk ^ (1 - θ) / (4 * L ^ 3) := by
    rw [hΓ]; unfold DesignedZero.heightScale Construction.kappa0Param; rw [← hLdef]
    field_simp
  have hα0 : 0 < α := by
    rw [hα]; unfold DesignedZero.amplitudeOf Construction.kappa0Param; positivity
  have hα2 : α ≤ 2 := by
    have : α * γ ≤ 2 * γ := by rw [hαγ, ← h2Γ]; nlinarith [hγ.1]
    nlinarith
  have hb := Oscillation.abs_deriv_oscTerm_le (θ := θ) (α := α) (γ := γ) hw0 hxk
  rw [abs_of_pos hα0, abs_of_nonneg (show (0 : ℝ) ≤ θ by linarith), abs_of_pos hγ0] at hb
  -- `x_k^{1-θ} ≥ 20 L³`
  have hbig : 20 * L ^ 3 ≤ xk ^ (1 - θ) := by
    have h1 := exp_half_ge hL
    have h2 : Real.exp (L / 2) ≤ xk ^ (1 - θ) := by
      rw [Real.rpow_def_of_pos hxk, ← hLdef]
      exact Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - θ by linarith) hL0.le])
    linarith
  have hwθ : 0 ≤ w ^ (θ - 1) := Real.rpow_nonneg hw0.le _
  have key : α * w ^ (θ - 1) * (θ + γ + 2) ≤ w ^ (θ - 1) * xk ^ (1 - θ) / (2 * L ^ 3) := by
    have e : α * w ^ (θ - 1) * (θ + γ + 2) = w ^ (θ - 1) * (α * γ + α * (θ + 2)) := by ring
    rw [e, hαγ]
    have h5 : α * (θ + 2) ≤ xk ^ (1 - θ) / (4 * L ^ 3) := by
      have h5' : α * (θ + 2) ≤ 5 := by nlinarith
      have hL3 : 0 ≤ L ^ 3 := by positivity
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h5' hL3]
    have : xk ^ (1 - θ) / (4 * L ^ 3) + α * (θ + 2) ≤ xk ^ (1 - θ) / (2 * L ^ 3) := by
      have : xk ^ (1 - θ) / (2 * L ^ 3) = 2 * (xk ^ (1 - θ) / (4 * L ^ 3)) := by
        field_simp; ring
      linarith
    calc w ^ (θ - 1) * (xk ^ (1 - θ) / (4 * L ^ 3) + α * (θ + 2))
        ≤ w ^ (θ - 1) * (xk ^ (1 - θ) / (2 * L ^ 3)) := mul_le_mul_of_nonneg_left this hwθ
      _ = _ := by ring
  have hratio : w ^ (θ - 1) * xk ^ (1 - θ) = (xk / w) ^ (1 - θ) := by
    rw [Real.div_rpow hxk.le hw0.le, show θ - 1 = -(1 - θ) by ring, Real.rpow_neg hw0.le]
    field_simp
  have hq : (xk / w) ^ (1 - θ) ≤ Real.sqrt (xk / w) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge (div_pos hxk hw0) ((div_le_one hw0).mpr hw)
      (by linarith)
  refine hb.trans (key.trans ?_)
  rw [hratio]
  exact div_le_div_of_nonneg_right hq (by positivity)

/-! ### The dyadic telescoping -/

/-- **The dyadic sum of one oscillation**: for `x ≥ 2X`,
`∑_{j<J} 1[x < 2^{j+1}X] log(2^{j+1}X) (2x/2ʲX)^{1/2} ≤ 7.2 log(2x)`. -/
lemma tele_sum {X x : ℝ} (hX : 0 < X) (hlX : 40 ≤ Real.log (2 * X)) (hx : 2 * X ≤ x) (J : ℕ) :
    ∑ j ∈ Finset.range J, (if x < 2 * (2 ^ j * X) then
      Real.log (2 * (2 ^ j * X)) * Real.sqrt (2 * x / (2 ^ j * X)) else 0) ≤
      7.2 * Real.log (2 * x) := by
  set t : ℕ → ℝ := fun j => if x < 2 * (2 ^ j * X) then
    Real.log (2 * (2 ^ j * X)) * Real.sqrt (2 * x / (2 ^ j * X)) else 0 with ht
  have hx0 : 0 < x := by linarith
  have h2X : 41 ≤ 2 * X := by
    have := Real.add_one_le_exp (Real.log (2 * X))
    rw [Real.exp_log (by linarith)] at this; linarith
  have hlx : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hs : ∀ j : ℕ, 0 < 2 ^ j * X := fun j => by positivity
  have hl : ∀ j : ℕ, 40 ≤ Real.log (2 * (2 ^ j * X)) := fun j =>
    hlX.trans (Real.log_le_log (by linarith) (by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); nlinarith))
  have ht0 : ∀ j, 0 ≤ t j := fun j => by
    simp only [ht]; split_ifs
    · exact mul_nonneg (by linarith [hl j]) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hmono : ∀ i j : ℕ, i ≤ j → 2 * (2 ^ i * X) ≤ 2 * (2 ^ j * X) := fun i j hij => by
    have : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hij
    nlinarith
  have hs2 : (1.4142 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have key : ∀ J : ℕ, ∑ j ∈ Finset.range J, t j + 3.6 * t J ≤ 7.2 * Real.log (2 * x) := by
    intro J
    induction J with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, ht, pow_zero, one_mul]
      rw [if_neg (by linarith)]; linarith
    | succ J ih =>
      rw [Finset.sum_range_succ]
      have e2 : 2 ^ (J + 1) * X = 2 * (2 ^ J * X) := by ring
      by_cases hc : x < 2 * (2 ^ J * X)
      · -- both blocks see `x_k`
        have hc' : x < 2 * (2 ^ (J + 1) * X) := lt_of_lt_of_le hc (hmono J (J + 1) (by omega))
        have hJ : t J = Real.log (2 * (2 ^ J * X)) * (Real.sqrt 2 *
            Real.sqrt (x / (2 ^ J * X))) := by
          simp only [ht, if_pos hc]
          rw [← Real.sqrt_mul (by norm_num), mul_div_assoc]
        have hJ1 : t (J + 1) = (Real.log (2 * (2 ^ J * X)) + Real.log 2) *
            Real.sqrt (x / (2 ^ J * X)) := by
          simp only [ht, if_pos hc']
          rw [e2, Real.log_mul (by norm_num) (by positivity), add_comm]
          congr 2
          field_simp
        have hb : 0 ≤ Real.sqrt (x / (2 ^ J * X)) := Real.sqrt_nonneg _
        have hl2 := Real.log_two_lt_d9
        have hlJ := hl J
        have : t J + 3.6 * t (J + 1) ≤ 3.6 * t J := by
          rw [hJ, hJ1]
          have : Real.log (2 * (2 ^ J * X)) + 3.6 * (Real.log (2 * (2 ^ J * X)) + Real.log 2) ≤
              3.6 * (Real.log (2 * (2 ^ J * X)) * Real.sqrt 2) - 0 := by nlinarith
          nlinarith [mul_nonneg hb (by linarith : (0 : ℝ) ≤ Real.log (2 * (2 ^ J * X)))]
        linarith
      · push_neg at hc
        by_cases hc' : x < 2 * (2 ^ (J + 1) * X)
        · -- the first block that sees `x_k`
          have hz : ∑ j ∈ Finset.range J, t j = 0 := Finset.sum_eq_zero fun j hj => by
            simp only [ht]
            rw [if_neg (not_lt.mpr (le_trans (hmono j J (Finset.mem_range.mp hj).le) hc))]
          have htJ : t J = 0 := by simp only [ht]; rw [if_neg (not_lt.mpr hc)]
          have hJ1 : t (J + 1) ≤ Real.log (2 * x) * 2 := by
            simp only [ht, if_pos hc']
            have h1 : Real.log (2 * (2 ^ (J + 1) * X)) ≤ Real.log (2 * x) :=
              Real.log_le_log (by positivity) (by rw [e2]; linarith)
            have h2 : Real.sqrt (2 * x / (2 ^ (J + 1) * X)) ≤ 2 := by
              rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (hs _)]
              rw [e2]; linarith
            exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hlx
          rw [hz, htJ]; linarith
        · have htJ1 : t (J + 1) = 0 := by simp only [ht]; rw [if_neg hc']
          rw [htJ1]
          have := ht0 J
          linarith
  have := key J
  have := ht0 J
  linarith

/-! ### The block bound -/

variable (X₀) in
/-- The bound of `|R_k'|` on the block `[2^{j-1}X₀, 2^{j+1}X₀]`:
`1[x_k < 2^{j+1}X₀] (2x_k/2ʲX₀)^{1/2}/(2 L_k³)`. -/
noncomputable def βk (j k : ℕ) : ℝ :=
  if switchOn (X₀ : ℝ) k < 2 * (2 ^ j * (X₀ : ℝ)) then
    Real.sqrt (2 * switchOn (X₀ : ℝ) k / (2 ^ j * X₀)) / (2 * Real.log (switchOn (X₀ : ℝ) k) ^ 3)
  else 0

variable (X₀) in
/-- The number of oscillations that can be active on the block `j`. -/
noncomputable def Kb (j : ℕ) : ℕ := ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ + 1

lemma βk_nonneg (j k : ℕ) : 0 ≤ βk X₀ j k := by
  unfold βk; split_ifs
  · have h := log_switchOn_ge (X₀ : ℝ) k
    have : 0 ≤ Real.log (switchOn (X₀ : ℝ) k) := le_trans (by positivity) h
    exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  · exact le_rfl

section Blk

variable (hc : Cond θ X₀)
include hc

/-- **`|R'(w)| ≤ ∑_{k < K_j} β_k(j)`** on `[2^{j-1}X₀, 2^{j+1}X₀] ∩ [X₀, ∞)` (Step 4,
"Pointwise", for every oscillation; `R_k' = 0` on `(0, x_k]`). -/
theorem abs_RpR_le_blk (ω : JitterΩ) (j : ℕ) {w : ℝ} (hw1 : 2 ^ j * (X₀ : ℝ) / 2 ≤ w)
    (hw2 : w ≤ 2 * (2 ^ j * X₀)) (hwX : (X₀ : ℝ) ≤ w) :
    |RpR θ X₀ ω w| ≤ ∑ k ∈ Finset.range (Kb X₀ j), βk X₀ j k := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hw0 : 0 < w := by linarith
  have hwK : w < switchOn (X₀ : ℝ) (Kb X₀ j) := by
    have h1 := nat_lt_switchOn hX1.le (Kb X₀ j)
    have h2 : 2 * (2 ^ j * (X₀ : ℝ)) ≤ ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ := Nat.le_ceil _
    have h3 : ((Kb X₀ j : ℕ) : ℝ) = ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ + 1 := by
      unfold Kb; push_cast; ring
    linarith
  unfold RpR
  rw [deriv_osc_eq_sum _ _ _ hw0 hwK]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hxk := switchOn_pos (X₀ : ℝ) k
  rw [← deriv_oscTerm_eq hw0 hxk]
  rcases le_or_gt w (switchOn (X₀ : ℝ) k) with h | h
  · rw [deriv_oscTerm_of_le hw0 h, abs_zero]; exact βk_nonneg j k
  · have hLk := log_switchOn_ge (X₀ : ℝ) k
    have hL : 10000 ≤ Real.log (switchOn (X₀ : ℝ) k) := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hb := abs_deriv_oscTerm_le' hc.hθ.1 (by linarith [hc.hθ.2]) hxk hL
      (gammaD_range (θ := θ) hX (DF θ X₀ ω) k) h.le
    refine hb.trans ?_
    unfold βk
    rw [if_pos (lt_of_lt_of_le h hw2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hw0 (by positivity)]
    nlinarith

end Blk

/-! ### The `R'` change -/

section Main

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 4000000 in
/-- **`RprimeChangeR` at every start** (04f-bridge.tex, Proposition 5.35(B), Steps 3–4, sizes of
Step 5): on (H_BS) on `[1, Zc b]`, for `X₀ ≤ y ≤ b + H(b)` and `0 ≤ δ ≤ 1/4`,
`log y · |∑_n c_n(y)(R'(max(z/n, X₀)) - R'(y/n))/n| ≤ 77 · 9.7 X₀⁻⁴` for `z ∈ J`, which is
within `2 log⁻² y + 4·10⁴ Λ² X₀⁻²`. -/
theorem rprimeChange_all (ω : JitterΩ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4) :
    RprimeChangeR θ X₀ ω y δ := by
  classical
  intro z hz
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hdec := KR.Chain.dec_R hT
  have hXm0 := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hZ := Zc_facts hc hb
  have hy0 : 0 < y := by linarith
  set r := z / y with hr
  have hr0 : 1 / 2 ≤ r := by
    rw [hr, le_div_iff₀ hy0]; nlinarith [hz.1]
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hy0]; nlinarith [hz.2]
  set bj : ℕ → ℝ := fun j => 2 * ∑ k ∈ Finset.range (Kb X₀ j), βk X₀ j k with hbj
  have hb0 : ∀ j, 0 ≤ bj j := fun j =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => βk_nonneg j k)
  have hg0 : ∀ u : ℝ, u < X₀ → oscF θ X₀ ω r u = 0 := fun u hu => by
    unfold oscF; rw [if_neg (not_le.mpr hu)]
  have hblk : ∀ (j : ℕ) (u : ℝ), 2 ^ j * (X₀ : ℝ) ≤ u → u ≤ 2 * (2 ^ j * X₀) →
      |oscF θ X₀ ω r u| ≤ bj j := by
    intro j u h1 h2
    have hj1 : (X₀ : ℝ) ≤ 2 ^ j * X₀ := le_mul_of_one_le_left hX0 (one_le_pow₀ (by norm_num))
    have huX : (X₀ : ℝ) ≤ u := hj1.trans h1
    have hu0 : 0 < u := by linarith
    obtain ⟨hm1, hm2⟩ := max_mem hr1 huX
    unfold oscF
    rw [if_pos huX]
    have hA := abs_RpR_le_blk hc ω j (w := max (r * u) X₀)
      (le_trans (by nlinarith) (le_max_left _ _)) (hm2.trans h2) hm1
    have hB := abs_RpR_le_blk hc ω j (w := u) (by linarith) h2 huX
    calc _ ≤ |RpR θ X₀ ω (max (r * u) X₀)| + |RpR θ X₀ ω u| := abs_sub _ _
      _ ≤ bj j := by simp only [hbj]; linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, y < 2 ^ J * X₀ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (y / X₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨J, by rw [div_lt_iff₀ hXp] at hJ; linarith⟩
  have hZy : 2 * y / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]
    have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
    linarith
  have hR := KR.G1.log_mul_abs_rhoSh_le (P := PR θ X₀ ω) (tw := twR θ X₀ ω) hT.hbs hT.hXm
    hdec.1 hdec.2 hXmX (hXmX.trans hy) hZy (g := oscF θ X₀ ω r) hg0 hb0 hblk hJ
  -- the dyadic sum
  have hlw : ∀ j : ℕ, 0 ≤ Real.log (2 * (2 ^ j * (X₀ : ℝ))) := fun j =>
    Real.log_nonneg (by have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); nlinarith)
  have hlX : 40 ≤ Real.log (2 * (X₀ : ℝ)) := by
    have := Real.log_le_log hXp (show (X₀ : ℝ) ≤ 2 * X₀ by linarith); linarith
  have hS1 : ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j ≤
      ∑ j ∈ Finset.range J, Real.log (2 * (2 ^ j * X₀)) * bj j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => mul_nonneg (hlw j) (hb0 j)
  have hS2 : ∑ j ∈ Finset.range J, Real.log (2 * (2 ^ j * X₀)) * bj j ≤
      2 * ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ Finset.range J,
        Real.log (2 * (2 ^ j * X₀)) * βk X₀ j k := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [hbj]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have hsub : Finset.range (Kb X₀ j) ⊆ Finset.range (Kb X₀ J) := by
      apply Finset.range_subset_range.mpr
      unfold Kb
      have : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num)
        (Finset.mem_range.mp hj).le
      have := Nat.ceil_mono (show 2 * (2 ^ j * (X₀ : ℝ)) ≤ 2 * (2 ^ J * X₀) by nlinarith)
      omega
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun k _ _ => by have := βk_nonneg (X₀ := X₀) j k; have := hlw j; positivity)
    refine Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k : ℕ, ∑ j ∈ Finset.range J, Real.log (2 * (2 ^ j * X₀)) * βk X₀ j k ≤
      3.61 * (1 / 4) ^ k / (X₀ : ℝ) ^ 4 := by
    intro k
    set xk := switchOn (X₀ : ℝ) k with hxk
    set L := Real.log xk with hL
    have hLk := log_switchOn_ge (X₀ : ℝ) k
    have hxk0 := switchOn_pos (X₀ : ℝ) k
    have hL1 : 10000 ≤ L := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); nlinarith
    have h2x : 2 * (X₀ : ℝ) ≤ xk := by
      have := Real.add_one_le_exp L
      rw [hL, Real.exp_log hxk0] at this
      have : (X₀ : ℝ) ≤ X₀ ^ 2 := by nlinarith
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have e : ∀ j : ℕ, Real.log (2 * (2 ^ j * X₀)) * βk X₀ j k =
        (if xk < 2 * (2 ^ j * X₀) then
          Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) /
          (2 * L ^ 3) := by
      intro j; unfold βk; split_ifs <;> ring
    simp_rw [e]
    rw [← Finset.sum_div]
    have ht := tele_sum hXp hlX h2x J
    have hL3 : 0 < 2 * L ^ 3 := by positivity
    have hl2 : Real.log (2 * xk) ≤ L + 1 := by
      rw [Real.log_mul (by norm_num) hxk0.ne']; linarith [Real.log_two_lt_d9]
    have h4 : (4 : ℝ) ^ k * (X₀ : ℝ) ^ 4 ≤ L ^ 2 := by
      have h0 : (0 : ℝ) ≤ 2 ^ k * (X₀ : ℝ) ^ 2 := by positivity
      have := pow_le_pow_left₀ h0 hLk 2
      calc (4 : ℝ) ^ k * (X₀ : ℝ) ^ 4 = (2 ^ k * (X₀ : ℝ) ^ 2) ^ 2 := by
            rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
              mul_comm 2 k]
        _ ≤ _ := this
    have hq : (1 / 4 : ℝ) ^ k / (X₀ : ℝ) ^ 4 = 1 / ((4 : ℝ) ^ k * (X₀ : ℝ) ^ 4) := by
      rw [one_div_pow]; field_simp
    rw [mul_div_assoc, hq, div_le_iff₀ hL3]
    have h7 : 7.2 * Real.log (2 * xk) ≤ 7.22 * L := by linarith
    have hX4 : 0 < (4 : ℝ) ^ k * (X₀ : ℝ) ^ 4 := by positivity
    have h8 : 3.61 * (1 / ((4 : ℝ) ^ k * (X₀ : ℝ) ^ 4)) * (2 * L ^ 3) ≥ 7.22 * L := by
      rw [ge_iff_le, show 3.61 * (1 / ((4 : ℝ) ^ k * (X₀ : ℝ) ^ 4)) * (2 * L ^ 3) =
        7.22 * L * (L ^ 2 / ((4 : ℝ) ^ k * (X₀ : ℝ) ^ 4)) by field_simp; ring]
      have : 1 ≤ L ^ 2 / ((4 : ℝ) ^ k * (X₀ : ℝ) ^ 4) := by rw [le_div_iff₀ hX4]; linarith
      nlinarith
    linarith
  have hS3 : 2 * ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ Finset.range J,
      Real.log (2 * (2 ^ j * X₀)) * βk X₀ j k ≤ 9.7 / (X₀ : ℝ) ^ 4 := by
    have h1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.range (Kb X₀ J)) => hk k
    have h2 : ∑ k ∈ Finset.range (Kb X₀ J), 3.61 * (1 / 4 : ℝ) ^ k / (X₀ : ℝ) ^ 4 =
        3.61 / (X₀ : ℝ) ^ 4 * ∑ k ∈ Finset.range (Kb X₀ J), (1 / 4 : ℝ) ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have h3 := Construction.sum_inv_four_pow_le (Kb X₀ J)
    have h4 : 0 ≤ 3.61 / (X₀ : ℝ) ^ 4 := by positivity
    have h5 : 2 * (3.61 / (X₀ : ℝ) ^ 4 * (4 / 3)) ≤ 9.7 / (X₀ : ℝ) ^ 4 := by
      rw [show 2 * (3.61 / (X₀ : ℝ) ^ 4 * (4 / 3)) = (2 * 3.61 * 4 / 3) / (X₀ : ℝ) ^ 4 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hCS := BeurlingSystem.CS_le
  have hS0 : 0 ≤ ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hlw j) (hb0 j)
  have hfin : 77 * (9.7 / (X₀ : ℝ) ^ 4) ≤
      2 / Real.log y ^ 2 + 4 * 10 ^ 4 * Real.log X₀ ^ 2 * (X₀ : ℝ) ^ (-2 : ℝ) := by
    have hly : 0 ≤ 2 / Real.log y ^ 2 := by positivity
    rw [Real.rpow_neg hX0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hX2 : (1 : ℝ) ≤ (X₀ : ℝ) ^ 2 := by nlinarith
    have hΛ : (1 : ℝ) ≤ Real.log X₀ ^ 2 := by nlinarith
    have h4 : (X₀ : ℝ) ^ 2 ≤ (X₀ : ℝ) ^ 4 := by nlinarith
    have : 77 * (9.7 / (X₀ : ℝ) ^ 4) ≤ 4 * 10 ^ 4 * Real.log X₀ ^ 2 * ((X₀ : ℝ) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul hΛ h4 (by positivity) (by positivity)]
    linarith
  calc Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y))|
      ≤ _ := hR
    _ ≤ 77 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
        Real.log (2 * (2 ^ j * X₀)) * bj j := mul_le_mul_of_nonneg_right hCS hS0
    _ ≤ 77 * (9.7 / (X₀ : ℝ) ^ 4) := by linarith
    _ ≤ _ := hfin

/-- **`RprimeChangeR` at the window parameter `δ = deltaB`** of the proof of Proposition
5.35(B), at every start `X₀ ≤ y ≤ b + H(b)` (in particular on range (B)), on (H_BS) on
`[1, Zc b]`. -/
theorem rprimeChange_c (ω : JitterΩ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b) :
    RprimeChangeR θ X₀ ω y (deltaB θ X₀ ω y) := by
  have hX65 := KR.WidthReal.X0_ge hc.hX (X₀ := X₀)
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have h4 : (4 : ℝ) ≤ (X₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) hX0.le]; linarith
  have hq : (X₀ : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 4 := by
    rw [show (-(1 / 2) : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hX0.le]
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 4) h4
    norm_num at this ⊢
    exact this
  exact rprimeChange_all hc ω hb hT hy hyb (deltaB_pos hc ω hy).le
    ((deltaB_le ω y).trans hq)

end Main

end BModel

end
