module

public import RequestProject.Beurling.Model.G1BOth
public import RequestProject.Beurling.Model.G1BDelta
public import RequestProject.Beurling.Model.OscD2

/-!
# The `R'` change of Proposition 5.35(B), Steps 3–4: `RprimeChangeR`

04f-bridge.tex, proof of Proposition 5.35 for range (B): Step 3 "Resolvable `R'_j`, smooth
change", Step 4 "Pointwise", sizes as in Step 5. We prove the named input `RprimeChangeR`
(Model/G1BOth.lean) at every start `y ≥ X₀` for `0 ≤ δ ≤ 1/4` with `δ γ_j² ≤ log⁻⁴ y` for every
resolvable `γ_j` (`δ = deltaB` is such), on (H_BS) only. The amplitude is constant,
`κ'_k = κ₀ = X₀⁻¹` (eq. (ampl)), so the pointwise bound of Step 4 is used only for the **current**
oscillation; the old ones are resolvable and change smoothly (Step 3). Both are fed into
Corollary 5.9 in the dyadic form (`KR.G1.log_mul_abs_rhoSh_le`, `C_S ≤ 77`):

* **old** `R_i` (`x_{i+1} < 2y`): `γ_i ≤ x_i < log 2y ≤ Γ(y)`, so `γ_i` is resolvable
  (`gammaD_res_of_old`) and, by the mean value theorem and `|R_i''(w)| ≤ 2 w^{θ-2}·22 γ_i²`
  (`abs_oscD2_le`), the change of `R_i'` on the block `[2ʲX₀, 2^{j+1}X₀]` is
  `≤ 352 δ γ_i² (2ʲX₀/2)^{θ-1} ≤ 352 (2x_i/2ʲX₀)^{1/2} x_i^{-1/2} log⁻⁴ y` (`βo`); summed over
  the blocks (`tele_sum`) and over `i` this is `≤ 2.7·10⁶ X₀⁻⁶ log⁻⁴ y`;
* **current** `R_i` (`x_i < 2y ≤ x_{i+1}`; at most one, `sum_window_le'`): Lemma G1,
  `|R_i'(w)| ≤ 2κ₀ (x_i/w)^{1/2}/L_i` (`abs_deriv_oscTerm_designed`), so on the block the change
  is `≤ 4κ₀ (2x_i/2ʲX₀)^{1/2}/L_i` (`βk`), and the dyadic sum is `≤ 28.9 κ₀`
  (`tele_sum`: the terms decay by `2^{-1/2}` from the first block on).

In total `log y · |∑_n c_n(y)(R'(max(z/n, X₀)) - R'(y/n))/n| ≤ 77 (28.9 κ₀ + 2.7·10⁶ X₀⁻⁶ log⁻⁴ y)
≤ 2 log⁻² y + 3000 κ₀` (`rprimeChange_all`).
-/

@[expose] public section

open Set Real Finset Construction CaplLink Queue6 KR QueueMono BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

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

/-! ### The windows -/

/-- At most one switch-on window `(x_k, x_{k+1}]` contains `x`. -/
lemma sum_window_le' (X x A : ℝ) (hA : 0 ≤ A) (K : ℕ) :
    ∑ k ∈ Finset.range K, (if switchOn X k < x ∧ x ≤ switchOn X (k + 1) then A else 0) ≤ A := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range K).filter (fun k => switchOn X k < x ∧
      x ≤ switchOn X (k + 1))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := switchOn_mono X (show a + 1 ≤ b by omega)
      linarith [ha.2.2, hb.2.1]
    · have := switchOn_mono X (show b + 1 ≤ a by omega)
      linarith [hb.2.2, ha.2.1]
  have hc' : (((Finset.range K).filter (fun k => switchOn X k < x ∧
      x ≤ switchOn X (k + 1))).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

/-! ### The block bounds -/

variable (θ X₀) in
/-- The pointwise bound of the current `R_k'` on the block `[2^{j-1}X₀, 2^{j+1}X₀]` (Step 4,
"Pointwise"; Lemma G1): `1[x_k < 2^{j+1}X₀] 2κ₀ (2x_k/2ʲX₀)^{1/2}/L_k`, `κ₀ = X₀⁻¹`. -/
noncomputable def βk (j k : ℕ) : ℝ :=
  if switchOn (swS θ X₀) k < 2 * (2 ^ j * (X₀ : ℝ)) then
    2 * Real.sqrt (2 * switchOn (swS θ X₀) k / (2 ^ j * X₀)) /
      ((X₀ : ℝ) * Real.log (switchOn (swS θ X₀) k))
  else 0

variable (θ X₀) in
/-- The smooth-change bound of an old (resolvable) `R_k'` on the block `[2ʲX₀, 2^{j+1}X₀]`
(Step 3, "Resolvable `R'_j`"): `1[x_k < 2^{j+1}X₀] 352 (2x_k/2ʲX₀)^{1/2} x_k^{-1/2} log⁻⁴ y`. -/
noncomputable def βo (y : ℝ) (j k : ℕ) : ℝ :=
  if switchOn (swS θ X₀) k < 2 * (2 ^ j * (X₀ : ℝ)) then
    352 * Real.sqrt (2 * switchOn (swS θ X₀) k / (2 ^ j * X₀)) /
      (Real.sqrt (switchOn (swS θ X₀) k) * Real.log y ^ 4)
  else 0

variable (θ X₀) in
/-- The pointwise bound of the switched-off part (design `θ = 0`, switched on at
`y_k = x_k max(x_k, 1)`) of `R_k'` on the block `j`: as `βk`, with the indicator `y_k < 2^{j+1}X₀`. -/
noncomputable def βkB (j k : ℕ) : ℝ :=
  if switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1 < 2 * (2 ^ j * (X₀ : ℝ)) then
    2 * Real.sqrt (2 * switchOn (swS θ X₀) k / (2 ^ j * X₀)) /
      ((X₀ : ℝ) * Real.log (switchOn (swS θ X₀) k))
  else 0

variable (θ) in
/-- `1` for the design `θ = 0` (which has a switched-off part), `0` otherwise. -/
noncomputable def offI : ℝ := if θ = 0 then 1 else 0

lemma offI_mem : 0 ≤ offI θ ∧ offI θ ≤ 1 := by unfold offI; split_ifs <;> norm_num

variable (X₀) in
/-- The number of oscillations that can be active on the block `j`. -/
noncomputable def Kb (j : ℕ) : ℕ := ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ + 1

lemma βk_nonneg (j k : ℕ) : 0 ≤ βk θ X₀ j k := by
  unfold βk; split_ifs
  · have h := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
    have : 0 ≤ Real.log (switchOn (swS θ X₀) k) := le_trans (by positivity) h
    exact div_nonneg (by positivity) (by positivity)
  · exact le_rfl

lemma βkB_nonneg (j k : ℕ) : 0 ≤ βkB θ X₀ j k := by
  unfold βkB; split_ifs
  · have h := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
    have : 0 ≤ Real.log (switchOn (swS θ X₀) k) := le_trans (by positivity) h
    exact div_nonneg (by positivity) (by positivity)
  · exact le_rfl

lemma βo_nonneg (y : ℝ) (j k : ℕ) : 0 ≤ βo θ X₀ y j k := by
  unfold βo; split_ifs
  · exact div_nonneg (by positivity) (by positivity)
  · exact le_rfl

/-- `Γ_k ≥ 1` for the designed heights. -/
lemma one_le_heightScale_switchOn {θ X S : ℝ} (hX : 10 ≤ X) (hXS : X ≤ S) (k : ℕ)
    (hθ : thK θ (switchOn S k) ≤ 1 / 2) :
    1 ≤ DesignedZero.heightScale (thK θ (switchOn S k)) (kappa0Param X) (switchOn S k) := by
  set xk := switchOn S k
  set θ := thK θ xk with hθdef
  set L := Real.log xk with hLdef
  have hLk : 2 ^ k * X ^ 2 ≤ L := log_switchOn_ge_of (by linarith) hXS k
  have hX2 : X ^ 2 ≤ L :=
    le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))) hLk
  have hL : 100 ≤ L := by nlinarith
  have hxk0 : 0 < xk := switchOn_pos S k
  have hxθ : Real.exp (L / 2) ≤ xk ^ (1 - θ) := by
    rw [Real.rpow_def_of_pos hxk0, ← hLdef]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h3 := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 3
  norm_num [Nat.factorial] at h3
  unfold DesignedZero.heightScale kappa0Param
  rw [← hLdef, le_div_iff₀ (by positivity)]
  have hXL : 96 * X ≤ L ^ 2 := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have : 2 * X * L ≤ xk ^ (1 - θ) := by nlinarith [mul_le_mul_of_nonneg_left hXL hL0]
  have hX0 : 0 < X := by linarith
  rw [show 1 / X * xk ^ (1 - θ) = xk ^ (1 - θ) / X by ring, le_div_iff₀ hX0] at *
  nlinarith

/-- `R_k' = 0` on `(0, x_k]`, in the form `oscD`. -/
lemma oscD_eq_zero_of_le' {α γ xk w : ℝ} (hw : 0 < w) (hxk : 0 < xk) (h : w ≤ xk) :
    oscD θ α γ xk w = 0 := by
  rw [← deriv_oscTerm_eq hw hxk, deriv_oscTerm_of_le hw h]

section Blk

variable (hc : Cond θ X₀)
include hc

/-- **The pointwise bound** (Step 4, Lemma G1): `|R_k'(w)| ≤ β_k(j)` on
`[2^{j-1}X₀, 2^{j+1}X₀]`, for the oscillation with the designed amplitude switched on at any
`y ≥ x_k`. -/
lemma abs_oscD_le_βk (ω : JitterΩ) (j k : ℕ) {yS : ℝ} (hyS : switchOn (swS θ X₀) k ≤ yS)
    {w : ℝ} (hw1 : 2 ^ j * (X₀ : ℝ) / 2 ≤ w) (hw2 : w ≤ 2 * (2 ^ j * X₀)) :
    |oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k) (gammaD θ X₀ (DF θ X₀ ω) k)
      yS w| ≤ βk θ X₀ j k := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw1
  have hxk := switchOn_pos (swS θ X₀) k
  have hyS0 : 0 < yS := lt_of_lt_of_le hxk hyS
  have ht := hc.thK_mem k
  rcases le_or_gt w yS with h | h
  · rw [oscD_eq_zero_of_le' hw0 hyS0 h, abs_zero]; exact βk_nonneg j k
  · have h' : switchOn (swS θ X₀) k < w := lt_of_le_of_lt hyS h
    have hb := abs_deriv_oscTerm_designed ht.1.le (by linarith [ht.2]) (by linarith)
        (le_swS θ _) k (gammaD_range (θ := θ) hX (DF θ X₀ ω) k) h'.le hyS0
    rw [deriv_oscTerm_eq hw0 hyS0] at hb
    refine hb.trans ?_
    unfold βk
    rw [if_pos (lt_of_lt_of_le h' hw2)]
    have hLk := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
    have hL : 0 < Real.log (switchOn (swS θ X₀) k) := lt_of_lt_of_le (by positivity) hLk
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hw0 (by positivity)]
    nlinarith

/-- **The pointwise bound of the switched-off part**: `|R_{k,off}'(w)| ≤ βkB_k(j)` on
`[2^{j-1}X₀, 2^{j+1}X₀]`. -/
lemma abs_oscD_le_βkB (ω : JitterΩ) (j k : ℕ) {w : ℝ} (hw1 : 2 ^ j * (X₀ : ℝ) / 2 ≤ w)
    (hw2 : w ≤ 2 * (2 ^ j * X₀)) :
    |oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k) (gammaD θ X₀ (DF θ X₀ ω) k)
      (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1) w| ≤ βkB θ X₀ j k := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw1
  have hxk := switchOn_pos (swS θ X₀) k
  have hyS : switchOn (swS θ X₀) k ≤ switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1 :=
    le_mul_of_one_le_right hxk.le (le_max_right _ _)
  have hyS0 := lt_of_lt_of_le hxk hyS
  have ht := hc.thK_mem k
  rcases le_or_gt w (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1) with h | h
  · rw [oscD_eq_zero_of_le' hw0 hyS0 h, abs_zero]; exact βkB_nonneg j k
  · have h' : switchOn (swS θ X₀) k < w := lt_of_le_of_lt hyS h
    have hb := abs_deriv_oscTerm_designed ht.1.le (by linarith [ht.2]) (by linarith)
        (le_swS θ _) k (gammaD_range (θ := θ) hX (DF θ X₀ ω) k) h'.le hyS0
    rw [deriv_oscTerm_eq hw0 hyS0] at hb
    refine hb.trans ?_
    unfold βkB
    rw [if_pos (lt_of_lt_of_le h hw2)]
    have hLk := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
    have hL : 0 < Real.log (switchOn (swS θ X₀) k) := lt_of_lt_of_le (by positivity) hLk
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hw0 (by positivity)]
    nlinarith

/-- **The smooth change of a resolvable `R_k'`** (Step 3): for `u ∈ [2ʲX₀, 2^{j+1}X₀]`,
`1/2 ≤ r ≤ 1`, `1 - r ≤ 2δ` and `δ γ_k² ≤ log⁻⁴ y`,
`|R_k'(max(ru, X₀)) - R_k'(u)| ≤ βo_k(j)`. -/
lemma abs_oscD_sub_le_βo (ω : JitterΩ) {y δ r : ℝ} (j k : ℕ) {yS : ℝ}
    (hyS : switchOn (swS θ X₀) k ≤ yS)
    (hres : δ * gammaD θ X₀ (DF θ X₀ ω) k ^ 2 ≤ 1 / Real.log y ^ 4) (hr0 : 1 / 2 ≤ r)
    (hr1 : r ≤ 1) (hrδ : 1 - r ≤ 2 * δ) {u : ℝ} (hu1 : 2 ^ j * (X₀ : ℝ) ≤ u)
    (hu2 : u ≤ 2 * (2 ^ j * X₀)) :
    |oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) yS (max (r * u) X₀) -
      oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) yS u| ≤
      βo θ X₀ y j k := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hj1 : (X₀ : ℝ) ≤ 2 ^ j * X₀ := le_mul_of_one_le_left hX0 (one_le_pow₀ (by norm_num))
  have huX : (X₀ : ℝ) ≤ u := hj1.trans hu1
  have hu0 : 0 < u := by linarith
  obtain ⟨hm1, hm2⟩ := max_mem hr1 huX
  set w₁ := max (r * u) (X₀ : ℝ) with hw₁
  have hw0 : 0 < w₁ := by linarith
  have hxk := switchOn_pos (swS θ X₀) k
  set xk := switchOn (swS θ X₀) k with hxkdef
  set g := gammaD θ X₀ (DF θ X₀ ω) k with hg
  set α := alphaD θ X₀ (DF θ X₀ ω) k with hα
  set t := thK θ xk with htdef
  have hyS0 : 0 < yS := lt_of_lt_of_le hxk hyS
  rcases le_or_gt u yS with h | h
  · rw [oscD_eq_zero_of_le' hw0 hyS0 (hm2.trans h), oscD_eq_zero_of_le' hu0 hyS0 h, sub_zero,
      abs_zero]
    exact βo_nonneg y j k
  replace h : xk < u := lt_of_le_of_lt hyS h
  have hγr := gammaD_range (θ := θ) hX (DF θ X₀ ω) k
  have hγ1 : 1 ≤ g := le_trans (one_le_heightScale_switchOn (by linarith) (le_swS θ _) k
    (by linarith [(hc.thK_mem k).2])) hγr.1
  have hαm := alphaD_mem (θ := θ) hX (DF θ X₀ ω) k
  set v := 2 ^ j * (X₀ : ℝ) with hv
  have hv0 : 0 < v := by positivity
  have hθ0 : 0 ≤ t := (hc.thK_mem k).1.le
  have hθ1 : t ≤ 1 / 2 := by linarith [(hc.thK_mem k).2]
  -- the bound of `R_k''` on `[w₁, u]`
  set C := 44 * g ^ 2 * (v / 2) ^ (t - 2) with hC
  have hd2 : ∀ x ∈ Icc w₁ u, ‖oscD2 t α g yS x‖ ≤ C := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hw0 hx.1
    have hxv : v / 2 ≤ x := by
      have : r * u ≤ w₁ := le_max_left _ _
      nlinarith [hx.1]
    rw [Real.norm_eq_abs]
    refine (abs_oscD2_le hθ0 (by linarith) (by linarith) hx0).trans ?_
    have hp : x ^ (t - 2) ≤ (v / 2) ^ (t - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hxv (by linarith)
    have hq : g ^ 2 + 6 * g + 15 ≤ 22 * g ^ 2 := by nlinarith
    rw [abs_of_nonneg (by linarith [hαm.1])]
    calc α * x ^ (t - 2) * (g ^ 2 + 6 * g + 15) ≤ 2 * (v / 2) ^ (t - 2) * (22 * g ^ 2) := by
          gcongr
          · exact hαm.2
      _ = C := by rw [hC]; ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := oscD t α g yS) (f' := oscD2 t α g yS) (s := Icc w₁ u) (C := C)
    (fun x hx => (hasDerivAt_oscD (lt_of_lt_of_le hw0 hx.1) hyS0).hasDerivWithinAt) hd2
    (convex_Icc w₁ u) (left_mem_Icc.mpr hm2) (right_mem_Icc.mpr hm2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - w₁)] at hmvt
  rw [abs_sub_comm]
  refine hmvt.trans ?_
  -- `(u - w₁) C ≤ 4δv · 44 γ² (v/2)^{θ-2} = 352 δγ² (v/2)^{θ-1}`
  have huw : u - w₁ ≤ 4 * δ * v := by
    have : r * u ≤ w₁ := le_max_left _ _
    have hδ0 : 0 ≤ δ := by nlinarith
    nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hpow : (v / 2) ^ (t - 2) * v = 2 * (v / 2) ^ (t - 1) := by
    rw [show t - 1 = (t - 2) + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]; ring
  have hlog : 0 < Real.log y ^ 4 ∨ Real.log y ^ 4 = 0 := by
    rcases (show (0:ℝ) ≤ Real.log y ^ 4 by positivity).lt_or_eq with h4 | h4
    · exact Or.inl h4
    · exact Or.inr h4.symm
  unfold βo
  rw [if_pos (lt_of_lt_of_le h hu2)]
  have hs : Real.sqrt (2 * xk / v) / Real.sqrt xk = (v / 2) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hv0.le, Real.sqrt_mul' _ hxk.le, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    have : Real.sqrt xk ≠ 0 := (Real.sqrt_pos.mpr hxk).ne'
    field_simp
  have hq : (v / 2) ^ (t - 1) ≤ (v / 2) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hq0 : 0 ≤ (v / 2) ^ (t - 1) := Real.rpow_nonneg (by positivity) _
  rcases hlog with h4 | h4
  · have hδg : δ * g ^ 2 * Real.log y ^ 4 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hres h4.le
      rwa [div_mul_cancel₀ _ h4.ne'] at this
    rw [show 352 * Real.sqrt (2 * xk / v) / (Real.sqrt xk * Real.log y ^ 4) =
      352 * (Real.sqrt (2 * xk / v) / Real.sqrt xk) / Real.log y ^ 4 by ring, hs,
      le_div_iff₀ h4]
    calc C * (u - w₁) * Real.log y ^ 4 ≤ 4 * δ * v * C * Real.log y ^ 4 := by
          rw [mul_comm C]; gcongr
      _ = 352 * (δ * g ^ 2 * Real.log y ^ 4) * (v / 2) ^ (t - 1) := by
          rw [hC, show 4 * δ * v * (44 * g ^ 2 * (v / 2) ^ (t - 2)) * Real.log y ^ 4 =
            176 * (δ * g ^ 2 * Real.log y ^ 4) * ((v / 2) ^ (t - 2) * v) by ring, hpow]; ring
      _ ≤ 352 * 1 * (v / 2) ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  · -- `log y = 0`: then `δ γ² ≤ 0`, so `δ ≤ 0` and `u = w₁`
    rw [h4, div_zero] at hres
    have hδ0 : δ ≤ 0 := by
      have : 0 < g ^ 2 := by positivity
      by_contra hne; push_neg at hne; have := mul_pos hne this; linarith
    have : u - w₁ ≤ 0 := by nlinarith
    have hr : 0 ≤ βo θ X₀ y j k := βo_nonneg y j k
    unfold βo at hr; rw [if_pos (lt_of_lt_of_le h hu2)] at hr
    nlinarith

/-- `R'` at `w` is the finite sum of the `R_k'(w)`, `k < K_j`, for `w ≤ 2^{j+1}X₀`. -/
lemma RpR_eq_sum (ω : JitterΩ) (j : ℕ) {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 2 * (2 ^ j * X₀)) :
    RpR θ X₀ ω w = ∑ k ∈ Finset.range (Kb X₀ j),
      RkD θ (alphaD θ X₀ (DF θ X₀ ω) k) (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) w := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hwK : w < switchOn (swS θ X₀) (Kb X₀ j) := by
    have h1 := nat_lt_switchOn (hX1.le.trans (le_swS θ _)) (Kb X₀ j)
    have h2 : 2 * (2 ^ j * (X₀ : ℝ)) ≤ ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ := Nat.le_ceil _
    have h3 : ((Kb X₀ j : ℕ) : ℝ) = ⌈2 * (2 ^ j * (X₀ : ℝ))⌉₊ + 1 := by
      unfold Kb; push_cast; ring
    linarith
  unfold RpR
  exact deriv_osc_eq_sum _ _ _ (hX1.le.trans (le_swS θ _)) hw0 hwK

/-- `Γ(y) ≥ log 2y` once `log y ≥ X₀⁵`: the old heights are resolvable. -/
lemma log_two_mul_le_GammaRes {y : ℝ} (hy0 : 0 < y) (hy : (X₀ : ℝ) ^ 5 ≤ Real.log y) :
    Real.log (2 * y) ≤ GammaRes X₀ y := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hΛX : Real.log X₀ ≤ X₀ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < X₀); linarith
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have hs0 : 0 < Real.log y := lt_of_lt_of_le (by positivity) hy
  rw [Real.log_mul (by norm_num) hy0.ne']
  unfold GammaRes LocalPNT.cLP LocalPNT.cZF
  set s := Real.log y with hs
  set Λ := Real.log (X₀ : ℝ) with hΛ
  set a := 0.088 / Λ / 5 * √s / 4 with ha
  have hsq : √s ^ 2 = s := Real.sq_sqrt hs0.le
  have ha0 : 0 ≤ a := by positivity
  have ha2 : 0.0000193 * s ≤ a ^ 2 * (X₀ : ℝ) ^ 2 := by
    have e : a ^ 2 = (0.0044 / Λ) ^ 2 * √s ^ 2 := by rw [ha]; ring
    rw [hsq] at e
    rw [e]
    have h1 : (0.0044 : ℝ) ^ 2 ≤ (0.0044 / Λ) ^ 2 * (X₀ : ℝ) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := pow_le_pow_left₀ hΛ0.le hΛX 2
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hs0.le]
  have h4 := Real.pow_div_factorial_le_exp a ha0 4
  norm_num [Nat.factorial] at h4
  have hl2 := Real.log_two_lt_d9
  have hXb : (10 : ℝ) ^ 12 ≤ X₀ := by
    have h2 := Real.pow_div_factorial_le_exp Λ (by linarith) 2
    rw [hΛ, Real.exp_log (by linarith)] at h2
    norm_num [Nat.factorial] at h2
    nlinarith
  have hX5 : (X₀ : ℝ) ^ 4 * 10 ^ 12 ≤ s := by
    have : (X₀ : ℝ) ^ 4 * 10 ^ 12 ≤ (X₀ : ℝ) ^ 5 := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hX4 : 0 < (X₀ : ℝ) ^ 4 := by positivity
  have hX41 : (1 : ℝ) ≤ (X₀ : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have hs1 : 1 ≤ s := by nlinarith
  have key : (s + 1) * 24 * (X₀ : ℝ) ^ 4 ≤ a ^ 4 * (X₀ : ℝ) ^ 4 := by
    have h1 := pow_le_pow_left₀ (by positivity) ha2 2
    have e : (a ^ 2 * (X₀ : ℝ) ^ 2) ^ 2 = a ^ 4 * (X₀ : ℝ) ^ 4 := by ring
    rw [e] at h1
    nlinarith [mul_le_mul_of_nonneg_left hX5 hs0.le]
  have : (s + 1) * 24 ≤ a ^ 4 := le_of_mul_le_mul_right key hX4
  linarith

/-- **Old heights are resolvable**: if `x_{k+1} < 2y`, then `γ_k ≤ x_k < log 2y ≤ Γ(y)`. -/
lemma gammaD_res_of_old (ω : JitterΩ) {y : ℝ} {k : ℕ} (hk : switchOn (swS θ X₀) (k + 1) < 2 * y) :
    gammaD θ X₀ (DF θ X₀ ω) k ≤ GammaRes X₀ y := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hX65 := KR.WidthReal.X0_ge hX (X₀ := X₀)
  have hxk := switchOn_pos (swS θ X₀) k
  have hLk := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
  have hL1 : 1 ≤ Real.log (switchOn (swS θ X₀) k) :=
    le_trans (by have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); nlinarith) hLk
  have hxk1 : 1 < switchOn (swS θ X₀) k := by
    rw [← Real.exp_log hxk]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hγ := gammaD_range (θ := θ) hX (DF θ X₀ ω) k
  have h1 : gammaD θ X₀ (DF θ X₀ ω) k ≤ switchOn (swS θ X₀) k :=
    hγ.2.trans (DesignedZero.two_heightScale_le (hc.thK_mem k).1.le
      (kappa0Param_pos (by linarith)).le (kappa0Param_le (by linarith)) hxk1 hL1)
  have hy0 : 0 < 2 * y := lt_of_lt_of_le (switchOn_pos _ _) hk.le
  have h2 : switchOn (swS θ X₀) k < Real.log (2 * y) := by
    have e : switchOn (swS θ X₀) (k + 1) = Real.exp (switchOn (swS θ X₀) k) := rfl
    rw [e] at hk
    rw [Real.lt_log_iff_exp_lt hy0]; exact hk
  -- `log y ≥ X₀⁵`
  have h3 : (X₀ : ℝ) ^ 5 ≤ Real.log y := by
    have hx1 : switchOn (swS θ X₀) 1 ≤ switchOn (swS θ X₀) (k + 1) := switchOn_mono _ (by omega)
    have e1 : switchOn (swS θ X₀) 1 = Real.exp (Real.exp (swS θ (X₀ : ℝ) ^ 2)) := rfl
    have hlt0 : Real.exp (swS θ (X₀ : ℝ) ^ 2) < Real.log (2 * y) := by
      rw [Real.lt_log_iff_exp_lt hy0, ← e1]; linarith
    have hlt : Real.exp ((X₀ : ℝ) ^ 2) < Real.log (2 * y) :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_swS θ _) 2))
        hlt0
    rw [Real.log_mul (by norm_num) (by linarith)] at hlt
    have h6 := Real.pow_div_factorial_le_exp ((X₀ : ℝ) ^ 2) (by positivity) 3
    norm_num [Nat.factorial] at h6
    have hl2 := Real.log_two_lt_d9
    have : (X₀ : ℝ) ^ 5 + 1 ≤ ((X₀ : ℝ) ^ 2) ^ 3 / 6 := by
      have : (X₀ : ℝ) ^ 5 * 7 ≤ (X₀ : ℝ) ^ 6 := by
        rw [show (X₀ : ℝ) ^ 6 = (X₀ : ℝ) ^ 5 * X₀ by ring]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : (1 : ℝ) ≤ (X₀ : ℝ) ^ 5 := one_le_pow₀ (by linarith)
      nlinarith
    linarith
  linarith [log_two_mul_le_GammaRes hc (by linarith) h3]

end Blk

/-! ### The `R'` change -/

section Main

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 8000000 in
/-- **`RprimeChangeR` at every start** (04f-bridge.tex, Proposition 5.35(B), Steps 3–4, sizes of
Step 5): on (H_BS) on `[1, Zc b]`, for `X₀ ≤ y ≤ b + H(b)`, `0 ≤ δ ≤ 1/4` with `δ γ_j² ≤ log⁻⁴ y`
for every resolvable `γ_j`, `log y · |∑_n c_n(y)(R'(max(z/n, X₀)) - R'(y/n))/n| ≤
77 (28.9 κ₀ + 2.7·10⁶ X₀⁻⁶ log⁻⁴ y) ≤ 2 log⁻² y + 3000 κ₀` for `z ∈ J`. -/
theorem rprimeChange_all (ω : JitterΩ) {b : ℝ} (hb : (X₀ : ℝ) ≤ b)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y δ : ℝ} (hy : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4)
    (hres : ∀ j, gammaD θ X₀ (DF θ X₀ ω) j ≤ GammaRes X₀ y →
      δ * gammaD θ X₀ (DF θ X₀ ω) j ^ 2 ≤ 1 / Real.log y ^ 4) :
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
  have hrδ : 1 - r ≤ 2 * δ := by
    have : y * (1 - 2 * δ) ≤ r * y := by rw [hr, div_mul_cancel₀ _ hy0.ne']; exact hz.1
    nlinarith
  -- the per-oscillation block bound
  set t : ℕ → ℕ → ℝ := fun j k =>
    if switchOn (swS θ X₀) (k + 1) < 2 * y then βo θ X₀ y j k else 2 * βk θ X₀ j k with ht
  have ht0 : ∀ j k, 0 ≤ t j k := fun j k => by
    simp only [ht]; split_ifs
    · exact βo_nonneg y j k
    · have := βk_nonneg (θ := θ) (X₀ := X₀) j k; linarith
  -- the switched-off parts (design `θ = 0`)
  set tB : ℕ → ℕ → ℝ := fun j k =>
    if switchOn (swS θ X₀) (k + 1) < 2 * y then offI θ * βo θ X₀ y j k
    else offI θ * (2 * βkB θ X₀ j k) with htB
  have htB0 : ∀ j k, 0 ≤ tB j k := fun j k => by
    have := (offI_mem (θ := θ)).1
    simp only [htB]; split_ifs
    · exact mul_nonneg this (βo_nonneg y j k)
    · have := βkB_nonneg (θ := θ) (X₀ := X₀) j k; positivity
  set bj : ℕ → ℝ := fun j => ∑ k ∈ Finset.range (Kb X₀ j), (t j k + tB j k) with hbj
  have hb0 : ∀ j, 0 ≤ bj j := fun j => Finset.sum_nonneg fun k _ => add_nonneg (ht0 j k) (htB0 j k)
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
    rw [if_pos huX, RpR_eq_sum hc ω j (by linarith) (hm2.trans h2), RpR_eq_sum hc ω j hu0 h2,
      ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hxk0 := switchOn_pos (swS θ X₀) k
    have hyS : switchOn (swS θ X₀) k ≤ switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1 :=
      le_mul_of_one_le_right hxk0.le (le_max_right _ _)
    have hRk : ∀ w, RkD θ (alphaD θ X₀ (DF θ X₀ ω) k) (gammaD θ X₀ (DF θ X₀ ω) k)
        (switchOn (swS θ X₀) k) w =
        oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
          (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) w - offI θ *
        oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
          (gammaD θ X₀ (DF θ X₀ ω) k)
          (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1) w := fun w => by
      unfold RkD offI; split_ifs <;> ring
    rw [hRk, hRk]
    have hoff := (offI_mem (θ := θ))
    simp only [ht, htB]
    split_ifs with hk
    · have hA := abs_oscD_sub_le_βo hc ω j k le_rfl (hres k (gammaD_res_of_old hc ω hk)) hr0 hr1
        hrδ h1 h2
      have hB := abs_oscD_sub_le_βo hc ω j k hyS (hres k (gammaD_res_of_old hc ω hk)) hr0 hr1
        hrδ h1 h2
      set A1 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) (max (r * u) X₀)
      set A2 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) u
      set B1 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1)
        (max (r * u) X₀)
      set B2 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1) u
      have e : A1 - offI θ * B1 - (A2 - offI θ * B2) = (A1 - A2) - offI θ * (B1 - B2) := by ring
      rw [e]
      calc _ ≤ |A1 - A2| + |offI θ * (B1 - B2)| := abs_sub _ _
        _ = |A1 - A2| + offI θ * |B1 - B2| := by rw [abs_mul, abs_of_nonneg hoff.1]
        _ ≤ _ := add_le_add hA (mul_le_mul_of_nonneg_left hB hoff.1)
    · have hA := abs_oscD_le_βk hc ω j k le_rfl (w := max (r * u) X₀)
        (le_trans (by nlinarith) (le_max_left _ _)) (hm2.trans h2)
      have hA' := abs_oscD_le_βk hc ω j k le_rfl (w := u) (by linarith) h2
      have hB := abs_oscD_le_βkB hc ω j k (w := max (r * u) X₀)
        (le_trans (by nlinarith) (le_max_left _ _)) (hm2.trans h2)
      have hB' := abs_oscD_le_βkB hc ω j k (w := u) (by linarith) h2
      set A1 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) (max (r * u) X₀)
      set A2 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k) u
      set B1 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1)
        (max (r * u) X₀)
      set B2 := oscD (thK θ (switchOn (swS θ X₀) k)) (alphaD θ X₀ (DF θ X₀ ω) k)
        (gammaD θ X₀ (DF θ X₀ ω) k) (switchOn (swS θ X₀) k * max (switchOn (swS θ X₀) k) 1) u
      have e : A1 - offI θ * B1 - (A2 - offI θ * B2) = (A1 - A2) - offI θ * (B1 - B2) := by ring
      rw [e]
      have hAA : |A1 - A2| ≤ 2 * βk θ X₀ j k := (abs_sub _ _).trans (by linarith)
      have hBB : |B1 - B2| ≤ 2 * βkB θ X₀ j k := (abs_sub _ _).trans (by linarith)
      calc _ ≤ |A1 - A2| + |offI θ * (B1 - B2)| := abs_sub _ _
        _ = |A1 - A2| + offI θ * |B1 - B2| := by rw [abs_mul, abs_of_nonneg hoff.1]
        _ ≤ _ := add_le_add hAA (mul_le_mul_of_nonneg_left hBB hoff.1)
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
  set F := (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y) with hF
  have hS2 : ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * bj j ≤
      ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * (t j k + tB j k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [hbj]
    rw [Finset.mul_sum]
    have hjJ : j < J := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hsub : Finset.range (Kb X₀ j) ⊆ Finset.range (Kb X₀ J) := by
      apply Finset.range_subset_range.mpr
      unfold Kb
      have : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hjJ.le
      have := Nat.ceil_mono (show 2 * (2 ^ j * (X₀ : ℝ)) ≤ 2 * (2 ^ J * X₀) by nlinarith)
      omega
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun k _ _ => mul_nonneg (hlw j) (add_nonneg (ht0 j k) (htB0 j k))
  have hFJ' : ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) → ∑ j ∈ F, f j ≤ ∑ j ∈ Finset.range J, f j :=
    fun f hf => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => hf j
  -- one oscillation
  set W : ℕ → ℝ := fun k => if switchOn (swS θ X₀) k < 2 * y ∧ 2 * y ≤ switchOn (swS θ X₀) (k + 1)
    then 28.9 / (X₀ : ℝ) else 0 with hW
  have hk : ∀ k : ℕ, ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * t j k ≤
      W k + 2.1 * 10 ^ 6 * (1 / 4) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
    intro k
    set xk := switchOn (swS θ X₀) k with hxk
    set L := Real.log xk with hL
    have hLk := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
    have hxk0 := switchOn_pos (swS θ X₀) k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hL1 : 10000 ≤ L := by nlinarith
    have hL0 : 0 < L := by linarith
    have h2x : 2 * (X₀ : ℝ) ≤ xk := by
      have := Real.add_one_le_exp L
      rw [hL, Real.exp_log hxk0] at this
      have : (X₀ : ℝ) ≤ X₀ ^ 2 := by nlinarith
      nlinarith
    have hl2 : Real.log (2 * xk) ≤ L + 1 := by
      rw [Real.log_mul (by norm_num) hxk0.ne']; linarith [Real.log_two_lt_d9]
    have hW0 : 0 ≤ W k := by simp only [hW]; split_ifs <;> positivity
    have hg0 : 0 ≤ 2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
      positivity
    have htele := tele_sum hXp hlX h2x J
    have hFJ : ∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) → ∑ j ∈ F, f j ≤ ∑ j ∈ Finset.range J, f j :=
      fun f hf => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun j _ _ => hf j
    by_cases hold : switchOn (swS θ X₀) (k + 1) < 2 * y
    · -- an old oscillation: smooth change
      have e : ∀ j, Real.log (2 * (2 ^ j * X₀)) * t j k =
          (if xk < 2 * (2 ^ j * X₀) then
            Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) *
            (352 / (Real.sqrt xk * Real.log y ^ 4)) := by
        intro j; simp only [ht, if_pos hold]; unfold βo; split_ifs <;> ring
      simp_rw [e]
      rw [← Finset.sum_mul]
      have hs0 : 0 ≤ 352 / (Real.sqrt xk * Real.log y ^ 4) := by positivity
      have h1 : ∑ j ∈ F, (if xk < 2 * (2 ^ j * X₀) then
          Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) ≤
          7.2 * Real.log (2 * xk) := by
        refine (hFJ _ fun j => ?_).trans htele
        split_ifs
        · exact mul_nonneg (hlw j) (Real.sqrt_nonneg _)
        · exact le_rfl
      -- `7.2 · 352 log(2x_k)/√x_k ≤ 2.1·10⁶ 4⁻ᵏ X₀⁻⁶`
      have hsx : L ^ 4 / 384 ≤ Real.sqrt xk := by
        have h := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 4
        norm_num [Nat.factorial] at h
        have : Real.sqrt xk = Real.exp (L / 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxk0, ← hL]; ring_nf
        rw [this]; linarith
      have hL3 : (8 : ℝ) ^ k * (X₀ : ℝ) ^ 6 ≤ L ^ 3 := by
        have h0 : (0 : ℝ) ≤ 2 ^ k * (X₀ : ℝ) ^ 2 := by positivity
        have := pow_le_pow_left₀ h0 hLk 3
        calc (8 : ℝ) ^ k * (X₀ : ℝ) ^ 6 = (2 ^ k * (X₀ : ℝ) ^ 2) ^ 3 := by
              rw [mul_pow, ← pow_mul, ← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul,
                mul_comm 3 k]
          _ ≤ _ := this
      have h48 : (1 / 4 : ℝ) ^ k * 8 ^ k ≥ 1 := by
        rw [← mul_pow]; norm_num; exact one_le_pow₀ (by norm_num)
      have hly : 0 < Real.log y := Real.log_pos (by linarith)
      have hsq0 : 0 < Real.sqrt xk := Real.sqrt_pos.mpr hxk0
      have hfin : 7.2 * Real.log (2 * xk) * (352 / (Real.sqrt xk * Real.log y ^ 4)) ≤
          2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have hy4 : 0 < Real.log y ^ 4 := by positivity
        -- `7.2·352·(L+1)·X₀⁶ ≤ 2.1·10⁶ 4⁻ᵏ √x_k`
        have hA : 7.2 * Real.log (2 * xk) * 352 * (X₀ : ℝ) ^ 6 ≤
            2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k * Real.sqrt xk := by
          have h1' : 7.2 * Real.log (2 * xk) * 352 ≤ 2535 * (2 * L) := by nlinarith
          have h2' : (2 * L) * (X₀ : ℝ) ^ 6 * 8 ^ k ≤ 2 * L ^ 4 := by nlinarith
          have h3' : 2 * L ^ 4 ≤ 768 * Real.sqrt xk := by linarith
          have h4' : (1 / 4 : ℝ) ^ k * 8 ^ k * Real.sqrt xk ≥ Real.sqrt xk := by
            nlinarith
          have hq : (0 : ℝ) ≤ (1 / 4) ^ k := by positivity
          have h8 : (0 : ℝ) < 8 ^ k := by positivity
          have : 2535 * (2 * L) * (X₀ : ℝ) ^ 6 * 8 ^ k ≤ 2535 * 768 * Real.sqrt xk := by
            nlinarith
          have : 7.2 * Real.log (2 * xk) * 352 * (X₀ : ℝ) ^ 6 * 8 ^ k ≤
              2.1 * 10 ^ 6 * ((1 / 4 : ℝ) ^ k * 8 ^ k) * Real.sqrt xk := by
            nlinarith [mul_le_mul_of_nonneg_right h1' (show (0 : ℝ) ≤ (X₀ : ℝ) ^ 6 * 8 ^ k by
              positivity)]
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hA hy4.le]
      have hW' : W k = 0 := by simp only [hW]; rw [if_neg (fun h => absurd h.2 (not_le.mpr hold))]
      rw [hW', zero_add]
      calc _ ≤ 7.2 * Real.log (2 * xk) * (352 / (Real.sqrt xk * Real.log y ^ 4)) :=
            mul_le_mul_of_nonneg_right h1 hs0
        _ ≤ _ := hfin
    · -- the current oscillation (or one not yet switched on): the pointwise bound
      push_neg at hold
      have e : ∀ j, Real.log (2 * (2 ^ j * X₀)) * t j k =
          (if xk < 2 * (2 ^ j * X₀) then
            Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) *
            (4 / ((X₀ : ℝ) * L)) := by
        intro j; simp only [ht, if_neg (not_lt.mpr hold)]; unfold βk; split_ifs <;> ring
      simp_rw [e]
      rw [← Finset.sum_mul]
      by_cases hcur : xk < 2 * y
      · have hW' : W k = 28.9 / (X₀ : ℝ) := by simp only [hW]; rw [if_pos ⟨hcur, hold⟩]
        have h1 : ∑ j ∈ F, (if xk < 2 * (2 ^ j * X₀) then
            Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) ≤
            7.2 * Real.log (2 * xk) := by
          refine (hFJ _ fun j => ?_).trans htele
          split_ifs
          · exact mul_nonneg (hlw j) (Real.sqrt_nonneg _)
          · exact le_rfl
        have h2 : 7.2 * Real.log (2 * xk) * (4 / ((X₀ : ℝ) * L)) ≤ 28.9 / (X₀ : ℝ) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hXp]
          nlinarith
        calc _ ≤ 7.2 * Real.log (2 * xk) * (4 / ((X₀ : ℝ) * L)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ W k := by rw [hW']; exact h2
          _ ≤ _ := le_add_of_nonneg_right hg0
      · -- `x_k ≥ 2y`: no block of `F` sees `R_k`
        push_neg at hcur
        have hz : ∑ j ∈ F, (if xk < 2 * (2 ^ j * X₀) then
            Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk / (2 ^ j * X₀)) else 0) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            have := (Finset.mem_filter.mp hj).2
            rw [if_neg (by linarith)]
        rw [hz, zero_mul]
        positivity
  -- the switched-off parts (design `θ = 0`)
  set WB : ℕ → ℝ := fun k => if switchOn (swS θ X₀) k < 2 * y ∧
    2 * y ≤ switchOn (swS θ X₀) (k + 1) then 0.1 / (X₀ : ℝ) else 0 with hWB
  have hkB : ∀ k : ℕ, ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * tB j k ≤
      offI θ * (WB k + 2.1 * 10 ^ 6 * (1 / 4) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4)) := by
    intro k
    have hoff := offI_mem (θ := θ)
    have hg0 : 0 ≤ 2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
      positivity
    by_cases hold : switchOn (swS θ X₀) (k + 1) < 2 * y
    · have e : ∀ j, Real.log (2 * (2 ^ j * X₀)) * tB j k =
          offI θ * (Real.log (2 * (2 ^ j * X₀)) * t j k) := by
        intro j; simp only [htB, ht, if_pos hold]; ring
      simp_rw [e]; rw [← Finset.mul_sum]
      have hWB0 : WB k = 0 := by
        simp only [hWB]; rw [if_neg (fun h => absurd h.2 (not_le.mpr hold))]
      have hW0 : W k = 0 := by
        simp only [hW]; rw [if_neg (fun h => absurd h.2 (not_le.mpr hold))]
      have := hk k
      rw [hW0, zero_add] at this
      rw [hWB0, zero_add]
      exact mul_le_mul_of_nonneg_left this hoff.1
    · push_neg at hold
      have e : ∀ j, Real.log (2 * (2 ^ j * X₀)) * tB j k =
          offI θ * (2 * (Real.log (2 * (2 ^ j * X₀)) * βkB θ X₀ j k)) := by
        intro j; simp only [htB, if_neg (not_lt.mpr hold)]; ring
      simp_rw [e]; rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hoff.1
      refine le_trans ?_ (le_add_of_nonneg_right hg0)
      set xk := switchOn (swS θ X₀) k with hxk
      set L := Real.log xk with hL
      have hLk := log_switchOn_ge_of (Nat.cast_nonneg _) (le_swS θ (X₀ : ℝ)) k
      have hxk0 := switchOn_pos (swS θ X₀) k
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hL1 : 10000 ≤ L := by nlinarith
      have hL0 : 0 < L := by linarith
      have hxL : xk = Real.exp L := (Real.exp_log hxk0).symm
      have hxk1 : 1 ≤ xk := by rw [hxL]; exact Real.one_le_exp (by linarith)
      have hyk : xk * max xk 1 = xk ^ 2 := by rw [max_eq_left hxk1]; ring
      have hxbig : 10 ^ 8 ≤ xk := by
        have := Real.quadratic_le_exp_of_nonneg hL0.le
        rw [← hxL] at this; nlinarith
      by_cases hcur : xk < 2 * y
      · have hWB' : WB k = 0.1 / (X₀ : ℝ) := by simp only [hWB]; rw [if_pos ⟨hcur, hold⟩]
        rw [hWB']
        have h2y : 2 * (X₀ : ℝ) ≤ xk ^ 2 := by
          have hXL : (X₀ : ℝ) ^ 2 ≤ L := le_trans (le_mul_of_one_le_left (by positivity) h2k) hLk
          have hLx : L ≤ xk := by
            have := Real.add_one_le_exp L; rw [← hxL] at this; linarith
          nlinarith
        have htele := tele_sum hXp hlX h2y J
        have hsx0 : 0 < Real.sqrt xk := Real.sqrt_pos.mpr hxk0
        have e2 : ∀ j, 2 * (Real.log (2 * (2 ^ j * X₀)) * βkB θ X₀ j k) =
            (if xk ^ 2 < 2 * (2 ^ j * X₀) then
              Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk ^ 2 / (2 ^ j * X₀)) else 0) *
              (4 / ((X₀ : ℝ) * L * Real.sqrt xk)) := by
          intro j
          unfold βkB
          rw [← hxk, hyk]
          split_ifs
          · have hv : (0 : ℝ) < 2 ^ j * X₀ := by positivity
            have hsq : Real.sqrt (2 * xk ^ 2 / (2 ^ j * X₀)) =
                Real.sqrt (2 * xk / (2 ^ j * X₀)) * Real.sqrt xk := by
              rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
            rw [hsq, ← hL]; field_simp; ring
          · ring
        simp_rw [e2]
        rw [← Finset.sum_mul]
        have h1 : ∑ j ∈ F, (if xk ^ 2 < 2 * (2 ^ j * X₀) then
            Real.log (2 * (2 ^ j * X₀)) * Real.sqrt (2 * xk ^ 2 / (2 ^ j * X₀)) else 0) ≤
            7.2 * Real.log (2 * xk ^ 2) := by
          refine (hFJ' _ fun j => ?_).trans htele
          split_ifs
          · exact mul_nonneg (hlw j) (Real.sqrt_nonneg _)
          · exact le_rfl
        have hl2 : Real.log (2 * xk ^ 2) ≤ 3 * L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; linarith [Real.log_two_lt_d9]
        have hsx : 1000 ≤ Real.sqrt xk := by
          rw [Real.le_sqrt (by norm_num) hxk0.le]; linarith
        calc _ ≤ 7.2 * Real.log (2 * xk ^ 2) * (4 / ((X₀ : ℝ) * L * Real.sqrt xk)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ 7.2 * (3 * L) * (4 / ((X₀ : ℝ) * L * Real.sqrt xk)) := by gcongr
          _ = 86.4 / ((X₀ : ℝ) * Real.sqrt xk) := by field_simp; ring
          _ ≤ 0.1 / (X₀ : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hXp]; nlinarith
      · push_neg at hcur
        have hWB' : WB k = 0 := by
          simp only [hWB]; rw [if_neg (fun h => absurd h.1 (not_lt.mpr hcur))]
        rw [hWB']
        apply le_of_eq
        refine Finset.sum_eq_zero fun j hj => ?_
        have := (Finset.mem_filter.mp hj).2
        unfold βkB
        rw [if_neg (by rw [← hxk, hyk]; nlinarith)]
        ring
  have hS3 : ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ F,
      Real.log (2 * (2 ^ j * X₀)) * (t j k + tB j k) ≤
      29 / (X₀ : ℝ) + 5.6 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
    have hsplit : ∀ k, ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * (t j k + tB j k) =
        ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * t j k +
          ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * tB j k := fun k => by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hoff := offI_mem (θ := θ)
    have h1 := sum_window_le' (swS θ (X₀ : ℝ)) (2 * y) (28.9 / (X₀ : ℝ)) (by positivity) (Kb X₀ J)
    have h1B := sum_window_le' (swS θ (X₀ : ℝ)) (2 * y) (0.1 / (X₀ : ℝ)) (by positivity) (Kb X₀ J)
    have h2 : ∑ k ∈ Finset.range (Kb X₀ J),
        2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) ≤
        2.8 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := Construction.sum_inv_four_pow_le (Kb X₀ J)
      nlinarith
    have hA : ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * t j k ≤
        28.9 / (X₀ : ℝ) + 2.8 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
      refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
      rw [Finset.sum_add_distrib]
      exact add_le_add h1 h2
    have hB : ∑ k ∈ Finset.range (Kb X₀ J), ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * tB j k ≤
        0.1 / (X₀ : ℝ) + 2.8 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
      refine (Finset.sum_le_sum fun k _ => hkB k).trans ?_
      have hle : ∀ k, offI θ * (WB k + 2.1 * 10 ^ 6 * (1 / 4) ^ k /
          ((X₀ : ℝ) ^ 6 * Real.log y ^ 4)) ≤
          WB k + 2.1 * 10 ^ 6 * (1 / 4) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := fun k => by
        have hWB0 : 0 ≤ WB k := by simp only [hWB]; split_ifs <;> positivity
        have : 0 ≤ 2.1 * 10 ^ 6 * (1 / 4 : ℝ) ^ k / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by
          positivity
        nlinarith
      refine (Finset.sum_le_sum fun k _ => hle k).trans ?_
      rw [Finset.sum_add_distrib]
      exact add_le_add h1B h2
    have e1 : (29 : ℝ) / X₀ = 28.9 / X₀ + 0.1 / X₀ := by ring
    have e2 : (5.6 * 10 ^ 6 : ℝ) / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) =
        2.8 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) +
          2.8 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4) := by ring
    rw [e1, e2]
    linarith
  have hCS := BeurlingSystem.CS_le
  have hS0 : 0 ≤ ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * bj j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hlw j) (hb0 j)
  have hly : (10 : ℝ) ^ 8 ≤ Real.log y := hX.trans (Real.log_le_log hXp hy)
  have hfin : 77 * (29 / (X₀ : ℝ) + 5.6 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4)) ≤
      2 / Real.log y ^ 2 + 3000 * kappa0Param X₀ := by
    unfold kappa0Param
    have hX6 : (1 : ℝ) ≤ (X₀ : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    have hly2 : 0 < Real.log y ^ 2 := by positivity
    have h1 : 77 * (5.6 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4)) ≤ 2 / Real.log y ^ 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hly2]
      have : (10 : ℝ) ^ 16 ≤ Real.log y ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hX6 (show (0 : ℝ) ≤ Real.log y ^ 4 by positivity)]
    have h2 : 77 * (29 / (X₀ : ℝ)) ≤ 3000 * (1 / (X₀ : ℝ)) := by
      rw [mul_div_assoc', mul_one_div, div_le_div_iff_of_pos_right hXp]; norm_num
    linarith
  calc Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (oscF θ X₀ ω (z / y))|
      ≤ _ := hR
    _ ≤ 77 * ∑ j ∈ F, Real.log (2 * (2 ^ j * X₀)) * bj j := mul_le_mul_of_nonneg_right hCS hS0
    _ ≤ 77 * (29 / (X₀ : ℝ) + 5.6 * 10 ^ 6 / ((X₀ : ℝ) ^ 6 * Real.log y ^ 4)) := by
        linarith
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
    ((deltaB_le ω y).trans hq) fun j hj => deltaB_res hc ω hy hj

end Main

end BModel

end
