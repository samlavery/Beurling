module

public import RequestProject.Beurling.Model.SlotsSharp
public import RequestProject.Beurling.Model.JLaw
public import RequestProject.Beurling.Model.SlotHypCap
public import RequestProject.Beurling.Queue6.Defs6

/-!
# The landing compensator bound `μ(J) ≤ μ̄(J)` (Lemma 6.1, (F1)–(F2))

For a landing window `J = [P + i/2, P + j/2)` of `𝒥_P` (`AdmJ`), the compensator
`μ(J) = ∑_k P(the prime decided at slot k + 1 lands in J | F_k)` of the candidates
(`|s - J| ≤ H(s)/2`, `Queue6.landInd`) is at most
`μ̄(J) = (|J| + H₊ + 2) min(1, |J|/H₋)`, `H₋ = H(P/2)`, `H₊ = H(8P)` (§6.2).

**Bookkeeping (checked).** Each conditional probability is `|J ∩ box(s)|/H(s) ≤ min(1, |J|/H₋)`
((F2), `law_dens`; `H(s) ≥ H₋` since `s ≥ 8P/9`). The candidates are placed slots with starts in
`(a, b]`, `b - a ≤ |J| + H_c + 1/2`, `H_c = H(5P) ≥ H(s)`; their number is at most
`C(b) - C(a) + 1` (`card_le_contD`: consecutive placed slots with unit jumps are `≥ 1` apart in
`C`). The slot-density excess is absorbed as in the paper (§6.2, after the definition of `μ̄`):

* below `x₁ = switchOn X₀ 0` the oscillation vanishes, so `C(b) - C(a) ≤ b - a`
  (`contD_upper_below`; the density is `≤ 1`, not only `≤ 1 + 1/(κt)`);
* if `b > x₁`, then `log log (5P) ≥ log X₀`, `H = H_std` on `[5P, 8P]` (`capH_eq_std_large`) and
  the gap `H(8P) - H(5P) ≥ 7 H(5P)/log(8P)` (`capH_gap`) exceeds the excess
  `0.02 (|J| + H_c + 1/2)/log a ≤ 0.15 H(5P)/log a`.

So the count is `≤ |J| + H₊ + 2`, and the paper's `μ̄(J)` is correct.

* `slot_gt` : `X₀ < s_{k+1}`;
* `contD_upper_below`, `card_le_contD`, `capH_eq_std_large`, `capH_gap`, `capH_half_le`;
* `cand_card_le` : the candidate count `≤ |J| + H₊ + 2`, on the event that all stages are good;
* `land_compensator` : the field `land` of `Queue6.QueueInputs`.
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Target Oscillation Absorbed Construction
  DesignedZero CaplLink SlotModel BSCert.Capl
open scoped ENNReal

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section Det

variable {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- Slot starts beyond the first lie strictly above `X₀`. -/
lemma slot_gt (k : ℕ) : (X₀ : ℝ) < h.limModel.slot (k + 1) := by
  by_contra hc
  push_neg at hc
  have h1 := h.limModel.level_le_T_slot (k + 1)
  have h2 := h.limModel_T_le hc
  have hϑ : h.limModel.ϑ = 1 / 2 := rfl
  unfold SlotModel.level at h1
  rw [hϑ] at h1
  push_cast at h1
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- **Below `x₁` the slot density is at most `1`**: `C(x') - C(x) ≤ x' - x` for
`X₀ ≤ x ≤ x' ≤ x₁ = switchOn X₀ 0` (the oscillation vanishes there, `ρ_det, ρ̄_A ≥ 0`). -/
lemma contD_upper_below (D : PrimeData) (hD : LocFinD D) {x x' : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (hxx : x ≤ x') (hx1 : x' ≤ switchOn X₀ 0) :
    contD θ X₀ D x' - contD θ X₀ D x ≤ x' - x := by
  have hX := h.hX
  have hX1 : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX1n : 1 ≤ X₀ := by exact_mod_cast hX1.le
  have hb : 0 < θ / 2 := by linarith [h.hθ.1]
  obtain ⟨hκ0, -⟩ := kappa_facts hX
  have hA := absSet_locFin (X₀ := X₀) hD
  unfold contD
  rw [show uA θ = (fun n => solveU (θ / 2) n) from rfl]
  rw [contPart_sub (fun y hy => intervalIntegrable_rhoDet X₀ hκ0 hX1n hy)
    (fun y hy => intervalIntegrable_absorbedDensityCap _ hA hb hX1 hy) hx hxx]
  have h1 : 0 ≤ ∫ u in x..x', Target.rhoDet X₀ (kappaParam X₀) u :=
    intervalIntegral.integral_nonneg hxx fun u hu => rhoDet_nonneg X₀ hκ0 (by linarith [hu.1])
  have h2 : 0 ≤ ∫ u in x..x', absorbedDensityCap (θ / 2) (absSet X₀ D)
      (fun n => solveU (θ / 2) n) u :=
    intervalIntegral.integral_nonneg hxx fun u hu =>
      (absorbedDensityCap_mem _ (by linarith [hu.1]) _).1
  have hsp := switchOn_spacing (X₀ : ℝ)
  have hR1 : osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) x' = 0 :=
    Target.osc_eq_zero_of_le hsp (by linarith) hx1
  have hR2 : osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀) x = 0 :=
    Target.osc_eq_zero_of_le hsp (by linarith) (hxx.trans hx1)
  rw [hR1, hR2]
  linarith

/-- **The placed slots with unit jumps in `(a, b]` number at most `C(b) - C(a) + 1`.** -/
lemma card_le_contD {a b : ℝ} (S : Finset ℕ)
    (hS : ∀ m ∈ S, placedAt h.limModel m ∧
      UnitJumpAt X₀ (DM h.limModel U) (h.limModel.slot (m + 1)) ∧
      a < h.limModel.slot (m + 1) ∧ h.limModel.slot (m + 1) ≤ b)
    (ha : (X₀ : ℝ) ≤ a) (hab : a ≤ b) :
    (S.card : ℝ) ≤ contD θ X₀ (DM h.limModel U) b - contD θ X₀ (DM h.limModel U) a + 1 := by
  classical
  set M := h.limModel
  set W := winFacts h
  set C := contD θ X₀ (DM M U)
  have hge : ∀ m ∈ S, (X₀ : ℝ) < M.slot (m + 1) := fun m _ => slot_gt h m
  set g : ℕ → ℕ := fun m => ⌊C (M.slot (m + 1)) - C a⌋₊
  have hpos : ∀ m ∈ S, 0 ≤ C (M.slot (m + 1)) - C a := by
    intro m hm
    have := W.cmono _ _ ha (hS m hm).2.2.1.le
    linarith
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' hg
    by_contra hne
    have h3 : (g m : ℝ) = g m' := by rw [hg]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := placed_gap W (hS m hm).2.1 (hS m' hm').2.1 hlt (hS m hm).1 (hS m' hm').1
        (hge m hm)
      have h1 := Nat.floor_le (hpos m hm)
      have h2 := Nat.lt_floor_add_one (C (M.slot (m' + 1)) - C a)
      simp only [g] at h3
      linarith
    · have := placed_gap W (hS m' hm').2.1 (hS m hm).2.1 hlt (hS m' hm').1 (hS m hm).1
        (hge m' hm')
      have h1 := Nat.floor_le (hpos m' hm')
      have h2 := Nat.lt_floor_add_one (C (M.slot (m + 1)) - C a)
      simp only [g] at h3
      linarith
  have hmaps : Set.MapsTo g S (Finset.range (⌊C b - C a⌋₊ + 1) : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    have := W.cmono _ _ (ha.trans (hS m hm).2.2.1.le) (hS m hm).2.2.2
    linarith
  have hcard := Set.ncard_le_ncard_of_injOn g hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range] at hcard
  have hCab : 0 ≤ C b - C a := by have := W.cmono _ _ ha hab; linarith
  have h1 : ((⌊C b - C a⌋₊ + 1 : ℕ) : ℝ) ≤ C b - C a + 1 := by
    push_cast; linarith [Nat.floor_le hCab]
  have hc : (S.card : ℝ) ≤ ((⌊C b - C a⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

end Det

/-! ### The jitter width near `P` -/

/-- `18 ≤ log y` for `y ≥ 9·10⁷`. -/
lemma log_ge_18' {y : ℝ} (hy : 90000000 ≤ y) : 18 ≤ Real.log y := by
  have h : Real.exp 18 ≤ 90000000 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 18 ≤ 2.7182818286 ^ 18 := by gcongr
      _ ≤ 90000000 := by norm_num
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- `γ(s) ≤ 7.5` at the break point `s_H`. -/
lemma gam_le_75 (s : ℝ) : gam sHroot s ≤ 7.5 := by
  have hsH := sHroot_mem
  by_cases hs : s ≤ sHroot
  · unfold gam; rw [if_pos hs]
    have := gstar_mono hs (by linarith [hsH.2])
    linarith [QueueMono.gstar_sHroot_le]
  · exact gam_le_of_gt QueueMono.gstar_sHroot_le (by push_neg at hs; exact hs)

/-- If `log c = 4ℓ² - log 4` at `x` (and `ℓ ≥ 18`), then `M̄₁(x)² ≤ H_std(x)`. -/
lemma capM1_sq_le_std {X₀ x : ℝ} (hl : 18 ≤ Real.log (Real.log x))
    (hlogc : logc sHroot (Real.log X₀) (capS X₀ x) =
      4 * Real.log (Real.log x) ^ 2 - Real.log 4)
    (hMpos : 0 ≤ capM1 X₀ x) :
    capM1 X₀ x ^ 2 ≤ Real.exp (8 * Real.log (Real.log x) ^ 2) := by
  set ℓ := Real.log (Real.log x)
  have hℓ : 2 * Real.log (Real.log X₀) + capS X₀ x = ℓ := ell_eq X₀ x
  have hM := Mbar1_le (sH := sHroot) (Λ := Real.log X₀) (s := capS X₀ x) (by rw [hℓ]; exact hl)
  rw [hlogc, Real.exp_sub, Real.exp_log (by norm_num)] at hM
  have hM' : capM1 X₀ x ≤ Real.exp (4 * ℓ ^ 2) / 2 := by unfold capM1; linarith
  have e : Real.exp (8 * ℓ ^ 2) = Real.exp (4 * ℓ ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e]
  have h0 : 0 < Real.exp (4 * ℓ ^ 2) := Real.exp_pos _
  nlinarith

/-- **`H = H_std` at large heights**: if `log log x ≥ log X₀` then `H(x) = e^{8 (log log x)²}`. -/
theorem capH_eq_std_large {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hl : Real.log X₀ ≤ Real.log (Real.log x)) :
    capH X₀ x = Real.exp (8 * Real.log (Real.log x) ^ 2) := by
  set Λ := Real.log X₀
  set ℓ := Real.log (Real.log x)
  have hℓ : 2 * Real.log Λ + capS X₀ x = ℓ := ell_eq X₀ x
  have hg := gam_le_75 (capS X₀ x)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hlogc : logc sHroot Λ (capS X₀ x) = 4 * ℓ ^ 2 - Real.log 4 := by
    unfold logc
    rw [hℓ]
    apply max_eq_left
    have hΛ0 : 0 < Λ := by linarith
    have : gam sHroot (capS X₀ x) * Λ ≤ 7.5 * Λ := mul_le_mul_of_nonneg_right hg hΛ0.le
    nlinarith
  have hl18 : 18 ≤ ℓ := by linarith
  have hsq := capM1_sq_le_std hl18 hlogc (capM1_pos hX0 hX hx).le
  unfold capH
  exact max_eq_left hsq

/-- `log(1 + t) ≥ t/(1 + t)` for `t ≥ 0`. -/
lemma log_one_add_ge {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ≤ Real.log (1 + t) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 + t) by positivity)
  rw [one_div, Real.log_inv] at h
  have e : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by field_simp; ring
  linarith

/-- **The gap of `H` above `5P`**: `H(8P) - H(5P) ≥ 7 H(5P)/log(8P)` when `H = H_std` there
(`log log (5P) ≥ log X₀`). -/
theorem capH_gap {X₀ P : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hP : X₀ ≤ P)
    (hl : Real.log X₀ ≤ Real.log (Real.log (5 * P))) :
    7 * capH X₀ (5 * P) / Real.log (8 * P) ≤ capH X₀ (8 * P) - capH X₀ (5 * P) := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hP0 : 0 < P := by linarith
  have h5 : X₀ ≤ 5 * P := by linarith
  have h8 : X₀ ≤ 8 * P := by linarith
  have hL5 : 0 < Real.log (5 * P) := Real.log_pos (by linarith)
  have hL58 : Real.log (5 * P) ≤ Real.log (8 * P) := Real.log_le_log (by linarith) (by linarith)
  have hl8 : Real.log X₀ ≤ Real.log (Real.log (8 * P)) :=
    hl.trans (Real.log_le_log hL5 hL58)
  rw [capH_eq_std_large hX0 hX h5 hl, capH_eq_std_large hX0 hX h8 hl8]
  have hL8 : Real.log (8 * P) = Real.log (5 * P) + Real.log 1.6 := by
    rw [show (8 : ℝ) * P = 1.6 * (5 * P) by ring, Real.log_mul (by norm_num) (by positivity)]
    ring
  set L5 := Real.log (5 * P)
  set L8 := Real.log (8 * P)
  set ℓ5 := Real.log L5
  set ℓ8 := Real.log L8
  have hl16 : 0.46 ≤ Real.log 1.6 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_bound (x := (0.46 : ℝ)) (by norm_num [abs_of_pos]) (n := 5) (by norm_num)
    have := (abs_le.mp this).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  -- `ℓ8 - ℓ5 ≥ 0.47/L8`
  set t := Real.log 1.6 / L5 with ht
  have ht0 : 0 ≤ t := by positivity
  have hdiff : ℓ8 - ℓ5 = Real.log (1 + t) := by
    rw [← Real.log_div (by linarith) hL5.ne']
    congr 1; rw [hL8, ht]; field_simp
  have hlt := log_one_add_ge ht0
  have ht1 : t / (1 + t) = Real.log 1.6 / L8 := by
    rw [ht, hL8]; field_simp
  have hL8p : 0 < L8 := by linarith
  have hd : 0.46 / L8 ≤ ℓ8 - ℓ5 := by
    rw [hdiff]; refine le_trans ?_ hlt; rw [ht1]
    exact div_le_div_of_nonneg_right hl16 hL8p.le
  have hℓ5 : 18 ≤ ℓ5 := by
    have : (18 : ℝ) ≤ Real.log X₀ := by linarith
    linarith
  -- `8(ℓ8² - ℓ5²) ≥ 7/L8`
  have hsq : 7 / L8 ≤ 8 * ℓ8 ^ 2 - 8 * ℓ5 ^ 2 := by
    have hpos : 0 ≤ ℓ8 - ℓ5 := le_trans (by positivity) hd
    have e : 8 * ℓ8 ^ 2 - 8 * ℓ5 ^ 2 = 8 * (ℓ8 - ℓ5) * (ℓ8 + ℓ5) := by ring
    rw [e]
    have h1 : 8 * (0.46 / L8) * 36 ≤ 8 * (ℓ8 - ℓ5) * (ℓ8 + ℓ5) := by
      apply mul_le_mul (by linarith) (by linarith) (by norm_num) (by positivity)
    have h2 : 7 / L8 ≤ 8 * (0.46 / L8) * 36 := by
      rw [show 8 * (0.46 / L8) * 36 = 132.48 / L8 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hL8p.le
    linarith
  set E := Real.exp (8 * ℓ5 ^ 2)
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : E * (1 + 7 / L8) ≤ Real.exp (8 * ℓ8 ^ 2) := by
    have h := Real.add_one_le_exp (8 * ℓ8 ^ 2 - 8 * ℓ5 ^ 2)
    have e : Real.exp (8 * ℓ8 ^ 2) = E * Real.exp (8 * ℓ8 ^ 2 - 8 * ℓ5 ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hE0.le
  have : 7 * E / L8 = E * (7 / L8) := by ring
  linarith

/-- **`H(s) ≥ H₋ = H(P/2)`** for slot starts `s ≥ max(X₀, P/2)`, `P = 2^m X₀` (for `m = 0`,
`H(X₀/2) = H_std(X₀/2) ≤ H(X₀)`). -/
theorem capH_half_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) (m : ℕ) {s : ℝ} (hs : (X₀ : ℝ) ≤ s)
    (hsP : 2 ^ m * (X₀ : ℝ) / 2 ≤ s) :
    capH X₀ (2 ^ m * (X₀ : ℝ) / 2) ≤ capH X₀ s := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hmono := capH_monotoneOn hX0 hX
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, one_mul]
    refine le_trans ?_ (hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs)
    -- `H(X₀/2) ≤ H(X₀)`
    set Λ := Real.log (X₀ : ℝ)
    have hΛ0 : 0 < Λ := by linarith
    have hL2 : Real.log ((X₀ : ℝ) / 2) = Λ - Real.log 2 :=
      Real.log_div (by linarith) (by norm_num)
    have hl2 := Real.log_two_lt_d9
    have hL2p : 0 < Real.log ((X₀ : ℝ) / 2) := by rw [hL2]; linarith
    set ℓ₂ := Real.log (Real.log ((X₀ : ℝ) / 2))
    have hℓ₂le : ℓ₂ ≤ Real.log Λ := Real.log_le_log hL2p (by
      rw [hL2]; linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)])
    have hℓ₂18 : 18 ≤ ℓ₂ := log_ge_18' (by rw [hL2]; linarith)
    have hℓ₂lo : Real.log Λ - 1 ≤ ℓ₂ := by
      have h := Real.log_le_log (by positivity) (show Λ / 2 ≤ Real.log ((X₀ : ℝ) / 2) by
        rw [hL2]; linarith)
      rw [Real.log_div hΛ0.ne' (by norm_num)] at h
      linarith
    set s' := capS (X₀ : ℝ) ((X₀ : ℝ) / 2)
    have hs'e : 2 * Real.log Λ + s' = ℓ₂ := ell_eq _ _
    have hsH := sHroot_mem
    have hs'1 : s' ≤ -Real.log Λ := by linarith
    have hgam : gam sHroot s' = gstar s' := by
      unfold gam; rw [if_pos (by linarith [hsH.1, Real.log_nonneg (show (1 : ℝ) ≤ Λ by linarith)])]
    have hgm := gstar_mono hs'1 (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Λ by linarith)])
    have hgΛ := JitterFloor.gstar_mul_le (show (10 : ℝ) ^ 8 ≤ Λ by linarith) le_rfl
      (by linarith)
    have hl18 : 18 ≤ Real.log Λ := log_ge_18 (by norm_num; linarith)
    have hlog4 : 0 ≤ Real.log 4 ∧ Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); push_cast; constructor <;> linarith
    have hlogc : logc sHroot Λ s' = 4 * ℓ₂ ^ 2 - Real.log 4 := by
      unfold logc
      rw [hs'e, hgam]
      apply max_eq_left
      have : gstar s' * Λ ≤ gstar (-Real.log Λ) * Λ := mul_le_mul_of_nonneg_right hgm hΛ0.le
      nlinarith
    have hMp : 0 ≤ capM1 (X₀ : ℝ) ((X₀ : ℝ) / 2) := by
      have := exp_logc_le_Mbar1 (sH := sHroot) (Λ := Λ) (s := s') (by rw [hs'e]; linarith)
      unfold capM1
      exact le_trans (Real.exp_pos _).le this
    have hsq := capM1_sq_le_std hℓ₂18 hlogc hMp
    have hstd : Real.exp (8 * ℓ₂ ^ 2) ≤ Real.exp (8 * Real.log Λ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : ℓ₂ ^ 2 ≤ Real.log Λ ^ 2 := pow_le_pow_left₀ (by linarith) hℓ₂le 2
      linarith
    have hX₀std : Real.exp (8 * Real.log Λ ^ 2) ≤ capH (X₀ : ℝ) X₀ := le_max_left _ _
    unfold capH
    exact max_le (hstd.trans hX₀std) (hsq.trans (hstd.trans hX₀std))
  · have h2 : (X₀ : ℝ) ≤ 2 ^ m * (X₀ : ℝ) / 2 := by
      have : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
      nlinarith
    exact hmono (mem_Ici.mpr h2) (mem_Ici.mpr hs) hsP

/-! ### The candidate count -/

section Count

variable {U : ℕ → ℝ} (h : Std θ X₀ U)
include h

/-- **The candidate count** (§6.2, `μ̄`): if the placed candidate slots of `J ∈ 𝒥_P` have unit
jumps, at most `|J| + H₊ + 2` of them lie in any finite set `S`. -/
theorem cand_card_le {m i j : ℕ} (hJ : Queue6.AdmJ X₀ m i j) (S : Finset ℕ)
    (hS : ∀ k ∈ S, placedAt h.limModel k ∧
      UnitJumpAt X₀ (DM h.limModel U) (h.limModel.slot (k + 1)) ∧
      Queue6.Jlo X₀ m i - capH X₀ (h.limModel.slot (k + 1)) / 2 ≤ h.limModel.slot (k + 1) ∧
      h.limModel.slot (k + 1) ≤ Queue6.Jhi X₀ m j + capH X₀ (h.limModel.slot (k + 1)) / 2) :
    (S.card : ℝ) ≤ ((j : ℝ) - i) / 2 + capH X₀ (8 * Queue6.uS X₀ m) + 2 := by
  have hX := h.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hXb : 2 ^ (16 : ℕ) ≤ (X₀ : ℝ) := (winFacts h).big
  set M := h.limModel
  set P := Queue6.uS X₀ m with hPdef
  have hP : (X₀ : ℝ) ≤ P := by
    rw [hPdef, Queue6.uS]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := m)]
  obtain ⟨hij, hJH, hJhi⟩ := hJ
  rw [← hPdef] at hJH hJhi
  have hP8 : (8 : ℝ) ≤ P := by
    have h16 : (2 : ℝ) ^ (16 : ℕ) = 65536 := by norm_num
    linarith
  have hlo : Queue6.Jlo X₀ m i = P + i / 2 := rfl
  have hhi : Queue6.Jhi X₀ m j = P + j / 2 := rfl
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hmono := capH_monotoneOn hX0 hX
  set Hc := capH X₀ (5 * P) with hHc
  set Hp := capH X₀ (8 * P) with hHp
  have hHcHp : Hc ≤ Hp := hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith))
    (by linarith)
  have hHPc : capH X₀ P ≤ Hc := hmono (mem_Ici.mpr hP) (mem_Ici.mpr (by linarith)) (by linarith)
  have hHc1 : 1 ≤ Hc := InitialRange.one_le_capH hX0 hX (by linarith)
  have hHc4 : 4 * Hc ≤ 5 * P := four_capH_le hX0 hX (by linarith)
  -- every candidate has `X₀ < s ≤ 5P` and `H(s) ≤ H_c`
  have hcand : ∀ k ∈ S, (X₀ : ℝ) < M.slot (k + 1) ∧ M.slot (k + 1) ≤ 5 * P ∧
      capH X₀ (M.slot (k + 1)) ≤ Hc := by
    intro k hk
    obtain ⟨-, -, h1, h2⟩ := hS k hk
    have hgt := slot_gt h k
    have h4 := four_capH_le hX0 hX hgt.le
    have h5 : M.slot (k + 1) ≤ 5 * P := by rw [hhi] at h2; linarith
    exact ⟨hgt, h5, hmono (mem_Ici.mpr hgt.le) (mem_Ici.mpr (by linarith)) h5⟩
  set a := max (X₀ : ℝ) (Queue6.Jlo X₀ m i - Hc / 2 - 1 / 2) with ha
  set b := Queue6.Jhi X₀ m j + Hc / 2 with hb
  have haX : (X₀ : ℝ) ≤ a := le_max_left _ _
  have hab : a ≤ b := max_le (by rw [hb, hhi]; linarith) (by rw [hb, hhi, hlo]; linarith)
  have hba : b - a ≤ ((j : ℝ) - i) / 2 + Hc + 1 / 2 := by
    have := le_max_right (X₀ : ℝ) (Queue6.Jlo X₀ m i - Hc / 2 - 1 / 2)
    rw [← ha] at this
    rw [hb, hhi]; rw [hlo] at this; linarith
  have hcard := card_le_contD h S (a := a) (b := b) (fun k hk => by
    obtain ⟨hp, hu, h1, h2⟩ := hS k hk
    obtain ⟨hgt, -, hHk⟩ := hcand k hk
    refine ⟨hp, hu, max_lt hgt (by linarith), by rw [hb]; linarith⟩) haX hab
  have hD := locFinD_DM hX h.hU M
  by_cases hb1 : b ≤ switchOn X₀ 0
  · have hC := contD_upper_below h (DM M U) hD haX hab hb1
    linarith
  · push_neg at hb1
    have hC := contD_upper_log h.hθ hX (DM M U) hD haX hab
    -- the height is beyond `x₁`, so `H = H_std` on `[5P, 8P]`
    have hb5 : b ≤ 5 * P := by rw [hb, hhi]; linarith
    have hlogb : (X₀ : ℝ) ^ 2 < Real.log (5 * P) := by
      have h1 : Real.exp ((X₀ : ℝ) ^ 2) < 5 * P := lt_of_lt_of_le hb1 hb5
      have := Real.log_lt_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at this
    have hll : Real.log (X₀ : ℝ) ≤ Real.log (Real.log (5 * P)) := by
      have h2 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 2 := by nlinarith
      exact Real.log_le_log (by linarith) (by linarith)
    have hgap := capH_gap hX0 hX hP hll
    rw [← hHc, ← hHp] at hgap
    -- `log a ≥ log P - log 4`, `log(8P) = log P + log 8`
    have haP : P / 4 ≤ a := le_trans (by rw [hlo]; linarith) (le_max_right _ _)
    have hP0 : 0 < P := by linarith
    have hlogP : 10 ^ 8 ≤ Real.log P := hX.trans (Real.log_le_log (by linarith) hP)
    have hla : Real.log P - Real.log 4 ≤ Real.log a := by
      have := Real.log_le_log (by positivity) haP
      rwa [Real.log_div hP0.ne' (by norm_num)] at this
    have hl8 : Real.log (8 * P) = Real.log 8 + Real.log P := Real.log_mul (by norm_num) hP0.ne'
    have hl2 := Real.log_two_lt_d9
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hl8' : Real.log 8 ≤ 7 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith
    have hLa : 0 < Real.log a := by linarith
    have hL8 : 0 < Real.log (8 * P) := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)]
    -- the excess `0.02 (b - a)/log a ≤ 0.15 H_c/log a ≤ 7 H_c/log(8P)`
    have hJc : ((j : ℝ) - i) / 2 ≤ 6 * Hc := by linarith
    have hexc1 : 0.02 * (b - a) ≤ 0.15 * Hc := by linarith
    have hexc2 : 0.15 * Hc / Real.log a ≤ 7 * Hc / Real.log (8 * P) := by
      rw [div_le_div_iff₀ hLa hL8]
      have hk : 0.15 * Real.log (8 * P) ≤ 7 * Real.log a := by linarith
      have := mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℝ) ≤ Hc)
      linarith
    have hexc : 0.02 / Real.log a * (b - a) ≤ Hp - Hc := by
      have e : 0.02 / Real.log a * (b - a) = 0.02 * (b - a) / Real.log a := by ring
      rw [e]
      have := div_le_div_of_nonneg_right hexc1 hLa.le
      linarith
    have : (1 + 0.02 / Real.log a) * (b - a) = (b - a) + 0.02 / Real.log a * (b - a) := by ring
    linarith

end Count

/-! ### The conditional means -/

/-- A conditional expectation is bounded by an `m`-measurable `g` whose set integrals over
`m`-measurable sets dominate those of `f`. -/
lemma condExp_ae_le_of_setIntegral {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg : StronglyMeasurable[m] g) (hgi : Integrable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ) :
    μ[f | m] ≤ᵐ[μ] g := by
  refine ae_of_ae_trim hm ?_
  refine ae_le_of_forall_setIntegral_le (integrable_condExp.trim hm stronglyMeasurable_condExp)
    (hgi.trim hm hg) fun s hs _ => ?_
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hs, ← setIntegral_trim hm hg hs,
    setIntegral_condExp hm hf hs]
  exact h s hs

section Prob

variable (hc : Cond θ X₀)
include hc

/-- The candidate event of slot `k + 1` for `J = [Jlo, Jhi)`. -/
def candEv (θ : ℝ) (X₀ : ℕ) (m i j k : ℕ) : Set JitterΩ :=
  {ω | placedAt (Mcl θ X₀ ω) k ∧
    Queue6.Jlo X₀ m i - HF θ X₀ k ω / 2 ≤ slotF θ X₀ k ω ∧
    slotF θ X₀ k ω ≤ Queue6.Jhi X₀ m j + HF θ X₀ k ω / 2}

omit hc in
lemma landInd_eq (m i j k : ℕ) (ω : JitterΩ) :
    Queue6.landInd θ X₀ m i j k ω =
      (candEv θ X₀ m i j k ∩
        {ω | valF θ X₀ k ω ∈ Ico (Queue6.Jlo X₀ m i) (Queue6.Jhi X₀ m j)}).indicator 1 ω := by
  classical
  unfold Queue6.landInd
  by_cases h : ω ∈ candEv θ X₀ m i j k ∩
      {ω | valF θ X₀ k ω ∈ Ico (Queue6.Jlo X₀ m i) (Queue6.Jhi X₀ m j)}
  · rw [indicator_of_mem h]
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    rw [if_pos ⟨h1, h2, h3, h4.1, h4.2⟩]; rfl
  · rw [indicator_of_notMem h, if_neg]
    rintro ⟨h1, h2, h3, h4, h5⟩
    exact h ⟨⟨h1, h2, h3⟩, h4, h5⟩

lemma candEv_adapted (m i j k : ℕ) :
    MeasurableSet[jitterFiltration k] (candEv θ X₀ m i j k) := by
  have hs := slotF_adapted hc (stageMeas hc) k
  have hH := HF_adapted hc (stageMeas hc) k
  refine (placedF_adapted hc (stageMeas hc) k).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le (measurable_const.sub (hH.div_const _)) hs
  · exact measurableSet_le hs (measurable_const.add (hH.div_const _))

/-- The bound `g_k = 1[cand] min(1, |J|/H(s_k))` on the conditional landing probability. -/
noncomputable def gLand (θ : ℝ) (X₀ : ℕ) (m i j k : ℕ) (ω : JitterΩ) : ℝ :=
  (candEv θ X₀ m i j k).indicator
    (fun ω => min 1 ((((j : ℝ) - i) / 2) / HF θ X₀ k ω)) ω

/-- **(F2) for the landing indicator**: `E[landInd_k | F_k] ≤ 1[cand] min(1, |J|/H(s_k))`. -/
theorem condExp_landInd_le {m i j : ℕ} (hij : i < j) (k : ℕ) :
    jitterMeasure[Queue6.landInd θ X₀ m i j k | jitterFiltration k] ≤ᵐ[jitterMeasure]
      gLand θ X₀ m i j k := by
  classical
  have hFle := jitterFiltration.le (Ω := JitterΩ) k
  have hC := candEv_adapted hc m i j k
  have hCm : MeasurableSet (candEv θ X₀ m i j k) := hFle _ hC
  have hH := HF_adapted hc (stageMeas hc) k
  have hval := valF_measurable hc (stageMeas hc) k
  set Jl := Queue6.Jlo X₀ m i
  set Jh := Queue6.Jhi X₀ m j
  set L := Queue6.landInd θ X₀ m i j k with hL
  have hLe : L = (candEv θ X₀ m i j k ∩ {ω | valF θ X₀ k ω ∈ Ico Jl Jh}).indicator 1 :=
    funext (landInd_eq m i j k)
  have hLS : MeasurableSet (candEv θ X₀ m i j k ∩
      {ω | valF θ X₀ k ω ∈ Ico Jl Jh}) := hCm.inter (hval measurableSet_Ico)
  have hLi : Integrable L jitterMeasure := by
    rw [hLe]; exact (integrable_const (1 : ℝ)).indicator hLS
  have hgm : StronglyMeasurable[jitterFiltration k] (gLand θ X₀ m i j k) := by
    refine Measurable.stronglyMeasurable ?_
    unfold gLand
    exact (measurable_const.min (measurable_const.div hH)).indicator hC
  have hg01 : ∀ ω, 0 ≤ gLand θ X₀ m i j k ω ∧
      gLand θ X₀ m i j k ω ≤ 1 := by
    intro ω
    unfold gLand
    by_cases hω : ω ∈ candEv θ X₀ m i j k
    · rw [indicator_of_mem hω]
      have hJ : 0 ≤ ((j : ℝ) - i) / 2 := by
        have : (i : ℝ) < j := by exact_mod_cast hij
        linarith
      exact ⟨le_min zero_le_one (div_nonneg hJ (HF_pos hc k ω).le), min_le_left _ _⟩
    · rw [indicator_of_notMem hω]; exact ⟨le_rfl, zero_le_one⟩
  have hgi : Integrable (gLand θ X₀ m i j k) jitterMeasure :=
    Integrable.of_bound (hgm.mono hFle).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg01 ω).1]; exact (hg01 ω).2)
  refine condExp_ae_le_of_setIntegral hFle hLi hgm hgi fun S hS => ?_
  have hSm : MeasurableSet S := hFle _ hS
  -- the law of the landing point
  set Φ : JitterΩ × ℝ → ℝ≥0∞ :=
    ((S ∩ candEv θ X₀ m i j k) ×ˢ Ico Jl Jh).indicator 1 with hΦ
  have hΦm : RankFull.JMeas (jitterFiltration k) Φ := by
    unfold RankFull.JMeas
    exact measurable_const.indicator
      (@MeasurableSet.prod _ _ (jitterFiltration k) _ _ _ (hS.inter hC) measurableSet_Ico)
  have hdens := law_dens hc k Φ hΦm
  -- the left side
  have hstage : ∀ᵐ ω ∂jitterMeasure, ω ∈ stageGood θ X₀ k := by
    have h0 := good_compl_null hc (k + 1)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_setOf_eq] at hω
    simp only [goodLt, mem_compl_iff, mem_iInter, not_forall]
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hω⟩
  have hlhs : ∫⁻ ω in S, ENNReal.ofReal (L ω) ∂jitterMeasure =
      ∫⁻ ω, (lawA θ X₀ k).indicator (fun ω => Φ (ω, valF θ X₀ k ω)) ω ∂jitterMeasure := by
    rw [← lintegral_indicator hSm]
    refine lintegral_congr_ae (hstage.mono fun ω hω => ?_)
    rw [hLe]
    by_cases hωC : ω ∈ candEv θ X₀ m i j k
    · have hA : ω ∈ lawA θ X₀ k := ⟨hωC.1, hω⟩
      rw [indicator_of_mem hA]
      by_cases hωS : ω ∈ S <;> by_cases hωv : valF θ X₀ k ω ∈ Ico Jl Jh <;>
        simp only [mem_Ico] at hωv <;> simp [hΦ, hωS, hωC, hωv]
    · have h0 : Φ (ω, valF θ X₀ k ω) = 0 := by
        simp [hΦ, hωC]
      have h1 : (candEv θ X₀ m i j k ∩ {ω | valF θ X₀ k ω ∈ Ico Jl Jh}).indicator
          (1 : JitterΩ → ℝ) ω = 0 := indicator_of_notMem (fun h => hωC h.1) _
      by_cases hA : ω ∈ lawA θ X₀ k
      · rw [indicator_of_mem hA, h0]
        by_cases hωS : ω ∈ S
        · rw [indicator_of_mem hωS, h1]; simp
        · rw [indicator_of_notMem hωS]
      · rw [indicator_of_notMem hA]
        by_cases hωS : ω ∈ S
        · rw [indicator_of_mem hωS, h1]; simp
        · rw [indicator_of_notMem hωS]
  -- the right side
  have hJlen : Jh - Jl = ((j : ℝ) - i) / 2 := by
    simp only [Jh, Jl, Queue6.Jhi, Queue6.Jlo]; ring
  have hrhs : ∀ ω, (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
      ∫⁻ t in RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)) ω ≤
      S.indicator (fun ω => ENNReal.ofReal (gLand θ X₀ m i j k ω)) ω := by
    intro ω
    by_cases hωS : ω ∈ S ∩ candEv θ X₀ m i j k
    · have hint : ∫⁻ t in RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t) =
          volume (Ico Jl Jh ∩ RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω)) := by
        have e : (fun t => Φ (ω, t)) = (Ico Jl Jh).indicator 1 := by
          funext t
          by_cases ht : t ∈ Ico Jl Jh <;> simp [hΦ, indicator, hωS, ht]
        rw [e, lintegral_indicator_one measurableSet_Ico, Measure.restrict_apply
          measurableSet_Ico]
      have hHp := HF_pos hc k ω
      set H := HF θ X₀ k ω
      have hv1 : volume (Ico Jl Jh ∩ RankFull.box (slotF θ X₀ k ω) H) ≤
          ENNReal.ofReal (Jh - Jl) := by
        rw [← Real.volume_Ico]; exact measure_mono inter_subset_left
      have hv2 : volume (Ico Jl Jh ∩ RankFull.box (slotF θ X₀ k ω) H) ≤ ENNReal.ofReal H := by
        have : volume (RankFull.box (slotF θ X₀ k ω) H) = ENNReal.ofReal H := by
          unfold RankFull.box; rw [Real.volume_Ico]; congr 1; ring
        rw [← this]; exact measure_mono inter_subset_right
      have hv : volume (Ico Jl Jh ∩ RankFull.box (slotF θ X₀ k ω) H) ≤
          ENNReal.ofReal (min H (Jh - Jl)) := by
        rw [ENNReal.ofReal_min]; exact le_min hv2 hv1
      calc (lawA θ X₀ k).indicator (fun ω => ENNReal.ofReal (HF θ X₀ k ω)⁻¹ *
            ∫⁻ t in RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t)) ω
          ≤ ENNReal.ofReal H⁻¹ * ∫⁻ t in RankFull.box (slotF θ X₀ k ω) H, Φ (ω, t) :=
            indicator_le_self _ _ ω
        _ ≤ ENNReal.ofReal H⁻¹ * ENNReal.ofReal (min H (Jh - Jl)) := by
            rw [hint]; exact mul_le_mul_left' hv _
        _ = ENNReal.ofReal (gLand θ X₀ m i j k ω) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hHp.le)]
            unfold gLand
            rw [indicator_of_mem hωS.2]
            congr 1
            rw [hJlen.symm, mul_min_of_nonneg _ _ (inv_nonneg.mpr hHp.le),
              inv_mul_cancel₀ hHp.ne', inv_mul_eq_div]
        _ = S.indicator (fun ω => ENNReal.ofReal (gLand θ X₀ m i j k ω)) ω := by
            rw [indicator_of_mem hωS.1]
    · have hz : ∫⁻ t in RankFull.box (slotF θ X₀ k ω) (HF θ X₀ k ω), Φ (ω, t) = 0 := by
        have e : (fun t => Φ (ω, t)) = 0 := by
          funext t; rw [hΦ]; exact indicator_of_notMem (fun h => hωS h.1) _
        rw [e]; exact lintegral_zero
      refine le_trans (indicator_le_self _ _ ω) ?_
      dsimp only
      rw [hz, mul_zero]
      exact zero_le _
  have hle : ∫⁻ ω in S, ENNReal.ofReal (L ω) ∂jitterMeasure ≤
      ∫⁻ ω in S, ENNReal.ofReal (gLand θ X₀ m i j k ω) ∂jitterMeasure := by
    rw [hlhs, ← lintegral_indicator hSm]
    exact hdens.trans (lintegral_mono hrhs)
  have hL0 : ∀ ω, 0 ≤ L ω := fun ω => by rw [hLe]; exact indicator_nonneg (fun _ _ => zero_le_one) _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hL0)
      hLi.aestronglyMeasurable.restrict,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => (hg01 ω).1)
      hgi.aestronglyMeasurable.restrict]
  refine ENNReal.toReal_mono ?_ hle
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in S, 1 ∂jitterMeasure) ?_ ?_
  · simp
  · exact lintegral_mono fun ω => by
      rw [ENNReal.ofReal_le_one]; exact (hg01 ω).2

/-- Almost surely every stage is good (`𝒩₌` is null). -/
lemma ae_stageGood : ∀ᵐ ω ∂jitterMeasure, ∀ k, ω ∈ stageGood θ X₀ k := by
  refine ae_all_iff.mpr fun k => ?_
  have h0 := good_compl_null hc (k + 1)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [mem_setOf_eq] at hω
  simp only [goodLt, mem_compl_iff, mem_iInter, not_forall]
  exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hω⟩

open Classical in
/-- **Lemma 6.1 / (F1)–(F2): the landing compensator is surely at most `μ̄(J)`** — the field
`land` of `Queue6.QueueInputs`. -/
theorem land_compensator {m i j : ℕ} (hJ : Queue6.AdmJ X₀ m i j) :
    ∀ᵐ ω ∂jitterMeasure, ∀ n,
      ∑ k ∈ Finset.range n,
        (jitterMeasure[Queue6.landInd θ X₀ m i j k | jitterFiltration k]) ω ≤
      Queue6.muBar X₀ m i j := by
  have h1 : ∀ᵐ ω ∂jitterMeasure, ∀ k,
      (jitterMeasure[Queue6.landInd θ X₀ m i j k | jitterFiltration k]) ω ≤
        gLand θ X₀ m i j k ω :=
    ae_all_iff.mpr fun k => condExp_landInd_le hc hJ.1 k
  filter_upwards [h1, ae_stageGood hc] with ω hω hg n
  refine (Finset.sum_le_sum fun k _ => hω k).trans ?_
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  set hstd := hc.std ω
  have hM : Mcl θ X₀ ω = hstd.limModel := Mcl_eq hc ω
  set P := Queue6.uS X₀ m with hPdef
  have hP : (X₀ : ℝ) ≤ P := by
    rw [hPdef, Queue6.uS]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := m)]
  set Hm := capH X₀ (P / 2) with hHm
  have hHm0 : 0 < Hm := by
    rw [hHm]; unfold capH; exact lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  set c := min 1 ((((j : ℝ) - i) / 2) / Hm) with hcdef
  have hij' : (i : ℝ) < j := by exact_mod_cast hJ.1
  have hc0 : 0 ≤ c := le_min zero_le_one (div_nonneg (by linarith) hHm0.le)
  set Fl := (Finset.range n).filter (fun k => ω ∈ candEv θ X₀ m i j k)
  have hgk : ∀ k ∈ Finset.range n, gLand θ X₀ m i j k ω ≤
      (candEv θ X₀ m i j k).indicator (fun _ => c) ω := by
    intro k _
    unfold gLand
    by_cases hk : ω ∈ candEv θ X₀ m i j k
    · rw [indicator_of_mem hk, indicator_of_mem hk]
      obtain ⟨-, h2, -⟩ := hk
      have hs := slotF_ge hc k ω
      have h4 := four_capH_le hX0 hX hs
      have hsP : 2 ^ m * (X₀ : ℝ) / 2 ≤ slotF θ X₀ k ω := by
        have : P ≤ Queue6.Jlo X₀ m i := by
          simp only [Queue6.Jlo]; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
        unfold HF at h2
        have : 2 ^ m * (X₀ : ℝ) = P := rfl
        linarith
      have hHk : Hm ≤ HF θ X₀ k ω := by
        rw [hHm]; unfold HF
        have e : P / 2 = 2 ^ m * (X₀ : ℝ) / 2 := rfl
        rw [e]; exact capH_half_le hX m hs hsP
      apply min_le_min le_rfl
      exact div_le_div_of_nonneg_left (by linarith) hHm0 hHk
    · rw [indicator_of_notMem hk, indicator_of_notMem hk]
  refine (Finset.sum_le_sum hgk).trans ?_
  have hsum : ∑ k ∈ Finset.range n, (candEv θ X₀ m i j k).indicator (fun _ => c) ω =
      (Fl.card : ℝ) * c := by
    simp only [indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  -- the candidate count
  have hcard := cand_card_le hstd (U := Ucl ω) hJ Fl (fun k hk => by
    have hk' := (Finset.mem_filter.mp hk).2
    obtain ⟨h1, h2, h3⟩ := hk'
    have hu := hg k
    simp only [stageGood, mem_setOf_eq, DF] at hu
    simp only [HF, slotF] at h2 h3
    unfold slotF at hu
    rw [hM] at h1 h2 h3 hu
    exact ⟨h1, hu, h2, h3⟩)
  unfold Queue6.muBar
  rw [← hPdef]
  have e : capH X₀ (P / 2) = Hm := rfl
  rw [e, ← hcdef]
  exact mul_le_mul_of_nonneg_right hcard hc0

end Prob

end BModel
