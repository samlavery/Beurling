module

public import RequestProject.Beurling.Noise.LemSRankin

/-!
# Lemma 5.21 (filtered cofactor weight)

For a Beurling system `P` satisfying (HBS) on `[1, Z]`, decision times `t` with
`DecidedSmall` (a prime decided before slot `2v` is `≤ 3v`), and `log 3v ≥ 10⁸`:

* (i) `HBS.lemS_i` : `ω_y(v) ≤ 1` (paper: `≤ 1.2`);
* (ii) `HBS.lemS_ii_dickman` (`ω_y(v) ≤ C₀ ρ(u_y) e^{a_V}`, `a_V ≤ 13 u_y log(u_y+2)/log 3v`,
  `aV_uY_le`), `HBS.lemS_ii_le30`, `HBS.lemS_ii_gt30`, and for `u_y > log 3v` Rankin's bound
  `HBS.lemS_rankin` (`ω_y(v) ≤ 5 (log 3v)^{1.65} e^{-u_y/2}`);
* (iii) `HBS.lemS_iii` : `∑_{Y=2^k ≥ v} log(2Y) sup_{[Y,2Y)} ω_y(v) ≤ 10 (log 3v)²`, for the
  dyadic `Y` with `2Y ≤ vZ` (where `ω` reads `𝒩` only on `[1, Z]`);
* `HBS.lemma_5_21` : the three parts together.

Differences from the paper's text, all in the safe direction: (i) gives `1` instead of `1.2`;
(ii) gives `C₀` instead of `2C₀` in the Dickman bound; (iii) is proved with the cruder decay
`ρ(u) ≤ e^{1-u}` (no `1/Γ` integrals), which the factor `2` saved in (ii) pays for.
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- **Lemma 5.21(iii)**: for `log 3v ≥ 10⁸`, every partial sum over the dyadic `Y = 2^k ≥ v`
(with `2Y ≤ vZ`) of `log(2Y) sup_{y ∈ [Y, 2Y)} ω_y(v)` is at most `C'_S (log 3v)²`,
`C'_S = 10`. -/
theorem lemS_iii (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ} (hd : P.DecidedSmall t v)
    (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) (N : ℕ) :
    ∑ k ∈ (Finset.range N).filter (fun k => v ≤ (2 : ℝ) ^ k ∧ 2 * 2 ^ k ≤ v * Z),
        Real.log (2 * 2 ^ k) * (⨆ y : Set.Ico ((2 : ℝ) ^ k) (2 * 2 ^ k), P.omegaW t y v) ≤
      10 * Real.log (3 * v) ^ 2 := by
  set L := Real.log (3 * v) with hLdef
  set K := (Finset.range N).filter (fun k => v ≤ (2 : ℝ) ^ k ∧ 2 * 2 ^ k ≤ v * Z)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstep : ∀ k ∈ K, Real.log (2 * 2 ^ k) *
      (⨆ y : Set.Ico ((2 : ℝ) ^ k) (2 * 2 ^ k), P.omegaW t y v) ≤
      ((k : ℝ) + 1) * Real.log 2 * LemS.OmB L (Real.log ((2 : ℝ) ^ k / (2 * v))) := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have e : Real.log (2 * 2 ^ k) = ((k : ℝ) + 1) * Real.log 2 := by
      rw [← pow_succ', Real.log_pow]; push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (iSup_omega_le h hd hv hL (by positivity) hk'.2)
      (by positivity)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not K
    (fun k => Real.log ((2 : ℝ) ^ k / (2 * v)) < L)]
  have hA : ∑ k ∈ K.filter (fun k => Real.log ((2 : ℝ) ^ k / (2 * v)) < L),
      ((k : ℝ) + 1) * Real.log 2 * LemS.OmB L (Real.log ((2 : ℝ) ^ k / (2 * v))) ≤ 3 * L ^ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun (k : ℕ) hk => ?_)))
      (LemS.partA_le hv hL _ ?_)
    · have := (Finset.mem_filter.mp hk).2
      show _ = ((k : ℝ) + 1) * Real.log 2
      unfold LemS.OmB; rw [if_pos this, mul_one]
    exact (fun k hk => ⟨(Finset.mem_filter.mp
      (Finset.mem_filter.mp hk).1).2.1, (Finset.mem_filter.mp hk).2⟩)
  have hB : ∑ k ∈ K.filter (fun k => ¬ Real.log ((2 : ℝ) ^ k / (2 * v)) < L),
      ((k : ℝ) + 1) * Real.log 2 * LemS.OmB L (Real.log ((2 : ℝ) ^ k / (2 * v))) ≤
      3.2 * L ^ 2 + 1 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun (k : ℕ) hk => ?_)))
      (LemS.partB_le hv hL _ (fun k hk => le_of_not_gt (Finset.mem_filter.mp hk).2))
    have := (Finset.mem_filter.mp hk).2
    unfold LemS.OmB; rw [if_neg this]
  have hL1 : 1 ≤ L ^ 2 := by nlinarith
  linarith

/-- **Lemma 5.21 (filtered cofactor weight)** for a Beurling system satisfying (HBS) on
`[1, Z]`, decision times with `DecidedSmall t v`, and `log 3v ≥ 10⁸` (in the paper `v ≥ X₀/2`):
(i) `ω_y(v) ≤ 1.2`; (ii) the Dickman bound for `1 ≤ u_y ≤ log 3v`, its numerical forms for
`u_y ≤ 30` and `30 < u_y ≤ log 3v`, and Rankin's bound for `u_y > log 3v`; (iii) the dyadic
sum `≤ 10 (log 3v)²`. Each `ω_y(v)` is evaluated with `y/v ≤ Z`. -/
theorem lemma_5_21 (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ} (hd : P.DecidedSmall t v)
    (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) :
    (∀ y, 0 < y → y / v ≤ Z → P.omegaW t y v ≤ 1.2) ∧
    (∀ y, 0 < y → y / v ≤ Z → 1 ≤ uY y v → uY y v ≤ Real.log (3 * v) →
      P.omegaW t y v ≤ BSaias.C0 * Dickman.rho (uY y v) *
        Real.exp (BSaias.aV (Real.log (y / (2 * v))) (uY y v)) ∧
      BSaias.aV (Real.log (y / (2 * v))) (uY y v) ≤
        13 * uY y v * Real.log (uY y v + 2) / Real.log (3 * v)) ∧
    (∀ y, 0 < y → y / v ≤ Z → uY y v ≤ 30 →
      P.omegaW t y v ≤ 2 * BSaias.C0 * Dickman.rho (uY y v) * Real.exp 0.02) ∧
    (∀ y, 0 < y → y / v ≤ Z → 30 < uY y v → uY y v ≤ Real.log (3 * v) →
      P.omegaW t y v ≤ 2 * BSaias.C0 * Real.exp (-(0.7 * uY y v * Real.log (uY y v)))) ∧
    P.LemSRankin Z t v ∧
    (∀ N : ℕ, ∑ k ∈ (Finset.range N).filter (fun k => v ≤ (2 : ℝ) ^ k ∧ 2 * 2 ^ k ≤ v * Z),
        Real.log (2 * 2 ^ k) * (⨆ y : Set.Ico ((2 : ℝ) ^ k) (2 * 2 ^ k), P.omegaW t y v) ≤
      10 * Real.log (3 * v) ^ 2) := by
  refine ⟨fun y _ hZ => (lemS_i h t hv hZ).trans (by norm_num),
    fun y hy hZ hu1 hu2 => ⟨lemS_ii_dickman h hd hv (by linarith) hy hu1 hu2 hZ,
      aV_uY_le (by linarith) hu1⟩,
    fun y hy hZ hu => lemS_ii_le30 h hd hv hL hy hu hZ,
    fun y hy hZ hu1 hu2 => lemS_ii_gt30 h hd hv hL hy hu1 hu2 hZ,
    lemS_rankin h hd hv hL, fun N => lemS_iii h hd hv hL N⟩

end HBS

end BeurlingSystem

end
