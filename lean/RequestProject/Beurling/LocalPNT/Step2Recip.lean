module

public import RequestProject.Beurling.LocalPNT.ZetaJOne

/-!
# Step 2 of the proof of Theorem 5.24: `∫_{[1,y]} dΠ/u ≤ log log y + 7`

From Lemma 5.1(ii)–(iv): `∑_{p ≤ y} 1/p ≤ log log y + 5.3`, and the prime powers `p^k`, `k ≥ 2`,
contribute at most `(S(y) - S_p(y))/(2 log 2) ≤ 2.2/(2 log 2) ≤ 1.6`. (The paper has `+ 4.5`; the
constant only enters `log K` through `Λ^{0.3}`-room.) Also `LPHyp` passes to smaller heights.
-/

@[expose] public section

open Set Real Finset Construction

namespace LocalPNT

namespace LPHyp

variable {P : BeurlingSystem} {θ : ℝ} {X₀ : ℕ} {α γ xp : ℕ → ℝ} {Xm y : ℝ} {D0 : ℝ → ℝ}

/-- **(LP-a) on `[1, y]` gives (LP-a) on `[1, v]`** for `X₀ ≤ v ≤ y`. -/
theorem mono (h : LPHyp P θ X₀ α γ xp Xm y D0) {v : ℝ} (hv : (X₀ : ℝ) ≤ v) (hvy : v ≤ y) :
    LPHyp P θ X₀ α γ xp Xm v D0 where
  theta_mem := h.theta_mem
  logX := h.logX
  even := h.even
  alpha_le := h.alpha_le
  xp_zero := h.xp_zero
  xp_succ := h.xp_succ
  T0_mono := h.T0_mono
  Xm_ge := h.Xm_ge
  Xm_le := h.Xm_le
  y_ge := hv
  lpa_low := h.lpa_low
  lpa_high := fun u h1 h2 => h.lpa_high u h1 (h2.trans hvy)

variable (h : LPHyp P θ X₀ α γ xp Xm y D0)
include h

/-- `∫_{[1,y]} dΠ/u = ∑_{p^k ≤ y} 1/(k p^k) ≤ log log y + 7`. -/
theorem piRecip_le : piRecip P y ≤ Real.log (Real.log y) + 7 := by
  have H := h.hbs
  have hy1 : 1 ≤ y := le_trans h.one_le_X0 h.y_ge
  unfold piRecip
  rw [← Finset.sum_filter_add_sum_filter_not (P.pps y) (fun jk => jk.2 = 0)]
  -- `k = 0`: the primes
  have h0 : ∑ jk ∈ (P.pps y).filter (fun jk => jk.2 = 0),
      1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1)) = ∑ j ∈ P.primesLe y, 1 / P.p j := by
    refine Finset.sum_bij (fun jk _ => jk.1) ?_ ?_ ?_ ?_
    · intro jk hjk
      rw [Finset.mem_filter, BeurlingSystem.mem_pps] at hjk
      rw [BeurlingSystem.mem_primesLe]
      have := hjk.1; rw [hjk.2] at this; simpa using this
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      exact Prod.ext hab (by rw [ha.2, hb.2])
    · intro j hj
      refine ⟨(j, 0), ?_, rfl⟩
      rw [Finset.mem_filter, BeurlingSystem.mem_pps]
      exact ⟨by simpa using (BeurlingSystem.mem_primesLe P).mp hj, rfl⟩
    · intro jk hjk
      rw [Finset.mem_filter] at hjk
      rw [hjk.2]; simp
  -- `k ≥ 1`: bounded by `(S - S_p)/(2 log 2)`
  have hS := (H.mertensS_sub_log_mem hy1 le_rfl).2
  have hSp := (H.Sp_sub_log_mem hy1 le_rfl).1
  have hid := P.mertensS_eq_Sp_add y
  have hl2 := Real.log_two_gt_d9
  have h1 : ∑ jk ∈ (P.pps y).filter (fun jk => ¬ jk.2 = 0),
      1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1)) ≤
      (1 / (2 * Real.log 2)) * ∑ jk ∈ (P.pps y).filter (fun jk => 1 ≤ jk.2),
        Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) := by
    rw [Finset.mul_sum]
    have hf : (P.pps y).filter (fun jk => ¬ jk.2 = 0) = (P.pps y).filter (fun jk => 1 ≤ jk.2) := by
      ext jk; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.one_le_iff_ne_zero.mpr h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.one_le_iff_ne_zero.mp h2⟩
    rw [hf]
    refine Finset.sum_le_sum fun jk hjk => ?_
    rw [Finset.mem_filter, BeurlingSystem.mem_pps] at hjk
    have hp2 : 2 ≤ P.p jk.1 := h.p_ge_two'
      ((le_self_pow₀ (P.one_lt _).le (Nat.succ_ne_zero _)).trans hjk.1)
    have hlp : Real.log 2 ≤ Real.log (P.p jk.1) := Real.log_le_log (by norm_num) hp2
    have hpk : 0 < P.p jk.1 ^ (jk.2 + 1) := P.pp_pos jk
    have hk : (2 : ℝ) ≤ (jk.2 : ℝ) + 1 := by have := hjk.2; exact_mod_cast (by omega : 2 ≤ jk.2 + 1)
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * Real.log 2 ≤ ((jk.2 : ℝ) + 1) * Real.log (P.p jk.1) := by nlinarith
    nlinarith
  have hsum0 : 0 ≤ ∑ jk ∈ (P.pps y).filter (fun jk => 1 ≤ jk.2),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) :=
    Finset.sum_nonneg fun jk _ => div_nonneg (P.log_p_nonneg _) (P.pp_pos jk).le
  have h2 : (1 / (2 * Real.log 2)) * ∑ jk ∈ (P.pps y).filter (fun jk => 1 ≤ jk.2),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) ≤ 1.6 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  have h3 := h.sum_inv_p_le
  rw [h0]
  linarith

end LPHyp

end LocalPNT

end
