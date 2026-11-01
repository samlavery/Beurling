module

public import RequestProject.Beurling.Noise.BridgeSIDecomp
public import RequestProject.Beurling.GenDyadic

/-!
# Lemma 5.32 (A): the `m`-sum in dyadic blocks

Group the cofactors `m` into the blocks `(M_k, 2M_k]`, `M_k = 2^k M₀`, `M₀ = ½√(N/t)`. In a block,
`P⁺(m) ≤ N(1+η)/m < 2N/M_k` and `log(N/m) ≥ σ_k = log(N/(2M_k))`, so (`SIblocks_le`)

  `∑_m 1/(m log(N/m)) ≤ ∑_k W_t(M_k; 2N/M_k)/σ_k`,

with `W_t(M_k; 2N/M_k) = Wsm t M_k u_k`, `u_k = log M_k/log(2N/M_k)`.
-/

@[expose] public section

open Real Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- The dyadic index of `m`: `M₀ 2^k < m ≤ M₀ 2^{k+1}`. -/
noncomputable def SIidx (M0 : ℝ) (m : ℕ →₀ ℕ) : ℕ := GenDyadic.dIdx (P.val m / M0)

/-- `u_k = log M_k/log(2N/M_k)`. -/
noncomputable def SIu (N Mk : ℝ) : ℝ := Real.log Mk / Real.log (2 * N / Mk)

/-- **The `m`-sum in dyadic blocks.** -/
theorem SIblocks_le {t N η P1 M0 : ℝ} (hM0 : 1 ≤ M0) (hP1 : 4 ≤ P1) (hη1 : η ≤ 1)
    (hN : 0 < N)
    (hM : ∀ m ∈ P.SIcof t N η P1, 2 * M0 ≤ P.val m) :
    ∑ m ∈ P.SIcof t N η P1, 1 / P.val m * (1 / Real.log (N / P.val m)) ≤
      ∑ k ∈ (P.SIcof t N η P1).image (P.SIidx M0),
        P.Wsm t (M0 * 2 ^ k) (SIu N (M0 * 2 ^ k)) / Real.log (N / (2 * (M0 * 2 ^ k))) := by
  classical
  set M := P.SIcof t N η P1
  have hblock : ∀ m ∈ M, M0 * 2 ^ P.SIidx M0 m < P.val m ∧
      P.val m ≤ 2 * (M0 * 2 ^ P.SIidx M0 m) := by
    intro m hm
    have hM0p : 0 < M0 := by linarith
    have h1 : 1 < P.val m / M0 := by
      rw [lt_div_iff₀ hM0p]; linarith [hM m hm]
    obtain ⟨hl, hr⟩ := GenDyadic.dIdx_spec h1
    unfold SIidx
    constructor
    · rw [lt_div_iff₀ hM0p] at hl; linarith
    · rw [div_le_iff₀ hM0p] at hr; rw [pow_succ] at hr; linarith
  have hmemM : ∀ m ∈ M, P.val m ≤ N * (1 + η) / P1 ∧ √(N / t) ≤ P.val m ∧ P.IsDense t m ∧
      ∀ i ∈ m.support, P.p i ≤ N * (1 + η) / P.val m := by
    intro m hm
    simp only [M, SIcof, mem_filter, mem_elems] at hm
    exact ⟨hm.1, hm.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem (P.SIidx M0) hm)]
  refine Finset.sum_le_sum fun k hk => ?_
  set Mk := M0 * 2 ^ k with hMk
  have hMk1 : 1 ≤ Mk := by
    rw [hMk]; exact one_le_mul_of_one_le_of_one_le hM0 (one_le_pow₀ (by norm_num))
  have hMk0 : 0 < Mk := by linarith
  set F := M.filter (fun m => P.SIidx M0 m = k)
  -- the block is non-empty, so `2 M_k < N`
  obtain ⟨m0, hm0, hk0⟩ := Finset.mem_image.mp hk
  have hσpos : 2 * Mk < N := by
    obtain ⟨h1, -⟩ := hblock m0 hm0
    rw [hk0] at h1
    obtain ⟨h2, -⟩ := hmemM m0 hm0
    have h3 : N * (1 + η) / P1 ≤ N / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hσ : 0 < Real.log (N / (2 * Mk)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have hz1 : 1 < 2 * N / Mk := by rw [lt_div_iff₀ hMk0]; linarith
  have hlz : 0 < Real.log (2 * N / Mk) := Real.log_pos hz1
  calc ∑ m ∈ F, 1 / P.val m * (1 / Real.log (N / P.val m))
      ≤ ∑ m ∈ F, 1 / P.val m * (1 / Real.log (N / (2 * Mk))) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmM := (mem_filter.mp hm).1
        have hkm := (mem_filter.mp hm).2
        obtain ⟨-, h2⟩ := hblock m hmM
        rw [hkm] at h2
        have hv := P.val_pos m
        apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_one hv.le)
        apply one_div_le_one_div_of_le hσ
        apply Real.log_le_log (by positivity)
        exact div_le_div_of_nonneg_left hN.le hv h2
    _ = (∑ m ∈ F, 1 / P.val m) / Real.log (N / (2 * Mk)) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ P.Wsm t Mk (SIu N Mk) / Real.log (N / (2 * Mk)) := by
        apply div_le_div_of_nonneg_right _ hσ.le
        unfold Wsm
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          have hmM := (mem_filter.mp hm).1
          have hkm := (mem_filter.mp hm).2
          obtain ⟨h1, h2⟩ := hblock m hmM
          rw [hkm] at h1 h2
          obtain ⟨-, -, hd, hpr⟩ := hmemM m hmM
          simp only [mem_filter, mem_elems]
          refine ⟨h2, h1, hd, fun i hi => ?_⟩
          have hpi := hpr i hi
          have hv := P.val_pos m
          have hpz : P.p i ≤ 2 * N / Mk := by
            refine hpi.trans ?_
            rw [div_le_div_iff₀ hv hMk0]
            have hNM := mul_pos hN hMk0
            have e1 : N * (1 + η) * Mk ≤ 2 * N * Mk := by nlinarith
            have e2 : 2 * N * Mk ≤ 2 * N * P.val m := by nlinarith
            linarith
          have hlp : Real.log (P.p i) ≤ Real.log (2 * N / Mk) :=
            Real.log_le_log (P.p_pos i) hpz
          unfold SIu
          have hlM : 0 ≤ Real.log Mk := Real.log_nonneg hMk1
          calc Real.log Mk / Real.log (2 * N / Mk) * Real.log (P.p i)
              ≤ Real.log Mk / Real.log (2 * N / Mk) * Real.log (2 * N / Mk) :=
                mul_le_mul_of_nonneg_left hlp (div_nonneg hlM hlz.le)
            _ = Real.log Mk := by field_simp
        · intro m _ _; exact div_nonneg zero_le_one (P.val_pos m).le

end BeurlingSystem

end
