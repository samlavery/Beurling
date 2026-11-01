module

public import RequestProject.BSCert.RankinKChunks0
public import RequestProject.BSCert.RankinKChunks1
public import RequestProject.BSCert.RankinKChunks2
public import RequestProject.BSCert.RankinKChunks3
public import RequestProject.BSCert.RankinKChunks4

/-!
# `rankin_R.py`, head sum for `σ = 0.69`, kernel-checked

`∑_{p ≤ 10⁵} (-log(1 - p^{-0.69}) - p^{-0.69}) ≤ toR (rkC 101)` (`head69K`), from the 100
kernel-checked chunks of `RankinKChunks*`, and the final comparison with `0.77` (`final69K`).
-/

@[expose] public section

namespace BSCert.Rankin

open FX BSCert.FiniteN Finset

lemma rk_last : K.sumUp (termHiK 69 100) 1 100000 (rkC 100) = rkC 101 := by decide +kernel

lemma rk_chunks : ∀ k < 100, K.sumUp (termHiK 69 100) 1000 (1000 * k) (rkC k) = rkC (k + 1) := by
  intro k hk
  interval_cases k
  exacts [rk_chunk0, rk_chunk1, rk_chunk2, rk_chunk3, rk_chunk4, rk_chunk5, rk_chunk6, rk_chunk7, rk_chunk8, rk_chunk9, rk_chunk10, rk_chunk11, rk_chunk12, rk_chunk13, rk_chunk14, rk_chunk15, rk_chunk16, rk_chunk17, rk_chunk18, rk_chunk19, rk_chunk20, rk_chunk21, rk_chunk22, rk_chunk23, rk_chunk24, rk_chunk25, rk_chunk26, rk_chunk27, rk_chunk28, rk_chunk29, rk_chunk30, rk_chunk31, rk_chunk32, rk_chunk33, rk_chunk34, rk_chunk35, rk_chunk36, rk_chunk37, rk_chunk38, rk_chunk39, rk_chunk40, rk_chunk41, rk_chunk42, rk_chunk43, rk_chunk44, rk_chunk45, rk_chunk46, rk_chunk47, rk_chunk48, rk_chunk49, rk_chunk50, rk_chunk51, rk_chunk52, rk_chunk53, rk_chunk54, rk_chunk55, rk_chunk56, rk_chunk57, rk_chunk58, rk_chunk59, rk_chunk60, rk_chunk61, rk_chunk62, rk_chunk63, rk_chunk64, rk_chunk65, rk_chunk66, rk_chunk67, rk_chunk68, rk_chunk69, rk_chunk70, rk_chunk71, rk_chunk72, rk_chunk73, rk_chunk74, rk_chunk75, rk_chunk76, rk_chunk77, rk_chunk78, rk_chunk79, rk_chunk80, rk_chunk81, rk_chunk82, rk_chunk83, rk_chunk84, rk_chunk85, rk_chunk86, rk_chunk87, rk_chunk88, rk_chunk89, rk_chunk90, rk_chunk91, rk_chunk92, rk_chunk93, rk_chunk94, rk_chunk95, rk_chunk96, rk_chunk97, rk_chunk98, rk_chunk99]

lemma rk_prefix : ∀ k ≤ 100, K.sumUp (termHiK 69 100) (1000 * k) 0 0 = rkC k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [show 1000 * (k + 1) = 1000 * k + 1000 by ring, K.sumUp_add, ih (by omega), zero_add]
    exact rk_chunks k (by omega)

/-- The head sum for `σ = 0.69`, kernel-checked. -/
theorem head69K : ∑ p ∈ (range (100000 + 1)).filter Nat.Prime, rTerm ((69 : ℕ) / (100 : ℕ) : ℝ) p ≤
    toR (rkC 101) := by
  have hσ : (1 / 2 : ℝ) ≤ ((69 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) := by norm_num
  have h := K.sumUp_spec (termHiK 69 100) (fun p => if p.Prime then rTerm ((69 : ℕ) / (100 : ℕ) : ℝ) p else 0)
    (termHiK_spec (by norm_num) hσ) 100001 0 0
  rw [toR_zero, zero_add, zero_add, ← Finset.range_eq_Ico, ← Finset.sum_filter] at h
  have e : K.sumUp (termHiK 69 100) 100001 0 0 = rkC 101 := by
    rw [show 100001 = 1000 * 100 + 1 by norm_num, K.sumUp_add, rk_prefix 100 le_rfl, zero_add]
    exact rk_last
  rw [e] at h
  exact h

lemma final69_int : 100000000 * rkC 101 + 829545 * ZI ≤ 77000000 * ZI := by decide +kernel

/-- The final comparison: head sum plus the tail bound is at most `0.77`. -/
theorem final69K :
    toR (rkC 101) + (1 / 2 + (9 / 25000) / (1 - 9 / 25000)) *
      ((63 / 5000) / (2 * (2 * (69 / 100) - 1))) ≤ (77 / 100 : ℝ) := by
  have h := toR_le_toR.mpr final69_int
  have e1 : toR (100000000 * rkC 101 + 829545 * ZI) = 100000000 * toR (rkC 101) + 829545 := by
    unfold toR; push_cast; field_simp [ZR_pos.ne']
  have e2 : toR (77000000 * ZI) = 77000000 := by unfold toR; push_cast; field_simp [ZR_pos.ne']
  rw [e1, e2] at h
  norm_num
  linarith

end BSCert.Rankin
