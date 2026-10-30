module

public import RequestProject.BSCert.FX.RTab

/-!
# Certification of the sparse `r_low` table

`chainOK` of the 2949 entries of `rtabF` is checked by the kernel in 15 blocks of 200
consecutive pairs (one `exp` evaluation per pair), and the first entry is checked against the
exact value `r(2) = 1/(2(1 - log 2))`. Hence `rtabF_ok : TabOKF r rtabF` for every `r`
satisfying `DickmanRatioFacts`.
-/

@[expose] public section

namespace BSCert.FX

/-- `chainOK` in terms of consecutive pairs. -/
lemma chainOK_iff : ∀ (l : List REntry), chainOK l = true ↔
    ∀ i (h : i + 1 < l.length), pairOK (l[i]'(by omega)) (l[i + 1]) = true
  | [] => by simp [chainOK]
  | [_] => by simp [chainOK]
  | e :: f :: rest => by
    rw [chainOK, Bool.and_eq_true, chainOK_iff (f :: rest)]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ i => simpa using h2 i (by simp at hi ⊢; omega)
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      simpa using h (i + 1) (by simp at hi ⊢; omega)

/-- The table as a list. -/
def rtabL : List REntry := rtabF.toList

/-- Block `b`: the entries `200 b, …, 200 b + 200`. -/
def rblk (b : ℕ) : List REntry := (rtabL.drop (200 * b)).take 201

lemma chainOK_of_blocks (nb : ℕ) (hlen : rtabL.length ≤ 200 * nb + 1)
    (h : ∀ b < nb, chainOK (rblk b) = true) : chainOK rtabL = true := by
  rw [chainOK_iff]
  intro i hi
  have hb : i / 200 < nb := by omega
  have hc := (chainOK_iff _).mp (h (i / 200) hb) (i % 200) (by
    unfold rblk; simp only [List.length_take, List.length_drop]; omega)
  unfold rblk at hc
  simp only [List.getElem_take, List.getElem_drop] at hc
  have e1 : 200 * (i / 200) + i % 200 = i := Nat.div_add_mod i 200
  have e2 : 200 * (i / 200) + (i % 200 + 1) = i + 1 := by omega
  simp only [e1, e2] at hc
  exact hc

lemma rtabL_length : rtabL.length = 2949 := by decide +kernel

lemma blk0 : chainOK (rblk 0) = true := by decide +kernel
lemma blk1 : chainOK (rblk 1) = true := by decide +kernel
lemma blk2 : chainOK (rblk 2) = true := by decide +kernel
lemma blk3 : chainOK (rblk 3) = true := by decide +kernel
lemma blk4 : chainOK (rblk 4) = true := by decide +kernel
lemma blk5 : chainOK (rblk 5) = true := by decide +kernel
lemma blk6 : chainOK (rblk 6) = true := by decide +kernel
lemma blk7 : chainOK (rblk 7) = true := by decide +kernel
lemma blk8 : chainOK (rblk 8) = true := by decide +kernel
lemma blk9 : chainOK (rblk 9) = true := by decide +kernel
lemma blk10 : chainOK (rblk 10) = true := by decide +kernel
lemma blk11 : chainOK (rblk 11) = true := by decide +kernel
lemma blk12 : chainOK (rblk 12) = true := by decide +kernel
lemma blk13 : chainOK (rblk 13) = true := by decide +kernel
lemma blk14 : chainOK (rblk 14) = true := by decide +kernel

lemma rtab_chain : chainOK rtabL = true :=
  chainOK_of_blocks 15 (by rw [rtabL_length]; norm_num) (by
    intro b hb
    interval_cases b
    exacts [blk0, blk1, blk2, blk3, blk4, blk5, blk6, blk7, blk8, blk9, blk10, blk11, blk12,
      blk13, blk14])

/-- The first entry: `(2, a₀)` with `1 ≤ a₀ ≤ r(2)`. -/
def headOK : Bool :=
  match rtabL with
  | e :: _ => decide (e.1 = 2) && decide (ZI ≤ e.2) &&
      (match Ex.feval rExactEx [⟨2 * ZI, 2 * ZI⟩] with
       | some I => decide (e.2 ≤ I.lo)
       | none => false)
  | [] => false

lemma headOK_true : headOK = true := by decide +kernel

theorem rtabF_ok {r : ℝ → ℝ} (hr : DickmanRatioFacts r) : TabOKF r rtabF := by
  have hc := rtab_chain
  have hh := headOK_true
  unfold TabOKF
  change ∀ g ∈ rtabL, _
  unfold headOK at hh
  split at hh
  · rename_i e rest heq
    rw [heq] at hc ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    obtain ⟨⟨h2, hZ⟩, hI⟩ := hh
    split at hI
    · rename_i I hIe
      have hmem := Ex.feval_sound rExactEx [toR (2 * ZI)] _ I
        (List.Forall₂.cons (mem_pt _) List.Forall₂.nil) hIe
      have e2 : toR (2 * ZI) = 2 := by
        unfold toR; push_cast; rw [mul_div_assoc, div_self ZR_pos.ne', mul_one]
      rw [e2] at hmem
      simp only [rExactEx, Ex.eval, List.getD_cons_zero] at hmem
      have hr2 := hr.exact_one_two 2 (by norm_num) le_rfl
      have he : RInv r e.1 e.2 := by
        refine ⟨by rw [← toR_ZI]; exact toR_le_toR.mpr hZ, ?_⟩
        rw [h2]
        push_cast
        rw [hr2]
        push_cast at hmem
        exact (toR_le_toR.mpr (of_decide_eq_true hI)).trans hmem.1
      exact chainOK_spec hr rest e hc (by omega) he
    · cases hI
  · cases hh

end BSCert.FX
