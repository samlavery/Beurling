module

public import RequestProject.BSCert.AuxDefs
public import RequestProject.BSCert.FX.RTabCert
public import RequestProject.BSCert.FX.Cover
public import RequestProject.BSCert.FX.Glue

/-!
# The one-variable checks of `aux_cert_arb.py`, in fixed point (kernel-checked)

The cell tests of `AuxDefs` for the fixed-point arithmetic `BSCert.FX` (same expressions
`cAEx`, `lemVEx`, `lemVExtEx`; `r` enclosed with the sparse table `rtabF`), with soundness.
The covers (explicit break points, `FX.coverL`) are in `AuxKCovers.lean`.
-/

@[expose] public section

namespace BSCert

open FX Ex

/-- Cell test for check (1). -/
def cACellF (a b : ℤ) : Bool :=
  match rEncF rtabF a b, rEncF rtabF (a - ZI) (b - ZI) with
  | some R, some R0 => fcheckPos cAEx [⟨a, b⟩, R, R0]
  | _, _ => false

/-- Cell test for check (2). -/
def lemVCellF (a b : ℤ) : Bool :=
  match rEncF rtabF a b, rEncF rtabF (Max.max (a - ZI) ZI) (Max.max (b - ZI) ZI) with
  | some R, some R0 => fcheckPos lemVEx [⟨a, b⟩, R, R0]
  | _, _ => false

/-- Cell test for check (3). -/
def lemVExtCellF (a b : ℤ) : Bool :=
  match rEncF rtabF a b with
  | some R => fcheckPos lemVExtEx [⟨a, b⟩, R]
  | none => false

lemma cACellF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (a b : ℤ) (h : cACellF a b = true)
    (u : ℝ) (hu1 : toR a ≤ u) (hu2 : u ≤ toR b) : 0 < cAMargin r u := by
  have ht := rtabF_ok hr
  unfold cACellF at h
  split at h
  · rename_i R R0 hR hR0
    rw [← cAEx_eval]
    refine fcheckPos_sound ?_ h
    refine List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEncF_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEncF_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))
    · rw [toR_sub, toR_ZI]; linarith
    · rw [toR_sub, toR_ZI]; linarith
  · cases h

lemma lemVCellF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (a b : ℤ)
    (h : lemVCellF a b = true) (u : ℝ) (hu1 : toR a ≤ u) (hu2 : u ≤ toR b) :
    0 < lemVLHS r u := by
  have ht := rtabF_ok hr
  unfold lemVCellF at h
  split at h
  · rename_i R R0 hR hR0
    rw [← lemVEx_eval]
    refine fcheckPos_sound ?_ h
    refine List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEncF_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEncF_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))
    · rw [FI.toR_max, toR_sub, toR_ZI]; exact max_le_max (by linarith) le_rfl
    · rw [FI.toR_max, toR_sub, toR_ZI]; exact max_le_max (by linarith) le_rfl
  · cases h

lemma lemVExtCellF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) (a b : ℤ)
    (h : lemVExtCellF a b = true) (u : ℝ) (hu1 : toR a ≤ u) (hu2 : u ≤ toR b) :
    0 < lemVExtLHS r u := by
  have ht := rtabF_ok hr
  unfold lemVExtCellF at h
  split at h
  · rename_i R hR
    rw [← lemVExtEx_eval]
    refine fcheckPos_sound ?_ h
    exact List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEncF_sound hr ht hR hu1 hu2)
      List.Forall₂.nil)
  · cases h

/-- `toR (c · 2^128) = c`. -/
lemma toR_mulZ (c : ℤ) : toR (c * ZI) = (c : ℝ) := by
  unfold toR; push_cast; field_simp [ZR_pos.ne']

end BSCert
