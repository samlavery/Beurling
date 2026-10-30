module

public import RequestProject.BSCert.Z2Cover
public import RequestProject.BSCert.FX.RTabCert
public import RequestProject.BSCert.FX.Cover

/-!
# Region Z2, checked by the kernel: cells and bands in fixed point

The analogue of `Z2Cells` for the fixed-point arithmetic (`BSCert.FX`), evaluated by the kernel
(`decide +kernel`, no `native_decide`): the same expression `z2Ex`, with `feval` and the sparse
`r_low` table `rtabF`.

* `cellUF`, `cellVF`: the cell tests in the variables `(ℓ, u)` and `(ℓ, v = u - ℓ^{1/4})`;
* `bandDataF la lb = some (s, va, vb)`: the split point `s` between `u`- and `v`-cells and the
  `v`-range `[va, vb]` of the band `ℓ ∈ [la, lb]`;
* `bandF_sound`: covers of `[2, s]` by `u`-cells and of `[va, vb]` by `v`-cells give `Z2Prop`
  on the whole band.

The covers themselves (adaptive, with bisection: `FX.coverF`) are generated per band and split
into small declarations in `Z2KChunks/*.lean`.
-/

@[expose] public section

namespace BSCert.Z2

open FX Ex

/-- Cell test, `u`-mode: `ℓ ∈ [la, lb]`, `u ∈ [ua, ub]` (fixed point). -/
def cellUF (la lb ua ub : ℤ) : Bool :=
  match feval vOfUEx [⟨la, lb⟩, ⟨ua, ub⟩], rEncF rtabF ua ub, rEncF rtabF (ua - ZI) (ub - ZI) with
  | some V, some R, some R0 => fcheckPos z2Ex [⟨la, lb⟩, ⟨ua, ub⟩, V, R, R0]
  | _, _, _ => false

/-- Cell test, `v`-mode, given the enclosure `U` of `u = u₀(ℓ) + v`. -/
def cellVU (la lb va vb : ℤ) (U : FI) : Bool :=
  match rEncF rtabF U.lo U.hi, rEncF rtabF (U.lo - ZI) (U.hi - ZI) with
  | some R, some R0 => fcheckPos z2Ex [⟨la, lb⟩, U, ⟨va, vb⟩, R, R0]
  | _, _ => false

/-- Cell test, `v`-mode: `ℓ ∈ [la, lb]`, `v = u - u₀(ℓ) ∈ [va, vb]`. -/
def cellVF (la lb va vb : ℤ) : Bool :=
  match feval uOfVEx [⟨la, lb⟩, ⟨va, vb⟩] with
  | some U => cellVU la lb va vb U
  | none => false

lemma fmem_of {a b : ℤ} {x : ℝ} (h1 : toR a ≤ x) (h2 : x ≤ toR b) : FI.Mem x ⟨a, b⟩ := ⟨h1, h2⟩

lemma toR_sub_ZI (a : ℤ) : toR (a - ZI) = toR a - 1 := by rw [toR_sub, toR_ZI]

lemma cellUF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb ua ub : ℤ}
    (h : cellUF la lb ua ub = true) {ℓ u : ℝ} (hl1 : toR la ≤ ℓ) (hl2 : ℓ ≤ toR lb)
    (hu1 : toR ua ≤ u) (hu2 : u ≤ toR ub) : 0 < Z2Claim r ℓ u := by
  have ht := rtabF_ok hr
  unfold cellUF at h
  split at h
  · rename_i V R R0 hV hR hR0
    have hv : FI.Mem (u - u0 ℓ) V := by
      have := feval_sound vOfUEx [ℓ, u] _ V
        (List.Forall₂.cons (fmem_of hl1 hl2) (List.Forall₂.cons (fmem_of hu1 hu2)
          List.Forall₂.nil)) hV
      simpa [vOfUEx, Ex.eval, u0] using this
    rw [← z2Ex_eval]
    refine fcheckPos_sound ?_ h
    refine List.Forall₂.cons (fmem_of hl1 hl2) (List.Forall₂.cons (fmem_of hu1 hu2)
      (List.Forall₂.cons hv (List.Forall₂.cons (rEncF_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEncF_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))))
    · rw [toR_sub_ZI]; linarith
    · rw [toR_sub_ZI]; linarith
  · cases h

lemma cellVU_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb va vb : ℤ} {U : FI}
    (h : cellVU la lb va vb U = true) {ℓ v : ℝ} (hl1 : toR la ≤ ℓ) (hl2 : ℓ ≤ toR lb)
    (hv1 : toR va ≤ v) (hv2 : v ≤ toR vb) (hu : FI.Mem (u0 ℓ + v) U) :
    0 < Z2Claim r ℓ (u0 ℓ + v) := by
  have ht := rtabF_ok hr
  unfold cellVU at h
  split at h
  · rename_i R R0 hR hR0
    rw [← z2Ex_eval]
    refine fcheckPos_sound ?_ h
    have e : u0 ℓ + v - u0 ℓ = v := by ring
    have hv' : FI.Mem (u0 ℓ + v - u0 ℓ) ⟨va, vb⟩ := by rw [e]; exact fmem_of hv1 hv2
    refine List.Forall₂.cons (fmem_of hl1 hl2) (List.Forall₂.cons hu
      (List.Forall₂.cons hv' (List.Forall₂.cons (rEncF_sound hr ht hR hu.1 hu.2)
      (List.Forall₂.cons (rEncF_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))))
    · rw [toR_sub_ZI]; linarith [hu.1]
    · rw [toR_sub_ZI]; linarith [hu.2]
  · cases h

lemma cellVF_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb va vb : ℤ}
    (h : cellVF la lb va vb = true) {ℓ v : ℝ} (hl1 : toR la ≤ ℓ) (hl2 : ℓ ≤ toR lb)
    (hv1 : toR va ≤ v) (hv2 : v ≤ toR vb) : 0 < Z2Claim r ℓ (u0 ℓ + v) := by
  unfold cellVF at h
  split at h
  · rename_i U hU
    have hu : FI.Mem (u0 ℓ + v) U := by
      have := feval_sound uOfVEx [ℓ, v] _ U
        (List.Forall₂.cons (fmem_of hl1 hl2) (List.Forall₂.cons (fmem_of hv1 hv2)
          List.Forall₂.nil)) hU
      simpa [uOfVEx, Ex.eval, u0] using this
    exact cellVU_sound hr h hl1 hl2 hv1 hv2 hu
  · cases h

/-- The data of the band `ℓ ∈ [la, lb]`: the split `s = max(40, u₀/2)` and the `v`-range
`[s - u₀, Ū - u₀]` (enclosures over the whole band). -/
def bandDataF (la lb : ℤ) : Option (ℤ × ℤ × ℤ) :=
  match feval u0Ex [⟨la, lb⟩], feval ubmu0Ex [⟨la, lb⟩] with
  | some U0, some W =>
    let s := Max.max (40 * ZI) (U0.lo / 2)
    some (s, s - U0.hi, W.hi)
  | _, _ => none

/-- The `u`-cover of a band gives the claim on `[2, s]`. -/
lemma coverU_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y : ℤ} {d n : ℕ}
    {step : ℤ → ℤ} (h : coverF (fun a b => cellUF la lb a b) d step n x y = true) :
    ∀ u : ℝ, toR x ≤ u → u ≤ toR y → ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ u :=
  coverF_sound (fun u => ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ u) _
    (fun _ _ hab u h1 h2 ℓ hl1 hl2 => cellUF_sound hr hab hl1 hl2 h1 h2) d step n x y h

/-- The `v`-cover of a band gives the claim on `[va, vb]` (in the variable `v`). -/
lemma coverV_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y : ℤ} {d n : ℕ}
    {step : ℤ → ℤ} (h : coverF (fun a b => cellVF la lb a b) d step n x y = true) :
    ∀ v : ℝ, toR x ≤ v → v ≤ toR y → ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb →
      0 < Z2Claim r ℓ (u0 ℓ + v) :=
  coverF_sound (fun v => ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ (u0 ℓ + v)) _
    (fun _ _ hab v h1 h2 ℓ hl1 hl2 => cellVF_sound hr hab hl1 hl2 h1 h2) d step n x y h

/-- **A band.** -/
theorem bandF_sound {r : ℝ → ℝ} {la lb s va vb : ℤ} (hd : bandDataF la lb = some (s, va, vb))
    (hU : ∀ u : ℝ, 2 ≤ u → u ≤ toR s → ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ u)
    (hV : ∀ v : ℝ, toR va ≤ v → v ≤ toR vb → ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb →
      0 < Z2Claim r ℓ (u0 ℓ + v)) :
    ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → Z2Prop r ℓ := by
  intro ℓ hl1 hl2 u hu1 hu2
  unfold bandDataF at hd
  split at hd
  · rename_i U0 W hU0 hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    have hl : FI.Mem ℓ ⟨la, lb⟩ := fmem_of hl1 hl2
    have hu0 : FI.Mem (u0 ℓ) U0 := by
      have := feval_sound u0Ex [ℓ] _ U0 (List.Forall₂.cons hl List.Forall₂.nil) hU0
      simpa [u0Ex, Ex.eval, u0] using this
    have hw : FI.Mem (UbMu0 ℓ) W := by
      have := feval_sound ubmu0Ex [ℓ] _ W (List.Forall₂.cons hl List.Forall₂.nil) hW
      simpa [ubmu0Ex, Ex.eval, UbMu0, u0] using this
    set s := Max.max (40 * ZI) (U0.lo / 2)
    by_cases hs : u ≤ toR s
    · exact hU u hu1 hs ℓ hl1 hl2
    · have key := hV (u - u0 ℓ) ?_ ?_ ℓ hl1 hl2
      · simpa using key
      · rw [toR_sub]; linarith [hu0.2, not_le.mp hs]
      · have : u - u0 ℓ ≤ UbMu0 ℓ := by unfold Ubar at hu2; linarith
        exact le_trans this hw.2
  · cases hd

/-- `toR (c · 2^128) = c`. -/
lemma toR_intZ (c : ℤ) : toR (c * ZI) = (c : ℝ) := by
  unfold toR; push_cast; field_simp [ZR_pos.ne']

/-- `u`-steps of the adaptive cover: `+16` below `40`, ratio `2.6` above (cells are bisected
up to depth 5 where needed). -/
def stepUF (x : ℤ) : ℤ := if x < 40 * ZI then x + 16 * ZI else x * 13 / 5

/-- The claim for one `u` on a band. -/
def PU (r : ℝ → ℝ) (la lb : ℤ) (u : ℝ) : Prop :=
  ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ u

/-- The claim for one `v` on a band. -/
def PV (r : ℝ → ℝ) (la lb : ℤ) (v : ℝ) : Prop :=
  ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → 0 < Z2Claim r ℓ (u0 ℓ + v)

lemma segU {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y : ℤ} {n : ℕ}
    (h : coverF (fun a b => cellUF la lb a b) 5 stepUF n x y = true) :
    ∀ u : ℝ, toR x ≤ u → u ≤ toR y → PU r la lb u :=
  coverU_sound hr h

lemma segV {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y H : ℤ} {n : ℕ}
    (h : coverF (fun a b => cellVF la lb a b) 5 (fun x => x + H) n x y = true) :
    ∀ v : ℝ, toR x ≤ v → v ≤ toR y → PV r la lb v :=
  coverV_sound hr h

lemma segLU {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y : ℤ} {l : List ℤ}
    (h : coverL (fun a b => cellUF la lb a b) x l y = true) :
    ∀ u : ℝ, toR x ≤ u → u ≤ toR y → PU r la lb u :=
  coverL_sound (PU r la lb) _ (fun _ _ hab u h1 h2 ℓ hl1 hl2 => cellUF_sound hr hab hl1 hl2 h1 h2)
    l x y h

lemma segLV {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {la lb x y : ℤ} {l : List ℤ}
    (h : coverL (fun a b => cellVF la lb a b) x l y = true) :
    ∀ v : ℝ, toR x ≤ v → v ≤ toR y → PV r la lb v :=
  coverL_sound (PV r la lb) _ (fun _ _ hab v h1 h2 ℓ hl1 hl2 => cellVF_sound hr hab hl1 hl2 h1 h2)
    l x y h

lemma glueI {P : ℝ → Prop} {a b c : ℤ} (h1 : ∀ x : ℝ, toR a ≤ x → x ≤ toR b → P x)
    (h2 : ∀ x : ℝ, toR b ≤ x → x ≤ toR c → P x) : ∀ x : ℝ, toR a ≤ x → x ≤ toR c → P x :=
  glue h1 h2

/-- A band from its two glued covers. -/
theorem bandF {r : ℝ → ℝ} {la lb s va vb : ℤ} (hd : bandDataF la lb = some (s, va, vb))
    (hU : ∀ u : ℝ, toR (2 * ZI) ≤ u → u ≤ toR s → PU r la lb u)
    (hV : ∀ v : ℝ, toR va ≤ v → v ≤ toR vb → PV r la lb v) :
    ∀ ℓ : ℝ, toR la ≤ ℓ → ℓ ≤ toR lb → Z2Prop r ℓ :=
  bandF_sound hd (fun u h1 h2 => hU u (by rw [toR_intZ]; exact_mod_cast h1) h2) hV

/-- Turn a range in fixed point into a range of reals. -/
lemma range_intZ {P : ℝ → Prop} {a b : ℤ} (h : ∀ x : ℝ, toR (a * ZI) ≤ x → x ≤ toR (b * ZI) → P x) :
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → P x := by
  intro x h1 h2; exact h x (by rw [toR_intZ]; exact h1) (by rw [toR_intZ]; exact h2)

end BSCert.Z2
