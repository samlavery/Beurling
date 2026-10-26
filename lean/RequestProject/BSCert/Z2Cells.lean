module

public import RequestProject.BSCert.Z2Ex

/-!
# Region Z2: cells, bands and their soundness

As in `cert_run_arb.py`: the range of `ℓ` is cut into bands `[la, lb]` of ratio `1.05`. In each
band,
* `u`-cells cover `u ∈ [2, split]`, `split = max(40, u₀(la)/2)` (steps `0.5` up to `40`, then
  ratio `1.05`);
* `v`-cells, in the variable `v = u - u₀(ℓ)`, cover `v ∈ [va, vb]` with
  `va ≤ split - u₀(ℓ)` and `vb ≥ Ū(ℓ) - u₀(ℓ)` for every `ℓ` in the band (both bounds are
  computed in interval arithmetic over the whole band, so the seams and the top edge are
  covered exactly).
On each cell (a product of an `ℓ`-interval and a `u`- or `v`-interval) the expression `z2Ex`
is evaluated in interval arithmetic, and the cell passes if the lower bound is positive.
-/

@[expose] public section

namespace BSCert

namespace Z2

/-- `v = u - ℓ^{1/4}` from `[ℓ, u]`. -/
def vOfUEx : Ex := X 1 - .sqrt (.sqrt (X 0))
/-- `u = ℓ^{1/4} + v` from `[ℓ, v]`. -/
def uOfVEx : Ex := .sqrt (.sqrt (X 0)) + X 1
/-- `u₀ = ℓ^{1/4}` from `[ℓ]`. -/
def u0Ex : Ex := .sqrt (.sqrt (X 0))
/-- `Ū - u₀` from `[ℓ]`. -/
def ubmu0Ex : Ex := .sqrt (.sqrt (X 0)) * .sqrt (2 * .log (X 0 / 100000000) + 4)

/-- Cell test, `u`-mode: `ℓ ∈ [la, lb]`, `u ∈ [ua, ub]`. -/
def cellU (tbl : Array ℚ) (la lb ua ub : ℚ) : Bool :=
  match Ex.ieval vOfUEx [⟨la, lb⟩, ⟨ua, ub⟩], rEnc tbl ua ub, rEnc tbl (ua - 1) (ub - 1) with
  | some V, some R, some R0 => Ex.checkPos z2Ex [⟨la, lb⟩, ⟨ua, ub⟩, V, R, R0]
  | _, _, _ => false

/-- Cell test, `v`-mode: `ℓ ∈ [la, lb]`, `v = u - u₀(ℓ) ∈ [va, vb]`. -/
def cellV (tbl : Array ℚ) (la lb va vb : ℚ) : Bool :=
  match Ex.ieval uOfVEx [⟨la, lb⟩, ⟨va, vb⟩] with
  | some U =>
    match rEnc tbl U.lo U.hi, rEnc tbl (U.lo - 1) (U.hi - 1) with
    | some R, some R0 => Ex.checkPos z2Ex [⟨la, lb⟩, U, ⟨va, vb⟩, R, R0]
    | _, _ => false
  | none => false

/-- `u`-steps: `0.5` below `40`, ratio `1.05` above. -/
def stepU (x : ℚ) : ℚ := if x < 40 then x + 1 / 2 else rup (x * 21 / 20)

/-- The check of one band `ℓ ∈ [la, lb]`. -/
def bandOK (tbl : Array ℚ) (la lb : ℚ) : Bool :=
  match Ex.ieval u0Ex [⟨la, lb⟩], Ex.ieval ubmu0Ex [⟨la, lb⟩] with
  | some U0, some W =>
    let split : ℚ := max 40 (rdn (U0.lo / 2))
    let va := rdn (split - U0.hi)
    let vb := W.hi
    let n : ℕ := max 8 ⌊(vb - va) / max 1 (U0.lo / 100)⌋.toNat
    let h := rup ((vb - va) / n)
    cover (fun a b => cellU tbl la lb a b) 0 stepU 100000 2 split &&
      cover (fun a b => cellV tbl la lb a b) 0 (fun x => rup (x + h)) 100000 va vb
  | _, _ => false

lemma mem_of {a b : ℚ} {x : ℝ} (h1 : (a : ℝ) ≤ x) (h2 : x ≤ (b : ℝ)) : Itv.Mem x ⟨a, b⟩ :=
  ⟨h1, h2⟩

lemma cellU_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    {la lb ua ub : ℚ} (h : cellU tbl la lb ua ub = true) {ℓ u : ℝ}
    (hl1 : (la : ℝ) ≤ ℓ) (hl2 : ℓ ≤ (lb : ℝ)) (hu1 : (ua : ℝ) ≤ u) (hu2 : u ≤ (ub : ℝ)) :
    0 < Z2Claim r ℓ u := by
  unfold cellU at h
  split at h
  · rename_i V R R0 hV hR hR0
    have hv : Itv.Mem (u - u0 ℓ) V := by
      have := Ex.ieval_sound vOfUEx [ℓ, u] _ V
        (List.Forall₂.cons (mem_of hl1 hl2) (List.Forall₂.cons (mem_of hu1 hu2) List.Forall₂.nil)) hV
      simpa [vOfUEx, Ex.eval, u0] using this
    rw [← z2Ex_eval]
    refine Ex.checkPos_sound ?_ h
    refine List.Forall₂.cons (mem_of hl1 hl2) (List.Forall₂.cons (mem_of hu1 hu2)
      (List.Forall₂.cons hv (List.Forall₂.cons (rEnc_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEnc_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))))
    · push_cast; linarith
    · push_cast; linarith
  · cases h

lemma cellV_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    {la lb va vb : ℚ} (h : cellV tbl la lb va vb = true) {ℓ v : ℝ}
    (hl1 : (la : ℝ) ≤ ℓ) (hl2 : ℓ ≤ (lb : ℝ)) (hv1 : (va : ℝ) ≤ v) (hv2 : v ≤ (vb : ℝ)) :
    0 < Z2Claim r ℓ (u0 ℓ + v) := by
  unfold cellV at h
  split at h
  · rename_i U hU
    have hu : Itv.Mem (u0 ℓ + v) U := by
      have := Ex.ieval_sound uOfVEx [ℓ, v] _ U
        (List.Forall₂.cons (mem_of hl1 hl2) (List.Forall₂.cons (mem_of hv1 hv2) List.Forall₂.nil)) hU
      simpa [uOfVEx, Ex.eval, u0] using this
    split at h
    · rename_i R R0 hR hR0
      rw [← z2Ex_eval]
      refine Ex.checkPos_sound ?_ h
      have e : u0 ℓ + v - u0 ℓ = v := by ring
      refine List.Forall₂.cons (mem_of hl1 hl2) (List.Forall₂.cons hu
        (List.Forall₂.cons (by rw [e]; exact mem_of hv1 hv2)
        (List.Forall₂.cons (rEnc_sound hr ht hR hu.1 hu.2)
        (List.Forall₂.cons (rEnc_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))))
      · push_cast; linarith [hu.1]
      · push_cast; linarith [hu.2]
    · cases h
  · cases h

theorem bandOK_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    {la lb : ℚ} (h : bandOK tbl la lb = true) {ℓ : ℝ} (hl1 : (la : ℝ) ≤ ℓ) (hl2 : ℓ ≤ (lb : ℝ))
    (u : ℝ) (hu1 : 2 ≤ u) (hu2 : u ≤ Ubar ℓ) : 0 < Z2Claim r ℓ u := by
  unfold bandOK at h
  split at h
  · rename_i U0 W hU0 hW
    have hl : Itv.Mem ℓ ⟨la, lb⟩ := mem_of hl1 hl2
    have hu0 : Itv.Mem (u0 ℓ) U0 := by
      have := Ex.ieval_sound u0Ex [ℓ] _ U0 (List.Forall₂.cons hl List.Forall₂.nil) hU0
      simpa [u0Ex, Ex.eval, u0] using this
    have hw : Itv.Mem (UbMu0 ℓ) W := by
      have := Ex.ieval_sound ubmu0Ex [ℓ] _ W (List.Forall₂.cons hl List.Forall₂.nil) hW
      simpa [ubmu0Ex, Ex.eval, UbMu0, u0] using this
    simp only [Bool.and_eq_true] at h
    obtain ⟨hcu, hcv⟩ := h
    set split : ℚ := max 40 (rdn (U0.lo / 2))
    by_cases hs : u ≤ (split : ℝ)
    · exact cover_sound (fun u => ∀ ℓ : ℝ, (la : ℝ) ≤ ℓ → ℓ ≤ (lb : ℝ) → 0 < Z2Claim r ℓ u)
        _ (fun a b hab u h1 h2 ℓ hl1 hl2 => cellU_sound hr ht hab hl1 hl2 h1 h2) 0 _ _ _ _ hcu u
        (by push_cast; exact hu1) hs ℓ hl1 hl2
    · have key := cover_sound
        (fun v => ∀ ℓ : ℝ, (la : ℝ) ≤ ℓ → ℓ ≤ (lb : ℝ) → 0 < Z2Claim r ℓ (u0 ℓ + v))
        _ (fun a b hab v h1 h2 ℓ hl1 hl2 => cellV_sound hr ht hab hl1 hl2 h1 h2) 0 _ _ _ _ hcv
        (u - u0 ℓ) ?_ ?_ ℓ hl1 hl2
      · simpa using key
      · apply rdn_le_real
        push_cast
        have := hu0.2
        linarith [not_le.mp hs]
      · have : u - u0 ℓ ≤ UbMu0 ℓ := by unfold Ubar at hu2; linarith
        exact le_trans this hw.2
  · cases h

end Z2

end BSCert
