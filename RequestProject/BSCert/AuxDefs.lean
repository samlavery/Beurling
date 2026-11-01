module

public import RequestProject.BSCert.Cover

/-!
# The one-variable inequalities of Appendix B.1 (`aux_cert_arb.py`)

Real-valued statements of the three one-variable checks, their expression trees, the cell
tests, and the soundness of the cell tests. The computations themselves are in
`RequestProject.BSCert.AuxCert`.

Throughout, `r` is the Dickman ratio, only through the hypotheses `DickmanRatioFacts r`.

1. `cAMargin r u > 0` on `[27, 4·10⁵]`: positivity of `c₀(u)` (proof of Theorem 5.6, Step 7,
   "Positivity of `c(u)`"): the bracket bound for `c₀(u)/(K'u²)` exceeds `log(1+u)`.
2. `lemVLHS r u > 0` on `[1, 10⁶]`: the left side of (28) in Lemma 5.3 without `X(u)`, at
   `L_z = max(100, u)`, with `K = 3.2`, `K_M = 1.01`.
3. `lemVExtLHS r u > 0` on `[1, 2]`: the left side of (28) at `L_z = 100` including `X(u)` and
   the extra allowance `2 K_M r(u) (e^{0.141} - 1)`.
-/

@[expose] public section

namespace BSCert

open Real

/-! ## Real-valued statements -/

/-- Check (1): `5 log(1+u) [3(1-1/r(u)) - (1+u)³ log(2+u)/(u³ log(1+u))
 - 144 (1+u)² log(2+u)/(u³ r(u-1)² log(1+u))] - 2 r(u-1) - (u+1)/u² - log(1+u)`. -/
noncomputable def cAMargin (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  5 * Real.log (1 + u) * (3 * (1 - 1 / r u)
      - (1 + u) ^ 3 * Real.log (2 + u) / (u ^ 3 * Real.log (1 + u))
      - 144 * (1 + u) ^ 2 * Real.log (2 + u) / (u ^ 3 * r (u - 1) ^ 2 * Real.log (1 + u)))
    - 2 * r (u - 1) - (u + 1) / u ^ 2 - Real.log (1 + u)

/-- `α = 4K (log(u+1) + (u-1)/(u+1)) / L` with `K = 3.2` (Lemma 5.3). -/
noncomputable def lemVAlpha (u L : ℝ) : ℝ := 4 * 3.2 * (Real.log (u + 1) + (u - 1) / (u + 1)) / L

/-- Check (2): `L (1 - e^{-α}) E* - 2 K_M r(u) - 22 e^{-0.4 L}` at `L = max(100, u)`,
with `E* = max(1/2, 1 - 1/r(u-1))` for `u ≥ 2` and `E* = 1/2` otherwise, `K_M = 1.01`. -/
noncomputable def lemVLHS (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  max 100 u * (1 - Real.exp (-lemVAlpha u (max 100 u)))
      * (if 2 ≤ u then max (1 / 2) (1 - 1 / r (u - 1)) else 1 / 2)
    - 2 * 1.01 * r u - 22 * Real.exp (-0.4 * max 100 u)

/-- `X(u) = 0.7627/(C₀ (1 - log u) u)` for `u < 1 + log 72/100`, else `0` (`C₀ = 0.70`). -/
noncomputable def lemVX (u : ℝ) : ℝ :=
  if u < 1 + Real.log 72 / 100 then 0.7627 / (0.70 * (1 - Real.log u) * u) else 0

/-- Check (3): at `L = 100`,
`L (1 - e^{-α})/2 - 2 K_M r(u) - 22 e^{-0.4 L} - X(u) - 2 K_M r(u) (e^{0.141} - 1)`. -/
noncomputable def lemVExtLHS (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  100 * (1 - Real.exp (-lemVAlpha u 100)) / 2 - 2 * 1.01 * r u - 22 * Real.exp (-0.4 * 100)
    - lemVX u - 2 * 1.01 * r u * (Real.exp 0.141 - 1)

/-! ## Expression trees -/

namespace AuxEx
/-- variables -/
def u : Ex := .var 0
def R : Ex := .var 1
def R0 : Ex := .var 2
end AuxEx

open AuxEx in
/-- Expression for `cAMargin`, environment `[u, r u, r (u-1)]`. -/
def cAEx : Ex :=
  .lett (.log (1 + u)) <|            -- var 3 = log(1+u)
  .lett (.log (2 + u)) <|            -- var 4 = log(2+u)
  5 * .var 3 * (3 * (1 - 1 / R)
      - (1 + u) * (1 + u) * (1 + u) * .var 4 / (u * u * u * .var 3)
      - 144 * (1 + u) * (1 + u) * .var 4 / (u * u * u * .sq R0 * .var 3))
    - 2 * R0 - (u + 1) / (u * u) - .var 3

open AuxEx in
/-- Expression for `lemVLHS`, environment `[u, r u, r (max (u-1) 1)]`. -/
def lemVEx : Ex :=
  .lett (.max 100 u) <|                                          -- var 3 = L
  .lett (4 * 3.2 * (.log (u + 1) + (u - 1) / (u + 1)) / .var 3) <|  -- var 4 = α
  .var 3 * (1 - .exp (-(.var 4))) * .ite (2 - u) (.max (1 / 2) (1 - 1 / R0)) (1 / 2)
    - 2 * 1.01 * R - 22 * .exp (-(0.4) * .var 3)

open AuxEx in
/-- Expression for `lemVExtLHS`, environment `[u, r u]`. -/
def lemVExtEx : Ex :=
  .lett (4 * 3.2 * (.log (u + 1) + (u - 1) / (u + 1)) / 100) <|    -- var 2 = α
  100 * (1 - .exp (-(.var 2))) / 2 - 2 * 1.01 * R - 22 * .exp (-(0.4) * 100)
    - .ite (1 + .log 72 / 100 - u) 0 (0.7627 / (0.70 * (1 - .log u) * u))
    - 2 * 1.01 * R * (.exp 0.141 - 1)

lemma cAEx_eval (r : ℝ → ℝ) (u : ℝ) : cAEx.eval [u, r u, r (u - 1)] = cAMargin r u := by
  simp [cAEx, Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific, cAMargin, AuxEx.u, AuxEx.R, AuxEx.R0]
  ring

lemma lemVEx_eval (r : ℝ → ℝ) (u : ℝ) :
    lemVEx.eval [u, r u, r (max (u - 1) 1)] = lemVLHS r u := by
  simp only [lemVEx, Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific, lemVLHS, lemVAlpha, AuxEx.u, AuxEx.R, AuxEx.R0, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  have h2 : ∀ u : ℝ, 2 ≤ u → max (u - 1) 1 = u - 1 := fun u h => max_eq_left (by linarith)
  by_cases hu : 2 ≤ u
  · rw [if_pos (by push_cast; linarith), if_pos hu, h2 u hu]
    push_cast; ring_nf
  · rw [if_neg (by push_cast; linarith), if_neg hu]
    push_cast; ring_nf

lemma lemVExtEx_eval (r : ℝ → ℝ) (u : ℝ) : lemVExtEx.eval [u, r u] = lemVExtLHS r u := by
  simp only [lemVExtEx, Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific, lemVExtLHS, lemVAlpha, lemVX, AuxEx.u, AuxEx.R, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  by_cases hu : u < 1 + Real.log 72 / 100
  · rw [if_neg (by push_cast; linarith), if_pos hu]
    push_cast; ring_nf
  · rw [if_pos (by push_cast; linarith), if_neg hu]
    push_cast; ring_nf

/-! ## Cell tests and their soundness -/

/-- Cell test for check (1). -/
def cACell (tbl : Array ℚ) (a b : ℚ) : Bool :=
  match rEnc tbl a b, rEnc tbl (a - 1) (b - 1) with
  | some R, some R0 => Ex.checkPos cAEx [⟨a, b⟩, R, R0]
  | _, _ => false

/-- Cell test for check (2). -/
def lemVCell (tbl : Array ℚ) (a b : ℚ) : Bool :=
  match rEnc tbl a b, rEnc tbl (max (a - 1) 1) (max (b - 1) 1) with
  | some R, some R0 => Ex.checkPos lemVEx [⟨a, b⟩, R, R0]
  | _, _ => false

/-- Cell test for check (3). -/
def lemVExtCell (tbl : Array ℚ) (a b : ℚ) : Bool :=
  match rEnc tbl a b with
  | some R => Ex.checkPos lemVExtEx [⟨a, b⟩, R]
  | none => false

lemma cACell_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    (a b : ℚ) (h : cACell tbl a b = true) (u : ℝ) (hu1 : (a : ℝ) ≤ u) (hu2 : u ≤ (b : ℝ)) :
    0 < cAMargin r u := by
  unfold cACell at h
  split at h
  · rename_i R R0 hR hR0
    rw [← cAEx_eval]
    refine Ex.checkPos_sound ?_ h
    refine List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEnc_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEnc_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))
    · push_cast; linarith
    · push_cast; linarith
  · cases h

lemma lemVCell_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ} (ht : TableOK r tbl)
    (a b : ℚ) (h : lemVCell tbl a b = true) (u : ℝ) (hu1 : (a : ℝ) ≤ u) (hu2 : u ≤ (b : ℝ)) :
    0 < lemVLHS r u := by
  unfold lemVCell at h
  split at h
  · rename_i R R0 hR hR0
    rw [← lemVEx_eval]
    refine Ex.checkPos_sound ?_ h
    refine List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEnc_sound hr ht hR hu1 hu2)
      (List.Forall₂.cons (rEnc_sound hr ht hR0 ?_ ?_) List.Forall₂.nil))
    · push_cast; exact max_le_max (by linarith) le_rfl
    · push_cast; exact max_le_max (by linarith) le_rfl
  · cases h

lemma lemVExtCell_sound {r : ℝ → ℝ} (hr : DickmanRatioFacts r) {tbl : Array ℚ}
    (ht : TableOK r tbl) (a b : ℚ) (h : lemVExtCell tbl a b = true) (u : ℝ)
    (hu1 : (a : ℝ) ≤ u) (hu2 : u ≤ (b : ℝ)) : 0 < lemVExtLHS r u := by
  unfold lemVExtCell at h
  split at h
  · rename_i R hR
    rw [← lemVExtEx_eval]
    refine Ex.checkPos_sound ?_ h
    exact List.Forall₂.cons ⟨hu1, hu2⟩ (List.Forall₂.cons (rEnc_sound hr ht hR hu1 hu2)
      List.Forall₂.nil)
  · cases h

end BSCert
