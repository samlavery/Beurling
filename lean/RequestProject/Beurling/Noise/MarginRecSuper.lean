module

public import RequestProject.Beurling.Noise.MarginVarRec
public import RequestProject.Beurling.Noise.KptDefs
public import RequestProject.BSCert.Finite.X0Band

/-!
# Proposition 5.38, Step 5: the ordered-factorisation super-solution of the recursion

Step 3 of the proof of Proposition 5.38 gives the recursion (`Margin.Var.RecIneq`)

  `v(t) ≤ S(t) + ∑_{w ≥ 2} c_w(t) sup{v(t') : |t' - t/w| ≤ 2.1 H(t/w)}`,
  `0 ≤ c_w(t) ≤ 1.0101 w^{ε-2}`

(the paper writes `1.01`; the factor `1 + 10⁻⁹` of the negative shifts is absorbed in Step 5,
"as `1.01(1 + 10⁻⁹) ≤ 2^{0.015}`"), with `log t · S(t) ≤ E_S` (Step 4). Step 5 says: iterating,
a chain of cofactors with product `M` has weight at most `H_ord(M) M^{ε'-2}`, `ε' = ε + 0.015`,
and ends at a base point within `4.4 H(X₀)` of `t/M`, so

  `v(t) ≤ ∑_M H_ord(M) M^{ε'-2} E_S/log(t/M) + v_{X₀}(t)`,
  `v_{X₀}(t) ≤ j ∑_{M : |t/M - X₀| ≤ 5.5 H(X₀)} H_ord(M) M^{ε'-2}`.

Here this is proved as a statement about an explicit **super-solution** (`Vsup`):

  `V(t) = ∑_M H_ord(M) M^{ε'-2} Φ(t/M, M)`,
  `Φ(z, M) = 1[z ≥ c(M)] E_S/log z + 1[|z - X₀| ≤ r(M)] j`,

with level-dependent cut-offs `c(M) = c_∞ + K_c M^{ε-1}` and radii `r(M) = R₀ - K_r M^{ε-1}`.
These absorb the drift of the chain end points exactly: one step moves a point by at most
`2.1 H(t/w)/M ≤ 2.1 M^{ε-1} H(z)` (by (RH)), and `c(M) - c(wM)`, `r(wM) - r(M)` are at least
`(1 - 2^{ε-1}) K M^{ε-1}`. With `K_r = 4.41 H(X₀)` and `r(1) ≥ 1.01 H(X₀)` this gives
`r(M) ≤ R₀ = 5.5 H(X₀)`, the window `I'_t` of the paper.

* `Margin.Rec.super` : `Vsup` is a super-solution (`Margin.Var.Super`);
* `Margin.Rec.v_le_Vsup` : with the recursion, the base case and the well-foundedness,
  `v ≤ Vsup` everywhere (Step 5's first display, in level form).

All hypotheses are on `H`, the parameters and the recursion (`ChainHyp`); the identification of
the Step-3 recursion for the margin's variation is `MarginRecStep.lean`.
-/

@[expose] public section

open Finset Real

namespace Margin.Rec

/-- The parameters of the super-solution. -/
structure CP where
  Xm : ℝ
  X0 : ℝ
  ES : ℝ
  j : ℝ
  ε : ℝ
  ε' : ℝ
  θ : ℝ
  θ0 : ℝ
  Kc : ℝ
  Kr : ℝ
  R0 : ℝ
  cinf : ℝ

variable (P : BeurlingSystem) (p : CP)

/-- The value `V(M)` of a level. -/
noncomputable abbrev Vv (M : ℕ) : ℝ := KR.Vl P M

/-- The cut-off `c(M) = c_∞ + K_c M^{ε-1}`. -/
noncomputable def cutL (M : ℕ) : ℝ := p.cinf + p.Kc * Vv P M ^ (p.ε - 1)

/-- The jump radius `r(M) = R₀ - K_r M^{ε-1}`. -/
noncomputable def radJ (M : ℕ) : ℝ := p.R0 - p.Kr * Vv P M ^ (p.ε - 1)

/-- `Φ(z, M) = 1[z ≥ c(M)] E_S/log z + 1[|z - X₀| ≤ r(M)] j`. -/
noncomputable def PhiC (z : ℝ) (M : ℕ) : ℝ :=
  (if cutL P p M ≤ z then p.ES / Real.log z else 0) +
    (if |z - p.X0| ≤ radJ P p M then p.j else 0)

/-- The chain weight `H_ord(M) M^{ε'-2}`. -/
noncomputable def Aw (M : ℕ) : ℝ := (BSCert.X0Band.Hord M : ℝ) * Vv P M ^ (p.ε' - 2)

/-- **The super-solution** `V(t) = ∑_M H_ord(M) M^{ε'-2} Φ(t/M, M)`. -/
noncomputable def Vsup (t : ℝ) : ℝ :=
  ∑ M ∈ KR.NAll P t (p.Xm / 2), Aw P p M * PhiC P p (t / Vv P M) M

/-- The cofactors of the recursion at `t`: the levels `w ≥ 2` with `t/w ≥ X₀⁻/2` (those that
can meet the support of `ρ̃` after a shift). -/
noncomputable def Fset (t : ℝ) : Finset ℕ := (KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·)

/-- The neighbourhood `|t' - t/w| ≤ 2.1 H(t/w)` of the recursion. -/
def Nbhd (H : ℝ → ℝ) (t : ℝ) (w : ℕ) : Set ℝ :=
  Set.Icc (t / Vv P w - 2.1 * H (t / Vv P w)) (t / Vv P w + 2.1 * H (t / Vv P w))

/-- The hypotheses on `H` and the parameters. -/
structure ChainHyp (H : ℝ → ℝ) : Prop where
  hXm : 2 < p.Xm
  hε0 : 0 ≤ p.ε
  hε1 : p.ε < 1
  hεε : p.ε ≤ p.ε'
  hES : 0 ≤ p.ES
  hj : 0 ≤ p.j
  hθ : 0 ≤ p.θ
  hθ0 : 0 ≤ p.θ0
  hθ01 : p.θ0 < 1
  hKc : 0 ≤ p.Kc
  hKr : 0 ≤ p.Kr
  /-- `H(y)/y` is small above `X₀⁻/2`: `2.1 H(y) ≤ θ₀ y`. -/
  hrel : ∀ y, p.Xm / 2 ≤ y → 2.1 * H y ≤ p.θ0 * y
  /-- `H ≥ 0` and non-decreasing on `[X₀⁻/2, ∞)`. -/
  hH0 : ∀ y, 0 ≤ H y
  hmono : MonotoneOn H (Set.Ici (p.Xm / 2))
  /-- (RH): `H(az) ≤ a^ε H(z)` for `z ≥ X₀⁻/2`, `a ≥ 1`. -/
  hRH : ∀ z, p.Xm / 2 ≤ z → ∀ a : ℝ, 1 ≤ a → H (a * z) ≤ a ^ p.ε * H z
  hcinf : (1 + p.θ0) * (p.Xm / 2) ≤ p.cinf
  hXR : (1 + p.θ0) * (p.Xm / 2) ≤ p.X0 - p.R0
  hR0 : 0 ≤ p.R0
  /-- The log loss of one step is absorbed by `1 + θ`. -/
  hlog : (1 + p.θ) * (-Real.log (1 - p.θ0)) ≤ p.θ * Real.log p.cinf
  /-- The cut-off decrement pays for the drift. -/
  hKcH : 2.1 * H (p.cinf + p.Kc) ≤ p.Kc * (1 - 2 ^ (p.ε - 1))
  /-- The radius increment pays for the drift. -/
  hKrH : 2.1 * H ((p.X0 + p.R0) / (1 - p.θ0)) ≤ p.Kr * (1 - 2 ^ (p.ε - 1))
  /-- The step weight: `1.0101 (1 + θ) 2^{ε-ε'} ≤ 1`. -/
  hweight : 1.0101 * (1 + p.θ) * 2 ^ (p.ε - p.ε') ≤ 1
  /-- Prime values are at least `2`. -/
  hp2 : ∀ i, 2 ≤ P.p i

variable {P p}

/-! ## Values of levels -/

lemma Vv_pos (M : ℕ) : 0 < Vv P M := KR.valN_labelVal_pos P M

lemma Vv_one : Vv P 1 = 1 := LemmaM.valN_one _

lemma one_le_Vv (M : ℕ) : 1 ≤ Vv P M :=
  LemmaM.one_le_valN _ (fun r _ => P.one_le_labelVal r)

lemma Vv_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : Vv P (a * b) = Vv P a * Vv P b :=
  LemmaM.valN_mul _ ha hb

lemma two_le_Vv (hp2 : ∀ i, 2 ≤ P.p i) {w : ℕ} (hw : 2 ≤ w) : 2 ≤ Vv P w := by
  obtain ⟨q, hq, hqw⟩ := Nat.exists_prime_and_dvd (show w ≠ 1 by omega)
  have h1 := LemmaM.valN_le_of_dvd P.labelVal (fun r _ => P.one_le_labelVal r) hqw
    (by omega)
  have h2 : LemmaM.valN P.labelVal q = P.labelVal q := by
    unfold LemmaM.valN
    rw [hq.factorization]; simp
  have h3 : 2 ≤ P.labelVal q := hp2 _
  show 2 ≤ LemmaM.valN P.labelVal w
  linarith

lemma mem_NAll_iff' {y X : ℝ} (hX : 0 < X) {n : ℕ} :
    n ∈ KR.NAll P y X ↔ n ≠ 0 ∧ X ≤ y / Vv P n := by
  rw [KR.Sharp.mem_NAll_iff P hX, KR.Sharp.le_div_iff_cut P hX]

/-! ## Elementary facts on the parameters -/

variable {H : ℝ → ℝ}

lemma rpow_le_two (h : ChainHyp P p H) {w : ℕ} (hw : 2 ≤ w) :
    Vv P w ^ (p.ε - 1) ≤ 2 ^ (p.ε - 1) :=
  Real.rpow_le_rpow_of_nonpos two_pos (two_le_Vv h.hp2 hw) (by linarith [h.hε1])

lemma rpow_le_one (h : ChainHyp P p H) (M : ℕ) : Vv P M ^ (p.ε - 1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_Vv M) (by linarith [h.hε1])

lemma rpow_mul_eq {w M : ℕ} (hw : w ≠ 0) (hM : M ≠ 0) (x : ℝ) :
    Vv P (w * M) ^ x = Vv P w ^ x * Vv P M ^ x := by
  rw [Vv_mul hw hM, Real.mul_rpow (Vv_pos w).le (Vv_pos M).le]

lemma cutL_ge (h : ChainHyp P p H) (M : ℕ) : p.cinf ≤ cutL P p M := by
  unfold cutL
  have := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
  nlinarith [h.hKc]

lemma cutL_le_one (h : ChainHyp P p H) (M : ℕ) : cutL P p M ≤ p.cinf + p.Kc := by
  unfold cutL
  have := rpow_le_one h M
  nlinarith [h.hKc]

lemma cinf_gt_one (h : ChainHyp P p H) : 1 < p.cinf := by
  have := h.hcinf; have := h.hθ0; have := h.hXm; nlinarith

lemma cinf_ge (h : ChainHyp P p H) : p.Xm / 2 ≤ p.cinf := by
  have := h.hcinf; have := h.hθ0; have := h.hXm; nlinarith

/-- One step decreases the cut-off by at least the drift. -/
lemma cutL_step (h : ChainHyp P p H) {w M : ℕ} (hw : 2 ≤ w) (hM : M ≠ 0) :
    cutL P p (w * M) + 2.1 * Vv P M ^ (p.ε - 1) * H (p.cinf + p.Kc) ≤ cutL P p M := by
  unfold cutL
  rw [rpow_mul_eq (by omega) hM]
  have h1 := rpow_le_two h hw
  have h2 := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
  have h3 := h.hKcH
  have : p.Kc * (Vv P w ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) +
      2.1 * Vv P M ^ (p.ε - 1) * H (p.cinf + p.Kc) ≤
      p.Kc * (2 ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) +
        Vv P M ^ (p.ε - 1) * (p.Kc * (1 - 2 ^ (p.ε - 1))) := by
    have e1 : p.Kc * (Vv P w ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) ≤
        p.Kc * (2 ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) h.hKc
    have e2 : 2.1 * Vv P M ^ (p.ε - 1) * H (p.cinf + p.Kc) ≤
        Vv P M ^ (p.ε - 1) * (p.Kc * (1 - 2 ^ (p.ε - 1))) := by
      have := mul_le_mul_of_nonneg_left h3 h2
      linarith
    linarith
  nlinarith

/-- One step increases the radius by at least the drift. -/
lemma radJ_step (h : ChainHyp P p H) {w M : ℕ} (hw : 2 ≤ w) (hM : M ≠ 0) :
    radJ P p M + 2.1 * Vv P M ^ (p.ε - 1) * H ((p.X0 + p.R0) / (1 - p.θ0)) ≤
      radJ P p (w * M) := by
  unfold radJ
  rw [rpow_mul_eq (by omega) hM]
  have h1 := rpow_le_two h hw
  have h2 := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
  have h3 := h.hKrH
  have e1 : p.Kr * (Vv P w ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) ≤
      p.Kr * (2 ^ (p.ε - 1) * Vv P M ^ (p.ε - 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) h.hKr
  have e2 : 2.1 * Vv P M ^ (p.ε - 1) * H ((p.X0 + p.R0) / (1 - p.θ0)) ≤
      Vv P M ^ (p.ε - 1) * (p.Kr * (1 - 2 ^ (p.ε - 1))) := by
    have := mul_le_mul_of_nonneg_left h3 h2
    linarith
  nlinarith

lemma radJ_le (h : ChainHyp P p H) (M : ℕ) : radJ P p M ≤ p.R0 := by
  unfold radJ
  have := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
  nlinarith [h.hKr]

lemma PhiC_nonneg (h : ChainHyp P p H) (z : ℝ) (M : ℕ) : 0 ≤ PhiC P p z M := by
  unfold PhiC
  apply add_nonneg
  · split_ifs with hz
    · have := cutL_ge h M
      have := cinf_gt_one h
      exact div_nonneg h.hES (Real.log_nonneg (by linarith))
    · exact le_rfl
  · split_ifs
    · exact h.hj
    · exact le_rfl

lemma Aw_nonneg (M : ℕ) : 0 ≤ Aw P p M := by
  unfold Aw
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Vv_pos M).le _)

/-! ## The drift of one step -/

/-- The position after one step: if `y ≥ X₀⁻/2` and `|t' - y| ≤ 2.1 H(y)`, then
`|t'/M - y/M| ≤ θ₀ y/M` and, when `y/M ≥ X₀⁻/2`, `≤ 2.1 M^{ε-1} H(y/M)`. -/
lemma drift_rel (h : ChainHyp P p H) {y t' : ℝ} (hy : p.Xm / 2 ≤ y)
    (ht' : t' ∈ Set.Icc (y - 2.1 * H y) (y + 2.1 * H y)) (M : ℕ) :
    |t' / Vv P M - y / Vv P M| ≤ p.θ0 * (y / Vv P M) := by
  have hV := Vv_pos (P := P) M
  have h1 := h.hrel y hy
  rw [← sub_div, abs_div, abs_of_pos hV, mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hV.le
  rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]

lemma drift_abs (h : ChainHyp P p H) {y t' : ℝ}
    (ht' : t' ∈ Set.Icc (y - 2.1 * H y) (y + 2.1 * H y)) {M : ℕ}
    (hz : p.Xm / 2 ≤ y / Vv P M) :
    |t' / Vv P M - y / Vv P M| ≤ 2.1 * Vv P M ^ (p.ε - 1) * H (y / Vv P M) := by
  have hV := Vv_pos (P := P) M
  have hRH := h.hRH (y / Vv P M) hz (Vv P M) (one_le_Vv M)
  rw [mul_div_cancel₀ _ hV.ne'] at hRH
  have hM : Vv P M ^ (p.ε - 1) = Vv P M ^ p.ε / Vv P M := by
    rw [Real.rpow_sub_one hV.ne']
  rw [← sub_div, abs_div, abs_of_pos hV, div_le_iff₀ hV, hM]
  have : |t' - y| ≤ 2.1 * H y := by rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
  calc |t' - y| ≤ 2.1 * H y := this
    _ ≤ 2.1 * (Vv P M ^ p.ε * H (y / Vv P M)) := by linarith
    _ = 2.1 * (Vv P M ^ p.ε / Vv P M) * H (y / Vv P M) * Vv P M := by
        field_simp

/-- **The cut-off part of one step.** -/
lemma step_cut (h : ChainHyp P p H) {y t' : ℝ} (hy : p.Xm / 2 ≤ y)
    (ht' : t' ∈ Set.Icc (y - 2.1 * H y) (y + 2.1 * H y)) {w M : ℕ} (hw : 2 ≤ w)
    (hM : M ≠ 0) (hc : cutL P p M ≤ t' / Vv P M) :
    cutL P p (w * M) ≤ y / Vv P M ∧
      p.ES / Real.log (t' / Vv P M) ≤ (1 + p.θ) * (p.ES / Real.log (y / Vv P M)) := by
  set z := y / Vv P M with hz
  have hrel := drift_rel h hy ht' M
  rw [← hz] at hrel
  have hθ0 := h.hθ0
  have hcge := cutL_ge h M
  have hcinf := h.hcinf
  have hz0 : 0 ≤ z := div_nonneg (by linarith [h.hXm]) (Vv_pos M).le
  -- `z ≥ X₀⁻/2`
  have hzlow : p.Xm / 2 ≤ z := by
    have : t' / Vv P M ≤ z + p.θ0 * z := by
      have := (abs_le.mp hrel).2; linarith
    have h1 : (1 + p.θ0) * (p.Xm / 2) ≤ (1 + p.θ0) * z := by linarith
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hcut : cutL P p (w * M) ≤ z := by
    by_contra hlt; push_neg at hlt
    have hz1 : z ≤ p.cinf + p.Kc := le_trans hlt.le (cutL_le_one h _)
    have hHz : H z ≤ H (p.cinf + p.Kc) :=
      h.hmono (Set.mem_Ici.mpr hzlow) (Set.mem_Ici.mpr (by
        have := cinf_ge h; linarith [h.hKc])) hz1
    have habs := drift_abs h ht' (M := M) hzlow
    rw [← hz] at habs
    have hstep := cutL_step h hw hM
    have hr := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
    have : 2.1 * Vv P M ^ (p.ε - 1) * H z ≤
        2.1 * Vv P M ^ (p.ε - 1) * H (p.cinf + p.Kc) :=
      mul_le_mul_of_nonneg_left hHz (by positivity)
    have := (abs_le.mp habs).2
    linarith
  refine ⟨hcut, ?_⟩
  -- the logarithms
  have hzc : p.cinf ≤ z := le_trans (cutL_ge h _) hcut
  have hc1 := cinf_gt_one h
  have hlz : Real.log p.cinf ≤ Real.log z := Real.log_le_log (by linarith) hzc
  have hlc : 0 < Real.log p.cinf := Real.log_pos hc1
  have ht'z : z * (1 - p.θ0) ≤ t' / Vv P M := by
    have := (abs_le.mp hrel).1; linarith
  have hpos : 0 < z * (1 - p.θ0) := mul_pos (by linarith) (by linarith [h.hθ01])
  have hlt' : Real.log z + Real.log (1 - p.θ0) ≤ Real.log (t' / Vv P M) := by
    rw [← Real.log_mul (by linarith) (by linarith [h.hθ01])]
    exact Real.log_le_log hpos ht'z
  have hL := h.hlog
  -- `log z ≤ (1 + θ) log(t'/M)`
  have hkey : Real.log z ≤ (1 + p.θ) * Real.log (t' / Vv P M) := by
    have hθ := h.hθ
    have hneg : 0 ≤ -Real.log (1 - p.θ0) := by
      have : Real.log (1 - p.θ0) ≤ 0 :=
        Real.log_nonpos (by linarith [h.hθ01]) (by linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left hlz hθ
    nlinarith
  have hlpos : 0 < Real.log (t' / Vv P M) := by
    have : 0 < Real.log z := by linarith
    nlinarith [h.hθ]
  have hzpos : 0 < Real.log z := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hlpos hzpos]
  have hES := h.hES
  nlinarith

/-- **The jump part of one step.** -/
lemma step_jump (h : ChainHyp P p H) {y t' : ℝ} (hy : p.Xm / 2 ≤ y)
    (ht' : t' ∈ Set.Icc (y - 2.1 * H y) (y + 2.1 * H y)) {w M : ℕ} (hw : 2 ≤ w)
    (hM : M ≠ 0) (hj : |t' / Vv P M - p.X0| ≤ radJ P p M) :
    |y / Vv P M - p.X0| ≤ radJ P p (w * M) := by
  set z := y / Vv P M with hz
  have hrel := drift_rel h hy ht' M
  rw [← hz] at hrel
  have hθ0 := h.hθ0
  have hθ01 := h.hθ01
  have hR := radJ_le h M
  have hXR := h.hXR
  have hz0 : 0 ≤ z := div_nonneg (by linarith [h.hXm]) (Vv_pos M).le
  have hjl := abs_le.mp hj
  have hr1 := (abs_le.mp hrel)
  have hzlow : p.Xm / 2 ≤ z := by nlinarith
  have hzhigh : z ≤ (p.X0 + p.R0) / (1 - p.θ0) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hHz : H z ≤ H ((p.X0 + p.R0) / (1 - p.θ0)) :=
    h.hmono (Set.mem_Ici.mpr hzlow) (Set.mem_Ici.mpr (le_trans hzlow hzhigh)) hzhigh
  have habs := drift_abs h ht' (M := M) hzlow
  rw [← hz] at habs
  have hstep := radJ_step h hw hM
  have hr := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε - 1)
  have : 2.1 * Vv P M ^ (p.ε - 1) * H z ≤
      2.1 * Vv P M ^ (p.ε - 1) * H ((p.X0 + p.R0) / (1 - p.θ0)) :=
    mul_le_mul_of_nonneg_left hHz (by positivity)
  have hab := abs_le.mp habs
  rw [abs_le]; constructor <;> linarith

/-! ## `Vsup` is a super-solution -/

/-- The bound `b_w` for `sup_{N(t, w)} V`. -/
noncomputable def bW (t : ℝ) (w : ℕ) : ℝ :=
  (1 + p.θ) * ∑ M ∈ KR.NAll P (t / Vv P w) (p.Xm / 2),
    Aw P p M * PhiC P p (t / Vv P w / Vv P M) (w * M)

lemma XR_ge (h : ChainHyp P p H) : p.Xm / 2 ≤ p.X0 - p.R0 := by
  have := h.hXR; have := h.hθ0; have := h.hXm; nlinarith

/-- One step of `Φ`: `Φ(t'/M, M) ≤ (1 + θ) Φ(y/M, wM)`, and `Φ(t'/M, M) ≠ 0` forces
`y/M ≥ X₀⁻/2`. -/
lemma phi_step (h : ChainHyp P p H) {y t' : ℝ} (hy : p.Xm / 2 ≤ y)
    (ht' : t' ∈ Set.Icc (y - 2.1 * H y) (y + 2.1 * H y)) {w M : ℕ} (hw : 2 ≤ w)
    (hM : M ≠ 0) :
    PhiC P p (t' / Vv P M) M ≤ (1 + p.θ) * PhiC P p (y / Vv P M) (w * M) ∧
      (PhiC P p (t' / Vv P M) M ≠ 0 → p.Xm / 2 ≤ y / Vv P M) := by
  have hθ := h.hθ
  have hj := h.hj
  have hc1 := cinf_gt_one h
  have hXR := XR_ge h
  have hcutpos : ∀ z, cutL P p (w * M) ≤ z → 0 ≤ p.ES / Real.log z := fun z hz =>
    div_nonneg h.hES (Real.log_nonneg (by linarith [cutL_ge h (w * M)]))
  constructor
  · unfold PhiC
    have e1 : (if cutL P p M ≤ t' / Vv P M then p.ES / Real.log (t' / Vv P M) else 0) ≤
        (1 + p.θ) * (if cutL P p (w * M) ≤ y / Vv P M then
          p.ES / Real.log (y / Vv P M) else 0) := by
      split_ifs with h1 h2
      · exact (step_cut h hy ht' hw hM h1).2
      · exact absurd (step_cut h hy ht' hw hM h1).1 h2
      · exact mul_nonneg (by linarith) (hcutpos _ (by assumption))
      · simp
    have e2 : (if |t' / Vv P M - p.X0| ≤ radJ P p M then p.j else 0) ≤
        (1 + p.θ) * (if |y / Vv P M - p.X0| ≤ radJ P p (w * M) then p.j else 0) := by
      split_ifs with h1 h2
      · nlinarith
      · exact absurd (step_jump h hy ht' hw hM h1) h2
      · exact mul_nonneg (by linarith) hj
      · simp
    rw [mul_add]; linarith
  · intro hne
    unfold PhiC at hne
    by_cases h1 : cutL P p M ≤ t' / Vv P M
    · exact le_trans (cinf_ge h) (le_trans (cutL_ge h _) (step_cut h hy ht' hw hM h1).1)
    · by_cases h2 : |t' / Vv P M - p.X0| ≤ radJ P p M
      · have := abs_le.mp (step_jump h hy ht' hw hM h2)
        have := radJ_le h (w * M)
        linarith
      · rw [if_neg h1, if_neg h2, add_zero] at hne; exact absurd rfl hne

lemma sup_le_bW (h : ChainHyp P p H) {t : ℝ} {w : ℕ} (hw : w ∈ Fset P p t) {t' : ℝ}
    (ht' : t' ∈ Nbhd P H t w) : Vsup P p t' ≤ bW (P := P) (p := p) t w := by
  classical
  have hXm := h.hXm
  have hX2 : 0 < p.Xm / 2 := by linarith
  obtain ⟨hwA, hw2⟩ := Finset.mem_filter.mp hw
  have hy : p.Xm / 2 ≤ t / Vv P w := ((mem_NAll_iff' (by linarith)).mp hwA).2
  set y := t / Vv P w with hydef
  have hθ := h.hθ
  unfold Vsup bW
  rw [Finset.mul_sum]
  have hpt : ∀ M ∈ KR.NAll P t' (p.Xm / 2),
      Aw P p M * PhiC P p (t' / Vv P M) M ≤
        if M ∈ KR.NAll P y (p.Xm / 2) then
          (1 + p.θ) * (Aw P p M * PhiC P p (y / Vv P M) (w * M)) else 0 := by
    intro M hM
    have hM0 := ((mem_NAll_iff' hX2).mp hM).1
    have hA := Aw_nonneg (P := P) (p := p) M
    obtain ⟨hφ, hsupp⟩ := phi_step h hy ht' hw2 hM0
    split_ifs with hmem
    · have := mul_le_mul_of_nonneg_left hφ hA
      linarith
    · have hz : PhiC P p (t' / Vv P M) M = 0 := by
        by_contra hne
        exact hmem ((mem_NAll_iff' hX2).mpr ⟨hM0, hsupp hne⟩)
      rw [hz, mul_zero]
  calc ∑ M ∈ KR.NAll P t' (p.Xm / 2), Aw P p M * PhiC P p (t' / Vv P M) M
      ≤ ∑ M ∈ KR.NAll P t' (p.Xm / 2), (if M ∈ KR.NAll P y (p.Xm / 2) then
          (1 + p.θ) * (Aw P p M * PhiC P p (y / Vv P M) (w * M)) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ M ∈ KR.NAll P t' (p.Xm / 2) ∩ KR.NAll P y (p.Xm / 2),
          (1 + p.θ) * (Aw P p M * PhiC P p (y / Vv P M) (w * M)) :=
        Finset.sum_ite_mem _ _ _
    _ ≤ ∑ M ∈ KR.NAll P y (p.Xm / 2),
          (1 + p.θ) * (Aw P p M * PhiC P p (y / Vv P M) (w * M)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro M _ _
        exact mul_nonneg (by linarith)
          (mul_nonneg (Aw_nonneg M) (PhiC_nonneg h _ _))

/-- `∑_{w ∣ M, w ≥ 2} H_ord(M/w) = H_ord(M)` for `M ≥ 2`. -/
lemma sum_Hord_cofactor {M : ℕ} (hM : 2 ≤ M) :
    ∑ w ∈ M.divisors.filter (2 ≤ ·), (BSCert.X0Band.Hord (M / w) : ℝ) =
      BSCert.X0Band.Hord M := by
  rw [BSCert.X0Band.Hord_eq M, if_neg (by omega)]
  push_cast
  have hM0 : M ≠ 0 := by omega
  refine Finset.sum_nbij' (fun w => M / w) (fun d => M / d) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Nat.mem_divisors] at hw
    obtain ⟨⟨hwM, -⟩, hw2⟩ := hw
    rw [Nat.mem_properDivisors]
    exact ⟨Nat.div_dvd_of_dvd hwM, Nat.div_lt_self (by omega) (by omega)⟩
  · intro d hd
    rw [Nat.mem_properDivisors] at hd
    simp only [Finset.mem_filter, Nat.mem_divisors]
    obtain ⟨hdM, hdlt⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdM (by omega)
    refine ⟨⟨Nat.div_dvd_of_dvd hdM, hM0⟩, ?_⟩
    obtain ⟨k, hk⟩ := hdM
    rw [hk, Nat.mul_div_cancel_left k hd0]
    by_contra hc; push_neg at hc
    have : d * k ≤ d * 1 := Nat.mul_le_mul_left d (by omega)
    omega
  · intro w hw
    simp only [Finset.mem_filter, Nat.mem_divisors] at hw
    exact Nat.div_div_self hw.1.1 hM0
  · intro d hd
    rw [Nat.mem_properDivisors] at hd
    exact Nat.div_div_self hd.1 hM0
  · intro w _; rfl

/-- The weight of one step: `c_w (1 + θ) H_ord(M) M^{ε'-2} ≤ H_ord(M) (wM)^{ε'-2}`. -/
lemma weight_step (h : ChainHyp P p H) {w M : ℕ} (hw : 2 ≤ w) (hM : M ≠ 0) {c : ℝ}
    (hc : c ≤ 1.0101 * Vv P w ^ (p.ε - 2)) :
    c * (1 + p.θ) * Aw P p M ≤
      (BSCert.X0Band.Hord M : ℝ) * Vv P (w * M) ^ (p.ε' - 2) := by
  have hVw := Vv_pos (P := P) w
  have hθ := h.hθ
  have hsplit : Vv P w ^ (p.ε - 2) = Vv P w ^ (p.ε - p.ε') * Vv P w ^ (p.ε' - 2) := by
    rw [← Real.rpow_add hVw]; ring_nf
  have h2 : Vv P w ^ (p.ε - p.ε') ≤ 2 ^ (p.ε - p.ε') :=
    Real.rpow_le_rpow_of_nonpos two_pos (two_le_Vv h.hp2 hw) (by linarith [h.hεε])
  have hw' := h.hweight
  have hpos1 := Real.rpow_nonneg hVw.le (p.ε' - 2)
  have hpos2 := Real.rpow_nonneg (Vv_pos (P := P) M).le (p.ε' - 2)
  have hH := (Nat.cast_nonneg (α := ℝ) (BSCert.X0Band.Hord M))
  have hfac : c * (1 + p.θ) ≤ Vv P w ^ (p.ε' - 2) := by
    calc c * (1 + p.θ) ≤ 1.0101 * Vv P w ^ (p.ε - 2) * (1 + p.θ) :=
          mul_le_mul_of_nonneg_right hc (by linarith)
      _ = 1.0101 * (1 + p.θ) * Vv P w ^ (p.ε - p.ε') * Vv P w ^ (p.ε' - 2) := by
          rw [hsplit]; ring
      _ ≤ 1.0101 * (1 + p.θ) * 2 ^ (p.ε - p.ε') * Vv P w ^ (p.ε' - 2) := by
          apply mul_le_mul_of_nonneg_right _ hpos1
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 1 * Vv P w ^ (p.ε' - 2) := mul_le_mul_of_nonneg_right hw' hpos1
      _ = Vv P w ^ (p.ε' - 2) := one_mul _
  unfold Aw
  rw [rpow_mul_eq (by omega) hM]
  calc c * (1 + p.θ) * ((BSCert.X0Band.Hord M : ℝ) * Vv P M ^ (p.ε' - 2))
      = (BSCert.X0Band.Hord M : ℝ) * (c * (1 + p.θ) * Vv P M ^ (p.ε' - 2)) := by ring
    _ ≤ (BSCert.X0Band.Hord M : ℝ) * (Vv P w ^ (p.ε' - 2) * Vv P M ^ (p.ε' - 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfac hpos2) hH

/-- **`Vsup` is a super-solution** of the Step-3 recursion: at every `t ≥ T₀`,
`S(t) + ∑_{w ≥ 2} c_w(t) b_w ≤ V(t)` with `b_w ≥ sup_{|t' - t/w| ≤ 2.1H(t/w)} V(t')`. -/
theorem super_J (h : ChainHyp P p H) {T0 : ℝ} {S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0)
    (hS : ∀ t, T0 ≤ t →
      S t ≤ p.ES / Real.log t + (if |t - p.X0| ≤ radJ P p 1 then p.j else 0))
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2)) :
    Var.Super T0 (Vsup P p) S (Fset P p) c (Nbhd P H) := by
  classical
  intro t ht
  refine ⟨bW (P := P) (p := p) t, fun w hw t' ht' => sup_le_bW h hw ht', ?_⟩
  have hXm := h.hXm
  have hX2 : 0 < p.Xm / 2 := by linarith
  have hθ := h.hθ
  have hc1 := cinf_gt_one h
  have hKc := h.hKc
  have htc : p.cinf + p.Kc ≤ t := hT0.trans ht
  have h1 : (1 : ℕ) ∈ KR.NAll P t (p.Xm / 2) := by
    rw [mem_NAll_iff' hX2, Vv_one, div_one]
    exact ⟨one_ne_zero, by linarith [cinf_ge h]⟩
  have hsplit : KR.NAll P t (p.Xm / 2) =
      insert 1 ((KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·)) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hn
      have hn0 := ((mem_NAll_iff' hX2).mp hn).1
      rcases Nat.lt_or_ge n 2 with h' | h'
      · left; omega
      · right; exact ⟨hn, h'⟩
    · rintro (rfl | ⟨hn, -⟩)
      · exact h1
      · exact hn
  have hnot : (1 : ℕ) ∉ (KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·) := by simp
  unfold Vsup
  rw [hsplit, Finset.sum_insert hnot]
  -- the trivial chain pays for `S(t)`
  have hS1 : S t ≤ Aw P p 1 * PhiC P p (t / Vv P 1) 1 := by
    have hA1 : Aw P p 1 = 1 := by
      unfold Aw; rw [Vv_one, Real.one_rpow, BSCert.X0Band.Hord_eq 1, if_pos le_rfl]; simp
    rw [hA1, one_mul, Vv_one, div_one]
    unfold PhiC
    have hcut1 : cutL P p 1 = p.cinf + p.Kc := by
      unfold cutL; rw [Vv_one, Real.one_rpow, mul_one]
    rw [hcut1, if_pos htc]
    exact hS t ht
  -- the chains with a first step
  have hstep : ∑ w ∈ Fset P p t, c t w * bW (P := P) (p := p) t w ≤
      ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·), Aw P p M * PhiC P p (t / Vv P M) M := by
    -- expand and bound each term
    have hexp : ∑ w ∈ Fset P p t, c t w * bW (P := P) (p := p) t w ≤
        ∑ q ∈ (Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2)),
          (BSCert.X0Band.Hord q.2 : ℝ) * Vv P (q.1 * q.2) ^ (p.ε' - 2) *
            PhiC P p (t / Vv P (q.1 * q.2)) (q.1 * q.2) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_le_sum fun w hw => ?_
      obtain ⟨-, hcw⟩ := hc t ht w hw
      have hw2 := (Finset.mem_filter.mp hw).2
      unfold bW
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun M hM => ?_
      have hM0 := ((mem_NAll_iff' hX2).mp hM).1
      have hdiv : t / Vv P w / Vv P M = t / Vv P (w * M) := by
        rw [div_div, Vv_mul (by omega) hM0]
      rw [hdiv]
      have hφ := PhiC_nonneg h (t / Vv P (w * M)) (w * M)
      have := mul_le_mul_of_nonneg_right (weight_step h hw2 hM0 hcw) hφ
      calc c t w * ((1 + p.θ) * (Aw P p M * PhiC P p (t / Vv P (w * M)) (w * M)))
          = c t w * (1 + p.θ) * Aw P p M * PhiC P p (t / Vv P (w * M)) (w * M) := by ring
        _ ≤ _ := this
    -- regroup by `M' = wM`
    set T := ((KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·)).sigma
      (fun M' => M'.divisors.filter (2 ≤ ·))
    set g : (Σ _ : ℕ, ℕ) → ℝ := fun q => (BSCert.X0Band.Hord (q.1 / q.2) : ℝ) *
      Vv P q.1 ^ (p.ε' - 2) * PhiC P p (t / Vv P q.1) q.1
    have hinj : ∀ q ∈ (Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2)),
        ∀ q' ∈ (Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2)),
        (⟨q.1 * q.2, q.1⟩ : Σ _ : ℕ, ℕ) = ⟨q'.1 * q'.2, q'.1⟩ → q = q' := by
      rintro ⟨w, M⟩ hq ⟨w', M'⟩ hq' he
      simp only [Sigma.mk.injEq, heq_eq_eq] at he
      obtain ⟨h1, h2⟩ := he
      subst h2
      have hw2 : 2 ≤ w := (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).1).2
      have : M = M' := Nat.eq_of_mul_eq_mul_left (by omega) h1
      subst this; rfl
    have himg : ((Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2))).image
        (fun q => (⟨q.1 * q.2, q.1⟩ : Σ _ : ℕ, ℕ)) ⊆ T := by
      intro q hq
      obtain ⟨⟨w, M⟩, hwM, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hw, hM⟩ := Finset.mem_sigma.mp hwM
      have hw2 : 2 ≤ w := (Finset.mem_filter.mp hw).2
      obtain ⟨hM0, hMc⟩ := (mem_NAll_iff' hX2).mp hM
      simp only [T, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors]
      have hwM0 : w * M ≠ 0 := Nat.mul_ne_zero (by omega) hM0
      refine ⟨⟨(mem_NAll_iff' hX2).mpr ⟨hwM0, ?_⟩, ?_⟩, ⟨dvd_mul_right w M, hwM0⟩, hw2⟩
      · rw [Vv_mul (by omega) hM0, ← div_div]; exact hMc
      · have : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
        nlinarith
    have hrw : ∑ q ∈ (Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2)),
          (BSCert.X0Band.Hord q.2 : ℝ) * Vv P (q.1 * q.2) ^ (p.ε' - 2) *
            PhiC P p (t / Vv P (q.1 * q.2)) (q.1 * q.2) =
        ∑ q ∈ ((Fset P p t).sigma (fun w => KR.NAll P (t / Vv P w) (p.Xm / 2))).image
          (fun q => (⟨q.1 * q.2, q.1⟩ : Σ _ : ℕ, ℕ)), g q := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨hw, -⟩ := Finset.mem_sigma.mp hq
      have hw2 : 2 ≤ q.1 := (Finset.mem_filter.mp hw).2
      simp only [g]
      rw [Nat.mul_div_cancel_left _ (by omega)]
    have hg0 : ∀ q ∈ T, 0 ≤ g q := fun q _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Vv_pos _).le _))
        (PhiC_nonneg h _ _)
    have hT : ∑ q ∈ T, g q = ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (2 ≤ ·),
        Aw P p M * PhiC P p (t / Vv P M) M := by
      simp only [T, g]
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun M hM => ?_
      have hM2 := (Finset.mem_filter.mp hM).2
      simp only
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_Hord_cofactor hM2]
      unfold Aw; ring
    calc ∑ w ∈ Fset P p t, c t w * bW (P := P) (p := p) t w ≤ _ := hexp
      _ = _ := hrw
      _ ≤ ∑ q ∈ T, g q := Finset.sum_le_sum_of_subset_of_nonneg himg
          (fun q hq _ => hg0 q hq)
      _ = _ := hT
  linarith

/-- **`Vsup` is a super-solution** (the form without the jump source). -/
theorem super (h : ChainHyp P p H) {T0 : ℝ} {S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0) (hS : ∀ t, T0 ≤ t → S t ≤ p.ES / Real.log t)
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2)) :
    Var.Super T0 (Vsup P p) S (Fset P p) c (Nbhd P H) := by
  refine super_J h hT0 (fun t ht => (hS t ht).trans ?_) hc
  have : 0 ≤ (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
    split_ifs; exact h.hj; exact le_rfl
  linarith

/-! ## The comparison `v ≤ V` -/

/-- `V ≥ 0`. -/
lemma Vsup_nonneg (h : ChainHyp P p H) (t : ℝ) : 0 ≤ Vsup P p t :=
  Finset.sum_nonneg fun M _ => mul_nonneg (Aw_nonneg M) (PhiC_nonneg h _ _)

/-- The trivial chain: `Φ(t, 1) ≤ V(t)`. -/
lemma phi_one_le_Vsup (h : ChainHyp P p H) (t : ℝ) : PhiC P p t 1 ≤ Vsup P p t := by
  have hXm := h.hXm
  have hX2 : 0 < p.Xm / 2 := by linarith
  by_cases ht : p.Xm / 2 ≤ t
  · have h1 : (1 : ℕ) ∈ KR.NAll P t (p.Xm / 2) := by
      rw [mem_NAll_iff' hX2, Vv_one, div_one]; exact ⟨one_ne_zero, ht⟩
    have hA1 : Aw P p 1 = 1 := by
      unfold Aw; rw [Vv_one, Real.one_rpow, BSCert.X0Band.Hord_eq 1, if_pos le_rfl]; simp
    have := Finset.single_le_sum (f := fun M => Aw P p M * PhiC P p (t / Vv P M) M)
      (fun M _ => mul_nonneg (Aw_nonneg M) (PhiC_nonneg h _ _)) h1
    simp only [hA1, one_mul, Vv_one, div_one] at this
    exact this
  · push_neg at ht
    have hz : PhiC P p t 1 = 0 := by
      unfold PhiC
      have hc := cutL_ge h 1
      have hcg := cinf_ge h
      have hXR := XR_ge h
      have hr := radJ_le h 1
      rw [if_neg (by linarith), if_neg (by
        intro habs; have := (abs_le.mp habs).1; linarith), add_zero]
    rw [hz]; exact Vsup_nonneg h t

/-- **Step 5 of the proof of Proposition 5.38, solved by the super-solution**: if the variation
satisfies the Step-3 recursion with `0 ≤ c_w ≤ 1.0101 w^{ε-2}` and `S(t) ≤ E_S/log t` above
`T₀`, and the base case `v(t) ≤ Φ(t, 1)` below `T₀` (`Φ(t, 1) = 1[t ≥ c(1)] E_S/log t +
1[|t - X₀| ≤ r(1)] j`: the paper's `v(t) ≤ o_t + j 1[|t - X₀| ≤ 1.01H(t)]`), then
`v(t) ≤ V(t) = ∑_M H_ord(M) M^{ε'-2} Φ(t/M, M)` for every `t`. -/
theorem v_le_Vsup_J (h : ChainHyp P p H) {T0 : ℝ} {v S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0) (hT0wf : 2 ≤ T0 * (1 - p.θ0))
    (hS : ∀ t, T0 ≤ t →
      S t ≤ p.ES / Real.log t + (if |t - p.X0| ≤ radJ P p 1 then p.j else 0))
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2))
    (hrec : Var.RecIneq T0 v S (Fset P p) c (Nbhd P H))
    (hbase : ∀ t, t < T0 → v t ≤ PhiC P p t 1) : ∀ t, v t ≤ Vsup P p t := by
  refine Var.le_of_super hrec (super_J h hT0 hS hc)
    (fun t ht => (hbase t ht).trans (phi_one_le_Vsup h t)) ?_
  intro t ht w hw t' ht'
  have hXm := h.hXm
  obtain ⟨hwA, hw2⟩ := Finset.mem_filter.mp hw
  have hy : p.Xm / 2 ≤ t / Vv P w := ((mem_NAll_iff' (by linarith)).mp hwA).2
  have hrel := h.hrel _ hy
  have hV2 := two_le_Vv h.hp2 hw2
  have ht0 : 0 ≤ t := by
    have := cinf_gt_one h; linarith [h.hKc]
  have hy2 : t / Vv P w ≤ t / 2 := div_le_div_of_nonneg_left ht0 two_pos hV2
  have hθ0 := h.hθ0
  have := ht'.2
  have hT : 2 ≤ t * (1 - p.θ0) := le_trans hT0wf
    (mul_le_mul_of_nonneg_right ht (by linarith [h.hθ01]))
  nlinarith

/-- **Step 5, first display** (level form): `v(t) ≤ ∑_M H_ord(M) M^{ε'-2} E_S/log(t/M) +
j ∑_{M : |t/M - X₀| ≤ R₀} H_ord(M) M^{ε'-2}` (over the levels with `t/M ≥ X₀⁻/2`; the first sum
only over `t/M ≥ c(M)`), the second sum being `v_{X₀}(t)/j` over the window `I'_t` of radius
`R₀` (`= 5.5 H(X₀)` in the paper). -/
theorem v_le_chain_J (h : ChainHyp P p H) {T0 : ℝ} {v S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0) (hT0wf : 2 ≤ T0 * (1 - p.θ0))
    (hS : ∀ t, T0 ≤ t →
      S t ≤ p.ES / Real.log t + (if |t - p.X0| ≤ radJ P p 1 then p.j else 0))
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2))
    (hrec : Var.RecIneq T0 v S (Fset P p) c (Nbhd P H))
    (hbase : ∀ t, t < T0 → v t ≤ PhiC P p t 1) (t : ℝ) :
    v t ≤ ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => cutL P p M ≤ t / Vv P M),
        Aw P p M * (p.ES / Real.log (t / Vv P M)) +
      p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => |t / Vv P M - p.X0| ≤ p.R0),
        Aw P p M := by
  classical
  refine (v_le_Vsup_J h hT0 hT0wf hS hc hrec hbase t).trans ?_
  unfold Vsup PhiC
  simp only [mul_add, Finset.sum_add_distrib]
  apply add_le_add
  · rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun M _ => ?_
    split_ifs <;> simp
  · rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun M _ => ?_
    have hA := Aw_nonneg (P := P) (p := p) M
    have hr := radJ_le h M
    split_ifs with h1 h2
    · rw [mul_comm]
    · exact absurd (h1.trans hr) h2
    · rw [mul_zero]; exact mul_nonneg h.hj hA
    · simp

lemma hS_J_of (h : ChainHyp P p H) {T0 : ℝ} {S : ℝ → ℝ}
    (hS : ∀ t, T0 ≤ t → S t ≤ p.ES / Real.log t) :
    ∀ t, T0 ≤ t →
      S t ≤ p.ES / Real.log t + (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
  intro t ht
  have : 0 ≤ (if |t - p.X0| ≤ radJ P p 1 then p.j else 0) := by
    split_ifs; exact h.hj; exact le_rfl
  linarith [hS t ht]

/-- `v ≤ V` (the form without the jump source). -/
theorem v_le_Vsup (h : ChainHyp P p H) {T0 : ℝ} {v S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0) (hT0wf : 2 ≤ T0 * (1 - p.θ0))
    (hS : ∀ t, T0 ≤ t → S t ≤ p.ES / Real.log t)
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2))
    (hrec : Var.RecIneq T0 v S (Fset P p) c (Nbhd P H))
    (hbase : ∀ t, t < T0 → v t ≤ PhiC P p t 1) : ∀ t, v t ≤ Vsup P p t :=
  v_le_Vsup_J h hT0 hT0wf (hS_J_of h hS) hc hrec hbase

/-- Step 5, first display (the form without the jump source). -/
theorem v_le_chain (h : ChainHyp P p H) {T0 : ℝ} {v S : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hT0 : p.cinf + p.Kc ≤ T0) (hT0wf : 2 ≤ T0 * (1 - p.θ0))
    (hS : ∀ t, T0 ≤ t → S t ≤ p.ES / Real.log t)
    (hc : ∀ t, T0 ≤ t → ∀ w ∈ Fset P p t, 0 ≤ c t w ∧ c t w ≤ 1.0101 * Vv P w ^ (p.ε - 2))
    (hrec : Var.RecIneq T0 v S (Fset P p) c (Nbhd P H))
    (hbase : ∀ t, t < T0 → v t ≤ PhiC P p t 1) (t : ℝ) :
    v t ≤ ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => cutL P p M ≤ t / Vv P M),
        Aw P p M * (p.ES / Real.log (t / Vv P M)) +
      p.j * ∑ M ∈ (KR.NAll P t (p.Xm / 2)).filter (fun M => |t / Vv P M - p.X0| ≤ p.R0),
        Aw P p M :=
  v_le_chain_J h hT0 hT0wf (hS_J_of h hS) hc hrec hbase t

end Margin.Rec

end
