module

public import RequestProject.Beurling.Model.MarginTop
public import RequestProject.Beurling.Noise.RML10Strip
public import RequestProject.Beurling.Noise.RML9Bnd
public import RequestProject.Beurling.Noise.RML7G1

/-!
# §5 fields of `BModel.RestMargin` (Proposition 5.38, Steps 2–6)

Theorems filling the §5 fields of `BModel.RestMargin` (`Model/MarginTop.lean`) for the
canonical data

* `s2mst := fun _ => M` (a bound on `|m|` near the strip, chosen by the caller);
* `e := e10 X₀ M`, the supremum over the strip `z' ∈ [t/w - 0.52 H(t/w), t/w]` of the Step 3
  weight `fE X₀ M z'` (the function in the field `hS2e`).

* `hS2e_10`, `he0_10` : the fields `hS2e`, `he0`;
* `hES0`, `hjP0` : immediate for `ES, jP ≥ 0`.
-/

@[expose] public section

open Finset Real MeasureTheory Set BeurlingSystem Construction BModel KR Queue6 CaplLink

namespace BModel.RML10

variable {X₀ : ℕ}

variable (X₀) in
/-- The Step 3 weight of the field `hS2e` at the constant strip bound `s2mst = M`. -/
noncomputable def fE (M z : ℝ) : ℝ :=
  2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z + 1)) +
    210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 + (6.6 + 4.2 * M) / Queue6.Hc X₀ z

variable (X₀) in
/-- The strip `[c - 0.52 H(c), c]`. -/
def strip (c : ℝ) : Set ℝ := Icc (c - 0.52 * Queue6.Hc X₀ c) c

variable (X₀) in
/-- **The canonical recursion weight** `e(t, w) = sup_{z' ∈ strip(t/w)} fE(z')`. -/
noncomputable def e10 (P : BeurlingSystem) (M t : ℝ) (w : ℕ) : ℝ :=
  sSup (fE X₀ M '' strip X₀ (t / KR.Vl P w))

section Bounds

variable (hX : 10 ^ 8 ≤ Real.log X₀)
include hX

lemma X0_pos : (0 : ℝ) < X₀ := by
  by_contra h
  push_neg at h
  have : (X₀ : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
  rw [this, Real.log_zero] at hX; linarith

lemma Hc_ge_one (z : ℝ) : 1 ≤ Queue6.Hc X₀ z := by
  unfold Queue6.Hc
  exact capH_ge_one (Nat.cast_nonneg _) hX (le_max_right _ _)

lemma uS_ge (m : ℕ) : (X₀ : ℝ) ≤ uS X₀ m := by
  unfold uS
  have := X0_pos hX
  have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  nlinarith

lemma uS_m1z_le {z c : ℝ} (hzc : z ≤ c) : uS X₀ (m1z X₀ z) ≤ max c X₀ := by
  have h0 := X0_pos hX
  have hH := (Hc_ge_one hX z)
  have := (mB_spec h0 (le_max_right (z - Queue6.Hc X₀ z) (X₀ : ℝ))).1
  unfold m1z
  refine this.trans (max_le_max (by linarith) le_rfl)

omit hX in
lemma uS_succ (m : ℕ) : uS X₀ (m + 1) = 2 * uS X₀ m := by
  unfold uS; ring

lemma log_uS_ge (m : ℕ) : Real.log X₀ ≤ Real.log (uS X₀ m) :=
  Real.log_le_log (X0_pos hX) (uS_ge hX m)

omit hX in
lemma s2E3_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ s2E3 X₀ u := by
  unfold s2E3
  have := Real.log_nonneg hu
  positivity

omit hX in
lemma s2E3_le {u : ℝ} (hu : 1 ≤ u) : s2E3 X₀ u ≤ 9 * Real.log u := by
  unfold s2E3
  have hl := Real.log_nonneg hu
  have hm : 0 ≤ max (Real.log (Xm X₀)) (Real.sqrt (Real.log u * Real.log (Real.log u)) / 2) :=
    le_trans (by positivity) (le_max_right _ _)
  have he : Real.exp (-(max (Real.log (Xm X₀))
      (Real.sqrt (Real.log u * Real.log (Real.log u)) / 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

lemma one_le_uS (m : ℕ) : 1 ≤ uS X₀ m := by
  have := uS_ge hX m
  have h1 : (1 : ℝ) ≤ X₀ := by
    have := X0_pos hX
    by_contra hc; push_neg at hc
    have : Real.log X₀ < 0 := Real.log_neg this hc
    linarith
  linarith

lemma fE_nonneg {M : ℝ} (hM : 0 ≤ M) (z : ℝ) : 0 ≤ fE X₀ M z := by
  unfold fE
  have h1 := s2E3_nonneg (X₀ := X₀) (one_le_uS hX (m1z X₀ z))
  have h2 := s2E3_nonneg (X₀ := X₀) (one_le_uS hX (m1z X₀ z + 1))
  have h3 : 0 ≤ 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 := by positivity
  have h4 : 0 ≤ (6.6 + 4.2 * M) / Queue6.Hc X₀ z :=
    div_nonneg (by linarith) (by linarith [Hc_ge_one hX z])
  linarith

lemma fE_le {M : ℝ} (hM : 0 ≤ M) {z c : ℝ} (hzc : z ≤ c) :
    fE X₀ M z ≤ 4.4 * (9 * Real.log (2 * max c X₀)) + 210 / Real.log X₀ ^ 6 +
      (6.6 + 4.2 * M) := by
  unfold fE
  have hX0 := X0_pos hX
  have hu1 := uS_m1z_le hX hzc
  have hu2 : uS X₀ (m1z X₀ z + 1) ≤ 2 * max c X₀ := by
    rw [uS_succ]; linarith
  have hu1' : uS X₀ (m1z X₀ z) ≤ 2 * max c X₀ := by
    have := le_max_right c (X₀ : ℝ); linarith
  have hpos1 := one_le_uS hX (m1z X₀ z)
  have hpos2 := one_le_uS hX (m1z X₀ z + 1)
  have hmax : (1 : ℝ) ≤ 2 * max c X₀ := by linarith
  have l1 : Real.log (uS X₀ (m1z X₀ z)) ≤ Real.log (2 * max c X₀) :=
    Real.log_le_log (by linarith) hu1'
  have l2 : Real.log (uS X₀ (m1z X₀ z + 1)) ≤ Real.log (2 * max c X₀) :=
    Real.log_le_log (by linarith) hu2
  have e1 := s2E3_le (X₀ := X₀) hpos1
  have e2 := s2E3_le (X₀ := X₀) hpos2
  have hl := log_uS_ge hX (m1z X₀ z)
  have hlX : 0 < Real.log X₀ := by linarith
  have h3 : 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 ≤ 210 / Real.log X₀ ^ 6 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hlX.le hl 6)
  have hH := Hc_ge_one hX z
  have h4 : (6.6 + 4.2 * M) / Queue6.Hc X₀ z ≤ 6.6 + 4.2 * M :=
    div_le_self (by linarith) hH
  nlinarith

lemma bdd_fE {M : ℝ} (hM : 0 ≤ M) (c : ℝ) : BddAbove (fE X₀ M '' strip X₀ c) := by
  refine ⟨4.4 * (9 * Real.log (2 * max c X₀)) + 210 / Real.log X₀ ^ 6 + (6.6 + 4.2 * M), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact fE_le hX hM hz.2

lemma fE_le_e10 {M : ℝ} (hM : 0 ≤ M) (P : BeurlingSystem) (t : ℝ) (w : ℕ) {z : ℝ}
    (hz : z ∈ strip X₀ (t / KR.Vl P w)) : fE X₀ M z ≤ e10 X₀ P M t w :=
  le_csSup (bdd_fE hX hM _) (mem_image_of_mem _ hz)

lemma e10_nonneg {M : ℝ} (hM : 0 ≤ M) (P : BeurlingSystem) (t : ℝ) (w : ℕ) :
    0 ≤ e10 X₀ P M t w := by
  have hc : t / KR.Vl P w ∈ strip X₀ (t / KR.Vl P w) := by
    refine ⟨?_, le_rfl⟩
    have := Hc_ge_one hX (t / KR.Vl P w); linarith
  exact (fE_nonneg hX hM _).trans (fE_le_e10 hX hM P t w hc)

end Bounds

variable {θ : ℝ}

/-- **The field `hS2e`** of `RestMargin`, at `s2mst = fun _ => M` and `e = e10 X₀ (PR θ X₀ ω) M`. -/
theorem hS2e_10 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {M : ℝ} (hM : 0 ≤ M) (ES jP b : ℝ) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω)
        (RML7.canonP X₀ epsH ES jP) t, ∀ z',
      t / KR.Vl (PR θ X₀ ω) w - 0.52 * Queue6.Hc X₀ (t / KR.Vl (PR θ X₀ ω) w) ≤ z' →
        z' ≤ t / KR.Vl (PR θ X₀ ω) w → (fun z => 2.2 * s2E3 X₀ (uS X₀ (m1z X₀ z)) + 2.2 * s2E3 X₀
          (uS X₀ (m1z X₀ z + 1)) + 210 / Real.log (uS X₀ (m1z X₀ z)) ^ 6 +
            (6.6 + 4.2 * (fun _ => M) z) / Queue6.Hc X₀ z) z' ≤
          e10 X₀ (PR θ X₀ ω) M t w := by
  intro t _ _ w _ z' h1 h2
  exact fE_le_e10 hX hM _ t w ⟨h1, h2⟩

/-- **The field `he0`** of `RestMargin`, at `e = e10 X₀ (PR θ X₀ ω) M`. -/
theorem he0_10 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {M : ℝ} (hM : 0 ≤ M) (ES jP b : ℝ) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b → ∀ w ∈ Margin.Rec.Fset (PR θ X₀ ω)
        (RML7.canonP X₀ epsH ES jP) t, 0 ≤ e10 X₀ (PR θ X₀ ω) M t w :=
  fun t _ _ w _ => e10_nonneg hX hM _ t w

/-! ## Step 2: the strip comparison (fields `hS2sp`, `hS2sm`) -/

/-- The realised width `H_c` satisfies the strip hypotheses `WidthH` for `ε ≤ 1/10`. -/
theorem widthH_Hc (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hS : KR.WidthReal.CapHSlope X₀ ε) : Margin.Strip.WidthH (Queue6.Hc X₀) X₀ ε where
  mono := KR.WidthReal.Hc_mono hX
  ge_one := Hc_ge_one hX
  sq_le := fun y => by
    have hX0 := X0_pos hX
    have hm1 : (1 : ℝ) ≤ max y X₀ := by
      have h1 : (1 : ℝ) ≤ X₀ := by
        by_contra hc; push_neg at hc
        have : Real.log X₀ < 0 := Real.log_neg hX0 hc
        linarith
      exact h1.trans (le_max_right _ _)
    have h := InitialRange.capH_le_rpow (Nat.cast_nonneg X₀) hX (le_max_right y (X₀ : ℝ))
    have hpos : 0 ≤ capH X₀ (max y X₀) := le_trans zero_le_one (Hc_ge_one hX y)
    unfold Queue6.Hc
    calc capH X₀ (max y X₀) ^ 2 ≤ ((max y X₀) ^ (1 / 8 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hpos h 2
      _ = (max y X₀) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ (max y X₀) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = max y X₀ := Real.rpow_one _
  X0_ge := by
    have hX0 := X0_pos hX
    by_contra hc; push_neg at hc
    have : Real.log X₀ < 0 := Real.log_neg hX0 hc
    linarith
  ε0 := hε0
  ε1 := hε1
  ratio := fun s t hst => KR.RML9.Hc_incr_ratio hX hε0 (by linarith) hS hst

lemma s2δ_mul (z M : ℝ) (hX : 10 ^ 8 ≤ Real.log X₀) (hM : 0 ≤ M) :
    2 * M ≤ 1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * M := by
  unfold Queue6.s2δ
  have h := Hc_ge_one hX z
  have : 1.05 * (2 / Queue6.Hc X₀ z) * Queue6.Hc X₀ z = 2.1 := by field_simp; norm_num
  rw [this]; linarith

/-- **The field `hS2sp`** of `RestMargin` at `s2mst = fun _ => M`, from `|m| ≤ M` and
integrability of `m` on `[z - 3H(z), z + 3H(z)]` at the strip points (Model: the bound on the
margin density near the strips). -/
theorem hS2sp_10 (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hS : KR.WidthReal.CapHSlope X₀ ε) (ω : JitterΩ) {M : ℝ} (hM : 0 ≤ M) (ES jP b : ℝ)
    (hm : ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z →
      IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z), |marginM θ X₀ ω x| ≤ M) :
    ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
      |(∫ r in Margin.Exact.Aplus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
        ∫ r in (z + Queue6.Hc X₀ z / 2)..(z + Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
        1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * (fun _ => M) z := by
  intro z hz s hs0 hs
  obtain ⟨hi, hb⟩ := hm z hz
  exact ((widthH_Hc hX hε0 hε1 hS).strip_cmp_plus hs0 hs hi hb).trans (s2δ_mul z M hX hM)

/-- **The field `hS2sm`** of `RestMargin` at `s2mst = fun _ => M` (as `hS2sp_10`). -/
theorem hS2sm_10 (hX : 10 ^ 8 ≤ Real.log X₀) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hS : KR.WidthReal.CapHSlope X₀ ε) (ω : JitterΩ) {M : ℝ} (hM : 0 ≤ M) (ES jP b : ℝ)
    (hm : ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z →
      IntegrableOn (marginM θ X₀ ω) (Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z)) ∧
      ∀ x ∈ Icc (z - 3 * Queue6.Hc X₀ z) (z + 3 * Queue6.Hc X₀ z), |marginM θ X₀ ω x| ≤ M) :
    ∀ z, S2Rng θ X₀ ω (RML7.canonP X₀ epsH ES jP) ((RML7.canonP X₀ epsH ES jP).cinf +
      (RML7.canonP X₀ epsH ES jP).Kc) b z → ∀ s, 0 ≤ s → s ≤ 1.01 * Queue6.Hc X₀ z →
      |(∫ r in Margin.Exact.Aminus (Queue6.Hc X₀) z s, marginM θ X₀ ω r) -
        ∫ r in (z - Queue6.Hc X₀ z / 2)..(z - Queue6.Hc X₀ z / 2 + s), marginM θ X₀ ω r| ≤
        1.05 * (Queue6.s2δ X₀) z * Queue6.Hc X₀ z * (fun _ => M) z := by
  intro z hz s hs0 hs
  obtain ⟨hi, hb⟩ := hm z hz
  exact ((widthH_Hc hX hε0 hε1 hS).strip_cmp_minus hs0 hs hi hb).trans (s2δ_mul z M hX hM)

/-! ## `ES`, `jP`, Step 4 (fields `hES0`, `hjP0`, `hS4`) -/

theorem hES0_10 {ES : ℝ} (h : 0 ≤ ES) : 0 ≤ ES := h

/-- The canonical `jP = jzX X₀` (the jump at `X₀`, `V_{X₀}` term of Step 5) is `≥ 0`. -/
theorem hjP0_10 (hc : Cond θ X₀) : 0 ≤ jzX X₀ := jzX_nonneg hc

lemma one_le_X0 (hX : 10 ^ 8 ≤ Real.log X₀) : (1 : ℝ) ≤ X₀ := by
  have hX0 := X0_pos hX
  by_contra hc; push_neg at hc
  have : Real.log X₀ < 0 := Real.log_neg hX0 hc
  linarith

lemma Xm_nonneg (hX : 10 ^ 8 ≤ Real.log X₀) : 0 ≤ Xm X₀ := by
  have h1 := one_le_X0 hX
  have hH := InitialRange.capH_le_rpow (Nat.cast_nonneg X₀) hX le_rfl
  have h8 : (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ X₀ := by
    calc (X₀ : ℝ) ^ (1 / 8 : ℝ) ≤ (X₀ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = X₀ := Real.rpow_one _
  unfold Xm; linarith

lemma T0_gt_one (hX : 10 ^ 8 ≤ Real.log X₀) (ES jP : ℝ) :
    1 < (RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc := by
  have hk := Hc_ge_one hX (2 * X₀)
  have hKc : (RML7.canonP X₀ epsH ES jP).Kc = 5 * Queue6.Hc X₀ (2 * X₀) := rfl
  have hcinf : (RML7.canonP X₀ epsH ES jP).cinf = 1.21 * (Xm X₀ / 2) := rfl
  have := Xm_nonneg hX
  rw [hKc, hcinf]; linarith

/-- **The field `hS4`** of `RestMargin`, from the Step 4 bound at every `t ∈ [T₀, b]`
(`log t · (o_V + 2η_V + ∑_w e/w) ≤ E_S`; e.g. from `Margin.RML6.hS4_of` / `Margin.Var.step4`
with Lemma 5.21 and Lemma 5.22's `ν, δ`). -/
theorem hS4_10 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) {M : ℝ} (ES jP b : ℝ)
    (h4 : ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t →
      t ≤ b → Real.log t * ((oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t +
        ∑ w ∈ Margin.Rec.Fset (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t,
          e10 X₀ (PR θ X₀ ω) M t w / KR.Vl (PR θ X₀ ω) w) ≤ ES) :
    ∀ t, ((RML7.canonP X₀ epsH ES jP).cinf + (RML7.canonP X₀ epsH ES jP).Kc) ≤ t → t ≤ b →
      (oVc θ X₀ ω) t + 2 * (ηVc θ X₀ ω (RML7.canonP X₀ epsH ES jP)) t + ∑ w ∈ Margin.Rec.Fset
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t, e10 X₀ (PR θ X₀ ω) M t w /
          KR.Vl (PR θ X₀ ω) w ≤ (RML7.canonP X₀ epsH ES jP).ES / Real.log t := by
  intro t ht htb
  have h1 := T0_gt_one hX ES jP
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  rw [show (RML7.canonP X₀ epsH ES jP).ES = ES from rfl, le_div_iff₀ hl, mul_comm]
  exact h4 t ht htb

/-! ## The error sizes (field `hsmall`) -/

lemma exp_ge_pow (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
  have h := Real.exp_one_gt_d9
  rw [← Real.exp_one_rpow, Real.rpow_natCast]
  exact pow_le_pow_left₀ (by norm_num) h.le n

lemma exp_ge_big {n : ℕ} {c : ℝ} (h : c ≤ (2.7182818283 : ℝ) ^ n) : c ≤ Real.exp n :=
  h.trans (exp_ge_pow n)

lemma EBRc_tiny : BModel.EBRc ≤ 1 / 10 ^ 30 := by
  unfold BModel.EBRc
  have h : (10 : ℝ) ^ 30 ≤ Real.exp 76 := by
    have := exp_ge_big (n := 76) (c := 10 ^ 30) (by norm_num)
    exact_mod_cast this
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) h

/-- `x^{1/8} ≤ 10⁻²¹ x` for `log x ≥ 10⁸`. -/
lemma rpow_eighth_tiny {x : ℝ} (hx0 : 0 < x) (hx : 10 ^ 8 ≤ Real.log x) :
    x ^ (1 / 8 : ℝ) ≤ 1 / 10 ^ 21 * x := by
  rw [Real.rpow_def_of_pos hx0]
  have hxe : x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
  have h49 : (10 : ℝ) ^ 21 ≤ Real.exp 49 := by
    have := exp_ge_big (n := 49) (c := 10 ^ 21) (by norm_num)
    exact_mod_cast this
  have : (10 : ℝ) ^ 21 * Real.exp (Real.log x * (1 / 8)) ≤ Real.exp (Real.log x) := by
    calc (10 : ℝ) ^ 21 * Real.exp (Real.log x * (1 / 8))
        ≤ Real.exp 49 * Real.exp (Real.log x * (1 / 8)) :=
          mul_le_mul_of_nonneg_right h49 (Real.exp_pos _).le
      _ = Real.exp (49 + Real.log x * (1 / 8)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith)
  rw [← hxe] at this
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  linarith

/-- `6 log t / H(t) ≤ 10⁻³⁰` for `t ≥ X₀`. -/
lemma logH_tiny (hX : 10 ^ 8 ≤ Real.log X₀) {t : ℝ} (ht : (X₀ : ℝ) ≤ t) :
    6 * Real.log t / Queue6.Hc X₀ t ≤ 1 / 10 ^ 30 := by
  obtain ⟨hL, -, hll⟩ := CaplLink.logs_of_ge (Nat.cast_nonneg _) hX ht
  set L := Real.log t
  set l := Real.log L
  have hHc : Queue6.Hc X₀ t = capH X₀ t := by unfold Queue6.Hc; rw [max_eq_left ht]
  have hstd : Real.exp (8 * l ^ 2) ≤ Queue6.Hc X₀ t := by
    rw [hHc]; unfold capH; exact le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hl18 : 18 ≤ l := by
    have h18 : Real.exp 18 ≤ 10 ^ 8 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 18
        _ ≤ 10 ^ 8 := by norm_num
    have := Real.log_le_log (Real.exp_pos 18) (h18.trans hL)
    rwa [Real.log_exp] at this
  have hLe : L = Real.exp l := (Real.exp_log hL0).symm
  have h72 : (6 : ℝ) * 10 ^ 30 ≤ Real.exp 72 := by
    have := exp_ge_big (n := 72) (c := 6 * 10 ^ 30) (by norm_num)
    exact_mod_cast this
  have hbig : 6 * 10 ^ 30 * L ≤ Real.exp (8 * l ^ 2) := by
    calc 6 * 10 ^ 30 * L ≤ Real.exp 72 * Real.exp l := by
          rw [← hLe]; exact mul_le_mul_of_nonneg_right h72 hL0.le
      _ = Real.exp (72 + l) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (8 * l ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hH0 : 0 < Queue6.Hc X₀ t := lt_of_lt_of_le (Real.exp_pos _) hstd
  rw [div_le_div_iff₀ hH0 (by positivity)]
  nlinarith

/-- `o(1)` of Theorem 5.37: `oTot ≤ 2 H(x)/x ≤ 10⁻²⁰` for `x ≥ X₀`, `0 ≤ E_BR + j ≤ 1`. -/
lemma oTot_tiny (hX : 10 ^ 8 ≤ Real.log X₀) {x E j : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (_hEj0 : 0 ≤ E + j) (hEj : E + j ≤ 1) :
    KR.Chain.oTot (Queue6.Hc X₀ x) x E j ≤ 1 / 10 ^ 20 := by
  obtain ⟨hL, -, -⟩ := CaplLink.logs_of_ge (Nat.cast_nonneg _) hX hx
  have hx0 : 0 < x := lt_of_lt_of_le (X0_pos hX) hx
  set H := Queue6.Hc X₀ x
  have hH1 : 1 ≤ H := Hc_ge_one hX x
  have hHle : H ≤ x ^ (1 / 8 : ℝ) := by
    have : H = capH X₀ x := by simp only [H]; unfold Queue6.Hc; rw [max_eq_left hx]
    rw [this]; exact InitialRange.capH_le_rpow (Nat.cast_nonneg X₀) hX hx
  have hHx : H ≤ 1 / 10 ^ 21 * x := hHle.trans (rpow_eighth_tiny hx0 hL)
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  -- the two logarithms
  have hu : H / (2 * x) ≤ 1 / 10 ^ 21 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hp : x + H / 2 = x * (1 + H / (2 * x)) := by field_simp
  have hm : x - H / 2 = x * (1 - H / (2 * x)) := by field_simp
  have hpos1 : 0 < 1 + H / (2 * x) := by positivity
  have hpos2 : 0 < 1 - H / (2 * x) := by linarith
  have hlp : Real.log (x + H / 2) = L + Real.log (1 + H / (2 * x)) := by
    rw [hp, Real.log_mul hx0.ne' hpos1.ne']
  have hlm : Real.log (x - H / 2) = L + Real.log (1 - H / (2 * x)) := by
    rw [hm, Real.log_mul hx0.ne' hpos2.ne']
  have hv0 : 0 ≤ H / (2 * x) := by positivity
  have a1 : Real.log (1 + H / (2 * x)) ≤ H / (2 * x) := by
    have := Real.log_le_sub_one_of_pos hpos1; linarith
  have a1' : 0 ≤ Real.log (1 + H / (2 * x)) := Real.log_nonneg (by linarith)
  have a2 : -(H / (2 * x) / (1 - H / (2 * x))) ≤ Real.log (1 - H / (2 * x)) := by
    have := Real.one_sub_inv_le_log_of_pos hpos2
    have e : ∀ u : ℝ, u < 1 → 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by
      intro u hu
      have : 1 - u ≠ 0 := by linarith
      field_simp; ring
    rw [e _ (by linarith)] at this
    linarith
  have a2' : Real.log (1 - H / (2 * x)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hq : H / (2 * x) / (1 - H / (2 * x)) ≤ 2 / 10 ^ 21 := by
    rw [div_le_iff₀ hpos2]; nlinarith
  set lp := Real.log (1 + H / (2 * x))
  set lm := Real.log (1 - H / (2 * x))
  unfold KR.Chain.oTot
  rw [hlp, hlm]
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hd1 : 1 ≤ L + lp := by linarith
  have hd2 : 1 ≤ L + lm := by linarith
  have t1 : 1 - L / (L + lp) ≤ 1 / 10 ^ 21 := by
    have e : 1 - L / (L + lp) = lp / (L + lp) := by field_simp; ring
    rw [e]
    exact (div_le_self a1' hd1).trans (by linarith)
  have t1' : 0 ≤ 1 - L / (L + lp) := by
    have e : 1 - L / (L + lp) = lp / (L + lp) := by field_simp; ring
    rw [e]; positivity
  have t2 : L / (L + lm) - 1 ≤ 3 / 10 ^ 21 := by
    have e : L / (L + lm) - 1 = -lm / (L + lm) := by field_simp; ring
    rw [e]
    exact (div_le_self (by linarith) hd2).trans (by linarith)
  have t2' : 0 ≤ L / (L + lm) - 1 := by
    have e : L / (L + lm) - 1 = -lm / (L + lm) := by field_simp; ring
    rw [e]; exact div_nonneg (by linarith) (by linarith)
  have : (L / (L + lm) - 1) * (E + j) ≤ 3 / 10 ^ 21 :=
    (mul_le_of_le_one_right t2' hEj).trans t2
  nlinarith

/-- **The field `hsmall`** of `RestMargin`, in generic form: the error sizes are `≤ 0.01`
once the four non-tiny terms are (`a_K`, `G`, `j_{X₀}`, `6.5 E_S + V_{X₀}`). -/
theorem hsmall_gen (hX : 10 ^ 8 ≤ Real.log X₀) {x j aKv Gv ES VXv a2 a3 a4 a5 : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hj0 : 0 ≤ j) (hj : j ≤ a4) (ha4 : a4 ≤ 1 / 2) (haK : aKv ≤ a2)
    (hG : Gv ≤ a3) (hES : 6.5 * ES + VXv ≤ a5) (hPhi : KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2) ≤
      Real.exp (-200)) (hsum : a2 + a3 + a4 + a5 ≤ 0.0099) :
    KR.Chain.oTot (Queue6.Hc X₀ x) x BModel.EBRc j + (aKv + Gv + 6 * Real.log x /
      Queue6.Hc X₀ x) + BModel.EBRc + j + 54 * (sηB X₀) + 6 * Real.log x / Queue6.Hc X₀ x +
      6.5 * ES + VXv ≤ 0.01 := by
  have hE := EBRc_tiny
  have hE0 : 0 ≤ BModel.EBRc := (Real.exp_pos _).le
  have h1 := oTot_tiny hX hx (j := j) (E := BModel.EBRc) (by linarith) (by linarith)
  have h2 := logH_tiny hX hx
  have h3 : 54 * sηB X₀ ≤ 1 / 10 ^ 30 := by
    unfold sηB
    have h200 : (10 : ℝ) ^ 40 ≤ Real.exp 200 := by
      have := exp_ge_big (n := 200) (c := 10 ^ 40) (by norm_num)
      exact_mod_cast this
    have he : Real.exp (-200) ≤ 1 / 10 ^ 40 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h200
    have hP0 : 0 ≤ KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2) := by
      unfold KR.TNP.Phi
      have := Hc_ge_one hX (Xm X₀ / 2)
      have hxm := Xm_nonneg hX
      positivity
    nlinarith
  linarith

section Fields

open KR.TNP KR.Chain CaplLink

lemma X0_le_X1 (hX : 10 ^ 8 ≤ Real.log X₀) : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ (1.01 : ℝ) := by
  have h1 := one_le_X0 hX
  calc (X₀ : ℝ) = (X₀ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (X₀ : ℝ) ^ (1.01 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-- **The field `hsmall`** of `RestMargin` (Model's concrete `a`, `b`, `j_{X₀}`, `E_S`, `V_{X₀}`),
from bounds `a₂, a₃, a₄, a₅` on the `a_K`-term, the `G`-term, `j_{X₀}` and `6.5 E_S + V_{X₀}`
with `a₂ + a₃ + a₄ + a₅ ≤ 0.0099` and `Φ₂(X₀⁻/2) ≤ e^{-200}` (`WidthReal.Phi_tiny`); all
other terms are proved `≤ 10⁻²⁰`. -/
theorem hsmall_10 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) (nb : ℕ → ℝ) (ES jP b a2 a3 a4 a5 : ℝ)
    (hj : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      0 ≤ jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ∧
      jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
        (NKc X₀) t ≤ a4) (ha4 : a4 ≤ 1 / 2)
    (haK : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      KR.RML6K.aK (CNt X₀) (SK θ X₀ ω nb t) (Queue6.Hc X₀) t ≤ a2)
    (hG : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      35.8 * CNt X₀ * 10 * ∑ i ∈ Finset.range (Jc X₀ t + 1), Real.log (3 *
        (Xm X₀ * 2 ^ i)) ^ 2 * (obG X₀ i + FrBv θ X₀ ω nb i) ≤ a3)
    (hEV : ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
      6.5 * (RML7.canonP X₀ epsH ES jP).ES + VX (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t ≤ a5)
    (hPhi : KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2) ≤ Real.exp (-200))
    (hsum : a2 + a3 + a4 + a5 ≤ 0.0099) :
    ∀ t, (X₀ : ℝ) ^ (1.01 : ℝ) ≤ t → t ≤ b →
    oTot (Queue6.Hc X₀ t) t ((fun _ => EBRc) t) ((fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀)
      (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t) +
      ((fun x => KR.RML6K.aK (CNt X₀) (SK θ X₀ ω nb x) (Queue6.Hc X₀) x) t +
        (fun x => 35.8 * CNt X₀ * 10 * ∑ i ∈ Finset.range (Jc X₀ x + 1), Real.log (3 *
          (Xm X₀ * 2 ^ i)) ^ 2 *
            (obG X₀ i + FrBv θ X₀ ω nb i)) t + 6 * Real.log t / Queue6.Hc X₀ t) +
              (fun _ => EBRc) t + (fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω)
                (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t +
      54 * (sηB X₀) + 6 * Real.log t / Queue6.Hc X₀ t + 6.5 * (RML7.canonP X₀ epsH ES jP).ES + VX
        (PR θ X₀ ω) (RML7.canonP X₀ epsH ES jP) t ≤ 0.01 := by
  intro t ht htb
  have hxt : (X₀ : ℝ) ≤ t := (X0_le_X1 hX).trans ht
  obtain ⟨hj0, hj1⟩ := hj t ht htb
  have := hsmall_gen hX hxt hj0 hj1 ha4 (haK t ht htb) (hG t ht htb) (hEV t ht htb) hPhi hsum
  simp only
  linarith

end Fields

section Sum

open KR.TNP KR.Chain CaplLink

/-- **The field `hsum`** of `RestMargin` (Step 6(b), "Sum"): on `[2X₀, X₀^{1.01}] ∩ (-∞, b]`,
`ρ^sh T'(t) log t - j_{X₀}(t) - 10⁻¹² ≤ m(t) log t`. Inputs at each such `t`: Proposition 5.26
(`log t |BR_c(t)| ≤ E_BR`, from `KR.TcLoc.prop_5_26_loc` with `sizeE_le`), Lemma 5.27
(`|R_res 1 - ρ^sh 1|(t) ≤ 𝔅 + 4.3 C_N E_θ/log t`, from `KR.lemma_5_27`), the boundedness of the
`j_{X₀}` family on `W_t` (Model: `hbdd_c`), and the margin decomposition
`(R_res T'(t) - m(t)) log t ≤ 10⁻¹² - E_BR` (Model/§5: `m = R_res T'` up to the noise on
`[2X₀, X₀^{1.01}]`). -/
theorem hsum_10 (hX : 10 ^ 8 ≤ Real.log X₀) (ω : JitterΩ) (b : ℝ)
    (hO : KR.Ops.OpHyp (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀))
    {εW θW : ℝ} (hP : KR.PaperWidth (Queue6.Hc X₀) (Xm X₀) εW θW)
    (hj00 : 0 ≤ jzX X₀) (hTm : Measurable (TcR θ X₀ ω (jzX X₀)))
    (hin : ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      Xm X₀ ≤ t ∧ 0 < Real.log t ∧
      (∀ u, u ≤ 1.2 * t → |TcR θ X₀ ω (jzX X₀) u| ≤ 2) ∧
      Real.log t * |BRc (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
        (TcR θ X₀ ω (jzX X₀))| ≤ EBRc ∧
      |Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t (KR.Chain.ind X₀) -
          rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (KR.Chain.ind X₀)| ≤
        xbB (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t X₀ (epsH / 10) lamH +
          4.3 * CNc X₀ * (∑ v ∈ dyScales X₀ t (NKc X₀ t).1, Real.log (2 * v) *
            TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NKc X₀ t).2 v) / Real.log t ∧
      BddAbove (Set.range fun y : {y : ℝ // InW (Queue6.Hc X₀ t) t y} =>
        jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
          (NKc X₀ y.1).1 (NKc X₀ y.1).2 y.1) ∧
      (Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
          (fun s => TcR θ X₀ ω (jzX X₀) s + (jzX X₀) * ind X₀ s) - marginM θ X₀ ω t) *
        Real.log t ≤ 1 / 10 ^ 12 - EBRc) :
    ∀ t, 2 * (X₀ : ℝ) ≤ t → t ≤ (X₀ : ℝ) ^ (1.01 : ℝ) → t ≤ b →
      rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω (jzX X₀) s +
        (jzX X₀) * ind X₀ s) *
        Real.log t - (fun x => jXdef (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀
          (epsH / 10) lamH (jzX X₀) (NKc X₀) x) t - 1 / 10 ^ 12 ≤ marginM θ X₀ ω t *
            Real.log t := by
  intro t h1 h2 h3
  obtain ⟨hs, hls, hTb, hBR, hXB, hbdd, hRm⟩ := hin t h1 h2 h3
  have hd := KR.RML7.abs_Rres_sub_rhoSh_loc (tw := twR θ X₀ ω) (j0 := jzX X₀) hO hP hs hls hTm
    hTb hBR hXB
  have hH0 : 0 ≤ Queue6.Hc X₀ t := le_trans zero_le_one (Hc_ge_one hX t)
  have hW : InW (Queue6.Hc X₀ t) t t := ⟨by linarith, by linarith⟩
  have hjx := le_jXdef (P := PR θ X₀ ω) (H := Queue6.Hc X₀) (tw := twR θ X₀ ω) (X0m := Xm X₀)
    (X0 := X₀) (θ := epsH / 10) (lam0 := lamH) (j0 := jzX X₀) (NK := NKc X₀) hW hbdd
  have hjat : jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH (jzX X₀)
      (NKc X₀ t).1 (NKc X₀ t).2 t = |jzX X₀| * (xbB (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω)
        (Xm X₀) t X₀ (epsH / 10) lamH + 4.3 * CNc X₀ * (∑ v ∈ dyScales X₀ t (NKc X₀ t).1,
          Real.log (2 * v) * TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NKc X₀ t).2 v) /
            Real.log t) * Real.log t := by
    unfold jXat; rw [abs_of_nonneg hj00]
  have hab := abs_le.mp hd
  have hmul : (rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω (jzX X₀) s +
        jzX X₀ * KR.Chain.ind X₀ s) - Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
        (fun s => TcR θ X₀ ω (jzX X₀) s + jzX X₀ * KR.Chain.ind X₀ s)) * Real.log t ≤
      EBRc + jXat (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) X₀ (epsH / 10) lamH
        (jzX X₀) (NKc X₀ t).1 (NKc X₀ t).2 t := by
    rw [hjat]
    have := mul_le_mul_of_nonneg_right (by linarith [hab.1] :
      rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) t (fun s => TcR θ X₀ ω (jzX X₀) s +
        jzX X₀ * KR.Chain.ind X₀ s) - Rres (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) t
        (fun s => TcR θ X₀ ω (jzX X₀) s + jzX X₀ * KR.Chain.ind X₀ s) ≤
        EBRc / Real.log t + |jzX X₀| * (xbB (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω)
        (Xm X₀) t X₀ (epsH / 10) lamH + 4.3 * CNc X₀ * (∑ v ∈ dyScales X₀ t (NKc X₀ t).1,
          Real.log (2 * v) * TNP.sTheta (PR θ X₀ ω) (Queue6.Hc X₀) (Xm X₀) (NKc X₀ t).2 v) /
            Real.log t)) hls.le
    rw [add_mul, div_mul_cancel₀ _ hls.ne'] at this
    exact this
  simp only
  unfold KR.Chain.ind at *
  nlinarith

end Sum

end BModel.RML10

end
