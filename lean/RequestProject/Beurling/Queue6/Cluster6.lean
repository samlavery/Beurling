module

public import RequestProject.Beurling.Queue6.ClusterLevel
public import RequestProject.Beurling.Model.RFLink
public import RequestProject.Beurling.RankFull.TopBound

/-!
# The cluster events E1 through the window model of Appendix A (Proposition 6.11)

At the dyadic height `z_n = (X₀/2) 2^n`, the cluster event is stated in the window model of
`RankFull` for the construction (Model/RFLink.lean: the decided slots `decOf J`, the values
`qOf J`, `J = constructionLaw2`):

* `Queue6.gridW n` : the grid windows `[kδ₁, (k + 2)δ₁)` with left end in `[z, 2z)`;
* `Queue6.EclW hc hev n` : every grid window holds at most `M₁(z)` window elements;
* `Queue6.tB hc n` : the target bound `T(x) ≤ 3x` up to `u_n/2` (`tBound`);
* `Queue6.clusterUpTo_of_eclW` : on these events (all stages good, jitters in `[0, 1]`),
  `ClusterUpTo` holds, by `clusterUpTo_of_windows2`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono RankFull RankFull.Config

namespace Queue6

variable {θ : ℝ} {X₀ : ℕ}

/-! ### The window-model parameters at a height -/

/-- The number of decided slots needed below `2z + 1`: `⌊24(2z + 1)/7⌋ + 1`. -/
noncomputable def NpZ (z : ℝ) : ℕ := ⌊24 / 7 * (2 * z + 1)⌋₊ + 1

/-- The degree bound: `⌈(log z + 1.4)/log X₀⁻⌉`. -/
noncomputable def DpZ (X₀ : ℕ) (z : ℝ) : ℕ := ⌈(Real.log z + 1.4) / Real.log (Xm X₀)⌉₊

/-- The rigid-part bound: `⌈2z + 1⌉`. -/
noncomputable def DmaxZ (z : ℝ) : ℕ := ⌈2 * z + 1⌉₊

/-- The grid windows at the height `z_n`, by their index `k`. -/
noncomputable def gridW (X₀ : ℕ) (n : ℕ) : Finset ℤ :=
  Finset.Icc ⌈zH X₀ n / gridDelta (zH X₀ n)⌉ (⌈2 * zH X₀ n / gridDelta (zH X₀ n)⌉ - 1)

/-- The grid window of index `k`. -/
def gwin (z : ℝ) (k : ℤ) : Set ℝ := Ico (k * gridDelta z) ((k + 2) * gridDelta z)

lemma mem_gridW {n : ℕ} {k : ℤ} (hz : 0 < gridDelta (zH X₀ n)) :
    k ∈ gridW X₀ n ↔ zH X₀ n ≤ k * gridDelta (zH X₀ n) ∧
      k * gridDelta (zH X₀ n) < 2 * zH X₀ n := by
  unfold gridW
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_sub_one_iff, Int.lt_ceil, div_le_iff₀ hz,
    lt_div_iff₀ hz]

variable (hc : Cond θ X₀) (hev : Even X₀)

/-- **The cluster event `E_cl(z_n)`** in the window model. -/
def EclW (n : ℕ) : Set JitterΩ :=
  {ω | ∀ k ∈ gridW X₀ n,
    ((windowElems (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
      (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
      (gwin (zH X₀ n) k)).card : ℝ) ≤ M1cl X₀ (zH X₀ n)}

/-- **The target bound** `T(x) ≤ 3x` up to `u_n/2`. -/
def tB (n : ℕ) : Set JitterΩ := tBound θ X₀ (2 ^ n * (X₀ : ℝ) / 2)

/-- The time of `tB n`. -/
noncomputable def ttB (X₀ : ℕ) (n : ℕ) : ℕ := ⌈2 ^ n * (X₀ : ℝ) / 2⌉₊ + 1

/-- All stages good. -/
def SG : Set JitterΩ := ⋂ m, stageGood θ X₀ m

include hc in
lemma zH_log (n : ℕ) : 2 ≤ Real.log (zH X₀ n) := by
  have hX := hc.hX
  have hX1 := one_lt_of_logX (Nat.cast_nonneg _) hX
  have hz := zH_ge (X₀ := X₀) n
  have hz0 : 0 < zH X₀ n := by linarith
  have : Real.log ((X₀ : ℝ) / 2) ≤ Real.log (zH X₀ n) := Real.log_le_log (by positivity) hz
  rw [Real.log_div (by positivity) (by norm_num)] at this
  linarith [Real.log_two_lt_d9]

include hc in
lemma Xm_pos : 1 < Xm X₀ := by
  unfold Xm
  have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  have h3 := X₀_ge_two_pow hc.hX
  linarith

include hc in
/-- `2z + 1 ≤ X₀⁻^{D+1}`. -/
lemma DpZ_spec {z : ℝ} (hz0 : 0 < z) (hz : 2 ≤ Real.log z) :
    2 * z + 1 ≤ Xm X₀ ^ (DpZ X₀ z + 1) := by
  have hXm := Xm_pos hc
  have hl : 0 < Real.log (Xm X₀) := Real.log_pos hXm
  have hz1 : 1 ≤ z := by
    by_contra h; push_neg at h
    have := Real.log_nonpos hz0.le h.le; linarith
  have hlog3 : Real.log (2 * z + 1) ≤ Real.log z + 1.4 := by
    have : 2 * z + 1 ≤ 3 * z := by linarith
    have h := Real.log_le_log (by linarith) this
    rw [Real.log_mul (by norm_num) hz0.ne'] at h
    have := log3_le
    linarith
  have hD : (Real.log z + 1.4) / Real.log (Xm X₀) ≤ DpZ X₀ z := Nat.le_ceil _
  have key : Real.log (2 * z + 1) ≤ Real.log (Xm X₀ ^ (DpZ X₀ z + 1)) := by
    rw [Real.log_pow]
    rw [div_le_iff₀ hl] at hD
    push_cast
    nlinarith
  exact (Real.log_le_log_iff (by linarith) (by positivity)).mp key

include hc in
lemma zH_gt_one (n : ℕ) : 1 < zH X₀ n := by
  have := zH_ge (X₀ := X₀) n
  have := X₀_ge_two_pow hc.hX
  linarith

/-- **`ClusterUpTo` from the window-model cluster events** (`clusterUpTo_of_windows2`). -/
theorem clusterUpTo_of_eclW {ω : JitterΩ} (hU : ∀ j, ω j ∈ Icc (0 : ℝ) 1)
    (hG : ω ∈ SG (θ := θ) (X₀ := X₀)) {Z w : ℝ} (hZw : Z ≤ w)
    (hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * Z + 1)))
    (hcl : ∀ n, zH X₀ n ≤ Z → ω ∈ EclW hc hev n) :
    ClusterUpTo (realisedSystem (constructedModel θ X₀ ω) (capH X₀) ω) X₀ Z (capM1 X₀ w) := by
  have hG' : ∀ m, ω ∈ stageGood θ X₀ m := by simpa [SG] using hG
  refine clusterUpTo_of_windows2 hc hev hU hG' hTB NpZ (DpZ X₀) DmaxZ ?_ ?_
  · rintro z ⟨n, rfl⟩ _
    have hz2 := zH_log hc n
    have hz1 := zH_gt_one hc n
    unfold zH at hz2 hz1
    refine ⟨?_, DpZ_spec hc (by linarith) hz2, Nat.le_ceil _⟩
    unfold NpZ; push_cast; exact Nat.lt_floor_add_one _
  · rintro z ⟨n, rfl⟩ hzZ k hk1 hk2
    have hδ : 0 < gridDelta (zH X₀ n) := gridDelta_pos (zH_gt_one hc n)
    have hmem : k ∈ gridW X₀ n := (mem_gridW hδ).mpr ⟨hk1, hk2⟩
    have h := hcl n hzZ k hmem
    refine h.trans (M1cl_le hc.hX (zH_ge n) (hzZ.trans hZw))


/-! ### The parameters of Proposition 6.11 at a height -/

/-- `A_top = e^γ log(2z + H(2z)) exp(2.21/Λ + 5H(X₀)/X₀)` (Lemma A.6 (S3)(d)). -/
noncomputable def AtopZ (X₀ : ℕ) (z : ℝ) : ℝ :=
  Real.exp eulerMascheroniConstant * Real.log (2 * z + capH X₀ (2 * z)) *
    Real.exp (2.21 / Real.log X₀ + 5 * capH X₀ X₀ / X₀)

/-- `Ch = e^γ log(2z + H(2z)) exp(2.21/Λ + 10⁻⁹)` (Proposition 6.19). -/
noncomputable def ChZ (X₀ : ℕ) (z : ℝ) : ℝ :=
  Real.exp eulerMascheroniConstant * Real.log (2 * z + capH X₀ (2 * z)) *
    Real.exp (2.21 / Real.log X₀ + 1e-9)

/-- `Eu_rat = ∑_{d ≤ D_max, X₀-smooth} 1/d`. -/
noncomputable def EuZ (X₀ : ℕ) (z : ℝ) : ℝ := tailSum (DmaxZ z) X₀

/-- `s_max = ⌊24 (2z + 1)/7⌋`. -/
noncomputable def smaxZ (z : ℝ) : ℕ := ⌊24 * (2 * z + 1) / 7⌋₊

section Params

variable {hc} in
include hc in
lemma X0_ge_big : (10 : ℝ) ^ 10 ≤ X₀ := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) < X₀ := by have := one_lt_of_logX (Nat.cast_nonneg _) hX; linarith
  have h := Real.pow_div_factorial_le_exp (Real.log X₀) (by linarith) 2
  rw [Real.exp_log hX0] at h
  simp [Nat.factorial] at h
  nlinarith

variable {hc} in
include hc in
lemma capH_X0_small : 5 * capH X₀ X₀ / X₀ ≤ 1e-9 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hH := InitialRange.capH_le_rpow hX0 hX le_rfl
  have hX16 := X₀_ge_two_pow hX
  rw [div_le_iff₀ (by linarith)]
  -- `X₀^{1/8} ≤ X₀ / 10¹⁰`
  have h8 : (X₀ : ℝ) ^ (1 / 8 : ℝ) * (X₀ : ℝ) ^ (7 / 8 : ℝ) = X₀ := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h78 : (10 : ℝ) ^ 10 ≤ (X₀ : ℝ) ^ (7 / 8 : ℝ) := by
    have hl : Real.log ((10 : ℝ) ^ 10) ≤ Real.log ((X₀ : ℝ) ^ (7 / 8 : ℝ)) := by
      rw [Real.log_rpow (by linarith), Real.log_pow]
      have : Real.log 10 ≤ 3 := by
        have he := Real.exp_one_gt_d9
        have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
        rw [Real.log_le_iff_le_exp (by norm_num)]; nlinarith
      push_cast; nlinarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hl
  have hpos : 0 ≤ (X₀ : ℝ) ^ (1 / 8 : ℝ) := by positivity
  nlinarith

end Params

section Numerics

variable {hc}
include hc

/-- `e^{2 log Λ + s(z)} = log z`. -/
lemma exp_ell_eq {z : ℝ} (hz : 1 < z) :
    Real.exp (2 * Real.log (Real.log X₀) + capS X₀ z) = Real.log z := by
  rw [ell_eq, Real.exp_log (Real.log_pos hz)]

/-- `log H(X₀) ≤ 0.001 Λ`. -/
lemma log_capH_X0 : Real.log (capH X₀ X₀) ≤ 0.001 * Real.log X₀ := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨-, -, h3⟩ := capH_conditions hX0 hX (le_refl (X₀ : ℝ))
  have h4 := (AbsorbEmpty.log_estimates hX).1
  nlinarith

/-- `log(X₀⁻) ≥ Λ - e^{-0.98Λ}`. -/
lemma log_Xm_ge : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log (Xm X₀) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hH1 := capH_ge_one hX0 hX (le_refl (X₀ : ℝ))
  have hlH := log_capH_X0 (hc := hc)
  set Λ := Real.log X₀
  set H := capH X₀ X₀
  set t := H / (2 * X₀)
  have hXe : (X₀ : ℝ) = Real.exp Λ := (Real.exp_log hXp).symm
  have hHe : H ≤ Real.exp (0.001 * Λ) := by
    rw [← Real.exp_log (by linarith : 0 < H)]; exact Real.exp_le_exp.mpr hlH
  have ht : t ≤ Real.exp (-0.98 * Λ) / 2 := by
    simp only [t]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : Real.exp (0.001 * Λ) * 2 ≤ Real.exp (-0.98 * Λ) * (2 * X₀) := by
      rw [hXe, show Real.exp (-0.98 * Λ) * (2 * Real.exp Λ) = 2 * Real.exp (0.02 * Λ) by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf]
      have : Real.exp (0.001 * Λ) ≤ Real.exp (0.02 * Λ) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    nlinarith
  have hsmall : Real.exp (-0.98 * Λ) ≤ 1 / 4 := by
    have : Real.exp (-0.98 * Λ) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have h3 := Real.pow_div_factorial_le_exp (2 : ℝ) (by norm_num) 3
    simp [Nat.factorial] at h3
    have : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg]; ring
    have : 1 / Real.exp 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      linarith
    linarith
  have ht0 : 0 ≤ t := by positivity
  have hXm : Xm X₀ = X₀ * (1 - t) := by
    unfold Xm; simp only [t, H]; field_simp
  rw [hXm, Real.log_mul hXp.ne' (by linarith)]
  have := log_one_sub_ge ht0 (by linarith)
  linarith

/-- `1 < τ_j` for the slot thresholds. -/
lemma one_lt_tauSlot (j : ℕ) : 1 < tauSlot (capH X₀) X₀ j := by
  unfold tauSlot
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  have h1 := InitialRange.capH_le_rpow (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  have h2 := four_capH_le (Nat.cast_nonneg (α := ℝ) X₀) hc.hX le_rfl
  have h3 := X₀_ge_two_pow hc.hX
  linarith

end Numerics

section Numerics2

variable {hc}
include hc

variable {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
include hz

lemma z_facts : 1 < z ∧ 10 ^ 8 ≤ Real.log z ∧ Real.log (Real.log X₀) ≤ Real.log (Real.log z) ∧
    18 ≤ Real.log (Real.log z) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  obtain ⟨h1, h2, -⟩ := logs_of_ge hX0 hc.hX hz
  exact ⟨by linarith, h1, h2, BSCert.Capl.log_ge_18 (by linarith)⟩

lemma hs_of : -Real.log (Real.log X₀) ≤ capS X₀ z := by
  obtain ⟨-, -, h, -⟩ := z_facts (hc := hc) hz
  unfold capS; linarith

lemma r0_lo : Real.log z / (3 * Real.log (Real.log z)) + 3 ≤ (r0At z : ℝ) := by
  unfold r0At; push_cast
  have := Nat.le_ceil (Real.log z / (3 * Real.log (Real.log z)))
  linarith

lemma r0_hi : (r0At z : ℝ) ≤ Real.log z / (3 * Real.log (Real.log z)) + 4 := by
  obtain ⟨-, h1, -, h2⟩ := z_facts (hc := hc) hz
  unfold r0At; push_cast
  have := Nat.ceil_lt_add_one (show 0 ≤ Real.log z / (3 * Real.log (Real.log z)) by positivity)
  linarith

lemma DpZ_ge_one : 1 ≤ DpZ X₀ z := by
  obtain ⟨-, h1, -, -⟩ := z_facts (hc := hc) hz
  have hl := Real.log_pos (Xm_pos hc)
  unfold DpZ
  apply Nat.one_le_iff_ne_zero.mpr
  rw [Ne, Nat.ceil_eq_zero, not_le]
  positivity

/-- **`D ≤ 2L/Λ`** (`hDle`). -/
lemma DpZ_le : (DpZ X₀ z : ℝ) ≤ 2 * Real.log z / Real.log X₀ := by
  obtain ⟨-, hL, -, -⟩ := z_facts (hc := hc) hz
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hLΛ : Real.log X₀ ≤ Real.log z := Real.log_le_log (by linarith) hz
  have hXm := log_Xm_ge (hc := hc)
  have he : Real.exp (-0.98 * Real.log X₀) ≤ 1e-6 := by
    have h6 : Real.exp (-0.98 * Real.log X₀) ≤ Real.exp (-14) := Real.exp_le_exp.mpr (by nlinarith)
    have h14 : Real.exp (-14) ≤ 1e-6 := by
      rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos 14)]
      have := AbsorbEmpty.exp_fourteen_ge; linarith
    linarith
  set Λ := Real.log X₀
  set L := Real.log z
  have hlXm : 0.999999 * Λ ≤ Real.log (Xm X₀) := by nlinarith
  have hlXm0 : 0 < Real.log (Xm X₀) := by nlinarith
  set x := (L + 1.4) / Real.log (Xm X₀)
  have hx : x ≤ (L + 1.4) / (0.999999 * Λ) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hlXm
  have hx1 : (L + 1.4) / (0.999999 * Λ) ≤ 1.000002 * (L / Λ) := by
    rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀
      (by positivity)]
    nlinarith
  have hy : 1 ≤ L / Λ := by rw [le_div_iff₀ (by positivity)]; linarith
  set y := L / Λ
  have hD : (DpZ X₀ z : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hgoal : 2 * L / Λ = 2 * y := by simp only [y]; ring
  rw [hgoal]
  -- `⌈x⌉ ≤ 2y` with `x ≤ 1.000002 y`, `y ≥ 1`
  rcases le_or_gt y 1.5 with hy2 | hy2
  · -- then `x < 2`, so `⌈x⌉ ≤ 2 ≤ 2y`
    have hx2 : x ≤ 2 := by nlinarith
    have : DpZ X₀ z ≤ 2 := by unfold DpZ; exact Nat.ceil_le.mpr (by exact_mod_cast hx2)
    have : (DpZ X₀ z : ℝ) ≤ 2 := by exact_mod_cast this
    linarith
  · nlinarith

/-- `2δ₁(z) = 4 L^{-6}`. -/
lemma two_gridDelta : 2 * gridDelta z = 4 * Real.exp (2 * Real.log (Real.log X₀) + capS X₀ z) ^
    (-6 : ℝ) := by
  obtain ⟨hz1, hL, -, -⟩ := z_facts (hc := hc) hz
  rw [exp_ell_eq (hc := hc) hz1]
  unfold gridDelta
  rw [Real.rpow_neg (by linarith)]
  have : Real.log z ^ (6 : ℝ) = Real.log z ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [this]; ring

end Numerics2

section Numerics3

variable {hc}
include hc

variable {z : ℝ} (hz : (X₀ : ℝ) ≤ z)
include hz

lemma capH_two_z_small : capH X₀ (2 * z) ≤ 0.0001 * (2 * z) := by
  obtain ⟨hz1, hL, -, -⟩ := z_facts (hc := hc) hz
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have h2 : (X₀ : ℝ) ≤ 2 * z := by linarith
  have hH := InitialRange.capH_le_rpow hX0 hc.hX h2
  have hz2 := four_capH_le hX0 hc.hX h2
  -- `(2z)^{1/8} ≤ 10⁻⁴ · 2z` since `2z ≥ 10^{8/7·4}`
  have hsq : (2 * z) ^ (1 / 8 : ℝ) * (2 * z) ^ (7 / 8 : ℝ) = 2 * z := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h78 : (10 : ℝ) ^ 4 ≤ (2 * z) ^ (7 / 8 : ℝ) := by
    have hl : Real.log ((10 : ℝ) ^ 4) ≤ Real.log ((2 * z) ^ (7 / 8 : ℝ)) := by
      rw [Real.log_rpow (by linarith), Real.log_pow]
      have h10 : Real.log 10 ≤ 3 := by
        have he := Real.exp_one_gt_d9
        have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
        rw [Real.log_le_iff_le_exp (by norm_num)]; nlinarith
      have : Real.log z ≤ Real.log (2 * z) := Real.log_le_log (by linarith) (by linarith)
      push_cast; nlinarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hl
  have hpos : 0 ≤ (2 * z) ^ (1 / 8 : ℝ) := by positivity
  nlinarith

lemma log_top_le' : Real.log (2 * z + capH X₀ (2 * z)) ≤ Real.log z + 0.7 := by
  obtain ⟨hz1, -, -, -⟩ := z_facts (hc := hc) hz
  exact RankFull.log_top_le (by linarith) (capH_nonneg _ _) (capH_two_z_small (hc := hc) hz)

lemma log_top_nonneg : 0 ≤ Real.log (2 * z + capH X₀ (2 * z)) := by
  obtain ⟨hz1, -, -, -⟩ := z_facts (hc := hc) hz
  exact Real.log_nonneg (by linarith [capH_nonneg X₀ (2 * z)])

/-- `A_top ≤ Ch` (`hACh`). -/
lemma Atop_le_Ch : AtopZ X₀ z ≤ ChZ X₀ z :=
  RankFull.A_top_le_Ch (log_top_nonneg (hc := hc) hz) (capH_X0_small (hc := hc))

/-- `A_top ≤ A_R e^{2.2/Λ}` (`hAtop'`). -/
lemma Atop_le_AR : AtopZ X₀ z ≤ 1.8 * (Real.log z + 4) * Real.exp (2.2 / Real.log X₀) := by
  obtain ⟨-, hL, -, -⟩ := z_facts (hc := hc) hz
  exact RankFull.A_top_le hc.hX (by linarith) (log_top_nonneg (hc := hc) hz)
    (log_top_le' (hc := hc) hz) (by linarith [capH_X0_small (hc := hc)])

/-- `Ch ≤ 2L` (`hCh`). -/
lemma Ch_le : ChZ X₀ z ≤ 2 * Real.log z := by
  obtain ⟨-, hL, -, -⟩ := z_facts (hc := hc) hz
  have hX := hc.hX
  have hg := RankFull.exp_eulerMascheroni_lt
  have ht := log_top_le' (hc := hc) hz
  have ht0 := log_top_nonneg (hc := hc) hz
  have hsmall : 2.21 / Real.log X₀ + 1e-9 ≤ 0.001 := by
    have : 2.21 / Real.log X₀ ≤ 2.21 / 10 ^ 8 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hX
    norm_num at this ⊢; linarith
  have hexp : Real.exp (2.21 / Real.log X₀ + 1e-9) ≤ 1.0011 := by
    have h1 := Real.exp_le_exp.mpr hsmall
    have hb := Real.exp_bound (x := (0.001 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
      (by norm_num)
    have := (abs_le.mp hb).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  unfold ChZ
  have hg0 := Real.exp_pos eulerMascheroniConstant
  calc Real.exp eulerMascheroniConstant * Real.log (2 * z + capH X₀ (2 * z)) *
        Real.exp (2.21 / Real.log X₀ + 1e-9) ≤ 1.79 * (Real.log z + 0.7) * 1.0011 := by gcongr
    _ ≤ 2 * Real.log z := by nlinarith

lemma tailSum_ge_one : 1 ≤ EuZ X₀ z := by
  unfold EuZ tailSum
  have hX1 : 1 ≤ DmaxZ z := by
    obtain ⟨hz1, -, -, -⟩ := z_facts (hc := hc) hz
    unfold DmaxZ; exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hmem : 1 ∈ Nat.smoothNumbersUpTo (DmaxZ z) X₀ := by
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨hX1, ?_⟩
    rw [Nat.mem_smoothNumbers]; simp
  have := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ))⁻¹)
    (fun d _ => by positivity) hmem
  simpa using this

/-- `1 + r₀ log(A_top/Eu) ≤ L` (`hrlam`), for `1 ≤ Eu ≤ A_top`. -/
lemma rlam_le (hEu : EuZ X₀ z ≤ AtopZ X₀ z) :
    1 + (r0At z : ℝ) * Real.log (AtopZ X₀ z / EuZ X₀ z) ≤ Real.log z := by
  obtain ⟨hz1, hL, -, hℓ⟩ := z_facts (hc := hc) hz
  have hE1 := tailSum_ge_one (hc := hc) hz
  have hA := (Atop_le_Ch (hc := hc) hz).trans (Ch_le (hc := hc) hz)
  have hr := r0_hi (hc := hc) hz
  set L := Real.log z
  set ℓ := Real.log L
  have hlam : Real.log (AtopZ X₀ z / EuZ X₀ z) ≤ ℓ + 0.7 := by
    have h1 : AtopZ X₀ z / EuZ X₀ z ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h0 : 0 < AtopZ X₀ z / EuZ X₀ z := div_pos (by linarith) (by linarith)
    have := Real.log_le_log h0 h1
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith [Real.log_two_lt_d9]
  have hlam0 : 0 ≤ Real.log (AtopZ X₀ z / EuZ X₀ z) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hℓL : ℓ ≤ L / 1000 := by
    have := sq_log_le (show (1 : ℝ) ≤ L by linarith)
    by_contra hc'; push_neg at hc'
    have : L ^ 2 < (1000 * ℓ) ^ 2 := by nlinarith
    nlinarith
  have hr0 : (0 : ℝ) ≤ r0At z := Nat.cast_nonneg _
  calc 1 + (r0At z : ℝ) * Real.log (AtopZ X₀ z / EuZ X₀ z)
      ≤ 1 + (L / (3 * ℓ) + 4) * (ℓ + 0.7) := by
        gcongr
    _ = 1 + L / 3 + 0.7 * L / (3 * ℓ) + 4 * ℓ + 2.8 := by
        have hℓ0 : ℓ ≠ 0 := by linarith
        field_simp; ring
    _ ≤ L := by
        have : 0.7 * L / (3 * ℓ) ≤ 0.7 * L / 54 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num); linarith
        nlinarith

/-- `#W ≤ 2z/(4L^{-6}) + 1` (`hW`). -/
lemma gridW_card {n : ℕ} (hzn : zH X₀ n = z) :
    ((gridW X₀ n).card : ℝ) ≤ 2 * z / (4 * Real.log z ^ (-6 : ℝ)) + 1 := by
  obtain ⟨hz1, hL, -, -⟩ := z_facts (hc := hc) hz
  have hδ : 0 < gridDelta z := gridDelta_pos hz1
  unfold gridW
  rw [hzn, Int.card_Icc]
  set c1 := ⌈z / gridDelta z⌉
  set c2 := ⌈2 * z / gridDelta z⌉
  have h1 : z / gridDelta z ≤ c1 := Int.le_ceil _
  have h2 : (c2 : ℝ) < 2 * z / gridDelta z + 1 := Int.ceil_lt_add_one _
  have e : 2 * z / (4 * Real.log z ^ (-6 : ℝ)) = z / gridDelta z := by
    unfold gridDelta
    rw [Real.rpow_neg (by linarith)]
    have : Real.log z ^ (6 : ℝ) = Real.log z ^ (6 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
    rw [this]; field_simp; ring
  rw [e]
  rcases le_or_gt c1 (c2 - 1 + 1) with h | h
  · have : (((c2 - 1 + 1 - c1).toNat : ℕ) : ℝ) = ((c2 - 1 + 1 - c1 : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [this]; push_cast
    have : 2 * z / gridDelta z = 2 * (z / gridDelta z) := by ring
    linarith
  · rw [Int.toNat_of_nonpos (by omega)]; simp; positivity

/-- `θ e^{(3H(X₀)+2)/X₀} b ≤ 1.01` (`hθab`), `θ = 1 + 1/Λ`, `b = e^{2.2/Λ}`. -/
lemma theta_ab : (1 + 1 / Real.log X₀) * Real.exp ((3 * capH X₀ X₀ + 2) / X₀) *
    Real.exp (2.2 / Real.log X₀) ≤ 1.01 := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hs := capH_X0_small (hc := hc)
  have hX16 := X0_ge_big (hc := hc)
  have h1 : (3 * capH X₀ X₀ + 2) / X₀ ≤ 1e-9 := by
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (by linarith)] at hs
    nlinarith
  have h2 : 2.2 / Real.log X₀ ≤ 1e-7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 1 / Real.log X₀ ≤ 1e-8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [mul_assoc, ← Real.exp_add]
  have he : Real.exp ((3 * capH X₀ X₀ + 2) / X₀ + 2.2 / Real.log X₀) ≤ 1.001 := by
    have : (3 * capH X₀ X₀ + 2) / X₀ + 2.2 / Real.log X₀ ≤ 0.0001 := by linarith
    have h1' := Real.exp_le_exp.mpr this
    have hb := Real.exp_bound (x := (0.0001 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
      (by norm_num)
    have := (abs_le.mp hb).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hpos := Real.exp_pos ((3 * capH X₀ X₀ + 2) / X₀ + 2.2 / Real.log X₀)
  nlinarith

/-- `1 + r₀/X₀ ≤ 2L` (`hu`). -/
lemma hu_le : 1 + (r0At z : ℝ) / X₀ ≤ 2 * Real.log z := by
  obtain ⟨hz1, hL, -, hℓ⟩ := z_facts (hc := hc) hz
  have hr := r0_hi (hc := hc) hz
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have h1 : (r0At z : ℝ) / X₀ ≤ r0At z := div_le_self (Nat.cast_nonneg _) hX1.le
  have h2 : Real.log z / (3 * Real.log (Real.log z)) ≤ Real.log z / 54 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  linarith

/-- **`∏_{i<r} (1 - 1/τ_i)^{-1} ≤ 2.1 L^{1.02}`** (`hBτ`), from Lemma A.3. -/
lemma prod_tau_le (hH : SlotHyp (capH X₀) X₀) {r : ℕ} (hr : r < r0At z) :
    ∏ i : Fin r, (1 - (tauSlot (capH X₀) X₀ i)⁻¹)⁻¹ ≤ 2.1 * Real.log z ^ (1.02 : ℝ) := by
  obtain ⟨hz1, hL, -, hℓ⟩ := z_facts (hc := hc) hz
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hτ : ∀ j : ℕ, 1 < tauSlot (capH X₀) X₀ j := one_lt_tauSlot (hc := hc)
  -- each factor is at most `exp(1/(τ - 1))`
  have hfac : ∀ j : ℕ, (1 - (tauSlot (capH X₀) X₀ j)⁻¹)⁻¹ ≤
      Real.exp (1 / (tauSlot (capH X₀) X₀ j - 1)) := by
    intro j
    have h1 := hτ j
    have e : (1 - (tauSlot (capH X₀) X₀ j)⁻¹)⁻¹ = 1 + 1 / (tauSlot (capH X₀) X₀ j - 1) := by
      have h0 : tauSlot (capH X₀) X₀ j - 1 ≠ 0 := by linarith
      have h0' : tauSlot (capH X₀) X₀ j ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    have := Real.add_one_le_exp (1 / (tauSlot (capH X₀) X₀ j - 1))
    linarith
  rw [Fin.prod_univ_eq_prod_range (fun i => (1 - (tauSlot (capH X₀) X₀ i)⁻¹)⁻¹) r]
  have hprod : ∏ j ∈ Finset.range r, (1 - (tauSlot (capH X₀) X₀ j)⁻¹)⁻¹ ≤
      Real.exp (∑ j ∈ Finset.range r, 1 / (tauSlot (capH X₀) X₀ j - 1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => by
      have := hτ j
      have : 0 < 1 - (tauSlot (capH X₀) X₀ j)⁻¹ := by
        rw [sub_pos]; exact inv_lt_one_of_one_lt₀ this
      positivity) fun j _ => hfac j
  have hsum := hH.sum_inv_tau_le r
  have hb : 1 + (r : ℝ) / X₀ ≤ 2 * Real.log z := by
    have := hu_le (hc := hc) hz
    have : (r : ℝ) ≤ r0At z := by exact_mod_cast hr.le
    have : (r : ℝ) / X₀ ≤ (r0At z : ℝ) / X₀ := div_le_div_of_nonneg_right this hX0
    linarith
  have hb0 : 0 < 1 + (r : ℝ) / X₀ := by positivity
  have h1 : (3 * capH X₀ X₀ + 2) / X₀ ≤ 1e-9 := by
    have hs := capH_X0_small (hc := hc)
    have hX16 := X0_ge_big (hc := hc)
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (by linarith)] at hs
    nlinarith
  calc ∏ j ∈ Finset.range r, (1 - (tauSlot (capH X₀) X₀ j)⁻¹)⁻¹
      ≤ Real.exp ((3 * capH X₀ X₀ + 2) / X₀ + 1.02 * Real.log (1 + r / X₀)) :=
        hprod.trans (Real.exp_le_exp.mpr hsum)
    _ = Real.exp ((3 * capH X₀ X₀ + 2) / X₀) * (1 + r / X₀) ^ (1.02 : ℝ) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hb0]; ring_nf
    _ ≤ 1.001 * (2 * Real.log z) ^ (1.02 : ℝ) := by
        gcongr
        · have : Real.exp ((3 * capH X₀ X₀ + 2) / X₀) ≤ Real.exp 1e-9 := Real.exp_le_exp.mpr h1
          have hb := Real.exp_bound (x := (1e-9 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
            (by norm_num)
          have := (abs_le.mp hb).2
          norm_num [Finset.sum_range_succ, Nat.factorial] at this
          linarith
    _ = 1.001 * 2 ^ (1.02 : ℝ) * Real.log z ^ (1.02 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
    _ ≤ 2.1 * Real.log z ^ (1.02 : ℝ) := by
        have h2 : (2 : ℝ) ^ (1.02 : ℝ) ≤ 2.06 := by
          rw [show (1.02 : ℝ) = 1 + 0.02 by norm_num, Real.rpow_add (by norm_num),
            Real.rpow_one]
          have : (2 : ℝ) ^ (0.02 : ℝ) ≤ 1.03 := by
            rw [Real.rpow_def_of_pos (by norm_num)]
            have hl := Real.log_two_lt_d9
            have : Real.log 2 * 0.02 ≤ 0.02 := by nlinarith
            have h3 := Real.exp_le_exp.mpr this
            have hb := Real.exp_bound (x := (0.02 : ℝ)) (by norm_num [abs_of_pos]) (n := 2)
              (by norm_num)
            have := (abs_le.mp hb).2
            norm_num [Finset.sum_range_succ, Nat.factorial] at this
            linarith
          nlinarith
        have hp : 0 ≤ Real.log z ^ (1.02 : ℝ) := by positivity
        nlinarith

end Numerics3

/-! ### Proposition 6.11 for the cluster events, from the window model -/

section Prop611

/-- For `T ⊆ ...`: the restriction to the measurable hull of `S ∩ B` intersected with a
measurable `B` is the restriction to `S ∩ B`. -/
lemma restrict_hull_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    μ.restrict (toMeasurable μ (S ∩ B) ∩ B) = μ.restrict (S ∩ B) := by
  rw [Set.inter_comm, ← Measure.restrict_restrict hB,
    Measure.restrict_toMeasurable (measure_ne_top _ _), Measure.restrict_restrict hB]
  congr 1
  ext x; simp only [mem_inter_iff]; tauto

lemma sqrt_exp (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- **Proposition 6.11 at the dyadic height `z_n ≥ X₀`** for the cluster event `E_cl(z_n)`, on a
good event `G`, from the window model (`prop_6_11_window`) with the skeleton bound of
Lemma A.5 + Theorem A.10 (`skeletonBound_construction`). The residual inputs are the named
hypotheses of Appendix A: (S3)(d) (`S3dHyp`), the multi-run skeleton bound
(`MultiRunSkeletonBound`), the Cover Bound (`CoverSkeletonBound`, Lemmas 6.17–6.19) and the
standing hypotheses on `H` (`SlotHyp`). -/
theorem eclW_fail (hH : SlotHyp (capH X₀) X₀) {n : ℕ} (hn : 1 ≤ n) (G : Set JitterΩ)
    (hS3 : S3dHyp hc hev (NpZ (zH X₀ n)) (DmaxZ (zH X₀ n)) (smaxZ (zH X₀ n))
      (AtopZ X₀ (zH X₀ n)))
    (hmulti : ∀ k ∈ gridW X₀ n, MultiRunSkeletonBound jitterMeasure
      (G ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) (r0At (zH X₀ n)) (1 + 1 / Real.log X₀)
      (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n)) (EuZ X₀ (zH X₀ n))
      (fun j => tauSlot (capH X₀) X₀ j)
      (fun E l ω => skelCount (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
        (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
        (gwin (zH X₀ n) k)) E l))
    (hcov : ∀ j, ∀ k ∈ gridW X₀ n, ∀ r < r0At (zH X₀ n), ∀ C ∈ CSet r j, ∀ lab ex s4,
      ExOK C ex → ∃ l : List ℕ, l.sum = C.card ∧ l.count 0 ≤ r - C.card ∧
        CoverSkeletonBound jitterMeasure (G ∩ goodLt θ X₀ (smaxZ (zH X₀ n))) r
          (1 + 1 / Real.log X₀) (2 * gridDelta (zH X₀ n)) (AtopZ X₀ (zH X₀ n))
          (EuZ X₀ (zH X₀ n)) (zH X₀ n) (fun i => tauSlot (capH X₀) X₀ i) (exExcess ex)
          (r - C.card) l (fun ω => cfgSkelCount (DpZ X₀ (zH X₀ n)) (r0At (zH X₀ n)) 0 0
            (tailOf (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k))
            (windowVecs (decOf (N := NpZ (zH X₀ n)) (constructionLaw2 hc hev) ω)
              (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ (zH X₀ n)) (DmaxZ (zH X₀ n))
              (gwin (zH X₀ n) k)) r C lab ex s4)) :
    jitterMeasure ((EclW hc hev n)ᶜ ∩ G) ≤
      ENNReal.ofReal (Real.log (zH X₀ n) ^ (-2 : ℝ)) := by
  classical
  set z := zH X₀ n with hzdef
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hz : (X₀ : ℝ) ≤ z := by
    simp only [hzdef, zH]
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith
  obtain ⟨hz1, hL, hll, hℓ⟩ := z_facts (hc := hc) hz
  have hz2 : 2 ≤ Real.log z := by linarith
  have hE := exp_ell_eq (hc := hc) hz1
  have hzz : Real.exp (Real.exp (2 * Real.log (Real.log X₀) + capS X₀ z)) = z := by
    rw [hE, Real.exp_log (by linarith)]
  set smax := smaxZ z
  set B := goodLt θ X₀ smax
  have hBm : MeasurableSet B := jitterFiltration.le smax _ (good_meas hc smax)
  set GoodM := toMeasurable jitterMeasure (G ∩ B) ∩ B
  have hGM : MeasurableSet GoodM := (measurableSet_toMeasurable _ _).inter hBm
  have hres : jitterMeasure.restrict GoodM = jitterMeasure.restrict (G ∩ B) :=
    restrict_hull_inter jitterMeasure G hBm
  -- `Eu ≤ A_top`, from (S3)(d) at `u = 0`
  have hEuA : EuZ X₀ z ≤ AtopZ X₀ z := by
    have h := hS3 (fun _ => 0) 0 (Nat.zero_le _) (by simp [goodLt])
    simpa [EuZ] using h
  have hE1 := tailSum_ge_one (hc := hc) hz
  have hA0 : 0 ≤ AtopZ X₀ z := by linarith
  -- the threshold
  have hM : M1cl X₀ z = (r0At z : ℝ) + Covers.phi
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z)))
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z) / 2)) (r0At z) + 1 := by
    unfold M1cl cAt logcAt; rw [sqrt_exp]
  -- apply `prop_6_11_window`
  have hmain := prop_6_11_window jitterMeasure hGM (gridW X₀ n)
    (fun ω => decOf (N := NpZ z) (constructionLaw2 hc hev) ω) (qOf (constructionLaw2 hc hev))
    (DmaxZ z) (gwin z) (fun k => k * gridDelta z) (δ := 2 * gridDelta z)
    (fun k => gridWin_sub z k) (gridDelta_two_lt hz2) hc.hX sHroot_mem gstar_sHroot
    (hs_of (hc := hc) hz) (r₀ := r0At z) (D := DpZ X₀ z) (DpZ_ge_one (hc := hc) hz)
    (by rw [hE]; exact r0_lo (hc := hc) hz)
    (by rw [hE, ell_eq]; exact r0_hi (hc := hc) hz)
    (by rw [hE]; exact DpZ_le (hc := hc) hz) (Xm := Xm X₀) (by linarith [Xm_pos hc])
    (log_Xm_ge (hc := hc)) (by
      have h1 := Xm_pos hc
      unfold Xm at h1 ⊢
      exact Real.log_le_log (by linarith) (by linarith [capH_nonneg X₀ X₀]))
    (tauL X₀) (fun i => le_max_left _ _) (fun i => le_max_right _ _) (hq1_dec hc hev)
    (fun k hk => by
      rw [hzz]
      have hδ : 0 < gridDelta z := gridDelta_pos hz1
      exact gridWin_le hz2 ((mem_gridW hδ).mp hk).2) (hτq_dec hc hev)
    (fun r i => tauSlot (capH X₀) X₀ i) (fun r i => one_lt_tauSlot (hc := hc) i)
    (lam := Real.log (AtopZ X₀ z / EuZ X₀ z))
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (by rw [hE]; exact rlam_le (hc := hc) hz hEuA) (Ch := ChZ X₀ z)
    (by rw [hE]; exact Ch_le (hc := hc) hz) (B := 2.1 * Real.log z ^ (1.02 : ℝ))
    (fun r hr => prod_tau_le (hc := hc) hz hH hr) (by rw [hE]) (by linarith) hEuA
    (Atop_le_Ch (hc := hc) hz) le_rfl
    (by rw [hE, Real.exp_log (by linarith)]; exact gridW_card (hc := hc) hz rfl)
    (θ := 1 + 1 / Real.log X₀) (A := AtopZ X₀ z) (Eu' := EuZ X₀ z)
    (A_R := 1.8 * (Real.log z + 4)) (b := Real.exp (2.2 / Real.log X₀)) hH (by positivity)
    (Real.exp_pos _) (theta_ab (hc := hc) hz) (by positivity) (by rw [hE])
    (by rw [hE]; exact hu_le (hc := hc) hz) (by linarith) hEuA (Atop_le_AR (hc := hc) hz)
    (fun k E l => meas_skelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k E l)
    (fun k _ => meas_rankFullCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k)
    (fun j k' k _ => meas_configCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) j k' k)
    (fun k r C lab ex s4 =>
      meas_cfgSkelCount_dec hc hev (fun k => measurableSet_Ico) (r0At z) k r C lab ex s4)
    (fun k hk => by
      rw [← two_gridDelta (hc := hc) hz]
      have h := skeletonBound_construction hc hev hGM smax Set.inter_subset_right
        (r₀ := r0At z) (by
          have := r0_lo (hc := hc) hz
          have h0 : 0 ≤ Real.log z / (3 * Real.log (Real.log z)) := by positivity
          exact_mod_cast (show (1 : ℝ) ≤ r0At z by linarith))
        (Jw := gwin z k) measurableSet_Ico (gridWin_sub z k)
        (by have := gridDelta_pos hz1; linarith) (V := 2 * z + 1)
        (gridWin_le hz2 ((mem_gridW (gridDelta_pos hz1)).mp hk).2) le_rfl (DpZ X₀ z) (DmaxZ z)
        hA0 hEuA hS3 (by
          have := hmulti k hk
          unfold MultiRunSkeletonBound at this ⊢
          intro E hE' l hl hl'
          rw [hres]; exact this E hE' l hl hl')
      exact h)
    (fun j k hk r hr C hC lab ex s4 hex => by
      obtain ⟨l, h1, h2, h3⟩ := hcov j k hk r hr C hC lab ex s4 hex
      refine ⟨l, h1, h2, ?_⟩
      rw [← two_gridDelta (hc := hc) hz, hzz]
      unfold CoverSkeletonBound at h3 ⊢
      rw [hres]; exact h3)
  -- conclude
  have hcompl : (EclW hc hev n)ᶜ = {ω | ∃ k ∈ gridW X₀ n, (r0At z : ℝ) + Covers.phi
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z)))
      (Real.exp (BSCert.Capl.logc sHroot (Real.log X₀) (capS X₀ z) / 2)) (r0At z) + 1 <
        ((windowElems (decOf (N := NpZ z) (constructionLaw2 hc hev) ω)
          (qOf (constructionLaw2 hc hev) ω) X₀ (DpZ X₀ z) (DmaxZ z) (gwin z k)).card : ℝ)} := by
    ext ω
    simp only [EclW, mem_compl_iff, mem_setOf_eq, not_forall, not_le, exists_prop]
    rw [← hM]
  have hnull : jitterMeasure Bᶜ = 0 := good_compl_null hc smax
  calc jitterMeasure ((EclW hc hev n)ᶜ ∩ G)
      ≤ jitterMeasure ((EclW hc hev n)ᶜ ∩ (G ∩ B)) + jitterMeasure Bᶜ := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        intro ω ⟨h1, h2⟩
        by_cases hb : ω ∈ B
        · left; exact ⟨h1, h2, hb⟩
        · right; exact hb
    _ = jitterMeasure ((EclW hc hev n)ᶜ ∩ (G ∩ B)) := by rw [hnull, add_zero]
    _ ≤ jitterMeasure ((EclW hc hev n)ᶜ ∩ GoodM) :=
        measure_mono (Set.inter_subset_inter_right _ fun ω hω =>
          ⟨subset_toMeasurable _ _ hω, hω.2⟩)
    _ ≤ _ := by
        rw [hcompl]
        refine hmain.trans (le_of_eq ?_)
        rw [hE]

end Prop611


end Queue6

end
