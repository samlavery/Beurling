module

public import RequestProject.Beurling.Queue6.S4Inputs
public import RequestProject.Beurling.Model.Wire2
public import RequestProject.Beurling.Noise.RML10Rest

/-!
# The Queue6 inputs of `KR.RML10.WinGlob` and of Step 4 (`RML6.hS4_of`)

`WinGlob` (`Noise/RML10G1Win.lean`), at the Model's `Z = Zc b`, `εW = epsH`, `θW = epsH/10`,
for a range-(B) start `y ≤ b + H(b)`:

* `winGlob_htnp` : the field `htnp` (`BModel.tnpR`, i.e. `tnpHyp_R`, on `NiceEv`, from (HBS) on
  `[1, Zc b]`); it reads no event beyond `SG` and (HBS);
* `winGlob_θ3` : `3 θW ≤ 10⁻³`;
* `winGlob_Z` : the horizons `hZ4 : 4y/X₀⁻ ≤ Zc b`, `hZ36 : 36 y ≤ (Zc b)²`.

Step 4 (`RML6.hS4_of`, Lemma 5.22's `ν`, `δ`), with `ν = nuQ X₀`, `δ = dQ X₀` on the dyadic
scales `V_s = {u_m : m ∈ M}` (deterministic: no event is read):

* `nuQ_nonneg`, `dQ_nonneg` : the fields `hν`, `hδ`;
* `fE_le_nuQ` : the recursion weight `fE X₀ m* z ≤ 2ν(u₁) + δ(u₁)` (`u₁` the block of `z`,
  `0 ≤ m* ≤ 3.1 log z + 4.2`), the input of the grouping `hS`;
* `sum_scales_le` : `27 ∑_{v ∈ V_s} log(3v) ν(v) + 4.3 ∑_{v ∈ V_s} log(3v) δ(v) ≤ 5405 Λ⁻⁴`
  (`sum_nuQ_le`, `sum_dQ_le`), the `ν, δ` part of `hES`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀)
include hc

/-- **The field `htnp` of `WinGlob`** for `P(ω)` on `NiceEv`, at `Z = Zc b`. -/
theorem winGlob_htnp (hev : Even X₀) {ω : JitterΩ} {b : ℝ}
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hN : ω ∈ NiceEv θ X₀) (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) :
    KR.TNP.Hyp (PR θ X₀ ω) (Hc X₀) (BModel.twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10) :=
  tnpR hc hev hbs hN.2.1 hX1

omit hc in
/-- **The field `hθ3` of `WinGlob`** at `θW = epsH/10`. -/
lemma winGlob_θ3 : 3 * (epsH / 10) ≤ 1 / 1000 := by unfold epsH; norm_num

/-- **The fields `hZ4`, `hZ36` of `WinGlob`** at `Z = Zc b`, for `y ≤ b + H(b)`, `X₀ ≤ b`. -/
theorem winGlob_Z {b y : ℝ} (hb : (X₀ : ℝ) ≤ b) (hyb : y ≤ b + Hc X₀ b) :
    4 * y / Xm X₀ ≤ Zc X₀ b ∧ 36 * y ≤ Zc X₀ b ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hXb : (10 : ℝ) ^ 8 ≤ X₀ := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log hX0p]; exact Real.exp_le_exp.mpr hc.hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hc.hX le_rfl
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by unfold Xm; linarith
  have hXm0 : 0 < Xm X₀ := by linarith
  have hHb : Hc X₀ b ≤ b / 10 ^ 7 := by have := Hc_le hc b; rwa [max_eq_left hb] at this
  have hH0 := Hc_nonneg (X₀ := X₀) b
  have hy : y ≤ 1.0000001 * b := by linarith
  unfold Zc
  split_ifs with hbig
  · constructor
    · rw [div_le_iff₀ hXm0]; nlinarith
    · nlinarith
  · push_neg at hbig
    constructor
    · rw [div_le_iff₀ hXm0]; nlinarith
    · nlinarith

/-- **The field `hν` of `hS4_of`**: `ν(v) ≥ 0` for `v ≥ X₀`. -/
lemma nuQ_nonneg {v : ℝ} (hv : (X₀ : ℝ) ≤ v) : 0 ≤ nuQ X₀ v := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hs : ∀ u : ℝ, (X₀ : ℝ) ≤ u → 0 ≤ s2E3 X₀ u := fun u hu => by
    unfold s2E3
    have : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    positivity
  unfold nuQ
  have h1 := hs v hv
  have h2 := hs (2 * v) (by linarith)
  have : 0 ≤ 105 / Real.log v ^ 6 := by positivity
  positivity

omit hc in
/-- **The field `hδ` of `hS4_of`**: `δ(v) ≥ 0` for `v ≥ 1`. -/
lemma dQ_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ dQ X₀ v := by
  unfold dQ
  have : 0 ≤ Real.log (4 * v) := Real.log_nonneg (by linarith)
  have := capH_nonneg (X₀ : ℝ) v
  positivity

/-- **The recursion weight is `2ν(u₁) + δ(u₁)`**: `fE X₀ m* z ≤ 2 ν(u₁) + δ(u₁)` for `X₀ ≤ z`,
`0 ≤ m* ≤ 3.1 log z + 4.2`, `u₁ = u_{m₁(z)}`. -/
theorem fE_le_nuQ {z mst : ℝ} (hz : (X₀ : ℝ) ≤ z) (hm0 : 0 ≤ mst)
    (hm : mst ≤ 3.1 * Real.log z + 4.2) :
    BModel.RML10.fE X₀ mst z ≤ 2 * nuQ X₀ (uS X₀ (m1z X₀ z)) + dQ X₀ (uS X₀ (m1z X₀ z)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX0p : (0 : ℝ) < X₀ := by linarith [X₀_ge_two_pow hc.hX]
  set m1 := m1z X₀ z with hset16
  set u1 := uS X₀ m1 with hset17
  obtain ⟨hu1X, hl1, hH1, -⟩ := uS_facts hc m1
  obtain ⟨hm1a, hm1b⟩ := mB_spec hX0p (le_max_right (z - Hc X₀ z) (X₀ : ℝ))
  have hH0 := Hc_nonneg (X₀ := X₀) z
  have hu1z : u1 ≤ z := hm1a.trans (max_le (by linarith) hz)
  have hz4 : z ≤ 4 * u1 := by
    have h2 : max (z - Hc X₀ z) (X₀ : ℝ) < 2 * u1 := by
      have := hm1b; rw [uS_succ] at this; exact this
    have hHz : Hc X₀ z ≤ z / 10 ^ 7 := by have := Hc_le hc z; rwa [max_eq_left hz] at this
    have := le_max_left (z - Hc X₀ z) (X₀ : ℝ)
    linarith
  have hHH : capH X₀ u1 ≤ Hc X₀ z := by
    rw [Hc_eq hz]
    exact capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hu1X) (mem_Ici.mpr hz) hu1z
  have hH1p : 0 < capH X₀ u1 := by linarith
  have h2u : uS X₀ (m1 + 1) = 2 * u1 := uS_succ m1
  have hlz : Real.log z ≤ Real.log (4 * u1) := Real.log_le_log (by linarith) hz4
  have hl4 : 2 ≤ Real.log (4 * u1) := by
    have h1 := Real.log_le_log (by linarith) (show u1 ≤ 4 * u1 by linarith)
    have h2 : Real.log u1 = Real.log (uS X₀ m1) := rfl
    linarith
  have hd : (6.6 + 4.2 * mst) / Hc X₀ z ≤ dQ X₀ u1 := by
    unfold dQ
    have h1 : 6.6 + 4.2 * mst ≤ 30 * Real.log (4 * u1) := by nlinarith
    calc (6.6 + 4.2 * mst) / Hc X₀ z ≤ (6.6 + 4.2 * mst) / capH X₀ u1 :=
          div_le_div_of_nonneg_left (by linarith) hH1p hHH
      _ ≤ 30 * Real.log (4 * u1) / capH X₀ u1 := div_le_div_of_nonneg_right h1 hH1p.le
  unfold BModel.RML10.fE nuQ
  rw [← hset16, ← hset17, h2u]
  have h6 : 210 / Real.log u1 ^ 6 = 2 * (105 / Real.log u1 ^ 6) := by ring
  linarith

/-- **The `ν, δ` part of `hES`** on the dyadic scales `V_s = M.image u`:
`27 ∑ log(3v) ν(v) + 4.3 ∑ log(3v) δ(v) ≤ 5405/Λ⁴`. -/
theorem sum_scales_le (M : Finset ℕ) :
    27 * ∑ v ∈ M.image (uS X₀), Real.log (3 * v) * nuQ X₀ v +
      4.3 * ∑ v ∈ M.image (uS X₀), Real.log (3 * v) * dQ X₀ v ≤ 5405 / Real.log X₀ ^ 4 := by
  have hX0p : (0 : ℝ) < X₀ := by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith
  have hinj : Set.InjOn (uS X₀) (M : Set ℕ) := fun m _ m' _ h => by
    unfold uS at h
    have h2 : (2 : ℝ) ^ m = 2 ^ m' := by
      have := mul_right_cancel₀ hX0p.ne' h; exact this
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2)
  rw [Finset.sum_image hinj, Finset.sum_image hinj]
  have h1 := sum_nuQ_le hc M
  have h2 := sum_dQ_le hc M
  have hΛ : 0 < Real.log X₀ ^ 4 := by have := hc.hX; positivity
  have e : 5405 / Real.log X₀ ^ 4 = 27 * (200 / Real.log X₀ ^ 4) +
      4.3 * (1 / Real.log X₀ ^ 4) + 0.7 / Real.log X₀ ^ 4 := by ring
  have : 0 ≤ 0.7 / Real.log X₀ ^ 4 := by positivity
  linarith

end Queue6

end
