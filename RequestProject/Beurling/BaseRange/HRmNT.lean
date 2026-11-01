module

public import RequestProject.Beurling.Model.NTEta
public import RequestProject.Beurling.Noise.TauNearProofLoc
public import RequestProject.Beurling.Noise.Saias59

/-!
# Proposition 5.38, Step 6(b), first bullet: `NT_pt = 0` in the small range

For `y < 0.7 (X₀⁻)²` no cofactor `w` is `τ`-near at `y`: a cofactor with `y/w ≥ X₀⁻` has
`w ≤ y/X₀⁻`, its decision time is `τ_w ≤ 1.1 w` (every prime factor `p | w` has `p ≤ w` and
`t(p) ≤ p + H(p) ≤ 1.1 p`), while `τ`-nearness forces `τ_w ≥ y/w - 2H(y/w) ≥ 0.8 y/w`; hence
`0.8 y/w ≤ 1.1 w`, i.e. `y ≥ 0.727 (X₀⁻)²`. (The paper: "every `n` with `c_n(y) ≠ 0` has
`n ≤ y/X₀⁻ < X₀`, so `τ_w < y/w` always: the `τ`-filter of `K_pt` is void, `NT = NT_pt = 0`".)

* `BaseRange.etaG_small_zero` : `η(y) = ∑_{w τ-near at y} ψ(y/w)/w = 0` for `y < 0.7 (X₀⁻)²`;
* `BaseRange.NTpt_small_zero` : `NT_pt(y) = 0` there, for the realised system (eq. (NT),
  `BModel.NTpt_abs_le_eta`).
-/

@[expose] public section

open Finset BeurlingSystem

namespace BaseRange

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- The decision time of a cofactor is at most `1.1` times its value: `τ_w ≤ 1.1 w`. -/
lemma tauW_le_val (h : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (e : ℕ →₀ ℕ) :
    KR.tauW tw (iota e) ≤ 1.1 * P.val e := by
  unfold KR.tauW
  split_ifs with hne
  · refine Finset.sup'_le _ _ fun r hr => ?_
    rw [BeurlingSystem.primeFactors_iota] at hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hp := P.p_le_val hj
    have hp0 := P.p_pos j
    by_cases hjX : X0m / 2 ≤ P.p j
    · have h1 := (abs_le.mp (h.dec_hi j hjX)).2
      have h2 := h.width.small _ hjX
      linarith
    · push_neg at hjX
      rw [h.dec_lo j hjX]; linarith
  · have := P.val_pos e; linarith

/-- **No `τ`-near cofactors below `0.7 (X₀⁻)²`** (Proposition 5.38, Step 6(b), first bullet). -/
theorem not_tauNear_small (h : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) {v : ℝ}
    (hv : v < 0.7 * X0m ^ 2) {m : ℕ} (hm : m ∈ KR.Cof P X0m v) :
    ¬ KR.TauNearAt P H tw X0m v m := by
  rintro ⟨hτ, hX⟩
  have hX0 := h.width.X0m_pos
  obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
  rw [mem_elems] at he
  have hVl : KR.Vl P (iota e) = P.val e := P.valN_iota e
  rw [hVl] at hτ hX
  have hval := P.val_pos e
  have hsm := h.width.small (v / P.val e) (by linarith)
  have hτ1 := (abs_le.mp hτ).1
  have hτ2 := tauW_le_val h e
  set q := v / P.val e with hq
  have hvq : v = q * P.val e := by rw [hq]; field_simp
  have hve : P.val e * X0m ≤ v := by rw [le_div_iff₀ hX0] at he; linarith
  -- `0.8 q ≤ 1.1 w`, `X₀⁻ ≤ q`, `w X₀⁻ ≤ q w`
  have h08 : 0.8 * q ≤ 1.1 * P.val e := by linarith
  have hqX : X0m ≤ q := hX
  have hwX : P.val e * X0m ≤ q * P.val e := by linarith
  have hw : X0m * X0m ≤ q * q := mul_le_mul hqX hqX hX0.le (by linarith)
  -- `X₀⁻² ≤ q²` and `q² ≤ 1.375 q w = 1.375 v`
  have hq2 : q * q ≤ 1.375 * v := by rw [hvq]; nlinarith
  nlinarith

/-- `η(y) = 0` for `y < 0.7 (X₀⁻)²`, for every weight `ψ`. -/
theorem etaG_small_zero (h : KR.TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ) (ψ : ℝ → ℝ) {v : ℝ}
    (hv : v < 0.7 * X0m ^ 2) : KR.etaG P H tw X0m ψ v = 0 := by
  classical
  unfold KR.etaG
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  exact absurd hm2 (not_tauNear_small h hv hm1)

end BaseRange

namespace BaseRange

open BModel Construction

variable {θ : ℝ} {X₀ : ℕ}

/-- **`NT_pt(y) = 0` for `y < 0.7 (X₀⁻)²`** at the realised system (eq. (NT) with no `τ`-near
cofactors). -/
theorem NTpt_small_zero (hc : Cond θ X₀) (hev : Even X₀) {ω : JitterΩ} {Z η1 η2 ε θH : ℝ}
    {ε1 : ℝ → ℝ}
    (h : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 ε θH) {y : ℝ}
    (hy : y < 0.7 * Xm X₀ ^ 2) : NTpt θ X₀ ω y = 0 := by
  have := NTpt_abs_le_eta hc hev ω y
  rw [etaG_small_zero h _ hy, mul_zero] at this
  exact abs_nonpos_iff.mp this

end BaseRange

end
