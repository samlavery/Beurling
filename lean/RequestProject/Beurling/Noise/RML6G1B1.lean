module

public import RequestProject.Beurling.Noise.BridgeG1B

/-!
# Field `g1`, range (B), Step 1: the window average of `ρ̃` (proof of Proposition 5.35(B))

For a start `x` in range (B) (`log x ≥ X₀^{1/100}`), the window `J = [x(1-2δ), x(1-δ)]` with
`δ ≤ X₀^{-1/2}` and `1/δ ≤ Γ(x)² log⁴ x + X₀^{1/2}`, `Γ(x)² = e^{c_LP √(log x)/2}`
(the paper's choice `δ = min(γ_*^{-2} log^{-4} x, X₀^{-1/2})` with `γ_*` resolvable), and the
first bullet of Step 1 (`∫_J ρ̃ ≥ Π(J) - E_loc`, `E_loc ≤ 40√x`: the partial boxes, the local
count of Corollary 6.3 and the prime powers — owner: Queue6 / Model), Theorem 5.24(ii) at the
certified height `x(1-δ)` gives

  `avg_J ρ̃ ≥ π₀(x) - o₁/log x`,  `o₁ ≤ 10⁻²⁵`  (`step1_g1`).

The size of `o₁` is the paper's "the error is at most `π₀(x) e^{-Λ}`": here
`o₁ = log x · (2K x e^{-c_LP √(log x(1-2δ))} + E_loc)/(δx)` is bounded outright from
`c_LP = 0.0176/Λ`, `K = e^{98} Λ^{5.9}` and `√(log x) ≥ 4.5·10⁷ Λ³` (`sqrt_log_ge`).
-/

@[expose] public section

open Real

namespace KR.RML6

/-- `√(log x) ≥ 4.5·10⁷ Λ³` when `log x ≥ e^{Λ/100}`, `Λ ≥ 10⁸`. -/
lemma sqrt_log_ge {Λ L : ℝ} (hΛ : 100000000 ≤ Λ) (hL : Real.exp (Λ / 100) ≤ L) :
    45000000 * Λ ^ 3 ≤ √L := by
  have h12 := Real.pow_div_factorial_le_exp (x := Λ / 100) (by positivity) 12
  norm_num [Nat.factorial] at h12
  have hΛ6 : (100000000 : ℝ) ^ 6 ≤ Λ ^ 6 := pow_le_pow_left₀ (by norm_num) hΛ 6
  have hL' : (45000000 * Λ ^ 3) ^ 2 ≤ L := by
    have e : (Λ / 100) ^ 12 / 479001600 = Λ ^ 6 * Λ ^ 6 / 479001600000000000000000000000000 := by
      ring
    rw [e] at h12
    have : (45000000 * Λ ^ 3) ^ 2 ≤ Λ ^ 6 * Λ ^ 6 / 479001600000000000000000000000000 := by
      rw [le_div_iff₀ (by norm_num)]
      have h6 : 0 ≤ Λ ^ 6 := by positivity
      nlinarith
    linarith
  exact Real.le_sqrt_of_sq_le hL'

/-- The two exponential sizes behind `o₁`, in log form. With `s = √L`, `c = 0.0176/Λ`:
`c s/2 ≥ 20√s + 6.4Λ + 172` and `s²/2 ≥ 20√s + Λ/2 + c s/2 + 77`. -/
lemma step1_exponents {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : 45000000 * Λ ^ 3 ≤ s) :
    20 * √s + 6.4 * Λ + 172 ≤ 0.0176 / Λ * s / 2 ∧
      20 * √s + Λ / 2 + 0.0176 / Λ * s / 2 + 77 ≤ s ^ 2 / 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛ3 : (100000000 : ℝ) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by norm_num) hΛ 3
  have hs0 : 0 < s := by nlinarith
  have hsq : √s * √s = s := Real.mul_self_sqrt hs0.le
  have hsq0 : 0 ≤ √s := Real.sqrt_nonneg s
  -- `√s ≤ s / 10^10`, as `s ≥ 10^20`
  have hsbig : (100000000000000000000 : ℝ) ≤ s := by nlinarith
  have hsqbig : (10000000000 : ℝ) ≤ √s := by
    rw [show (10000000000 : ℝ) = √(100000000000000000000) by
      rw [show (100000000000000000000 : ℝ) = 10000000000 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hsbig
  have hrt : √s ≤ s / 10000000000 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  -- `c s ≥ 3.9·10⁵ Λ² ≥ ...`
  have hcs : 0.0176 / Λ * s / 2 = 0.0088 * s / Λ := by field_simp; ring
  have hcs1 : 396000 * Λ ^ 2 ≤ 0.0088 * s / Λ := by
    rw [le_div_iff₀ hΛ0]; nlinarith
  have hΛ2 : 100000000 * Λ ≤ Λ ^ 2 := by nlinarith
  constructor
  · rw [hcs]
    -- `20√s ≤ 0.0044 s/Λ` and `6.4Λ + 172 ≤ 0.0044 s/Λ`
    have h1 : 20 * √s ≤ 0.0044 * s / Λ := by
      rw [le_div_iff₀ hΛ0]
      -- `20 √s Λ ≤ 20 (s/10^10) Λ` and `s ≥ 4.5·10⁷ Λ³ ≥ Λ · 10^23`
      have : 20 * √s * Λ ≤ 20 * (s / 10000000000) * Λ := by
        apply mul_le_mul_of_nonneg_right _ hΛ0.le; linarith
      have hsΛ : Λ * 1000000 ≤ s := by nlinarith
      nlinarith
    have h2 : 6.4 * Λ + 172 ≤ 0.0044 * s / Λ := by
      rw [le_div_iff₀ hΛ0]; nlinarith
    have : 0.0088 * s / Λ = 0.0044 * s / Λ + 0.0044 * s / Λ := by ring
    linarith
  · have hc1 : 0.0176 / Λ * s / 2 ≤ s := by
      rw [hcs, div_le_iff₀ hΛ0]; nlinarith
    have : 20 * √s + Λ / 2 + s + 77 ≤ s ^ 2 / 2 := by
      have hΛs : Λ ≤ s := by nlinarith
      nlinarith
    linarith

lemma exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have := Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith

lemma exp_neg_71_le : Real.exp (-71) ≤ 1 / (2 * 10 ^ 25) := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have h := Real.exp_one_gt_d9
  have e : Real.exp 71 = Real.exp 1 ^ 71 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7 : ℝ) ^ 71 ≤ Real.exp 1 ^ 71 := pow_le_pow_left₀ (by norm_num) (by linarith) 71
  have h2 : (2 * 10 ^ 25 : ℝ) ≤ 2.7 ^ 71 := by norm_num
  linarith

/-- Room above `log X_LP`: `10⁵ Λ² log² Λ + 1 ≤ e^{Λ/100}`. -/
lemma xlp_room {Λ : ℝ} (hΛ : 100000000 ≤ Λ) :
    10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 + 1 ≤ Real.exp (Λ / 100) := by
  have hΛ0 : 0 < Λ := by linarith
  have h13 := Real.pow_div_factorial_le_exp (x := Λ / 100) (by positivity) 13
  have hlog : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
  have hlog0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hl2' : Real.log Λ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have e13 : (Λ / 100) ^ 13 / (Nat.factorial 13 : ℝ) =
      Λ ^ 9 * Λ ^ 4 / 622702080000000000000000000000000000 := by
    norm_num [Nat.factorial]; ring
  rw [e13] at h13
  have hΛ9 : (100000000 : ℝ) ^ 9 ≤ Λ ^ 9 := pow_le_pow_left₀ (by norm_num) hΛ 9
  have h4pos : 0 ≤ Λ ^ 4 := by positivity
  have h1 : (1 : ℝ) ≤ Λ ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show (1 : ℝ) ≤ Λ by linarith) 4
    simpa using this
  have hkey : 10 ^ 5 * Λ ^ 4 + 1 ≤ Λ ^ 9 * Λ ^ 4 / 622702080000000000000000000000000000 := by
    rw [le_div_iff₀ (by norm_num)]
    have h9 : (10 ^ 5 + 1) * 622702080000000000000000000000000000 ≤ Λ ^ 9 := by
      norm_num at hΛ9 ⊢; linarith
    have := mul_le_mul_of_nonneg_right h9 h4pos
    nlinarith
  have hA : 10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2 ≤ 10 ^ 5 * Λ ^ 4 := by
    have := mul_le_mul_of_nonneg_left hl2' (show (0 : ℝ) ≤ 10 ^ 5 * Λ ^ 2 by positivity)
    nlinarith
  linarith

/-- `X_LP ≤ x(1-2δ)` in range (B). -/
lemma xlp_le {Λ x δ : ℝ} (hΛ : 100000000 ≤ Λ) (hx0 : 0 < x)
    (hL : Real.exp (Λ / 100) ≤ Real.log x) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    LocalPNT.XLP Λ ≤ x * (1 - 2 * δ) := by
  unfold LocalPNT.XLP
  have hhalf : x / 2 ≤ x * (1 - 2 * δ) := by nlinarith
  refine le_trans ?_ hhalf
  have hxe : x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
  rw [hxe, le_div_iff₀ (by norm_num), ← Real.exp_log (show (0:ℝ) < 2 by norm_num),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have := xlp_room hΛ
  linarith

/-- First term of `o₁`. -/
lemma o1_term1 {Λ s c K E iδ : ℝ} (_hs0 : 0 < s)
    (hc1 : c ≤ 1) (hex1 : 20 * √s + 6.4 * Λ + 172 ≤ c * s / 2)
    (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (98 + 5.9 * Λ)) (hE0 : 0 ≤ E)
    (hEb : E ≤ Real.exp c * Real.exp (-(c * s))) (_hiδ0 : 0 ≤ iδ)
    (hiδ : iδ ≤ 2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2))
    (hlogs : Real.log s ≤ 2 * √s) :
    Real.exp (2 * Real.log s) * iδ * (2 * K * E) ≤ Real.exp (-71) := by
  set T := 2 * Real.log s + (c * s / 2 + 8 * Real.log s + Λ / 2) + (98 + 5.9 * Λ) + c +
    -(c * s) with hT
  have hTe : Real.exp T = Real.exp (2 * Real.log s) *
      Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2) * Real.exp (98 + 5.9 * Λ) * Real.exp c *
        Real.exp (-(c * s)) := by
    simp only [hT, Real.exp_add]
  have hb : T ≤ -73 := by rw [hT]; linarith
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
  calc Real.exp (2 * Real.log s) * iδ * (2 * K * E)
      ≤ Real.exp (2 * Real.log s) * (2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2)) *
          (2 * Real.exp (98 + 5.9 * Λ) * (Real.exp c * Real.exp (-(c * s)))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hiδ (Real.exp_pos _).le) _ (by positivity)
          (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num)) hEb hE0 (by positivity)
    _ = 4 * Real.exp T := by rw [hTe]; ring
    _ ≤ Real.exp 2 * Real.exp (-73) :=
        mul_le_mul h4 (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-71) := by rw [← Real.exp_add]; norm_num

/-- Second term of `o₁`. -/
lemma o1_term2 {Λ s c L iδ F : ℝ}
    (hex2 : 20 * √s + Λ / 2 + c * s / 2 + 77 ≤ s ^ 2 / 2) (hss : s ^ 2 = L)
    (hiδ : iδ ≤ 2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2))
    (hlogs : Real.log s ≤ 2 * √s) (hF0 : 0 ≤ F) (hF : F ≤ 40 * Real.exp (-(L / 2))) :
    Real.exp (2 * Real.log s) * iδ * F ≤ Real.exp (-71) := by
  set T := 2 * Real.log s + (c * s / 2 + 8 * Real.log s + Λ / 2) + -(L / 2) with hT
  have hTe : Real.exp T = Real.exp (2 * Real.log s) *
      Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2) * Real.exp (-(L / 2)) := by
    simp only [hT, Real.exp_add]
  have hb : T ≤ -77 := by rw [hT, ← hss]; linarith
  have h80 : (80 : ℝ) ≤ Real.exp 6 := by
    have := Real.sum_le_exp_of_nonneg (x := (6 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
  calc Real.exp (2 * Real.log s) * iδ * F
      ≤ Real.exp (2 * Real.log s) * (2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2)) *
          (40 * Real.exp (-(L / 2))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hiδ (Real.exp_pos _).le) hF hF0 (by positivity)
    _ = 80 * Real.exp T := by rw [hTe]; ring
    _ ≤ Real.exp 6 * Real.exp (-77) :=
        mul_le_mul h80 (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-71) := by rw [← Real.exp_add]; norm_num

/-- **Step 1 of Proposition 5.35(B), with the size of the error.** For `Λ = log X₀ ≥ 10⁸`,
`log x ≥ X₀^{1/100}`, `0 < δ ≤ X₀^{-1/2}`, `1/δ ≤ e^{c_LP √(log x)/2} log⁴ x + X₀^{1/2}`,
Theorem 5.24 at the height `x(1-δ)`, and the first bullet `∫_J ρ̃ ≥ Π(J) - E_loc` with
`0 ≤ E_loc ≤ 40√x`: there is `o₁ ≤ 10⁻²⁵` with `π₀(x) - o₁/log x ≤ (∫_J ρ̃)/(δx)`. -/
theorem step1_g1 {P : BeurlingSystem} {X₀ : ℕ} {x δ IJ Eloc : ℝ}
    (hΛ : 100000000 ≤ Real.log X₀) (hx0 : 0 < x) (hx : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ Real.log x)
    (hT : LocalPNT.Theorem524Concl P X₀ (x * (1 - δ))) (hδ0 : 0 < δ)
    (hδ : δ ≤ (X₀ : ℝ) ^ (-(1 / 2) : ℝ))
    (hδlow : 1 / δ ≤ Real.exp (LocalPNT.cLP (Real.log X₀) * √(Real.log x) / 2) *
      Real.log x ^ 4 + (X₀ : ℝ) ^ (1 / 2 : ℝ))
    (hE0 : 0 ≤ Eloc) (hE : Eloc ≤ 40 * √x)
    (hcount : LocalPNT.piCount P (x * (1 - δ)) - LocalPNT.piCount P (x * (1 - 2 * δ)) - Eloc ≤
      IJ) :
    ∃ o1 : ℝ, o1 ≤ 1 / 10 ^ 25 ∧ LocalPNT.pi0Dens x - o1 / Real.log x ≤ IJ / (δ * x) := by
  set Λ := Real.log X₀ with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : (0 : ℝ) < X₀ := by
    by_contra hc; push_neg at hc
    have : (X₀ : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hΛdef, this, Real.log_zero] at hΛ; linarith
  have hrp : ∀ a : ℝ, (X₀ : ℝ) ^ a = Real.exp (a * Λ) := fun a => by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  set L := Real.log x with hLdef
  have hL : Real.exp (Λ / 100) ≤ L := by
    rw [hrp] at hx; convert! hx using 2; ring
  have hL1 : 1 ≤ L := le_trans (by
    have := Real.add_one_le_exp (Λ / 100); linarith) hL
  have hL0 : 0 < L := by linarith
  have hxe : x = Real.exp L := (Real.exp_log hx0).symm
  have hs := sqrt_log_ge hΛ hL
  set s := √L with hsdef
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hΛ3 : 0 < Λ ^ 3 := pow_pos hΛ0 3
  have hs0 : 0 < s := by nlinarith
  set c := LocalPNT.cLP Λ with hcdef
  have hc : c = 0.0176 / Λ := by
    rw [hcdef]; unfold LocalPNT.cLP LocalPNT.cZF; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hΛ0]; linarith
  obtain ⟨hex1, hex2⟩ := step1_exponents hΛ hs
  rw [← hc] at hex1 hex2
  have hδ4 : δ ≤ 1 / 4 := by
    refine hδ.trans ?_
    rw [hrp]
    exact le_trans (Real.exp_le_exp.mpr (by nlinarith)) exp_neg_two_le
  have hXLP1 : 1 < LocalPNT.XLP Λ := by
    unfold LocalPNT.XLP; apply Real.one_lt_exp_iff.mpr
    have : 0 < Real.log Λ := Real.log_pos (by linarith)
    positivity
  have hXLP := xlp_le hΛ hx0 hL hδ0 hδ4
  have havg := KR.G1B.step1_avg hT hδ0 hδ4 hXLP le_rfl hXLP1 hcount
  set E := Real.exp (-(c * √(Real.log (x * (1 - 2 * δ)))))
  set K := LocalPNT.KLP Λ
  refine ⟨L * ((2 * K * x * E + Eloc) / (δ * x)), ?_, ?_⟩
  swap
  · rw [mul_div_cancel_left₀ _ hL0.ne']
    exact havg
  -- `√(log(x(1-2δ))) ≥ s - 1`
  have hl12 : Real.log (x * (1 - 2 * δ)) ≥ L - 1 := by
    have hpos : (0 : ℝ) < 1 - 2 * δ := by linarith
    rw [Real.log_mul hx0.ne' hpos.ne', ← hLdef]
    have : -1 ≤ Real.log (1 - 2 * δ) := by
      rw [Real.le_log_iff_exp_le hpos]
      have he : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have := Real.add_one_le_exp (1 : ℝ); linarith
      linarith
    linarith
  have hsE : s - 1 ≤ √(Real.log (x * (1 - 2 * δ))) := by
    rcases le_or_gt s 1 with h | h
    · exact (by linarith : s - 1 ≤ 0).trans (Real.sqrt_nonneg _)
    · apply Real.le_sqrt_of_sq_le
      have : (s - 1) ^ 2 = L - 2 * s + 1 := by rw [← hss]; ring
      linarith
  have hEb : E ≤ Real.exp c * Real.exp (-(c * s)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hsE hc0.le
    linarith
  have hK : K ≤ Real.exp (98 + 5.9 * Λ) := by
    simp only [K, LocalPNT.KLP]
    rw [Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log Λ ≤ Λ := (Real.log_le_sub_one_of_pos hΛ0).trans (by linarith)
    linarith
  have hK0 : 0 ≤ K := by simp only [K, LocalPNT.KLP]; positivity
  have hL4 : L ^ 4 = Real.exp (8 * Real.log s) := by
    rw [← hss, ← pow_mul, show 8 * Real.log s = ((2 * 4 : ℕ) : ℝ) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs0]
  have hlogs : Real.log s ≤ 2 * √s := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hs0)
    rw [Real.log_sqrt hs0.le] at h
    linarith [Real.sqrt_nonneg s]
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by nlinarith)
  have hinvδ : 1 / δ ≤ 2 * Real.exp (c * s / 2 + 8 * Real.log s + Λ / 2) := by
    refine hδlow.trans ?_
    rw [hL4, hrp, ← Real.exp_add, two_mul]
    apply add_le_add
    · apply Real.exp_le_exp.mpr; linarith
    · apply Real.exp_le_exp.mpr
      have : 0 ≤ c * s := by positivity
      linarith
  have hLs : L = Real.exp (2 * Real.log s) := by
    rw [← hss, show (2 : ℝ) * Real.log s = ((2 : ℕ) : ℝ) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs0]
  have hsqx : √x = Real.exp (L / 2) := by
    rw [hxe, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
      ← Real.exp_add]
    congr 1; ring
  have hEx : Eloc / x ≤ 40 * Real.exp (-(L / 2)) := by
    rw [div_le_iff₀ hx0]
    calc Eloc ≤ 40 * Real.exp (L / 2) := by rw [← hsqx]; exact hE
      _ = 40 * Real.exp (-(L / 2)) * x := by
        rw [hxe, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hsplit : L * ((2 * K * x * E + Eloc) / (δ * x)) =
      Real.exp (2 * Real.log s) * (1 / δ) * (2 * K * E) +
        Real.exp (2 * Real.log s) * (1 / δ) * (Eloc / x) := by
    rw [← hLs]; field_simp
  have hiδ0 : 0 ≤ 1 / δ := by positivity
  have hE0' : 0 ≤ E := (Real.exp_pos _).le
  have h1 := o1_term1 hs0 hc1 hex1 hK0 hK hE0' hEb hiδ0 hinvδ hlogs
  have h2 := o1_term2 hex2 hss hinvδ hlogs (div_nonneg hE0 hx0.le) hEx
  have h72 := exp_neg_71_le
  rw [hsplit]
  have : (1 : ℝ) / (2 * 10 ^ 25) + 1 / (2 * 10 ^ 25) = 1 / 10 ^ 25 := by norm_num
  linarith

end KR.RML6

end
