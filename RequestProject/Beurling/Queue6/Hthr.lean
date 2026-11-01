module

public import RequestProject.Beurling.Queue6.ThreshFields
public import RequestProject.Beurling.Queue6.LocalCount0
public import RequestProject.Beurling.Queue6.G1BQueue6
public import RequestProject.Beurling.Queue6.Thresh6
public import RequestProject.Beurling.InitialRange
public import RequestProject.Beurling.Model.MarginMine

/-!
# Lemma 5.23 at `2δ` for `P(ω)`: the fields `Hy`, `Kloc`, `hthr`, `hH1`, `hH`, `hK0`, `hK` of
`KR.RML6.G1BRest` (Proposition 5.35(B))

At a range-(B) start `y` (`X₀ ≤ y`, `log y > X₀^{1/100}`) and `δ = deltaB θ X₀ ω y`:

* `rangeB_sizes` : `X₀³ ≤ y`, `6H(y)y^{-1/3} ≤ 2δ ≤ 1/4`, `X₀ ≤ a_*(y, 2δ)` and
  `H(y) ≤ e^{log y/8}` (`InitialRange.capH_le_rpow`);
* `threshHyp_R` : **`BeurlingSystem.ThreshHyp`** for `P(ω)`, `t = tJ`, `H = Hc X₀`, `x = y`,
  `2δ`, `K_loc = 0`, from (HBS) on `[1, Z]` with `√y ≤ Z`, Lemma 5.1(iv) up to `Z' ≥ y`
  (`MertensUpTo`, e.g. `mertens_G0` on `Good(< tE1 n)`), on `Good(< t₀) ∩ NiceEv`, `y ≤ t₀`;
* `hthr_R` : **the field `hthr`** with `Hy = Hc X₀ y`, `Kloc = 0` (`ThreshHyp.threshold_mass`);
* `hH_R` : the fields `hH1`, `hH` with `Hy = Hc X₀ y`;
* `sqrt_le_Zc` : `√y ≤ Zc X₀ b` for `y ≤ b + H(b)` (so (HBS) on `[1, Zc b]`, e.g. `hT.hbs`, serves).
-/

@[expose] public section

open Set Real Construction CaplLink QueueMono SlotModel

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1600000 in
/-- **The sizes at a range-(B) start** (proof of Proposition 5.35(B) with Lemma 5.23 at `2δ`):
`X₀³ ≤ y`, `6H(y)y^{-1/3} ≤ 2δ`, `2δ ≤ 1/4`, `X₀ ≤ a_*(y, 2δ)`, `H(y) ≤ e^{log y/8}`. -/
theorem rangeB_sizes (ω : JitterΩ) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) :
    (X₀ : ℝ) ^ 3 ≤ y ∧ 6 * Hc X₀ y / y ^ (1 / 3 : ℝ) ≤ 2 * deltaB θ X₀ ω y ∧
      2 * deltaB θ X₀ ω y ≤ 1 / 4 ∧
      (X₀ : ℝ) ≤ BeurlingSystem.aStar y (2 * deltaB θ X₀ ω y) ∧
      Hc X₀ y ≤ Real.exp (Real.log y / 8) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set Λ := Real.log X₀ with hΛe
  have hΛ : (10 : ℝ) ^ 8 ≤ Λ := hc.hX
  set δ := deltaB θ X₀ ω y with hδe
  have hδ0 : 0 < δ := deltaB_pos hc ω hy
  have hδs : δ ≤ 1 / 1000 := BModel.delta_small hc hev (deltaB_le (θ := θ) ω y)
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hLe
  -- `L ≥ e^{Λ/100}`
  have hLe' : Real.exp (Λ / 100) ≤ L := by
    have h := hyB
    rw [Real.rpow_def_of_pos hX0p] at h
    have : Λ * (1 / 100) = Λ / 100 := by ring
    rw [this] at h; exact h.le
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Λ / 100 by positivity)
  have hL8 : 8 * Λ + 10 ≤ L := by nlinarith
  have hLb : (2 * 10 ^ 8 : ℝ) ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  have hye : y = Real.exp L := (Real.exp_log hy0).symm
  -- `y ≥ 16 X₀⁴`
  have hy4 : 16 * (X₀ : ℝ) ^ 4 ≤ y := by
    have e : Real.log (16 * (X₀ : ℝ) ^ 4) = Real.log 16 + 4 * Λ := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h16 : Real.log 16 ≤ 10 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 10 by norm_num)]
    have : Real.log (16 * (X₀ : ℝ) ^ 4) ≤ Real.log y := by rw [e]; linarith
    exact (Real.log_le_log_iff (by positivity) hy0).mp this
  have hX4 : (X₀ : ℝ) ^ 3 ≤ (X₀ : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hX2 : (X₀ : ℝ) ^ 2 ≤ (X₀ : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  -- `H(y) ≤ y^{1/8} = e^{L/8}`
  have hH8 : Hc X₀ y ≤ Real.exp (L / 8) := by
    rw [Hc_eq hy]
    refine (InitialRange.capH_le_rpow hX0 hc.hX hy).trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos hy0]; congr 1; ring
  refine ⟨by linarith, ?_, by linarith, ?_, hH8⟩
  · -- `1/δ ≤ D ≤ 2 e^{L/16}`
    have hlow := deltaB_low hc ω hy
    have hX2' : (X₀ : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Λ / 2) := by
      rw [Real.rpow_def_of_pos hX0p]; congr 1; ring
    rw [hX2'] at hlow
    have hcl := cLP_mem (Λ := Λ) (by linarith)
    set c := LocalPNT.cLP Λ
    have hs : c * √L / 2 ≤ L / 32 := by
      have hsq := Real.sq_sqrt hL0.le
      have hs0 := Real.sqrt_nonneg L
      have hs16 : 16 ≤ √L := by
        rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
      have : c * √L ≤ √L := by nlinarith
      nlinarith
    have hp := Real.pow_div_factorial_le_exp (L / 32) (by positivity) 8
    have e8 : ((8 : ℕ).factorial : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [e8, div_pow] at hp
    have hL4 : L ^ 4 ≤ Real.exp (L / 32) := by
      have hL4b : (10 : ℝ) ^ 32 ≤ L ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) hLb 4; nlinarith
      have : L ^ 8 = L ^ 4 * L ^ 4 := by ring
      have h8 : (32 : ℝ) ^ 8 * 40320 ≤ 10 ^ 32 := by norm_num
      have hp' : L ^ 8 / 32 ^ 8 / 40320 = L ^ 8 / (32 ^ 8 * 40320) := by ring
      rw [hp', div_le_iff₀ (by norm_num)] at hp
      nlinarith
    have hE1 : Real.exp (c * √L / 2) * L ^ 4 ≤ Real.exp (L / 16) := by
      have : Real.exp (L / 16) = Real.exp (L / 32) * Real.exp (L / 32) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      exact mul_le_mul (Real.exp_le_exp.mpr hs) hL4 (by positivity) (Real.exp_pos _).le
    have hE2 : Real.exp (Λ / 2) ≤ Real.exp (L / 16) := Real.exp_le_exp.mpr (by linarith)
    have hD : 1 / δ ≤ 2 * Real.exp (L / 16) := by linarith
    -- `3 e^{L/8} · 2 e^{L/16} ≤ e^{L/3}`
    have hy3 : y ^ (1 / 3 : ℝ) = Real.exp (L / 3) := by
      rw [Real.rpow_def_of_pos hy0]; congr 1; ring
    rw [hy3, div_le_iff₀ (Real.exp_pos _)]
    have hδD : 1 ≤ δ * (2 * Real.exp (L / 16)) := by
      rw [div_le_iff₀ hδ0] at hD; linarith
    have e3 : Real.exp (L / 3) = Real.exp (L / 8) * Real.exp (L / 16) * Real.exp (7 * L / 48) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h6 : (6 : ℝ) ≤ Real.exp (7 * L / 48) := by
      have := Real.add_one_le_exp (7 * L / 48); linarith
    have hH0 : 0 ≤ Hc X₀ y := by linarith [Hx_ge_R hc y]
    have hA := Real.exp_pos (L / 8)
    have hB := Real.exp_pos (L / 16)
    calc 6 * Hc X₀ y ≤ 6 * Real.exp (L / 8) * (δ * (2 * Real.exp (L / 16))) := by nlinarith
      _ = 2 * δ * (Real.exp (L / 8) * Real.exp (L / 16) * 6) := by ring
      _ ≤ 2 * δ * (Real.exp (L / 8) * Real.exp (L / 16) * Real.exp (7 * L / 48)) := by
          gcongr
      _ = 2 * δ * Real.exp (L / 3) := by rw [e3]
  · -- `a_*(y, 2δ)² ≥ 3y/8 ≥ X₀²`
    unfold BeurlingSystem.aStar
    rw [Real.le_sqrt hX0 (div_nonneg (by nlinarith) (by linarith)), le_div_iff₀ (by linarith)]
    nlinarith

variable (D : Sec5Family)

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`ThreshHyp` for `P(ω)` at a range-(B) start `y`** with `t = tJ`, `H = Hc X₀`, `x = y`,
window `2δ`, `δ = deltaB θ X₀ ω y`, `K_loc = 0` (the hypotheses of Lemma 5.23), on
`Good(< t₀) ∩ NiceEv` with `y ≤ t₀`, from (HBS) on `[1, Z]` (`√y ≤ Z`) and Lemma 5.1(iv) up to
`Z' ≥ y`. -/
theorem threshHyp_R {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS X0m Z η1 η2 ε1) {Z' : ℝ}
    (hM : MertensUpTo (PR θ X₀ ω) Z') {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hyZ : √y ≤ Z) (hyZ' : y ≤ Z')
    (hyt : y ≤ t₀) :
    (PR θ X₀ ω).ThreshHyp (tJ θ X₀ ω) (Hc X₀) y (2 * deltaB θ X₀ ω y) 0 X0m Z η1 η2 ε1 := by
  obtain ⟨hy3, hδge, hδle, ha, -⟩ := rangeB_sizes hc hev ω hy hyB
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX3 : (X₀ : ℝ) ≤ (X₀ : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hbig := X₀_ge_two_pow hc.hX
  have hy16 : 16 ≤ y := by linarith
  exact
    { hbs := hbs
      sqrt_le := hyZ
      x_ge := hy16
      loglog := by
        obtain ⟨-, -, hll⟩ := logs_of_ge hX0 hc.hX hy
        have : (0 : ℝ) ≤ Real.log (Real.log y) := by
          have h1 := logH_R hc hy
          have h2 : 1 ≤ Real.log y := by
            rw [Real.le_log_iff_exp_le (by linarith)]
            have := Real.exp_one_lt_d9; linarith
          exact Real.log_nonneg h2
        exact this
      t_ge := t_ge_R hc ω
      jit := jit_R hc ω
      jit_small := jitSmall_R hc ω
      H_mono := H_mono_R hc
      H_two := fun z hz => H_two_R hc hz
      Hx_ge := Hx_ge_R hc y
      logH := logH_R hc hy
      δ_ge := hδge
      δ_le := hδle
      Kloc_nonneg := le_rfl
      kSum := fun j _ _ => kSum_R hc ω hM hy hyZ' (tJ θ X₀ ω) j
      countI := countI_R hc D hev hG hN hy3 hyt hδge hδle
      localCount := localCount_R0 hc hev hN hy16 hδge hδle ha }

/-- **The field `hthr` of `KR.RML6.G1BRest`** (Lemma 5.23 at `2δ`, `δ = deltaB`) with
`Hy = Hc X₀ y`, `Kloc = 0`, under the hypotheses of `threshHyp_R`. -/
theorem hthr_R {t₀ : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t₀) (hN : ω ∈ NiceEv θ X₀)
    {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hbs : (PR θ X₀ ω).HBS X0m Z η1 η2 ε1) {Z' : ℝ}
    (hM : MertensUpTo (PR θ X₀ ω) Z') {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyB : (X₀ : ℝ) ^ (1 / 100 : ℝ) < Real.log y) (hyZ : √y ≤ Z) (hyZ' : y ≤ Z')
    (hyt : y ≤ t₀) :
    (PR θ X₀ ω).threshSum (tJ θ X₀ ω) y (2 * deltaB θ X₀ ω y) ≤
      55 * (2 * deltaB θ X₀ ω y) * Real.log y *
          (Real.log (Hc X₀ y) + Real.log (1 / (2 * deltaB θ X₀ ω y)) + 2) +
        14 * (0 + 2) * Real.log y * √(Hc X₀ y / (2 * deltaB θ X₀ ω y * y)) :=
  (threshHyp_R hc hev D hG hN hbs hM hy hyB hyZ hyZ' hyt).threshold_mass

omit hev in
/-- **The fields `hH1`, `hH` (and `hK0`, `hK` with `Kloc = 0`)** of `KR.RML6.G1BRest` with
`Hy = Hc X₀ y`: `1 ≤ H(y) ≤ e^{log y/8}` (`InitialRange.capH_le_rpow`), `0 ≤ 0 ≤ H(y)`. -/
theorem hH_R {y : ℝ} (hy : (X₀ : ℝ) ≤ y) :
    1 ≤ Hc X₀ y ∧ Hc X₀ y ≤ Real.exp (Real.log y / 8) ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ Hc X₀ y := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hy0 : 0 < y := by linarith
  have h1 := Hx_ge_R hc y
  refine ⟨h1, ?_, le_rfl, by linarith⟩
  rw [Hc_eq hy]
  refine (InitialRange.capH_le_rpow hX0 hc.hX hy).trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos hy0]; congr 1; ring

omit hev in
/-- **The (HBS) horizon of `ThreshHyp`**: `√y ≤ Zc X₀ b` for `X₀ ≤ b`, `y ≤ b + H(b)`. -/
theorem sqrt_le_Zc {b y : ℝ} (hb : (X₀ : ℝ) ≤ b) (hyb : y ≤ b + Hc X₀ b) :
    √y ≤ Zc X₀ b := by
  obtain ⟨-, h2500, h18, -⟩ := Zc_facts hc hb
  have hH0 := Hc_nonneg (X₀ := X₀) b
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

end Queue6

end
