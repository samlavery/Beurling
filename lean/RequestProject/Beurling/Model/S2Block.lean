module

public import RequestProject.Beurling.Noise.LemSii
public import RequestProject.Beurling.Noise.Lemma53Main
public import RequestProject.Beurling.Noise.Lemma53Sums

/-!
# The second bound of (s2): one dyadic cofactor block (04d-noise.tex, l. 58–80)

The second bullet of the proof of (s2) (Proposition 4.10 / Lemma 4.11 input, "second bound, for
`σ > log X₀⁻`") sums, over cofactors `m ∈ (Y, 2Y]` with `P⁺(m) ≤ z`, the weight
`e^{-(c-1)s_Y}`, where `e^{s_Y}` is the least admissible prime. Here we bound one such block
for a general Beurling system `P` with (HBS) on `[1, Z]`:

`e^{-(c-1) s_Y} v(log Y, z) ≤ 3 e^{-σ} (X₀⁻)^{-(c-2)/2}`, `σ = ½ √(L log L)`, `L = log v`,

with `s_Y = max(log X₀⁻, log(v/8Y)/c)` and `z = 2(2v/Y)^{1/c}` (`block_le`).

* If `s_Y ≥ σ` or `(c-2) s_Y ≥ 2σ`, the trivial bound `v ≤ ∑_{(Y,2Y]} 1/n ≤ 1` suffices.
* Otherwise `ℓ = log Y ≥ L - 4σ - log 8`, `log z ≤ σ + 2.08`, and `v(ℓ, z) ≤ e^{-σ}` by
  Lemma 5.3 (`HBS.lemma53`): at `(z, u' = ℓ/log z)` if `u' ≤ log z`, and at
  `(e^{√ℓ}, √ℓ)` otherwise (monotonicity in `z`), each time with `ρ(u)e^{a_V} ≤ 2e^{-0.7u log u}`
  (`LemS.rho_exp_le_big`).
-/

@[expose] public section

open Real Finset

namespace BeurlingSystem

namespace S2Block

/-- `12.8 log(y + 2) ≤ 1.3·10⁻⁵ y` for `y ≥ 10⁸ - 1`. -/
lemma log_small {y : ℝ} (hy : 10 ^ 8 - 1 ≤ y) :
    4 * 3.2 * Real.log (y + 2) ≤ 0.000013 * y := by
  have h1 : Real.log (y + 2) ≤ Real.log ((y + 1) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 := LemS.log_add_two_le (L := y + 1) (by linarith)
  nlinarith

/-- `e^{18} ≤ 10⁸`. -/
lemma exp_18_le : Real.exp 18 ≤ 10 ^ 8 := by
  have h := Real.exp_one_lt_d9
  have h1 : Real.exp 18 = Real.exp 1 ^ 18 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h.le 18
    _ ≤ 10 ^ 8 := by norm_num

/-- The numerics of `σ = ½ √(L log L) > 10⁸ - 1` (`λ = log L`): `4σ² = Lλ`, `λ ≥ 18`,
`σ ≥ 50 λ + 100`, and `log 4 + 2 log σ = λ + log λ`. -/
lemma sigma_facts {L σ : ℝ} (hL : 0 < L) (hσdef : σ = √(L * Real.log L) / 2)
    (hσ : 10 ^ 8 - 1 < σ) :
    4 * σ ^ 2 = L * Real.log L ∧ 18 ≤ Real.log L ∧ 50 * Real.log L + 100 ≤ σ ∧
      Real.log 4 + 2 * Real.log σ = Real.log L + Real.log (Real.log L) := by
  have hpos : 0 < L * Real.log L := by
    by_contra hn
    push_neg at hn
    rw [Real.sqrt_eq_zero'.mpr hn] at hσdef
    linarith
  have hlam : 0 < Real.log L := by
    by_contra hn
    push_neg at hn
    nlinarith
  have hsq : 4 * σ ^ 2 = L * Real.log L := by
    rw [hσdef, div_pow, Real.sq_sqrt hpos.le]; ring
  have hlamL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL).trans (by linarith)
  have hL2 : 2 * σ ≤ L := by
    by_contra hn
    push_neg at hn
    have := mul_self_lt_mul_self hL.le hn
    nlinarith
  have h18 : 18 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL]
    linarith [exp_18_le]
  refine ⟨hsq, h18, ?_, ?_⟩
  · -- `L ≤ 4σ² = ρ⁴`, `ρ = √(2σ)`, and `log L ≤ 4 log ρ ≤ 4(ρ - 1)`
    have hσ0 : 0 < σ := by linarith
    set ρ := √(2 * σ) with hρ
    have hρ2 : ρ ^ 2 = 2 * σ := Real.sq_sqrt (by linarith)
    have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by linarith)
    have hρ1000 : 1000 ≤ ρ := by nlinarith
    have hL4 : L ≤ ρ ^ 4 := by nlinarith
    have hlog : Real.log L ≤ 4 * (ρ - 1) := by
      calc Real.log L ≤ Real.log (ρ ^ 4) := Real.log_le_log hL hL4
        _ = 4 * Real.log ρ := by rw [Real.log_pow]; norm_num
        _ ≤ 4 * (ρ - 1) := by linarith [Real.log_le_sub_one_of_pos hρ0]
    nlinarith
  · have h1 : Real.log (4 * σ ^ 2) = Real.log 4 + 2 * Real.log σ := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    rw [← h1, hsq, Real.log_mul hL.ne' hlam.ne']

/-- `C₀ ρ(u) e^{a} ≤ e^{-σ}` once `u > 30`, `a ≤ 1.3·10⁻⁵ u` and `0.7 u log u ≥ σ + 1`
(`LemS.rho_exp_le_big`, `2C₀ = 1.4 ≤ e`). -/
lemma final_step {u a σ : ℝ} (hu : 30 < u) (ha : a ≤ 0.000013 * u)
    (hσ : σ + 1 ≤ 0.7 * u * Real.log u) :
    BSaias.C0 * Dickman.rho u * Real.exp a ≤ Real.exp (-σ) := by
  have h := LemS.rho_exp_le_big hu ha
  have hC : BSaias.C0 = 0.70 := rfl
  have he : Real.exp (-(0.7 * u * Real.log u)) ≤ Real.exp (-σ + -1) :=
    Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-σ + -1) * Real.exp 1 = Real.exp (-σ) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpos := Real.exp_pos (-σ + -1)
  rw [hC, mul_assoc]
  nlinarith

/-- First case of Lemma 5.3's use (`u' = ℓ/log z ≤ log z`): `u' > 30` and
`0.7 u' log u' ≥ σ + 1`, from `ℓ > L - 4σ - 2.08`, `0 < log z ≤ σ + 2.08`. -/
lemma case1_num {L σ ℓ Lz : ℝ} (hsq : 4 * σ ^ 2 = L * Real.log L)
    (h18 : 18 ≤ Real.log L) (h50 : 50 * Real.log L + 100 ≤ σ)
    (hlog : Real.log 4 + 2 * Real.log σ = Real.log L + Real.log (Real.log L))
    (hℓ : L - 4 * σ - 2.08 < ℓ) (hLz0 : 0 < Lz) (hLz : Lz ≤ σ + 2.08) :
    30 < ℓ / Lz ∧ σ + 1 ≤ 0.7 * (ℓ / Lz) * Real.log (ℓ / Lz) := by
  set lam := Real.log L with hlamdef
  have hlam0 : 0 < lam := by linarith
  have hσ0 : 0 < σ := by linarith
  set K := 3.9 * σ / lam with hK
  have hKu : K ≤ ℓ / Lz := by
    rw [hK, div_le_div_iff₀ hlam0 hLz0]
    have h1 : (L - 4 * σ - 2.08) * lam ≤ ℓ * lam := mul_le_mul_of_nonneg_right hℓ.le hlam0.le
    have h2 : 3.9 * σ * Lz ≤ 3.9 * σ * (σ + 2.08) := by gcongr
    nlinarith
  have hK30 : 30 < K := by
    rw [hK, lt_div_iff₀ hlam0]; nlinarith
  have hK0 : 0 < K := by linarith
  -- `log K = log 3.9 - log 2 + (λ - log λ)/2 ≥ (λ - log λ)/2`
  have hlogK : (lam - Real.log lam) / 2 ≤ Real.log K := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h39 : Real.log 2 ≤ Real.log 3.9 := Real.log_le_log (by norm_num) (by norm_num)
    rw [hK, Real.log_div (by positivity) hlam0.ne', Real.log_mul (by norm_num) hσ0.ne']
    linarith
  -- `log λ ≤ 3 log 2 + λ/8 - 1`
  have hloglam : Real.log lam ≤ 1.08 + lam / 8 := by
    have h8 : Real.log lam = Real.log 8 + Real.log (lam / 8) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
    have h8' : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show 0 < lam / 8 by positivity)
    have := Real.log_two_lt_d9
    linarith
  have hKlog : σ + 1 ≤ 0.7 * K * Real.log K := by
    have h1 : 0.7 * K * ((lam - Real.log lam) / 2) ≤ 0.7 * K * Real.log K := by gcongr
    have h2 : 0.7 * K * ((lam - Real.log lam) / 2) * lam
        = 1.365 * σ * (lam - Real.log lam) := by
      rw [hK]; field_simp; ring
    have h3 : (σ + 1) * lam ≤ 0.7 * K * ((lam - Real.log lam) / 2) * lam := by
      rw [h2]; nlinarith
    have h4 := le_of_mul_le_mul_right h3 hlam0
    linarith
  refine ⟨hK30.trans_le hKu, hKlog.trans ?_⟩
  have := Real.log_le_log hK0 hKu
  have hlK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  nlinarith

/-- Second case (`u' > log z`): with `r = √ℓ`, `r > 30` and `0.7 r log r ≥ σ + 1`. -/
lemma case2_num {L σ ℓ : ℝ} (hL : 0 < L) (hsq : 4 * σ ^ 2 = L * Real.log L)
    (h18 : 18 ≤ Real.log L) (h50 : 50 * Real.log L + 100 ≤ σ)
    (hℓ : L - 4 * σ - 2.08 < ℓ) :
    30 < √ℓ ∧ σ + 1 ≤ 0.7 * √ℓ * Real.log √ℓ := by
  set lam := Real.log L with hlamdef
  have hlam0 : 0 < lam := by linarith
  have hσ0 : 0 < σ := by linarith
  have hL200 : 200 * σ ≤ L := by nlinarith
  have hℓL : 0.81 * L ≤ ℓ := by nlinarith
  set a := √L with ha
  set m := √lam with hm
  have ha2 : a ^ 2 = L := Real.sq_sqrt hL.le
  have hm2 : m ^ 2 = lam := Real.sq_sqrt hlam0.le
  have ha0 : 0 < a := Real.sqrt_pos.mpr hL
  have hm0 : 0 < m := Real.sqrt_pos.mpr hlam0
  have hσam : 2 * σ = a * m := by
    have h1 : (a * m) ^ 2 = (2 * σ) ^ 2 := by rw [mul_pow, ha2, hm2]; nlinarith
    exact ((pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1).symm
  have hr : 0.9 * a ≤ √ℓ := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; nlinarith
  have hm4 : 4.2 ≤ m := by nlinarith
  have hlogr : lam / 2 - 0.12 ≤ Real.log √ℓ := by
    have h1 : Real.log (0.9 * a) = Real.log 0.9 + lam / 2 := by
      rw [Real.log_mul (by norm_num) ha0.ne', ha, Real.log_sqrt hL.le]
    have h2 : -0.12 ≤ Real.log 0.9 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.9 by norm_num)
      norm_num at this ⊢; linarith
    have := Real.log_le_log (by positivity) hr
    linarith
  have ha1 : 100 ≤ a := by
    by_contra hn
    push_neg at hn
    have := mul_lt_mul'' hn hn ha0.le ha0.le
    nlinarith
  refine ⟨by nlinarith, ?_⟩
  have hl0 : 0 ≤ lam / 2 - 0.12 := by linarith
  have h1 : 0.7 * (0.9 * a) * (lam / 2 - 0.12) ≤ 0.7 * √ℓ * Real.log √ℓ := by
    have := mul_le_mul hr hlogr hl0 (by positivity)
    nlinarith
  nlinarith


/-- **The regime `s_Y < σ`, `(c-2)s_Y < 2σ` of the second bound of (s2)** (04d-noise.tex,
l. 66–80): if `ℓ = log Y > L - 4σ - 2.08` and `10⁸ - 1 + log 2 < log z ≤ σ + 2.08`, then
`v(ℓ, z) ≤ e^{-σ}`, by Lemma 5.3 at `(z, ℓ/log z)` if `ℓ/log z ≤ log z`, and at
`(e^{√ℓ}, √ℓ)` otherwise. -/
theorem caseB {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {Y z L σ : ℝ} (hY : 0 < Y) (h2Y : 2 * Y ≤ Z) (hz0 : 0 < z)
    (hLz_up : Real.log z ≤ σ + 2.08) (hLz_lo : 10 ^ 8 - 1 + Real.log 2 < Real.log z)
    (hL0 : 0 < L) (hσdef : σ = √(L * Real.log L) / 2) (hσ : 10 ^ 8 - 1 < σ)
    (hℓ : L - 4 * σ - 2.08 < Real.log Y) :
    P.vSmooth Y z ≤ Real.exp (-σ) := by
  obtain ⟨hsq, h18, h50, hlog⟩ := sigma_facts hL0 hσdef hσ
  have hl2' := Real.log_two_gt_d9
  set ℓ := Real.log Y with hℓdef
  set Lz := Real.log z with hLz
  have hLz0 : 0 < Lz := by linarith
  have hz0 : 0 < z := by positivity
  by_cases hB : ℓ ≤ Lz ^ 2
  · -- Lemma 5.3 at `(z, u' = ℓ/log z)`, `u' ≤ log z`
    obtain ⟨hu30, huσ⟩ := case1_num hsq h18 h50 hlog hℓ hLz0 hLz_up
    set u := ℓ / Lz with hu
    have hu0 : 0 < u := by linarith
    have hul : u * Lz = ℓ := by rw [hu]; field_simp
    have huLz : u ≤ Lz := by
      rw [hu, div_le_iff₀ hLz0]; nlinarith
    have hYe : Real.exp (u * Lz) = Y := by rw [hul, hℓdef, Real.exp_log hY]
    have h53 := h.lemma53 z u (by linarith) (by linarith) huLz (by rw [hYe]; exact h2Y)
    rw [hYe] at h53
    refine h53.trans (final_step hu30 ?_ huσ)
    have hlg : Real.log (u + 2) ≤ Real.log (Lz + 2) := Real.log_le_log (by linarith) (by linarith)
    have hsm := log_small (y := Lz) (by linarith)
    unfold BSaias.aV
    rw [hul, div_le_iff₀ (by rw [← hul]; positivity), ← hul]
    have := mul_le_mul_of_nonneg_left hlg (show 0 ≤ 4 * 3.2 * u ^ 2 by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hsm (show 0 ≤ u ^ 2 by positivity)]
  · -- Lemma 5.3 at `(e^{√ℓ}, √ℓ)`, using `z ≤ e^{√ℓ}`
    push_neg at hB
    obtain ⟨hr30, hrσ⟩ := case2_num hL0 hsq h18 h50 hℓ
    set r := √ℓ with hr
    have hℓ0 : 0 < ℓ := lt_of_le_of_lt (by positivity) hB
    have hrr : r * r = ℓ := Real.mul_self_sqrt hℓ0.le
    have hLzr : Lz < r := by rw [hr, Real.lt_sqrt hLz0.le]; exact hB
    have hzr : z ≤ Real.exp r := by
      rw [← Real.exp_log hz0]; exact Real.exp_le_exp.mpr hLzr.le
    have hYe : Real.exp (r * r) = Y := by rw [hrr, hℓdef, Real.exp_log hY]
    have h53 := h.lemma53 (Real.exp r) r (by rw [Real.log_exp]; linarith) (by linarith)
      (by rw [Real.log_exp]) (by rw [Real.log_exp, hYe]; exact h2Y)
    rw [Real.log_exp, hYe] at h53
    refine (P.vSmooth_mono hzr).trans (h53.trans (final_step hr30 ?_ hrσ))
    have haV : BSaias.aV (r * r) r = 4 * 3.2 * Real.log (r + 2) := by
      unfold BSaias.aV; field_simp
    rw [haV]
    exact log_small (by linarith)

end S2Block

set_option maxHeartbeats 1000000 in
open S2Block in
/-- **The second bound of (s2), one cofactor block** (04d-noise.tex, l. 58–80; Lemma 5.3).
Let `P` satisfy (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸ - 1`, `L = log v`,
`σ = ½ √(L log L) > log X₀⁻`, `4v/(X₀⁻)² ≤ Z`, `c ≥ 2`, `1/2 ≤ Y < 2v/(X₀⁻)^c`. With
`s_Y = max(log X₀⁻, log(v/8Y)/c)` and `z = 2(2v/Y)^{1/c}`,
`e^{-(c-1) s_Y} v(log Y, z) ≤ 3 e^{-σ} (X₀⁻)^{-(c-2)/2}`. -/
theorem block_le (P : BeurlingSystem) {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hX0m : 10 ^ 8 - 1 ≤ Real.log X0m) {v : ℝ} (hv : X0m ≤ v)
    (hσ : Real.log X0m < Real.sqrt (Real.log v * Real.log (Real.log v)) / 2)
    (hZ : 4 * v / X0m ^ 2 ≤ Z) {c : ℕ} (hc : 2 ≤ c) {Y : ℝ} (hY0 : 1 / 2 ≤ Y)
    (hYv : Y < 2 * v / X0m ^ c) :
    Real.exp (-((c - 1 : ℝ) * max (Real.log X0m) (Real.log (v / (8 * Y)) / c))) *
        P.vSmooth Y (2 * (2 * v / Y) ^ (1 / (c : ℝ))) ≤
      3 * Real.exp (-(Real.sqrt (Real.log v * Real.log (Real.log v)) / 2)) *
        X0m ^ (-((c - 2 : ℝ) / 2)) := by
  set σ := √(Real.log v * Real.log (Real.log v)) / 2 with hσdef
  set lX := Real.log X0m with hlX
  set s := Real.log (v / (8 * Y)) / c with hs
  set sY := max lX s with hsY
  set z := 2 * (2 * v / Y) ^ (1 / (c : ℝ)) with hz
  set V := P.vSmooth Y z with hV
  have hX0 : 0 < X0m := h.X0m_pos
  have hX1 : 1 ≤ X0m := by linarith [h.X0m_ge]
  have hv0 : 0 < v := by linarith
  have hY : 0 < Y := by linarith
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun e _ => (one_div_pos.mpr (P.val_pos e)).le)
  have hXc : X0m ^ 2 ≤ X0m ^ c := pow_le_pow_right₀ hX1 hc
  have h2Y : 2 * Y ≤ Z := by
    have h1 : Y < 2 * v / X0m ^ 2 :=
      hYv.trans_le (div_le_div_of_nonneg_left (by positivity) (by positivity) hXc)
    have h2 : 2 * (2 * v / X0m ^ 2) = 4 * v / X0m ^ 2 := by ring
    linarith
  have hV1 : V ≤ 1 := (P.vSmooth_le_harmBlock _ _).trans (h.harmBlock_le_one h2Y)
  have hsYX : lX ≤ sY := le_max_left _ _
  have hlX0 : 0 ≤ lX := by linarith
  have hrpow : X0m ^ (-((c - 2 : ℝ) / 2)) = Real.exp (-((c - 2) / 2 * lX)) := by
    rw [Real.rpow_def_of_pos hX0, hlX]; ring_nf
  rw [hrpow]
  have hc2 : (0 : ℝ) ≤ c - 2 := by linarith
  by_cases hA : σ ≤ sY ∨ 2 * σ ≤ (c - 2) * sY
  · -- the trivial bound `v(log Y, z) ≤ 1`
    have hkey : σ + (c - 2) / 2 * lX ≤ (c - 1) * sY := by
      have h1 : 0 ≤ (c - 2) * (sY - lX) := mul_nonneg hc2 (by linarith)
      have h2 : 0 ≤ (c - 2) * lX := mul_nonneg hc2 hlX0
      rcases hA with hA | hA <;> nlinarith
    have he := Real.exp_le_exp.mpr (show -((c - 1) * sY) ≤ -σ + -((c - 2) / 2 * lX) by linarith)
    rw [Real.exp_add] at he
    have hp := Real.exp_pos (-((c - 1) * sY))
    have hp2 := Real.exp_pos (-σ)
    have hp3 := Real.exp_pos (-((c - 2) / 2 * lX))
    calc Real.exp (-((c - 1) * sY)) * V ≤ Real.exp (-((c - 1) * sY)) * 1 := by gcongr
      _ ≤ 3 * Real.exp (-σ) * Real.exp (-((c - 2) / 2 * lX)) := by nlinarith
  push_neg at hA
  obtain ⟨hA1, hA2⟩ := hA
  suffices hVs : V ≤ Real.exp (-σ) by
    have hkey : -((c - 1) * sY) ≤ -((c - 2) / 2 * lX) := by
      have h1 : 0 ≤ (c - 2) * (sY - lX) := mul_nonneg hc2 (by linarith)
      nlinarith
    have he := Real.exp_le_exp.mpr hkey
    have hp := Real.exp_pos (-((c - 1) * sY))
    have hp2 := Real.exp_pos (-σ)
    calc Real.exp (-((c - 1) * sY)) * V ≤ Real.exp (-((c - 2) / 2 * lX)) * Real.exp (-σ) := by
          gcongr
      _ ≤ 3 * Real.exp (-σ) * Real.exp (-((c - 2) / 2 * lX)) := by
          nlinarith [Real.exp_pos (-((c - 2) / 2 * lX))]
  -- the regime `s_Y < σ`, `(c - 2) s_Y < 2σ`
  set L := Real.log v with hLdef
  have hL0 : 0 < L := by have := Real.log_le_log hX0 hv; linarith
  obtain ⟨hsq, h18, h50, hlog⟩ := sigma_facts hL0 hσdef (by linarith)
  set ℓ := Real.log Y with hℓdef
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlogv8 : Real.log (v / (8 * Y)) = L - 3 * Real.log 2 - ℓ := by
    rw [Real.log_div hv0.ne' (by positivity), Real.log_mul (by norm_num) hY.ne', h8]; ring
  have hcs : Real.log (v / (8 * Y)) = c * s := by
    rw [hs]; field_simp
  have hss : s ≤ sY := le_max_right _ _
  have hcs4 : c * s < 4 * σ := by
    have h1 : (c - 2) * s ≤ (c - 2) * sY := mul_le_mul_of_nonneg_left hss hc2
    linarith
  have hℓ : L - 4 * σ - 2.08 < ℓ := by linarith
  -- `log z = log 2 + log(2v/Y)/c`
  have hlog2vY : Real.log (2 * v / Y) = 4 * Real.log 2 + c * s := by
    rw [← hcs, hlogv8, Real.log_div (by positivity) hY.ne', Real.log_mul (by norm_num) hv0.ne']
    ring
  have hLzeq : Real.log z = Real.log 2 + Real.log (2 * v / Y) / c := by
    rw [hz, Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by positivity)]; ring
  have hc0 : (0 : ℝ) < c := by linarith
  have hLz_up : Real.log z ≤ σ + 2.08 := by
    have h1 : 4 * Real.log 2 / c ≤ 2 * Real.log 2 := by
      rw [div_le_iff₀ hc0]
      have := mul_le_mul_of_nonneg_left hcR (show 0 ≤ 2 * Real.log 2 by linarith)
      linarith
    have h2 : Real.log (2 * v / Y) / c = 4 * Real.log 2 / c + s := by
      rw [hlog2vY, add_div, mul_div_cancel_left₀ _ hc0.ne']
    have : s < σ := lt_of_le_of_lt hss hA1
    linarith
  have hLz_lo : lX + Real.log 2 < Real.log z := by
    have h0 := (lt_div_iff₀ (by positivity)).mp hYv
    have h1 : X0m ^ c < 2 * v / Y := by rw [lt_div_iff₀ hY, mul_comm]; exact h0
    have h2 : (c : ℝ) * lX < Real.log (2 * v / Y) := by
      have := Real.log_lt_log (by positivity) h1
      rwa [Real.log_pow] at this
    have h3 : lX < Real.log (2 * v / Y) / c := by rw [lt_div_iff₀ hc0]; linarith
    linarith
  exact caseB h hY h2Y (by positivity) hLz_up (by linarith) hL0 hσdef (by linarith) hℓ

end BeurlingSystem

end
