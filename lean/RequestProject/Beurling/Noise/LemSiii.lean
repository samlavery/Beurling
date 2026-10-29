module

public import RequestProject.Beurling.Noise.LemSii
public import RequestProject.Beurling.Noise.LemSSum

/-!
# Lemma 5.21(iii): the dyadic sum of the filtered cofactor weights

`HBS.lemS_iii` : for `log 3v ≥ 10⁸`,

  `∑_{Y = 2^k ≥ v} log(2Y) sup_{y ∈ [Y, 2Y)} ω_y(v) ≤ C'_S (log 3v)²`,  `C'_S = 10`,

for every finite range of `k` (restricted to the heights `2Y ≤ vZ` where (HBS) is read).

The proof uses the decreasing majorant `OmB L ℓ` of `ω_y(v)` as a function of
`ℓ = log(y/2v)`, `L = log 3v` (`omega_le_OmB`): `1` for `ℓ < L` ((i)), and
`0.71 e^{-0.99(ℓ/L - 1)} + 2 e^{-√ℓ/2}` for `ℓ ≥ L` ((ii) via Lemma 5.3, with `z = 3v` for
`ℓ ≤ L²` and `z = e^{√ℓ}` for `ℓ > L²`). The levels `ℓ < L` contribute at most `3L²`
(`partA_le`), the others at most `3.2L² + 1` (`partB_le`, geometric sums). The paper bounds the
sum by `9.82 (log 3v)²` with `ρ ≤ 1/Γ(u+1)`; the cruder decay `ρ(u) ≤ e^{1-u}` suffices here
because Lemma 5.3 is used with the constant `C₀` (the paper uses `2C₀`).
-/

@[expose] public section

open Finset Real

namespace LemS

/-- The majorant of `ω_y(v)` in terms of `ℓ = log(y/2v)` and `L = log 3v`. -/
noncomputable def OmB (L ℓ : ℝ) : ℝ :=
  if ℓ < L then 1 else 0.71 * Real.exp (-(0.99 * (ℓ / L - 1))) + 2 * Real.exp (-(√ℓ / 2))

lemma OmB_nonneg (L ℓ : ℝ) : 0 ≤ OmB L ℓ := by
  unfold OmB; split_ifs <;> positivity

lemma exp_neg_le_inv {s : ℝ} (hs : 0 ≤ s) : Real.exp (-s) ≤ 1 / (1 + s) := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp s])

lemma OmB_anti {L : ℝ} (hL : 100000000 ≤ L) {ℓ₁ ℓ₂ : ℝ} (h12 : ℓ₁ ≤ ℓ₂) :
    OmB L ℓ₂ ≤ OmB L ℓ₁ := by
  have hL0 : 0 < L := by linarith
  unfold OmB
  by_cases h2 : ℓ₂ < L
  · rw [if_pos h2, if_pos (lt_of_le_of_lt h12 h2)]
  rw [if_neg h2]
  push_neg at h2
  have hs2 : 10000 ≤ √ℓ₂ := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  by_cases h1 : ℓ₁ < L
  · rw [if_pos h1]
    have e1 : Real.exp (-(0.99 * (ℓ₂ / L - 1))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 1 ≤ ℓ₂ / L := by rw [le_div_iff₀ hL0]; linarith
      nlinarith
    have e2 : Real.exp (-(√ℓ₂ / 2)) ≤ 1 / (1 + √ℓ₂ / 2) := exp_neg_le_inv (by positivity)
    have e3 : 1 / (1 + √ℓ₂ / 2) ≤ 0.1 :=
      by rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  · rw [if_neg h1]
    push_neg at h1
    have a1 : Real.exp (-(0.99 * (ℓ₂ / L - 1))) ≤ Real.exp (-(0.99 * (ℓ₁ / L - 1))) := by
      apply Real.exp_le_exp.mpr
      have : ℓ₁ / L ≤ ℓ₂ / L := div_le_div_of_nonneg_right h12 hL0.le
      linarith
    have a2 : Real.exp (-(√ℓ₂ / 2)) ≤ Real.exp (-(√ℓ₁ / 2)) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_le_sqrt h12
      linarith
    linarith

end LemS

namespace BeurlingSystem

variable {P : BeurlingSystem}

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- `ω_y(v) ≤ OmB (log 3v) (log(y/2v))`. -/
theorem omega_le_OmB (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {y : ℝ}
    (hy : 0 < y) (hZ : y / v ≤ Z) :
    P.omegaW t y v ≤ LemS.OmB (Real.log (3 * v)) (Real.log (y / (2 * v))) := by
  set L := Real.log (3 * v) with hLdef
  set ℓ := Real.log (y / (2 * v)) with hℓdef
  have hL0 : 0 < L := by linarith
  unfold LemS.OmB
  by_cases h1 : ℓ < L
  · rw [if_pos h1]; exact lemS_i h t hv hZ
  rw [if_neg h1]
  push_neg at h1
  have hp1 := (Real.exp_pos (-(0.99 * (ℓ / L - 1)))).le
  have hp2 := (Real.exp_pos (-(√ℓ / 2))).le
  by_cases h2 : ℓ ≤ L ^ 2
  · have hu1 : 1 ≤ uY y v := by
      show 1 ≤ ℓ / L
      rw [le_div_iff₀ hL0]; linarith
    have hu2 : uY y v ≤ L := by
      show ℓ / L ≤ L
      rw [div_le_iff₀ hL0]; nlinarith
    have := omega_le_mid h hd hv hL hy hu1 hu2 hZ
    have e : uY y v = ℓ / L := rfl
    rw [e] at this
    linarith
  · push_neg at h2
    have := omega_le_far h hd hv hL hy h2 hZ
    linarith

/-- The supremum over a dyadic block `[Y, 2Y)` is at most the majorant at its left end. -/
theorem iSup_omega_le (h : P.HBS X0m Z η1 η2 ε1) {t : ℕ → ℝ} {v : ℝ}
    (hd : P.DecidedSmall t v) (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) {Y : ℝ}
    (hY : 0 < Y) (hZ : 2 * Y ≤ v * Z) :
    (⨆ y : Set.Ico Y (2 * Y), P.omegaW t y v) ≤
      LemS.OmB (Real.log (3 * v)) (Real.log (Y / (2 * v))) := by
  haveI : Nonempty (Set.Ico Y (2 * Y)) := ⟨⟨Y, le_rfl, by linarith⟩⟩
  refine ciSup_le fun y => ?_
  obtain ⟨y, hy1, hy2⟩ := y
  have hy0 : 0 < y := by linarith
  have hyZ : y / v ≤ Z := by
    rw [div_le_iff₀ hv]; linarith
  refine (omega_le_OmB h hd hv hL hy0 hyZ).trans (LemS.OmB_anti hL ?_)
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hy1 (by positivity))

end HBS

end BeurlingSystem

namespace LemS

/-- `ℓ_k = log(2^k/2v) = k log 2 - log 2v`. -/
lemma log_pow_div {v : ℝ} (hv : 0 < v) (k : ℕ) :
    Real.log ((2 : ℝ) ^ k / (2 * v)) = k * Real.log 2 - Real.log (2 * v) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]

lemma log2_bounds : 0.6931 < Real.log 2 ∧ Real.log 2 < 0.6932 := by
  constructor
  · have := Real.log_two_gt_d9; linarith
  · have := Real.log_two_lt_d9; linarith

/-- **Part A**: the levels `ℓ_k < L` (with `2^k ≥ v`) contribute at most `3L²`. -/
lemma partA_le {v : ℝ} (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) (K : Finset ℕ)
    (hK : ∀ k ∈ K, v ≤ (2 : ℝ) ^ k ∧ Real.log ((2 : ℝ) ^ k / (2 * v)) < Real.log (3 * v)) :
    ∑ k ∈ K, ((k : ℝ) + 1) * Real.log 2 ≤ 3 * Real.log (3 * v) ^ 2 := by
  set L := Real.log (3 * v) with hLdef
  obtain ⟨hl2a, hl2b⟩ := log2_bounds
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hc : Real.log (2 * v) ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hlv : Real.log v = L - Real.log 3 := by
    rw [hLdef, Real.log_mul (by norm_num) hv.ne']; ring
  rcases K.eq_empty_or_nonempty with hE | hne
  · rw [hE]; simp; positivity
  set a := ⌈(L - Real.log 3) / Real.log 2⌉₊
  set b := ⌊2 * L / Real.log 2⌋₊
  have hsub : K ⊆ Finset.Icc a b := by
    intro k hk
    obtain ⟨h1, h2⟩ := hK k hk
    rw [Finset.mem_Icc]
    have hkl : Real.log v ≤ k * Real.log 2 := by
      rw [← Real.log_pow]; exact Real.log_le_log hv h1
    rw [log_pow_div hv] at h2
    constructor
    · apply Nat.ceil_le.mpr
      rw [div_le_iff₀ (by linarith)]; linarith
    · apply Nat.le_floor
      rw [le_div_iff₀ (by linarith)]; linarith
  have hterm : ∀ k ∈ K, ((k : ℝ) + 1) * Real.log 2 ≤ 2 * L + 0.7 := by
    intro k hk
    have h2 := (hK k hk).2
    rw [log_pow_div hv] at h2
    nlinarith
  have hab : a ≤ b := by
    obtain ⟨k, hk⟩ := hne
    have := Finset.mem_Icc.mp (hsub hk); omega
  have hcard : (K.card : ℝ) ≤ (L + 2) / Real.log 2 + 1 := by
    have h1 : K.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hb : (b : ℝ) ≤ 2 * L / Real.log 2 := Nat.floor_le (by positivity)
    have ha : (L - Real.log 3) / Real.log 2 ≤ a := Nat.le_ceil _
    have : (K.card : ℝ) ≤ (b : ℝ) + 1 - a := by rw [← h2]; exact_mod_cast h1
    have e : 2 * L / Real.log 2 - (L - Real.log 3) / Real.log 2 =
        (L + Real.log 3) / Real.log 2 := by
      field_simp; ring
    have : (L + Real.log 3) / Real.log 2 ≤ (L + 2) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  calc ∑ k ∈ K, ((k : ℝ) + 1) * Real.log 2 ≤ ∑ _k ∈ K, (2 * L + 0.7) := Finset.sum_le_sum hterm
    _ = K.card * (2 * L + 0.7) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((L + 2) / Real.log 2 + 1) * (2 * L + 0.7) :=
        mul_le_mul_of_nonneg_right hcard (by linarith)
    _ ≤ 3 * L ^ 2 := by
        have hinv : (L + 2) / Real.log 2 ≤ 1.4428 * (L + 2) := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        nlinarith

/-- `ℓ e^{-√ℓ/2} ≤ 46080/ℓ²` for `ℓ > 0`. -/
lemma mul_exp_neg_sqrt_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ * Real.exp (-(√ℓ / 2)) ≤ 46080 / ℓ ^ 2 := by
  have hs : 0 ≤ √ℓ / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (x := √ℓ / 2) hs 6
  have hss : √ℓ * √ℓ = ℓ := Real.mul_self_sqrt hℓ.le
  have h6 : (√ℓ / 2) ^ 6 = ℓ ^ 3 / 64 := by
    have : (√ℓ / 2) ^ 6 = (√ℓ * √ℓ) ^ 3 / 64 := by ring
    rw [this, hss]
  rw [h6, show (6 : ℕ).factorial = 720 by rfl] at h
  push_cast at h
  have hE := Real.exp_pos (√ℓ / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Part B**: the levels `ℓ_k ≥ L` contribute at most `3.2 L² + 1`. -/
lemma partB_le {v : ℝ} (hv : 0 < v) (hL : 100000000 ≤ Real.log (3 * v)) (K : Finset ℕ)
    (hK : ∀ k ∈ K, Real.log (3 * v) ≤ Real.log ((2 : ℝ) ^ k / (2 * v))) :
    ∑ k ∈ K, ((k : ℝ) + 1) * Real.log 2 *
        (0.71 * Real.exp (-(0.99 * (Real.log ((2 : ℝ) ^ k / (2 * v)) / Real.log (3 * v) - 1)))
          + 2 * Real.exp (-(√(Real.log ((2 : ℝ) ^ k / (2 * v))) / 2))) ≤
      3.2 * Real.log (3 * v) ^ 2 + 1 := by
  set L := Real.log (3 * v) with hLdef
  set c := Real.log (2 * v) with hcdef
  obtain ⟨hl2a, hl2b⟩ := log2_bounds
  have hL0 : 0 < L := by linarith
  have hcL : c + Real.log 2 ≤ 1.01 * L := by
    have e : c + Real.log 2 = L + Real.log (4 / 3) := by
      rw [hcdef, hLdef, ← Real.log_mul (by positivity) (by norm_num),
        ← Real.log_mul (by positivity) (by norm_num)]
      congr 1; ring
    have : Real.log (4 / 3) ≤ 4 / 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hcL' : L - 1 ≤ c := by
    have e : c = L - Real.log (3 / 2) := by
      rw [hcdef, hLdef, ← Real.log_div (by positivity) (by norm_num)]
      congr 1; ring
    have : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  rcases K.eq_empty_or_nonempty with hE | hne
  · rw [hE]; simp; positivity
  set kB := K.min' hne
  set M := K.max' hne - kB + 1
  set ℓ0 := (kB : ℝ) * Real.log 2 - c
  have hℓ0 : L ≤ ℓ0 := by
    have := hK kB (K.min'_mem hne); rwa [log_pow_div hv] at this
  have hℓm : ∀ m : ℕ, ((kB + m : ℕ) : ℝ) * Real.log 2 - c = ℓ0 + m * Real.log 2 := by
    intro m; push_cast; ring
  -- the generic term
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) * Real.log 2 *
      (0.71 * Real.exp (-(0.99 * (((k : ℝ) * Real.log 2 - c) / L - 1)))
        + 2 * Real.exp (-(√((k : ℝ) * Real.log 2 - c) / 2))) with hF
  have hFnn : ∀ k, 0 ≤ F k := fun k => by
    simp only [hF]; positivity
  have hsum_eq : ∑ k ∈ K, ((k : ℝ) + 1) * Real.log 2 *
        (0.71 * Real.exp (-(0.99 * (Real.log ((2 : ℝ) ^ k / (2 * v)) / L - 1)))
          + 2 * Real.exp (-(√(Real.log ((2 : ℝ) ^ k / (2 * v))) / 2))) = ∑ k ∈ K, F k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, log_pow_div hv]
    rfl
  rw [hsum_eq]
  have hshift := LemS.sum_le_shift K kB M (fun k hk => ⟨K.min'_le k hk, by
    have := K.le_max' k hk; omega⟩) F hFnn
  refine hshift.trans ?_
  -- split the two pieces
  set Δ := Real.log 2 / L with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔs : Δ ≤ 0.00000001 := by
    rw [hΔ, div_le_iff₀ hL0]; nlinarith
  set x0 := ℓ0 / L with hx0
  have hx01 : 1 ≤ x0 := by rw [hx0, le_div_iff₀ hL0]; linarith
  set q := Real.exp (-(0.99 * Δ)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; nlinarith
  have h1q : 0.98 * Δ ≤ 1 - q := by
    have := one_sub_exp_neg_ge (t := 0.99 * Δ) (by positivity)
    have e : 0.98 * Δ ≤ 0.99 * Δ / (1 + 0.99 * Δ) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hE0 : Real.exp (-(0.99 * (x0 - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hE1 : (x0 + 1.01) * Real.exp (-(0.99 * (x0 - 1))) ≤ 2.01 := by
    have hb := Real.add_one_le_exp (0.99 * (x0 - 1))
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  -- the pieces at `m`
  have hF1 : ∀ m ∈ Finset.range M, F (kB + m) ≤
      0.71 * L * (2.01 * q ^ m + Δ * ((m : ℝ) * q ^ m)) +
        4.02 * (46080 / (ℓ0 + m * Real.log 2) ^ 2) := by
    intro m _
    have hlm := hℓm m
    set ℓm := ℓ0 + m * Real.log 2 with hℓmdef
    have hℓm0 : L ≤ ℓm := by
      have : 0 ≤ (m : ℝ) * Real.log 2 := by positivity
      linarith
    have hk1 : (((kB + m : ℕ) : ℝ) + 1) * Real.log 2 = ℓm + (c + Real.log 2) := by
      rw [← hlm]; ring
    have hexp : Real.exp (-(0.99 * (ℓm / L - 1))) =
        Real.exp (-(0.99 * (x0 - 1))) * q ^ m := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [hℓmdef, hx0, hΔ]; field_simp; ring
    simp only [hF]
    rw [hlm, hk1, hexp]
    have hpos1 : 0 ≤ ℓm + (c + Real.log 2) := by linarith
    have hq_m : 0 ≤ q ^ m := pow_nonneg hq0 m
    -- first piece
    have A1 : (ℓm + (c + Real.log 2)) * (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m)) ≤
        0.71 * L * (2.01 * q ^ m + Δ * ((m : ℝ) * q ^ m)) := by
      have e1 : ℓm + (c + Real.log 2) ≤ L * (x0 + 1.01 + m * Δ) := by
        have : L * (x0 + 1.01 + m * Δ) = ℓ0 + 1.01 * L + m * Real.log 2 := by
          rw [hx0, hΔ]; field_simp
        rw [this, hℓmdef]; linarith
      have hE := (Real.exp_pos (-(0.99 * (x0 - 1)))).le
      calc (ℓm + (c + Real.log 2)) * (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m))
          ≤ L * (x0 + 1.01 + m * Δ) * (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m)) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = 0.71 * L * ((x0 + 1.01) * Real.exp (-(0.99 * (x0 - 1))) * q ^ m +
            Δ * ((m : ℝ) * q ^ m) * Real.exp (-(0.99 * (x0 - 1)))) := by ring
        _ ≤ 0.71 * L * (2.01 * q ^ m + Δ * ((m : ℝ) * q ^ m) * 1) := by
            gcongr
        _ = _ := by ring
    -- second piece
    have A2 : (ℓm + (c + Real.log 2)) * (2 * Real.exp (-(√ℓm / 2))) ≤
        4.02 * (46080 / ℓm ^ 2) := by
      have hb := mul_exp_neg_sqrt_le (ℓ := ℓm) (by linarith)
      have e2 : ℓm + (c + Real.log 2) ≤ 2.01 * ℓm := by linarith
      have hE := (Real.exp_pos (-(√ℓm / 2))).le
      calc (ℓm + (c + Real.log 2)) * (2 * Real.exp (-(√ℓm / 2)))
          ≤ 2.01 * ℓm * (2 * Real.exp (-(√ℓm / 2))) :=
            mul_le_mul_of_nonneg_right e2 (by positivity)
        _ = 4.02 * (ℓm * Real.exp (-(√ℓm / 2))) := by ring
        _ ≤ 4.02 * (46080 / ℓm ^ 2) := by gcongr
    have : (ℓm + (c + Real.log 2)) *
        (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m) + 2 * Real.exp (-(√ℓm / 2))) =
        (ℓm + (c + Real.log 2)) * (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m)) +
        (ℓm + (c + Real.log 2)) * (2 * Real.exp (-(√ℓm / 2))) := by ring
    rw [show ((ℓm + (c + Real.log 2)) *
        (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m) + 2 * Real.exp (-(√ℓm / 2)))) =
        (ℓm + (c + Real.log 2)) *
        (0.71 * (Real.exp (-(0.99 * (x0 - 1))) * q ^ m) + 2 * Real.exp (-(√ℓm / 2))) from rfl]
    rw [this]
    linarith
  refine (Finset.sum_le_sum hF1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have g1 := sum_geom_le hq0 hq1 M
  have g2 := sum_mul_geom_le hq0 hq1 M
  have g3 := sum_inv_sq_le (a := ℓ0) (b := Real.log 2) (by linarith) (by linarith) M
  have hg3 : ∑ m ∈ Finset.range M, 46080 / (ℓ0 + m * Real.log 2) ^ 2 ≤
      46080 * (1 / ℓ0 ^ 2 + 1 / (ℓ0 * Real.log 2)) := by
    rw [show (∑ m ∈ Finset.range M, 46080 / (ℓ0 + m * Real.log 2) ^ 2) =
      46080 * ∑ m ∈ Finset.range M, 1 / (ℓ0 + m * Real.log 2) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring]
    exact mul_le_mul_of_nonneg_left g3 (by norm_num)
  -- numerical assembly
  have hA : 2.01 / (1 - q) ≤ 2.01 / (0.98 * Δ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h1q
  have hB : q / (1 - q) ^ 2 ≤ 1 / (0.98 * Δ) ^ 2 := by
    apply div_le_div₀ (by norm_num) hq1.le (by positivity)
    exact pow_le_pow_left₀ (by positivity) h1q 2
  have hlinv : L / Real.log 2 ≤ 1.4428 * L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hΔinv : 1 / Δ = L / Real.log 2 := by rw [hΔ]; field_simp
  have hpart1 : 0.71 * L * (2.01 * ∑ m ∈ Finset.range M, q ^ m +
      Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m) ≤ 3.2 * L ^ 2 := by
    have s1 : 2.01 * ∑ m ∈ Finset.range M, q ^ m ≤ 2.01 / (0.98 * Δ) := by
      have := mul_le_mul_of_nonneg_left g1 (show (0 : ℝ) ≤ 2.01 by norm_num)
      have e : 2.01 * (1 / (1 - q)) = 2.01 / (1 - q) := by ring
      linarith
    have s2 : Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m ≤ Δ * (1 / (0.98 * Δ) ^ 2) :=
      mul_le_mul_of_nonneg_left (g2.trans hB) hΔ0.le
    have e1 : 2.01 / (0.98 * Δ) = 2.01 / 0.98 * (1 / Δ) := by field_simp
    have e2 : Δ * (1 / (0.98 * Δ) ^ 2) = 1 / 0.9604 * (1 / Δ) := by field_simp; ring
    rw [e1, hΔinv] at s1
    rw [e2, hΔinv] at s2
    have : 2.01 * ∑ m ∈ Finset.range M, q ^ m + Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m ≤
        (2.01 / 0.98 + 1 / 0.9604) * (1.4428 * L) := by nlinarith
    have hL2 : 0 ≤ 0.71 * L := by positivity
    calc 0.71 * L * (2.01 * ∑ m ∈ Finset.range M, q ^ m +
          Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m)
        ≤ 0.71 * L * ((2.01 / 0.98 + 1 / 0.9604) * (1.4428 * L)) :=
          mul_le_mul_of_nonneg_left this hL2
      _ ≤ 3.2 * L ^ 2 := by nlinarith
  have hpart2 : 4.02 * (46080 * (1 / ℓ0 ^ 2 + 1 / (ℓ0 * Real.log 2))) ≤ 1 := by
    have h1 : 1 / ℓ0 ^ 2 ≤ 1 / 10000000000000000 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    have h2 : 1 / (ℓ0 * Real.log 2) ≤ 1 / 60000000 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    nlinarith
  have : 0.71 * L * (2.01 * ∑ m ∈ Finset.range M, q ^ m +
      Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m) =
      0.71 * L * (2.01 * ∑ m ∈ Finset.range M, q ^ m) +
        0.71 * L * (Δ * ∑ m ∈ Finset.range M, (m : ℝ) * q ^ m) := by ring
  nlinarith

end LemS

end
