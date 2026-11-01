module

public import RequestProject.Beurling.RankFull.RowAdm
public import RequestProject.Beurling.SmoothTailsCert

/-!
# Lemma 6.22(d): low-degree rows with smooth tails

The (s4) data of a row of `R` of degree in `[1, K]` are its monomial `v` in the `π` labels and
its `X₀`-smooth tail `d`, with `M_v(τ) d ≤ Y = 2z + 1` (`admDick`).

* `RankFull.card_admDick_le` : **Lemma 6.22(a)** with smooth tails:
  `#admDick ≤ ∑_{k=1}^{K} C(π + k - 1, k) Ψ(Y/Xm^k, X₀)` when all label values are `≥ Xm`.
* `RankFull.dickman_sum_le` : **Lemma 6.22(d)**: with `Λ = log X₀ ≥ 10⁸`,
  `Λ - e^{-0.98Λ} ≤ log Xm ≤ Λ`, `z ≥ X₀`, `D = log(2z+1)/log Xm`, `u₁ = max(10⁴, log Λ)`,
  `2u₁ ≤ D - 1`, `D ≤ X₀^{0.3}` and `π Xm^{-1} (eD)^{0.9} ≤ 1/3`,
  `z⁻¹ ∑_{k=1}^{K} C(π + k - 1, k) Ψ((2z+1)/Xm^k, X₀) ≤ e^{-g}`,
  `g = log Xm - log(3π) + 0.9 (D-1) log(D-1) - e^{-0.4Λ}`.

  **Additional hypothesis** (used implicitly in the paper's proof, "far less than 1/3"):
  `π e^{0.9 (u₁+1) log(u₁+1)} ≤ Xm/3`. It controls the ratio at the first term with `u < u₁`;
  it holds in every use (Steps 3–4 of Theorem 6.23, where `π ≤ L² ≤ X₀^{0.6}`).
-/

@[expose] public section

open Finset

namespace RankFull

lemma smoothCount_mono' (X₀ : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    Rankin.smoothCount X₀ x ≤ Rankin.smoothCount X₀ y := by
  unfold Rankin.smoothCount
  apply Finset.card_le_card
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans (Nat.floor_le_floor hxy), hn.2⟩

lemma smoothCount_le_self (X₀ : ℕ) {x : ℝ} (hx : 0 ≤ x) : (Rankin.smoothCount X₀ x : ℝ) ≤ x := by
  unfold Rankin.smoothCount
  have : (Nat.smoothNumbersUpTo ⌊x⌋₊ X₀).card ≤ ⌊x⌋₊ := by
    have hsub : Nat.smoothNumbersUpTo ⌊x⌋₊ X₀ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
      intro n hn
      rw [Nat.mem_smoothNumbersUpTo] at hn
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn.2.1, hn.1⟩
    have := Finset.card_le_card hsub
    simpa using this
  exact (Nat.cast_le.mpr this).trans (Nat.floor_le hx)

/-- The admissible (s4) data of a row of degree in `[1, K]` with `X₀`-smooth tail. -/
noncomputable def admDick (π K X₀ : ℕ) (τl : Fin π → ℝ) (Y : ℝ) :
    Finset ((Fin π → ℕ) × ℕ) := by
  classical exact (((Icc 1 K).biUnion (Finset.Nat.antidiagonalTuple π)) ×ˢ
    Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter fun p => monoVal τl p.1 * p.2 ≤ Y

lemma monoVal_ge {π k : ℕ} {τl : Fin π → ℝ} {Xm : ℝ} (hXm : 0 < Xm) (hτl : ∀ i, Xm ≤ τl i)
    {v : Fin π → ℕ} (hv : ∑ i, v i = k) : Xm ^ k ≤ monoVal τl v := by
  unfold monoVal
  rw [← hv, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg hXm.le _)
    fun i _ => pow_le_pow_left₀ hXm.le (hτl i) _

/-- **Lemma 6.22(a)**, smooth tails: `#admDick ≤ ∑_{k=1}^{K} C(π+k-1, k) Ψ(Y/Xm^k, X₀)`. -/
theorem card_admDick_le {π K X₀ : ℕ} {Xm Y : ℝ} (hXm : 0 < Xm) (hY : 0 ≤ Y) {τl : Fin π → ℝ}
    (hτl : ∀ i, Xm ≤ τl i) :
    ((admDick π K X₀ τl Y).card : ℝ) ≤
      ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) * Rankin.smoothCount X₀ (Y / Xm ^ k) := by
  classical
  set V := (Icc 1 K).biUnion (Finset.Nat.antidiagonalTuple π)
  have hfib : (admDick π K X₀ τl Y).card = ∑ v ∈ V, ((Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter
      fun d : ℕ => monoVal τl v * (d : ℝ) ≤ Y).card := by
    unfold admDick
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm
  have hv : ∀ k ∈ Icc 1 K, ∀ v ∈ Finset.Nat.antidiagonalTuple π k,
      (((Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter fun d : ℕ => monoVal τl v * (d : ℝ) ≤ Y).card : ℝ) ≤
        Rankin.smoothCount X₀ (Y / Xm ^ k) := by
    intro k _ v hvk
    have hM := monoVal_ge hXm hτl (Finset.Nat.mem_antidiagonalTuple.mp hvk)
    have hM0 : 0 < monoVal τl v := lt_of_lt_of_le (pow_pos hXm k) hM
    have hsub : ((Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter fun d : ℕ => monoVal τl v * (d : ℝ) ≤ Y) ⊆
        Nat.smoothNumbersUpTo ⌊Y / monoVal τl v⌋₊ X₀ := by
      intro d hd
      obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
      rw [Nat.mem_smoothNumbersUpTo] at hd1 ⊢
      refine ⟨Nat.le_floor ?_, hd1.2⟩
      rw [le_div_iff₀ hM0]; linarith
    have h1 := Finset.card_le_card hsub
    have h2 := smoothCount_mono' X₀ (div_le_div_of_nonneg_left hY (pow_pos hXm k) hM)
    unfold Rankin.smoothCount at h2
    exact_mod_cast h1.trans h2
  rw [hfib]
  push_cast
  rw [Finset.sum_biUnion]
  · refine Finset.sum_le_sum fun k hk => ?_
    calc ∑ v ∈ Finset.Nat.antidiagonalTuple π k,
          (((Nat.smoothNumbersUpTo ⌊Y⌋₊ X₀).filter fun d : ℕ =>
            monoVal τl v * (d : ℝ) ≤ Y).card : ℝ)
        ≤ ∑ _v ∈ Finset.Nat.antidiagonalTuple π k, (Rankin.smoothCount X₀ (Y / Xm ^ k) : ℝ) :=
          Finset.sum_le_sum (hv k hk)
      _ = _ := by rw [Finset.sum_const, RowWeights.card_rows_of_degree, nsmul_eq_mul]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hva hvb
    rw [Finset.Nat.mem_antidiagonalTuple] at hva hvb
    exact hab (hva.symm.trans hvb)

/-- `a log a - b log b ≤ (a - b)(1 + log a)` for `0 < b ≤ a`. -/
lemma xlogx_sub_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    a * Real.log a - b * Real.log b ≤ (a - b) * (1 + Real.log a) := by
  have ha : 0 < a := hb.trans_le hab
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have : b * (Real.log a - Real.log b) ≤ b * (a / b - 1) := mul_le_mul_of_nonneg_left h hb.le
  have e : b * (a / b - 1) = a - b := by field_simp
  nlinarith

lemma xlogx_mono {a b : ℝ} (hb : 1 ≤ b) (hab : b ≤ a) : b * Real.log b ≤ a * Real.log a := by
  have h1 : Real.log b ≤ Real.log a := Real.log_le_log (by linarith) hab
  have h2 : 0 ≤ Real.log b := Real.log_nonneg hb
  nlinarith

/-- `log(0.3Λ) ≤ 0.01Λ` for `Λ ≥ 10⁸`. -/
lemma log_small {Λ : ℝ} (hΛ : 10 ^ 8 ≤ Λ) : Real.log (0.3 * Λ) ≤ 0.01 * Λ := by
  have h := Real.log_le_sub_one_of_pos (x := 0.3 * Λ / 1000) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  have h1000 : Real.log 1000 ≤ 7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (7 : ℝ)
    have : (1000 : ℝ) ≤ Real.exp 7 := by
      have h2 := Real.sum_le_exp_of_nonneg (x := (7 : ℝ)) (by norm_num) 16
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      linarith
    exact this
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 6.22(d)** (low degree, smooth tails). See the module docstring for the additional
hypothesis `hπu`. -/
theorem dickman_sum_le {X₀ : ℕ} (hX₀ : 3 ≤ X₀) (hΛ : 10 ^ 8 ≤ Real.log X₀) {Xm z : ℝ}
    (hXm0 : 0 < Xm) (hXmlo : Real.log X₀ - Real.exp (-0.98 * Real.log X₀) ≤ Real.log Xm)
    (hXmhi : Real.log Xm ≤ Real.log X₀) (hz : (X₀ : ℝ) ≤ z) {π K : ℕ} (hπ : 1 ≤ π)
    (hD1 : 2 * max (10 ^ 4) (Real.log (Real.log X₀)) ≤ Real.log (2 * z + 1) / Real.log Xm - 1)
    (hD2 : Real.log (2 * z + 1) / Real.log Xm ≤ Real.exp (0.3 * Real.log X₀))
    (hπD : π * Xm⁻¹ * (Real.exp 1 * (Real.log (2 * z + 1) / Real.log Xm)) ^ (0.9 : ℝ) ≤ 1 / 3)
    (hπu : π * Real.exp (0.9 * ((max (10 ^ 4) (Real.log (Real.log X₀)) + 1) *
      Real.log (max (10 ^ 4) (Real.log (Real.log X₀)) + 1))) ≤ Xm / 3) :
    z⁻¹ * ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) *
        Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) ≤
      Real.exp (-(Real.log Xm - Real.log (3 * π) +
        0.9 * ((Real.log (2 * z + 1) / Real.log Xm - 1) *
          Real.log (Real.log (2 * z + 1) / Real.log Xm - 1)) - Real.exp (-0.4 * Real.log X₀))) := by
  set Λ := Real.log X₀ with hΛdef
  set D := Real.log (2 * z + 1) / Real.log Xm with hDdef
  set u₁ := max (10 ^ 4 : ℝ) (Real.log Λ) with hu₁
  set f : ℝ → ℝ := fun u => u * Real.log u with hf
  have hΛ0 : 0 < Λ := by linarith
  have hX0pos : (0 : ℝ) < X₀ := by exact_mod_cast (by omega : 0 < X₀)
  have hz0 : 0 < z := by linarith
  have hlXm : Λ / 2 ≤ Real.log Xm := by
    have : Real.exp (-0.98 * Λ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hlXm0 : 0 < Real.log Xm := by linarith
  have hu₁4 : 10 ^ 4 ≤ u₁ := le_max_left _ _
  have hu₁Λ : Real.log Λ ≤ u₁ := le_max_right _ _
  set ρ := Real.log Xm / Λ with hρ
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hΛ0]; exact hXmhi
  have hρ2 : 1 / 2 ≤ ρ := by rw [hρ, le_div_iff₀ hΛ0]; linarith
  have hYk : ∀ k : ℕ, 0 < (2 * z + 1) / Xm ^ k := fun k => by positivity
  have hlogY : ∀ k : ℕ, Real.log ((2 * z + 1) / Xm ^ k) / Λ = (D - k) * ρ := by
    intro k
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, hρ, hDdef]
    field_simp
  set u : ℕ → ℝ := fun k => (D - k) * ρ with hu
  set E : ℕ → ℝ := fun k => if u₁ ≤ u k then Real.exp (-0.9 * f (u k)) else 1 with hE
  set B : ℕ → ℝ := fun k =>
    ((π + k - 1).choose k : ℝ) * ((2 * z + 1) / Xm ^ k / z) * E k with hB
  -- Step A: each term is at most `B k`
  have hstepA : ∀ k : ℕ, ((π + k - 1).choose k : ℝ) *
      Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) / z ≤ B k := by
    intro k
    have hΨ : (Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) : ℝ) ≤
        (2 * z + 1) / Xm ^ k * E k := by
      by_cases hk : u₁ ≤ u k
      · simp only [hE, if_pos hk]
        have huk : Real.log ((2 * z + 1) / Xm ^ k) / Real.log X₀ = u k := hlogY k
        have hukD : u k ≤ D := by
          simp only [hu]
          have : (D - k) * ρ ≤ D - k := mul_le_of_le_one_right (by
            have : 0 ≤ u k := by linarith
            simp only [hu] at this
            by_contra h; push_neg at h; nlinarith) hρ1
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        have hσ : 0.69 ≤ 1 - Real.log (u k * Real.log (u k)) / Real.log X₀ := by
          have hu0 : 0 < u k := by linarith
          have hlu : 0 < Real.log (u k) := Real.log_pos (by linarith)
          have h1 : Real.log (u k) ≤ 0.3 * Λ := by
            rw [Real.log_le_iff_le_exp hu0]; exact hukD.trans hD2
          have h2 : Real.log (Real.log (u k)) ≤ Real.log (0.3 * Λ) :=
            Real.log_le_log hlu h1
          have h3 := log_small hΛ
          rw [Real.log_mul hu0.ne' hlu.ne']
          rw [← hΛdef]
          have : (Real.log (u k) + Real.log (Real.log (u k))) / Λ ≤ 0.31 := by
            rw [div_le_iff₀ hΛ0]; linarith
          linarith
        have := SmoothTails.smooth_tail_rankin_cert hX₀ (hYk k) (by rw [huk]; linarith)
          (by rw [huk]; linarith) (by rw [huk]; exact hσ)
        rw [huk] at this
        simpa [hf] using this
      · simp only [hE, if_neg hk, mul_one]
        exact smoothCount_le_self X₀ (hYk k).le
    simp only [hB]
    rw [mul_div_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [div_le_iff₀ hz0]
    calc (Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) : ℝ) ≤ (2 * z + 1) / Xm ^ k * E k := hΨ
      _ = (2 * z + 1) / Xm ^ k / z * E k * z := by field_simp
  -- Step B: ratio `B (k+1) ≤ B k / 3`
  have hE0 : ∀ k, 0 < E k := fun k => by simp only [hE]; split_ifs <;> positivity
  have hXm1 : 1 ≤ Xm := by
    rw [← Real.exp_log hXm0]; exact Real.one_le_exp (by linarith)
  have hπXm : (π : ℝ) / Xm ≤ 1 / 3 := by
    have hD1' : 1 ≤ Real.exp 1 * D := by
      have : 1 ≤ D := by linarith
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have : 1 ≤ (Real.exp 1 * D) ^ (0.9 : ℝ) := Real.one_le_rpow hD1' (by norm_num)
    calc (π : ℝ) / Xm = π * Xm⁻¹ * 1 := by ring
      _ ≤ π * Xm⁻¹ * (Real.exp 1 * D) ^ (0.9 : ℝ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 1 / 3 := hπD
  have hstepB : ∀ k, 1 ≤ k → B (k + 1) ≤ B k / 3 := by
    intro k hk
    have hch : ((π + (k + 1) - 1).choose (k + 1) : ℝ) ≤ π * ((π + k - 1).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (π + k - 1) k
      have e : π + k - 1 + 1 = π + (k + 1) - 1 := by omega
      rw [e] at h
      have hc : ((π + (k + 1) - 1 : ℕ) : ℝ) = π + k := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have h' : ((π + (k + 1) - 1).choose (k + 1) : ℝ) * (k + 1) =
          (π + k : ℝ) * ((π + k - 1).choose k : ℝ) := by
        rw [← hc]; exact_mod_cast h.symm
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      have hπk : (π : ℝ) + k ≤ π * (k + 1) := by
        have : (1 : ℝ) ≤ π := by exact_mod_cast hπ
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      have h0 : (0 : ℝ) ≤ ((π + k - 1).choose k : ℝ) := Nat.cast_nonneg _
      have : ((π + (k + 1) - 1).choose (k + 1) : ℝ) * (k + 1) ≤
          π * ((π + k - 1).choose k : ℝ) * (k + 1) := by
        rw [h']; nlinarith
      exact le_of_mul_le_mul_right this hk1
    have hY : (2 * z + 1) / Xm ^ (k + 1) / z = (2 * z + 1) / Xm ^ k / z / Xm := by
      rw [pow_succ]; field_simp
    have huk : u (k + 1) = u k - ρ := by simp only [hu]; push_cast; ring
    -- the ratio of the `E`s
    have hEr : E (k + 1) ≤ E k * max ((Real.exp 1 * D) ^ (0.9 : ℝ))
        (Real.exp (0.9 * f (u₁ + 1))) := by
      by_cases h1 : u₁ ≤ u (k + 1)
      · have h0 : u₁ ≤ u k := by linarith
        simp only [hE, if_pos h1, if_pos h0]
        have hd : f (u k) - f (u (k + 1)) ≤ 1 + Real.log D := by
          have hb : 0 < u (k + 1) := by linarith
          have := xlogx_sub_le hb (by linarith : u (k + 1) ≤ u k)
          have hukD : u k ≤ D := by
            simp only [hu]
            have hDk : 0 ≤ D - k := by
              by_contra h; push_neg at h
              have : u k < 0 := by simp only [hu]; nlinarith
              linarith
            have : (D - k) * ρ ≤ D - k := mul_le_of_le_one_right hDk hρ1
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith
          have hl : Real.log (u k) ≤ Real.log D := Real.log_le_log (by linarith) hukD
          have h1l : 0 ≤ 1 + Real.log (u k) := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ u k by linarith); linarith
          simp only [hf]
          calc u k * Real.log (u k) - u (k + 1) * Real.log (u (k + 1))
              ≤ (u k - u (k + 1)) * (1 + Real.log (u k)) := this
            _ ≤ 1 * (1 + Real.log (u k)) := by
                apply mul_le_mul_of_nonneg_right _ h1l; rw [huk]; linarith
            _ ≤ 1 + Real.log D := by linarith
        have hD0 : 0 < D := by linarith
        have hrp : (Real.exp 1 * D) ^ (0.9 : ℝ) = Real.exp (0.9 * (1 + Real.log D)) := by
          rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) hD0.ne',
            Real.log_exp]; ring_nf
        calc Real.exp (-0.9 * f (u (k + 1)))
            = Real.exp (-0.9 * f (u k)) * Real.exp (0.9 * (f (u k) - f (u (k + 1)))) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp (-0.9 * f (u k)) * (Real.exp 1 * D) ^ (0.9 : ℝ) := by
              rw [hrp]
              exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
                (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
      · simp only [hE, if_neg h1]
        by_cases h0 : u₁ ≤ u k
        · simp only [if_pos h0]
          have hlt : u k < u₁ + 1 := by rw [huk] at h1; push_neg at h1; linarith
          have hmono : f (u k) ≤ f (u₁ + 1) := by
            simp only [hf]; exact xlogx_mono (by linarith) hlt.le
          calc (1 : ℝ) = Real.exp (-0.9 * f (u k)) * Real.exp (0.9 * f (u k)) := by
                rw [← Real.exp_add]; simp
            _ ≤ Real.exp (-0.9 * f (u k)) * Real.exp (0.9 * f (u₁ + 1)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le
        · simp only [if_neg h0, one_mul]
          exact le_trans (Real.one_le_exp (by
            have : 0 ≤ f (u₁ + 1) := by
              simp only [hf]; have := Real.log_nonneg (show (1 : ℝ) ≤ u₁ + 1 by linarith)
              positivity
            linarith)) (le_max_right _ _)
    have hmax : π * Xm⁻¹ * max ((Real.exp 1 * D) ^ (0.9 : ℝ)) (Real.exp (0.9 * f (u₁ + 1)))
        ≤ 1 / 3 := by
      rcases le_total ((Real.exp 1 * D) ^ (0.9 : ℝ)) (Real.exp (0.9 * f (u₁ + 1))) with h | h
      · rw [max_eq_right h]
        have := hπu
        rw [show π * Real.exp (0.9 * ((u₁ + 1) * Real.log (u₁ + 1))) = π * Real.exp (0.9 *
          f (u₁ + 1)) from rfl] at this
        calc (π : ℝ) * Xm⁻¹ * Real.exp (0.9 * f (u₁ + 1)) =
            (π * Real.exp (0.9 * f (u₁ + 1))) / Xm := by field_simp
          _ ≤ (Xm / 3) / Xm := div_le_div_of_nonneg_right this hXm0.le
          _ = 1 / 3 := by field_simp
      · rw [max_eq_left h]; exact hπD
    have hC0 : (0 : ℝ) ≤ ((π + k - 1).choose k : ℝ) := Nat.cast_nonneg _
    have hYk0 : 0 ≤ (2 * z + 1) / Xm ^ k / z := by positivity
    simp only [hB]
    rw [hY]
    calc ((π + (k + 1) - 1).choose (k + 1) : ℝ) * ((2 * z + 1) / Xm ^ k / z / Xm) * E (k + 1)
        ≤ (π * ((π + k - 1).choose k : ℝ)) * ((2 * z + 1) / Xm ^ k / z / Xm) *
            (E k * max ((Real.exp 1 * D) ^ (0.9 : ℝ)) (Real.exp (0.9 * f (u₁ + 1)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hch (by positivity)) hEr
            (hE0 _).le (by positivity)
      _ = ((π + k - 1).choose k : ℝ) * ((2 * z + 1) / Xm ^ k / z) * E k *
            (π * Xm⁻¹ * max ((Real.exp 1 * D) ^ (0.9 : ℝ)) (Real.exp (0.9 * f (u₁ + 1)))) := by
          ring
      _ ≤ ((π + k - 1).choose k : ℝ) * ((2 * z + 1) / Xm ^ k / z) * E k * (1 / 3) :=
          mul_le_mul_of_nonneg_left hmax (by have := hE0 k; positivity)
      _ = _ := by ring
  -- Step C: geometric sum
  have hgeo : ∀ n, B (n + 1) ≤ B 1 * (1 / 3) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc B (n + 1 + 1) ≤ B (n + 1) / 3 := hstepB (n + 1) (by omega)
        _ ≤ B 1 * (1 / 3) ^ n / 3 := by linarith
        _ = B 1 * (1 / 3) ^ (n + 1) := by ring
  have hB10 : 0 ≤ B 1 := by simp only [hB]; have := hE0 1; positivity
  have hsum : ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) *
      Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) / z ≤ 3 / 2 * B 1 := by
    calc ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) *
          Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) / z
        ≤ ∑ k ∈ Icc 1 K, B k := Finset.sum_le_sum fun k _ => hstepA k
      _ = ∑ n ∈ range K, B (n + 1) := by
          induction K with
          | zero => simp
          | succ K ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      _ ≤ ∑ n ∈ range K, B 1 * (1 / 3) ^ n := Finset.sum_le_sum fun n _ => hgeo n
      _ = B 1 * ∑ n ∈ range K, (1 / 3 : ℝ) ^ n := by rw [Finset.mul_sum]
      _ ≤ B 1 * (3 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hB10
          rw [geom_sum_eq (by norm_num)]
          have : 0 ≤ (1 / 3 : ℝ) ^ K := by positivity
          rw [div_le_iff_of_neg (by norm_num)]; linarith
      _ = 3 / 2 * B 1 := by ring
  -- Step D: `B 1`
  have hu1 : u 1 = (D - 1) * ρ := by simp [hu]
  have hu1ge : u₁ ≤ u 1 := by
    rw [hu1]
    have : 0 ≤ D - 1 := by linarith
    nlinarith
  have hfu1 : f (D - 1) - Real.exp (-0.48 * Λ) ≤ f (u 1) := by
    have hb : 0 < u 1 := by linarith
    have hle : u 1 ≤ D - 1 := by rw [hu1]; exact mul_le_of_le_one_right (by linarith) hρ1
    have h := xlogx_sub_le hb hle
    have h1ρ : 1 - ρ ≤ Real.exp (-0.98 * Λ) / Λ := by
      rw [hρ, le_div_iff₀ hΛ0]
      have : (1 - Real.log Xm / Λ) * Λ = Λ - Real.log Xm := by field_simp
      linarith
    have hDl : Real.log (D - 1) ≤ 0.3 * Λ := by
      rw [Real.log_le_iff_le_exp (by linarith)]; linarith
    have hdiff : (D - 1) - u 1 ≤ Real.exp (0.3 * Λ) * (Real.exp (-0.98 * Λ) / Λ) := by
      rw [hu1]
      have : (D - 1) - (D - 1) * ρ = (D - 1) * (1 - ρ) := by ring
      rw [this]
      apply mul_le_mul (by linarith) h1ρ (by linarith) (by positivity)
    have hfin : Real.exp (0.3 * Λ) * (Real.exp (-0.98 * Λ) / Λ) * (1 + 0.3 * Λ) ≤
        Real.exp (-0.48 * Λ) := by
      have e : Real.exp (0.3 * Λ) * Real.exp (-0.98 * Λ) =
          Real.exp (-0.48 * Λ) * Real.exp (-0.2 * Λ) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have h2 : Real.exp (-0.2 * Λ) * (1 + 0.3 * Λ) / Λ ≤ 1 := by
        rw [div_le_one hΛ0]
        have hb := Real.add_one_le_exp (0.2 * Λ)
        have hpos := Real.exp_pos (0.2 * Λ)
        have : Real.exp (-0.2 * Λ) = (Real.exp (0.2 * Λ))⁻¹ := by
          rw [← Real.exp_neg]; ring_nf
        rw [this, ← div_eq_inv_mul, div_le_iff₀ hpos]
        have hb2 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 0.2 * Λ by positivity)
        nlinarith
      calc Real.exp (0.3 * Λ) * (Real.exp (-0.98 * Λ) / Λ) * (1 + 0.3 * Λ)
          = Real.exp (-0.48 * Λ) * (Real.exp (-0.2 * Λ) * (1 + 0.3 * Λ) / Λ) := by
            have e2 : Real.exp (0.3 * Λ) * (Real.exp (-0.98 * Λ) / Λ) * (1 + 0.3 * Λ) =
                Real.exp (0.3 * Λ) * Real.exp (-0.98 * Λ) * (1 + 0.3 * Λ) / Λ := by ring
            rw [e2, e]; ring
        _ ≤ Real.exp (-0.48 * Λ) * 1 :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = _ := mul_one _
    simp only [hf] at h ⊢
    have h1l : 0 ≤ 1 + Real.log (D - 1) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ D - 1 by linarith); linarith
    have : ((D - 1) - u 1) * (1 + Real.log (D - 1)) ≤
        Real.exp (0.3 * Λ) * (Real.exp (-0.98 * Λ) / Λ) * (1 + 0.3 * Λ) := by
      apply mul_le_mul hdiff (by linarith) h1l (by positivity)
    linarith
  have hB1 : B 1 ≤ π * (2 + 1 / z) / Xm *
      Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ)) := by
    simp only [hB, hE, if_pos hu1ge]
    have hc1 : ((π + 1 - 1).choose 1 : ℝ) = π := by simp
    rw [hc1, pow_one]
    have hY1 : (2 * z + 1) / Xm / z = (2 + 1 / z) / Xm := by field_simp
    rw [hY1]
    have : Real.exp (-0.9 * f (u 1)) ≤ Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc (π : ℝ) * ((2 + 1 / z) / Xm) * Real.exp (-0.9 * f (u 1))
        ≤ π * ((2 + 1 / z) / Xm) * Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- conclusion
  have hz1 : 1 / z ≤ Real.exp (-Λ) := by
    rw [Real.exp_neg, Real.exp_log hX0pos]
    rw [one_div]; exact inv_anti₀ hX0pos hz
  have hsmall : Real.log (1 + 1 / (2 * z)) + 0.9 * Real.exp (-0.48 * Λ) ≤
      Real.exp (-0.4 * Λ) := by
    have h1 : Real.log (1 + 1 / (2 * z)) ≤ 1 / (2 * z) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (2 * z)) (by positivity); linarith
    have h2 : 1 / (2 * z) ≤ Real.exp (-Λ) / 2 := by
      rw [show 1 / (2 * z) = (1 / z) / 2 by ring]; linarith
    have h3 : Real.exp (-Λ) ≤ Real.exp (-0.4 * Λ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      have : Real.exp (-Λ) * 4 ≤ Real.exp (-Λ) * Real.exp (0.6 * Λ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have := Real.add_one_le_exp (0.6 * Λ); nlinarith
      rw [← Real.exp_add] at this; ring_nf at this ⊢; linarith
    have h4 : Real.exp (-0.48 * Λ) ≤ Real.exp (-0.4 * Λ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      have : Real.exp (-0.48 * Λ) * 4 ≤ Real.exp (-0.48 * Λ) * Real.exp (0.08 * Λ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have := Real.add_one_le_exp (0.08 * Λ); nlinarith
      rw [← Real.exp_add] at this; ring_nf at this ⊢; linarith
    nlinarith [Real.exp_pos (-0.4 * Λ)]
  have hπ0 : (0 : ℝ) < π := by exact_mod_cast hπ
  have hfinal : 3 / 2 * (π * (2 + 1 / z) / Xm *
      Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ))) ≤
      Real.exp (-(Real.log Xm - Real.log (3 * π) + 0.9 * f (D - 1) - Real.exp (-0.4 * Λ))) := by
    have hA : Real.exp (Real.log (3 * π) - Real.log Xm + Real.log (1 + 1 / (2 * z))) =
        3 * π * (1 + 1 / (2 * z)) / Xm := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log hXm0,
        Real.exp_log (by positivity)]
      ring
    have e1 : 3 / 2 * (π * (2 + 1 / z) / Xm *
        Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ))) =
        Real.exp (Real.log (3 * π) - Real.log Xm + Real.log (1 + 1 / (2 * z)) +
          (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ))) := by
      rw [Real.exp_add (Real.log (3 * π) - Real.log Xm + Real.log (1 + 1 / (2 * z))), hA]
      field_simp
    rw [e1]
    apply Real.exp_le_exp.mpr
    linarith
  calc z⁻¹ * ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) *
        Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k)
      = ∑ k ∈ Icc 1 K, ((π + k - 1).choose k : ℝ) *
          Rankin.smoothCount X₀ ((2 * z + 1) / Xm ^ k) / z := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 3 / 2 * B 1 := hsum
    _ ≤ 3 / 2 * (π * (2 + 1 / z) / Xm *
          Real.exp (-0.9 * f (D - 1) + 0.9 * Real.exp (-0.48 * Λ))) := by linarith
    _ ≤ _ := hfinal

end RankFull
