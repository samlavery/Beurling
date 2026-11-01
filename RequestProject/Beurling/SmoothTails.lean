module

public import RequestProject.Beurling.Rankin

/-!
# Lemma 6.22(c): smooth tails

Let `Ψ(Y, X₀)` be the number of `X₀`-smooth integers `≤ Y` (`Rankin.smoothCount`), `Λ = log X₀`
and `u = log Y / Λ`.

* `SmoothTails.smooth_tail_rankin` : the first part of Lemma 6.22(c). With `σ = 1 - η`,
  `η = log(u log u)/Λ`, Rankin's bound gives `Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)` for
  `u ≥ max(10⁴, log Λ)`, provided the Euler-product estimate
  `log ∏_{p < X₀} (1 - p^{-σ})^{-1} ≤ log Λ + 1.3 u + 2` holds. That estimate is the
  computer-assisted part of the paper's proof (it uses `R(0.69) ≤ 0.77`, Rosser–Schoenfeld and
  the bound on `Ei`); here it is a hypothesis.
* `SmoothTails.smoothCount_le_pow` : the counting argument of the second part: an `X₀`-smooth
  `d ≤ Y` is determined by its exponents, each at most `log Y / log 2`, so
  `Ψ(Y, X₀) ≤ (1 + log Y / log 2)^{π(X₀)}` (`π(X₀)` = number of primes below `X₀`).
* `SmoothTails.smooth_tail_count` : with `π(X₀) ≤ 1.26 X₀ / Λ` (Rosser–Schoenfeld, a
  hypothesis), `Ψ(Y, X₀) ≤ exp(1.26 X₀ log(2 log Y) / Λ)` for `log Y ≥ 2`.
-/

@[expose] public section

open Real Finset

namespace SmoothTails

/-- The arithmetic of the last step of Lemma 6.22(c): for `u ≥ max(10⁴, log Λ)`,
`-u log u - u log log u + 1.3 u + log Λ + 2 ≤ -0.9 u log u`. -/
lemma tail_arith {u Λ : ℝ} (hu : 10 ^ 4 ≤ u) (huΛ : Real.log Λ ≤ u) :
    -u * Real.log u - u * Real.log (Real.log u) + 1.3 * u + Real.log Λ + 2 ≤
      -0.9 * (u * Real.log u) := by
  have hu0 : 0 < u := by linarith
  have h9 : 9 ≤ Real.log u := by
    have he : Real.exp 9 ≤ 10 ^ 4 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 := pow_le_pow_left₀ (by positivity) this.le 9
        _ ≤ 10 ^ 4 := by norm_num
    rw [Real.le_log_iff_exp_le hu0]; linarith
  have h2 : 2 ≤ Real.log (Real.log u) := by
    have he : Real.exp 2 ≤ 9 := by
      have := Real.exp_one_lt_d9
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (by positivity) this.le 2
        _ ≤ 9 := by norm_num
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have k1 : 9 * u ≤ u * Real.log u := by nlinarith
  have k2 : 2 * u ≤ u * Real.log (Real.log u) := by nlinarith
  nlinarith

/-- **Lemma 6.22(c)**, first part (Rankin's bound with `σ = 1 - log(u log u)/Λ`). Let `X₀ ≥ 2`,
`Λ = log X₀`, `Y > 0`, `u = log Y / Λ` with `u ≥ max(10⁴, log Λ)`, and `σ = 1 - η > 0`,
`η = log(u log u)/Λ`. If `log ∏_{p < X₀} (1 - p^{-σ})^{-1} ≤ log Λ + 1.3 u + 2`, then
`Ψ(Y, X₀) ≤ Y exp(-0.9 u log u)`. -/
theorem smooth_tail_rankin {X₀ : ℕ} (hX₀ : 2 ≤ X₀) {Y : ℝ} (hY : 0 < Y)
    (hu : 10 ^ 4 ≤ Real.log Y / Real.log X₀)
    (huΛ : Real.log (Real.log X₀) ≤ Real.log Y / Real.log X₀)
    (hσ : 0 < 1 - Real.log (Real.log Y / Real.log X₀ *
      Real.log (Real.log Y / Real.log X₀)) / Real.log X₀)
    (hEuler : Real.log (Rankin.rankinConst X₀ (1 - Real.log (Real.log Y / Real.log X₀ *
      Real.log (Real.log Y / Real.log X₀)) / Real.log X₀)) ≤
      Real.log (Real.log X₀) + 1.3 * (Real.log Y / Real.log X₀) + 2) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤
      Y * Real.exp (-0.9 * (Real.log Y / Real.log X₀ *
        Real.log (Real.log Y / Real.log X₀))) := by
  set Λ := Real.log X₀ with hΛ
  set u := Real.log Y / Λ with hudef
  set σ := 1 - Real.log (u * Real.log u) / Λ with hσdef
  have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (by omega : 1 < X₀))
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hR := Rankin.smoothCount_le_rankin X₀ hσ hY.le
  have hRpos : 0 < Rankin.rankinConst X₀ σ := by
    unfold Rankin.rankinConst
    apply Finset.prod_pos
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
    have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
    positivity
  have hRle : Rankin.rankinConst X₀ σ ≤ Real.exp (Real.log Λ + 1.3 * u + 2) := by
    rw [← Real.exp_log hRpos]; exact Real.exp_le_exp.mpr hEuler
  have hYσ : Y ^ σ = Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u)) := by
    rw [Real.rpow_def_of_pos hY, ← Real.exp_log hY]
    rw [Real.log_exp, ← Real.exp_add]
    congr 1
    have hlY : Real.log Y = u * Λ := by rw [hudef]; field_simp
    rw [hσdef, Real.log_mul hu0.ne' hlu.ne', hlY]
    field_simp
    ring
  calc (Rankin.smoothCount X₀ Y : ℝ) ≤ Y ^ σ * Rankin.rankinConst X₀ σ := hR
    _ ≤ Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u)) *
          Real.exp (Real.log Λ + 1.3 * u + 2) := by
        rw [hYσ]; exact mul_le_mul_of_nonneg_left hRle (by positivity)
    _ = Y * Real.exp (-u * Real.log u - u * Real.log (Real.log u) + 1.3 * u +
          Real.log Λ + 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ Y * Real.exp (-0.9 * (u * Real.log u)) := by
        apply mul_le_mul_of_nonneg_left _ hY.le
        exact Real.exp_le_exp.mpr (tail_arith hu huΛ)

/-- **Counting exponents** (Lemma 6.22(c), second part): an `X₀`-smooth `d ≤ Y` is determined
by its exponents at the primes `p < X₀`, each at most `log Y / log 2`. Hence
`Ψ(Y, X₀) ≤ (⌊log Y / log 2⌋ + 1)^{π(X₀)}`. -/
theorem smoothCount_le_pow (X₀ : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Rankin.smoothCount X₀ Y ≤
      (⌊Real.log Y / Real.log 2⌋₊ + 1) ^ X₀.primesBelow.card := by
  classical
  set K := ⌊Real.log Y / Real.log 2⌋₊
  set T := X₀.primesBelow.pi (fun _ => Finset.range (K + 1))
  have hT : T.card = (K + 1) ^ X₀.primesBelow.card := by
    simp [T, Finset.card_pi, Finset.prod_const]
  rw [← hT]
  unfold Rankin.smoothCount
  apply Finset.card_le_card_of_injOn (fun n => fun p _ => n.factorization p)
  · intro n hn
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo] at hn
    obtain ⟨hnY, hns⟩ := hn
    have hn0 : n ≠ 0 := hns.1
    simp only [T, Finset.mem_coe, Finset.mem_pi, Finset.mem_range]
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have h1 : p ^ n.factorization p ≤ n := Nat.ordProj_le p hn0
    have h2 : 2 ^ n.factorization p ≤ n :=
      (Nat.pow_le_pow_left hp'.two_le _).trans h1
    have h3 : ((2 : ℝ)) ^ n.factorization p ≤ Y := by
      have : ((2 ^ n.factorization p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      have hnY' : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hnY).trans (Nat.floor_le (by linarith))
      push_cast at this
      linarith
    have h4 : (n.factorization p : ℝ) ≤ Real.log Y / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos (by norm_num))]
      have := Real.log_le_log (by positivity) h3
      rwa [Real.log_pow] at this
    have : n.factorization p ≤ K := Nat.le_floor h4
    omega
  · intro n hn m hm hnm
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo] at hn hm
    have hn0 : n ≠ 0 := hn.2.1
    have hm0 : m ≠ 0 := hm.2.1
    apply Nat.eq_of_factorization_eq hn0 hm0
    intro p
    by_cases hp : p ∈ X₀.primesBelow
    · exact congrFun (congrFun hnm p) hp
    · have hz : ∀ k ∈ X₀.smoothNumbers, k.factorization p = 0 := by
        intro k hk
        by_contra hne
        have hpk : p ∈ k.primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hne
        apply hp
        rw [Nat.mem_primesBelow]
        exact ⟨(Nat.mem_smoothNumbers'.mp hk) p (Nat.prime_of_mem_primeFactors hpk) (Nat.dvd_of_mem_primeFactors hpk), Nat.prime_of_mem_primeFactors hpk⟩
      rw [hz n hn.2, hz m hm.2]

/-- **Lemma 6.22(c)**, second part: if `π(X₀) ≤ 1.26 X₀ / Λ` (Rosser–Schoenfeld) and
`Y > 0` with `log Y ≥ 2`, then `Ψ(Y, X₀) ≤ exp(1.26 X₀ log(2 log Y) / Λ)`. -/
theorem smooth_tail_count {X₀ : ℕ} (hX₀ : 2 ≤ X₀) {Y : ℝ} (hY0 : 0 < Y) (hY : 2 ≤ Real.log Y)
    (hπ : (X₀.primesBelow.card : ℝ) ≤ 1.26 * X₀ / Real.log X₀) :
    (Rankin.smoothCount X₀ Y : ℝ) ≤
      Real.exp (1.26 * X₀ * Real.log (2 * Real.log Y) / Real.log X₀) := by
  have hY1 : 1 ≤ Y := ((Real.log_pos_iff hY0.le).mp (by linarith)).le
  have h := smoothCount_le_pow X₀ hY1
  set K := ⌊Real.log Y / Real.log 2⌋₊
  have hl2 : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hK : ((K + 1 : ℕ) : ℝ) ≤ 2 * Real.log Y := by
    have h1 : (K : ℝ) ≤ Real.log Y / Real.log 2 := Nat.floor_le (by positivity)
    have h2 : Real.log Y / Real.log 2 ≤ Real.log Y / 0.69 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hl2
    push_cast
    have : Real.log Y / 0.69 = Real.log Y * (1 / 0.69) := by ring
    nlinarith
  have hΛ : 0 < Real.log X₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < X₀))
  have hlog2 : 0 ≤ Real.log (2 * Real.log Y) := Real.log_nonneg (by linarith)
  calc (Rankin.smoothCount X₀ Y : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) ^ X₀.primesBelow.card := by
        exact_mod_cast h
    _ ≤ (2 * Real.log Y) ^ X₀.primesBelow.card := pow_le_pow_left₀ (by positivity) hK _
    _ = Real.exp (X₀.primesBelow.card * Real.log (2 * Real.log Y)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]; ring_nf
    _ ≤ Real.exp (1.26 * X₀ * Real.log (2 * Real.log Y) / Real.log X₀) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right hπ hlog2
        calc (X₀.primesBelow.card : ℝ) * Real.log (2 * Real.log Y)
            ≤ 1.26 * X₀ / Real.log X₀ * Real.log (2 * Real.log Y) := this
          _ = 1.26 * X₀ * Real.log (2 * Real.log Y) / Real.log X₀ := by ring

end SmoothTails
