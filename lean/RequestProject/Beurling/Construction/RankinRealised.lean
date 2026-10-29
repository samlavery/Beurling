module

public import RequestProject.Beurling.Construction.RankinBeurling
public import RequestProject.Beurling.Construction.DivisorTrick
public import RequestProject.Beurling.GenNatPart
public import RequestProject.Beurling.SmoothTailsCert

/-!
# Lemma 6.26, step (v): Rankin's bound for the realised system

Let `P` be a discrete Beurling system, `z = 2y`, `Y > 0`, and put
`u_* := log Y / log z`, `η := log u_* / log z`, `σ := 1 - η`. Step (v) of Lemma 6.26 proves,
under

  `(∗)  u_* ≥ 2Λ (≥ 2·10⁸),  log log z ≤ 1.79 u_*,  η ≤ 0.31`,

that `Ψ_N(Y, z) ≤ Y exp(-0.9 u_* log u_*)`, from three properties of the realised primes:

* `π_P(s) ≤ 2s / log s` (here used for `8 ≤ s ≤ z`);
* `∑_{p_j < z} 1/p_j ≤ log log z + 4.1` (Lemma 5.1(iv));
* `R_N(0.69) = ∑_{p_j < z} (-log(1 - p_j^{-0.69}) - p_j^{-0.69}) ≤ 0.78`.

The proof is the paper's: Rankin's bound with `σ = 1 - η` (`smoothCountN_le_rankin`),
`Y^σ = Y e^{-u_* log u_*}`, `log ∏ (1 - p^{-σ})^{-1} = ∑ p^{-σ} + R_N(σ)` with `R_N(σ) ≤ R_N(0.69)`,
`p^{-σ} = 1/p + g(p)` with `g(t) = (t^η - 1)/t`, and partial summation of `g` against
`π_P(s) ≤ 2s/log s`, compared with `2 Ein(η log z) = 2 Ein(log u_*)`. The partial summation is done
on the integer parts of the realised primes (`sum_g_le`); this changes only the additive constant
(`26` here), which is absorbed since `u_* ≥ 2·10⁸`. The coefficient of `u_*/log u_*` is the
paper's `2(1 + 2/log u_*)`.

* `smoothCountN_le_realised` : step (v) (second bound).
* `lemma626_of_steps_v` : Lemma 6.26 from steps (i), (iv), (81) and the hypotheses of step (v) at
  `Y = 2yh`, i.e. with step (v) proved.
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

/-- `-log(1 - t^{-σ}) - t^{-σ}`, the prime-power part of `log (1 - t^{-σ})^{-1}`, at a real `t`. -/
noncomputable def rTermR (σ t : ℝ) : ℝ := -Real.log (1 - t ^ (-σ)) - t ^ (-σ)

/-- `g(t) = (t^η - 1)/t`, so that `t^{-(1-η)} = 1/t + g(t)`. -/
noncomputable def gEta (η t : ℝ) : ℝ := (t ^ η - 1) / t

lemma rTermR_anti {t : ℝ} (ht : 1 < t) {σ τ : ℝ} (hτ : 0 < τ) (hστ : τ ≤ σ) :
    rTermR σ t ≤ rTermR τ t := by
  unfold rTermR
  set a := t ^ (-σ)
  set b := t ^ (-τ)
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by linarith) _
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg ht (by linarith)
  have h1 : Real.log ((1 - b) / (1 - a)) ≤ (1 - b) / (1 - a) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  rw [Real.log_div (by linarith) (by linarith)] at h1
  have h2 : (1 - b) / (1 - a) - 1 ≤ a - b := by
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

lemma rpow_neg_one_sub_eq {t : ℝ} (ht : 0 < t) (η : ℝ) :
    t ^ (-(1 - η)) = 1 / t + gEta η t := by
  unfold gEta
  rw [show -(1 - η) = η + (-1 : ℝ) by ring, Real.rpow_add ht, Real.rpow_neg_one]
  field_simp
  ring

lemma gEta_nonneg {η t : ℝ} (hη : 0 ≤ η) (ht : 1 ≤ t) : 0 ≤ gEta η t := by
  unfold gEta
  have : 1 ≤ t ^ η := Real.one_le_rpow ht hη
  exact div_nonneg (by linarith) (by linarith)

lemma gEta_le_one {η t : ℝ} (hη1 : η ≤ 1) (ht : 1 ≤ t) : gEta η t ≤ 1 := by
  unfold gEta
  have : t ^ η ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hη1
  rw [Real.rpow_one] at this
  rw [div_le_one (by linarith)]
  linarith

/-- `g` is non-increasing on `[8, ∞)` for `0 ≤ η ≤ 0.31`. -/
lemma gEta_anti {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 0.31) {s t : ℝ} (hs : 8 ≤ s) (hst : s ≤ t) :
    gEta η t ≤ gEta η s := by
  unfold gEta
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  set r := t / s with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hs0]; linarith
  have htr : t = s * r := by rw [hr]; field_simp
  have hB : r ^ η ≤ 1 + η * (r - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := r - 1) (p := η) (by linarith) hη (by linarith)
    simpa using this
  have hl8 : 2.07 ≤ Real.log 8 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hsη : 1 + 2.07 * η ≤ s ^ η := by
    have h1 : (8 : ℝ) ^ η ≤ s ^ η := Real.rpow_le_rpow (by norm_num) hs hη
    have h2 : (8 : ℝ) ^ η = Real.exp (η * Real.log 8) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have h3 := Real.add_one_le_exp (η * Real.log 8)
    nlinarith
  have hkey : 1 ≤ s ^ η * (1 - η) := by nlinarith
  have hpos : 0 ≤ s ^ η := Real.rpow_nonneg hs0.le _
  have htη : t ^ η = s ^ η * r ^ η := by
    rw [htr, Real.mul_rpow hs0.le (by linarith)]
  rw [div_le_div_iff₀ ht0 hs0, htη, htr]
  have : s ^ η * r ^ η ≤ s ^ η * (1 + η * (r - 1)) := mul_le_mul_of_nonneg_left hB hpos
  have h2 : (r - 1) ≤ s ^ η * (1 - η) * (r - 1) := by nlinarith
  nlinarith

/-- `t / log t` is non-decreasing on `[e, ∞)` (stated for `3 ≤ s`). -/
lemma div_log_mono {s t : ℝ} (hs : 3 ≤ s) (hst : s ≤ t) : s / Real.log s ≤ t / Real.log t := by
  have hs0 : 0 < s := by linarith
  have hl1 : 1 ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]
    have := Real.exp_one_lt_d9; linarith
  have hlt : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  have hq : Real.log (t / s) ≤ t / s - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) hs0)
  rw [Real.log_div (by linarith) hs0.ne'] at hq
  have h1 : s * Real.log t ≤ t * Real.log s := by
    have : s * (Real.log t - Real.log s) ≤ t - s := by
      have := mul_le_mul_of_nonneg_left hq hs0.le
      have e : s * (t / s - 1) = t - s := by field_simp
      linarith
    nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- `F(t) = Ein(η log t)` has derivative `g(t)/log t`. -/
lemma hasDerivAt_EinLog {η t : ℝ} (hη : 0 < η) (ht : 1 < t) :
    HasDerivAt (fun t => BSCert.EiFn.Ein (η * Real.log t)) (gEta η t / Real.log t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 : HasDerivAt (fun t => Real.log t) t⁻¹ t := Real.hasDerivAt_log ht0.ne'
  have h3 := h1.const_mul η
  have h4 := (BSCert.EiFn.hasDerivAt_Ein (mul_pos hη hl)).comp t h3
  convert h4 using 1
  unfold gEta
  rw [Real.rpow_def_of_pos ht0, mul_comm (Real.log t) η]
  field_simp

/-- The tail of the comparison sum: `∑_{n=9}^N g(n)/log n ≤ F(N) - F(8)`. -/
lemma sum_gEta_div_log_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 0.31) {N : ℕ} (hN : 8 ≤ N) :
    ∑ n ∈ Icc 9 N, gEta η n / Real.log n ≤
      BSCert.EiFn.Ein (η * Real.log N) - BSCert.EiFn.Ein (η * Real.log 8) := by
  set F : ℝ → ℝ := fun t => BSCert.EiFn.Ein (η * Real.log t) with hF
  have step : ∀ n : ℕ, 9 ≤ n → gEta η n / Real.log n ≤ F n - F (n - 1 : ℕ) := by
    intro n hn
    have hn' : (9 : ℝ) ≤ n := by exact_mod_cast hn
    have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hc]
    obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope F (fun t => gEta η t / Real.log t)
      (show (n : ℝ) - 1 < n by linarith)
      (fun x hx => (hasDerivAt_EinLog hη (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_EinLog hη (by linarith [hx.1]))
    simp only [sub_sub_cancel, div_one] at hc2
    rw [← hc2]
    have hc8 : 8 ≤ c := by linarith [hc1.1]
    have hg := gEta_anti hη.le hη1 hc8 hc1.2.le
    have hg0 := gEta_nonneg (η := η) (t := n) hη.le (by linarith)
    have hlc : 0 < Real.log c := Real.log_pos (by linarith)
    have hlcn : Real.log c ≤ Real.log n := Real.log_le_log (by linarith) hc1.2.le
    calc gEta η n / Real.log n ≤ gEta η n / Real.log c :=
          div_le_div_of_nonneg_left hg0 hlc hlcn
      _ ≤ gEta η c / Real.log c := by gcongr
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := step (M + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    simp only [hF] at this
    push_cast at this ⊢
    linarith

lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- The realised primes below `8` contribute at most `8` to `∑ g(p_j)`. -/
lemma sum_gEta_small (P : BeurlingSystem) {z η : ℝ} (hz : 8 ≤ z) (hη1 : η ≤ 1)
    (hπ : ∀ s, 8 ≤ s → s ≤ z → ((P.primesLe s).card : ℝ) ≤ 2 * s / Real.log s) :
    ∑ j ∈ (P.primesLt z).filter (fun j => P.p j < 8), gEta η (P.p j) ≤ 8 := by
  set S := (P.primesLt z).filter (fun j => P.p j < 8)
  have hsub : S ⊆ P.primesLe 8 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [mem_primesLe]; exact hj.2.le
  have hcard : (S.card : ℝ) ≤ 8 := by
    have h1 : (S.card : ℝ) ≤ (P.primesLe 8).card := by exact_mod_cast Finset.card_le_card hsub
    have h2 := hπ 8 le_rfl hz
    have hl8 : 2.07 ≤ Real.log 8 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    have h3 : 2 * 8 / Real.log 8 ≤ 8 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  calc ∑ j ∈ S, gEta η (P.p j) ≤ ∑ _j ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => gEta_le_one hη1 (P.one_lt j).le
    _ = S.card := by simp
    _ ≤ 8 := hcard

/-- The comparison sum after partial summation:
`∑_{n=3}^N (2/log n) g(max(n, 8)) ≤ 12 + 2 (F(N) - F(8))`. -/
lemma sum_two_div_log_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 0.31) {N : ℕ} (hN : 8 ≤ N) :
    ∑ n ∈ Icc 3 N, 2 / Real.log n * gEta η (max (n : ℝ) 8) ≤
      12 + 2 * (BSCert.EiFn.Ein (η * Real.log N) - BSCert.EiFn.Ein (η * Real.log 8)) := by
  have hsplit : Icc 3 N = Icc 3 8 ∪ Icc 9 N := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 3 8) (Icc 9 N) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have h1 : ∑ n ∈ (Icc 3 8 : Finset ℕ), 2 / Real.log n * gEta η (max (n : ℝ) 8) ≤ 12 := by
    have : ∀ n ∈ (Icc 3 8 : Finset ℕ), 2 / Real.log n * gEta η (max (n : ℝ) 8) ≤ 2 := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hl : 1 ≤ Real.log n :=
        one_le_log_three.trans (Real.log_le_log (by norm_num) hn3)
      have hg1 := gEta_le_one (η := η) (t := max (n : ℝ) 8) (by linarith)
        (by linarith [le_max_right (n : ℝ) 8])
      have hg0 := gEta_nonneg (t := max (n : ℝ) 8) hη.le (by linarith [le_max_right (n : ℝ) 8])
      have h2 : 2 / Real.log n ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      have h20 : 0 ≤ 2 / Real.log n := by positivity
      nlinarith
    calc _ ≤ ∑ _n ∈ (Icc 3 8 : Finset ℕ), (2 : ℝ) := Finset.sum_le_sum this
      _ = 12 := by simp; norm_num
  have h2 : ∑ n ∈ Icc 9 N, 2 / Real.log n * gEta η (max (n : ℝ) 8) =
      2 * ∑ n ∈ Icc 9 N, gEta η n / Real.log n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have : (8 : ℝ) ≤ n := by exact_mod_cast (by omega : 8 ≤ n)
    rw [max_eq_left this]; ring
  have h3 := sum_gEta_div_log_le hη hη1 hN
  linarith

/-- **Partial summation of `g` over the realised primes** against `π_P(s) ≤ 2s/log s`:
`∑_{p_j < z} g(p_j) ≤ 26 + 2 Ein(η log z)`. -/
lemma sum_gEta_le (P : BeurlingSystem) {z η : ℝ} (hz : 8 ≤ z) (hη : 0 < η) (hη1 : η ≤ 0.31)
    (hπ : ∀ s, 8 ≤ s → s ≤ z → ((P.primesLe s).card : ℝ) ≤ 2 * s / Real.log s) :
    ∑ j ∈ P.primesLt z, gEta η (P.p j) ≤ 26 + 2 * BSCert.EiFn.Ein (η * Real.log z) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLt z) (fun j => P.p j < 8)]
  have hsmall := sum_gEta_small P hz (by linarith) hπ
  set S := (P.primesLt z).filter (fun j => ¬ P.p j < 8) with hS
  set N := ⌊z⌋₊ with hNdef
  have hN8 : 8 ≤ N := Nat.le_floor (by exact_mod_cast hz)
  have hNz : (N : ℝ) ≤ z := Nat.floor_le (by linarith)
  set f : ℕ → ℕ := fun j => ⌊P.p j⌋₊ with hf
  set w : ℕ → ℝ := fun n => gEta η (max (n : ℝ) 8) with hw
  have hmemS : ∀ j ∈ S, 8 ≤ P.p j ∧ P.p j < z := by
    intro j hj
    rw [hS, Finset.mem_filter, mem_primesLt] at hj
    exact ⟨not_lt.mp hj.2, hj.1⟩
  have hf8 : ∀ j ∈ S, 8 ≤ f j := fun j hj => Nat.le_floor (by exact_mod_cast (hmemS j hj).1)
  -- step 1: `g(p_j) ≤ w(⌊p_j⌋)`
  have h1 : ∑ j ∈ S, gEta η (P.p j) ≤ ∑ j ∈ S, w (f j) := by
    apply Finset.sum_le_sum
    intro j hj
    have h8 : (8 : ℝ) ≤ f j := by exact_mod_cast hf8 j hj
    have hle : (f j : ℝ) ≤ P.p j := Nat.floor_le (by linarith [(hmemS j hj).1])
    simp only [hw, max_eq_left h8]
    exact gEta_anti hη.le hη1 h8 hle
  -- step 2: group by integer part
  set a : ℕ → ℝ := fun n => ((S.filter (fun j => f j = n)).card : ℝ) with ha
  have hmaps : ∀ j ∈ S, f j ∈ Icc 2 N := by
    intro j hj
    rw [Finset.mem_Icc]
    refine ⟨by linarith [hf8 j hj], Nat.floor_le_floor (hmemS j hj).2.le⟩
  have h2 : ∑ j ∈ S, w (f j) = ∑ n ∈ Icc 2 N, a n * w n := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
      Finset.sum_const, nsmul_eq_mul]
  -- step 3: partial sums
  set B : ℕ → ℝ := fun M => 2 * ((M : ℝ) + 1) / Real.log ((M : ℝ) + 1) with hB
  have hA : ∀ M ≥ 2, ∑ n ∈ Icc 2 M, a n ≤ B M := by
    intro M hM
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hBnn : 0 ≤ B M := by
      simp only [hB]
      exact div_nonneg (by linarith) (Real.log_nonneg (by linarith))
    have e : ∑ n ∈ Icc 2 M, a n = ((S.filter (fun j => f j ∈ Icc 2 M)).card : ℝ) := by
      simp only [ha]
      rw [← Finset.sum_card_fiberwise_eq_card_filter]
      push_cast; rfl
    rw [e]
    by_cases hM8 : M + 1 < 8
    · have : S.filter (fun j => f j ∈ Icc 2 M) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj hmem
        rw [Finset.mem_Icc] at hmem
        have := hf8 j hj
        omega
      rw [this]; simpa using hBnn
    by_cases hMz : (M : ℝ) + 1 ≤ z
    · have hsub : S.filter (fun j => f j ∈ Icc 2 M) ⊆ P.primesLe ((M : ℝ) + 1) := by
        intro j hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        rw [mem_primesLe]
        have h1 := Nat.lt_floor_add_one (P.p j)
        have h2 : ((f j : ℕ) : ℝ) ≤ M := by exact_mod_cast hj.2.2
        simp only [hf] at h2
        linarith
      have hc := hπ ((M : ℝ) + 1) (by
        have : (8 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (not_lt.mp hM8)
        push_cast at this; linarith) hMz
      calc _ ≤ ((P.primesLe ((M : ℝ) + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ B M := hc
    · push_neg at hMz
      have hsub : S.filter (fun j => f j ∈ Icc 2 M) ⊆ P.primesLe z := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [mem_primesLe]; exact (hmemS j hj.1).2.le
      have hc := hπ z hz le_rfl
      have hmono := div_log_mono (s := z) (t := (M : ℝ) + 1) (by linarith) hMz.le
      calc _ ≤ ((P.primesLe z).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 * z / Real.log z := hc
        _ ≤ B M := by
          simp only [hB, mul_div_assoc]; linarith
  -- step 4: Abel summation
  have hwanti : ∀ n ≥ 2, w (n + 1) ≤ w n := by
    intro n _
    simp only [hw]
    apply gEta_anti hη.le hη1 (le_max_right _ _)
    push_cast
    exact max_le_max (by linarith) le_rfl
  have hw0 : ∀ n ≥ 2, 0 ≤ w n := fun n _ =>
    gEta_nonneg hη.le (by linarith [le_max_right (n : ℝ) 8])
  have hab := Mertens.abel_upper a w B hA hwanti hw0 (by omega : 2 ≤ N)
  -- step 5: the pieces
  have hB2 : B 2 * w 2 ≤ 6 := by
    have hg1 : w 2 ≤ 1 := gEta_le_one (by linarith) (by linarith [le_max_right ((2:ℕ) : ℝ) 8])
    have hg0 := hw0 2 le_rfl
    have hl3 := one_le_log_three
    have : B 2 ≤ 6 := by
      simp only [hB]; norm_num
      rw [div_le_iff₀ (by linarith)]; linarith
    have hB0 : 0 ≤ B 2 := by
      simp only [hB]; norm_num; positivity
    nlinarith
  have hdiff : ∀ n ∈ Icc 3 N, (B n - B (n - 1)) * w n ≤ 2 / Real.log n * w n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    apply mul_le_mul_of_nonneg_right _ (hw0 n (by omega))
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hln : 0 < Real.log n := Real.log_pos (by linarith)
    have hlnn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    simp only [hB, hc, sub_add_cancel]
    have : 2 * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) / Real.log n :=
      div_le_div_of_nonneg_left (by linarith) hln hlnn
    have e : 2 * ((n : ℝ) + 1) / Real.log n - 2 * (n : ℝ) / Real.log n = 2 / Real.log n := by
      field_simp; ring
    linarith
  have h5 := Finset.sum_le_sum hdiff
  have h6 := sum_two_div_log_le hη hη1 hN8
  have h7 : BSCert.EiFn.Ein (η * Real.log N) ≤ BSCert.EiFn.Ein (η * Real.log z) :=
    SmoothTails.Ein_mono (by
      have h8N : (8 : ℝ) ≤ N := by exact_mod_cast hN8
      have : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
      positivity) (by
      have : (8 : ℝ) ≤ N := by exact_mod_cast hN8
      gcongr)
  have h8 := SmoothTails.Ein_nonneg (x := η * Real.log 8) (by
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity)
  have hw' : ∑ n ∈ Icc 3 N, 2 / Real.log n * w n =
      ∑ n ∈ Icc 3 N, 2 / Real.log n * gEta η (max (n : ℝ) 8) := rfl
  linarith

/-- `Ein(L) ≤ (e^L/L)(1 + 2/L)` for `L ≥ 11`. -/
lemma Ein_le_of_ge_11 {L : ℝ} (hL : 11 ≤ L) :
    BSCert.EiFn.Ein L ≤ Real.exp L / L * (1 + 2 / L) := by
  have hEi := BSCert.EiFn.Ei_le_of_ge_11 hL
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlx : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  unfold BSCert.EiFn.Ei at hEi
  linarith

/-- `log (2·10⁸) ≥ 19.1`. -/
lemma log_two_e8_ge : 19.1 ≤ Real.log (2 * 10 ^ 8) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 19.1 = Real.exp 1 ^ 19 * Real.exp 0.1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_bound_div_one_sub_of_interval' (x := 0.1) (by norm_num) (by norm_num)
  rw [h1]
  calc Real.exp 1 ^ 19 * Real.exp 0.1 ≤ 2.7182818286 ^ 19 * (1 / (1 - 0.1)) := by gcongr
    _ ≤ 2 * 10 ^ 8 := by norm_num

/-- The final inequality of step (v). -/
lemma step_v_arith {u L ll : ℝ} (hu : 2 * 10 ^ 8 ≤ u) (hL : 19.1 ≤ L) (hll : ll ≤ 1.79 * u) :
    -(u * L) + (ll + 4.1) + (26 + 2 * (u / L * (1 + 2 / L))) + 0.78 ≤ -(0.9 * u * L) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have k2 : u / L * (1 + 2 / L) ≤ u / 19.1 * (1 + 2 / 19.1) := by
    have : u / L ≤ u / 19.1 := div_le_div_of_nonneg_left hu0.le (by norm_num) hL
    have k1 : 2 / L ≤ 2 / 19.1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
    have h0 : 0 ≤ u / L := by positivity
    calc u / L * (1 + 2 / L) ≤ u / L * (1 + 2 / 19.1) := by gcongr
      _ ≤ u / 19.1 * (1 + 2 / 19.1) := by gcongr
  have k3 : u * 19.1 ≤ u * L := by nlinarith
  set X := u / L * (1 + 2 / L)
  norm_num at k2 ⊢
  nlinarith

/-- `log ∏_{p_j<z} (1 - p_j^{-σ})^{-1} = ∑_{p_j<z} (p_j^{-σ} + rTermR σ p_j)`. -/
lemma log_rankinProd_eq (P : BeurlingSystem) {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    Real.log (P.rankinProd z σ) = ∑ j ∈ P.primesLt z, (P.p j ^ (-σ) + rTermR σ (P.p j)) := by
  have hfac : ∀ j, 0 < 1 - P.p j ^ (-σ) := by
    intro j
    have : P.p j ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)
    linarith
  unfold rankinProd
  rw [Real.log_prod (fun j _ => (inv_pos.mpr (hfac j)).ne')]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.log_inv]; unfold rTermR; ring

lemma rankinProd_pos (P : BeurlingSystem) {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    0 < P.rankinProd z σ := by
  unfold rankinProd
  apply Finset.prod_pos
  intro j _
  have : P.p j ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (P.one_lt j) (by linarith)
  have : 0 < 1 - P.p j ^ (-σ) := by linarith
  positivity

/-- **Lemma 6.26, step (v): Rankin's bound for the realised system.** Let `z ≥ 8`, `Y > 0`,
`u = log Y / log z`, `η = log u / log z`. Suppose the realised primes satisfy
`π_P(s) ≤ 2s/log s` for `8 ≤ s ≤ z`, `∑_{p_j<z} 1/p_j ≤ log log z + 4.1` and
`R_N(0.69) ≤ 0.78`, and that `(∗)` holds: `u ≥ 2·10⁸`, `log log z ≤ 1.79 u`, `η ≤ 0.31`. Then
`Ψ_N(Y, z) ≤ Y exp(-0.9 u log u)`. -/
theorem smoothCountN_le_realised (P : BeurlingSystem) {z Y : ℝ} (hz : 8 ≤ z) (hY : 0 < Y)
    (hπ : ∀ s, 8 ≤ s → s ≤ z → ((P.primesLe s).card : ℝ) ≤ 2 * s / Real.log s)
    (hM : ∑ j ∈ P.primesLt z, 1 / P.p j ≤ Real.log (Real.log z) + 4.1)
    (hR : ∑ j ∈ P.primesLt z, rTermR 0.69 (P.p j) ≤ 0.78)
    (hu : 2 * 10 ^ 8 ≤ Real.log Y / Real.log z)
    (hll : Real.log (Real.log z) ≤ 1.79 * (Real.log Y / Real.log z))
    (hη : Real.log (Real.log Y / Real.log z) / Real.log z ≤ 0.31) :
    P.smoothCountN Y z ≤ Y * Real.exp (-(0.9 * (Real.log Y / Real.log z) *
      Real.log (Real.log Y / Real.log z))) := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set u := Real.log Y / Real.log z with hudef
  set L := Real.log u with hLdef
  set η := L / Real.log z with hηdef
  have hu0 : 0 < u := by linarith
  have hL : 19.1 ≤ L := log_two_e8_ge.trans (Real.log_le_log (by norm_num) hu)
  have hη0 : 0 < η := div_pos (by linarith) hlz
  have hσ : 0 < 1 - η := by linarith
  have hηlz : η * Real.log z = L := by rw [hηdef]; field_simp
  have hlY : Real.log Y = u * Real.log z := by rw [hudef]; field_simp
  -- Rankin's bound
  have hRk := P.smoothCountN_le_rankin hσ hY.le z
  -- `Y^σ = Y e^{-u log u}`
  have hYσ : Y ^ (1 - η) = Y * Real.exp (-(u * L)) := by
    rw [Real.rpow_def_of_pos hY]
    conv_rhs => rw [← Real.exp_log hY]
    rw [← Real.exp_add]
    congr 1
    rw [hlY, ← hηlz]; ring
  -- the Euler product
  have hlog := log_rankinProd_eq P hσ z
  have hsplit : ∀ j ∈ P.primesLt z, P.p j ^ (-(1 - η)) + rTermR (1 - η) (P.p j) ≤
      1 / P.p j + gEta η (P.p j) + rTermR 0.69 (P.p j) := by
    intro j _
    rw [rpow_neg_one_sub_eq (by linarith [P.one_lt j])]
    have := rTermR_anti (P.one_lt j) (σ := 1 - η) (τ := 0.69) (by norm_num) (by linarith)
    linarith
  have hsum := Finset.sum_le_sum hsplit
  have e : ∑ j ∈ P.primesLt z, (1 / P.p j + gEta η (P.p j) + rTermR 0.69 (P.p j)) =
      ∑ j ∈ P.primesLt z, 1 / P.p j + ∑ j ∈ P.primesLt z, gEta η (P.p j) +
        ∑ j ∈ P.primesLt z, rTermR 0.69 (P.p j) := by
    simp only [Finset.sum_add_distrib]
  rw [e] at hsum
  have hg := sum_gEta_le P hz hη0 hη hπ
  rw [hηlz] at hg
  have hEin : BSCert.EiFn.Ein L ≤ u / L * (1 + 2 / L) := by
    have := Ein_le_of_ge_11 (L := L) (by linarith)
    rwa [hLdef, Real.exp_log hu0] at this
  have hlogR : Real.log (P.rankinProd z (1 - η)) ≤
      (Real.log (Real.log z) + 4.1) + (26 + 2 * (u / L * (1 + 2 / L))) + 0.78 := by
    rw [hlog]; linarith
  have hRpos := rankinProd_pos P hσ z
  have hRle : P.rankinProd z (1 - η) ≤
      Real.exp ((Real.log (Real.log z) + 4.1) + (26 + 2 * (u / L * (1 + 2 / L))) + 0.78) := by
    rw [← Real.exp_log hRpos]; exact Real.exp_le_exp.mpr hlogR
  have harith := step_v_arith hu hL hll
  calc P.smoothCountN Y z ≤ Y ^ (1 - η) * P.rankinProd z (1 - η) := hRk
    _ ≤ Y * Real.exp (-(u * L)) *
          Real.exp ((Real.log (Real.log z) + 4.1) + (26 + 2 * (u / L * (1 + 2 / L))) + 0.78) := by
        rw [hYσ]; exact mul_le_mul_of_nonneg_left hRle (by positivity)
    _ = Y * Real.exp (-(u * L) +
          ((Real.log (Real.log z) + 4.1) + (26 + 2 * (u / L * (1 + 2 / L))) + 0.78)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ Y * Real.exp (-(0.9 * u * L)) := by
        apply mul_le_mul_of_nonneg_left _ hY.le
        apply Real.exp_le_exp.mpr
        linarith

/-- **Lemma 6.26 with step (v) proved.** Let `z = 2y ≥ 8`, `1 ≤ h < u`, and let
`u_* = log(2yh) / log(2y)`, `η = log u_* / log(2y)`. Suppose
* (i) every `n ∈ A ∩ [u, u + h]` is the value of a `2y`-smooth element of `N`;
* (iv) each window `[u/d, (u + h)/d]`, `d` smooth in `(h, 2yh]`, holds at most `C_d` elements;
* the realised primes below `2y` satisfy `π_P(s) ≤ 2s/log s` (`8 ≤ s ≤ 2y`),
  `∑_{p_j<2y} 1/p_j ≤ log log 2y + 4.1` and `R_N(0.69) ≤ 0.78`;
* `(∗)` at `Y = 2yh`: `u_* ≥ 2·10⁸`, `log log 2y ≤ 1.79 u_*`, `η ≤ 0.31`;
* `1 ≤ u₀ ≤ u_*` (in the paper `u_* = 1 + u₀`);
* (81) `0.9 u₀ log u₀ ≥ log(2y) + log C_d + 4 log L`.

Then `#(A ∩ [u, u + h]) ≤ h L^{-4}`. -/
theorem lemma626_of_steps_v (P : BeurlingSystem) {A : Set ℝ} {u h y Cd u0 L : ℝ} (hh : 1 ≤ h)
    (hu : h < u) (hy : 4 ≤ y) (hCd : 0 < Cd) (hL : 0 < L)
    (hS : ∀ n ∈ A, u ≤ n → (n : ℝ) ≤ u + h → ∃ e ∈ P.smoothElems (2 * y), P.val e = n)
    (hW : ∀ d ∈ P.smoothElems (2 * y), h < P.val d → P.val d ≤ 2 * y * h →
      ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.ncard : ℝ) ≤ Cd)
    (hπ : ∀ s, 8 ≤ s → s ≤ 2 * y → ((P.primesLe s).card : ℝ) ≤ 2 * s / Real.log s)
    (hM : ∑ j ∈ P.primesLt (2 * y), 1 / P.p j ≤ Real.log (Real.log (2 * y)) + 4.1)
    (hR : ∑ j ∈ P.primesLt (2 * y), rTermR 0.69 (P.p j) ≤ 0.78)
    (hus : 2 * 10 ^ 8 ≤ Real.log (2 * y * h) / Real.log (2 * y))
    (hll : Real.log (Real.log (2 * y)) ≤ 1.79 * (Real.log (2 * y * h) / Real.log (2 * y)))
    (hη : Real.log (Real.log (2 * y * h) / Real.log (2 * y)) / Real.log (2 * y) ≤ 0.31)
    (hu01 : 1 ≤ u0) (hu0 : u0 ≤ Real.log (2 * y * h) / Real.log (2 * y))
    (h81 : Real.log (2 * y) + Real.log Cd + 4 * Real.log L ≤ 0.9 * u0 * Real.log u0) :
    (Absorbed.localCountA A u (u + h) : ℝ) ≤ h * L ^ (-4 : ℤ) := by
  have hY : 0 < 2 * y * h := by positivity
  have hv := smoothCountN_le_realised P (z := 2 * y) (Y := 2 * y * h) (by linarith) hY hπ hM hR
    hus hll hη
  set us := Real.log (2 * y * h) / Real.log (2 * y)
  have hmono : u0 * Real.log u0 ≤ us * Real.log us := by
    have h1 : Real.log u0 ≤ Real.log us := Real.log_le_log (by linarith) hu0
    have h2 : 0 ≤ Real.log u0 := Real.log_nonneg hu01
    nlinarith
  have hR' : P.smoothCountN (2 * y * h) (2 * y) ≤
      2 * y * h * Real.exp (-(0.9 * u0 * Real.log u0)) := by
    refine hv.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hY.le)
    nlinarith
  exact P.lemma626_of_steps hh hu (by linarith) hCd hL hS hW hR' h81

end BeurlingSystem

end
