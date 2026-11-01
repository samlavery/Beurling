module

public import RequestProject.Beurling.Construction.RankinRealised
public import RequestProject.Beurling.GenLemma51Final
public import RequestProject.Beurling.Construction.NatPrimeCount
public import RequestProject.Beurling.RankinMinorant

/-!
# Lemma 6.26, step (v): the properties of the realised primes, from (HBS)

Step (v) of Lemma 6.26 (`smoothCountN_le_realised`) uses three properties of the realised primes
below `z = 2y`. The paper derives them from Lemma 5.1 (at heights `≤ 2y`) and from the fact that
below `X₀⁻` the realised primes are the rational primes. Here they are derived from the hypothesis
(HBS) on `[1, z']`, `z ≤ z'` (`BeurlingSystem.HBS`), under which Lemma 5.1 is proved:

* `HBS.sum_inv_primesLt_le` : `∑_{p_j<z} 1/p_j ≤ log log z + 4.1` (Lemma 5.1(iv) with `y = 2`,
  plus the prime `2`);
* `HBS.primesLe_card_le` : `π_P(s) ≤ 2s/log s` for `8 ≤ s ≤ z'` (below `X₀⁻` the rational
  primes, `NatPrimeCount.primeCount_le`; above, `π_P(s) ≤ ψ_P(s^{0.9})/log 2 + ψ_P(s)/(0.9 log s)`
  with Lemma 5.1(i));
* `HBS.sum_rTermR_le` : `R_N(0.69) ≤ R(0.69) + 0.01 ≤ 0.78` (the rational primes give at most
  `R(0.69) ≤ 0.77`, the primes `≥ X₀⁻` at most `∑ 2p^{-1.38}`, bounded on dyadic blocks with
  `ψ_P(t) ≤ 1.42 t`);
* `HBS.smoothCountN_le` : step (v) for such a system, with only `(∗)` as hypothesis;
* `HBS.lemma626` : Lemma 6.26 from steps (i), (iv) and (81);
* `HBS.countA_le_sigmaStar` : the Rankin bound `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}` of the proof of
  Lemma 4.4, from step (i) (with `Y = x`), `(∗)` and `log 2y ≤ λ(log x)`.

The paper has `X₀⁻ ≥ X₀/2` with `log X₀ ≥ 10⁸`; here `log X₀⁻ ≥ 100` is assumed, which is what
the count above `X₀⁻` needs (`log s ≤ 0.2 s^{0.1}`).
-/

@[expose] public section

open Finset Real

namespace BeurlingSystem

/-- `#(A ∩ [1, x]) ≤ Ψ_N(x, z)` when every `n ∈ A`, `n ≤ x`, is the value of a `z`-smooth
element (step (iii) of Lemma 6.26 with `Y = x`). -/
theorem countA_le_smoothCountN (P : BeurlingSystem) {A : Set ℝ} {z x : ℝ} (_hx : 0 ≤ x)
    (hA : ∀ n ∈ A, (n : ℝ) ≤ x → ∃ e ∈ P.smoothElems z, P.val e = n) :
    Absorbed.countA A x ≤ P.smoothCountN x z := by
  choose! f hf using fun n (hn : n ∈ A ∧ n ≤ x) => hA n hn.1 hn.2
  unfold Absorbed.countA smoothCountN
  have key := Set.ncard_le_ncard_of_injOn (s := A ∩ Set.Icc 1 x)
    (t := {e | e ∈ P.smoothElems z ∧ P.val e ≤ x}) f
    (fun n hn => ⟨(hf n ⟨hn.1, hn.2.2⟩).1, by rw [(hf n ⟨hn.1, hn.2.2⟩).2]; exact hn.2.2⟩)
    (fun n hn m hm h => by
      have := congrArg P.val h
      rwa [(hf n ⟨hn.1, hn.2.2⟩).2, (hf m ⟨hm.1, hm.2.2⟩).2] at this)
    (P.finite_smooth_le x z)
  exact_mod_cast key

namespace HBS

variable {P : BeurlingSystem} {X0m z' η1 η2 : ℝ} {ε1 : ℝ → ℝ}

/-- Under (HBS), the only realised prime `≤ 2` is `p_0 = 2`. -/
lemma primesLe_two_subset (h : P.HBS X0m z' η1 η2 ε1) (hz : 3 ≤ z') :
    (P.primesLe z').filter (fun j => ¬ 2 < P.p j) ⊆ {0} := by
  intro j hj
  rw [Finset.mem_filter, mem_primesLe] at hj
  have hX := h.X0m_ge
  have hj2 : P.p j ≤ 2 := not_lt.mp hj.2
  have hid := h.ident (x := 2) (by linarith) (by linarith) j (Or.inl hj2)
  rw [Finset.mem_singleton]
  by_contra hne
  have h1 : qp 1 ≤ qp j := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone
    (Nat.one_le_iff_ne_zero.mpr hne)
  rw [qp, Nat.nth_prime_one_eq_three] at h1
  have : (3 : ℝ) ≤ P.p j := by rw [hid]; exact_mod_cast h1
  linarith

lemma p_zero_eq_two (h : P.HBS X0m z' η1 η2 ε1) (hz : 3 ≤ z') : P.p 0 = 2 := by
  have hX := h.X0m_ge
  have hid := h.ident (x := 2) (by linarith) (by linarith) 0
    (Or.inr (by rw [qp, Nat.nth_prime_zero_eq_two]; norm_num))
  rw [hid, qp, Nat.nth_prime_zero_eq_two]; norm_num

/-- **`∑_{p_j<z} 1/p_j ≤ log log z + 4.1`** under (HBS) on `[1, z']`, `3 ≤ z ≤ z'`
(Lemma 5.1(iv) with `y = 2`, plus the prime `2`). -/
theorem sum_inv_primesLt_le (h : P.HBS X0m z' η1 η2 ε1) {z : ℝ} (hz : 3 ≤ z) (hzz : z ≤ z') :
    ∑ j ∈ P.primesLt z, 1 / P.p j ≤ Real.log (Real.log z) + 4.1 := by
  classical
  have hpos : ∀ j, 0 ≤ 1 / P.p j := fun j => div_nonneg zero_le_one (by linarith [P.one_lt j])
  have hsub : P.primesLt z ⊆ P.primesLe z := by
    intro j hj; rw [mem_primesLt] at hj; rw [mem_primesLe]; exact hj.le
  have h1 : ∑ j ∈ P.primesLt z, 1 / P.p j ≤ ∑ j ∈ P.primesLe z, 1 / P.p j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hpos j)
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLe z) (fun j => 2 < P.p j)] at h1
  have hiv := h.mertens_iv (y := 2) (x := z) le_rfl (by linarith) hzz
  have hiv' := (abs_le.mp hiv).2
  -- the prime `2`
  have h2 : ∑ j ∈ (P.primesLe z).filter (fun j => ¬ 2 < P.p j), 1 / P.p j ≤ 1 / 2 := by
    have hs : (P.primesLe z).filter (fun j => ¬ 2 < P.p j) ⊆ {0} := by
      intro j hj
      apply h.primesLe_two_subset (by linarith)
      rw [Finset.mem_filter, mem_primesLe] at hj ⊢
      exact ⟨hj.1.trans hzz, hj.2⟩
    calc _ ≤ ∑ j ∈ ({0} : Finset ℕ), 1 / P.p j :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => hpos j)
      _ = 1 / 2 := by rw [Finset.sum_singleton, h.p_zero_eq_two (by linarith)]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have e : Real.log (Real.log z / Real.log 2) = Real.log (Real.log z) - Real.log (Real.log 2) :=
    Real.log_div hlz.ne' hl2.ne'
  have e4 : -0.38 ≤ Real.log (Real.log 2) := by
    rw [Real.le_log_iff_exp_le hl2]
    have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.38 by norm_num)
    have h2' := Real.log_two_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hl2]
    calc (Real.log 2)⁻¹ ≤ (0.6931471803 : ℝ)⁻¹ := by
          apply inv_anti₀ (by norm_num); linarith
      _ ≤ 1 + 0.38 + 0.38 ^ 2 / 2 := by norm_num
      _ ≤ _ := hq
  have e5 : 2.20 / Real.log 2 ≤ 3.18 := by
    have := Real.log_two_gt_d9
    rw [div_le_iff₀ hl2]; linarith
  linarith

/-- `θ_P(x) = ∑_{p_j ≤ x} log p_j ≤ ψ_P(x)`. -/
lemma theta_le_psi (P : BeurlingSystem) (S : Finset ℕ) {x : ℝ} (hS : ∀ j ∈ S, P.p j ≤ x) :
    ∑ j ∈ S, Real.log (P.p j) ≤ P.psi x := by
  classical
  rw [psi_eq_sum]
  have e : ∑ j ∈ S, Real.log (P.p j) = ∑ jk ∈ S.image (fun j => (j, 0)), Real.log (P.p jk.1) := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
  rw [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro jk hjk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
    rw [mem_pps]; simpa using hS j hj
  · intro i _ _; exact P.log_p_nonneg i.1

/-- `log s ≤ 0.2 s^{0.1}` for `log s ≥ 100`. -/
lemma log_le_rpow_tenth {s : ℝ} (hs0 : 0 < s) (hs : 100 ≤ Real.log s) :
    Real.log s ≤ 0.2 * s ^ (0.1 : ℝ) := by
  have he : s ^ (0.1 : ℝ) = Real.exp (0.1 * Real.log s) := by
    rw [Real.rpow_def_of_pos hs0]; ring_nf
  rw [he]
  set t := Real.log s
  have h5 := Real.pow_div_factorial_le_exp (x := 0.1 * t) (by positivity) 5
  have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h5
  have ht4 : (10 : ℝ) ^ 8 ≤ t ^ 4 := by
    have : (100 : ℝ) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) hs 4
    norm_num at this ⊢; linarith
  have : t ≤ 0.2 * ((0.1 * t) ^ 5 / 120) := by
    have e : 0.2 * ((0.1 * t) ^ 5 / 120) = t * (t ^ 4 / (6 * 10 ^ 7)) := by ring
    rw [e]
    have : 1 ≤ t ^ 4 / (6 * 10 ^ 7) := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  linarith

/-- **`π_P(s) ≤ 2s/log s` for the realised primes**, `8 ≤ s ≤ z'`, under (HBS) on `[1, z']` with
`log X₀⁻ ≥ 100`: below `X₀⁻` they are the rational primes (`NatPrimeCount.primeCount_le`); above,
`π_P(s) ≤ ψ_P(s^{0.9})/log 2 + ψ_P(s)/(0.9 log s)` and `ψ_P(t) ≤ 1.42 t` (Lemma 5.1(i)). -/
theorem primesLe_card_le (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m) {s : ℝ}
    (hs : 8 ≤ s) (hsz : s ≤ z') :
    ((P.primesLe s).card : ℝ) ≤ 2 * s / Real.log s := by
  classical
  have hX7 := h.X0m_ge
  have hs0 : 0 < s := by linarith
  have hls : 0 < Real.log s := Real.log_pos (by linarith)
  rcases lt_or_ge s X0m with hsX | hsX
  · -- below `X₀⁻`: the rational primes
    set M := ⌊s⌋₊ with hM
    have hM8 : 8 ≤ M := Nat.le_floor (by exact_mod_cast hs)
    have hMs : (M : ℝ) ≤ s := Nat.floor_le hs0.le
    have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    have hcard : (P.primesLe s).card ≤ (M + 1).primesBelow.card := by
      apply Finset.card_le_card_of_injOn (fun j => qp j)
      · intro j hj
        rw [Finset.mem_coe, mem_primesLe] at hj
        have hid := h.ident hsX hsz j (Or.inl hj)
        rw [Finset.mem_coe, Nat.mem_primesBelow]
        refine ⟨show qp j < M + 1 from ?_, qp_prime j⟩
        have : ((qp j : ℕ) : ℝ) ≤ s := by rw [← hid]; exact hj
        have := Nat.le_floor this
        omega
      · intro a _ b _ hab; exact qp_injective hab
    have h1 : ((P.primesLe s).card : ℝ) ≤ (((M + 1).primesBelow.card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have h2 := NatPrimeCount.primeCount_le hM8
    have h3 := div_log_mono (s := (M : ℝ)) (t := s) (by linarith) hMs
    calc ((P.primesLe s).card : ℝ) ≤ _ := h1
      _ ≤ 2 * M / Real.log M := h2
      _ = 2 * (M / Real.log M) := by ring
      _ ≤ 2 * (s / Real.log s) := by linarith
      _ = 2 * s / Real.log s := by ring
  · -- above `X₀⁻`: Chebyshev's bound for the realised system
    have hL : 100 ≤ Real.log s := hX.trans (Real.log_le_log (by linarith) hsX)
    set a := s ^ (0.9 : ℝ) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos hs0 _
    have has : a * s ^ (0.1 : ℝ) = s := by
      rw [ha, ← Real.rpow_add hs0]; norm_num
    have hs1 : 0 < s ^ (0.1 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hlog10 := log_le_rpow_tenth hs0 hL
    have hla : Real.log a = 0.9 * Real.log s := by rw [ha, Real.log_rpow hs0]
    have hale : a ≤ s := by
      have : 1 ≤ s ^ (0.1 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      nlinarith
    rw [← Finset.card_filter_add_card_filter_not (fun j => P.p j ≤ a)]
    set S1 := (P.primesLe s).filter (fun j => P.p j ≤ a)
    set S2 := (P.primesLe s).filter (fun j => ¬ P.p j ≤ a)
    have hmem1 : ∀ j ∈ S1, P.p j ≤ a ∧ 2 ≤ P.p j := by
      intro j hj
      rw [Finset.mem_filter, mem_primesLe] at hj
      exact ⟨hj.2, h.p_ge_two (hj.1.trans hsz)⟩
    have hmem2 : ∀ j ∈ S2, a < P.p j ∧ P.p j ≤ s := by
      intro j hj
      rw [Finset.mem_filter, mem_primesLe] at hj
      exact ⟨not_le.mp hj.2, hj.1⟩
    have hl2 : 0.69 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    -- the primes below `a`
    have hc1 : (S1.card : ℝ) * Real.log 2 ≤ 1.42 * a := by
      have e1 : (S1.card : ℝ) * Real.log 2 ≤ ∑ j ∈ S1, Real.log (P.p j) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun j hj => Real.log_le_log (by norm_num) (hmem1 j hj).2
      have e2 := theta_le_psi P S1 (fun j hj => (hmem1 j hj).1)
      have e3 := h.psi_le ha0.le (hale.trans hsz)
      linarith
    -- the primes in `(a, s]`
    have hc2 : (S2.card : ℝ) * (0.9 * Real.log s) ≤ 1.42 * s := by
      have e1 : (S2.card : ℝ) * (0.9 * Real.log s) ≤ ∑ j ∈ S2, Real.log (P.p j) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const, ← hla]
        exact Finset.sum_le_sum fun j hj => Real.log_le_log ha0 (hmem2 j hj).1.le
      have e2 := theta_le_psi P S2 (fun j hj => (hmem2 j hj).2)
      have e3 := h.psi_le hs0.le hsz
      linarith
    -- `a ≤ s / (5 log s)`
    have hak : a * (5 * Real.log s) ≤ s := by
      have : 5 * Real.log s ≤ s ^ (0.1 : ℝ) := by linarith
      nlinarith
    have k1 : (S1.card : ℝ) * Real.log s * 0.69 ≤ 1.42 * s / 5 := by
      have h1 : (S1.card : ℝ) * 0.69 ≤ 1.42 * a := by
        have : (S1.card : ℝ) * 0.69 ≤ (S1.card : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
        linarith
      have h2 : (S1.card : ℝ) * 0.69 * Real.log s ≤ 1.42 * a * Real.log s :=
        mul_le_mul_of_nonneg_right h1 hls.le
      nlinarith
    rw [le_div_iff₀ hls]
    push_cast
    nlinarith

/-- `-log(1 - x) - x ≤ 2x²` at `x = t^{-0.69} ≤ 1/2`: `rTermR 0.69 t ≤ 2 t^{-1.38}`. -/
lemma rTermR_le_two_rpow {t : ℝ} (ht : 4 ≤ t) : rTermR 0.69 t ≤ 2 * t ^ (-1.38 : ℝ) := by
  have ht0 : 0 < t := by linarith
  set x := t ^ (-0.69 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg ht0.le _
  have hx2 : x ≤ 1 / 2 := by
    have h1 : t ^ (0.5 : ℝ) ≤ t ^ (0.69 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : (2 : ℝ) ≤ t ^ (0.5 : ℝ) := by
      have : (4 : ℝ) ^ (0.5 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [← this]; exact Real.rpow_le_rpow (by norm_num) ht (by norm_num)
    rw [hx, Real.rpow_neg ht0.le, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num; linarith
  have hsq : x ^ 2 = t ^ (-1.38 : ℝ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hlog := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  rw [abs_of_nonneg hx0] at hlog
  have h2 := (abs_le.mp hlog).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2
  have h3 : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  unfold rTermR
  rw [← hx, ← hsq]
  linarith

/-- The realised primes below `X₀⁻` contribute at most `R(0.69) ≤ 0.77` to `R_N(0.69)`. -/
lemma sum_rTermR_rational (h : P.HBS X0m z' η1 η2 ε1) {z : ℝ} (hzz : z ≤ z') :
    ∑ j ∈ (P.primesLt z).filter (fun j => P.p j < X0m), rTermR 0.69 (P.p j) ≤ 0.77 := by
  classical
  set S := (P.primesLt z).filter (fun j => P.p j < X0m)
  have hid : ∀ j ∈ S, P.p j = qp j := by
    intro j hj
    rw [Finset.mem_filter, mem_primesLt] at hj
    exact h.ident (x := P.p j) hj.2 (hj.1.le.trans hzz) j (Or.inl le_rfl)
  set g : ℕ → Nat.Primes := fun j => ⟨qp j, qp_prime j⟩
  have hginj : Set.InjOn g S := fun a _ b _ hab => qp_injective (congrArg Subtype.val hab)
  have e : ∑ j ∈ S, rTermR 0.69 (P.p j) = ∑ q ∈ S.image g, BSCert.Rankin.rTerm (69 / 100) q := by
    rw [Finset.sum_image hginj]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hid j hj]
    unfold rTermR BSCert.Rankin.rTerm
    norm_num [g]
  rw [e]
  have hs := BSCert.Rankin.summable_rTerm (σ := 69 / 100) (by norm_num)
  calc _ ≤ BSCert.Rankin.R (69 / 100) :=
        hs.sum_le_tsum _ (fun q _ => BSCert.Rankin.rTerm_nonneg (by norm_num) q.2.two_le)
    _ ≤ 0.77 := by have := BSCert.Rankin.R_069_le; norm_num at this ⊢; linarith

/-- The realised primes above `X₀⁻` (`log X₀⁻ ≥ 100`) satisfy `∑ p_j^{-1.38} ≤ 0.004`
(dyadic blocks and `ψ_P(t) ≤ 1.42 t`). -/
lemma sum_rpow_large (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m) {z : ℝ}
    (hzz : z ≤ z') :
    ∑ j ∈ (P.primesLt z).filter (fun j => X0m ≤ P.p j), P.p j ^ (-1.38 : ℝ) ≤ 0.004 := by
  classical
  have hX7 := h.X0m_ge
  have hX0 : 0 < X0m := by linarith
  set X := X0m
  set S := (P.primesLt z).filter (fun j => X ≤ P.p j) with hS
  set kf : ℕ → ℕ := fun j => Nat.log 2 ⌊P.p j / X⌋₊ with hkf
  have hblock : ∀ j ∈ S, 2 ^ kf j * X ≤ P.p j ∧ P.p j < 2 ^ (kf j + 1) * X ∧ P.p j < z := by
    intro j hj
    rw [hS, Finset.mem_filter, mem_primesLt] at hj
    have hq : 1 ≤ P.p j / X := by rw [le_div_iff₀ hX0]; linarith [hj.2]
    set m := ⌊P.p j / X⌋₊ with hm
    have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hq)
    have h1 : 2 ^ kf j ≤ m := Nat.pow_log_le_self 2 (by omega)
    have h2 : m < 2 ^ (kf j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h1' : ((2 ^ kf j : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) + 1 ≤ ((2 ^ (kf j + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    have hfl := Nat.floor_le (show 0 ≤ P.p j / X by linarith)
    have hfl2 := Nat.lt_floor_add_one (P.p j / X)
    push_cast at h1' h2'
    refine ⟨?_, ?_, hj.1⟩
    · have : (m : ℝ) * X ≤ P.p j := by rw [← le_div_iff₀ hX0]; exact hfl
      nlinarith
    · have : P.p j < ((m : ℝ) + 1) * X := by rw [← div_lt_iff₀ hX0]; exact hfl2
      nlinarith
  have hmaps : ∀ j ∈ S, kf j ∈ S.image kf := fun j hj => Finset.mem_image_of_mem kf hj
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set r : ℝ := (2 : ℝ) ^ (-0.38 : ℝ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr8 : r ≤ 0.8 := by
    rw [hr, Real.rpow_neg (by norm_num)]
    have : (1.25 : ℝ) ≤ 2 ^ (0.38 : ℝ) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * 0.38)
      have := Real.log_two_gt_d9
      nlinarith
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num at this ⊢; linarith
  have hXr : X ^ (-0.38 : ℝ) ≤ 1 / 39 := by
    rw [Real.rpow_def_of_pos hX0]
    have h1 := Real.add_one_le_exp (Real.log X * 0.38)
    rw [show Real.log X * -0.38 = -(Real.log X * 0.38) by ring, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num; nlinarith
  have hlX : 0 < Real.log X := by linarith
  -- the bound on one block
  have hfib : ∀ k ∈ S.image kf, ∑ j ∈ S.filter (fun j => kf j = k), P.p j ^ (-1.38 : ℝ) ≤
      2.84 / Real.log X * X ^ (-0.38 : ℝ) * r ^ k := by
    intro k hk
    obtain ⟨j0, hj0, hk0⟩ := Finset.mem_image.mp hk
    set F := S.filter (fun j => kf j = k)
    have hF : ∀ j ∈ F, 2 ^ k * X ≤ P.p j ∧ P.p j < 2 ^ (k + 1) * X ∧ P.p j < z := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [← hj.2]; exact hblock j hj.1
    have h2k : (0 : ℝ) < 2 ^ k * X := by positivity
    -- each term
    have hterm : ∀ j ∈ F, P.p j ^ (-1.38 : ℝ) ≤ (2 ^ k * X) ^ (-1.38 : ℝ) := fun j hj =>
      Real.rpow_le_rpow_of_nonpos h2k (hF j hj).1 (by norm_num)
    -- the count
    have hz'0 : 0 ≤ z' := by
      have := hblock j0 hj0
      rw [hk0] at this
      have : (0 : ℝ) < 2 ^ k * X := h2k
      linarith [this, (hblock j0 hj0).2.2, (hblock j0 hj0).1]
    set b := min (2 ^ (k + 1) * X) z'
    have hb0 : 0 ≤ b := le_min (by positivity) hz'0
    have hbz : b ≤ z' := min_le_right _ _
    have hcount : (F.card : ℝ) * Real.log X ≤ 1.42 * (2 ^ (k + 1) * X) := by
      have e1 : (F.card : ℝ) * Real.log X ≤ ∑ j ∈ F, Real.log (P.p j) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_le_sum fun j hj => Real.log_le_log hX0 ?_
        have := (hF j hj).1
        have : X ≤ 2 ^ k * X := le_mul_of_one_le_left hX0.le (one_le_pow₀ (by norm_num))
        linarith
      have e2 := theta_le_psi P F (x := b) (fun j hj =>
        le_min (hF j hj).2.1.le ((hF j hj).2.2.le.trans hzz))
      have e3 := h.psi_le hb0 hbz
      have e4 : b ≤ 2 ^ (k + 1) * X := min_le_left _ _
      linarith
    have hsplit : (2 ^ k * X) ^ (-1.38 : ℝ) = (2 ^ k * X)⁻¹ * (r ^ k * X ^ (-0.38 : ℝ)) := by
      rw [show (-1.38 : ℝ) = -1 + -0.38 by norm_num, Real.rpow_add h2k, Real.rpow_neg_one,
        Real.mul_rpow (by positivity) hX0.le]
      congr 2
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    calc ∑ j ∈ F, P.p j ^ (-1.38 : ℝ) ≤ ∑ _j ∈ F, (2 ^ k * X) ^ (-1.38 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (F.card : ℝ) * (2 ^ k * X) ^ (-1.38 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (F.card : ℝ) * Real.log X * ((Real.log X)⁻¹ * (2 ^ k * X)⁻¹ * (r ^ k * X ^ (-0.38 : ℝ))) := by
          rw [hsplit]; field_simp
      _ ≤ 1.42 * (2 ^ (k + 1) * X) * ((Real.log X)⁻¹ * (2 ^ k * X)⁻¹ * (r ^ k * X ^ (-0.38 : ℝ))) := by
          apply mul_le_mul_of_nonneg_right hcount
          have := Real.rpow_nonneg hX0.le (-0.38 : ℝ)
          have := pow_nonneg hr0 k
          positivity
      _ = 2.84 / Real.log X * X ^ (-0.38 : ℝ) * r ^ k := by
          rw [pow_succ]; field_simp; ring
  have hgeom : ∑ k ∈ S.image kf, r ^ k ≤ 5 := by
    have hs := summable_geometric_of_lt_one hr0 (by linarith)
    calc ∑ k ∈ S.image kf, r ^ k ≤ ∑' k, r ^ k := hs.sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 (by linarith)
      _ ≤ 5 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hc : 2.84 / Real.log X ≤ 0.0284 := by rw [div_le_iff₀ hlX]; linarith
  have hXr0 : 0 ≤ X ^ (-0.38 : ℝ) := Real.rpow_nonneg hX0.le _
  calc _ ≤ ∑ k ∈ S.image kf, 2.84 / Real.log X * X ^ (-0.38 : ℝ) * r ^ k := Finset.sum_le_sum hfib
    _ = 2.84 / Real.log X * X ^ (-0.38 : ℝ) * ∑ k ∈ S.image kf, r ^ k := by rw [Finset.mul_sum]
    _ ≤ 0.0284 * (1 / 39) * 5 := by
        have h0 : 0 ≤ 2.84 / Real.log X := by positivity
        have hs0 : 0 ≤ ∑ k ∈ S.image kf, r ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hr0 k
        gcongr
    _ ≤ 0.004 := by norm_num

/-- **`R_N(0.69) ≤ 0.78`** for the realised primes below `z ≤ z'`, under (HBS) on `[1, z']` with
`log X₀⁻ ≥ 100`: the rational primes contribute at most `R(0.69) ≤ 0.77`, the others
(`≥ X₀⁻`) at most `∑ 2p^{-1.38} ≤ 0.008`. -/
theorem sum_rTermR_le (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m) {z : ℝ}
    (hzz : z ≤ z') :
    ∑ j ∈ P.primesLt z, rTermR 0.69 (P.p j) ≤ 0.78 := by
  classical
  have hX7 := h.X0m_ge
  rw [← Finset.sum_filter_add_sum_filter_not (P.primesLt z) (fun j => P.p j < X0m)]
  have h1 := h.sum_rTermR_rational hzz
  have h2 := h.sum_rpow_large hX hzz
  have e : (P.primesLt z).filter (fun j => ¬ P.p j < X0m) =
      (P.primesLt z).filter (fun j => X0m ≤ P.p j) :=
    Finset.filter_congr fun j _ => not_lt
  rw [e]
  have h3 : ∑ j ∈ (P.primesLt z).filter (fun j => X0m ≤ P.p j), rTermR 0.69 (P.p j) ≤
      ∑ j ∈ (P.primesLt z).filter (fun j => X0m ≤ P.p j), 2 * P.p j ^ (-1.38 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_filter] at hj
    exact rTermR_le_two_rpow (by linarith [hj.2])
  rw [← Finset.mul_sum] at h3
  linarith

/-- **Lemma 6.26, step (v), for a system satisfying (HBS).** Let `P` satisfy (HBS) on `[1, z']`
with `log X₀⁻ ≥ 100`, let `8 ≤ z ≤ z'`, `Y > 0`, `u = log Y / log z`, `η = log u / log z`, and
suppose `(∗)`: `u ≥ 2·10⁸`, `log log z ≤ 1.79 u`, `η ≤ 0.31`. Then
`Ψ_N(Y, z) ≤ Y exp(-0.9 u log u)`. -/
theorem smoothCountN_le (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m) {z Y : ℝ}
    (hz : 8 ≤ z) (hzz : z ≤ z') (hY : 0 < Y)
    (hu : 2 * 10 ^ 8 ≤ Real.log Y / Real.log z)
    (hll : Real.log (Real.log z) ≤ 1.79 * (Real.log Y / Real.log z))
    (hη : Real.log (Real.log Y / Real.log z) / Real.log z ≤ 0.31) :
    P.smoothCountN Y z ≤ Y * Real.exp (-(0.9 * (Real.log Y / Real.log z) *
      Real.log (Real.log Y / Real.log z))) :=
  smoothCountN_le_realised P hz hY (fun s hs hsz => h.primesLe_card_le hX hs (hsz.trans hzz))
    (h.sum_inv_primesLt_le (by linarith) hzz) (h.sum_rTermR_le hX hzz) hu hll hη

/-- **Lemma 6.26 from steps (i), (iv) and (81), for a system satisfying (HBS) on `[1, z']`**
(`log X₀⁻ ≥ 100`, `4 ≤ y`, `2y ≤ z'`): with `u_* = log(2yh)/log(2y)` and
`η = log u_*/log(2y)`, if `(∗)` holds (`u_* ≥ 2·10⁸`, `log log 2y ≤ 1.79 u_*`, `η ≤ 0.31`),
`1 ≤ u₀ ≤ u_*` and (81) `0.9 u₀ log u₀ ≥ log(2y) + log C_d + 4 log L`, then
`#(A ∩ [u, u + h]) ≤ h L^{-4}`. Step (v) is proved (`smoothCountN_le`). -/
theorem lemma626 (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m) {A : Set ℝ}
    {u hh y Cd u0 L : ℝ} (h1 : 1 ≤ hh) (hu : hh < u) (hy : 4 ≤ y) (hyz : 2 * y ≤ z')
    (hCd : 0 < Cd) (hL : 0 < L)
    (hS : ∀ n ∈ A, u ≤ n → (n : ℝ) ≤ u + hh → ∃ e ∈ P.smoothElems (2 * y), P.val e = n)
    (hW : ∀ d ∈ P.smoothElems (2 * y), hh < P.val d → P.val d ≤ 2 * y * hh →
      ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + hh}.ncard : ℝ) ≤ Cd)
    (hus : 2 * 10 ^ 8 ≤ Real.log (2 * y * hh) / Real.log (2 * y))
    (hll : Real.log (Real.log (2 * y)) ≤ 1.79 * (Real.log (2 * y * hh) / Real.log (2 * y)))
    (hη : Real.log (Real.log (2 * y * hh) / Real.log (2 * y)) / Real.log (2 * y) ≤ 0.31)
    (hu01 : 1 ≤ u0) (hu0 : u0 ≤ Real.log (2 * y * hh) / Real.log (2 * y))
    (h81 : Real.log (2 * y) + Real.log Cd + 4 * Real.log L ≤ 0.9 * u0 * Real.log u0) :
    (Absorbed.localCountA A u (u + hh) : ℝ) ≤ hh * L ^ (-4 : ℤ) :=
  lemma626_of_steps_v P h1 hu hy hCd hL hS hW
    (fun s hs hsz => h.primesLe_card_le hX hs (hsz.trans hyz))
    (h.sum_inv_primesLt_le (by linarith) hyz) (h.sum_rTermR_le hX hyz) hus hll hη hu01 hu0 h81

/-- **The Rankin bound for `A` (proof of Lemma 4.4, from Lemma 6.26 steps (i) and (v) with
`Y = x`)**, for a system satisfying (HBS) on `[1, z']` with `log X₀⁻ ≥ 100`. Let `4 ≤ y`,
`2y ≤ z'`, `x ≥ 1`, `u = log x / log(2y)`, and suppose
* (i) every `n ∈ A` with `n ≤ x` is the value of a `2y`-smooth element;
* `(∗)`: `u ≥ 2·10⁸`, `log log 2y ≤ 1.79 u`, `log u / log 2y ≤ 0.31`;
* `log 2y ≤ λ(log x) = max(22.6Λ, 12(log log x)² + 9 log log x + 8)`.

Then `#(A ∩ [1, x]) ≤ x e^{-ς_*(log x)}`. -/
theorem countA_le_sigmaStar (h : P.HBS X0m z' η1 η2 ε1) (hX : 100 ≤ Real.log X0m)
    {A : Set ℝ} {y x Λ : ℝ} (hy : 4 ≤ y) (hyz : 2 * y ≤ z') (hx : 1 ≤ x)
    (hA : ∀ n ∈ A, (n : ℝ) ≤ x → ∃ e ∈ P.smoothElems (2 * y), P.val e = n)
    (hu : 2 * 10 ^ 8 ≤ Real.log x / Real.log (2 * y))
    (hll : Real.log (Real.log (2 * y)) ≤ 1.79 * (Real.log x / Real.log (2 * y)))
    (hη : Real.log (Real.log x / Real.log (2 * y)) / Real.log (2 * y) ≤ 0.31)
    (hlam : Real.log (2 * y) ≤ RankinMinorant.rankinLambda Λ (Real.log x)) :
    Absorbed.countA A x ≤ x * Real.exp (-RankinMinorant.sigmaStar Λ (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have h1 := countA_le_smoothCountN P hx0.le hA
  have h2 := h.smoothCountN_le hX (z := 2 * y) (Y := x) (by linarith) hyz hx0 hu hll hη
  set u := Real.log x / Real.log (2 * y)
  set ut := RankinMinorant.rankinU Λ (Real.log x)
  have hly : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlam0 : 0 < RankinMinorant.rankinLambda Λ (Real.log x) := lt_of_lt_of_le hly hlam
  have hut0 : 0 ≤ ut := div_nonneg hlx hlam0.le
  have hutu : ut ≤ u := div_le_div_of_nonneg_left hlx hly hlam
  have hu1 : 1 ≤ u := by linarith
  have hmono : ut * Real.log ut ≤ u * Real.log u := by
    have hlu : 0 ≤ Real.log u := Real.log_nonneg hu1
    rcases le_or_gt 1 ut with hut1 | hut1
    · have h3 : Real.log ut ≤ Real.log u := Real.log_le_log (by linarith) hutu
      have h4 : 0 ≤ Real.log ut := Real.log_nonneg hut1
      nlinarith
    · have : Real.log ut ≤ 0 := Real.log_nonpos hut0 hut1.le
      nlinarith
  refine h1.trans (h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx0.le))
  unfold RankinMinorant.sigmaStar
  nlinarith

end HBS

end BeurlingSystem

end
