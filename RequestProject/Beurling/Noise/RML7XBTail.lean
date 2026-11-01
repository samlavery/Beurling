module

public import RequestProject.Beurling.Noise.RML7XBLevel
public import RequestProject.BSCert.Finite.X0BandCert
public import RequestProject.BSCert.Consts.XBandConsts
public import RequestProject.BSCert.Consts.OrdFact

/-!
# Proposition 5.31(i): `Br(n) ≤ 5/12` for every `n ≥ 2`

* `BrN_le_Bx` : for `n ≤ 10⁶` and `λ₀ (10⁶)^ε ≤ 1.0001`, `Br(n) ≤ B(n)`, the certified quantity
  of `x0band_exact.py` (`BSCert.X0Band.Bx`, with `λ = 1.0001`), so `Br(n) ≤ 5/12`
  (`BSCert.X0Band.Bx_le_five_twelfths`);
* `BrN_le_tail` : for `n > 10⁶`, `Br(n) ≤ (½ + 1.64√n)/n + ¼λ₀ · 1.64 · 13.1 · n^{-0.2} ≤ 0.35`
  (the analytic tail of the paper: `Σ_{d ∣ n} μ²(d) = 2^{ω(n)} ≤ 1.64√n`, `BSCert.Consts.x3`, and
  the factorisation `d = em`, `Σ_{m ≥ 2} H_ord(m) m^{-1.77} = A(1.77) ≤ 13.1`,
  `BSCert.Consts.Hord_sum_177_le`);
* `BrN_le` : `Br(n) ≤ 5/12` for every `n ≥ 2`.
-/

@[expose] public section

open Finset Real

namespace KR.XB7

lemma musqR_eq (m : ℕ) : musqR m = if Squarefree m then 1 else 0 := by
  unfold musqR
  split_ifs with h
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

lemma musqR_le_one (m : ℕ) : musqR m ≤ 1 := by
  rw [musqR_eq]; split_ifs <;> norm_num

/-- `Σ_{j ∣ k} μ²(j) = 2^{ω(k)}`. -/
lemma sum_musqR_divisors {k : ℕ} (hk : k ≠ 0) :
    ∑ j ∈ k.divisors, musqR j = 2 ^ k.primeFactors.card := by
  simp_rw [musqR_eq]
  rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hk]
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
  push_cast
  congr 2
  rw [Nat.factors_eq, List.toFinset_coe]
  rfl

/-- `Σ_{j ∣ k} μ²(j) ≤ 1.64 √k`. -/
lemma sum_musqR_le {k : ℕ} (hk : k ≠ 0) : ∑ j ∈ k.divisors, musqR j ≤ 1.64 * √k := by
  rw [sum_musqR_divisors hk]
  obtain ⟨h1, h2⟩ := BSCert.Consts.x3 hk
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    ← Nat.primeFactors.eq_1] at h1
  have := Real.sqrt_nonneg (k : ℝ)
  nlinarith

/-- The inner reindexing `e ↦ m = d/e`. -/
lemma inner_reindex (ε : ℝ) {d : ℕ} (hd : d ≠ 0) :
    ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d) =
      ∑ m ∈ d.divisors.filter (fun m => 1 < m ∧ m < d),
        musqR (d / m) * ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  refine Finset.sum_nbij' (fun e => d / e) (fun m => d / m) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
    obtain ⟨⟨hed, -⟩, he1, he2⟩ := he
    obtain ⟨k, hk⟩ := hed
    have he0 : 0 < e := by omega
    have hk' : d / e = k := by rw [hk]; exact Nat.mul_div_cancel_left k he0
    rw [hk']
    refine ⟨⟨⟨e, by rw [hk]; ring⟩, hd⟩, ?_, ?_⟩
    · by_contra h; push_neg at h
      interval_cases k <;> simp_all
    · rw [hk]
      calc k = 1 * k := (one_mul k).symm
        _ < e * k := Nat.mul_lt_mul_of_pos_right he1 (by
            rcases Nat.eq_zero_or_pos k with h | h
            · subst h; simp at hk; omega
            · exact h)
  · intro m hm
    simp only [Finset.mem_filter, Nat.mem_divisors] at hm ⊢
    obtain ⟨⟨hmd, -⟩, hm1, hm2⟩ := hm
    obtain ⟨k, hk⟩ := hmd
    have hm0 : 0 < m := by omega
    have hk' : d / m = k := by rw [hk]; exact Nat.mul_div_cancel_left k hm0
    rw [hk']
    refine ⟨⟨⟨m, by rw [hk]; ring⟩, hd⟩, ?_, ?_⟩
    · by_contra h; push_neg at h
      interval_cases k <;> simp_all
    · rw [hk]
      calc k = 1 * k := (one_mul k).symm
        _ < m * k := Nat.mul_lt_mul_of_pos_right hm1 (by
            rcases Nat.eq_zero_or_pos k with h | h
            · subst h; simp at hk; omega
            · exact h)
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    exact Nat.div_div_self he.1.1 hd
  · intro m hm
    simp only [Finset.mem_filter, Nat.mem_divisors] at hm
    exact Nat.div_div_self hm.1.1 hd
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hed, -⟩, he1, -⟩ := he
    rw [Nat.div_div_self hed hd]
    obtain ⟨k, hk⟩ := id hed
    have he0 : 0 < e := by omega
    have hk' : d / e = k := by rw [hk]; exact Nat.mul_div_cancel_left k he0
    simp only [hk']
    have hk0 : (k : ℝ) ≠ 0 := by
      have : k ≠ 0 := by rintro rfl; simp at hk; omega
      exact_mod_cast this
    have hdk : (d : ℝ) = e * k := by exact_mod_cast hk
    rw [hdk]
    have he0' : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    field_simp

/-- The swap `Σ_{d ∣ n} Σ_{m ∣ d, m > 1} G(m, d/m) = Σ_{m ∣ n, m > 1} Σ_{j ∣ n/m} G(m, j)`. -/
lemma swap_sum {n : ℕ} (hn : n ≠ 0) (G : ℕ → ℕ → ℝ) :
    ∑ d ∈ n.divisors, ∑ m ∈ d.divisors.filter (1 < ·), G m (d / m) =
      ∑ m ∈ n.divisors.filter (1 < ·), ∑ j ∈ (n / m).divisors, G m j := by
  rw [Finset.sum_comm' (t' := n.divisors.filter (1 < ·))
    (s' := fun m => n.divisors.filter (m ∣ ·))]
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hm
    obtain ⟨⟨hmn, -⟩, hm1⟩ := hm
    have hm0 : 0 < m := by omega
    refine Finset.sum_nbij' (fun d => d / m) (fun j => m * j) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdn, -⟩, hmd⟩ := hd
      obtain ⟨j, rfl⟩ := hmd
      rw [Nat.mul_div_cancel_left j hm0]
      obtain ⟨k, hk⟩ := hdn
      refine ⟨⟨k, ?_⟩, ?_⟩
      · rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hm0]
      · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨j * k, by rw [hk]; ring⟩)
          hm0).ne'
    · intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj ⊢
      obtain ⟨hjd, -⟩ := hj
      refine ⟨⟨?_, hn⟩, dvd_mul_right m j⟩
      obtain ⟨k, hk⟩ := hjd
      obtain ⟨l, hl⟩ := hmn
      refine ⟨k, ?_⟩
      rw [hl, Nat.mul_div_cancel_left _ hm0] at hk
      rw [hl, hk]; ring
    · intro d hd
      simp only [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro j _
      exact Nat.mul_div_cancel_left j hm0
    · intro d _; rfl
  · intro d m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, ⟨hmd, hd0⟩, hm1⟩
      exact ⟨⟨⟨hdn, hn⟩, hmd⟩, ⟨dvd_trans hmd hdn, hn⟩, hm1⟩
    · rintro ⟨⟨⟨hdn, -⟩, hmd⟩, ⟨-, -⟩, hm1⟩
      refine ⟨⟨hdn, hn⟩, ⟨hmd, ?_⟩, hm1⟩
      rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdn)

/-- **`Br(n) ≤ B(n)`** for `2 ≤ n ≤ 10⁶`, when `λ₀ (10⁶)^ε ≤ 1.0001`. -/
lemma BrN_le_Bx {ε lam0 : ℝ} (hε0 : 0 ≤ ε) (hlam0 : 0 ≤ lam0)
    (hlε : lam0 * ((10 : ℝ) ^ 6) ^ ε ≤ 1.0001) {n : ℕ} (hn1 : 2 ≤ n) (hn2 : n ≤ 10 ^ 6) :
    BrN ε lam0 n ≤ (BSCert.X0Band.Bx n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold BrN BSCert.X0Band.Bx BSCert.X0Band.X BSCert.X0Band.lam BSCert.X0Band.musq
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hmusq : ∀ m : ℕ, ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 = musqR m := fun m => rfl
  simp only [hmusq]
  refine add_le_add_right ?_ _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hd' := Finset.mem_filter.mp hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd'.1
  have hd1 : 1 < d := hd'.2.1
  have hdle : d ≤ 10 ^ 6 := by
    have := Nat.le_of_dvd (by omega) hdn; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold betaD
  -- each inner term
  have hin : ∀ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      lam0 * (musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) *
        ((e : ℝ) / d)) ≤
      10001 / 10000 * (musqR e * e * (BSCert.X0Band.Hord (d / e) : ℝ)) / d := by
    intro e he
    have hq : lam0 * ((d / e : ℕ) : ℝ) ^ ε ≤ 10001 / 10000 := by
      have hde : ((d / e : ℕ) : ℝ) ≤ 10 ^ 6 := by
        have : d / e ≤ 10 ^ 6 := (Nat.div_le_self d e).trans hdle
        exact_mod_cast this
      have h1 : ((d / e : ℕ) : ℝ) ^ ε ≤ ((10 : ℝ) ^ 6) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hde hε0
      nlinarith [mul_le_mul_of_nonneg_left h1 hlam0]
    have hmu := musqR_nonneg e
    have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have e1 : lam0 * (musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) *
        ((e : ℝ) / d)) = (lam0 * ((d / e : ℕ) : ℝ) ^ ε) *
          (musqR e * e * (BSCert.X0Band.Hord (d / e) : ℝ)) / d := by ring
    rw [e1]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact mul_le_mul_of_nonneg_right hq (by positivity)
  have hsum := Finset.sum_le_sum hin
  rw [← Finset.mul_sum] at hsum
  set S' := ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
    musqR e * e * (BSCert.X0Band.Hord (d / e) : ℝ)
  set S := ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
    musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)
  have hR : ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      10001 / 10000 * (musqR e * e * (BSCert.X0Band.Hord (d / e) : ℝ)) / d =
      10001 / 10000 * S' / d := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hR] at hsum
  have e3 : 1 / 2 * (2 * musqR d + 1 / 2 * (10001 / 10000) * S' / d) =
      musqR d + 1 / 4 * (10001 / 10000 * S' / d) := by ring
  rw [e3]
  have e4 : 1 / 4 * lam0 * S = 1 / 4 * (lam0 * S) := by ring
  rw [e4]
  linarith


/-- `m^ε · m⁻¹ · √(n/m) · n⁻¹ ≤ m^{-1.77} n^{-0.2}` for `1 ≤ m ≤ n`, `0 ≤ ε ≤ 0.03`. -/
lemma rpow_tail_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 0.03) {m n : ℝ} (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    m ^ ε / m * √(n / m) / n ≤ m ^ (-1.77 : ℝ) * n ^ (-0.2 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hsq : √(n / m) = n ^ (1 / 2 : ℝ) * m ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hn0.le hm0.le, Real.rpow_neg hm0.le, div_eq_mul_inv]
  have hL : m ^ ε / m * √(n / m) / n =
      m ^ (-1.77 : ℝ) * (m ^ (ε + 0.27) * n ^ (-(1 / 2 : ℝ))) := by
    rw [hsq]
    have e1 : m ^ ε / m = m ^ (ε - 1) := by rw [Real.rpow_sub hm0, Real.rpow_one]
    have e2 : n ^ (1 / 2 : ℝ) / n = n ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn0]; norm_num
    have e3 : m ^ (ε - 1) * m ^ (-(1 / 2 : ℝ)) = m ^ (-1.77 : ℝ) * m ^ (ε + 0.27) := by
      rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]; ring_nf
    calc m ^ ε / m * (n ^ (1 / 2 : ℝ) * m ^ (-(1 / 2 : ℝ))) / n
        = (m ^ (ε - 1) * m ^ (-(1 / 2 : ℝ))) * (n ^ (1 / 2 : ℝ) / n) := by rw [e1]; ring
      _ = _ := by rw [e3, e2]; ring
  rw [hL]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hm0.le _)
  have h1 : m ^ (ε + 0.27) ≤ n ^ (ε + 0.27) := Real.rpow_le_rpow hm0.le hmn (by linarith)
  have h2 : n ^ (ε + 0.27) ≤ n ^ (0.3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3 : n ^ (0.3 : ℝ) * n ^ (-(1 / 2 : ℝ)) = n ^ (-0.2 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have h4 : 0 ≤ n ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
  calc m ^ (ε + 0.27) * n ^ (-(1 / 2 : ℝ)) ≤ n ^ (0.3 : ℝ) * n ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) h4
    _ = _ := h3

/-- `∑_{m ∣ n, m > 1} H_ord(m) m^{-1.77} ≤ A(1.77) ≤ 13.1`. -/
lemma sum_Hord_177_le (n : ℕ) :
    ∑ m ∈ n.divisors.filter (1 < ·), (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-1.77 : ℝ) ≤
      13.1 := by
  have hS := (BSCert.Consts.hasSum_Hord (s := 1.77) (by norm_num)
    BSCert.Consts.ordA_177_le.1).summable
  set f : ℕ → ℝ := fun m => if 2 ≤ m then (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-1.77 : ℝ)
    else 0
  have hf0 : ∀ m, 0 ≤ f m := fun m => by
    simp only [f]; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact le_rfl
  have hfS : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun m => ?_) hS
    simp only [f]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ∑ m ∈ n.divisors.filter (1 < ·), (BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-1.77 : ℝ)
      = ∑ m ∈ n.divisors.filter (1 < ·), f m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have : 2 ≤ m := (Finset.mem_filter.mp hm).2
        simp only [f, if_pos this]
    _ ≤ ∑' m, f m := hfS.sum_le_tsum _ (fun m _ => hf0 m)
    _ ≤ 13.1 := BSCert.Consts.Hord_sum_177_le

/-- **The analytic tail**: for `n > 10⁶`, `Br(n) ≤ 5/12` (`0 ≤ ε ≤ 4·10⁻⁶`, `λ₀ ≤ 1.001`). -/
lemma BrN_le_tail {ε lam0 : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hlam0 : 0 ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) {n : ℕ} (hn : 10 ^ 6 < n) : BrN ε lam0 n ≤ 5 / 12 := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (10 : ℝ) ^ 6 < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set D := n.divisors.filter (fun d => 1 < d ∧ d < n)
  -- (i) the `μ²` part
  have hA : musqR n / 2 + ∑ d ∈ D, musqR d ≤ 1 / 2 + 1.64 * √n := by
    have h1 := musqR_le_one n
    have h2 : ∑ d ∈ D, musqR d ≤ ∑ d ∈ n.divisors, musqR d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => musqR_nonneg d)
    have h3 := sum_musqR_le hn0
    linarith
  -- (ii) the double sum
  set G : ℕ → ℕ → ℝ := fun m j => musqR j * ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m
  have hG0 : ∀ m j, 0 ≤ G m j := fun m j => by
    simp only [G]
    have := musqR_nonneg j
    have : (0 : ℝ) ≤ (m : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hB : ∑ d ∈ D, ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d) ≤
      ∑ m ∈ n.divisors.filter (1 < ·), ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m *
        (1.64 * √((n / m : ℕ) : ℝ)) := by
    calc _ = ∑ d ∈ D, ∑ m ∈ d.divisors.filter (fun m => 1 < m ∧ m < d), G m (d / m) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd0 : d ≠ 0 := by
            have := (Finset.mem_filter.mp hd).2.1; omega
          rw [inner_reindex ε hd0]
      _ ≤ ∑ d ∈ n.divisors, ∑ m ∈ d.divisors.filter (1 < ·), G m (d / m) := by
          refine (Finset.sum_le_sum fun d _ => Finset.sum_le_sum_of_subset_of_nonneg
            (fun m hm => ?_) (fun m _ _ => hG0 m _)).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun d _ _ => Finset.sum_nonneg fun m _ => hG0 m _))
          simp only [Finset.mem_filter] at hm ⊢
          exact ⟨hm.1, hm.2.1⟩
      _ = ∑ m ∈ n.divisors.filter (1 < ·), ∑ j ∈ (n / m).divisors, G m j := swap_sum hn0 G
      _ ≤ _ := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_filter.mp hm
          have hmn : m ∣ n := Nat.dvd_of_mem_divisors hm'.1
          have hk0 : n / m ≠ 0 := by
            have := Nat.div_pos (Nat.le_of_dvd (by omega) hmn) (by omega : 0 < m); omega
          simp only [G]
          have e : ∑ j ∈ (n / m).divisors, musqR j * ((m : ℝ) ^ ε) *
              (BSCert.X0Band.Hord m : ℝ) / m =
              ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m * ∑ j ∈ (n / m).divisors, musqR j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
          rw [e]
          have : (0 : ℝ) ≤ (m : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
          exact mul_le_mul_of_nonneg_left (sum_musqR_le hk0) (by positivity)
  -- (iii) each term `≤ 1.64 H_ord(m) m^{-1.77} n^{-0.2} · n`
  have hC : ∑ m ∈ n.divisors.filter (1 < ·), ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m *
        (1.64 * √((n / m : ℕ) : ℝ)) ≤ n * (1.64 * 13.1 * (n : ℝ) ^ (-0.2 : ℝ)) := by
    have hpt : ∀ m ∈ n.divisors.filter (1 < ·), ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m *
        (1.64 * √((n / m : ℕ) : ℝ)) ≤
        n * (1.64 * ((BSCert.X0Band.Hord m : ℝ) * (m : ℝ) ^ (-1.77 : ℝ)) *
          (n : ℝ) ^ (-0.2 : ℝ)) := by
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hmn : m ∣ n := Nat.dvd_of_mem_divisors hm'.1
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      have hmle : (m : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (by omega) hmn
      have hdiv : ((n / m : ℕ) : ℝ) = (n : ℝ) / m := by
        rw [Nat.cast_div hmn (by positivity)]
      rw [hdiv]
      have hr := rpow_tail_le hε0 (by linarith) hm1 hmle
      have hH : (0 : ℝ) ≤ (BSCert.X0Band.Hord m : ℝ) := Nat.cast_nonneg _
      have e1 : ((m : ℝ) ^ ε) * (BSCert.X0Band.Hord m : ℝ) / m * (1.64 * √((n : ℝ) / m)) =
          n * (1.64 * (BSCert.X0Band.Hord m : ℝ) * ((m : ℝ) ^ ε / m * √((n : ℝ) / m) / n)) := by
        field_simp
      rw [e1]
      apply mul_le_mul_of_nonneg_left _ hnpos.le
      have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 1.64 *
        (BSCert.X0Band.Hord m : ℝ))
      linarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    have h1 := sum_Hord_177_le n
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-0.2 : ℝ) := Real.rpow_nonneg hnpos.le _
    nlinarith
  -- (iv) numerics: `n^{0.2} ≥ 15`, `√n ≥ 1000`
  have hrp : (n : ℝ) ^ (-0.2 : ℝ) ≤ 1 / 15 := by
    have h1 : (15 : ℝ) ^ (5 : ℕ) ≤ n := by norm_num; linarith
    have h2 : ((15 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) ≤ (n : ℝ) ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((15 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) = 15 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h3] at h2
    rw [Real.rpow_neg hnpos.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hsq : 1000 ≤ √(n : ℝ) := by
    rw [show (1000 : ℝ) = √(10 ^ 6) by
      rw [show ((10 : ℝ) ^ 6) = 1000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hnR.le
  have hsqn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnpos.le
  have hfirst : (1 / 2 + 1.64 * √n) / n ≤ 0.0017 := by
    rw [div_le_iff₀ hnpos]; nlinarith
  -- assemble
  unfold BrN betaD
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hS0 : 0 ≤ ∑ d ∈ D, ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d) :=
    Finset.sum_nonneg fun d _ => betaD_sum_nonneg ε d
  have hBC := hB.trans hC
  have h1 : 1 / (n : ℝ) * (musqR n / 2 + (∑ d ∈ D, musqR d + 1 / 4 * lam0 *
      ∑ d ∈ D, ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) *
          ((e : ℝ) / d))) ≤
      (1 / 2 + 1.64 * √n) / n + 1 / 4 * lam0 * (1.64 * 13.1 * (n : ℝ) ^ (-0.2 : ℝ)) := by
    have k1 : 1 / 4 * lam0 * (∑ d ∈ D, ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)) ≤
        1 / 4 * lam0 * (n * (1.64 * 13.1 * (n : ℝ) ^ (-0.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hBC (by positivity)
    rw [div_add' _ _ _ hnpos.ne', one_div_mul_eq_div, div_le_div_iff_of_pos_right hnpos]
    nlinarith
  refine h1.trans ?_
  have h2 : 0 ≤ (n : ℝ) ^ (-0.2 : ℝ) := Real.rpow_nonneg hnpos.le _
  nlinarith

/-- **`Br(n) ≤ 5/12` for every `n ≥ 2`** (Proposition 5.31(i): the certified range `n ≤ 10⁶`
and the analytic tail), when `λ₀ (10⁶)^ε ≤ 1.0001`. -/
theorem BrN_le {ε lam0 : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 4 / 1000000) (hlam0 : 0 ≤ lam0)
    (hlam1 : lam0 ≤ 1.001) (hlε : lam0 * ((10 : ℝ) ^ 6) ^ ε ≤ 1.0001) {n : ℕ} (hn : 2 ≤ n) :
    BrN ε lam0 n ≤ 5 / 12 := by
  rcases le_or_gt n (10 ^ 6) with h | h
  · refine (BrN_le_Bx hε0 hlam0 hlε hn h).trans ?_
    have := (BSCert.X0Band.Bx_le_five_twelfths hn h).1
    have h2 : ((BSCert.X0Band.Bx n : ℚ) : ℝ) ≤ ((5 / 12 : ℚ) : ℝ) := Rat.cast_le.mpr this
    rw [show ((5 / 12 : ℚ) : ℝ) = 5 / 12 by norm_num] at h2
    exact h2
  · exact BrN_le_tail hε0 hε hlam0 hlam1 h

end KR.XB7

end
