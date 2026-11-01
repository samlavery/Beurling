module

public import RequestProject.Beurling.BaseRange.AbelFin
public import RequestProject.Beurling.GenLemma51Final
public import RequestProject.BSCert.Finite.ChebN
public import RequestProject.Beurling.Construction.HBSEps
public import RequestProject.Beurling.BaseRange.Window

/-!
# Steps 1–2 of the proof of Lemma 7.3(b): from the element count to the prime count

Let `P` be a Beurling system and `Δ = N_𝒩 - ⌊·⌋`. Step 2 of the proof of Lemma 7.3(b) derives
`|ψ_𝒩(t) - ψ(t)| ≪ κ t log² t` from `|Δ| ≪ κ t` through the Chebyshev identity and Möbius
inversion. Here (`psi_diff_le`): if `|Δ(v)| ≤ A v` on `[0, T]`, `T ≤ Z` and (HBS) holds on
`[1, Z]`, then for `1 ≤ t ≤ T`

  `|ψ_𝒩(t) - ψ(t)| ≤ 2A t (log t + 1)²`.

The proof (a variant of the paper's, with the Möbius function of `ℕ` instead of that of `𝒩`):

* `sum_psi_div` (both systems): `∑_{n ≤ t} ψ(t/n) = ∑_{p^k ≤ t} log p ⌊t/p^k⌋`; with the
  Chebyshev identity `ℓ_𝒩(t) = ∑_{p^k ≤ t} log p N(t/p^k)` (`chebyshev_identity`) and
  `log⌊t⌋! = ∑_{d ≤ t} Λ(d)⌊t/d⌋` this gives `∑_{n ≤ t} (ψ_𝒩 - ψ)(t/n) = h(t)` with
  `h(t) = (ℓ_𝒩(t) - log⌊t⌋!) - ∑_{p^k ≤ t} log p Δ(t/p^k)` (`sum_psiDiff_eq`);
* `|h(s)| ≤ 2A s (log s + 1)` (`abs_hdiff_le`): the first part by Abel summation
  (`BaseRange.abel_fin`), the second by Lemma 5.1(ii) (`mertensS ≤ log + 0.43`);
* Möbius inversion for functions of a real variable (`moebius_inversion_real`).

Step 1 (`delta_le_of_hbsEps`): the bound `|Δ(v)| ≤ hbsEps(v) v` of (HBS) on `Good(<x)`
(`BModel.hbs_local`; `hbsEps(v) = 10 v^{-2/5} + min(κ + (κX₀ + 1)/v, …)`) gives `|Δ(v)| ≤ 4κ v`
on `[X₀/2, ∞)`; so `A = 4κ` and `|ψ_𝒩 - ψ| ≤ 8κ t (log t + 1)²`.
-/

@[expose] public section

open Real Finset MeasureTheory intervalIntegral BeurlingSystem
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace BaseRange

/-! ### Möbius inversion for functions of a real variable -/

lemma sum_moebius_divisors_eq {k : ℕ} (hk : 1 ≤ k) :
    ∑ d ∈ k.divisors, (μ d : ℝ) = if k = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at this
  have h2 : ∑ d ∈ k.divisors, (μ d : ℝ) = ((∑ d ∈ k.divisors, μ d : ℤ) : ℝ) := by push_cast; rfl
  rw [h2, this]
  split_ifs with h
  · subst h; simp
  · rw [ArithmeticFunction.one_apply_ne h]; simp

/-- **Möbius inversion** (real variable): `F(t) = ∑_{n ≤ t} μ(n) G(t/n)`,
`G(s) = ∑_{m ≤ s} F(s/m)`, for `t ≥ 1`. -/
theorem moebius_inversion_real (F : ℝ → ℝ) {t : ℝ} (ht : 1 ≤ t) :
    F t = ∑ n ∈ Icc 1 ⌊t⌋₊, (μ n : ℝ) * ∑ m ∈ Icc 1 ⌊t / n⌋₊, F (t / n / m) := by
  classical
  set X := ⌊t⌋₊ with hX
  have hX1 : 1 ≤ X := Nat.le_floor (by exact_mod_cast ht)
  -- the pairs `(n, m)` with `nm ≤ X`
  set s := (Icc 1 X ×ˢ Icc 1 X).filter fun q : ℕ × ℕ => q.1 * q.2 ≤ X
  set H : ℕ × ℕ → ℝ := fun q => (μ q.1 : ℝ) * F (t / (q.1 * q.2 : ℕ))
  have h1 : ∑ n ∈ Icc 1 X, (μ n : ℝ) * ∑ m ∈ Icc 1 ⌊t / n⌋₊, F (t / n / m) = ∑ q ∈ s, H q := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [Finset.mul_sum, Nat.floor_div_natCast, ← hX, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext m
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, h2.trans (Nat.div_le_self _ _)⟩, ?_⟩
        calc n * m ≤ n * (X / n) := Nat.mul_le_mul_left _ h2
          _ ≤ X := Nat.mul_div_le X n
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm n m])⟩
    · intro m _
      simp only [H]
      congr 2
      push_cast; rw [div_div]
  rw [h1]
  have h2 : ∑ q ∈ s, H q = ∑ k ∈ Icc 1 X, ∑ q ∈ s.filter (fun q => q.1 * q.2 = k), H q := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro q hq
    simp only [s, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    simp only [Finset.mem_Icc]
    exact ⟨by nlinarith [hq.1.1.1, hq.1.2.1], hq.2⟩
  rw [h2]
  have h3 : ∀ k ∈ Icc 1 X, ∑ q ∈ s.filter (fun q => q.1 * q.2 = k), H q =
      (∑ d ∈ k.divisors, (μ d : ℝ)) * F (t / k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkX : k ≤ X := (Finset.mem_Icc.mp hk).2
    rw [Finset.sum_mul]
    apply Finset.sum_nbij' (fun q => q.1) (fun d => (d, k / d))
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq
      simp only [Nat.mem_divisors]
      exact ⟨⟨q.2, hq.2.symm⟩, by omega⟩
    · intro d hd
      simp only [Nat.mem_divisors] at hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      have hdk : d * (k / d) = k := Nat.mul_div_cancel' hd.1
      have hq0 : 1 ≤ k / d := by
        rcases Nat.eq_zero_or_pos (k / d) with h | h
        · rw [h, mul_zero] at hdk; omega
        · exact h
      simp only [s, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      refine ⟨⟨⟨⟨hd0, (Nat.le_of_dvd (by omega) hd.1).trans hkX⟩, hq0,
        (Nat.div_le_self _ _).trans hkX⟩, by omega⟩, hdk⟩
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq
      ext
      · rfl
      · simp only; rw [← hq.2, Nat.mul_div_cancel_left _ (by omega)]
    · intro d hd; rfl
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq
      simp only [H, hq.2]
  rw [Finset.sum_congr rfl h3]
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hX1⟩)]
  · rw [sum_moebius_divisors_eq le_rfl]; simp
  · intro k hk hk1
    rw [sum_moebius_divisors_eq (Finset.mem_Icc.mp hk).1, if_neg hk1, zero_mul]

/-! ### The Chebyshev sums -/

/-- `∑_{n ≤ t} ψ_𝒩(t/n) = ∑_{p^k ≤ t} log p ⌊t/p^k⌋`. -/
lemma sum_psi_div (P : BeurlingSystem) {t : ℝ} (ht : 0 ≤ t) :
    ∑ n ∈ Icc 1 ⌊t⌋₊, P.psi (t / n) =
      ∑ jk ∈ P.pps t, Real.log (P.p jk.1) * (⌊t / P.p jk.1 ^ (jk.2 + 1)⌋₊ : ℝ) := by
  classical
  have hsub : ∀ n ∈ Icc 1 ⌊t⌋₊, P.pps (t / n) =
      (P.pps t).filter (fun jk => P.p jk.1 ^ (jk.2 + 1) ≤ t / n) := by
    intro n hn
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    ext jk
    simp only [mem_pps, Finset.mem_filter]
    constructor
    · intro h; exact ⟨h.trans (div_le_self ht hn0), h⟩
    · intro h; exact h.2
  rw [Finset.sum_congr rfl fun n hn => by rw [P.psi_eq_sum, hsub n hn]]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun jk hjk => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have ha : 0 < P.p jk.1 ^ (jk.2 + 1) := P.pp_pos jk
  have hat : P.p jk.1 ^ (jk.2 + 1) ≤ t := P.mem_pps.mp hjk
  have e : (Icc 1 ⌊t⌋₊).filter (fun n : ℕ => P.p jk.1 ^ (jk.2 + 1) ≤ t / n) =
      Icc 1 ⌊t / P.p jk.1 ^ (jk.2 + 1)⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      refine ⟨h1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ ha]; rw [le_div_iff₀ hn0] at h3; linarith
    · rintro ⟨h1, h2⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have h2' : (n : ℝ) ≤ t / P.p jk.1 ^ (jk.2 + 1) := (Nat.cast_le.mpr h2).trans
        (Nat.floor_le (div_nonneg ht ha.le))
      refine ⟨⟨h1, Nat.le_floor ?_⟩, ?_⟩
      · have : t / P.p jk.1 ^ (jk.2 + 1) ≤ t := by
          have h1' : 1 ≤ P.p jk.1 ^ (jk.2 + 1) := one_le_pow₀ (P.one_lt _).le
          exact div_le_self ht h1'
        linarith
      · rw [le_div_iff₀ hn0]; rw [le_div_iff₀ ha] at h2'; linarith
  rw [e, Nat.card_Icc]; simp

/-- The swap `∑_{n ≤ X} ∑_{d ≤ X/n} f(d) = ∑_{d ≤ X} f(d) ⌊X/d⌋`. -/
lemma sum_swap_div (f : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 (X / n), f d = ∑ d ∈ Icc 1 X, f d * ((X / d : ℕ) : ℝ) := by
  classical
  have e : ∀ n ∈ Icc 1 X, Icc 1 (X / n) = (Icc 1 X).filter (fun d => n * d ≤ X) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    ext d
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2.trans (Nat.div_le_self _ _)⟩, ?_⟩
      calc n * d ≤ n * (X / n) := Nat.mul_le_mul_left _ h2
        _ ≤ X := Nat.mul_div_le X n
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm n d])⟩
  rw [Finset.sum_congr rfl fun n hn => by rw [e n hn]]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have e2 : (Icc 1 X).filter (fun n => n * d ≤ X) = Icc 1 (X / d) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr h2⟩
    · rintro ⟨h1, h2⟩
      have := (Nat.le_div_iff_mul_le (by omega)).mp h2
      exact ⟨⟨h1, h2.trans (Nat.div_le_self _ _)⟩, this⟩
  rw [e2, Nat.card_Icc]; simp

/-- `∑_{n ≤ t} ψ(t/n) = log ⌊t⌋!` for the rational primes. -/
lemma sum_psiNat_div (t : ℝ) :
    ∑ n ∈ Icc 1 ⌊t⌋₊, Chebyshev.psi (t / n) = Real.log (⌊t⌋₊.factorial : ℝ) := by
  classical
  rw [← BSCert.FiniteN.chebL_eq_log_factorial]
  unfold BSCert.FiniteN.chebL Chebyshev.psi
  set X := ⌊t⌋₊
  have hf : ∀ n ∈ Icc 1 X, Ioc 0 ⌊t / n⌋₊ = Icc 1 (X / n) := by
    intro n _; rw [Nat.floor_div_natCast]; rfl
  rw [Finset.sum_congr rfl fun n hn => by rw [hf n hn], sum_swap_div]
  apply Finset.sum_subset
  · intro d hd
    have := (Finset.mem_Icc.mp hd).2
    exact Finset.mem_range.mpr (by omega)
  · intro d hd hd'
    simp only [Finset.mem_range, Finset.mem_Icc] at hd hd'
    have : d = 0 := by omega
    subst this; simp

lemma log_factorial_eq (X : ℕ) : Real.log (X.factorial : ℝ) = ∑ n ∈ Icc 1 X, Real.log n := by
  rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro n hn; have := (Finset.mem_Ico.mp hn).1; positivity

/-- `ℓ_𝒩(t) - log ⌊t⌋! = Δ(t) log t - ∫_{1/2}^t Δ(s)/s ds`, `Δ = N - ⌊·⌋` (Abel summation). -/
lemma ellN_sub_logfact (P : BeurlingSystem) {t : ℝ} (ht : 1 ≤ t) :
    P.ellN t - Real.log (⌊t⌋₊.factorial : ℝ) =
      (P.N t - ⌊t⌋₊) * Real.log t - ∫ s in (1 / 2 : ℝ)..t, (P.N s - (⌊s⌋₊ : ℝ)) / s := by
  classical
  have hab : (1 / 2 : ℝ) ≤ t := by linarith
  have hder : ∀ s ∈ Set.Icc (1 / 2 : ℝ) t, HasDerivAt Real.log (s⁻¹) s := fun s hs =>
    Real.hasDerivAt_log (by linarith [hs.1])
  have hcont : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc (1 / 2 : ℝ) t) :=
    continuousOn_inv₀.mono fun s hs => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hs.1]
  -- the system
  have hP := abel_fin (P.elems t) P.val (fun _ => (1 : ℝ)) hab
    (fun e he => ⟨by linarith [P.one_le_val e], P.mem_elems.mp he⟩) Real.log (fun s => s⁻¹)
    hder hcont
  -- `ℕ`
  have hN := abel_fin (Icc 1 ⌊t⌋₊) (fun n : ℕ => (n : ℝ)) (fun _ => (1 : ℝ)) hab
    (fun n hn => ⟨by have : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
                     linarith,
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))⟩)
    Real.log (fun s => s⁻¹) hder hcont
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hP hN
  have hCP : ∀ s ∈ Set.uIcc (1 / 2 : ℝ) t,
      (∑ e ∈ P.elems t, if P.val e ≤ s then (1 : ℝ) else 0) * s⁻¹ = P.N s * s⁻¹ := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    congr 1
    rw [Finset.sum_boole, P.N_eq_card]
    congr 2
    ext e; simp only [Finset.mem_filter, P.mem_elems]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hs.2, h⟩⟩
  have hCN : ∀ s ∈ Set.uIcc (1 / 2 : ℝ) t,
      (∑ n ∈ Icc 1 ⌊t⌋₊, if (n : ℝ) ≤ s then (1 : ℝ) else 0) * s⁻¹ = (⌊s⌋₊ : ℝ) * s⁻¹ := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    congr 1
    rw [Finset.sum_boole]
    have : (Icc 1 ⌊t⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ s) = Icc 1 ⌊s⌋₊ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
      · rintro ⟨h1, h2⟩
        have h3 : (n : ℝ) ≤ s := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith [hs.1]))
        exact ⟨⟨h1, Nat.le_floor (h3.trans hs.2)⟩, h3⟩
    rw [this, Nat.card_Icc]; simp
  rw [intervalIntegral.integral_congr hCP] at hP
  rw [intervalIntegral.integral_congr hCN] at hN
  have hiP : IntervalIntegrable (fun s => P.N s * s⁻¹) volume (1 / 2) t :=
    (P.N_mono.intervalIntegrable).mul_continuousOn (by rw [Set.uIcc_of_le hab]; exact hcont)
  have hiN : IntervalIntegrable (fun s : ℝ => (⌊s⌋₊ : ℝ) * s⁻¹) volume (1 / 2) t := by
    have hm : Monotone (fun s : ℝ => (⌊s⌋₊ : ℝ)) := fun a b h => by
      simp only; exact_mod_cast Nat.floor_le_floor h
    exact hm.intervalIntegrable.mul_continuousOn (by rw [Set.uIcc_of_le hab]; exact hcont)
  have hint : ∫ s in (1 / 2 : ℝ)..t, (P.N s - (⌊s⌋₊ : ℝ)) / s =
      (∫ s in (1 / 2 : ℝ)..t, P.N s * s⁻¹) - ∫ s in (1 / 2 : ℝ)..t, (⌊s⌋₊ : ℝ) * s⁻¹ := by
    rw [← intervalIntegral.integral_sub hiP hiN]
    congr 1; funext s; ring
  unfold BeurlingSystem.ellN
  rw [log_factorial_eq, hP, hN, hint, P.N_eq_card]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-- The sum `∑_{n ≤ t} (ψ_𝒩 - ψ)(t/n)`. -/
theorem sum_psiDiff_eq (P : BeurlingSystem) {t : ℝ} (ht : 0 ≤ t) :
    ∑ n ∈ Icc 1 ⌊t⌋₊, (P.psi (t / n) - Chebyshev.psi (t / n)) =
      (P.ellN t - Real.log (⌊t⌋₊.factorial : ℝ)) -
        ∑ jk ∈ P.pps t, Real.log (P.p jk.1) *
          (P.N (t / P.p jk.1 ^ (jk.2 + 1)) - ⌊t / P.p jk.1 ^ (jk.2 + 1)⌋₊) := by
  rw [Finset.sum_sub_distrib, sum_psi_div P ht, sum_psiNat_div, P.chebyshev_identity]
  rw [show ∀ a b c : ℝ, a - c = (b - c) - (b - a) from fun a b c => by ring]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun jk _ => ?_
  ring

/-- `|h(s)| ≤ 2A s (log s + 1)` under `|Δ(v)| ≤ A v` on `[0, s]` and (HBS) on `[1, Z]`. -/
theorem abs_hdiff_le {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) {A s : ℝ} (hA : 0 ≤ A) (hs : 1 ≤ s) (hsZ : s ≤ Z)
    (hΔ : ∀ v, 0 ≤ v → v ≤ s → |P.N v - ⌊v⌋₊| ≤ A * v) :
    |(P.ellN s - Real.log (⌊s⌋₊.factorial : ℝ)) -
        ∑ jk ∈ P.pps s, Real.log (P.p jk.1) *
          (P.N (s / P.p jk.1 ^ (jk.2 + 1)) - ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊)| ≤
      2 * A * s * (Real.log s + 1) := by
  have hs0 : 0 < s := by linarith
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs
  rw [ellN_sub_logfact P hs]
  -- the Abel part
  have h1 : |(P.N s - ⌊s⌋₊) * Real.log s| ≤ A * s * Real.log s := by
    rw [abs_mul, abs_of_nonneg hls]
    exact mul_le_mul_of_nonneg_right (hΔ s hs0.le le_rfl) hls
  have h2 : |∫ v in (1 / 2 : ℝ)..s, (P.N v - (⌊v⌋₊ : ℝ)) / v| ≤ A * s := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    have hc : A * s ≥ ∫ _ in (1 / 2 : ℝ)..s, A := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have : (s - 1 / 2) * A = A * s - A / 2 := by ring
      linarith
    refine le_trans ?_ hc
    have hs2 : (1 / 2 : ℝ) ≤ s := by linarith
    apply intervalIntegral.integral_mono_on hs2
    · have := (intervalIntegrable_E_div_sq P (by norm_num : (0:ℝ) < 1 / 2) hs2)
      -- `|Δ/v|` is integrable: `Δ/v = (Δ/v²) · v`
      have hi : IntervalIntegrable (fun v => (P.N v - (⌊v⌋₊ : ℝ)) / v) volume (1 / 2) s := by
        have hc : ContinuousOn (fun v : ℝ => v) (Set.uIcc (1 / 2) s) := continuousOn_id
        refine (this.mul_continuousOn hc).congr (fun v hv => ?_)
        rw [Set.uIoc_of_le (by linarith)] at hv
        have hv0 : 0 < v := by linarith [hv.1]
        field_simp
      exact hi.abs
    · exact _root_.intervalIntegrable_const
    · intro v hv
      have hv0 : 0 < v := by linarith [hv.1]
      rw [abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
      exact hΔ v hv0.le hv.2
  -- the prime-power part
  have h3 : |∑ jk ∈ P.pps s, Real.log (P.p jk.1) *
      (P.N (s / P.p jk.1 ^ (jk.2 + 1)) - ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊)| ≤
      A * s * (Real.log s + 0.43) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hM := (h.mertensS_sub_log_mem hs hsZ).2
    have hle : ∀ jk ∈ P.pps s, |Real.log (P.p jk.1) *
        (P.N (s / P.p jk.1 ^ (jk.2 + 1)) - ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊)| ≤
        A * s * (Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1)) := by
      intro jk _
      have ha := P.pp_pos jk
      have hl : 0 ≤ Real.log (P.p jk.1) := Real.log_nonneg (P.one_lt _).le
      have ha1 : 1 ≤ P.p jk.1 ^ (jk.2 + 1) := one_le_pow₀ (P.one_lt _).le
      rw [abs_mul, abs_of_nonneg hl]
      have := hΔ (s / P.p jk.1 ^ (jk.2 + 1)) (by positivity) (div_le_self hs0.le ha1)
      calc Real.log (P.p jk.1) * |P.N (s / P.p jk.1 ^ (jk.2 + 1)) -
            ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊| ≤
            Real.log (P.p jk.1) * (A * (s / P.p jk.1 ^ (jk.2 + 1))) :=
            mul_le_mul_of_nonneg_left this hl
        _ = A * s * (Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1)) := by ring
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    have : ∑ jk ∈ P.pps s, Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) = P.mertensS s := rfl
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc |_ - _ - _| ≤ |(P.N s - ⌊s⌋₊) * Real.log s| +
        |∫ v in (1 / 2 : ℝ)..s, (P.N v - (⌊v⌋₊ : ℝ)) / v| +
        |∑ jk ∈ P.pps s, Real.log (P.p jk.1) *
          (P.N (s / P.p jk.1 ^ (jk.2 + 1)) - ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊)| := by
        have := abs_sub (((P.N s - ⌊s⌋₊) * Real.log s) -
          ∫ v in (1 / 2 : ℝ)..s, (P.N v - (⌊v⌋₊ : ℝ)) / v) (∑ jk ∈ P.pps s, Real.log (P.p jk.1) *
          (P.N (s / P.p jk.1 ^ (jk.2 + 1)) - ⌊s / P.p jk.1 ^ (jk.2 + 1)⌋₊))
        have := abs_sub ((P.N s - ⌊s⌋₊) * Real.log s)
          (∫ v in (1 / 2 : ℝ)..s, (P.N v - (⌊v⌋₊ : ℝ)) / v)
        linarith
    _ ≤ A * s * Real.log s + A * s + A * s * (Real.log s + 0.43) := by linarith
    _ ≤ 2 * A * s * (Real.log s + 1) := by nlinarith

/-- **Step 2 of the proof of Lemma 7.3(b)**: under (HBS) on `[1, Z]` and `|Δ(v)| ≤ A v` on
`[0, T]`, `T ≤ Z`, for `1 ≤ t ≤ T`: `|ψ_𝒩(t) - ψ(t)| ≤ 2A t (log t + 1)²`. -/
theorem psi_diff_le {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) {A T : ℝ} (hA : 0 ≤ A) (hTZ : T ≤ Z)
    (hΔ : ∀ v, 0 ≤ v → v ≤ T → |P.N v - ⌊v⌋₊| ≤ A * v) {t : ℝ} (ht : 1 ≤ t) (htT : t ≤ T) :
    |P.psi t - Chebyshev.psi t| ≤ 2 * A * t * (Real.log t + 1) ^ 2 := by
  have ht0 : 0 < t := by linarith
  set F : ℝ → ℝ := fun s => P.psi s - Chebyshev.psi s
  have hinv := moebius_inversion_real F ht
  change |F t| ≤ _
  rw [hinv]
  have hnb : ∀ n ∈ Icc 1 ⌊t⌋₊, 1 ≤ t / n ∧ t / n ≤ t := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnt : (n : ℝ) ≤ t := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le ht0.le)
    exact ⟨by rw [le_div_iff₀ (by linarith)]; linarith, div_le_self ht0.le hn1⟩
  have hterm : ∀ n ∈ Icc 1 ⌊t⌋₊, |(μ n : ℝ) * ∑ m ∈ Icc 1 ⌊t / n⌋₊, F (t / n / m)| ≤
      2 * A * (t / n) * (Real.log t + 1) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hnb n hn
    have hsum := sum_psiDiff_eq P (t := t / n) (by linarith)
    have hb := abs_hdiff_le h hA h1 (h2.trans (htT.trans hTZ))
      (fun v hv0 hv => hΔ v hv0 (hv.trans (h2.trans htT)))
    rw [abs_mul]
    have hμ : |(μ n : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      exact_mod_cast this
    have hs : |∑ m ∈ Icc 1 ⌊t / n⌋₊, F (t / n / m)| ≤ 2 * A * (t / n) * (Real.log (t / n) + 1) := by
      simp only [F]; rw [hsum]; exact hb
    have hlog : Real.log (t / n) ≤ Real.log t := Real.log_le_log (by linarith) h2
    have hl0 : 0 ≤ Real.log (t / n) := Real.log_nonneg h1
    calc |(μ n : ℝ)| * |∑ m ∈ Icc 1 ⌊t / n⌋₊, F (t / n / m)| ≤
          1 * (2 * A * (t / n) * (Real.log (t / n) + 1)) :=
          mul_le_mul hμ hs (abs_nonneg _) (by norm_num)
      _ ≤ 2 * A * (t / n) * (Real.log t + 1) := by
          rw [one_mul]
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  have e : ∑ n ∈ Icc 1 ⌊t⌋₊, 2 * A * (t / n) * (Real.log t + 1) =
      2 * A * t * (Real.log t + 1) * ∑ n ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) / n := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [e]
  have hH := natHarm_le_one_add_log ht
  have hl0 : 0 ≤ Real.log t + 1 := by linarith [Real.log_nonneg ht]
  have : 2 * A * t * (Real.log t + 1) * ∑ n ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) / n ≤
      2 * A * t * (Real.log t + 1) * (1 + Real.log t) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

/-- **Step 1 of the proof of Lemma 7.3(b)**: the bound of (HBS) on `Good(<x)`,
`|Δ(v)| ≤ hbsEps(v) v` (`BModel.hbs_local`), gives `|Δ(v)| ≤ 4κ v` for `v ≥ X₀/2`. -/
theorem delta_le_of_hbsEps {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {v Δv : ℝ}
    (hv : (X0 : ℝ) / 2 ≤ v) (hΔ : |Δv| ≤ Construction.hbsEps X0 v * v) :
    |Δv| ≤ 4 * Construction.kappaParam X0 * v := by
  set κ := Construction.kappaParam X0 with hκdef
  obtain ⟨hκ0, hκ1⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hv0 : 0 < v := by linarith
  refine hΔ.trans ?_
  unfold Construction.hbsEps
  have hmin : min (κ + (κ * X0 + 1) / v)
      ((Rankin.smoothCount X0 (2 * v) : ℝ) / v) ≤ κ + (κ * X0 + 1) / v := min_le_left _ _
  -- `10 v^{-2/5} + 1/v ≤ κ`
  have hsmall : 10 * v ^ (-(2 / 5 : ℝ)) + 1 / v ≤ κ := by
    have h1 : v ^ (-(2 / 5 : ℝ)) ≤ ((X0 : ℝ) / 2) ^ (-(2 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hv (by norm_num)
    have h2 : ((X0 : ℝ) / 2) ^ (-(2 / 5 : ℝ)) =
        Real.exp (-(2 / 5) * (Real.log X0 - Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_div hX0.ne' (by norm_num)]; ring_nf
    have h3 : κ = Real.exp ((-5 / 12 + 2 * 0.01) * Real.log X0) := by
      rw [hκdef, kappa_eq_exp hX0]; ring_nf
    have h4 : 1 / v ≤ 2 / X0 := by
      rw [div_le_div_iff₀ hv0 hX0]; linarith
    have h5 : 2 / (X0 : ℝ) = Real.exp (Real.log 2 - Real.log X0) := by
      rw [Real.exp_sub, Real.exp_log hX0, Real.exp_log (by norm_num)]
    -- compare exponents: `κ ≥ 11 · max(...)`
    have hl2 := Real.log_two_lt_d9
    have hA : 10 * Real.exp (-(2 / 5) * (Real.log X0 - Real.log 2)) + Real.exp (Real.log 2 -
        Real.log X0) ≤ Real.exp ((-5 / 12 + 2 * 0.01) * Real.log X0) := by
      have hE1 : Real.exp (-(2 / 5) * (Real.log X0 - Real.log 2)) ≤
          Real.exp ((-5 / 12 + 2 * 0.01) * Real.log X0) * Real.exp (-(1 / 400) * Real.log X0) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have hE2 : Real.exp (Real.log 2 - Real.log X0) ≤
          Real.exp ((-5 / 12 + 2 * 0.01) * Real.log X0) * Real.exp (-(1 / 400) * Real.log X0) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have hE3 : Real.exp (-(1 / 400) * Real.log X0) ≤ 1 / 11 := by
        have h11 : (11 : ℝ) ≤ Real.exp (1 / 400 * Real.log X0) := by
          have := Real.add_one_le_exp (1 / 400 * Real.log X0); nlinarith
        rw [neg_mul, Real.exp_neg, show (1 : ℝ) / 11 = (11 : ℝ)⁻¹ by norm_num]
        exact inv_anti₀ (by norm_num) h11
      have hK := Real.exp_pos ((-5 / 12 + 2 * 0.01) * Real.log X0)
      nlinarith
    rw [h3]
    have := mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) (by norm_num : (0 : ℝ) ≤ 10)
    linarith
  have hκX : κ * X0 ≤ 2 * κ * v := by nlinarith
  calc (10 * v ^ (-(2 / 5 : ℝ)) + min (κ + (κ * X0 + 1) / v)
        ((Rankin.smoothCount X0 (2 * v) : ℝ) / v)) * v
      ≤ (10 * v ^ (-(2 / 5 : ℝ)) + (κ + (κ * X0 + 1) / v)) * v := by
        apply mul_le_mul_of_nonneg_right _ hv0.le; linarith
    _ = (10 * v ^ (-(2 / 5 : ℝ)) + 1 / v) * v + κ * v + κ * X0 := by field_simp; ring
    _ ≤ κ * v + κ * v + 2 * κ * v := by
        have := mul_le_mul_of_nonneg_right hsmall hv0.le
        linarith
    _ = 4 * κ * v := by ring

end BaseRange
