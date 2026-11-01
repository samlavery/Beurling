module

public import RequestProject.BSCert.Consts.ZetaCert
public import RequestProject.BSCert.Finite.X0Band

/-!
# Ordered factorisations: `∑_{m ≥ 1} H_ord(m) m^{-s} = 1/(2 - ζ(s))`

Section 5.5.2 of the paper uses, for `N = ℕ`, the Dirichlet series identity
`∑_{m ≥ 1} H_ord(m) m^{-s} = 1/(2 - ζ(s))` for real `s` with `ζ(s) < 2` (that is, `s > ρ₀`).
So `A(s) = 1/(2 - ζ(s)) - 1 = ∑_{m ≥ 2} H_ord(m) m^{-s}`, which is how `consts.py` evaluates
`A₀(0.03) = A(1.97)` and `A(1.8 - 3·10⁻⁶)`.

Proof: `H_ord = δ + H_ord ⋆ 1_{≥2}` (Dirichlet convolution). Truncating `H_ord` at `N` gives
`S_N ≤ 1 + S_N (ζ(s) - 1)`, so the partial sums are bounded by `1/(2 - ζ(s))` and the series
converges; then the convolution identity of Mathlib's `LSeries` gives `H = 1 + H (ζ(s) - 1)`.
-/

@[expose] public section

namespace BSCert.Consts

open Real LSeries Finset BSCert.X0Band

/-- Real Dirichlet term `f(n) n^{-s}` (it is `0` at `n = 0`). -/
noncomputable def rterm (f : ℕ → ℕ) (s : ℝ) (n : ℕ) : ℝ := (f n : ℝ) * (n : ℝ) ^ (-s)

lemma rterm_nonneg (f : ℕ → ℕ) (s : ℝ) (n : ℕ) : 0 ≤ rterm f s n := by
  unfold rterm; have := Real.rpow_nonneg (n.cast_nonneg (α := ℝ)) (-s); positivity

lemma term_natCast (f : ℕ → ℕ) {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    term (fun n => (f n : ℂ)) (s : ℂ) n = ((rterm f s n : ℝ) : ℂ) := by
  rw [term_def]
  split_ifs with hn
  · subst hn; simp [rterm, Real.zero_rpow (neg_ne_zero.mpr hs)]
  · have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    unfold rterm
    rw [Real.rpow_neg hn0, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow hn0]
    push_cast
    rw [div_eq_mul_inv]

lemma LSeries_natCast (f : ℕ → ℕ) {s : ℝ} (hs : s ≠ 0) :
    LSeries (fun n => (f n : ℂ)) (s : ℂ) = ((∑' n, rterm f s n : ℝ) : ℂ) := by
  unfold LSeries
  simp_rw [term_natCast f hs]
  rw [Complex.ofReal_tsum]

lemma LSeriesSummable_natCast_iff (f : ℕ → ℕ) {s : ℝ} (hs : s ≠ 0) :
    LSeriesSummable (fun n => (f n : ℂ)) (s : ℂ) ↔ Summable (rterm f s) := by
  unfold LSeriesSummable
  have e : term (fun n => (f n : ℂ)) (s : ℂ) = fun n => ((rterm f s n : ℝ) : ℂ) :=
    funext (term_natCast f hs)
  rw [e]
  exact Complex.summable_ofReal

/-! ## The arithmetic functions -/

/-- `1_{n ≥ 2}`. -/
def gN (n : ℕ) : ℕ := if 2 ≤ n then 1 else 0

/-- `δ(n) = 1_{n = 1}`. -/
def dN (n : ℕ) : ℕ := if n = 1 then 1 else 0

/-- Dirichlet convolution of `ℕ`-valued functions. -/
def convN (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2

/-- `H_ord` truncated at `N`. -/
def hT (N : ℕ) (n : ℕ) : ℕ := if n ≤ N then Hord n else 0

lemma convN_cast (f g : ℕ → ℕ) :
    (fun n => (convN f g n : ℂ)) = convolution (fun n => (f n : ℂ)) (fun n => (g n : ℂ)) := by
  rw [convolution_def]
  funext n
  unfold convN
  push_cast
  rfl

lemma dN_cast : (fun n => (dN n : ℂ)) = delta := by
  funext n; unfold dN delta; split_ifs <;> simp

lemma convN_gN (f : ℕ → ℕ) (n : ℕ) : convN f gN n = ∑ d ∈ n.properDivisors, f d := by
  unfold convN
  rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * gN b)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Nat.insert_self_properDivisors hn.ne', Finset.sum_insert Nat.self_notMem_properDivisors]
  simp only [Nat.div_self hn, gN, show ¬ (2 ≤ 1) by norm_num, if_false, mul_zero, zero_add]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  obtain ⟨⟨k, hk⟩, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  have hdiv : n / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  have hk2 : 2 ≤ k := by
    by_contra hc
    push_neg at hc
    interval_cases k <;> simp_all
  simp [hdiv, hk2]

lemma Hord_zero : Hord 0 = 0 := by rw [Hord_eq]; simp

lemma Hord_one : Hord 1 = 1 := by rw [Hord_eq]; simp

lemma Hord_conv (n : ℕ) : Hord n = dN n + convN Hord gN n := by
  rw [convN_gN]
  unfold dN
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [Hord_zero, Hord_one]
  · rw [Hord_eq]
    simp [show ¬ n ≤ 1 by omega, show n ≠ 1 by omega]

lemma hT_le (N n : ℕ) : hT N n ≤ dN n + convN (hT N) gN n := by
  rw [convN_gN]
  unfold hT
  split_ifs with hn
  · have : ∑ d ∈ n.properDivisors, (if d ≤ N then Hord d else 0)
        = ∑ d ∈ n.properDivisors, Hord d := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have := (Nat.mem_properDivisors.mp hd).2
      simp [show d ≤ N by omega]
    rw [this, Hord_conv n, convN_gN]
  · exact Nat.zero_le _

/-! ## The `L`-series of `1_{n ≥ 2}` -/

lemma LSeries_gN {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (gN n : ℂ)) (s : ℂ) ∧
      LSeries (fun n => (gN n : ℂ)) (s : ℂ) = ((zetaR s - 1 : ℝ) : ℂ) := by
  have hre : 1 < (s : ℂ).re := by simpa using hs
  have h1 : LSeriesSummable 1 (s : ℂ) := LSeriesSummable_one_iff.mpr hre
  have hd : LSeriesSummable delta (s : ℂ) := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    rw [term_def]; split_ifs <;> simp [delta, hn]
  have heq : ∀ {n : ℕ}, n ≠ 0 → (gN n : ℂ) = (1 - delta) n := by
    intro n hn
    unfold gN delta
    simp only [Pi.sub_apply, Pi.one_apply]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp_all
    · simp [h, show n ≠ 1 by omega]
  refine ⟨?_, ?_⟩
  · refine LSeriesSummable.congr' (s := (s : ℂ)) ?_ (h1.sub hd)
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    exact (heq hn).symm
  · rw [LSeries_congr heq, LSeries_sub h1 hd, LSeries_one_eq_riemannZeta hre, LSeries_delta,
      riemannZeta_eq_zetaR hs]
    push_cast; rfl

/-! ## The main identity -/

/-- **Ordered factorisations.** For real `s > 1` with `ζ(s) < 2`,
`∑_{m ≥ 1} H_ord(m) m^{-s} = 1/(2 - ζ(s))`. -/
theorem hasSum_Hord {s : ℝ} (hs : 1 < s) (hz : zetaR s < 2) :
    HasSum (fun m : ℕ => (Hord m : ℝ) * (m : ℝ) ^ (-s)) (1 / (2 - zetaR s)) := by
  have hs0 : s ≠ 0 := by linarith
  obtain ⟨hgS, hgL⟩ := LSeries_gN hs
  set Z := zetaR s - 1 with hZ
  have hZ1 : Z < 1 := by rw [hZ]; linarith
  have hZ0 : 0 ≤ Z := by
    have := zetaR_split hs 1
    have h2 : 0 ≤ ∑' k : ℕ, (1 + (k : ℝ) + 1) ^ (-s) :=
      tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
    simp at this
    rw [hZ]; linarith
  -- bounded partial sums
  have hbound : ∀ N : ℕ, ∑' n, rterm (hT N) s n ≤ 1 / (2 - zetaR s) := by
    intro N
    have hTs : Summable (rterm (hT N) s) := by
      apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp [rterm, hT, show ¬ n ≤ N by omega]
    have hTL := (LSeriesSummable_natCast_iff (hT N) hs0).mpr hTs
    have hconv := LSeries_convolution' hTL hgS
    rw [← convN_cast, LSeries_natCast _ hs0, LSeries_natCast _ hs0, hgL] at hconv
    have hconv' : ∑' n, rterm (convN (hT N) gN) s n = (∑' n, rterm (hT N) s n) * Z := by
      exact_mod_cast hconv
    have hcS : Summable (rterm (convN (hT N) gN) s) := by
      rw [← LSeriesSummable_natCast_iff _ hs0, convN_cast]
      exact hTL.convolution hgS
    have hdS : Summable (rterm dN s) := by
      apply summable_of_ne_finset_zero (s := {1})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [rterm, dN, hn]
    have hd1 : ∑' n, rterm dN s n = 1 := by
      rw [tsum_eq_single 1 (fun n hn => by simp [rterm, dN, hn])]
      simp [rterm, dN]
    have hle : ∑' n, rterm (hT N) s n ≤ 1 + (∑' n, rterm (hT N) s n) * Z := by
      rw [← hd1, ← hconv', ← hdS.tsum_add hcS]
      refine hTs.tsum_le_tsum (fun n => ?_) (hdS.add hcS)
      unfold rterm
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (n.cast_nonneg) _)
      exact_mod_cast hT_le N n
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  -- summability
  have hS : Summable (rterm Hord s) := by
    apply summable_of_sum_range_le (rterm_nonneg Hord s) (c := 1 / (2 - zetaR s))
    intro M
    refine le_trans ?_ (hbound M)
    rw [tsum_eq_sum (s := Finset.range (M + 1)) (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp [rterm, hT, show ¬ n ≤ M by omega])]
    rw [Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range M, rterm Hord s i = ∑ i ∈ Finset.range M, rterm (hT M) s i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      simp [rterm, hT, show i ≤ M by omega]
    rw [this]
    have := rterm_nonneg (hT M) s M
    linarith
  -- the identity `H = 1 + H Z`
  have hHL := (LSeriesSummable_natCast_iff Hord hs0).mpr hS
  have hid : (fun n => (Hord n : ℂ)) = delta + convolution (fun n => (Hord n : ℂ))
      (fun n => (gN n : ℂ)) := by
    rw [← convN_cast, ← dN_cast]
    funext n
    simp only [Pi.add_apply]
    exact_mod_cast Hord_conv n
  have hdL : LSeriesSummable delta (s : ℂ) := by
    rw [← dN_cast, LSeriesSummable_natCast_iff _ hs0]
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [rterm, dN, hn]
  have hL := congrArg (fun f => LSeries f (s : ℂ)) hid
  try simp only at hL
  rw [LSeries_add hdL (hHL.convolution hgS), LSeries_convolution' hHL hgS, LSeries_delta,
    LSeries_natCast _ hs0, hgL] at hL
  have hL' : ∑' n, rterm Hord s n = 1 + (∑' n, rterm Hord s n) * Z := by
    simp only [Pi.one_apply] at hL
    exact_mod_cast hL
  have hval : ∑' n, rterm Hord s n = 1 / (2 - zetaR s) := by
    rw [eq_div_iff (by linarith)]
    rw [hZ] at hL'
    linarith
  rw [← hval]
  exact hS.hasSum

/-- `A(s) = 1/(2 - ζ(s)) - 1 = ∑_{m ≥ 2} H_ord(m) m^{-s}` for real `s > 1` with `ζ(s) < 2`. -/
theorem ordA_eq_tsum {s : ℝ} (hs : 1 < s) (hz : zetaR s < 2) :
    ordA s = ∑' m : ℕ, (if 2 ≤ m then (Hord m : ℝ) * (m : ℝ) ^ (-s) else 0) := by
  have h := hasSum_Hord hs hz
  have hs0 : -s ≠ 0 := by linarith
  have e : (fun m : ℕ => (Hord m : ℝ) * (m : ℝ) ^ (-s))
      = fun m => (if m = 1 then 1 else 0) + (if 2 ≤ m then (Hord m : ℝ) * (m : ℝ) ^ (-s) else 0) := by
    funext m
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;> simp [Hord_zero, Hord_one, Real.zero_rpow hs0]
    · simp [hm, show m ≠ 1 by omega]
  rw [e] at h
  have h1 : HasSum (fun m : ℕ => if m = 1 then (1 : ℝ) else 0) 1 := by
    convert! hasSum_ite_eq 1 (1 : ℝ) using 1
  have h2 := (h.sub h1)
  simp only [add_sub_cancel_left] at h2
  unfold ordA
  rw [h2.tsum_eq]

/-- **k5, for `N = ℕ`.** `∑_{m ≥ 1} H_ord(m) m^{-1.8} ≤ 8.6`. -/
theorem Hord_sum_18_le : ∑' m : ℕ, (Hord m : ℝ) * (m : ℝ) ^ (-1.8 : ℝ) ≤ 8.6 := by
  have hz := zeta_18_le
  have hz2 : zetaR 1.8 < 2 := by norm_num at hz ⊢; linarith
  rw [(hasSum_Hord (by norm_num) hz2).tsum_eq]
  rw [div_le_iff₀ (by linarith)]
  norm_num at hz ⊢
  linarith

/-! ## `A₁`: the series with `log m` -/

lemma ordA_le_aux {s₁ s : ℝ} (hs : 1 < s) (h1 : 1 < s₁) (hz1 : zetaR s₁ < 2) (hle : s₁ ≤ s) :
    zetaR s < 2 :=
  lt_of_le_of_lt (zetaR_strictAntiOn.antitoneOn h1 hs hle) hz1

lemma LSeries_gN_complex {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (gN n : ℂ)) z ∧
      LSeries (fun n => (gN n : ℂ)) z = riemannZeta z - 1 := by
  have h1 : LSeriesSummable 1 z := LSeriesSummable_one_iff.mpr hz
  have hd : LSeriesSummable delta z := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    rw [term_def]; split_ifs <;> simp [delta, hn]
  have heq : ∀ {n : ℕ}, n ≠ 0 → (gN n : ℂ) = (1 - delta) n := by
    intro n hn
    unfold gN delta
    simp only [Pi.sub_apply, Pi.one_apply]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp_all
    · simp [h, show n ≠ 1 by omega]
  refine ⟨?_, ?_⟩
  · refine LSeriesSummable.congr' (s := z) ?_ (h1.sub hd)
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    exact (heq hn).symm
  · rw [LSeries_congr heq, LSeries_sub h1 hd, LSeries_one_eq_riemannZeta hz, LSeries_delta]
    rfl

/-- The identity `H(z) (2 - ζ(z)) = 1` wherever the series of `H_ord` converges absolutely. -/
lemma LSeries_Hord_mul {z : ℂ} (hz : 1 < z.re) (hH : LSeriesSummable (fun n => (Hord n : ℂ)) z) :
    LSeries (fun n => (Hord n : ℂ)) z * (2 - riemannZeta z) = 1 := by
  obtain ⟨hgS, hgL⟩ := LSeries_gN_complex hz
  have hid : (fun n => (Hord n : ℂ)) = delta + convolution (fun n => (Hord n : ℂ))
      (fun n => (gN n : ℂ)) := by
    rw [← convN_cast, ← dN_cast]
    funext n
    simp only [Pi.add_apply]
    exact_mod_cast Hord_conv n
  have hdL : LSeriesSummable delta z := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    rw [term_def]; split_ifs <;> simp [delta, hn]
  have hL := congrArg (fun f => LSeries f z) hid
  try simp only at hL
  rw [LSeries_add hdL (hH.convolution hgS), LSeries_convolution' hH hgS, LSeries_delta, hgL] at hL
  simp only [Pi.one_apply] at hL
  linear_combination hL

lemma term_logMul_natCast (f : ℕ → ℕ) (s : ℝ) (n : ℕ) :
    term (logMul fun n => (f n : ℂ)) (s : ℂ) n
      = ((Real.log n * (f n : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [term_def]
  split_ifs with hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    simp only [logMul]
    rw [Real.rpow_neg hn0, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow hn0, Complex.ofReal_log hn0]
    push_cast
    rw [div_eq_mul_inv]

/-- **`A₁`.** If `1 < s₁ < s` and `ζ(s₁) < 2`, then
`∑_{m ≥ 1} H_ord(m) m^{-s} log m = -ζ'(s)/(2 - ζ(s))² = ordA1 s`. -/
theorem tsum_Hord_log {s₁ s : ℝ} (h1 : 1 < s₁) (hz1 : zetaR s₁ < 2) (hs : s₁ < s) :
    ∑' m : ℕ, Real.log m * (Hord m : ℝ) * (m : ℝ) ^ (-s) = ordA1 s := by
  have hs1 : 1 < s := lt_trans h1 hs
  have hs0 : s ≠ 0 := by linarith
  have hS1 : LSeriesSummable (fun n => (Hord n : ℂ)) (s₁ : ℂ) :=
    (LSeriesSummable_natCast_iff Hord (by linarith)).mpr (hasSum_Hord h1 hz1).summable
  -- `H = 1/(2 - ζ)` on `{re z > s₁}`
  have hU : IsOpen {z : ℂ | s₁ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : LSeries (fun n => (Hord n : ℂ)) =ᶠ[nhds (s : ℂ)] fun z => (2 - riemannZeta z)⁻¹ := by
    filter_upwards [hU.mem_nhds (by simpa using hs)] with z hz
    have hz' : s₁ < z.re := hz
    have hmul := LSeries_Hord_mul (by linarith) (hS1.of_re_le_re (by simpa using hz'.le))
    exact eq_inv_of_mul_eq_one_left hmul
  have hne : (2 - riemannZeta (s : ℂ)) ≠ 0 := by
    rw [riemannZeta_eq_zetaR hs1]
    have := (ordA_le_aux hs1 h1 hz1 hs.le)
    intro h
    have h' : (2 - zetaR s : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hdz : HasDerivAt riemannZeta (deriv riemannZeta (s : ℂ)) (s : ℂ) :=
    (differentiableAt_riemannZeta (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)).hasDerivAt
  have hdinv : HasDerivAt (fun z => (2 - riemannZeta z)⁻¹)
      (-(0 - deriv riemannZeta (s : ℂ)) / (2 - riemannZeta (s : ℂ)) ^ 2) (s : ℂ) :=
    ((hasDerivAt_const (s : ℂ) (2 : ℂ)).sub hdz).inv hne
  have hderiv := LSeries_deriv (f := fun n => (Hord n : ℂ)) (s := (s : ℂ))
    (lt_of_le_of_lt hS1.abscissaOfAbsConv_le (by simpa using hs))
  rw [hev.deriv_eq, hdinv.deriv, deriv_riemannZeta_eq hs1, riemannZeta_eq_zetaR hs1] at hderiv
  -- the `L`-series with `log` as a real `tsum`
  have hlog : LSeries (logMul fun n => (Hord n : ℂ)) (s : ℂ)
      = ((∑' m : ℕ, Real.log m * (Hord m : ℝ) * (m : ℝ) ^ (-s) : ℝ) : ℂ) := by
    unfold LSeries
    simp_rw [term_logMul_natCast Hord s]
    rw [Complex.ofReal_tsum]
  rw [hlog] at hderiv
  have hreal : ((∑' m : ℕ, Real.log m * (Hord m : ℝ) * (m : ℝ) ^ (-s) : ℝ) : ℂ)
      = ((zetaDR s / (2 - zetaR s) ^ 2 : ℝ) : ℂ) := by
    have := congrArg Neg.neg hderiv
    simp only [neg_neg] at this
    rw [← this]
    push_cast
    ring
  unfold ordA1
  exact_mod_cast hreal

lemma zeta_18_lt_two : zetaR 1.8 < 2 := by
  have hz := zeta_18_le; norm_num at hz ⊢; linarith

/-- **k2, as a series.** `A₀(0.03) = ∑_{m ≥ 2} H_ord(m) m^{-1.97} ≤ 2.07`. -/
theorem Hord_sum_197_le :
    ∑' m : ℕ, (if 2 ≤ m then (Hord m : ℝ) * (m : ℝ) ^ (-1.97 : ℝ) else 0) ≤ 2.07 := by
  have hz : zetaR 1.97 < 2 :=
    lt_of_le_of_lt (zetaR_strictAntiOn.antitoneOn (show (1 : ℝ) < 1.8 by norm_num)
      (show (1 : ℝ) < 1.97 by norm_num) (by norm_num)) zeta_18_lt_two
  rw [← ordA_eq_tsum (by norm_num) hz]
  exact ordA_197_le

/-- **k3, as a series.** `A₁(0.03) = ∑_{m ≥ 1} H_ord(m) m^{-1.97} log m ≤ 9.42`. -/
theorem Hord_log_sum_197_le :
    ∑' m : ℕ, Real.log m * (Hord m : ℝ) * (m : ℝ) ^ (-1.97 : ℝ) ≤ 9.42 := by
  rw [tsum_Hord_log (s₁ := 1.8) (by norm_num) zeta_18_lt_two (by norm_num)]
  exact ordA1_197_le

/-- **x1, as a series.** `∑_{m ≥ 2} H_ord(m) m^{-(1.8 - 3·10⁻⁶)} ≤ 7.4915`. -/
theorem Hord_sum_x1_le :
    ∑' m : ℕ, (if 2 ≤ m then (Hord m : ℝ) * (m : ℝ) ^ (-(1.8 - 3e-6) : ℝ) else 0) ≤ 7.4915 := by
  have hz : zetaR (1.8 - 3e-6) < 2 :=
    (ordA_le_check zH1799997 (by decide +kernel : _ ∧ _ ≤ (74915 / 10000 : ℚ))).1
  rw [← ordA_eq_tsum (by norm_num) hz]
  exact ordA_x1_le

/-- **x5, as a series.** `∑_{m ≥ 2} H_ord(m) m^{-1.77} ≤ 13.1`. -/
theorem Hord_sum_177_le :
    ∑' m : ℕ, (if 2 ≤ m then (Hord m : ℝ) * (m : ℝ) ^ (-1.77 : ℝ) else 0) ≤ 13.1 := by
  rw [← ordA_eq_tsum (by norm_num) ordA_177_le.1]
  exact ordA_177_le.2

end BSCert.Consts
