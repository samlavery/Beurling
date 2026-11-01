module

public import RequestProject.Beurling.GenNatPart
public import RequestProject.Beurling.GenPartial
public import RequestProject.Beurling.GenDyadic
public import RequestProject.Beurling.MertensIV

/-!
# Lemma 5.1 (Chebyshev–Mertens) for a Beurling system satisfying (HBS)

`BeurlingSystem.HBS P X₀⁻ z η₁ η₂ ε₁` is the hypothesis (HBS) of §5.2 on `[1, z]`:

* `N(v) = ⌊v⌋` for `1 ≤ v < X₀⁻` (and `v ≤ z`);
* `|N(v) - ⌊v⌋| ≤ ε₁(v) v` for `X₀⁻ ≤ v ≤ z`;
* (24): `ε₁(v) log v ≤ η₂`, and `∑_k ε₁(w_k) ≤ η₁` for any choice of points `w_k` in the dyadic
  blocks `[x 2^{-k-1}, x 2^{-k}] ∩ [X₀⁻, z]` (this is implied by the paper's
  `η₁ = sup_x ∑_k sup_{block k} ε₁`);
* `η₁, η₂ ∈ [0, 10⁻³]`, and `X₀⁻ ≥ 10⁷` (in the paper `X₀⁻ ≥ e^{10⁸} - H(X₀)/2`).

Under (HBS) on `[1, z]`, for every `1 ≤ x ≤ z` (`lemma_5_1`):

* (i) `ψ_P(x) - ψ_P(x/2) ≤ 0.71 x` and `ψ_P(x) ≤ 1.42 x`;
* (ii) `-1.01 ≤ S_P(x) - log x ≤ 0.43`;
* (iii) `-1.77 ≤ S_{p,P}(x) - log x ≤ 0.43`;
* (iv) `|∑_{y < p ≤ x} 1/p - log(log x / log y)| ≤ 2.20 / log y` for `2 ≤ y ≤ x`.

The proof is the paper's. Below `X₀⁻` the system is `ℕ` (`p_eq_nth_prime`), and the results
for `ℕ` (`Lemma51Nat`, `BSCert.FiniteN`) apply. Above `X₀⁻`, the Chebyshev identity
(`chebyshev_identity`) with `N = ⌊·⌋ + E₁` gives (25); the two error integrals are bounded by
partial summation (`abs_ellN_sub_le`) and by the dyadic-block argument (26) (`blocks_E`), which
uses (i) at smaller scales, so (i) is proved by induction on the scale.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- **The hypothesis (HBS)** on `[1, z]`, with the parameters `X₀⁻`, `η₁`, `η₂` and the error
profile `ε₁` (see the module docstring). -/
structure HBS (X0m z η1 η2 : ℝ) (ε1 : ℝ → ℝ) : Prop where
  X0m_ge : (10 : ℝ) ^ 7 ≤ X0m
  eta1_nonneg : 0 ≤ η1
  eta1_le : η1 ≤ 1 / 1000
  eta2_nonneg : 0 ≤ η2
  eta2_le : η2 ≤ 1 / 1000
  floor_eq : ∀ v, 1 ≤ v → v < X0m → v ≤ z → P.N v = ⌊v⌋₊
  err : ∀ v, X0m ≤ v → v ≤ z → |P.N v - ⌊v⌋₊| ≤ ε1 v * v
  eta2 : ∀ v, X0m ≤ v → v ≤ z → ε1 v * Real.log v ≤ η2
  eta1 : ∀ (x : ℝ) (K : Finset ℕ) (w : ℕ → ℝ),
    (∀ k ∈ K, x / 2 ^ (k + 1) ≤ w k ∧ w k ≤ x / 2 ^ k ∧ X0m ≤ w k ∧ w k ≤ z) →
      ∑ k ∈ K, ε1 (w k) ≤ η1

namespace HBS

variable {P} {X0m z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma X0m_pos (h : P.HBS X0m z η1 η2 ε1) : 0 < X0m := lt_of_lt_of_le (by norm_num) h.X0m_ge

lemma eps_nonneg (h : P.HBS X0m z η1 η2 ε1) {v : ℝ} (h1 : X0m ≤ v) (h2 : v ≤ z) :
    0 ≤ ε1 v := by
  have hv : 0 < v := lt_of_lt_of_le h.X0m_pos h1
  have := (abs_nonneg _).trans (h.err v h1 h2)
  exact nonneg_of_mul_nonneg_left this hv

lemma eps_le (h : P.HBS X0m z η1 η2 ε1) {v : ℝ} (h1 : X0m ≤ v) (h2 : v ≤ z) : ε1 v ≤ η1 := by
  have hv : 0 < v := lt_of_lt_of_le h.X0m_pos h1
  have := h.eta1 v {0} (fun _ => v) (by
    intro k hk
    rw [mem_singleton] at hk; subst hk
    refine ⟨?_, by simp, h1, h2⟩
    simp only [zero_add, pow_one]; linarith)
  simpa using this

lemma E_zero (h : P.HBS X0m z η1 η2 ε1) {v : ℝ} (h0 : 0 ≤ v) (h1 : v < X0m) (h2 : v ≤ z) :
    P.N v - ⌊v⌋₊ = 0 := by
  rcases lt_or_ge v 1 with hv | hv
  · rw [P.N_eq_zero hv, Nat.floor_eq_zero.mpr hv]; simp
  · rw [h.floor_eq v hv h1 h2]; ring

lemma abs_E_le (h : P.HBS X0m z η1 η2 ε1) {t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ z) :
    |P.N t - ⌊t⌋₊| ≤ η1 * t := by
  rcases lt_or_ge t X0m with h1 | h1
  · rw [h.E_zero h0 h1 ht, abs_zero]; exact mul_nonneg h.eta1_nonneg h0
  · exact (h.err t h1 ht).trans (mul_le_mul_of_nonneg_right (h.eps_le h1 ht) h0)

lemma abs_E_log_le (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z) :
    |P.N x - ⌊x⌋₊| * Real.log x ≤ η2 * x := by
  have hx0 : 0 ≤ x := by linarith
  rcases lt_or_ge x X0m with h1 | h1
  · rw [h.E_zero hx0 h1 hxz, abs_zero, zero_mul]; exact mul_nonneg h.eta2_nonneg hx0
  · have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    calc |P.N x - ⌊x⌋₊| * Real.log x ≤ ε1 x * x * Real.log x :=
          mul_le_mul_of_nonneg_right (h.err x h1 hxz) hl
      _ = (ε1 x * Real.log x) * x := by ring
      _ ≤ η2 * x := mul_le_mul_of_nonneg_right (h.eta2 x h1 hxz) hx0

/-- `|∫_{[1,x]} log v dE₁| ≤ (η₁ + η₂) x`. -/
lemma delta_le (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z) :
    |P.ellN x - Real.log (⌊x⌋₊.factorial : ℝ)| ≤ (η1 + η2) * x := by
  have := P.abs_ellN_sub_le (c := η1) (d := η2) hx
    (fun t ht => h.abs_E_le (by linarith [ht.1]) (ht.2.trans hxz)) (h.abs_E_log_le hx hxz)
  linarith

/-- Below `X₀⁻` the generalized primes are the rational primes. -/
lemma ident (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : x < X0m) (hxz : x ≤ z) :
    ∀ j, (P.p j ≤ x ∨ ((qp j : ℕ) : ℝ) ≤ x) → P.p j = qp j := by
  set D : Set ℝ := {v | v < X0m ∧ v ≤ z}
  have hD : ∀ u v, u ≤ v → v ∈ D → u ∈ D := fun u v huv hv =>
    ⟨lt_of_le_of_lt huv hv.1, huv.trans hv.2⟩
  have hN : ∀ v ∈ D, 1 ≤ v → P.N v = ⌊v⌋₊ := fun v hv h1 => h.floor_eq v h1 hv.1 hv.2
  intro j hj
  apply P.p_eq_nth_prime hD hN j
  rcases hj with hj | hj
  · exact Or.inl ⟨lt_of_le_of_lt hj hx, hj.trans hxz⟩
  · exact Or.inr ⟨lt_of_le_of_lt hj hx, hj.trans hxz⟩

/-- `ψ_P(b) - ψ_P(a) = ∑_{a < p^{k+1} ≤ b} log p`, as an upper bound for a sub-sum. -/
lemma sum_le_psi_sub {a b : ℝ} (hab : a ≤ b) (s : Finset (ℕ × ℕ))
    (hs : ∀ jk ∈ s, a < P.p jk.1 ^ (jk.2 + 1) ∧ P.p jk.1 ^ (jk.2 + 1) ≤ b) :
    ∑ jk ∈ s, Real.log (P.p jk.1) ≤ P.psi b - P.psi a := by
  rw [psi_eq_sum, psi_eq_sum, ← Finset.sum_sdiff (P.pps_mono hab)]
  have : s ⊆ P.pps b \ P.pps a := by
    intro jk hjk
    simp only [mem_sdiff, mem_pps, not_le]
    exact ⟨(hs jk hjk).2, (hs jk hjk).1⟩
  have := sum_le_sum_of_subset_of_nonneg this (fun i _ _ => P.log_p_nonneg i.1)
  linarith

/-- **The bound (26)**: `∫ |E₁(x/a)| dψ(a) ≤ 1.42 η₁ x`, given (i) at the scales
`t ≤ 2x/X₀⁻`. -/
lemma blocks_E (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z)
    (hψ : ∀ t, 1 ≤ t → t ≤ 2 * x / X0m → P.psi t - P.psi (t / 2) ≤ 0.71 * t) :
    ∑ jk ∈ P.pps x, Real.log (P.p jk.1) *
      |P.N (x / P.p jk.1 ^ (jk.2 + 1)) - ⌊x / P.p jk.1 ^ (jk.2 + 1)⌋₊| ≤ 1.42 * η1 * x := by
  set a : ℕ × ℕ → ℝ := fun jk => P.p jk.1 ^ (jk.2 + 1) with ha_def
  have hX := h.X0m_pos
  have hx0 : 0 < x := by linarith
  have ha1 : ∀ jk, 1 < a jk := fun jk => one_lt_pow₀ (P.one_lt _) (by omega)
  have hapos : ∀ jk, 0 < a jk := fun jk => by linarith [ha1 jk]
  have hxa_le : ∀ jk, x / a jk ≤ x := fun jk =>
    div_le_self hx0.le (ha1 jk).le
  set s := (P.pps x).filter (fun jk => X0m ≤ x / a jk) with hs_def
  -- only the terms with `x/a ≥ X₀⁻` contribute
  have e1 : ∑ jk ∈ P.pps x, Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| =
      ∑ jk ∈ s, Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| := by
    symm
    apply Finset.sum_subset (filter_subset _ _)
    intro jk _ hjk
    simp only [hs_def, mem_filter, not_and, not_le] at hjk
    have hlt : x / a jk < X0m := by
      by_contra hc; push_neg at hc
      exact absurd (hjk (by simpa using ‹jk ∈ P.pps x›)) (not_lt.mpr hc)
    rw [h.E_zero (div_nonneg hx0.le (hapos jk).le) hlt ((hxa_le jk).trans hxz)]
    simp
  -- bound each term by `ε₁(x/a) · x/a`
  have e2 : ∑ jk ∈ s, Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| ≤
      ∑ jk ∈ s, Real.log (P.p jk.1) * (ε1 (x / a jk) * (x / a jk)) := by
    refine Finset.sum_le_sum fun jk hjk => ?_
    rw [mem_filter] at hjk
    exact mul_le_mul_of_nonneg_left (h.err _ hjk.2 ((hxa_le jk).trans hxz))
      (P.log_p_nonneg _)
  -- choose a maximiser of `ε₁(x/a)` on each block
  set K := s.image (fun jk => GenDyadic.dIdx (a jk)) with hK_def
  have hex : ∀ m ∈ K, ∃ jk ∈ s.filter (fun jk => GenDyadic.dIdx (a jk) = m),
      ∀ jk' ∈ s.filter (fun jk => GenDyadic.dIdx (a jk) = m),
        ε1 (x / a jk') ≤ ε1 (x / a jk) := by
    intro m hm
    apply Finset.exists_max_image
    obtain ⟨jk, hjk, hm'⟩ := mem_image.mp hm
    exact ⟨jk, mem_filter.mpr ⟨hjk, hm'⟩⟩
  choose! J hJmem hJmax using hex
  have hJs : ∀ m ∈ K, J m ∈ s := fun m hm => (mem_filter.mp (hJmem m hm)).1
  have hJidx : ∀ m ∈ K, GenDyadic.dIdx (a (J m)) = m := fun m hm =>
    (mem_filter.mp (hJmem m hm)).2
  have hJX : ∀ m ∈ K, X0m ≤ x / a (J m) := fun m hm => (mem_filter.mp (hJs m hm)).2
  have e3 := GenDyadic.sum_le_blocks s a (fun jk => Real.log (P.p jk.1))
    (fun jk => ε1 (x / a jk) * (x / a jk)) (fun m => 1.42 * 2 ^ m)
    (fun m => ε1 (x / a (J m)) * (x / 2 ^ m)) (fun jk _ => P.log_p_nonneg _) ?hB ?hG ?hG0
  case hB =>
    intro m hm
    obtain ⟨jk0, hjk0, hm0⟩ := mem_image.mp hm
    have hspec0 := GenDyadic.dIdx_spec (ha1 jk0)
    rw [hm0] at hspec0
    have hjk0X : X0m ≤ x / a jk0 := (mem_filter.mp hjk0).2
    have ha0 : a jk0 ≤ x / X0m := by
      rw [le_div_iff₀ hX]; rw [le_div_iff₀ (hapos jk0)] at hjk0X; linarith
    have hpow : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hle : (2 : ℝ) ^ (m + 1) ≤ 2 * x / X0m := by
      rw [pow_succ]
      calc (2 : ℝ) ^ m * 2 ≤ a jk0 * 2 := by linarith [hspec0.1]
        _ ≤ x / X0m * 2 := by linarith
        _ = 2 * x / X0m := by ring
    have h1 := hψ _ hpow hle
    have h2 : (2 : ℝ) ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; ring
    rw [h2] at h1
    have h3 := sum_le_psi_sub (P := P) (a := 2 ^ m) (b := 2 ^ (m + 1)) (by
        rw [pow_succ]; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) m])
      (s.filter (fun jk => GenDyadic.dIdx (a jk) = m)) (by
        intro jk hjk
        rw [mem_filter] at hjk
        have := GenDyadic.dIdx_spec (ha1 jk)
        rw [hjk.2] at this
        exact this)
    calc _ ≤ P.psi (2 ^ (m + 1)) - P.psi (2 ^ m) := h3
      _ ≤ 0.71 * 2 ^ (m + 1) := h1
      _ = 1.42 * 2 ^ m := by rw [pow_succ]; ring
  case hG =>
    intro jk hjk
    have hm : GenDyadic.dIdx (a jk) ∈ K := mem_image_of_mem _ hjk
    have hX' : X0m ≤ x / a jk := (mem_filter.mp hjk).2
    have hmax := hJmax _ hm jk (mem_filter.mpr ⟨hjk, rfl⟩)
    have hspec := GenDyadic.dIdx_spec (ha1 jk)
    have he0 : 0 ≤ ε1 (x / a jk) := h.eps_nonneg hX' ((hxa_le jk).trans hxz)
    have hxa : x / a jk ≤ x / 2 ^ GenDyadic.dIdx (a jk) :=
      div_le_div_of_nonneg_left hx0.le (by positivity) hspec.1.le
    have hxa0 : 0 ≤ x / a jk := div_nonneg hx0.le (hapos jk).le
    calc ε1 (x / a jk) * (x / a jk)
        ≤ ε1 (x / a (J (GenDyadic.dIdx (a jk)))) * (x / a jk) :=
          mul_le_mul_of_nonneg_right hmax hxa0
      _ ≤ ε1 (x / a (J (GenDyadic.dIdx (a jk)))) * (x / 2 ^ GenDyadic.dIdx (a jk)) :=
          mul_le_mul_of_nonneg_left hxa (he0.trans hmax)
  case hG0 =>
    intro m hm
    have := h.eps_nonneg (hJX m hm) ((hxa_le _).trans hxz)
    positivity
  -- sum over the blocks
  have e4 : ∑ m ∈ K, 1.42 * 2 ^ m * (ε1 (x / a (J m)) * (x / 2 ^ m)) =
      1.42 * x * ∑ m ∈ K, ε1 (x / a (J m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : (2 : ℝ) ^ m ≠ 0 := by positivity
    field_simp
  have e5 : ∑ m ∈ K, ε1 (x / a (J m)) ≤ η1 := by
    apply h.eta1 x K (fun m => x / a (J m))
    intro m hm
    have hspec := GenDyadic.dIdx_spec (ha1 (J m))
    rw [hJidx m hm] at hspec
    refine ⟨div_le_div_of_nonneg_left hx0.le (hapos _) hspec.2,
      div_le_div_of_nonneg_left hx0.le (by positivity) hspec.1.le, hJX m hm,
      (hxa_le _).trans hxz⟩
  have hfin : ∑ jk ∈ P.pps x, Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| ≤
      1.42 * η1 * x := by
    rw [e1]
    refine e2.trans (e3.trans ?_)
    rw [e4]
    nlinarith
  exact hfin

lemma floor_sub_two_floor_half {v : ℝ} (hv : 0 ≤ v) :
    (0 : ℝ) ≤ (⌊v⌋₊ : ℝ) - 2 * ⌊v / 2⌋₊ := by
  have h1 : ((2 * ⌊v / 2⌋₊ : ℕ) : ℝ) ≤ v := by
    push_cast
    have := Nat.floor_le (show 0 ≤ v / 2 by linarith)
    linarith
  have h2 : 2 * ⌊v / 2⌋₊ ≤ ⌊v⌋₊ := Nat.le_floor h1
  have : ((2 * ⌊v / 2⌋₊ : ℕ) : ℝ) ≤ ⌊v⌋₊ := by exact_mod_cast h2
  push_cast at this; linarith

/-- `log 2 · x + log x + 0.00684 x ≤ 0.71 x` for `x ≥ 10⁷`. -/
lemma numeric_i {x : ℝ} (hx : 10 ^ 7 ≤ x) :
    x * Real.log 2 + Real.log x + (4 / 1000 + 2.84 / 1000) * x ≤ 0.71 * x := by
  have h1 := Real.log_two_lt_d9
  have h2 := Lemma51Nat.log_le_lin (show 0 < x by linarith)
  nlinarith

/-- **Lemma 5.1(i), the step above `X₀⁻`**: for `X₀⁻ ≤ x ≤ z`, given (i) at the scales
`t ≤ 2x/X₀⁻`, `ψ_P(x) - ψ_P(x/2) ≤ 0.71 x`. -/
lemma psi_diff_step (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hX : X0m ≤ x) (hxz : x ≤ z)
    (hψ : ∀ t, 1 ≤ t → t ≤ 2 * x / X0m → P.psi t - P.psi (t / 2) ≤ 0.71 * t) :
    P.psi x - P.psi (x / 2) ≤ 0.71 * x := by
  set a : ℕ × ℕ → ℝ := fun jk => P.p jk.1 ^ (jk.2 + 1) with ha_def
  have hX7 := h.X0m_ge
  have hx7 : (10 : ℝ) ^ 7 ≤ x := hX7.trans hX
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx7
  have hx0 : 0 < x := by linarith
  have hx2 : 1 ≤ x / 2 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have ha1 : ∀ jk, 1 < a jk := fun jk => one_lt_pow₀ (P.one_lt _) (by omega)
  have hapos : ∀ jk, 0 < a jk := fun jk => by linarith [ha1 jk]
  set A := P.pps x
  set B := P.pps (x / 2)
  have hBA : B ⊆ A := P.pps_mono (by linarith)
  -- ψ(x) - ψ(x/2) as a sum over `A`
  have hpsi : P.psi x - P.psi (x / 2) =
      ∑ jk ∈ A, Real.log (P.p jk.1) * (if x / 2 < a jk then 1 else 0) := by
    rw [psi_eq_sum, psi_eq_sum, ← Finset.sum_sdiff hBA]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have : A.filter (fun jk => x / 2 < a jk) = A \ B := by
      ext jk; simp [A, B, a, mem_sdiff, mem_pps, not_le]
    rw [this]; ring
  -- Chebyshev at `x/2`, extended to `A`
  have hcheb2 : P.ellN (x / 2) = ∑ jk ∈ A, Real.log (P.p jk.1) * P.N (x / 2 / a jk) := by
    rw [P.chebyshev_identity]
    apply Finset.sum_subset hBA
    intro jk _ hjk
    simp only [B, mem_pps, not_le] at hjk
    rw [P.N_eq_zero, mul_zero]
    rw [div_lt_one (hapos jk)]; exact hjk
  -- the per-term inequality
  have hterm : ∀ jk ∈ A, Real.log (P.p jk.1) * (if x / 2 < a jk then 1 else 0) ≤
      Real.log (P.p jk.1) * (P.N (x / a jk) - 2 * P.N (x / 2 / a jk)) +
      Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| +
      2 * (Real.log (P.p jk.1) * |P.N (x / 2 / a jk) - ⌊x / 2 / a jk⌋₊|) := by
    intro jk hjk
    have hl := P.log_p_nonneg jk.1
    simp only [A, mem_pps] at hjk
    set v := x / a jk
    have hv1 : 1 ≤ v := by rw [le_div_iff₀ (hapos jk)]; simpa using hjk
    have hv2 : x / 2 / a jk = v / 2 := by simp only [v]; ring
    rw [hv2]
    have key : (if x / 2 < a jk then (1 : ℝ) else 0) ≤ (⌊v⌋₊ : ℝ) - 2 * ⌊v / 2⌋₊ := by
      split_ifs with hc
      · have hv2' : v < 2 := by
          simp only [v]; rw [div_lt_iff₀ (hapos jk)]; linarith
        have f1 : ⌊v⌋₊ = 1 := by
          rw [Nat.floor_eq_iff (by linarith)]; norm_num; exact ⟨hv1, hv2'⟩
        have f2 : ⌊v / 2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [f1, f2]; norm_num
      · exact floor_sub_two_floor_half (by linarith)
    have hab1 := neg_abs_le (P.N v - ⌊v⌋₊)
    have hab2 := le_abs_self (P.N (v / 2) - ⌊v / 2⌋₊)
    have : (if x / 2 < a jk then (1 : ℝ) else 0) ≤
        (P.N v - 2 * P.N (v / 2)) + |P.N v - ⌊v⌋₊| + 2 * |P.N (v / 2) - ⌊v / 2⌋₊| := by
      linarith
    have := mul_le_mul_of_nonneg_left this hl
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← hpsi] at hsum
  have hdiff : ∑ jk ∈ A, Real.log (P.p jk.1) * (P.N (x / a jk) - 2 * P.N (x / 2 / a jk)) =
      P.ellN x - 2 * P.ellN (x / 2) := by
    rw [P.chebyshev_identity x, hcheb2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun jk _ => ?_
    simp only [a]; ring
  rw [hdiff] at hsum
  -- the `E₁` terms at `x/2` live on `B`
  have hE2 : ∑ jk ∈ A, Real.log (P.p jk.1) * |P.N (x / 2 / a jk) - ⌊x / 2 / a jk⌋₊| =
      ∑ jk ∈ B, Real.log (P.p jk.1) * |P.N (x / 2 / a jk) - ⌊x / 2 / a jk⌋₊| := by
    symm
    apply Finset.sum_subset hBA
    intro jk _ hjk
    simp only [B, mem_pps, not_le] at hjk
    have hlt : x / 2 / a jk < 1 := by rw [div_lt_one (hapos jk)]; exact hjk
    rw [h.E_zero (div_nonneg (by linarith) (hapos jk).le) (by linarith)
      (by linarith [h.X0m_ge, hxz, hlt, hx1])]
    simp
  rw [hE2] at hsum
  have hb1 := h.blocks_E hx1 hxz hψ
  have hb2 := h.blocks_E hx2 (by linarith) (fun t ht1 ht2 => hψ t ht1 (by
    refine ht2.trans ?_
    apply div_le_div_of_nonneg_right _ h.X0m_pos.le
    linarith))
  have hd1 := abs_le.mp (h.delta_le hx1 hxz)
  have hd2 := abs_le.mp (h.delta_le hx2 (by linarith))
  -- `log ⌊x⌋! - 2 log ⌊x/2⌋! ≤ x log 2 + log x`
  have hfl : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := by
    have := Nat.floor_div_natCast x 2
    simpa using this
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
  have hfac := BSCert.FiniteN.log_factorial_sub_le ⌊x⌋₊ hN1
  rw [← hfl] at hfac
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hNpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hN1
  have hlogN : Real.log ⌊x⌋₊ ≤ Real.log x := Real.log_le_log hNpos hNx
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfac' : Real.log (⌊x⌋₊.factorial : ℝ) - 2 * Real.log (⌊x / 2⌋₊.factorial : ℝ) ≤
      x * Real.log 2 + Real.log x := by nlinarith
  have hnum := numeric_i hx7
  have he1 := h.eta1_le
  have he2 := h.eta2_le
  have he10 := h.eta1_nonneg
  have he20 := h.eta2_nonneg
  nlinarith

/-- **Lemma 5.1(i), first part**: `ψ_P(x) - ψ_P(x/2) ≤ 0.71 x` for `1 ≤ x ≤ z`. -/
theorem psi_sub_psi_half_le (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x)
    (hxz : x ≤ z) : P.psi x - P.psi (x / 2) ≤ 0.71 * x := by
  suffices H : ∀ n : ℕ, ∀ x : ℝ, 1 ≤ x → x ≤ z → x ≤ 2 ^ n →
      P.psi x - P.psi (x / 2) ≤ 0.71 * x by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact H n x hx hxz hn.le
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro x hx hxz hxn
  rcases lt_or_ge x X0m with hlt | hge
  · rw [P.psi_eq_chebyshev (h.ident hlt hxz),
      P.psi_eq_chebyshev (h.ident (by linarith) (by linarith))]
    exact BSCert.FiniteN.psi_sub_psi_half_le hx
  · apply h.psi_diff_step hge hxz
    intro t ht1 ht2
    have hX7 := h.X0m_ge
    have hx7 : (10 : ℝ) ^ 7 ≤ x := hX7.trans hge
    have hn1 : 1 ≤ n := by
      by_contra hc; push_neg at hc
      have : n = 0 := by omega
      rw [this, pow_zero] at hxn; linarith
    have ht3 : t ≤ x / 2 := by
      refine ht2.trans ?_
      rw [div_le_iff₀ h.X0m_pos]
      nlinarith
    have h2n : (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hn1]
    exact IH (n - 1) (by omega) t ht1 (by linarith) (by linarith)

/-- **Lemma 5.1(i), second part**: `ψ_P(x) ≤ 1.42 x` for `0 ≤ x ≤ z`. -/
theorem psi_le (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 0 ≤ x) (hxz : x ≤ z) :
    P.psi x ≤ 1.42 * x := by
  suffices H : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ z → x < 2 ^ n → P.psi x ≤ 1.42 * x by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact H n x hx hxz hn
  intro n
  induction n with
  | zero =>
    intro x hx _ hxn
    rw [pow_zero] at hxn
    rw [P.psi_eq_zero hxn]; linarith
  | succ n ih =>
    intro x hx hxz hxn
    rcases lt_or_ge x 1 with h1 | h1
    · rw [P.psi_eq_zero h1]; linarith
    · have := h.psi_sub_psi_half_le h1 hxz
      have := ih (x / 2) (by linarith) (by linarith) (by rw [pow_succ] at hxn; linarith)
      linarith

/-- `n log n - n` against `x log x - x` for `n = ⌊x⌋`, and Stirling: the numerical core of
Lemma 5.1(ii) above `X₀⁻`. -/
lemma numeric_ii {x S L F G D : ℝ} (hx : 10 ^ 7 ≤ x)
    (hS : x * S = L + F - G) (hF0 : 0 ≤ F) (hF : F ≤ 1.42 * x) (hG : |G| ≤ 1.42 / 1000 * x)
    (hL : |L - D| ≤ 2 / 1000 * x)
    (hD1 : (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊ ≤ D)
    (hD2 : D ≤ (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊ + 1 + Real.log ⌊x⌋₊ / 2) :
    -1.01 ≤ S - Real.log x ∧ S - Real.log x ≤ 0.43 := by
  set N := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogx1 : Real.log N ≤ Real.log x := Real.log_le_log hNpos hNx
  have hlogx2 : Real.log x ≤ Real.log N + 1 / N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / N by positivity)
    rw [Real.log_div (by linarith) hNpos.ne'] at h
    have : x / N - 1 ≤ 1 / N := by
      rw [div_sub_one hNpos.ne', div_le_div_iff_of_pos_right hNpos]; linarith
    linarith
  have hNlog : (N : ℝ) * Real.log x - 1 ≤ N * Real.log N := by
    have : (N : ℝ) * (Real.log x - Real.log N) ≤ N * (1 / N) :=
      mul_le_mul_of_nonneg_left (by linarith) hNpos.le
    rw [mul_one_div_cancel hNpos.ne'] at this; linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlin := Lemma51Nat.log_le_lin (show 0 < x by linarith)
  have hG' := abs_le.mp hG
  have hL' := abs_le.mp hL
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  constructor
  · have h1 : x * (Real.log x - 1.01) ≤ x * S := by nlinarith
    have := le_of_mul_le_mul_left h1 (by linarith); linarith
  · have h2 : x * S ≤ x * (Real.log x + 0.43) := by nlinarith
    have := le_of_mul_le_mul_left h2 (by linarith); linarith

/-- **Lemma 5.1(ii)**: `-1.01 ≤ S_P(x) - log x ≤ 0.43` for `1 ≤ x ≤ z`. -/
theorem mertensS_sub_log_mem (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x)
    (hxz : x ≤ z) : -1.01 ≤ P.mertensS x - Real.log x ∧ P.mertensS x - Real.log x ≤ 0.43 := by
  rcases lt_or_ge x X0m with hlt | hge
  · rw [P.mertensS_eq_nat (h.ident hlt hxz)]
    exact Lemma51Nat.lemma_5_1_ii_nat hx
  set a : ℕ × ℕ → ℝ := fun jk => P.p jk.1 ^ (jk.2 + 1) with ha_def
  have hx7 : (10 : ℝ) ^ 7 ≤ x := h.X0m_ge.trans hge
  have hx0 : 0 < x := by linarith
  have hapos : ∀ jk, 0 < a jk := fun jk => P.pp_pos jk
  set A := P.pps x
  set F := ∑ jk ∈ A, Real.log (P.p jk.1) * (x / a jk - ⌊x / a jk⌋₊)
  set G := ∑ jk ∈ A, Real.log (P.p jk.1) * (P.N (x / a jk) - ⌊x / a jk⌋₊)
  have hS : x * P.mertensS x = P.ellN x + F - G := by
    rw [P.chebyshev_identity]
    unfold mertensS
    rw [Finset.mul_sum]
    simp only [F, G]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun jk _ => ?_
    simp only [a]
    field_simp
    ring
  have hF0 : 0 ≤ F := by
    refine Finset.sum_nonneg fun jk _ => mul_nonneg (P.log_p_nonneg _) ?_
    have := Nat.floor_le (div_nonneg hx0.le (hapos jk).le); linarith
  have hFle : F ≤ P.psi x := by
    rw [psi_eq_sum]
    refine Finset.sum_le_sum fun jk _ => ?_
    have := Nat.lt_floor_add_one (x / a jk)
    have hl := P.log_p_nonneg jk.1
    nlinarith
  have hpsi := h.psi_le hx0.le hxz
  have hG : |G| ≤ 1.42 / 1000 * x := by
    have h1 : |G| ≤ ∑ jk ∈ A, Real.log (P.p jk.1) * |P.N (x / a jk) - ⌊x / a jk⌋₊| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun jk _ => ?_
      rw [abs_mul, abs_of_nonneg (P.log_p_nonneg _)]
    have h2 := h.blocks_E hx hxz (fun t ht1 ht2 => h.psi_sub_psi_half_le ht1 (by
      refine ht2.trans ?_
      rw [div_le_iff₀ h.X0m_pos]
      nlinarith [h.X0m_ge]))
    have := h.eta1_le
    have := h.eta1_nonneg
    nlinarith
  have hL : |P.ellN x - Real.log (⌊x⌋₊.factorial : ℝ)| ≤ 2 / 1000 * x := by
    have := h.delta_le hx hxz
    have := h.eta1_le
    have := h.eta2_le
    nlinarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  obtain ⟨hD1, hD2⟩ := Lemma51Nat.log_factorial_bounds ⌊x⌋₊ hN1
  exact numeric_ii hx7 hS hF0 (hFle.trans hpsi) hG hL hD1 hD2

end HBS

end BeurlingSystem

end
