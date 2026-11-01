module

public import RequestProject.BSCert.Finite.X0Band

/-!
# The jump at `X₀`: an exact integer formula for `B(m)`

`40000 m² B(m) = 20000 m μ²(m) + 40000 m c(m) + 10001 Q(m)` (`Bx_formula`), with
`c(M) = ∑_{e | M, 1 < e < M} μ²(e)` and `Q(m) = ∑_{f | m, f > 1} H_ord(f) (m/f) c(m/f)`.
It comes from `∑_{1<d<m, d|m} X(d)/d = Q(m)/m`, by the change of variables `(d, e) ↦ (d/e, e)`
(`sum_pairs`).
-/

@[expose] public section

open Finset
namespace BSCert.X0Band

/-- `c(M) = ∑_{e | M, 1 < e < M} μ²(e)`. -/
def cS (M : ℕ) : ℕ := ∑ e ∈ M.divisors.filter (fun e => 1 < e ∧ e < M), sq e

/-- `Q(m) = ∑_{f | m, f > 1} H_ord(f) (m/f) c(m/f)`. -/
def QS (m : ℕ) : ℕ := ∑ f ∈ m.divisors.filter (1 < ·), Hord f * (m / f) * cS (m / f)

/-- Reindexing `(d, e) ↦ (d/e, e)` of the pairs `e | d | m`, `1 < e < d`, `1 < d < m`. -/
lemma sum_pairs {M : Type*} [AddCommMonoid M] {m : ℕ} (hm : m ≠ 0) (G : ℕ → ℕ → M) :
    ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m),
      ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d), G e (d / e) =
    ∑ f ∈ m.divisors.filter (1 < ·),
      ∑ e ∈ (m / f).divisors.filter (fun e => 1 < e ∧ e < m / f), G e f := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.1 / x.2, x.2⟩) (fun y _ => ⟨y.2 * y.1, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨⟨hdm, -⟩, hd1, hdm'⟩, ⟨hed, hd0⟩, he1, hed'⟩ := hx
    obtain ⟨f, rfl⟩ := hed
    obtain ⟨k, rfl⟩ := hdm
    have he0 : 0 < e := by omega
    simp only [Nat.mul_div_cancel_left _ he0]
    have hf1 : 1 < f := by
      by_contra h; push_neg at h; interval_cases f <;> simp_all
    have hk1 : 1 < k := by
      by_contra h; push_neg at h; interval_cases k <;> simp_all
    have hmf : e * f * k / f = e * k := by
      rw [show e * f * k = (e * k) * f by ring, Nat.mul_div_cancel _ (by omega)]
    refine ⟨⟨⟨⟨e * k, by ring⟩, hm⟩, hf1⟩, ⟨⟨k, ?_⟩, ?_⟩, he1, ?_⟩
    · rw [hmf]
    · rw [hmf]; positivity
    · rw [hmf]; nlinarith
  · rintro ⟨f, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨⟨hfm, -⟩, hf1⟩, ⟨hem, -⟩, he1, hem'⟩ := hy
    obtain ⟨k, hk⟩ := hfm
    have hf0 : 0 < f := by omega
    rw [hk, Nat.mul_div_cancel_left _ hf0] at hem hem'
    obtain ⟨j, rfl⟩ := hem
    refine ⟨⟨⟨⟨j, by rw [hk]; ring⟩, hm⟩, by nlinarith, ?_⟩, ⟨⟨f, by ring⟩, by positivity⟩, he1, ?_⟩
    · rw [hk]; nlinarith
    · nlinarith
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact Nat.mul_div_cancel' hx.2.1.1
  · rintro ⟨f, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hy
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    exact Nat.mul_div_cancel_left _ (by omega)
  · rintro ⟨d, e⟩ hx
    simp


lemma cS_cast (M : ℕ) : (cS M : ℚ) = ∑ e ∈ M.divisors.filter (fun e => 1 < e ∧ e < M), musq e := by
  simp [cS, musq_eq]

lemma sumX (m : ℕ) (hm : m ≠ 0) :
    ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), X d / d = (QS m : ℚ) / m := by
  have h1 : ∀ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), X d / d =
      ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d), musq e * (Hord (d / e) : ℚ) / ((d / e : ℕ) : ℚ) := by
    intro d hd
    have hd0 : d ≠ 0 := by simp at hd; omega
    rw [X, Finset.sum_div]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨⟨f, hf⟩, -⟩, he1, -⟩ := he
    have he0 : 0 < e := by omega
    have hf0 : f ≠ 0 := by rintro rfl; simp at hf; exact hd0 hf
    rw [hf, Nat.mul_div_cancel_left _ he0]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl h1, sum_pairs hm (fun e f => musq e * (Hord f : ℚ) / (f : ℚ)), QS]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun f hf => ?_
  simp only [Finset.mem_filter, Nat.mem_divisors] at hf
  obtain ⟨⟨hfm, -⟩, hf1⟩ := hf
  rw [cS_cast, Nat.cast_div hfm (by positivity), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : (f : ℚ) ≠ 0 := by positivity
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-- **Exact formula**: `40000 m² B(m) = 20000 m μ²(m) + 40000 m c(m) + 10001 Q(m)`. -/
theorem Bx_formula {m : ℕ} (hm : m ≠ 0) :
    Bx m * (40000 * (m : ℚ) ^ 2) = 20000 * m * sq m + 40000 * m * cS m + 10001 * QS m := by
  have hX := sumX m hm
  rw [Bx, Finset.sum_add_distrib, ← Finset.mul_sum, ← cS_cast]
  have e2 : ∑ d ∈ m.divisors.filter (fun d => 1 < d ∧ d < m), 1 / 2 * lam * X d / d =
      1 / 2 * lam * ((QS m : ℚ) / m) := by
    rw [← hX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [e2, musq_eq, lam]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

end BSCert.X0Band
