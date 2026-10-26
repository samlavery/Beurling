module

public import RequestProject.Beurling.MertensIV

/-!
# Lemma 5.1(i) (dyadic summation) and Lemma 5.1(iii) (from (ii))

Let `P` be a finite family of (Beurling) primes `p_i > 1`.

* `MertensIII.psi_le_of_dyadic` : the last step of Lemma 5.1(i): if
  `ψ(x) - ψ(x/2) ≤ c x` for all `1 ≤ x ≤ z`, and `ψ` vanishes below `1`, then
  `ψ(x) ≤ 2 c x` for all `0 ≤ x ≤ z` (with `c = 0.71`: `ψ(x) ≤ 1.42 x`).
* `MertensIII.Spow` : `S(x) = ∑_{p^k ≤ x} log p / p^k` (all prime powers, `k ≥ 1`).
* `MertensIII.Sp_le_Spow`, `MertensIII.Spow_sub_Sp_le` :
  `0 ≤ S(x) - S_p(x) ≤ ∑_i log p_i / (p_i (p_i - 1))`.
* `MertensIII.mertens_iii` : Lemma 5.1(iii) from (ii): if `a ≤ S(x) - log x ≤ M` and the
  prime-power constant is at most `B`, then `a - B ≤ S_p(x) - log x ≤ M`; with the paper's
  constants (`a = -1.01`, `M = 0.43`, `B = 0.7554`), `-1.77 ≤ S_p(x) - log x ≤ 0.43`.
* `MertensIII.mertens_iv_of_ii` : Lemma 5.1(iv) from (ii) and the prime-power constant.
-/

@[expose] public section

open Real Finset

namespace MertensIII

/-! ### Lemma 5.1(i): summing over dyadic blocks -/

/-- Telescoping over the dyadic blocks `(x/2^{k+1}, x/2^k]`. -/
lemma psi_le_geom (ψ : ℝ → ℝ) {c z : ℝ} (hc : 0 ≤ c) (hψ0 : ∀ x < 1, ψ x = 0)
    (hstep : ∀ x, 1 ≤ x → x ≤ z → ψ x - ψ (x / 2) ≤ c * x) :
    ∀ n : ℕ, ∀ x, 0 ≤ x → x < 2 ^ n → x ≤ z → ψ x ≤ 2 * c * x * (1 - (1 / 2 : ℝ) ^ n) := by
  intro n
  induction n with
  | zero =>
    intro x _ hx _
    simp only [pow_zero] at hx
    rw [hψ0 x hx]; simp
  | succ n ih =>
    intro x hx0 hx hxz
    by_cases h1 : 1 ≤ x
    · have hx2 : x / 2 < 2 ^ n := by rw [pow_succ] at hx; linarith
      have h := ih (x / 2) (by linarith) hx2 (by linarith)
      have hs := hstep x h1 hxz
      have : 2 * c * x * (1 - (1 / 2 : ℝ) ^ (n + 1)) =
          c * x + 2 * c * (x / 2) * (1 - (1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]; ring
      linarith
    · push_neg at h1
      rw [hψ0 x h1]
      have : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have : 0 ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) := by linarith
      positivity

/-- **Lemma 5.1(i)**, the summation over dyadic blocks: if `ψ` vanishes below `1` and
`ψ(x) - ψ(x/2) ≤ c x` for `1 ≤ x ≤ z`, then `ψ(x) ≤ 2 c x` for `0 ≤ x ≤ z`. -/
theorem psi_le_of_dyadic (ψ : ℝ → ℝ) {c z : ℝ} (hc : 0 ≤ c) (hψ0 : ∀ x < 1, ψ x = 0)
    (hstep : ∀ x, 1 ≤ x → x ≤ z → ψ x - ψ (x / 2) ≤ c * x) {x : ℝ} (hx0 : 0 ≤ x)
    (hxz : x ≤ z) : ψ x ≤ 2 * c * x := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  have h := psi_le_geom ψ hc hψ0 hstep n x hx0 hn hxz
  have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have : 0 ≤ 2 * c * x := by positivity
  nlinarith

/-- Lemma 5.1(i) with the paper's constant: `ψ(x) - ψ(x/2) ≤ 0.71 x` on `[1, z]` gives
`ψ(x) ≤ 1.42 x` on `[0, z]`. -/
theorem psi_le_explicit (ψ : ℝ → ℝ) {z : ℝ} (hψ0 : ∀ x < 1, ψ x = 0)
    (hstep : ∀ x, 1 ≤ x → x ≤ z → ψ x - ψ (x / 2) ≤ 0.71 * x) {x : ℝ} (hx0 : 0 ≤ x)
    (hxz : x ≤ z) : ψ x ≤ 1.42 * x := by
  have := psi_le_of_dyadic ψ (by norm_num) hψ0 hstep hx0 hxz
  linarith

/-! ### Lemma 5.1(iii) -/

variable {ι : Type*} (P : Finset ι) (pv : ι → ℝ)

/-- `S(x) = ∑_{p_i^k ≤ x, k ≥ 1} log p_i / p_i^k`, summed over the prime powers. -/
noncomputable def Spow (v : ℝ) : ℝ :=
  ∑ i ∈ P, ∑' k : ℕ, if pv i ^ (k + 1) ≤ v then Real.log (pv i) / pv i ^ (k + 1) else 0

/-- The contribution of the higher powers `k ≥ 2`. -/
noncomputable def higher (p v : ℝ) : ℝ :=
  ∑' k : ℕ, if p ^ (k + 2) ≤ v then Real.log p / p ^ (k + 2) else 0

lemma summable_term {p : ℝ} (hp : 1 < p) (v : ℝ) (j : ℕ) :
    Summable (fun k : ℕ => if p ^ (k + j) ≤ v then Real.log p / p ^ (k + j) else 0) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg hp.le
  have hg : Summable (fun k : ℕ => Real.log p / p ^ j * (1 / p) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hp0).mpr hp)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
  · split_ifs
    · positivity
    · exact le_rfl
  · have e : Real.log p / p ^ j * (1 / p) ^ k = Real.log p / p ^ (k + j) := by
      rw [pow_add, one_div_pow]; field_simp
    rw [e]
    split_ifs
    · exact le_rfl
    · positivity

lemma higher_nonneg {p : ℝ} (hp : 1 < p) (v : ℝ) : 0 ≤ higher p v := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg hp.le
  apply tsum_nonneg
  intro k
  split_ifs
  · have : 0 < p := by linarith
    positivity
  · exact le_rfl

lemma higher_le {p : ℝ} (hp : 1 < p) (v : ℝ) : higher p v ≤ Real.log p / (p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg hp.le
  have hr : 1 / p < 1 := (div_lt_one hp0).mpr hp
  have hg : Summable (fun k : ℕ => Real.log p / p ^ 2 * (1 / p) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left _
  calc higher p v ≤ ∑' k : ℕ, Real.log p / p ^ 2 * (1 / p) ^ k := by
        apply Summable.tsum_le_tsum _ (summable_term hp v 2) hg
        intro k
        have e : Real.log p / p ^ 2 * (1 / p) ^ k = Real.log p / p ^ (k + 2) := by
          rw [pow_add, one_div_pow]; field_simp
        rw [e]
        split_ifs
        · exact le_rfl
        · positivity
    _ = Real.log p / (p * (p - 1)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr]
        have : p - 1 ≠ 0 := by linarith
        field_simp

lemma inner_split {p : ℝ} (hp : 1 < p) (v : ℝ) :
    (∑' k : ℕ, if p ^ (k + 1) ≤ v then Real.log p / p ^ (k + 1) else 0) =
      (if p ≤ v then Real.log p / p else 0) + higher p v := by
  rw [(summable_term hp v 1).tsum_eq_zero_add]
  simp only [zero_add, pow_one, higher]

lemma Spow_eq (hp : ∀ i ∈ P, 1 < pv i) (v : ℝ) :
    Spow P pv v = MertensIV.Sp P pv v + ∑ i ∈ P, higher (pv i) v := by
  unfold Spow MertensIV.Sp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => inner_split (hp i hi) v)

/-- `S_p(x) ≤ S(x)`. -/
theorem Sp_le_Spow (hp : ∀ i ∈ P, 1 < pv i) (v : ℝ) : MertensIV.Sp P pv v ≤ Spow P pv v := by
  rw [Spow_eq P pv hp]
  have := Finset.sum_nonneg (fun i hi => higher_nonneg (hp i hi) v)
  linarith

/-- `S(x) - S_p(x) ≤ ∑_i log p_i / (p_i (p_i - 1))`. -/
theorem Spow_sub_Sp_le (hp : ∀ i ∈ P, 1 < pv i) (v : ℝ) :
    Spow P pv v - MertensIV.Sp P pv v ≤ ∑ i ∈ P, Real.log (pv i) / (pv i * (pv i - 1)) := by
  rw [Spow_eq P pv hp]
  have := Finset.sum_le_sum (fun i hi => higher_le (hp i hi) v)
  linarith

/-- **Lemma 5.1(iii)** from (ii): if `a ≤ S(x) - log x ≤ M` and
`∑_i log p_i/(p_i(p_i - 1)) ≤ B`, then `a - B ≤ S_p(x) - log x ≤ M`. -/
theorem mertens_iii (hp : ∀ i ∈ P, 1 < pv i) {a M B x : ℝ}
    (hB : ∑ i ∈ P, Real.log (pv i) / (pv i * (pv i - 1)) ≤ B)
    (hii : a ≤ Spow P pv x - Real.log x ∧ Spow P pv x - Real.log x ≤ M) :
    a - B ≤ MertensIV.Sp P pv x - Real.log x ∧ MertensIV.Sp P pv x - Real.log x ≤ M := by
  have h1 := Sp_le_Spow P pv hp x
  have h2 := Spow_sub_Sp_le P pv hp x
  constructor <;> linarith [hii.1, hii.2]

/-- Lemma 5.1(iii) with the paper's constants: `-1.01 ≤ S(x) - log x ≤ 0.43` (part (ii)) and a
prime-power constant `≤ 0.7554` give `-1.77 ≤ S_p(x) - log x ≤ 0.43`. -/
theorem mertens_iii_explicit (hp : ∀ i ∈ P, 1 < pv i) {x : ℝ}
    (hB : ∑ i ∈ P, Real.log (pv i) / (pv i * (pv i - 1)) ≤ 0.7554)
    (hii : -1.01 ≤ Spow P pv x - Real.log x ∧ Spow P pv x - Real.log x ≤ 0.43) :
    -1.77 ≤ MertensIV.Sp P pv x - Real.log x ∧ MertensIV.Sp P pv x - Real.log x ≤ 0.43 := by
  have := mertens_iii P pv hp hB hii
  constructor <;> linarith [this.1, this.2]

/-- **Lemma 5.1(iv) from (ii)**: if `-1.01 ≤ S(v) - log v ≤ 0.43` on `[y, x]` (`2 ≤ y ≤ x`) and
the prime-power constant is at most `0.7554`, then
`|∑_{y<p≤x} 1/p - log(log x / log y)| ≤ 2.20 / log y`. -/
theorem mertens_iv_of_ii (hp : ∀ i ∈ P, 1 < pv i) {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (hB : ∑ i ∈ P, Real.log (pv i) / (pv i * (pv i - 1)) ≤ 0.7554)
    (hii : ∀ v ∈ Set.Icc y x,
      -1.01 ≤ Spow P pv v - Real.log v ∧ Spow P pv v - Real.log v ≤ 0.43) :
    |∑ i ∈ P.filter (fun i => y < pv i ∧ pv i ≤ x), 1 / pv i -
      Real.log (Real.log x / Real.log y)| ≤ 2.20 / Real.log y :=
  MertensIV.mertens_iv_explicit P pv hp hy hyx
    (fun v hv => mertens_iii_explicit P pv hp hB (hii v hv))

end MertensIII
