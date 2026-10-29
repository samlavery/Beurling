module

public import RequestProject.Beurling.Noise.TauNearProofNum

/-!
# The dyadic scale family for the consumers of Lemma 5.20

`dyScales X₀ x N = {X₀ 2^k/4 : k < N, X₀ 2^k/4 ≤ x}`. It is `2`-separated (`TNP.Sep`), its
scales are `≥ 1` and `≤ x` (so `18 v ≤ Z` once `18 x ≤ Z`), each scale `u` has `2u ≤ X₀⁻` (only
`u = X₀/4`) or `X₀ ≤ 2u`, and, for `N` large, every height `y ∈ [X₀/4, x]` lies in `[v, 2v)` for
some scale `v` (`dyScales_cover`). Consequently the families of levels used by Propositions 5.18,
5.26 and Lemma 5.27 are covered (`cover_NAll`, `cover_levels`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

/-- The dyadic scales `X₀ 2^k/4 ≤ x`, `k < N`. -/
noncomputable def dyScales (X0 x : ℝ) (N : ℕ) : Finset ℝ :=
  ((range N).image fun k : ℕ => X0 * 2 ^ k / 4).filter (· ≤ x)

variable {X0 x : ℝ} {N : ℕ}

lemma mem_dyScales {v : ℝ} : v ∈ dyScales X0 x N ↔ ∃ k < N, v = X0 * 2 ^ k / 4 ∧ v ≤ x := by
  unfold dyScales
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hv⟩; exact ⟨k, hk, rfl, hv⟩
  · rintro ⟨k, hk, rfl, hv⟩; exact ⟨⟨k, hk, rfl⟩, hv⟩

lemma dyScales_sep (hX : 0 < X0) : Sep (dyScales X0 x N) := by
  intro v hv w hw hvw
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
  obtain ⟨l, -, rfl, -⟩ := mem_dyScales.mp hw
  have hkl : k < l := by
    by_contra hc; push_neg at hc
    have : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hc
    have : X0 * 2 ^ l / 4 ≤ X0 * 2 ^ k / 4 := by gcongr
    linarith
  have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hkl
  rw [pow_succ] at this
  have : X0 * (2 ^ k * 2) / 4 ≤ X0 * 2 ^ l / 4 := by gcongr
  linarith

lemma dyScales_ge (hX : 4 ≤ X0) {v : ℝ} (hv : v ∈ dyScales X0 x N) : 1 ≤ v := by
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

lemma dyScales_le {v : ℝ} (hv : v ∈ dyScales X0 x N) : v ≤ x := by
  obtain ⟨k, -, -, h⟩ := mem_dyScales.mp hv; exact h

lemma dyScales_kind {X0m : ℝ} (hX : 0 < X0) (hXm : X0 / 2 ≤ X0m) {u : ℝ}
    (hu : u ∈ dyScales X0 x N) : 2 * u ≤ X0m ∨ X0 ≤ 2 * u := by
  obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hu
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · left; simp only [pow_zero, mul_one]; linarith
  · right
    have : (2 : ℝ) ≤ 2 ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    nlinarith

lemma X0_mem_dyScales (hN : 2 < N) (hx : X0 ≤ x) : X0 ∈ dyScales X0 x N :=
  mem_dyScales.mpr ⟨2, hN, by norm_num, hx⟩

/-- For `N` with `x < X₀ 2^N/4`, every `y ∈ [X₀/4, x]` lies in `[v, 2v)` for a scale `v`. -/
lemma dyScales_cover (hX : 0 < X0) (hN : x < X0 * 2 ^ N / 4) {y : ℝ} (hy1 : X0 / 4 ≤ y)
    (hy2 : y ≤ x) : ∃ v ∈ dyScales X0 x N, v ≤ y ∧ y < 2 * v := by
  classical
  -- the largest `k < N` with `X₀ 2^k/4 ≤ y`
  set S := (range N).filter fun k => X0 * 2 ^ k / 4 ≤ y
  have hS : S.Nonempty := ⟨0, by
    simp only [S, Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
    refine ⟨?_, hy1⟩
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, pow_zero] at hN; linarith
    · exact h0⟩
  set k := S.max' hS
  have hkS := S.max'_mem hS
  simp only [S, Finset.mem_filter, Finset.mem_range] at hkS
  refine ⟨X0 * 2 ^ k / 4, mem_dyScales.mpr ⟨k, hkS.1, rfl, hkS.2.trans hy2⟩, hkS.2, ?_⟩
  by_contra hc; push_neg at hc
  have hk1 : k + 1 < N := by
    by_contra hc'; push_neg at hc'
    have : (2 : ℝ) ^ N ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) hc'
    rw [pow_succ] at this
    have : X0 * 2 ^ N / 4 ≤ 2 * (X0 * 2 ^ k / 4) := by
      have := mul_le_mul_of_nonneg_left this hX.le; linarith
    linarith
  have hmem : k + 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk1, ?_⟩
    rw [pow_succ]; linarith
  have := S.le_max' _ hmem
  omega

lemma exists_N (hX : 0 < X0) (x : ℝ) : ∃ N, 2 < N ∧ x < X0 * 2 ^ N / 4 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (4 * x / X0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N + 3, by omega, ?_⟩
  have h1 : (2 : ℝ) ^ N ≤ 2 ^ (N + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_lt_iff₀ hX] at hN
  nlinarith

/-- The levels `n = iota e` with `y = x/n ∈ [v, 2v)` belong to `NW P x v`. -/
lemma mem_NW_of {P : BeurlingSystem} {X : ℝ} {n : ℕ} (hn : n ∈ (P.elems X).image iota)
    {v : ℝ} (hv0 : 0 < v) (hv : v ≤ posn P.labelVal x n) (hv2 : posn P.labelVal x n < 2 * v) :
    n ∈ NW P x v := by
  obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hn
  unfold posn at hv hv2
  rw [P.valN_iota] at hv hv2
  unfold NW
  refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨?_, hv, hv2⟩, rfl⟩
  rw [mem_elems, le_div_iff₀ hv0]
  rw [le_div_iff₀ (P.val_pos e)] at hv
  linarith

/-- Every level of `NAll P x X0m` (`X0 ≤ 4 X0m`) is covered by the dyadic scales. -/
lemma cover_NAll {P : BeurlingSystem} {X0m : ℝ} (hX : 0 < X0) (hXm : 0 < X0m)
    (h4 : X0 / 4 ≤ X0m) (hN : x < X0 * 2 ^ N / 4) :
    ∀ d ∈ NAll P x X0m, ∃ v ∈ dyScales X0 x N, d ∈ NW P x v := by
  intro d hd
  have hy1 := posn_ge_of_mem_NAll hd hXm
  have hy2 : posn P.labelVal x d ≤ x := by
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hd
    unfold posn; rw [P.valN_iota]
    have hx0 : 0 ≤ x := by
      have : X0m ≤ x / P.val e := by
        have := posn_ge_of_mem_NAll (P := P) (x := x) hd hXm
        unfold posn at this; rwa [P.valN_iota] at this
      have := P.val_pos e
      rw [le_div_iff₀ this] at *; nlinarith
    exact div_le_self hx0 (P.one_le_val e)
  obtain ⟨v, hv, hvy, hy⟩ := dyScales_cover hX hN (h4.trans hy1) hy2
  have hv0 : 0 < v := by
    obtain ⟨k, -, rfl, -⟩ := mem_dyScales.mp hv; positivity
  exact ⟨v, hv, mem_NW_of hd hv0 hvy hy⟩

/-- Every level of `levels P X0m x` (`x/n ≥ X₀⁻/2`, `X₀ ≤ 2X₀⁻`) is covered. -/
lemma cover_levels {P : BeurlingSystem} {X0m : ℝ} (hX : 0 < X0) (hXm : 0 < X0m)
    (h2 : X0 / 2 ≤ X0m) (hN : x < X0 * 2 ^ N / 4) :
    ∀ n ∈ levels P X0m x, ∃ u ∈ dyScales X0 x N, n ∈ NW P x u := by
  intro n hn
  have hn' : n ∈ NAll P x (X0m / 2) := (Finset.mem_filter.mp hn).1
  exact cover_NAll hX (by linarith) (by linarith) hN n hn'

end KR.TNP

end
