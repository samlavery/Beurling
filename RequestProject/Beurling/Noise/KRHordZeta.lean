module

public import RequestProject.Beurling.Noise.KRWeights
public import RequestProject.BSCert.Consts.OrdFact
public import RequestProject.Beurling.GenDyadic

/-!
# `ζ_𝒩(1.8) ≤ 1.883` under (HBS) (§5.9.1, "Ordered factorisations")

For a Beurling system satisfying (HBS) on `[1, Z]` with `log X₀⁻ ≥ 10⁸`, the partial sums of
`ζ_𝒩(1.8) = ∑_{n ∈ 𝒩} n^{-1.8}` up to any `B ≤ Z` are at most `1.883` (`zetaPartial_le`).

Below `X₀⁻` the elements are the rational integers (`HBS.ident`), whose contribution is at most
`ζ(1.8)`; above `X₀⁻` the dyadic blocks `(2^m X₀⁻/2, 2^m X₀⁻]` hold at most `2·2^m X₀⁻`
elements (`N(v) ≤ (1 + η₁)v`), so their contribution is at most `20 (X₀⁻)^{-0.8} ≤ 10⁻³⁰`.
With `ζ(1.8) + 10⁻³⁰ ≤ 1.883` (`BSCert.Consts.zeta_18_le`) this is the bound
`ζ_𝒩(1.8) ≤ ζ(1.8) + X₀^{-0.7} ≤ 1.883` of the paper, read on `[1, Z]`.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR

variable (P : BeurlingSystem)

/-- `exp(-c L) ≤ 120/(c L)⁵`. -/
lemma exp_neg_le_inv_pow5 {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 120 / x ^ 5 := by
  have h5 := Real.pow_div_factorial_le_exp (x := x) hx.le 5
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  norm_num [Nat.factorial] at h5
  nlinarith

/-- `X^{-c} ≤ 120/(c log X)⁵` for `X > 1`. -/
lemma rpow_neg_le {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    X ^ (-c) ≤ 120 / (c * Real.log X) ^ 5 := by
  have hL := Real.log_pos hX
  rw [Real.rpow_def_of_pos (by linarith), show Real.log X * -c = -(c * Real.log X) by ring]
  exact exp_neg_le_inv_pow5 (by positivity)

/-- The rational part: `∑_{e : val e < X₀⁻} (val e)^{-1.8} ≤ ζ(1.8)`. -/
lemma zeta_low_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {B : ℝ}
    (hB : B ≤ Z) :
    ∑ e ∈ (P.elems B).filter (fun e => P.val e < X0m), P.val e ^ (-(1.8 : ℝ)) ≤
      BSCert.Consts.zetaR 1.8 := by
  set s := (P.elems B).filter (fun e => P.val e < X0m)
  have hid : ∀ e ∈ s, P.val e = (iota e : ℝ) := by
    intro e he
    obtain ⟨hB', hX⟩ := Finset.mem_filter.mp he
    rw [mem_elems] at hB'
    apply P.val_eq_iota
    intro i hi
    exact h.ident (x := P.val e) hX (hB'.trans hB) i
      (Or.inl (by
        have h1 : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
        calc P.p i = P.p i ^ 1 := (pow_one _).symm
          _ ≤ P.p i ^ e i := pow_le_pow_right₀ (P.one_lt i).le h1
          _ ≤ P.val e := P.pow_le_val e i))
  have hsum := BSCert.Consts.summable_zeta_terms (s := 1.8) (by norm_num)
  calc ∑ e ∈ s, P.val e ^ (-(1.8 : ℝ))
      = ∑ e ∈ s, (((iota e - 1 : ℕ) : ℝ) + 1) ^ (-(1.8 : ℝ)) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [hid e he]
        have := iota_pos e
        congr 1
        rw [Nat.cast_sub (by omega)]; push_cast; ring
    _ = ∑ n ∈ s.image (fun e => iota e - 1), ((n : ℝ) + 1) ^ (-(1.8 : ℝ)) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        have ha := iota_pos a
        have hb := iota_pos b
        exact iota_injective (by simp only at hab; omega)
    _ ≤ BSCert.Consts.zetaR 1.8 :=
        hsum.sum_le_tsum _ (fun n _ => by positivity)

/-- `N(v) ≤ 2v` on `[0, Z]`. -/
lemma card_elems_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {v : ℝ}
    (hv : 0 ≤ v) (hvZ : v ≤ Z) : ((P.elems v).card : ℝ) ≤ 2 * v := by
  have hE := h.abs_E_le hv hvZ
  rw [← P.N_eq_card]
  have hf : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv
  have := (abs_le.mp hE).2
  have h1 := h.eta1_le
  nlinarith

/-- The jittered part: `∑_{e : X₀⁻ ≤ val e ≤ B} (val e)^{-1.8} ≤ 20 (X₀⁻)^{-0.8}`. -/
lemma zeta_high_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1) {B : ℝ}
    (hB : B ≤ Z) :
    ∑ e ∈ (P.elems B).filter (fun e => X0m ≤ P.val e), P.val e ^ (-(1.8 : ℝ)) ≤
      20 * X0m ^ (-(0.8 : ℝ)) := by
  have hX := h.X0m_pos
  set s := (P.elems B).filter (fun e => X0m ≤ P.val e)
  set a : (ℕ →₀ ℕ) → ℝ := fun e => 2 * P.val e / X0m
  set r : ℝ := (2 : ℝ) ^ (-(0.8 : ℝ))
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr58 : r ≤ 0.6 := by
    have h1 : (2 : ℝ) ^ (0.8 : ℝ) ≥ 5 / 3 := by
      have : (5 / 3 : ℝ) ^ (5 : ℝ) ≤ 2 ^ (4 : ℝ) := by norm_num
      have h2 : ((5 / 3 : ℝ) ^ (5 : ℝ)) ^ (1 / 5 : ℝ) ≤ ((2 : ℝ) ^ (4 : ℝ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) this (by norm_num)
      rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)] at h2
      norm_num at h2
      linarith
    have : r = 1 / (2 : ℝ) ^ (0.8 : ℝ) := by
      simp only [r]; rw [Real.rpow_neg (by norm_num), one_div]
    rw [this, div_le_iff₀ (by positivity)]; nlinarith
  -- block counts and block values
  have ha1 : ∀ e ∈ s, 1 < a e := by
    intro e he
    have := (Finset.mem_filter.mp he).2
    simp only [a]; rw [lt_div_iff₀ hX]; linarith
  have hblk : ∀ e ∈ s, (2 : ℝ) ^ GenDyadic.dIdx (a e) * X0m / 2 < P.val e ∧
      P.val e ≤ (2 : ℝ) ^ GenDyadic.dIdx (a e) * X0m := by
    intro e he
    obtain ⟨h1, h2⟩ := GenDyadic.dIdx_spec (ha1 e he)
    simp only [a] at h1 h2
    rw [lt_div_iff₀ hX] at h1
    rw [div_le_iff₀ hX, pow_succ] at h2
    constructor <;> nlinarith
  set Bm : ℕ → ℝ := fun m => 2 * ((2 : ℝ) ^ m * X0m)
  set Gm : ℕ → ℝ := fun m => ((2 : ℝ) ^ m * X0m / 2) ^ (-(1.8 : ℝ))
  have hsplit : ∀ e ∈ s, P.val e ^ (-(1.8 : ℝ)) = 1 * P.val e ^ (-(1.8 : ℝ)) :=
    fun e _ => (one_mul _).symm
  rw [Finset.sum_congr rfl hsplit]
  refine (GenDyadic.sum_le_blocks s a (fun _ => 1) (fun e => P.val e ^ (-(1.8 : ℝ))) Bm Gm
    (fun _ _ => zero_le_one) ?_ ?_ ?_).trans ?_
  · intro m hm
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    obtain ⟨e0, he0, hm0⟩ := Finset.mem_image.mp hm
    set v := min ((2 : ℝ) ^ m * X0m) B
    have hfib : ∀ e ∈ s.filter (fun e => GenDyadic.dIdx (a e) = m), P.val e ≤ v := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      have hb := (hblk e he1).2
      rw [he2] at hb
      exact le_min hb (P.mem_elems.mp (Finset.mem_filter.mp he1).1)
    have hsub : s.filter (fun e => GenDyadic.dIdx (a e) = m) ⊆ P.elems v :=
      fun e he => P.mem_elems.mpr (hfib e he)
    have hv1 : 1 ≤ v := (P.one_le_val e0).trans
      (hfib e0 (Finset.mem_filter.mpr ⟨he0, hm0⟩))
    have hc := card_elems_le P h (by linarith) ((min_le_right _ _).trans hB)
    have hcard : ((s.filter (fun e => GenDyadic.dIdx (a e) = m)).card : ℝ) ≤
        ((P.elems v).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    simp only [Bm]
    have : v ≤ (2 : ℝ) ^ m * X0m := min_le_left _ _
    linarith
  · intro e he
    obtain ⟨h1, -⟩ := hblk e he
    simp only [Gm]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1.le (by norm_num)
  · intro m _; simp only [Gm]; positivity
  · have hterm : ∀ m : ℕ, Bm m * Gm m ≤ 8 * X0m ^ (-(0.8 : ℝ)) * r ^ m := by
      intro m
      simp only [Bm, Gm]
      set Y := (2 : ℝ) ^ m * X0m / 2
      have hY : 0 < Y := by positivity
      have e1 : 2 * ((2 : ℝ) ^ m * X0m) * Y ^ (-(1.8 : ℝ)) = 4 * Y ^ (-(0.8 : ℝ)) := by
        have := Real.rpow_add hY 1 (-(1.8 : ℝ))
        rw [Real.rpow_one] at this
        have e : (1 : ℝ) + -(1.8 : ℝ) = -(0.8 : ℝ) := by norm_num
        rw [e] at this
        rw [this]; simp only [Y]; ring
      have e2 : Y ^ (-(0.8 : ℝ)) = r ^ m * (X0m / 2) ^ (-(0.8 : ℝ)) := by
        have : Y = (2 : ℝ) ^ m * (X0m / 2) := by simp only [Y]; ring
        rw [this, Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        simp only [r]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), mul_comm]
      have e3 : (X0m / 2) ^ (-(0.8 : ℝ)) ≤ 2 * X0m ^ (-(0.8 : ℝ)) := by
        rw [Real.div_rpow hX.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_inv_eq_mul]
        have h2 : (2 : ℝ) ^ (0.8 : ℝ) ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (0.8 : ℝ) ≤ 1)
          simpa using this
        have h0 : 0 ≤ X0m ^ (-(0.8 : ℝ)) := by positivity
        nlinarith
      rw [e1, e2]
      have hrm : 0 ≤ r ^ m := by positivity
      nlinarith
    have hgeo : ∀ K : Finset ℕ, ∑ m ∈ K, r ^ m ≤ 2.5 := by
      intro K
      have hs := summable_geometric_of_lt_one hr0.le hr1
      calc ∑ m ∈ K, r ^ m ≤ ∑' m, r ^ m := hs.sum_le_tsum _ (fun _ _ => by positivity)
        _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
        _ ≤ 2.5 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h0 : 0 ≤ X0m ^ (-(0.8 : ℝ)) := by positivity
    calc ∑ m ∈ s.image (fun e => GenDyadic.dIdx (a e)), Bm m * Gm m
        ≤ ∑ m ∈ s.image (fun e => GenDyadic.dIdx (a e)), 8 * X0m ^ (-(0.8 : ℝ)) * r ^ m :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = 8 * X0m ^ (-(0.8 : ℝ)) * ∑ m ∈ s.image (fun e => GenDyadic.dIdx (a e)), r ^ m := by
          rw [Finset.mul_sum]
      _ ≤ 8 * X0m ^ (-(0.8 : ℝ)) * 2.5 :=
          mul_le_mul_of_nonneg_left (hgeo _) (by positivity)
      _ = 20 * X0m ^ (-(0.8 : ℝ)) := by ring

/-- **`ζ_𝒩(1.8) ≤ 1.883`**, read on `[1, B]`, `B ≤ Z`, for `log X₀⁻ ≥ 10⁸`. -/
theorem zetaPartial_le {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {B : ℝ} (hB : B ≤ Z) :
    ∑ e ∈ P.elems B, P.val e ^ (-(1.8 : ℝ)) ≤ 1.883 := by
  have hX := h.X0m_pos
  have hX1 : 1 < X0m := by have := h.X0m_ge; norm_num at this; linarith
  rw [← Finset.sum_filter_add_sum_filter_not (P.elems B) (fun e => P.val e < X0m)]
  have hlo := zeta_low_le P h hB
  have hhi := zeta_high_le P h hB
  have hfilt : (P.elems B).filter (fun e => ¬ P.val e < X0m) =
      (P.elems B).filter (fun e => X0m ≤ P.val e) := by
    ext e; simp [not_lt]
  rw [hfilt]
  have hz := BSCert.Consts.zeta_18_le
  have hsmall : 20 * X0m ^ (-(0.8 : ℝ)) ≤ 1 / 10 ^ 30 := by
    have h1 := rpow_neg_le hX1 (by norm_num : (0 : ℝ) < 0.8)
    have h2 : (80000000 : ℝ) ≤ 0.8 * Real.log X0m := by linarith
    have h3 : (80000000 : ℝ) ^ 5 ≤ (0.8 * Real.log X0m) ^ 5 :=
      pow_le_pow_left₀ (by norm_num) h2 5
    have h4 : 120 / (0.8 * Real.log X0m) ^ 5 ≤ 120 / (80000000 : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
    have h5 : 20 * (120 / (80000000 : ℝ) ^ 5) ≤ 1 / 10 ^ 30 := by norm_num
    linarith
  linarith

end KR

end
