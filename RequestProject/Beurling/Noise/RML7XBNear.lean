module

public import RequestProject.Beurling.Noise.BridgeXB
public import RequestProject.Beurling.Noise.KRHord

/-!
# Proposition 5.31(i), the small range: a single level carries `𝔅(y)`

For a start `y` with `N = y/X₀` small (`8 y H(X₀) ≤ X₀²`, `2y ≤ X₀⁻ X₀`), the bound `𝔅(y)`
(`KR.xbB`, eq. (frakB)) is carried by one level (04x-x0band.tex, proof of Proposition 5.31(i),
"A single level"):

* `xbTerm` : the term of `𝔅(y)` at the level `n`; `xbB_eq` : `𝔅(y) = ∑_{levels} xbTerm`;
* `xbTerm_eq_zero_far` : the term vanishes unless `|y/n - X₀| ≤ 1.6 H(X₀)` (all three kinds of
  contribution force this: `B₀`, the `X₀`-near steps and the `𝔹₂` steps);
* `val_near` : at a near level `V(n) = n` (the system is `ℕ` below `X₀⁻`) and `|n - y/X₀| ≤ 1/4`;
* `card_near_le_one` : so at most one level is near; `xbB_le_of_near` : `𝔅(y)` is at most the
  term at that level (or `0`).
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

open scoped Classical in
/-- The term of `𝔅(y)` at the level `n`. -/
noncomputable def xbTerm (P : BeurlingSystem) (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m y X0 θ lam0 : ℝ)
    (n : ℕ) : ℝ :=
  ((if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
      then |cN P tw X0m y n| / 2 else 0) +
    ∑ d ∈ n.properDivisors, xbBstep P H tw X0m y X0 θ lam0 d n) / Vl P n

lemma xbB_eq (X0 θ lam0 : ℝ) :
    xbB P H tw X0m y X0 θ lam0 = ∑ n ∈ levels P X0m y, xbTerm P H tw X0m y X0 θ lam0 n := by
  classical
  unfold xbB xbTerm; rfl

/-- The key estimate: `|z - X₀| ≤ c₁ H(z) + H(X₀)/2` with `c₁ ≤ 1.0157` forces
`|z - X₀| ≤ 1.6 H(X₀)` (`H` is `θ`-Lipschitz). -/
lemma near_of_bound {ε θ X0 z : ℝ} (hP : PaperWidth H X0m ε θ) (hX0e : X0m = X0 - H X0 / 2)
    (hz : X0m / 2 ≤ z) {c1 : ℝ} (hc0 : 0 ≤ c1) (hc1 : c1 ≤ 1.0157)
    (h : |z - X0| ≤ c1 * H z + H X0 / 2) : |z - X0| ≤ 1.6 * H X0 := by
  have hHX := hP.reg.pos X0
  have hX : X0m / 2 ≤ X0 := by
    have := hP.X0m_pos; linarith
  have hl := hP.lip z X0 hz hX
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hHz : H z ≤ H X0 + θ * |z - X0| := by
    have := (le_abs_self (H z - H X0)).trans hl; linarith
  have hA0 := abs_nonneg (z - X0)
  have h2 : |z - X0| ≤ c1 * (H X0 + θ * |z - X0|) + H X0 / 2 :=
    h.trans (by nlinarith [hP.reg.pos z])
  have hct : c1 * θ ≤ 0.010157 := by nlinarith
  have h3 : |z - X0| ≤ c1 * H X0 + (c1 * θ) * |z - X0| + H X0 / 2 := by
    have e : c1 * (H X0 + θ * |z - X0|) = c1 * H X0 + (c1 * θ) * |z - X0| := by ring
    linarith
  have h4 : (c1 * θ) * |z - X0| ≤ 0.010157 * |z - X0| := mul_le_mul_of_nonneg_right hct hA0
  have h5 : c1 * H X0 ≤ 1.0157 * H X0 := mul_le_mul_of_nonneg_right hc1 hHX.le
  linarith

/-- The step terms of `𝔅` vanish far from `X₀`. -/
lemma xbBstep_eq_zero_far {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) {n d : ℕ} (hn : n ∈ levels P X0m y)
    (hd : d ∈ n.properDivisors) (hfar : 1.6 * H X0 < |posn P.labelVal y n - X0|) :
    xbBstep P H tw X0m y X0 θ lam0 d n = 0 := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hX := hP.X0m_pos
  obtain ⟨hnA, hn2⟩ := Finset.mem_filter.mp hn
  have hz : X0m / 2 ≤ posn P.labelVal y n := posn_ge_of_mem_NAll hnA (by linarith)
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by omega
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  set z := posn P.labelVal y n
  have hpd : posn P.labelVal y d = z * LemmaM.valN P.labelVal (n / d) := posn_mul hval hdn hn0
  have hstep := hP.step_le hz hw
  rw [← hpd] at hstep
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  have hHz := hP.reg.pos z
  unfold xbBstep
  split_ifs with h1 h2 h3 h4
  · rfl
  · -- `X₀`-near, terminal parent
    rfl
  · -- `X₀`-near: `|z - X₀⁻| ≤ R_d/w`
    exfalso
    unfold X0Near at h2
    have hb : |z - X0| ≤ 0.51051 * H z + H X0 / 2 := by
      have e1 : |z - X0| ≤ |z - X0m| + H X0 / 2 := by
        have := abs_sub_le z X0m X0
        have e2 : |X0m - X0| = H X0 / 2 := by
          rw [hX0e]; rw [show X0 - H X0 / 2 - X0 = -(H X0 / 2) by ring, abs_neg,
            abs_of_pos (by linarith [hP.reg.pos X0])]
        linarith
      have e3 : 1.02 * H (posn P.labelVal y d) / LemmaM.valN P.labelVal (n / d) ≤
          0.51051 * H z := by
        rw [mul_div_assoc]; nlinarith
      linarith
    have := near_of_bound hP hX0e hz (c1 := 0.51051) (by norm_num) (by norm_num) hb
    linarith
  · -- `𝔹₂`
    exfalso
    have hb : |z - X0| ≤ ((1 + θ) / 2 + 0.51051) * H z + H X0 / 2 := by
      have e3 : 1.02 * H (posn P.labelVal y d) / LemmaM.valN P.labelVal (n / d) ≤
          0.51051 * H z := by
        rw [mul_div_assoc]; nlinarith
      have := hP.reg.pos X0
      have e4 : (1 + θ) * H z / 2 = (1 + θ) / 2 * H z := by ring
      linarith
    have := near_of_bound hP hX0e hz (c1 := (1 + θ) / 2 + 0.51051) (by linarith)
      (by linarith) hb
    linarith
  · rfl

/-- The term of `𝔅` at a level far from `X₀` vanishes. -/
lemma xbTerm_eq_zero_far {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hX0e : X0m = X0 - H X0 / 2) (hp2 : ∀ j, 2 ≤ P.p j) {n : ℕ} (hn : n ∈ levels P X0m y)
    (hfar : 1.6 * H X0 < |posn P.labelVal y n - X0|) :
    xbTerm P H tw X0m y X0 θ lam0 n = 0 := by
  classical
  have hX := hP.X0m_pos
  obtain ⟨hnA, -⟩ := Finset.mem_filter.mp hn
  have hz : X0m / 2 ≤ posn P.labelVal y n := posn_ge_of_mem_NAll hnA (by linarith)
  unfold xbTerm
  rw [Finset.sum_eq_zero fun d hd => xbBstep_eq_zero_far hP hX0e hp2 hn hd hfar]
  have hB0 : ¬ |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2 := by
    intro h
    have := near_of_bound hP hX0e hz (c1 := 1 / 2) (by norm_num) (by norm_num)
      (by have := hP.reg.pos X0; linarith)
    linarith
  rw [if_neg hB0]; simp

/-- At a near level, `V(n) = n` and `|n - y/X₀| ≤ 1/4`. -/
lemma val_near {ε θ X0 Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hP : PaperWidth H X0m ε θ)
    (hbs : P.HBS X0m Z η1 η2 ε1) (hXZ : X0m ≤ Z) (hX0e : X0m = X0 - H X0 / 2)
    (hy0 : 0 < y) (hδ : 8 * y * H X0 ≤ X0 ^ 2) (hyN : 2 * y ≤ X0m * X0) {n : ℕ}
    (hn : n ∈ levels P X0m y) (hnear : |posn P.labelVal y n - X0| ≤ 1.6 * H X0) :
    LemmaM.valN P.labelVal n = n ∧ |(n : ℝ) - y / X0| ≤ 1 / 4 := by
  have hX := hP.X0m_pos
  obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
  have hHX := hP.reg.pos X0
  have hX0pos : 0 < X0 := by
    have := hP.small X0 (by linarith [show X0m / 2 ≤ X0 by linarith]); linarith
  have hsm := hP.small X0 (by linarith)
  set z := posn P.labelVal y n
  have hV := KR.valN_labelVal_pos P n
  have hzdef : z = y / LemmaM.valN P.labelVal n := rfl
  have hz1 : 0.84 * X0 ≤ z := by
    have := (abs_le.mp hnear).1; linarith
  have hz0 : 0 < z := by linarith
  have hVz : LemmaM.valN P.labelVal n = y / z := by
    rw [hzdef]; field_simp
  -- `V(n) ≤ y/(0.84 X₀) < X₀⁻`
  have hVle : LemmaM.valN P.labelVal n ≤ y / (0.84 * X0) := by
    rw [hVz]; exact div_le_div_of_nonneg_left hy0.le (by positivity) hz1
  have hVlt : LemmaM.valN P.labelVal n < X0m := by
    refine lt_of_le_of_lt hVle ?_
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hself := valN_eq_self P hbs (by omega) hVlt (hVlt.le.trans hXZ)
  refine ⟨hself, ?_⟩
  rw [← hself, hVz]
  have e : y / z - y / X0 = y * (X0 - z) / (z * X0) := by field_simp
  rw [e, abs_div, abs_mul, abs_of_pos hy0, abs_of_pos (by positivity : 0 < z * X0),
    abs_sub_comm, div_le_iff₀ (by positivity)]
  have h1 : y * |z - X0| ≤ y * (1.6 * H X0) := mul_le_mul_of_nonneg_left hnear hy0.le
  nlinarith

/-- **At most one level is near.** -/
lemma card_near_le_one {ε θ X0 Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (hP : PaperWidth H X0m ε θ)
    (hbs : P.HBS X0m Z η1 η2 ε1) (hXZ : X0m ≤ Z) (hX0e : X0m = X0 - H X0 / 2)
    (hy0 : 0 < y) (hδ : 8 * y * H X0 ≤ X0 ^ 2) (hyN : 2 * y ≤ X0m * X0) :
    ((levels P X0m y).filter (fun n => |posn P.labelVal y n - X0| ≤ 1.6 * H X0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
  have h1 := (val_near hP hbs hXZ hX0e hy0 hδ hyN ha1 ha2).2
  have h2 := (val_near hP hbs hXZ hX0e hy0 hδ hyN hb1 hb2).2
  have h3 : |(a : ℝ) - b| < 1 := by
    have := abs_sub_le (a : ℝ) (y / X0) b
    rw [abs_sub_comm (y / X0)] at this; linarith
  have h4 : |(a : ℤ) - b| < 1 := by exact_mod_cast h3
  have := abs_lt.mp h4
  omega

/-- **`𝔅(y)` is carried by the near level**: if every near level has its term `≤ c` (and
`c ≥ 0`), then `𝔅(y) ≤ c`. -/
theorem xbB_le_of_near {ε θ X0 Z η1 η2 lam0 c : ℝ} {ε1 : ℝ → ℝ} (hP : PaperWidth H X0m ε θ)
    (hbs : P.HBS X0m Z η1 η2 ε1) (hXZ : X0m ≤ Z) (hX0e : X0m = X0 - H X0 / 2)
    (hp2 : ∀ j, 2 ≤ P.p j) (hy0 : 0 < y) (hδ : 8 * y * H X0 ≤ X0 ^ 2)
    (hyN : 2 * y ≤ X0m * X0) (hc : 0 ≤ c)
    (hterm : ∀ n ∈ levels P X0m y, |posn P.labelVal y n - X0| ≤ 1.6 * H X0 →
      xbTerm P H tw X0m y X0 θ lam0 n ≤ c) :
    xbB P H tw X0m y X0 θ lam0 ≤ c := by
  classical
  rw [xbB_eq, ← Finset.sum_filter_add_sum_filter_not (levels P X0m y)
    (fun n => |posn P.labelVal y n - X0| ≤ 1.6 * H X0)]
  rw [Finset.sum_eq_zero (s := (levels P X0m y).filter
    (fun n => ¬ |posn P.labelVal y n - X0| ≤ 1.6 * H X0)) fun n hn => by
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    exact xbTerm_eq_zero_far hP hX0e hp2 hn1 (not_le.mp hn2), add_zero]
  have hcard := card_near_le_one hP hbs hXZ hX0e hy0 hδ hyN (P := P)
  rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨n0, hsub⟩
  rcases Finset.subset_singleton_iff.mp hsub with he | he
  · rw [he, Finset.sum_empty]; exact hc
  · rw [he, Finset.sum_singleton]
    have hm : n0 ∈ (levels P X0m y).filter
        (fun n => |posn P.labelVal y n - X0| ≤ 1.6 * H X0) := by rw [he]; simp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
    exact hterm n0 h1 h2

end KR.XB7

end
