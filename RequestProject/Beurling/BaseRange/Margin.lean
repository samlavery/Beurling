module

public import RequestProject.Beurling.BaseRange.Mu1Sum
public import RequestProject.Beurling.BaseRange.EdgeIdentity

/-!
# Lemma 7.3 (the margin decomposition), in the form consumed by Propositions 5.35 and 5.38

§7.2 writes, for `x ≥ X₀` (eq. (86), `eq:shdecomp`),

  `ρ^sh = MA[ℙ] + ρ_edge + (1 + K_pt)⁻¹(μ₀ + μ₁)`,

and Lemma 7.3 bounds the four pieces. `MA[ℙ]` is a function of the rational primes only and is
formalized concretely (`BaseRange.MAP`); so is the edge source `μ_edge` (`BaseRange.muEdge`).
The realised latest-prime operator `K_pt` of §5 is not formalized in this repository, so the
realised functions `μ₀`, `μ₁`, `ρ_edge` enter as parameters, with the paper's bounds on them as
named hypotheses (`Lemma73Inputs`). The horizon `xmax` is the `x` of `Good(<x)`: the
hypotheses are the paper's statements "on `Good(<u)`" for the `u ≤ xmax`.

**Proved here** (no hypothesis beyond (84), `HuxleyFrom X₀`, and `log X₀ ≥ 10⁸`):
* (a) `lemma_7_3_a` (`Window.lean`);
* (c) ⟹ (87): `mu1sum_upTo` (the dyadic sum from the pointwise bounds, with the certified
  integrals `I₁, I₂, I₃` and m5, m6);
* (d)(i) from the expansion (★) (`lemma_7_3_d_i`), and (d)(ii) (`lemma_7_3_d_ii`);
* the arithmetic of "Use" (`use_mu0`, `use_rangeA_low`, `use_rangeA_high`).

**Named hypotheses** (`Lemma73Inputs`), each exactly a statement of Lemma 7.3 about the
realised functions:
* `Lemma73b` : (b), `|μ₀(u)| ≤ 2κ (log u)³`;
* `Lemma73c` : (c), the two pointwise bounds on `μ₁`;
* `EdgeExpansion` : the expansion (★) `ρ_edge(x) = ∑_n μ(n)/n μ_edge(x/n)` on
  `[X₀, X₀^{1.9}]` (Lemma M applied to the realised resolvent; the first display of the proof
  of (d)(i));
* `Lemma73diii` : (d)(iii), `|ρ_edge(x)| log x ≤ 3X₀^{-0.01} + X₀^{-0.34}`.

`lemma_7_3` packages everything.
-/

@[expose] public section

open Real Set Finset

namespace BaseRange

/-! ### The named hypotheses -/

/-- **Lemma 7.3(b)** (smooth part), on `Good(<xmax)`: `|μ₀(u)| ≤ 2κ (log u)³` for
`X₀ ≤ u ≤ xmax`. Here `μ₀` is the realised smooth part of §7.2,
`μ₀ = (K^sh_ℚ - K_pt)(f₀ 1_{[X₀,∞)}) + (K_ℚ - K^sh_ℚ)(MA[ℙ] 1_{[X₀,∞)}) + O(1/(κx))`. -/
def Lemma73b (X0 : ℕ) (xmax : ℝ) (μ0 : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, (X0 : ℝ) ≤ u → u ≤ xmax →
    |μ0 u| ≤ 2 * Construction.kappaParam X0 * Real.log u ^ 3

/-- **Lemma 7.3(c)** (Huxley-error part), on `Good(<xmax)`: with `Λ = log X₀`,
`v = log x/Λ`, `U = 1 + 2 log v`, for `X₀ ≤ x ≤ xmax`,
`|μ₁(x)| ≤ 2Λ⁻³ (log v + 1.01)`, and for `v ≥ 4`,
`|μ₁(x)| ≤ 2 [(U/log x)³ (log U + 1.01) + 2e^γ e^{Ein(2)} (v/U) v⁻⁴ Λ⁻³]`.
Here `μ₁ = (K^sh_ℚ - K_pt)(f₁ 1_{[X₀,∞)})` (correction #74). -/
def Lemma73c (X0 : ℕ) (xmax : ℝ) (μ1 : ℝ → ℝ) : Prop :=
  Mu1Pointwise X0 (fun x => if x ≤ xmax then μ1 x else 0)

/-- **Lemma 7.3(d)(iii)**, on `Good(<xmax)`: for `x ≥ X₀^{1.01}/2` with `log x ≤ X₀^{1/100}`
(and `x ≤ xmax`), `|ρ_edge(x)| log x ≤ 3X₀^{-0.01} + X₀^{-0.34}`. -/
def Lemma73diii (X0 : ℕ) (xmax : ℝ) (ρedge : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, (X0 : ℝ) ^ (1.01 : ℝ) / 2 ≤ x → Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ) → x ≤ xmax →
    |ρedge x| * Real.log x ≤ 3 * (X0 : ℝ) ^ (-0.01 : ℝ) + (X0 : ℝ) ^ (-0.34 : ℝ)

/-- The realised inputs of Lemma 7.3 (parts (b), (c), (d)) at the horizon `xmax`. -/
structure Lemma73Inputs (X0 : ℕ) (xmax : ℝ) (μ0 μ1 ρedge : ℝ → ℝ) : Prop where
  b : Lemma73b X0 xmax μ0
  c : Lemma73c X0 xmax μ1
  edge : EdgeExpansion X0 ρedge
  d_iii : Lemma73diii X0 xmax ρedge

/-! ### (c) up to the horizon -/

lemma Lemma73c.bound1 {X0 : ℕ} {xmax : ℝ} {μ1 : ℝ → ℝ} (h : Lemma73c X0 xmax μ1) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) (hxm : x ≤ xmax) :
    |μ1 x| ≤ 2 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 1.01) := by
  have := h.1 x hx
  simp only [if_pos hxm] at this
  exact this

lemma Lemma73c.bound2 {X0 : ℕ} {xmax : ℝ} {μ1 : ℝ → ℝ} (h : Lemma73c X0 xmax μ1) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) (hxm : x ≤ xmax) (hv : 4 ≤ Real.log x / Real.log X0) :
    |μ1 x| ≤ 2 * ((BSCert.Consts.Uf (Real.log x / Real.log X0) / Real.log x) ^ 3 *
          (Real.log (BSCert.Consts.Uf (Real.log x / Real.log X0)) + 1.01) +
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (BSCert.EiFn.Ein 2) *
          ((Real.log x / Real.log X0) / BSCert.Consts.Uf (Real.log x / Real.log X0)) /
          (Real.log x / Real.log X0) ^ 4 / Real.log X0 ^ 3) := by
  have := h.2 x hx hv
  simp only [if_pos hxm] at this
  exact this

/-- The two bounds of `Lemma73c` are nonnegative, so `Lemma73c` follows from the bounds on
`[X₀, xmax]` alone. -/
theorem lemma73c_of_upTo {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {xmax : ℝ} {μ1 : ℝ → ℝ}
    (h1 : ∀ x, (X0 : ℝ) ≤ x → x ≤ xmax →
      |μ1 x| ≤ 2 / Real.log X0 ^ 3 * (Real.log (Real.log x / Real.log X0) + 1.01))
    (h2 : ∀ x, (X0 : ℝ) ≤ x → x ≤ xmax → 4 ≤ Real.log x / Real.log X0 →
      |μ1 x| ≤ 2 * ((BSCert.Consts.Uf (Real.log x / Real.log X0) / Real.log x) ^ 3 *
          (Real.log (BSCert.Consts.Uf (Real.log x / Real.log X0)) + 1.01) +
        2 * Real.exp Real.eulerMascheroniConstant * Real.exp (BSCert.EiFn.Ein 2) *
          ((Real.log x / Real.log X0) / BSCert.Consts.Uf (Real.log x / Real.log X0)) /
          (Real.log x / Real.log X0) ^ 4 / Real.log X0 ^ 3)) :
    Lemma73c X0 xmax μ1 := by
  have hΛ0 : 0 < Real.log X0 := by linarith
  have hv1 : ∀ x, (X0 : ℝ) ≤ x → 1 ≤ Real.log x / Real.log X0 := by
    intro x hx
    rw [le_div_iff₀ hΛ0, one_mul]
    exact Real.log_le_log (by linarith [one_lt_of_log hX]) hx
  constructor
  · intro x hx
    simp only
    split_ifs with hxm
    · exact h1 x hx hxm
    · simp only [abs_zero]
      have := Real.log_nonneg (hv1 x hx)
      positivity
  · intro x hx hv
    simp only
    split_ifs with hxm
    · exact h2 x hx hxm hv
    · simp only [abs_zero]
      have hv0 : 0 < Real.log x / Real.log X0 := by linarith
      have hU := Uf_ge_one (hv1 x hx)
      have hlU := log_Uf_nonneg (hv1 x hx)
      have hlx : 0 < Real.log x := by
        have := hv1 x hx; rw [le_div_iff₀ hΛ0, one_mul] at this; linarith
      positivity

/-- **(87)** (`eq:mu1sum`) at the horizon: if the blocks `[2ʲX₀, 2ʲ⁺¹X₀]`, `j < J`, lie below
`xmax`, then `∑_{j<J} log(2u_j) sup_{[u_j, 2u_j]} |μ₁| ≤ 690/log X₀ ≤ 7·10⁻⁶`. -/
theorem mu1sum_upTo {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {xmax : ℝ} {μ1 : ℝ → ℝ}
    (h : Lemma73c X0 xmax μ1) {J : ℕ} (hJ : 2 ^ J * (X0 : ℝ) ≤ xmax) :
    ∑ j ∈ Finset.range J, dyTerm X0 μ1 j ≤ 690 / Real.log X0 ∧
      690 / Real.log X0 ≤ 7e-6 := by
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  have hsum := mu1sum_partial h hX0 hX J
  refine ⟨le_trans (le_of_eq ?_) hsum, BSCert.Consts.m6 hX⟩
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
  unfold dyTerm blockSup
  congr 2
  apply Set.image_congr
  intro x hx
  have h2 : 2 * (2 ^ j * (X0 : ℝ)) ≤ xmax := by
    refine le_trans ?_ hJ
    have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
    rw [pow_succ] at this
    nlinarith
  simp only [if_pos (hx.2.trans h2)]

/-! ### "Use" -/

/-- "Use", (b): `log x (log x + 1) · 2κ (log x)³ ≤ 2.1κ (log x)⁵ ≤ X₀^{-0.34}` for
`x ≥ X₀` and `log x ≤ X₀^{1/100}` (the response to `μ₀` through Lemma M, `B₁ = 1`). -/
theorem use_mu0 {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {x : ℝ} (hx : (X0 : ℝ) ≤ x)
    (hxl : Real.log x ≤ (X0 : ℝ) ^ (1 / 100 : ℝ)) :
    Real.log x * (Real.log x + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3) ≤
      (X0 : ℝ) ^ (-0.34 : ℝ) := by
  have hL := log_ge_of_ge hX hx
  have hκ0 := (BModel.kappa_facts hX).1
  have h := kappa_log5_le hX (c := 2.1) (by norm_num) (by linarith) hxl
  have hk : 0 ≤ Construction.kappaParam X0 * Real.log x ^ 4 := by positivity
  have : Real.log x * (Real.log x + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3) ≤
      2.1 * (Construction.kappaParam X0 * Real.log x ^ 5) := by
    have e1 : Real.log x * (Real.log x + 1) * (2 * Construction.kappaParam X0 * Real.log x ^ 3)
        = (2 * Real.log x + 2) * (Construction.kappaParam X0 * Real.log x ^ 4) := by ring
    have e2 : 2.1 * (Construction.kappaParam X0 * Real.log x ^ 5) =
        2.1 * Real.log x * (Construction.kappaParam X0 * Real.log x ^ 4) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) hk
  linarith

/-- "Use", range (A) of Proposition 5.35 on `[X₀ + H, X₀^{1.01}]`: with `L = log x`, if
`MA[ℙ](x) L ≥ 0.99` (Lemma 7.3(a)), `ρ_edge(x) L ≥ -0.167` ((d)(ii)), and the responses to
`μ₀`, `μ₁` and the absorbed source are at most `X₀^{-0.34}`, `6·10⁻⁴`, `e^{-80}` in absolute
value after multiplying by `L`, then `ρ^sh(x) L ≥ 0.822`. -/
theorem use_rangeA_low {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {L ma re r0 r1 rA : ℝ}
    (hma : 0.99 ≤ ma * L) (hre : -0.167 ≤ re * L) (hr0 : |r0 * L| ≤ (X0 : ℝ) ^ (-0.34 : ℝ))
    (hr1 : |r1 * L| ≤ 6e-4) (hrA : |rA * L| ≤ Real.exp (-80)) :
    0.822 ≤ (ma + re + r0 + r1 + rA) * L := by
  have h := use_A_low hX
  have := neg_abs_le (r0 * L); have := neg_abs_le (r1 * L); have := neg_abs_le (rA * L)
  nlinarith

/-- "Use", range (A) on `[X₀^{1.01}/2, X_sw]`: with `|ρ_edge(x)| L ≤ 3X₀^{-0.01} + X₀^{-0.34}`
((d)(iii)), `ρ^sh(x) L ≥ 0.989 ≥ 0.97`. -/
theorem use_rangeA_high {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {L ma re r0 r1 rA : ℝ}
    (hma : 0.99 ≤ ma * L)
    (hre : |re * L| ≤ 3 * (X0 : ℝ) ^ (-0.01 : ℝ) + (X0 : ℝ) ^ (-0.34 : ℝ))
    (hr0 : |r0 * L| ≤ (X0 : ℝ) ^ (-0.34 : ℝ)) (hr1 : |r1 * L| ≤ 6e-4)
    (hrA : |rA * L| ≤ Real.exp (-80)) :
    0.989 ≤ (ma + re + r0 + r1 + rA) * L := by
  have h := use_A_high hX
  have := neg_abs_le (re * L); have := neg_abs_le (r0 * L); have := neg_abs_le (r1 * L)
  have := neg_abs_le (rA * L)
  nlinarith

/-! ### Lemma 7.3 -/

/-- **Lemma 7.3 (the margin decomposition)**, for `log X₀ ≥ 10⁸` and `X₀ ≥ X_Hux` (i.e. (84)
from `X₀` on), at the horizon `xmax` (the realised parts (b)–(d) on `Good(<xmax)`, as the
named hypotheses `Lemma73Inputs`):
* (a) `MA[ℙ](q) log q ≥ 1 - 10⁻²⁰ ≥ 0.99` for every `q ≥ X₀` (and it tends to `1`:
  `lemma_7_3_a_tendsto`);
* (b) `|μ₀(u)| ≤ 2κ (log u)³` for `X₀ ≤ u ≤ xmax`;
* (c) the pointwise bounds on `μ₁`, and (87): every dyadic partial sum below `xmax` of
  `log(2u) sup_{[u,2u]} |μ₁|` is at most `690/log X₀ ≤ 7·10⁻⁶`;
* (d)(i) `ρ_edge(x) = -∑_{N ≥ 2: x/N ∈ (X₀/(1+κ), X₀)} μ(N) MA[ℙ](x/N)/N` for
  `X₀ ≤ x ≤ X₀^{1.9}`;
* (d)(ii) `ρ_edge(x) log x ≥ -0.167` for `X₀ ≤ x ≤ X₀^{1.01}`;
* (d)(iii) `|ρ_edge(x)| log x ≤ 3X₀^{-0.01} + X₀^{-0.34}` for `X₀^{1.01}/2 ≤ x ≤ xmax`,
  `log x ≤ X₀^{1/100}`. -/
theorem lemma_7_3 {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) {xmax : ℝ}
    {μ0 μ1 ρedge : ℝ → ℝ} (h : Lemma73Inputs X0 xmax μ0 μ1 ρedge) :
    (∀ q : ℝ, (X0 : ℝ) ≤ q →
        1 - 1 / 10 ^ 20 ≤ MAP X0 (Construction.kappaParam X0) q * Real.log q ∧
        0.99 ≤ MAP X0 (Construction.kappaParam X0) q * Real.log q) ∧
    (∀ u : ℝ, (X0 : ℝ) ≤ u → u ≤ xmax →
        |μ0 u| ≤ 2 * Construction.kappaParam X0 * Real.log u ^ 3) ∧
    (∀ J : ℕ, 2 ^ J * (X0 : ℝ) ≤ xmax →
        ∑ j ∈ Finset.range J, dyTerm X0 μ1 j ≤ 690 / Real.log X0 ∧
          690 / Real.log X0 ≤ 7e-6) ∧
    (∀ x : ℝ, (X0 : ℝ) ≤ x → x ≤ (X0 : ℝ) ^ (1.9 : ℝ) →
        ρedge x = edgeFormula X0 (Construction.kappaParam X0) x) ∧
    (∀ x : ℝ, (X0 : ℝ) ≤ x → x ≤ (X0 : ℝ) ^ (1.01 : ℝ) → -0.167 ≤ ρedge x * Real.log x) ∧
    Lemma73diii X0 xmax ρedge :=
  ⟨fun _ hq => ⟨(lemma_7_3_a hX hH hq).1, lemma_7_3_a_099 hX hH hq⟩, h.b,
    fun _ hJ => mu1sum_upTo hX h.c hJ,
    fun _ hx1 hx => lemma_7_3_d_i hX h.edge hx1 hx,
    fun _ hx1 hx => lemma_7_3_d_ii hX hH h.edge hx1 hx, h.d_iii⟩

end BaseRange
