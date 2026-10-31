module

public import RequestProject.Beurling.Theorem410
public import RequestProject.Beurling.LateNoise
public import RequestProject.Beurling.OscBounds

/-!
# Theorem 4.10 from Lemmas 4.2, 4.4, 4.6–4.8, the lag bound (13) and the decomposition (14)

The proof of Theorem 4.10 bounds the perturbation
`ζ_P - (Z_B + M_k) = E_k + ∑_{j≠k} R̂_j + D̂_{<a_k} + D̂_{≥a_k} + Ê_A`
on the Rouché circle of Lemma 4.6. Here:

* `E_k` and `∑_{j≠k} R̂_j` are bounded by the bullets after (17) (proved in `OscBounds` and below);
* `D̂_{≥a_k}` is bounded by Lemma 4.7 (proved in `LateNoise`, from the lag bound (13));
* `D̂_{<a_k}` is bounded by Lemma 4.8(ii) and `Ê_A` by Lemma 4.4(a) (both assumed).

`Theorem410InputsPaper` collects these inputs (with the decomposition (14) and the hypotheses of
Lemma 4.6, which include the bounds on `Z_B` from Lemma 4.2), and
`Theorem410InputsPaper.circle` derives the circle form of the inputs of Theorem 4.10.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory SmoothStep Oscillation BeurlingSystem

namespace DesignedZero

/-- **Earlier oscillations** (`j < k`): if `γ_k ≥ 2γ_j + 5`, then on `0.99 ≤ σ ≤ 1.01`,
`|t - γ_k| ≤ 1`, `|R̂_j(s)| ≤ 4 x_j^{-2/5}`. -/
theorem norm_oscHat_le_of_lt {θ α γj xj γk : ℝ} (hxj : 1 ≤ xj) (hα : |α| ≤ 2)
    (hθ : θ ≤ 1 / 2) (hγj : 0 ≤ γj) (hγk : 2 * γj + 5 ≤ γk) {s : ℂ} (hσ1 : 99 / 100 ≤ s.re)
    (hσ2 : s.re ≤ 101 / 100) (ht : |s.im - γk| ≤ 1) :
    ‖oscHat θ α γj xj s‖ ≤ 4 * xj ^ (-(2 / 5 : ℝ)) := by
  have hxj0 : 0 < xj := by linarith
  rw [oscHat_eq_Mk_add_Ek hxj (by linarith)]
  set w := s - θ - γj * I with hw
  set w' := s - θ + γj * I with hw'
  have hre : w.re = s.re - θ := by simp [hw]
  have hre' : w'.re = s.re - θ := by simp [hw']
  have h1 := norm_term_le (α := α) hxj hre (by rw [hre]; linarith)
  have h2 := norm_term_le (α := α) hxj hre' (by rw [hre']; linarith)
  have ht' := abs_le.mp ht
  have hsn : ‖s‖ ≤ γk + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at this; linarith
  have hwn : γk - 1 - γj ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    have him : w.im = s.im - γj := by simp [hw]
    rw [him] at this
    exact le_trans (by rw [abs_of_pos (by linarith)]; linarith) this
  have hw'n : γk - 1 ≤ ‖w'‖ := by
    have := Complex.abs_im_le_norm w'
    have him : w'.im = s.im + γj := by simp [hw']
    rw [him] at this
    exact le_trans (by rw [abs_of_pos (by linarith)]; linarith) this
  have hX : xj ^ (θ - s.re) ≤ xj ^ (-(2 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hxj (by linarith)
  have hX0 := Real.rpow_nonneg hxj0.le (θ - s.re)
  have hX1 := Real.rpow_nonneg hxj0.le (-(2 / 5 : ℝ))
  have hr1 : ‖s‖ / ‖w‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hr2 : ‖s‖ / ‖w'‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hα2 : |α| / 2 ≤ 1 := by linarith
  unfold Mk Ek
  rw [← hw, ← hw']
  calc _ ≤ ‖α * s / 2 * ((xj : ℂ) ^ (-w) * phiTransform w / w)‖ +
        ‖α * s / 2 * ((xj : ℂ) ^ (-w') * phiTransform w' / w')‖ := norm_add_le _ _
    _ ≤ |α| * ‖s‖ / 2 * (xj ^ (θ - s.re) / ‖w‖) + |α| * ‖s‖ / 2 * (xj ^ (θ - s.re) / ‖w'‖) :=
        add_le_add h1 h2
    _ = |α| / 2 * (‖s‖ / ‖w‖) * xj ^ (θ - s.re) + |α| / 2 * (‖s‖ / ‖w'‖) * xj ^ (θ - s.re) := by
        ring
    _ ≤ 1 * 2 * xj ^ (-(2 / 5 : ℝ)) + 1 * 2 * xj ^ (-(2 / 5 : ℝ)) := by
        gcongr
    _ = 4 * xj ^ (-(2 / 5 : ℝ)) := by ring

/-- `x_k ≥ 20` for all `k`, `x_k` increasing, and `x_j ≤ log x_k` for `j < k`, under the spacing
`x_0 ≥ 20`, `x_{k+1} ≥ e^{x_k}`. -/
lemma spacing_facts {xp : ℕ → ℝ} (h0 : 20 ≤ xp 0) (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) :
    (∀ k, 20 ≤ xp k) ∧ Monotone xp ∧ ∀ j k, j < k → xp j ≤ Real.log (xp k) := by
  have hstep : ∀ k, xp k + 1 ≤ xp (k + 1) := fun k => by
    have := Real.add_one_le_exp (xp k); linarith [hsp k]
  have hge : ∀ k, 20 ≤ xp k := by
    intro k; induction k with
    | zero => exact h0
    | succ n ih => linarith [hstep n]
  have hmono : Monotone xp := monotone_nat_of_le_succ fun k => by linarith [hstep k]
  refine ⟨hge, hmono, fun j k hjk => ?_⟩
  have h1 : xp j ≤ Real.log (xp (j + 1)) := by
    rw [Real.le_log_iff_exp_le (by linarith [hge (j + 1)])]; exact hsp j
  exact h1.trans (Real.log_le_log (by linarith [hge (j + 1)]) (hmono hjk))

/-- **The other oscillations** (`j ≠ k`): on `0.99 ≤ σ ≤ 1.01`, `|t - γ_k| ≤ 1`, if `|α_j| ≤ 2`,
`γ_j ≥ 0`, `γ_k ≥ 2γ_j + 5` for `j < k`, and the spacing holds, then
`|∑_j R̂_j(s) - R̂_k(s)| ≤ 8 x_0^{-2/5} + 10 |s| x_{k+1}^{-2/5}`. -/
theorem norm_tsum_oscHat_sub_le {θ : ℝ} {α γ xp : ℕ → ℝ} (hα : ∀ j, |α j| ≤ 2)
    (hθ : θ ≤ 1 / 2) (hγ : ∀ j, 0 ≤ γ j) (h0 : 20 ≤ xp 0)
    (hsp : ∀ k, Real.exp (xp k) ≤ xp (k + 1)) {k : ℕ} (hγk : ∀ j < k, 2 * γ j + 5 ≤ γ k)
    {s : ℂ} (hσ1 : 99 / 100 ≤ s.re) (hσ2 : s.re ≤ 101 / 100) (ht : |s.im - γ k| ≤ 1) :
    ‖(∑' j, oscHat θ (α j) (γ j) (xp j) s) - oscHat θ (α k) (γ k) (xp k) s‖ ≤
      8 * xp 0 ^ (-(2 / 5 : ℝ)) + 10 * ‖s‖ * xp (k + 1) ^ (-(2 / 5 : ℝ)) := by
  obtain ⟨hge, -, -⟩ := spacing_facts h0 hsp
  have hge1 : ∀ j, 1 ≤ xp j := fun j => by linarith [hge j]
  have hσ : θ + 2 / 5 ≤ s.re := by linarith
  set f : ℕ → ℂ := fun j => oscHat θ (α j) (γ j) (xp j) s with hf
  have hbound : ∀ j, ‖f j‖ ≤ 5 * ‖s‖ * xp j ^ (-(2 / 5 : ℝ)) := fun j =>
    norm_oscHat_le_of_re (γ := γ j) (hge1 j) (hα j) hσ
  have hgeom := rpow_neg_two_fifths_le_geom h0 hsp
  have hsumN : Summable fun j => ‖f j‖ := by
    refine ((summable_geometric_two).mul_left (5 * ‖s‖ * xp 0 ^ (-(2 / 5 : ℝ)))).of_nonneg_of_le
      (fun j => norm_nonneg _) fun j => ?_
    refine (hbound j).trans ?_
    have := hgeom j
    calc 5 * ‖s‖ * xp j ^ (-(2 / 5 : ℝ)) ≤ 5 * ‖s‖ * (xp 0 ^ (-(2 / 5 : ℝ)) * (1 / 2) ^ j) := by
          gcongr
      _ = _ := by ring
  have hsum : Summable f := hsumN.of_norm
  have hsplit : (∑' j, f j) - f k = (∑ j ∈ Finset.range k, f j) + ∑' i, f (i + (k + 1)) := by
    rw [← hsum.sum_add_tsum_nat_add (k + 1), Finset.sum_range_succ]; ring
  rw [show (∑' j, oscHat θ (α j) (γ j) (xp j) s) - oscHat θ (α k) (γ k) (xp k) s =
    (∑' j, f j) - f k from rfl, hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the finitely many earlier oscillations
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range k, ‖f j‖ ≤ ∑ j ∈ Finset.range k,
          4 * xp 0 ^ (-(2 / 5 : ℝ)) * (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk := Finset.mem_range.mp hj
          refine (norm_oscHat_le_of_lt (hge1 j) (hα j) hθ (hγ j) (hγk j hjk) hσ1 hσ2 ht).trans ?_
          have := hgeom j
          calc 4 * xp j ^ (-(2 / 5 : ℝ)) ≤ 4 * (xp 0 ^ (-(2 / 5 : ℝ)) * (1 / 2) ^ j) := by
                gcongr
            _ = _ := by ring
      _ = 4 * xp 0 ^ (-(2 / 5 : ℝ)) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ 4 * xp 0 ^ (-(2 / 5 : ℝ)) * 2 := by
          gcongr
          exact sum_geometric_two_le k
      _ = 8 * xp 0 ^ (-(2 / 5 : ℝ)) := by ring
  · -- the later oscillations
    have h0' : 20 ≤ xp (0 + (k + 1)) := hge _
    have hsp' : ∀ i, Real.exp (xp (i + (k + 1))) ≤ xp (i + 1 + (k + 1)) := fun i => by
      rw [show i + 1 + (k + 1) = (i + (k + 1)) + 1 by ring]; exact hsp _
    have hgeom' := rpow_neg_two_fifths_le_geom (xp := fun i => xp (i + (k + 1))) h0' hsp'
    simp only [zero_add] at hgeom'
    have hb' : ∀ i, ‖f (i + (k + 1))‖ ≤
        5 * ‖s‖ * xp (k + 1) ^ (-(2 / 5 : ℝ)) * (1 / 2 : ℝ) ^ i := fun i => by
      refine (hbound _).trans ?_
      have := hgeom' i
      calc 5 * ‖s‖ * xp (i + (k + 1)) ^ (-(2 / 5 : ℝ)) ≤
            5 * ‖s‖ * (xp (k + 1) ^ (-(2 / 5 : ℝ)) * (1 / 2) ^ i) := by gcongr
        _ = _ := by ring
    have hg2 : Summable fun i : ℕ => 5 * ‖s‖ * xp (k + 1) ^ (-(2 / 5 : ℝ)) * (1 / 2 : ℝ) ^ i :=
      (summable_geometric_two).mul_left _
    have hsumN' : Summable fun i => ‖f (i + (k + 1))‖ :=
      hg2.of_nonneg_of_le (fun i => norm_nonneg _) hb'
    refine (norm_tsum_le_tsum_norm hsumN').trans ?_
    refine (hsumN'.tsum_le_tsum hb' hg2).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_two]; ring

namespace Lemma46Hyp

variable {θ Λ κ₀ α γ x : ℝ} {ZB : ℂ → ℂ}

lemma L_ge_big (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : 2 * 10 ^ 8 ≤ Real.log x := by
  have h1 := h.big; have h2 := h.logL_ge; have h3 := h.Λ_ge
  have : (1000 : ℝ) ≤ Λ ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) h3 3; norm_num at this; linarith
  nlinarith

lemma x_eq_exp (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : x = Real.exp (Real.log x) :=
  (Real.exp_log (by linarith [h.one_lt_x])).symm

lemma rpow_eq_exp (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) (r : ℝ) :
    x ^ r = Real.exp (Real.log x * r) :=
  Real.rpow_def_of_pos (by linarith [h.one_lt_x]) r

lemma x_ge (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) : 10 ^ 10 ≤ x := by
  have hL := h.L_ge_big
  rw [h.x_eq_exp]
  have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log x by linarith)
  nlinarith

/-- `x^{-2/5} ≤ 10⁻⁷`. -/
lemma rpow_neg_two_fifths_le (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) :
    x ^ (-(2 / 5 : ℝ)) ≤ 1 / 10 ^ 7 := by
  have hL := h.L_ge_big
  rw [h.rpow_eq_exp, show Real.log x * (-(2 / 5 : ℝ)) = -(Real.log x * (2 / 5)) by ring,
    Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp (Real.log x * (2 / 5))
  norm_num at this ⊢; linarith

/-- `165 Λ x^{-θ/2} ≤ 1/100` (`θ ≥ 1/20`). -/
lemma lateNoise_numeric (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) :
    165 * Λ * x ^ (-(θ / 2)) ≤ 1 / 100 := by
  have hL := h.L_ge_big
  have hΛ := h.Λ_ge
  have hΛL : Λ ≤ Real.log x := by
    have := h.loglog_ge
    have := Real.log_le_sub_one_of_pos h.L_pos
    linarith
  have hmono : x ^ (-(θ / 2)) ≤ x ^ (-(1 / 40 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h.one_lt_x.le (by linarith [h.θ_ge])
  refine le_trans (mul_le_mul_of_nonneg_left hmono (by linarith)) ?_
  rw [h.rpow_eq_exp, show Real.log x * (-(1 / 40 : ℝ)) = -(Real.log x / 40) by ring, Real.exp_neg]
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Real.log x / 40 by linarith)
  have hpos := Real.exp_pos (Real.log x / 40)
  rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- `γ ≥ 2 log x + 5`, from `α γ = κ₀ x^{1-θ}/log³ x`, `α ≤ 2`, `κ₀ ≥ e^{-Λ}`. -/
lemma γ_ge_log (h : Lemma46Hyp θ Λ κ₀ α γ x ZB) (hα : α ≤ 2) :
    2 * Real.log x + 5 ≤ γ := by
  have hL := h.L_ge_big
  have hLp := h.L_pos
  set L := Real.log x with hLdef
  have hκ : 1 / L ≤ κ₀ := by
    refine le_trans ?_ h.κ_ge
    have : Λ ≤ Real.log L := by linarith [h.loglog_ge, h.Λ_ge]
    have e : 1 / L = Real.exp (-Real.log L) := by rw [Real.exp_neg, Real.exp_log hLp, one_div]
    rw [e, Real.exp_le_exp]
    linarith
  have hxθ : Real.exp (L / 2) ≤ x ^ (1 - θ) := by
    rw [h.rpow_eq_exp, Real.exp_le_exp, ← hLdef]
    have := h.θ_le; nlinarith
  have hγ : γ = κ₀ * x ^ (1 - θ) / L ^ 3 / α := by
    rw [← h.αγ_eq]; field_simp [h.α_pos.ne']
  have hexp : (L / 2) ^ 6 / 720 ≤ Real.exp (L / 2) := by
    have := Real.pow_div_factorial_le_exp (L / 2) (by linarith) 6
    norm_num [Nat.factorial] at this ⊢; linarith
  have hlow : Real.exp (L / 2) / (2 * L ^ 4) ≤ γ := by
    rw [hγ, div_div, div_le_div_iff₀ (by positivity) (by have := h.α_pos; positivity)]
    have hα0 := h.α_pos
    have hκ0 : 0 ≤ κ₀ := le_trans (by positivity) hκ
    have e1 : Real.exp (L / 2) * (L ^ 3 * α) ≤ Real.exp (L / 2) * (L ^ 3 * 2) := by gcongr
    have e2 : Real.exp (L / 2) * (L ^ 3 * 2) = (1 / L) * Real.exp (L / 2) * (2 * L ^ 4) := by
      field_simp
    have e3 : (1 / L) * Real.exp (L / 2) * (2 * L ^ 4) ≤ κ₀ * x ^ (1 - θ) * (2 * L ^ 4) := by
      gcongr
    linarith
  refine le_trans ?_ hlow
  rw [le_div_iff₀ (by positivity)]
  have h6 : (2 * L + 5) * (2 * L ^ 4) ≤ (L / 2) ^ 6 / 720 := by
    have hL5 : (2 * L + 5) * (2 * L ^ 4) ≤ 5 * L ^ 5 := by nlinarith [pow_pos hLp 4]
    have : 5 * L ^ 5 ≤ (L / 2) ^ 6 / 720 := by
      have : (L / 2) ^ 6 / 720 = L ^ 5 * (L / 46080) := by ring
      rw [this]
      have : (5 : ℝ) ≤ L / 46080 := by rw [le_div_iff₀ (by norm_num)]; linarith
      nlinarith [pow_pos hLp 5]
    linarith
  linarith

end Lemma46Hyp

/-- `10 (y + 3) e^{-2y/5} ≤ 1/100` for `y ≥ 10⁵`. -/
lemma tail_numeric {y : ℝ} (hy : 10 ^ 5 ≤ y) :
    10 * (y + 3) * Real.exp (-(2 / 5) * y) ≤ 1 / 100 := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 / 5 * y by linarith)
  have hpos := Real.exp_pos (2 / 5 * y)
  rw [show -(2 / 5) * y = -(2 / 5 * y) by ring, Real.exp_neg, ← div_eq_mul_inv,
    div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- **The inputs of Theorem 4.10, as in its proof.** For the oscillation data `α_k ∈ [1, 2]`,
`γ_k ≤ x_k` with switch-on points `x_k` (`x_{k+1} ≥ e^{x_k}`), a fixed base factor `Z_B`
satisfying the hypotheses of Lemma 4.6 at every `k` (these include the bounds of Lemma 4.2), the
noise `D` with the lag bound `|D(y)| ≤ y^η` (13) beyond `a_k`, where `a_k ≤ x_k ≤ 1.001 a_k`, and
on each disc `|s - (1 + iγ_k)| ≤ δ_k`:

* the decomposition (14): `F = Z_B + ∑_j R̂_j + (D̂_{<a_k} + D̂_{≥a_k}) + Ê_A`;
* Lemma 4.8(ii): `|D̂_{<a_k}| ≤ 1/16`;
* Lemma 4.4(a): `|Ê_A| ≤ 1/16` (the paper proves `≤ e^{-10^{10}}`). -/
def Theorem410InputsPaper (θ : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ (Λ κ₀ η : ℝ) (α γ xp a : ℕ → ℝ) (ZB : ℂ → ℂ) (D : ℝ → ℝ) (Dlt EA : ℕ → ℂ → ℂ),
    (∀ k, Lemma46Hyp θ Λ κ₀ (α k) (γ k) (xp k) ZB) ∧
    (∀ k, 1 ≤ α k ∧ α k ≤ 2) ∧
    (∀ k, Real.exp (xp k) ≤ xp (k + 1)) ∧
    (∀ k, γ k ≤ xp k) ∧
    0 ≤ η ∧ η ≤ θ / 2 ∧
    (∀ k, 0 < a k ∧ a k ≤ xp k ∧ xp k ≤ (1 + 1 / 1000) * a k) ∧
    (∀ k, ∀ y ≥ a k, |D y| ≤ y ^ η) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)),
      F s = ZB s + (∑' j, oscHat θ (α j) (γ j) (xp j) s) + (Dlt k s + lateNoise D (a k) s) +
        EA k s) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)), ‖Dlt k s‖ ≤ 1 / 16) ∧
    (∀ k, ∀ s ∈ closedBall (1 + γ k * I) (designRadius (xp k)), ‖EA k s‖ ≤ 1 / 16)

/-- **The perturbation bound of Theorem 4.10**: from the paper-form inputs, on the Rouché circle
of Lemma 4.6, `|F - (Z_B + M_k)| ≤ |E_k| + |∑_{j≠k} R̂_j| + |D̂_{<a_k}| + |D̂_{≥a_k}| + |Ê_A| < 1/4`. -/
theorem Theorem410InputsPaper.circle {θ : ℝ} {F : ℂ → ℂ} (h : Theorem410InputsPaper θ F) :
    Theorem410InputsCircle θ F := by
  obtain ⟨Λ, κ₀, η, α, γ, xp, a, ZB, D, Dlt, EA, hH, hα, hsp, hγx, hη0, hη, ha, hD, hdec,
    hDlt, hEA⟩ := h
  have hx0 : 20 ≤ xp 0 := by linarith [(hH 0).x_ge]
  obtain ⟨hge, hmono, hlog⟩ := spacing_facts hx0 hsp
  have htend : Tendsto xp atTop atTop := by
    have hstep : ∀ k : ℕ, (k : ℝ) ≤ xp k := fun k => by
      induction k with
      | zero => simp; linarith
      | succ n ih =>
        have := Real.add_one_le_exp (xp n); have := hsp n; push_cast; linarith
    exact tendsto_atTop_mono hstep tendsto_natCast_atTop_atTop
  refine ⟨Λ, κ₀, α, γ, xp, fun _ => ZB, htend, hH, fun k s₀ hz hdisc s hs => ?_⟩
  have hk := hH k
  have hL := hk.L_pos
  have hδ := hk.δ_le
  -- `s` lies in the disc
  have hsm : s ∈ closedBall (1 + γ k * I) (designRadius (xp k)) := by
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_sphere, dist_eq_norm] at hs
    calc ‖s - (1 + γ k * I)‖ = ‖(s - s₀) + (s₀ - (1 + γ k * I))‖ := by ring_nf
      _ ≤ ‖s - s₀‖ + ‖s₀ - (1 + γ k * I)‖ := norm_add_le _ _
      _ ≤ designRadius (xp k) := by linarith
  have hsn : ‖s - (1 + γ k * I)‖ ≤ 1 / 10 ^ 6 := by
    rw [mem_closedBall, dist_eq_norm] at hsm; linarith
  have hre := Complex.abs_re_le_norm (s - (1 + γ k * I))
  have him := Complex.abs_im_le_norm (s - (1 + γ k * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.one_im, Complex.mul_im] at hre him
  norm_num at hre him
  have hσ1 : 99 / 100 ≤ s.re := by linarith [(abs_le.mp (hre.trans hsn)).1]
  have hσ2 : s.re ≤ 101 / 100 := by linarith [(abs_le.mp (hre.trans hsn)).2]
  have ht : |s.im - γ k| ≤ 1 := by linarith
  have hθ2 := hk.θ_le
  -- the decomposition and `R̂_k = M_k + E_k`
  have hRk := oscHat_eq_Mk_add_Ek (α := α k) (γ := γ k) (xk := xp k) (by linarith [hge k])
    (show θ < s.re by linarith)
  show ‖F s - (ZB s + Mk θ (α k) (γ k) (xp k) s)‖ < 1 / 4
  have hkey : F s - (ZB s + Mk θ (α k) (γ k) (xp k) s) =
      ((∑' j, oscHat θ (α j) (γ j) (xp j) s) - oscHat θ (α k) (γ k) (xp k) s) +
        Ek θ (α k) (γ k) (xp k) s + Dlt k s + lateNoise D (a k) s + EA k s := by
    rw [hdec k s hsm, hRk]; ring
  rw [hkey]
  -- the other oscillations
  have hαabs : ∀ j, |α j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hα j).1], (hα j).2⟩
  have hγ0 : ∀ j, 0 ≤ γ j := fun j => by linarith [(hH j).γ_ge]
  have hγlog := (hH k).γ_ge_log (hα k).2
  have hγk : ∀ j < k, 2 * γ j + 5 ≤ γ k := fun j hj => by
    have := hlog j k hj; have := hγx j; linarith
  have hsum := norm_tsum_oscHat_sub_le hαabs hθ2 hγ0 hx0 hsp hγk hσ1 hσ2 ht
  have hx0r := (hH 0).rpow_neg_two_fifths_le
  have hxk := (hH k).x_ge
  have hsnorm : ‖s‖ ≤ xp k + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have h1 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |s.im| ≤ γ k + 1 := by
      rw [abs_le]; have := abs_le.mp ht; constructor <;> linarith [hγ0 k]
    linarith [hγx k]
  have hnext : xp (k + 1) ^ (-(2 / 5 : ℝ)) ≤ Real.exp (-(2 / 5) * xp k) := by
    have := Real.rpow_le_rpow_of_nonpos (Real.exp_pos (xp k)) (hsp k)
      (show (-(2 / 5 : ℝ)) ≤ 0 by norm_num)
    rw [← Real.exp_mul] at this
    calc _ ≤ Real.exp (xp k * (-(2 / 5 : ℝ))) := this
      _ = _ := by ring_nf
  have htail := tail_numeric (show (10 : ℝ) ^ 5 ≤ xp k by linarith)
  have hR : ‖(∑' j, oscHat θ (α j) (γ j) (xp j) s) - oscHat θ (α k) (γ k) (xp k) s‖ ≤
      8 / 10 ^ 7 + 1 / 100 := by
    refine hsum.trans ?_
    have h1 : 8 * xp 0 ^ (-(2 / 5 : ℝ)) ≤ 8 / 10 ^ 7 := by linarith
    have h2 : 10 * ‖s‖ * xp (k + 1) ^ (-(2 / 5 : ℝ)) ≤ 1 / 100 := by
      have hp := Real.rpow_nonneg (show 0 ≤ xp (k + 1) by linarith [hge (k + 1)])
        (-(2 / 5 : ℝ))
      calc 10 * ‖s‖ * xp (k + 1) ^ (-(2 / 5 : ℝ)) ≤
            10 * (xp k + 3) * Real.exp (-(2 / 5) * xp k) := by
            gcongr
      _ ≤ 1 / 100 := htail
    linarith
  -- the conjugate term
  have hE : ‖Ek θ (α k) (γ k) (xp k) s‖ ≤ 51 / 10 ^ 9 := by
    have h1 := norm_Ek_le (θ := θ) (α := α k) (γ := γ k) (xk := xp k) (by linarith [hge k])
      (hαabs k) hθ2 (by linarith [(hH k).L_ge_big]) hσ1 (by linarith) ht
    have h2 : xp k ^ (θ - s.re) ≤ xp k ^ (-(2 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hge k]) (by linarith)
    have h3 := (hH k).rpow_neg_two_fifths_le
    linarith
  -- the late noise (Lemma 4.7)
  have hN := (hk.lemma_4_7 (hα k).1 hη0 hη (ha k).1 (ha k).2.1 (ha k).2.2 (hD k) hz hdisc s
    hs).2
  have hN' := hk.lateNoise_numeric
  have hD1 := hDlt k s hsm
  have hE1 := hEA k s hsm
  set A := (∑' j, oscHat θ (α j) (γ j) (xp j) s) - oscHat θ (α k) (γ k) (xp k) s
  set B := Ek θ (α k) (γ k) (xp k) s
  set C := Dlt k s
  set D' := lateNoise D (a k) s
  set E := EA k s
  have n1 := norm_add_le (A + B + C + D') E
  have n2 := norm_add_le (A + B + C) D'
  have n3 := norm_add_le (A + B) C
  have n4 := norm_add_le A B
  linarith

end DesignedZero

open DesignedZero Target

/-- Refined inputs for one system: part (i) with the concrete target (6), and the inputs of
Theorem 4.10 as in its proof (`Theorem410InputsPaper`) for the canonical continuation. -/
def TheoremAInputsPaper (θ : ℝ) (X₀ : ℕ) (P : BeurlingSystem) : Prop :=
  PartIInputsTarget θ X₀ P ∧ Theorem410InputsPaper θ (P.zetaCont 1)

theorem TheoremAInputsPaper.target {θ : ℝ} {X₀ : ℕ} {P : BeurlingSystem}
    (hθ : θ ≤ 1 / 2) (h : TheoremAInputsPaper θ X₀ P) : TheoremAInputsTarget θ X₀ P :=
  ⟨h.1, (θ + 1) / 2, by linarith, by linarith,
    theorem410Inputs_of_circle (by linarith) h.2.circle⟩

/-- **Theorem 2.1, refined hypothesis (Theorem 4.10 reduced to its inputs)**: as
`Theorem21InputsTarget`, but part (ii) is reduced to the inputs of the proof of Theorem 4.10:
the hypotheses of Lemma 4.6 (with the bounds of Lemma 4.2 on `Z_B`), the decomposition (14), the
lag bound (13) beyond `a_k`, Lemma 4.8(ii) and Lemma 4.4(a). Lemmas 4.6 and 4.7, the bounds on
the oscillations, the perturbation bound and Rouché's theorem are proved. -/
def Theorem21InputsPaper : Prop :=
  ∀ θ ∈ Set.Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000), ∃ XHux : ℝ, ∀ X₀ : ℕ, Even X₀ →
    Real.exp (10 ^ 8) ≤ X₀ → XHux ≤ X₀ →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (P : Ω → BeurlingSystem) (G : Set Ω),
      IsProbabilityMeasure μ ∧ ENNReal.ofReal (1 - 1.5 / Real.log X₀) ≤ μ G ∧
      ∀ ω ∈ G, TheoremAInputsPaper θ X₀ (P ω)

theorem theorem21InputsTarget_of_paper (h : Theorem21InputsPaper) : Theorem21InputsTarget := by
  intro θ hθ
  obtain ⟨XHux, hX⟩ := h θ hθ
  refine ⟨XHux, fun X₀ hev h1 h2 => ?_⟩
  obtain ⟨Ω, m, μ, P, G, hμ, hG, hP⟩ := hX X₀ hev h1 h2
  exact ⟨Ω, m, μ, P, G, hμ, hG, fun ω hω => (hP ω hω).target (by linarith [hθ.2])⟩

/-- The refined hypothesis (Theorem 4.10 reduced to its inputs) implies Theorem 2.1. -/
theorem theorem21_of_paper (h : Theorem21InputsPaper) : Theorem21 :=
  theorem21_of_target (theorem21InputsTarget_of_paper h)

/-- **Corollary 2.2** from the refined hypothesis (Theorem 4.10 reduced to its inputs). -/
theorem corollary_2_2_of_paper (h : Theorem21InputsPaper) : ¬ QuestionQ :=
  corollary_2_2 (theorem21_of_paper h)

end
