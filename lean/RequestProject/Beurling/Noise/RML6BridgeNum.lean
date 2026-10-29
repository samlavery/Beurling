module

public import RequestProject.Beurling.Noise.KRTrueX0
public import RequestProject.Beurling.Noise.KRWidthReal
public import RequestProject.Beurling.Noise.MarginChain2
public import RequestProject.Beurling.Noise.TauNearLocNum

/-!
# Bridge data for the realised margin: the numerical size facts

* `KR.X0S.sX0_sum_le` : **Proposition 5.18, step (iii), unweighted**: over every family of dyadic
  scales `v = X₀ 2^k`, `∑_v s⁰_v ≤ 1.52` (`s⁰ = sX0 X₀`, the block bound of step (iii)): the
  scale `X₀` gives `1/2`, the scales `v ≥ 2X₀` give `1.01 ∑ X₀/v ≤ 1.01`, and the second-bullet
  terms (`v > X₀²/4`) give `≤ 12.34 · 4/(0.35 X₀^{1/4}) ≤ 10⁻²³`.
* `KR.WidthReal.Phi_tiny` : `Φ_a(X₀⁻/2) ≤ e^{-200}` for `a ≤ 3` (under the width bound
  `H(X₀⁻/2) ≤ 2 (X₀⁻/2)^{1/8}`), a sharper form of `Phi_small_r`.
* `KR.Chain.sizeE_le` : the right side of Proposition 5.26 at the dyadic scales is `≤ e^{-76}`,
  given the first display of eq. (osc), `∑_u log(2u) o_u ≤ e^{-83}`; this is the paper's bound
  `E_BR ≤ 883 e^{-83} + 8.4 C_N E_θ ≤ e^{-76}`.
-/

@[expose] public section

open Finset Real

namespace KR.X0S

/-- **Step (iii) of Proposition 5.18, unweighted**: `∑_v s⁰_v ≤ 1.52` over dyadic scales,
for `X₀ ≥ 10⁹⁶`. -/
theorem sX0_sum_le {X0 : ℝ} (hX : (10 : ℝ) ^ 96 ≤ X0) {Sc : Finset ℝ} (hSc : Dyadic X0 Sc) :
    ∑ v ∈ Sc, sX0 X0 v ≤ 1.52 := by
  classical
  have hX0p : 0 < X0 := lt_of_lt_of_le (by positivity) hX
  have hSep := dyadic_sep hX0p hSc
  set s1 : ℝ → ℝ := fun v =>
    if v < X0 then 0 else if v < 2 * X0 then 1 / 2 else 1.01 * X0 / v
  set s2 : ℝ → ℝ := fun v => if X0 ^ 2 / 4 < v then 12.34 * X0 * r8 (2 * v) ^ 2 / v else 0
  have hs : ∀ v, sX0 X0 v = s1 v + s2 v := fun v => rfl
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  -- the first part
  have hA : ∑ v ∈ Sc, s1 v ≤ 1 / 2 + 1.01 := by
    rw [← Finset.sum_filter_add_sum_filter_not Sc (fun v => v < 2 * X0)]
    have hlow : ∑ v ∈ Sc.filter (fun v => v < 2 * X0), s1 v ≤ 1 / 2 := by
      have hb : ∀ v ∈ Sc.filter (fun v => v < 2 * X0), s1 v ≤
          if v = X0 then 1 / 2 else 0 := by
        intro v hv
        obtain ⟨hvS, hv2⟩ := Finset.mem_filter.mp hv
        simp only [s1]
        rcases lt_or_ge v X0 with hlt | hge
        · rw [if_pos hlt]; split_ifs <;> norm_num
        · have he := dyadic_eq hX0p hSc hvS hge hv2
          subst he
          rw [if_neg (lt_irrefl _), if_pos hv2, if_pos rfl]
      refine (Finset.sum_le_sum hb).trans ?_
      rw [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    have hhigh : ∑ v ∈ Sc.filter (fun v => ¬ v < 2 * X0), s1 v ≤ 1.01 := by
      set T := Sc.filter (fun v => ¬ v < 2 * X0)
      have hT : Sep2 T := sep_mono (Finset.filter_subset _ _) hSep
      have hTV : ∀ v ∈ T, 2 * X0 ≤ v := fun v hv => not_lt.mp (Finset.mem_filter.mp hv).2
      have hb : ∀ v ∈ T, s1 v = 1.01 * (X0 / v) := by
        intro v hv
        have h2 := hTV v hv
        simp only [s1]
        rw [if_neg (by linarith), if_neg (by linarith)]
        ring
      rw [Finset.sum_congr rfl hb, ← Finset.mul_sum]
      have := sum_g1 hX0p hT hTV
      linarith
    linarith
  -- the second part
  have hB : ∑ v ∈ Sc, s2 v ≤ 1 / 100 := by
    rw [← Finset.sum_filter_add_sum_filter_not Sc (fun v => X0 ^ 2 / 4 < v)]
    have hzero : ∑ v ∈ Sc.filter (fun v => ¬ X0 ^ 2 / 4 < v), s2 v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [s2]
      rw [if_neg (Finset.mem_filter.mp hv).2]
    rw [hzero, add_zero]
    set T := Sc.filter (fun v => X0 ^ 2 / 4 < v)
    have hT : Sep2 T := sep_mono (Finset.filter_subset _ _) hSep
    have hTV : ∀ v ∈ T, X0 ^ 2 / 4 ≤ v := fun v hv => (Finset.mem_filter.mp hv).2.le
    have hX2 : (1 : ℝ) ≤ X0 ^ 2 / 4 := by nlinarith
    have hb : ∀ v ∈ T, s2 v ≤ 12.34 * (X0 * r8 (2 * v) ^ 3 / v) := by
      intro v hv
      have hv1 : 1 ≤ v := hX2.trans (hTV v hv)
      have hv0 : 0 < v := by linarith
      simp only [s2]
      rw [if_pos (Finset.mem_filter.mp hv).2]
      have hr1 : 1 ≤ r8 (2 * v) := one_le_r8 (by linarith)
      have h23 : r8 (2 * v) ^ 2 ≤ r8 (2 * v) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hv0]
      have : 0 ≤ X0 := hX0p.le
      nlinarith
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have h3 := sum_g3 hX0p hT hTV
    have ht : (10 : ℝ) ^ 12 ≤ r8 X0 := by
      apply le_r8_of_pow8 (by positivity)
      calc ((10 : ℝ) ^ 12) ^ 8 = 10 ^ 96 := by norm_num
        _ ≤ X0 := hX
    have ht2 : (10 : ℝ) ^ 24 ≤ r8 X0 ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) ht 2
      calc (10 : ℝ) ^ 24 = (10 ^ 12) ^ 2 := by norm_num
        _ ≤ r8 X0 ^ 2 := this
    have h4 : 4 / r8 X0 ^ 2 / 0.35 ≤ 4 / 10 ^ 24 / 0.35 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) ht2
    have : (12.34 : ℝ) * (4 / 10 ^ 24 / 0.35) ≤ 1 / 100 := by norm_num
    nlinarith
  linarith

end KR.X0S

namespace KR.WidthReal

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- `16 e^{200} ℓ³ ≤ e^{7ℓ/8}` for `ℓ ≥ 10⁷`. -/
lemma num_tiny {ℓ : ℝ} (hℓ : 10000000 ≤ ℓ) :
    16 * Real.exp 200 * ℓ ^ 3 ≤ Real.exp (7 * ℓ / 8) := by
  set x := 7 * ℓ / 8 - 200 with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have h7 := Real.pow_div_factorial_le_exp x hx0 7
  norm_num [Nat.factorial] at h7
  have hxbig : 8000000 ≤ x := by rw [hx]; linarith
  have hℓx : ℓ ≤ 2 * x := by rw [hx]; linarith
  have hsplit : Real.exp (7 * ℓ / 8) = Real.exp 200 * Real.exp x := by
    rw [← Real.exp_add]; congr 1; rw [hx]; ring
  rw [hsplit]
  have he := Real.exp_pos 200
  have hl0 : 0 ≤ ℓ := by linarith
  have hl3 : ℓ ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hl0 hℓx 3
  have hx4 : (8000000 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hxbig 4
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hkey : 16 * ℓ ^ 3 ≤ Real.exp x := by
    nlinarith [mul_le_mul_of_nonneg_left hx4 hx3]
  nlinarith

/-- **`Φ_a(X₀⁻/2) ≤ e^{-200}`** for `a ≤ 3`, under `H(X₀⁻/2) ≤ 2(X₀⁻/2)^{1/8}`. -/
theorem Phi_tiny (h : TNP.Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {a : ℕ} (ha : a ≤ 3) :
    TNP.Phi H a (X0m / 2) ≤ Real.exp (-200) := by
  have hP := h.width
  have hX := hP.X0m_pos
  have hl := TNP.log_Pk_ge hX h.hXm 0
  rw [TNP.Pk_zero] at hl
  set ℓ := Real.log (X0m / 2)
  have hP0 : X0m / 2 = Real.exp ℓ := (Real.exp_log (by positivity)).symm
  have hb : 1 ≤ ℓ + 2 := by linarith
  have hpow : (ℓ + 2) ^ a ≤ (ℓ + 2) ^ 3 := pow_le_pow_right₀ hb ha
  have h3 : (ℓ + 2) ^ 3 ≤ 2 * ℓ ^ 3 := by nlinarith [sq_nonneg ℓ]
  have hc := num_tiny hl
  have hr : (X0m / 2) ^ (1 / 8 : ℝ) = Real.exp (ℓ / 8) := by
    rw [hP0, ← Real.exp_mul]; ring_nf
  have hsplit' : X0m / 2 = Real.exp (ℓ / 8) * Real.exp (7 * ℓ / 8) := by
    rw [← Real.exp_add, show ℓ / 8 + 7 * ℓ / 8 = ℓ by ring, ← hP0]
  unfold TNP.Phi
  have he8 := Real.exp_pos (ℓ / 8)
  have he78 := Real.exp_pos (7 * ℓ / 8)
  have he200 := Real.exp_pos 200
  rw [hr] at hH
  have hpos : 0 ≤ (ℓ + 2) ^ a := by positivity
  have hm : Real.exp (-200) * Real.exp 200 = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ (by positivity)]
  calc H (X0m / 2) * (ℓ + 2) ^ a ≤ (2 * Real.exp (ℓ / 8)) * (2 * ℓ ^ 3) := by
        gcongr; exact hpow.trans h3
    _ ≤ Real.exp (-200) * (Real.exp (ℓ / 8) * Real.exp (7 * ℓ / 8)) := by
        have h1 : Real.exp (-200) * (16 * Real.exp 200 * ℓ ^ 3) ≤
            Real.exp (-200) * Real.exp (7 * ℓ / 8) :=
          mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
        have h2 : Real.exp (-200) * (16 * Real.exp 200 * ℓ ^ 3) = 16 * ℓ ^ 3 := by
          rw [show Real.exp (-200) * (16 * Real.exp 200 * ℓ ^ 3) =
            (Real.exp (-200) * Real.exp 200) * (16 * ℓ ^ 3) by ring, hm, one_mul]
        nlinarith
    _ = Real.exp (-200) * (X0m / 2) := by rw [← hsplit']

end KR.WidthReal

namespace KR.Chain

open KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

lemma CNc_bounds {X0 : ℝ} (hX0 : 100000000 ≤ Real.log X0) : 0 ≤ CNc X0 ∧ CNc X0 ≤ 158 := by
  have hPhi := BSaias.PhiInf_le (τ := 100000000) le_rfl
  have hCS : max (2.01 * BSaias.PhiInf 100000000) 1.4 ≤ 77 := by
    rw [max_le_iff]; constructor <;> linarith
  have hCS0 : (0 : ℝ) ≤ max (2.01 * BSaias.PhiInf 100000000) 1.4 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hl : 0 < Real.log X0 := by linarith
  have h1 : 4.71 / Real.log X0 ≤ 4.71 / 100000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX0
  have h2 : 0 ≤ 4.71 / Real.log X0 := by positivity
  unfold CNc
  constructor
  · positivity
  · have : 2.04 + 4.71 / Real.log X0 ≤ 2.0401 := by
      have : (4.71 : ℝ) / 100000000 ≤ 0.0001 := by norm_num
      linarith
    nlinarith

lemma CSc_bounds : 0 ≤ CSc ∧ CSc ≤ 77 := by
  have hPhi := BSaias.PhiInf_le (τ := 100000000) le_rfl
  unfold CSc
  refine ⟨le_trans (by norm_num) (le_max_right _ _), ?_⟩
  rw [max_le_iff]; constructor <;> linarith

lemma exp7_ge : (1000 : ℝ) ≤ Real.exp 7 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h.le 7
  nlinarith

lemma exp_neg117_le : Real.exp (-117) ≤ 1 / 10 ^ 40 := by
  have h1 := Real.exp_one_gt_d9
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h20 : (20 : ℝ) ≤ Real.exp 3 := by
    rw [e3]
    have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
    have h3 : (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    linarith
  have e117 : Real.exp 117 = Real.exp 3 ^ 39 := by rw [← Real.exp_nat_mul]; norm_num
  have h39 : (20 : ℝ) ^ 39 ≤ Real.exp 3 ^ 39 := pow_le_pow_left₀ (by norm_num) h20 39
  have h40 : (10 : ℝ) ^ 40 ≤ Real.exp 117 := by
    rw [e117]
    have : (10 : ℝ) ^ 40 ≤ 20 ^ 39 := by norm_num
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) h40

/-- **`E_BR ≤ e^{-76}`** (proof of eq. (osc), last item): with `∑_u log(2u) o_u ≤ e^{-83}`
(the first display of eq. (osc)) and Lemma 5.20 at the cofactor horizon, the right side of
Proposition 5.26 at the dyadic scales of `y` is at most `e^{-76}`. -/
theorem sizeE_le (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ)
    (hH : H (X0m / 2) ≤ 2 * (X0m / 2) ^ (1 / 8 : ℝ)) {X0 y : ℝ} (hX0 : 100000000 ≤ Real.log X0)
    (hX0e : X0m = X0 - H X0 / 2) (hX0m : X0m ≤ X0) (hZ0 : 2500 ≤ Z) (h18 : 18 * y ≤ Z ^ 2)
    {N K : ℕ} (hK : √(2 * y) ≤ Pk X0m K) {o : ℝ → ℝ}
    (hosc : ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u ≤ Real.exp (-83)) :
    (5.1 * CNc X0 + CSc) * ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u +
      8.4 * CNc X0 * ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v ≤
        Real.exp (-76) := by
  obtain ⟨-, -, -, h4, hX0p⟩ := sizes h hX0e hX0m
  have h1 : Sep (dyScales X0 y N) := dyScales_sep hX0p
  have h2 : ∀ v ∈ dyScales X0 y N, 1 ≤ v := fun v hv => dyScales_ge h4 hv
  have h3 : ∀ v ∈ dyScales X0 y N, 18 * v ≤ Z ^ 2 := fun v hv => by
    have := dyScales_le hv; linarith
  have h5 : ∀ v ∈ dyScales X0 y N, √(2 * v) ≤ Pk X0m K := fun v hv =>
    sqrt_le_Pk hK (dyScales_le hv)
  have hθ := (thetaBlk_sum_loc h h1 h2 hZ0 h3 h5).2
  have hΦ := WidthReal.Phi_tiny h hH (a := 3) (by norm_num)
  obtain ⟨hCN0, hCN⟩ := CNc_bounds hX0
  obtain ⟨hCS0, hCS⟩ := CSc_bounds
  set S1 := ∑ u ∈ dyScales X0 y N, Real.log (2 * u) * o u
  set S2 := ∑ v ∈ dyScales X0 y N, Real.log (2 * v) * sTheta P H X0m K v
  have hS2 : S2 ≤ 2493700 * Real.exp (-200) := hθ.trans (by nlinarith)
  have hS20 : 0 ≤ S2 := by
    apply Finset.sum_nonneg
    intro v hv
    apply mul_nonneg (Real.log_nonneg (by linarith [h2 v hv]))
    exact blk_nonneg (P := P) (H := H) (X0m := X0m) h.width K
      (fun k => by have := log_Pk_ge h.width.X0m_pos h.hXm k; linarith) v
  have hA : 5.1 * CNc X0 + CSc ≤ 883 := by nlinarith
  have hA0 : 0 ≤ 5.1 * CNc X0 + CSc := by positivity
  have he83 : Real.exp (-76) = Real.exp 7 * Real.exp (-83) := by
    rw [← Real.exp_add]; norm_num
  have he200 : Real.exp (-200) = Real.exp (-117) * Real.exp (-83) := by
    rw [← Real.exp_add]; norm_num
  have he117 := exp_neg117_le
  have h83 := Real.exp_pos (-83)
  have he7 := exp7_ge
  have hS1 : (5.1 * CNc X0 + CSc) * S1 ≤ 883 * Real.exp (-83) := by
    rcases le_total 0 S1 with hS1 | hS1
    · exact (mul_le_mul_of_nonneg_left hosc hA0).trans
        (mul_le_mul_of_nonneg_right hA h83.le)
    · nlinarith
  have hT : 8.4 * CNc X0 * S2 ≤ 8.4 * 158 * (2493700 * (Real.exp (-117) * Real.exp (-83))) := by
    rw [← he200]
    apply mul_le_mul (by nlinarith) hS2 hS20 (by norm_num)
  have h117 : 8.4 * 158 * (2493700 * (Real.exp (-117) * Real.exp (-83))) ≤ Real.exp (-83) := by
    have : 8.4 * 158 * 2493700 * Real.exp (-117) ≤ 1 := by
      have : (8.4 : ℝ) * 158 * 2493700 * (1 / 10 ^ 40) ≤ 1 := by norm_num
      nlinarith [Real.exp_pos (-117)]
    nlinarith
  rw [he83]
  nlinarith

end KR.Chain

end
