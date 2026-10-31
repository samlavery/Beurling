module

public import RequestProject.Beurling.Model.KAbsL4
public import RequestProject.Beurling.Noise.RML6G1

/-!
# The `σ_𝒜` response on range (A) (`SigmaAResp`, Proposition 5.35(A), third bullet)

On range (A) (`log y ≤ X₀^{1/100}`, so `y < x₁ ≤ e^{X₀²}` and `R' = 0`), the source
`f = T' - 1_{[X₀,∞)}(1 - ρ_det)` is `σ_𝒜 = K_𝒜 ρ̃ - ρ̄_𝒜` (`f_eq`), and vanishes below `X₀`.
Both parts vanish unless `log u > L_* := Λ² e^{s_H} - 1` (Theorem 6.23(b):
`2y(x) < X₀` for `s ≤ s_H`; `absorbY_big`, `f_support`), and there `|f| ≤ max(K_𝒜 ρ̃, ρ̄_𝒜) ≤
L_u⁻⁴` (Lemma 6.27(a), (b): `rhoA_le_QE`, `KAbsR_le_L4`). Corollary 5.9 in the dyadic form
(`KR.G1.log_mul_abs_rhoSh_le`, `C_S ≤ 77`) and the telescoping bound
`∑_{ℓ_j > L_*-δ} (ℓ_j + δ)/ℓ_j⁴ ≤ 1.01 δ⁻¹ (L_* - 2δ)⁻²` (`ℓ_j = log(2ʲX₀)`, `δ = log 2`) give
`log y · |ρ^sh f(y)| ≤ 77.8/(δ (L_* - 2δ)²) ≤ e^{-80}`.
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono
  BeurlingSystem

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-- `L_* = Λ² e^{s_H} - 1`. -/
noncomputable def Lstar (X₀ : ℕ) : ℝ := Real.log X₀ ^ 2 * Real.exp sHroot - 1

section

variable (hc : Cond θ X₀)
include hc

/-- **`y(n) > X₀⁻` forces `log n > Λ² e^{s_H}`** (Theorem 6.23(b): `2y(x) < X₀` for
`s(x) ≤ s_H`). -/
lemma absorbY_big {n : ℝ} (h : Xm X₀ < absorbY X₀ n) :
    Real.log X₀ ^ 2 * Real.exp sHroot < Real.log n := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  set x := dyadicScale (X₀ : ℝ) (max (X₀ : ℝ) n) with hxdef
  have hxX : (X₀ : ℝ) ≤ x := le_dyadicScale (by linarith) (le_max_left _ _)
  have hxt : x ≤ max (X₀ : ℝ) n := dyadicScale_le (by linarith) (by positivity)
  have e2 : absorbY X₀ n = absorbYAt X₀ x := rfl
  have hXmh := Xm_half hc
  have hs : sHroot < capS X₀ x := by
    by_contra hle; push_neg at hle
    have := two_absorbYAt_lt_of_le_sH hX0 hX hxX hle
    rw [e2] at h; linarith
  obtain ⟨hLx, -, hℓx⟩ := logs_of_ge hX0 hX hxX
  have hΛ0 : 0 < Real.log X₀ := by linarith
  have h1 : 2 * Real.log (Real.log X₀) + sHroot < Real.log (Real.log x) := by
    unfold capS at hs; linarith
  have h2 : Real.log X₀ ^ 2 * Real.exp sHroot < Real.log x := by
    have := Real.exp_lt_exp.mpr h1
    rw [Real.exp_log (by linarith), Real.exp_add, show 2 * Real.log (Real.log X₀) =
      Real.log (Real.log X₀) * 2 by ring, Real.exp_mul, Real.exp_log hΛ0] at this
    norm_cast at this
  have hxbig : (X₀ : ℝ) < x := by
    by_contra hc'; push_neg at hc'
    have : x = X₀ := le_antisymm hc' hxX
    rw [this] at h2
    have hsH := sHroot_mem
    have : (1 : ℝ) ≤ Real.exp sHroot := Real.one_le_exp (by linarith [hsH.1])
    nlinarith
  have hxn : x ≤ n := by
    rcases le_total (X₀ : ℝ) n with h' | h'
    · rwa [max_eq_right h'] at hxt
    · rw [max_eq_left h'] at hxt; linarith
  exact lt_of_lt_of_le h2 (Real.log_le_log (by linarith) hxn)

/-- `K_𝒜 g(t) = 0` for `log t ≤ Λ² e^{s_H}`. -/
lemma KAbsR_eq_zero_of_small (ω : JitterΩ) (g : ℝ → ℝ) {t : ℝ}
    (ht : Real.log t ≤ Real.log X₀ ^ 2 * Real.exp sHroot) : KAbsR θ X₀ ω g t = 0 := by
  classical
  have hXm0 : 0 < Xm X₀ := by linarith [Queue6.Xm_pos hc]
  unfold KAbsR
  refine Finset.sum_eq_zero fun w hw => ?_
  rw [if_neg]
  rintro ⟨-, -, habs⟩
  have hw' := (KR.Sharp.mem_NAll_iff (PR θ X₀ ω) hXm0).mp (Finset.mem_filter.mp hw).1
  have hcut : Xm X₀ ≤ t / Vl (PR θ X₀ ω) w :=
    (KR.Sharp.le_div_iff_cut (PR θ X₀ ω) hXm0).mp hw'.2
  have := absorbY_big hc (lt_of_le_of_lt hcut habs)
  linarith

/-- `ρ_𝒜(t) = 0` for `log t ≤ L_* = Λ² e^{s_H} - 1`. -/
lemma rhoA_eq_zero_of_small (ω : JitterΩ) {t : ℝ} (ht : Real.log t ≤ Lstar X₀) :
    absorbedDensity (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) t = 0 := by
  have hb : 0 < thetaB θ := thetaB_pos (by linarith [hc.hθ.1])
  have hb1 : thetaB θ ≤ 1 := (thetaB_le_quarter (by linarith [hc.hθ.2])).trans (by norm_num)
  unfold absorbedDensity
  refine (tsum_congr fun a => ?_).trans tsum_zero
  unfold absorbedBump
  split_ifs with ha
  · refine Set.indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    obtain ⟨-, e, hlive, -, hev, k, -, -, hk⟩ := ha
    have hbig := absorbY_big hc (lt_of_le_of_lt (valF_ge_Xm hc k ω) hk)
    have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
    have ha1 : 1 ≤ a := by
      rw [← hev]; exact one_le_evalD hc hlive
    obtain ⟨hu0, hu⟩ := solveU_spec hb (show 0 ≤ a by linarith)
    have hU : uA θ a = solveU (thetaB θ) a := rfl
    rw [hU] at h1
    have hhalf : a / 2 ≤ solveU (thetaB θ) a := by
      rcases le_or_gt 1 (solveU (thetaB θ) a) with hu1 | hu1
      · have : solveU (thetaB θ) a ^ (thetaB θ) ≤ solveU (thetaB θ) a :=
          Real.rpow_le_self_of_one_le hu1 hb1
        linarith
      · exfalso
        have : solveU (thetaB θ) a ^ (thetaB θ) ≤ 1 := Real.rpow_le_one hu0 hu1.le hb.le
        -- then `a ≤ 2`, contradicting `log a > Λ² e^{s_H}`
        have ha2 : a ≤ 2 := by linarith
        have : Real.log a ≤ Real.log 2 := Real.log_le_log (by linarith) ha2
        have := Real.log_two_lt_d9
        have : 1 ≤ Real.log X₀ ^ 2 * Real.exp sHroot := by
          have h1 : (1 : ℝ) ≤ Real.log X₀ ^ 2 := by nlinarith [hc.hX]
          have h2 : (1 : ℝ) ≤ Real.exp sHroot := Real.one_le_exp (by linarith [sHroot_mem.1])
          nlinarith
        linarith
    have hat : a ≤ 2 * t := by linarith
    have : Real.log a ≤ Real.log 2 + Real.log t := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) hat
    have := Real.log_two_lt_d9
    unfold Lstar at ht
    linarith
  · rfl

omit hc in
/-- `R' = 0` below `x₁ ≥ e^{X₀²}`. -/
lemma deriv_osc_low (α γ : ℕ → ℝ) {t : ℝ} (ht0 : 0 < t) (ht : t < switchOn X₀ 0) :
    deriv (Oscillation.osc θ α γ (switchOn X₀)) t = 0 := by
  have hev : Oscillation.osc θ α γ (switchOn X₀) =ᶠ[nhds t] fun _ => 0 := by
    have hmem : Ioo (0 : ℝ) (switchOn X₀ 0) ∈ nhds t := Ioo_mem_nhds ht0 ht
    filter_upwards [hmem] with x hx
    exact Target.osc_eq_zero_of_le (switchOn_spacing _) hx.1 hx.2.le
  rw [hev.deriv_eq]
  exact deriv_const _ _

end

variable (θ X₀) in
/-- The source `f = T' - 1_{[X₀,∞)}(1 - ρ_det)` of the `σ_𝒜` response. -/
noncomputable def fA (ω : JitterΩ) (t : ℝ) : ℝ :=
  (TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) - BaseRange.srcBase X₀ t

section

variable (hc : Cond θ X₀)
include hc

/-- `f = K_𝒜 ρ̃ - ρ̄_𝒜` on `[X₀, x₁)`, `f = 0` below `X₀`. -/
lemma fA_eq (ω : JitterΩ) {t : ℝ} (ht : t < switchOn X₀ 0) :
    fA θ X₀ ω t = if (X₀ : ℝ) ≤ t then KAbsR θ X₀ ω (rhoT θ X₀ ω) t -
      absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) t else 0 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hc.hX
  unfold fA
  split_ifs with hge
  · have hi : KR.Chain.ind X₀ t = 1 := by
      unfold KR.Chain.ind; exact Set.indicator_of_mem (by simpa using hge) _
    have hT : TpCont θ X₀ ω t = 1 - Target.rhoDet X₀ (kappaParam X₀) t -
        absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) t := by
      unfold TpCont
      rw [if_pos hge, deriv_osc_low (X₀ := X₀) _ _ (by linarith) ht]
      ring
    unfold TcR BaseRange.srcBase
    rw [if_pos hge, hT, hi]
    unfold jzX; ring
  · push_neg at hge
    rw [TcR_low hc ω hge.le]
    have hi : KR.Chain.ind X₀ t = 0 := by
      unfold KR.Chain.ind; exact Set.indicator_of_notMem (by simpa using hge) _
    unfold BaseRange.srcBase
    rw [if_neg (not_le.mpr hge), hi]; ring

end

/-! ### Numerics -/

/-- The telescoping majorant `ψ(ℓ) = max(ℓ, M)⁻²`. -/
noncomputable def psiT (M ℓ : ℝ) : ℝ := ((max ℓ M) ^ 2)⁻¹

lemma psiT_anti {M : ℝ} (hM : 0 < M) {a c : ℝ} (hac : a ≤ c) : psiT M c ≤ psiT M a := by
  unfold psiT
  have h1 : 0 < max a M := lt_of_lt_of_le hM (le_max_right _ _)
  have h2 : max a M ≤ max c M := max_le_max hac le_rfl
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)

lemma psiT_le {M : ℝ} (hM : 0 < M) (ℓ : ℝ) : psiT M ℓ ≤ (M ^ 2)⁻¹ := by
  unfold psiT
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hM.le (le_max_right _ _) 2)

/-- **One term of the dyadic sum**: `1[L < ℓ+δ] (ℓ+δ)/ℓ⁴ ≤ (1.01/δ) (ψ(ℓ-δ) - ψ(ℓ))`,
`ψ = max(·, L - 2δ)⁻²`. -/
lemma term_le {L ℓ δ : ℝ} (hδ : 0 < δ) (hδ7 : δ ≤ 0.7) (hL : 1000 ≤ L) (hℓ : 1000 ≤ ℓ) :
    (if L < ℓ + δ then (ℓ + δ) * (ℓ ^ 4)⁻¹ else 0) ≤
      1.01 / δ * (psiT (L - 2 * δ) (ℓ - δ) - psiT (L - 2 * δ) ℓ) := by
  have hM : 0 < L - 2 * δ := by linarith
  split_ifs with h
  · have e1 : max (ℓ - δ) (L - 2 * δ) = ℓ - δ := max_eq_left (by linarith)
    have e2 : max ℓ (L - 2 * δ) = ℓ := max_eq_left (by linarith)
    unfold psiT
    rw [e1, e2]
    have hℓδ : 0 < ℓ - δ := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    -- `(ℓ-δ)⁻² - ℓ⁻² ≥ δ/ℓ³`
    have key : δ / ℓ ^ 3 ≤ ((ℓ - δ) ^ 2)⁻¹ - (ℓ ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ ℓ ^ 2 + ℓ * δ - δ ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hδ.le (by positivity : (0 : ℝ) ≤ ℓ ^ 2)) this]
    have h2 : (ℓ + δ) * (ℓ ^ 4)⁻¹ ≤ 1.01 / δ * (δ / ℓ ^ 3) := by
      rw [show 1.01 / δ * (δ / ℓ ^ 3) = 1.01 / ℓ ^ 3 by field_simp, ← div_eq_mul_inv,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < ℓ ^ 3 := by positivity
      nlinarith
    calc (ℓ + δ) * (ℓ ^ 4)⁻¹ ≤ 1.01 / δ * (δ / ℓ ^ 3) := h2
      _ ≤ 1.01 / δ * (((ℓ - δ) ^ 2)⁻¹ - (ℓ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left key (by positivity)
  · have := psiT_anti hM (show ℓ - δ ≤ ℓ by linarith)
    have : 0 ≤ psiT (L - 2 * δ) (ℓ - δ) - psiT (L - 2 * δ) ℓ := by linarith
    positivity

/-- The telescoping sum. -/
lemma sum_term_le {L δ Λ : ℝ} (hδ : 0 < δ) (hδ7 : δ ≤ 0.7) (hL : 1000 ≤ L) (hΛ : 1000 ≤ Λ)
    (J : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range J) :
    ∑ j ∈ S, (if L < (Λ + j * δ) + δ then ((Λ + j * δ) + δ) * ((Λ + j * δ) ^ 4)⁻¹ else 0) ≤
      1.01 / δ * ((L - 2 * δ) ^ 2)⁻¹ := by
  have hM : 0 < L - 2 * δ := by linarith
  set φ : ℕ → ℝ := fun j => psiT (L - 2 * δ) (Λ + j * δ - δ)
  have hT : ∀ j : ℕ, (if L < (Λ + j * δ) + δ then ((Λ + j * δ) + δ) * ((Λ + j * δ) ^ 4)⁻¹
      else 0) ≤ 1.01 / δ * (φ j - φ (j + 1)) := by
    intro j
    have hj : (1000 : ℝ) ≤ Λ + j * δ := by
      have : (0 : ℝ) ≤ j * δ := by positivity
      linarith
    have h := term_le hδ hδ7 hL hj
    have e : Λ + ((j + 1 : ℕ) : ℝ) * δ - δ = Λ + j * δ := by push_cast; ring
    simp only [φ, e]
    exact h
  have hT0 : ∀ j : ℕ, 0 ≤ 1.01 / δ * (φ j - φ (j + 1)) := by
    intro j
    have := psiT_anti hM (show Λ + j * δ - δ ≤ Λ + ((j + 1 : ℕ) : ℝ) * δ - δ by
      push_cast; nlinarith)
    have : 0 ≤ φ j - φ (j + 1) := by simp only [φ]; linarith
    positivity
  calc _ ≤ ∑ j ∈ S, 1.01 / δ * (φ j - φ (j + 1)) := Finset.sum_le_sum fun j _ => hT j
    _ ≤ ∑ j ∈ Finset.range J, 1.01 / δ * (φ j - φ (j + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun j _ _ => hT0 j
    _ = 1.01 / δ * (φ 0 - φ J) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 1.01 / δ * ((L - 2 * δ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := psiT_le hM (Λ + (0 : ℕ) * δ - δ)
        have h2 : 0 ≤ φ J := by simp only [φ]; unfold psiT; positivity
        simp only [φ] at h1 ⊢
        linarith

/-- `e^{s_H} ≥ 393`. -/
lemma exp_sH_ge : (393 : ℝ) ≤ Real.exp sHroot := by
  have hsH := sHroot_mem
  have h6 : (403.4 : ℝ) ≤ Real.exp 6 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (403.4 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := by gcongr
  have h2 : 1 - 0.0255 ≤ Real.exp (sHroot - 6) := by
    have := Real.add_one_le_exp (sHroot - 6); linarith [hsH.1]
  have : Real.exp sHroot = Real.exp 6 * Real.exp (sHroot - 6) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; nlinarith

/-- `e^{-80} ≥ 10⁻³⁵`. -/
lemma exp_neg80_ge : (1 : ℝ) / 10 ^ 35 ≤ Real.exp (-80) := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 80 = Real.exp 1 ^ 80 := by rw [← Real.exp_nat_mul]; norm_num
  have h80 : Real.exp 80 ≤ 10 ^ 35 := by
    rw [e]
    calc Real.exp 1 ^ 80 ≤ 2.7182818286 ^ 80 := by gcongr
      _ ≤ 10 ^ 35 := by norm_num
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (Real.exp_pos _) h80

/-! ### The response -/

section Resp

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

lemma absorbYAt_pos' {u : ℝ} (hu : (X₀ : ℝ) ≤ u) : 0 < AbsorbEmpty.absorbYAt X₀ u := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hL, -, -⟩ := logs_of_ge hX0 hc.hX hu
  unfold AbsorbEmpty.absorbYAt AbsorbEmpty.absorbL0
  have : 0 < capH (X₀ : ℝ) u := lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  have : 0 < max (Real.log u ^ 5) (48 * capM1 (X₀ : ℝ) u * Real.log u ^ 3 / 0.15 ^ 2) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  positivity

set_option maxHeartbeats 1000000 in
/-- **`ρ̄_𝒜(u) ≤ L_u⁻⁴` on `Good(< t)`** at `X₀ ≤ u ≤ 2(b + H(b))`, `b ≤ t` (Lemma 6.27(a)). -/
lemma rhoCap_le_L4 {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀) {u : ℝ} (huX : (X₀ : ℝ) ≤ u)
    (hu2 : u ≤ 2 * (b + Queue6.Hc X₀ b)) :
    absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u ≤ (Real.log u ^ 4)⁻¹ := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hu0 : 0 < u := by linarith
  have hLu0 : 0 < Real.log u := by linarith [Real.log_le_log hXp huX]
  have hHb : Queue6.Hc X₀ b ≤ b / 4 := by
    unfold Queue6.Hc; rw [max_eq_left hb]
    have := four_capH_le hX0 hX hb; linarith
  set Λ := Real.log X₀ with hΛdef
  by_cases hsmall : Real.log u ≤ Lstar X₀
  · have : absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u = 0 := by
      unfold absorbedDensityCap
      rw [rhoA_eq_zero_of_small hc ω hsmall]
      exact min_eq_left (div_nonneg (by norm_num) hLu0.le)
    rw [this]; positivity
  push_neg at hsmall
  have hLs : (10 : ℝ) ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  set L := Real.log u with hLdef
  have hbu : u ≤ 3 * b := by linarith
  have hlog3 : Real.log 3 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith
  have hlogb : L - 2 < Real.log b := by
    have h3 : L ≤ Real.log 3 + Real.log b := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log hu0 hbu
    linarith
  have hbX : 4 * (X₀ : ℝ) + 2 ≤ b := by
    have h5 : Real.log (6 * (X₀ : ℝ)) ≤ 2 + Λ := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 6 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h := Real.exp_one_gt_d9
        have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]; nlinarith
      linarith
    have hΛb : 2 + Λ < Real.log b := by
      have : Λ ≤ Λ ^ 2 := by nlinarith
      have : Λ ^ 2 ≤ Lstar X₀ + 1 := by
        unfold Lstar
        have h2 := exp_sH_ge
        nlinarith
      nlinarith
    have h6 : 6 * (X₀ : ℝ) < b := (Real.log_lt_log_iff (by positivity) (by linarith)).mp
      (lt_of_le_of_lt h5 hΛb)
    linarith
  have hZb : Zc X₀ b = (b - 2) / 4 := by unfold Zc; rw [if_pos hbX]
  have hZX : (X₀ : ℝ) ≤ Zc X₀ b := by rw [hZb]; linarith
  have hZt : 4 * Zc X₀ b + 2 ≤ t := by rw [hZb]; linarith
  have hbig2 : Λ ^ 2 < Real.log (2 * u) := by
    have : L ≤ Real.log (2 * u) := Real.log_le_log hu0 (by linarith)
    have : Λ ^ 2 ≤ Lstar X₀ := by
      unfold Lstar
      have h2 := exp_sH_ge
      nlinarith
    linarith
  have hY := AbsorbSize.log_three_absorbYAt_le hX0 hX (show (X₀ : ℝ) ≤ 2 * u by linarith) hbig2
  have hY0 := absorbYAt_pos' hc hev (show (X₀ : ℝ) ≤ 2 * u by linarith)
  have hl2u : Real.log (2 * u) ≤ L + 1 := by
    rw [Real.log_mul (by norm_num) hu0.ne']; have := Real.log_two_lt_d9; linarith
  have hL18 : (10 : ℝ) ^ 18 ≤ L := by linarith
  have hsq : Real.sqrt (Real.log (2 * u)) ≤ L / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hlog3y : Real.log (3 * AbsorbEmpty.absorbYAt X₀ (2 * u)) ≤ L - 10 := by linarith
  have h3y : 3 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Real.exp (L - 10) := by
    rw [← Real.exp_log (show 0 < 3 * AbsorbEmpty.absorbYAt X₀ (2 * u) by positivity)]
    exact Real.exp_le_exp.mpr hlog3y
  have hexp : Real.exp (L - 10) ≤ u / 1000 := by
    rw [Real.exp_sub, Real.exp_log hu0, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have : (1000 : ℝ) ≤ Real.exp 10 := by
      have h := Real.exp_one_gt_d9
      have e : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      calc (1000 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
        _ ≤ Real.exp 1 ^ 10 := by gcongr
    nlinarith
  have hu1000 : (1000 : ℝ) ≤ u := by linarith [X₀_ge_two_pow hX]
  have h2y : 2 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Zc X₀ b := by
    rw [hZb]; linarith
  have hut : 20 * u / L ^ 11 + 5 ≤ t := by
    have hL11 : (1000 : ℝ) ≤ L ^ 11 := by
      have : L ≤ L ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
      linarith
    have : 20 * u / L ^ 11 ≤ u / 50 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hρA := rhoA_le_QE hc hev hQC hE1 hN hZX hZt huX h2y hut
  rw [zpow_neg, zpow_ofNat] at hρA
  exact (min_le_left _ _).trans hρA

set_option maxHeartbeats 1000000 in
/-- **The block bound** for the `σ_𝒜` source at `X₀ ≤ u ≤ 2(b + H(b))`, `u < x₁`:
`|f(u)| ≤ L_u⁻⁴`, and `f(u) = 0` if `log u ≤ L_*`. -/
lemma fA_bound {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {u : ℝ} (huX : (X₀ : ℝ) ≤ u) (hu2 : u ≤ 2 * (b + Queue6.Hc X₀ b))
    (hux : u < switchOn X₀ 0) :
    |fA θ X₀ ω u| ≤ (Real.log u ^ 4)⁻¹ ∧ (Real.log u ≤ Lstar X₀ → fA θ X₀ ω u = 0) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hc.hX
  have hu0 : 0 < u := by linarith
  have hLu0 : 0 < Real.log u := by
    linarith [Real.log_le_log (by linarith) huX, hc.hX]
  rw [fA_eq hc ω hux, if_pos huX]
  have hK0 : 0 ≤ KAbsR θ X₀ ω (rhoT θ X₀ ω) u := KAbsR_nonneg ω (rhoT_nonneg ω) u
  have hA0 : 0 ≤ absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u := by
    refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) hLu0.le)
    unfold absorbedBump
    split_ifs
    · by_cases hm : u ∈ Icc (uA θ a) a
      · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos hu0 _).le
      · rw [Set.indicator_of_notMem hm]
    · exact le_rfl
  have hXm0 := Xm_pos' hc
  have huZ : u / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ (Zc_facts hc hb).2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have hKb := KAbsR_le_L4 hc ω hT (rhoT_nonneg ω) (rhoT_le_two hc hev ω) huZ
  rw [zpow_neg, zpow_ofNat] at hKb
  have hAb := rhoCap_le_L4 hc hev hb hbt hQC hE1 hN huX hu2
  refine ⟨?_, fun hsmall => ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · have hK : KAbsR θ X₀ ω (rhoT θ X₀ ω) u = 0 :=
      KAbsR_eq_zero_of_small hc ω _ (by unfold Lstar at hsmall; linarith)
    have hA : absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u = 0 := by
      unfold absorbedDensityCap
      rw [rhoA_eq_zero_of_small hc ω hsmall]
      exact min_eq_left (div_nonneg (by norm_num) hLu0.le)
    rw [hK, hA]; ring

omit hev in
/-- The crude bound of the source on a block `[X₀, Y]`. -/
lemma fA_crude (ω : JitterΩ) {u Y : ℝ} (huX : (X₀ : ℝ) ≤ u) (huY : u ≤ Y) (hev' : Even X₀) :
    |fA θ X₀ ω u| ≤ 6 + ∑ w ∈ KR.NAll (PR θ X₀ ω) Y (Xm X₀), 2 / Vl (PR θ X₀ ω) w := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hc.hX
  have hu0 : 0 < u := by linarith
  have hρ2 : ∀ z, |rhoT θ X₀ ω z| ≤ 2 := fun z => by
    rw [abs_of_nonneg (rhoT_nonneg ω z)]; exact rhoT_le_two hc hev' ω z
  have hK := KAbsR_abs_le hc ω hρ2 huY
  have hT2 := TpCont_abs_le hc ω u
  have hκ0 := (kappa_facts hc.hX).1
  have hsrc : |BaseRange.srcBase X₀ u| ≤ 2 := by
    unfold BaseRange.srcBase
    rw [if_pos huX]
    have h0 := rhoDet_nonneg X₀ hκ0 hu0.le
    have h1 := (BaseRange.rhoDet_le_one_add X₀ hκ0 hu0).trans
      (by linarith [inv_kappa_le hc huX] : 1 + 1 / (kappaParam X₀ * u) ≤ 1 + 1 / 100)
    rw [abs_le]; constructor <;> linarith
  have e : fA θ X₀ ω u = TpCont θ X₀ ω u + KAbsR θ X₀ ω (rhoT θ X₀ ω) u -
      BaseRange.srcBase X₀ u := by
    unfold fA TcR; ring
  rw [e]
  have := abs_le.mp hK
  have := abs_le.mp hT2
  have := abs_le.mp hsrc
  rw [abs_le]; constructor <;> linarith

end Resp

section Resp2

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 2000000 in
/-- **`SigmaAResp` for the realised system** (Proposition 5.35(A), third bullet): on
`QC(< t) ∩ {E1 of time < t} ∩ NiceEv`, with (H_BS) on `[1, Zc b]`, at every start
`X₀ ≤ y ≤ b + H(b)`, `b ≤ t`. -/
theorem sigmaAResp_R {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hbs : (PR θ X₀ ω).HBS (Xm X₀) (Zc X₀ b) (1 / 1000) (1 / 1000) (hbsEps X₀))
    (hX1 : 10 ^ 8 + 1 ≤ Real.log X₀) {y : ℝ} (hy : (X₀ : ℝ) ≤ y)
    (hyb : y ≤ b + Queue6.Hc X₀ b) :
    KR.RML6.SigmaAResp (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) X₀
      (fun t => TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) y := by
  classical
  intro hyA
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  have hXb := X₀_ge_two_pow hX
  have hT := tnpR hc hev hbs hN.2.1 hX1
  have hdec := KR.Chain.dec_R hT
  have hXm0 := Xm_pos' hc
  have hXmX := Xm_le_X0 hc
  have hZ := Zc_facts hc hb
  have hy0 : 0 < y := by linarith
  set Λ := Real.log X₀ with hΛdef
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hLs : (3.9 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Λ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  -- the heights read lie below `x₁`
  have hsw : ∀ u : ℝ, 0 < u → u ≤ 2 * y → u < switchOn X₀ 0 := by
    intro u hu0 hu
    show u < Real.exp ((X₀ : ℝ) ^ 2)
    have h1 : Real.log u ≤ Real.log 2 + Real.log y := by
      rw [← Real.log_mul (by norm_num) hy0.ne']; exact Real.log_le_log hu0 hu
    have h2 : (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ X₀ := by
      calc (X₀ : ℝ) ^ (1 / 100 : ℝ) ≤ (X₀ : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1'.le (by norm_num)
        _ = X₀ := Real.rpow_one _
    have h3 : (X₀ : ℝ) + 1 ≤ (X₀ : ℝ) ^ 2 := by nlinarith
    rw [← Real.exp_log hu0]
    exact Real.exp_lt_exp.mpr (by linarith)
  -- the block bounds
  set bj : ℕ → ℝ := fun j => if (2 : ℝ) ^ j * X₀ ≤ y then
    (if Lstar X₀ < Real.log (2 * (2 ^ j * X₀)) then (Real.log (2 ^ j * X₀) ^ 4)⁻¹ else 0)
    else 6 + ∑ w ∈ KR.NAll (PR θ X₀ ω) (2 * (2 ^ j * X₀)) (Xm X₀), 2 / Vl (PR θ X₀ ω) w
    with hbj
  have hb0 : ∀ j, 0 ≤ bj j := by
    intro j; simp only [hbj]
    split_ifs
    · positivity
    · exact le_rfl
    · have : 0 ≤ ∑ w ∈ KR.NAll (PR θ X₀ ω) (2 * (2 ^ j * X₀)) (Xm X₀),
          2 / Vl (PR θ X₀ ω) w :=
        Finset.sum_nonneg fun w _ => div_nonneg (by norm_num) (KR.Sharp.Vl_pos _ w).le
      linarith
  have hg0 : ∀ u : ℝ, u < X₀ → fA θ X₀ ω u = 0 := by
    intro u hu
    rw [fA_eq hc ω (lt_of_lt_of_le hu (switchOn_zero_ge _)), if_neg (not_le.mpr hu)]
  have hblk : ∀ (j : ℕ) (u : ℝ), 2 ^ j * (X₀ : ℝ) ≤ u → u ≤ 2 * (2 ^ j * X₀) →
      |fA θ X₀ ω u| ≤ bj j := by
    intro j u h1 h2
    have hj1 : (X₀ : ℝ) ≤ 2 ^ j * X₀ := le_mul_of_one_le_left hX0 (one_le_pow₀ (by norm_num))
    have huX : (X₀ : ℝ) ≤ u := hj1.trans h1
    have hu0 : 0 < u := by linarith
    by_cases hjy : (2 : ℝ) ^ j * X₀ ≤ y
    · simp only [hbj, if_pos hjy]
      have hu2y : u ≤ 2 * y := by linarith
      have hHb0 : 0 ≤ Queue6.Hc X₀ b := by unfold Queue6.Hc; exact capH_nonneg _ _
      obtain ⟨hf1, hf2⟩ := fA_bound hc hev hb hbt hQC hE1 hN hT huX (by linarith)
        (hsw u hu0 hu2y)
      split_ifs with hbig
      · have hLj : 0 < Real.log (2 ^ j * X₀) := by
          have := Real.log_le_log hXp hj1; linarith
        have hmono : (Real.log u ^ 4)⁻¹ ≤ (Real.log (2 ^ j * X₀) ^ 4)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hLj.le
            (Real.log_le_log (by positivity) h1) 4)
        linarith
      · push_neg at hbig
        rw [hf2 ((Real.log_le_log hu0 h2).trans hbig), abs_zero]
    · simp only [hbj, if_neg hjy]
      exact fA_crude hc ω huX h2 hev
  -- `J` with `y < 2^J X₀`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, y < 2 ^ J * X₀ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (y / X₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨J, by rw [div_lt_iff₀ hXp] at hJ; linarith⟩
  have hZy : 2 * y / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ hZ.2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have hR := KR.G1.log_mul_abs_rhoSh_le (P := PR θ X₀ ω) (tw := twR θ X₀ ω) hT.hbs hT.hXm
    hdec.1 hdec.2 hXmX (hXmX.trans hy) hZy (g := fA θ X₀ ω) hg0 hb0 hblk hJ
  -- the dyadic sum
  have hsum : ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j ≤ 1.01 / δ * ((Lstar X₀ - 2 * δ) ^ 2)⁻¹ := by
    have hS := sum_term_le (L := Lstar X₀) (δ := δ) (Λ := Λ) (by linarith) hδ7
      (by linarith) (by linarith) J ((Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y))
      (Finset.filter_subset _ _)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_)) hS
    have hjy := (Finset.mem_filter.mp hj).2
    have e1 : Real.log (2 ^ j * (X₀ : ℝ)) = Λ + j * δ := by
      rw [Real.log_mul (by positivity) hXp.ne', Real.log_pow]; ring
    have e2 : Real.log (2 * (2 ^ j * (X₀ : ℝ))) = Λ + j * δ + δ := by
      rw [Real.log_mul (by norm_num) (by positivity), e1]; ring
    simp only [hbj, if_pos hjy, e1, e2]
    split_ifs <;> ring
  -- assembly
  have hCS := BeurlingSystem.CS_le
  have hlogy : 0 ≤ Real.log y := by linarith [Real.log_le_log hXp hy]
  have hfin : 77 * (1.01 / δ * ((Lstar X₀ - 2 * δ) ^ 2)⁻¹) ≤ Real.exp (-80) := by
    refine le_trans ?_ exp_neg80_ge
    have hM : (3.9 : ℝ) * 10 ^ 18 - 2 ≤ Lstar X₀ - 2 * δ := by linarith
    have hM2 : ((3.9 : ℝ) * 10 ^ 18 - 2) ^ 2 ≤ (Lstar X₀ - 2 * δ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hM 2
    have hinv : ((Lstar X₀ - 2 * δ) ^ 2)⁻¹ ≤ (((3.9 : ℝ) * 10 ^ 18 - 2) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hM2
    have h1 : 1.01 / δ ≤ 1.01 / 0.69 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hδ0
    have h2 : 77 * (1.01 / δ * ((Lstar X₀ - 2 * δ) ^ 2)⁻¹) ≤
        77 * (1.01 / 0.69 * (((3.9 : ℝ) * 10 ^ 18 - 2) ^ 2)⁻¹) := by
      gcongr
    refine h2.trans ?_
    norm_num
  have hS0 : 0 ≤ ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
      Real.log (2 * (2 ^ j * X₀)) * bj j := Finset.sum_nonneg fun j _ => by
    have : (1 : ℝ) ≤ 2 * (2 ^ j * (X₀ : ℝ)) := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    exact mul_nonneg (Real.log_nonneg this) (hb0 j)
  have hfA : (fun t => (TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) -
      BaseRange.srcBase X₀ t) = fA θ X₀ ω := rfl
  show |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (fun t =>
    (TcR θ X₀ ω (jzX X₀) t + jzX X₀ * KR.Chain.ind X₀ t) - BaseRange.srcBase X₀ t) *
      Real.log y| ≤ Real.exp (-80)
  rw [hfA, abs_mul, abs_of_nonneg hlogy, mul_comm]
  calc Real.log y * |rhoSh (PR θ X₀ ω) (twR θ X₀ ω) (Xm X₀) y (fA θ X₀ ω)|
      ≤ _ := hR
    _ ≤ 77 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * (X₀ : ℝ) ≤ y),
        Real.log (2 * (2 ^ j * X₀)) * bj j := mul_le_mul_of_nonneg_right hCS hS0
    _ ≤ 77 * (1.01 / δ * ((Lstar X₀ - 2 * δ) ^ 2)⁻¹) := by linarith
    _ ≤ Real.exp (-80) := hfin

end Resp2

end BModel
