module

public import RequestProject.Beurling.Model.Wire3
public import RequestProject.Beurling.Model.SigmaResp
public import RequestProject.Beurling.Model.RhoDetOsc
public import RequestProject.Beurling.Model.OscD2

/-!
# eq. (osc), first display: `∑_u log(2u) o_u ≤ e^{-83}` (the field `hosc`)

The oscillation `o_u` of the clamped `T_c` over the windows of length `2.04 H` meeting `[u, 2u)`
(04f-bridge.tex, paragraph "Oscillation of the target", proof of eq. (osc)) is bounded by the
three parts of `T_c = (ρ_det(X₀) - ρ_det) - ρ̄_𝒜 + R' + K_𝒜 ρ̃` on `[X₀, ∞)` (`T_c = 0` below
`X₀`, and `T_c(X₀) = 0`: continuity at `X₀`, first bullet):

* `o_det ≤ (5 d + 3)/(κ s)` for windows `[s, s + d]` (`rhoDet_kappa_sub_le`; the linear window
  of length `κu` and the unit spacing of the rigid set, second bullet);
* `o_R ≤ d s^{-1/20}` (`deriv_osc_sub_le`, from `|ϕ'| ≤ 2`, `|ϕ''| ≤ 10`; fourth bullet);
* the `𝒜`-part `≤ 2 L⁻⁴`, and `0` unless `log u > L_*` (`rhoCap_le_L4`, `KAbsR_le_L4`,
  `rhoA_eq_zero_of_small`, `KAbsR_eq_zero_of_small`; third bullet, Lemma 6.27(c)).

Summing over the dyadic scales `u = X₀ 2ᵏ/4`: the first two parts give `≤ ∑ u^{-1/10}`, and the
third the telescoping bound `2.02 δ⁻¹ (L_* - 4δ)⁻²` (`δ = log 2`), in all `≤ e^{-83}`
(`hosc_c`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR KR.Chain KR.TcLoc KR.TNP Absorbed
  AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

/-! ### Numerics -/

/-- One term of the `𝒜`-sum: `1[L < ℓ+3δ] (ℓ+2δ)/ℓ⁴ ≤ (1.01/δ) (ψ(ℓ-δ) - ψ(ℓ))`,
`ψ = max(·, L - 4δ)⁻²`. -/
lemma term_le3 {L ℓ δ : ℝ} (hδ : 0 < δ) (hδ7 : δ ≤ 0.7) (hL : 1000 ≤ L) (hℓ : 1000 ≤ ℓ) :
    (if L < ℓ + 3 * δ then (ℓ + 2 * δ) * (ℓ ^ 4)⁻¹ else 0) ≤
      1.01 / δ * (psiT (L - 4 * δ) (ℓ - δ) - psiT (L - 4 * δ) ℓ) := by
  have hM : 0 < L - 4 * δ := by linarith
  split_ifs with h
  · have e1 : max (ℓ - δ) (L - 4 * δ) = ℓ - δ := max_eq_left (by linarith)
    have e2 : max ℓ (L - 4 * δ) = ℓ := max_eq_left (by linarith)
    unfold psiT
    rw [e1, e2]
    have hℓδ : 0 < ℓ - δ := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have key : δ / ℓ ^ 3 ≤ ((ℓ - δ) ^ 2)⁻¹ - (ℓ ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ ℓ ^ 2 + ℓ * δ - δ ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hδ.le (by positivity : (0 : ℝ) ≤ ℓ ^ 2)) this]
    have h2 : (ℓ + 2 * δ) * (ℓ ^ 4)⁻¹ ≤ 1.01 / δ * (δ / ℓ ^ 3) := by
      rw [show 1.01 / δ * (δ / ℓ ^ 3) = 1.01 / ℓ ^ 3 by field_simp, ← div_eq_mul_inv,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < ℓ ^ 3 := by positivity
      nlinarith
    calc (ℓ + 2 * δ) * (ℓ ^ 4)⁻¹ ≤ 1.01 / δ * (δ / ℓ ^ 3) := h2
      _ ≤ 1.01 / δ * (((ℓ - δ) ^ 2)⁻¹ - (ℓ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left key (by positivity)
  · have := psiT_anti hM (show ℓ - δ ≤ ℓ by linarith)
    have : 0 ≤ psiT (L - 4 * δ) (ℓ - δ) - psiT (L - 4 * δ) ℓ := by linarith
    positivity

/-- The telescoping sum of the `𝒜`-terms over `ℓ_j = Λ + jδ`. -/
lemma sum_term_le3 {L δ Λ : ℝ} (hδ : 0 < δ) (hδ7 : δ ≤ 0.7) (hL : 1000 ≤ L) (hΛ : 1000 ≤ Λ)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, (if L < (Λ + j * δ) + 3 * δ then
      ((Λ + j * δ) + 2 * δ) * ((Λ + j * δ) ^ 4)⁻¹ else 0) ≤
      1.01 / δ * ((L - 4 * δ) ^ 2)⁻¹ := by
  have hM : 0 < L - 4 * δ := by linarith
  set φ : ℕ → ℝ := fun j => psiT (L - 4 * δ) (Λ + j * δ - δ)
  have hT : ∀ j : ℕ, (if L < (Λ + j * δ) + 3 * δ then
      ((Λ + j * δ) + 2 * δ) * ((Λ + j * δ) ^ 4)⁻¹ else 0) ≤ 1.01 / δ * (φ j - φ (j + 1)) := by
    intro j
    have hj : (1000 : ℝ) ≤ Λ + j * δ := by
      have : (0 : ℝ) ≤ j * δ := by positivity
      linarith
    have h := term_le3 hδ hδ7 hL hj
    have e : Λ + ((j + 1 : ℕ) : ℝ) * δ - δ = Λ + j * δ := by push_cast; ring
    simp only [φ, e]
    exact h
  calc _ ≤ ∑ j ∈ Finset.range J, 1.01 / δ * (φ j - φ (j + 1)) :=
        Finset.sum_le_sum fun j _ => hT j
    _ = 1.01 / δ * (φ 0 - φ J) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 1.01 / δ * ((L - 4 * δ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := psiT_le hM (Λ + (0 : ℕ) * δ - δ)
        have h2 : 0 ≤ φ J := by simp only [φ]; unfold psiT; positivity
        simp only [φ] at h1 ⊢
        linarith

/-- `2^{-1/10} ≤ 15/16`. -/
lemma two_rpow_neg_tenth_le : (2 : ℝ) ^ (-(1 / 40 : ℝ)) ≤ 58 / 59 := by
  have h : (59 / 58 : ℝ) ≤ (2 : ℝ) ^ (1 / 40 : ℝ) := by
    have h1 : ((59 / 58 : ℝ) ^ (40 : ℕ)) ≤ 2 := by norm_num
    have h2 := Real.rpow_le_rpow (by norm_num) h1 (show (0 : ℝ) ≤ 1 / 40 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), show ((40 : ℕ) : ℝ) * (1 / 40) = 1
      by norm_num, Real.rpow_one] at h2
  rw [Real.rpow_neg (by norm_num)]
  calc ((2 : ℝ) ^ (1 / 40 : ℝ))⁻¹ ≤ (59 / 58 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 58 / 59 := by norm_num

/-- **The geometric sum** `∑_{k<N} (c 2ᵏ)^{-1/40} ≤ 59 c^{-1/40}`. -/
lemma sum_geom_tenth {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ k ∈ Finset.range N, (c * 2 ^ k) ^ (-(1 / 40 : ℝ)) ≤ 59 * c ^ (-(1 / 40 : ℝ)) := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 40 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 := two_rpow_neg_tenth_le
  have e : ∀ k : ℕ, (c * 2 ^ k) ^ (-(1 / 40 : ℝ)) = c ^ (-(1 / 40 : ℝ)) * r ^ k := by
    intro k
    rw [Real.mul_rpow hc.le (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ), mul_comm]
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hc0 : 0 ≤ c ^ (-(1 / 40 : ℝ)) := Real.rpow_nonneg hc.le _
  have hgs : ∑ k ∈ Finset.range N, r ^ k ≤ 59 := by
    have hr1' : r < 1 := by linarith
    have := geom_sum_eq (show r ≠ 1 by linarith) N
    rw [this, div_le_iff_of_neg (by linarith)]
    have : 0 ≤ r ^ N := pow_nonneg hr0 N
    nlinarith
  nlinarith

/-- `e^{-83} ≥ 5 · 10⁻³⁷`. -/
lemma exp_neg83_ge : (5 : ℝ) / 10 ^ 37 ≤ Real.exp (-83) := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 83 = Real.exp 1 ^ 83 := by rw [← Real.exp_nat_mul]; norm_num
  have h83 : Real.exp 83 ≤ 10 ^ 37 / 5 := by
    rw [e]
    calc Real.exp 1 ^ 83 ≤ 2.7182818286 ^ 83 := by gcongr
      _ ≤ 10 ^ 37 / 5 := by norm_num
  rw [Real.exp_neg, show (5 : ℝ) / 10 ^ 37 = (10 ^ 37 / 5)⁻¹ by norm_num]
  exact inv_anti₀ (Real.exp_pos _) h83

/-! ### `T_c` on `[X₀, ∞)` -/

/-- `R'`, the derivative of the designed oscillation of the realised data. -/
noncomputable abbrev Rd (θ : ℝ) (X₀ : ℕ) (ω : JitterΩ) : ℝ → ℝ :=
  deriv (Oscillation.osc θ (alphaD θ X₀ (DF θ X₀ ω)) (gammaD θ X₀ (DF θ X₀ ω)) (switchOn X₀))

section Tc

variable (hc : Cond θ X₀)
include hc

/-- `T_c(v) = T_c(max(v, X₀))`: `T_c = 0` on `(-∞, X₀]` (continuity at `X₀`, first bullet of the
proof of eq. (osc)). -/
lemma TcR_eq_max (ω : JitterΩ) (v : ℝ) :
    TcR θ X₀ ω (jzX X₀) v = TcR θ X₀ ω (jzX X₀) (max v X₀) := by
  rcases le_total v X₀ with h | h
  · rw [max_eq_right h, TcR_low hc ω h, TcR_low hc ω le_rfl]
  · rw [max_eq_left h]

/-- `T_c = (ρ_det(X₀) - ρ_det) - ρ̄_𝒜 + R' + K_𝒜 ρ̃` on `[X₀, ∞)` (§5.1). -/
lemma TcR_split (ω : JitterΩ) {v : ℝ} (hv : (X₀ : ℝ) ≤ v) :
    TcR θ X₀ ω (jzX X₀) v = (Target.rhoDet X₀ (kappaParam X₀) X₀ -
        Target.rhoDet X₀ (kappaParam X₀) v) -
      absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v + Rd θ X₀ ω v +
      KAbsR θ X₀ ω (rhoT θ X₀ ω) v := by
  have hi : KR.Chain.ind X₀ v = 1 := by
    unfold KR.Chain.ind; exact Set.indicator_of_mem (by simpa using hv) _
  unfold TcR TpCont
  rw [if_pos hv, hi]
  unfold jzX; ring

end Tc

section Pair

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- The `𝒜`-parts at `X₀ ≤ v ≤ 2(b + H(b))` on `Good(< t)`: `0 ≤ K_𝒜 ρ̃, ρ̄_𝒜 ≤ L_v⁻⁴`, both
`0` if `log v ≤ L_*` (Lemma 6.27(a), (b)). -/
lemma absParts {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {v : ℝ} (hvX : (X₀ : ℝ) ≤ v) (hv2 : v ≤ 2 * (b + Queue6.Hc X₀ b)) :
    (0 ≤ KAbsR θ X₀ ω (rhoT θ X₀ ω) v ∧ KAbsR θ X₀ ω (rhoT θ X₀ ω) v ≤ (Real.log v ^ 4)⁻¹ ∧
      (Real.log v ≤ Lstar X₀ → KAbsR θ X₀ ω (rhoT θ X₀ ω) v = 0)) ∧
    (0 ≤ absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v ∧
      absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v ≤ (Real.log v ^ 4)⁻¹ ∧
      (Real.log v ≤ Lstar X₀ →
        absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) v = 0)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hc.hX
  have hv0 : 0 < v := by linarith
  have hLv0 : 0 < Real.log v := by
    linarith [Real.log_le_log (by linarith) hvX, hc.hX]
  have hXm0 := Xm_pos' hc
  have hvZ : v / Xm X₀ ≤ Zc X₀ b := by
    refine le_trans ?_ (Zc_facts hc hb).2.2.2
    rw [div_le_div_iff_of_pos_right hXm0]; linarith
  have hKb := KAbsR_le_L4 hc ω hT (rhoT_nonneg ω) (rhoT_le_two hc hev ω) hvZ
  rw [zpow_neg, zpow_ofNat] at hKb
  refine ⟨⟨KAbsR_nonneg ω (rhoT_nonneg ω) v, hKb, fun hs => KAbsR_eq_zero_of_small hc ω _
    (by unfold Lstar at hs; linarith)⟩, ⟨?_, rhoCap_le_L4 hc hev hb hbt hQC hE1 hN hvX hv2,
    fun hs => ?_⟩⟩
  · refine le_min (tsum_nonneg fun a => ?_) (div_nonneg (by norm_num) hLv0.le)
    unfold absorbedBump
    split_ifs
    · by_cases hm : v ∈ Icc (uA θ a) a
      · rw [Set.indicator_of_mem hm]; exact (Real.rpow_pos_of_pos hv0 _).le
      · rw [Set.indicator_of_notMem hm]
    · exact le_rfl
  · unfold absorbedDensityCap
    rw [rhoA_eq_zero_of_small hc ω hs]
    exact min_eq_left (div_nonneg (by norm_num) hLv0.le)

omit hc hev in
/-- `|a - c| ≤ e` for `0 ≤ a, c ≤ e`. -/
lemma abs_sub_le_of_nonneg {a c e : ℝ} (ha : 0 ≤ a) (hae : a ≤ e) (hc0 : 0 ≤ c) (hce : c ≤ e) :
    |a - c| ≤ e := by
  rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **The oscillation of `T_c` over `[s, u] ⊂ [X₀, 2(b + H(b))]`** on `Good(< t)`: the three
parts of the proof of eq. (osc). -/
lemma Tc_pair_le {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {s u : ℝ} (hs : (X₀ : ℝ) ≤ s) (hsu : s ≤ u) (hu2 : u ≤ 2 * (b + Queue6.Hc X₀ b)) :
    |TcR θ X₀ ω (jzX X₀) s - TcR θ X₀ ω (jzX X₀) u| ≤
      (5 * (u - s) + 3) / (kappaParam X₀ * s) + (u - s) * s ^ (-(1 / 20 : ℝ)) +
        2 * (if Lstar X₀ < Real.log u then (Real.log s ^ 4)⁻¹ else 0) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hc.hX
  have hs0 : 0 < s := by linarith
  have hu : (X₀ : ℝ) ≤ u := hs.trans hsu
  rw [TcR_split hc ω hs, TcR_split hc ω hu]
  have hdet := rhoDet_kappa_sub_le hc.hX hs hsu
  have hR := deriv_osc_sub_le hc.hθ hc.hX (gammaD_range (θ := θ) hc.hX (DF θ X₀ ω)) hs hsu
  have hR' : |Rd θ X₀ ω s - Rd θ X₀ ω u| ≤ (u - s) * s ^ (-(1 / 20 : ℝ)) := by
    rw [abs_sub_comm]; exact hR
  obtain ⟨⟨hK0s, hKs, hKs0⟩, ⟨hA0s, hAs, hAs0⟩⟩ :=
    absParts hc hev hb hbt hQC hE1 hN hT hs (hsu.trans hu2)
  obtain ⟨⟨hK0u, hKu, hKu0⟩, ⟨hA0u, hAu, hAu0⟩⟩ := absParts hc hev hb hbt hQC hE1 hN hT hu hu2
  set Ks := KAbsR θ X₀ ω (rhoT θ X₀ ω) s
  set Ku := KAbsR θ X₀ ω (rhoT θ X₀ ω) u
  set As := absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) s
  set Au := absorbedDensityCap (thetaB θ) (absSet X₀ (DF θ X₀ ω)) (uA θ) u
  have hlog : Real.log s ≤ Real.log u := Real.log_le_log hs0 hsu
  have hLs0 : 0 < Real.log s := by linarith [Real.log_le_log (by linarith) hs, hc.hX]
  have hinv : (Real.log u ^ 4)⁻¹ ≤ (Real.log s ^ 4)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hLs0.le hlog 4)
  have hA : |As - Au| + |Ks - Ku| ≤
      2 * (if Lstar X₀ < Real.log u then (Real.log s ^ 4)⁻¹ else 0) := by
    split_ifs with hL
    · have h1 := abs_sub_le_of_nonneg hA0s hAs hA0u (hAu.trans hinv)
      have h2 := abs_sub_le_of_nonneg hK0s hKs hK0u (hKu.trans hinv)
      linarith
    · push_neg at hL
      rw [hAs0 (hlog.trans hL), hAu0 hL, hKs0 (hlog.trans hL), hKu0 hL]; simp
  have e : (Target.rhoDet X₀ (kappaParam X₀) X₀ - Target.rhoDet X₀ (kappaParam X₀) s) - As +
      Rd θ X₀ ω s + Ks - ((Target.rhoDet X₀ (kappaParam X₀) X₀ -
        Target.rhoDet X₀ (kappaParam X₀) u) - Au + Rd θ X₀ ω u + Ku) =
      -(Target.rhoDet X₀ (kappaParam X₀) s - Target.rhoDet X₀ (kappaParam X₀) u) -
        (As - Au) + (Rd θ X₀ ω s - Rd θ X₀ ω u) + (Ks - Ku) := by ring
  rw [e]
  have t1 := abs_add_le (-(Target.rhoDet X₀ (kappaParam X₀) s -
    Target.rhoDet X₀ (kappaParam X₀) u) - (As - Au) + (Rd θ X₀ ω s - Rd θ X₀ ω u)) (Ks - Ku)
  have t2 := abs_add_le (-(Target.rhoDet X₀ (kappaParam X₀) s -
    Target.rhoDet X₀ (kappaParam X₀) u) - (As - Au)) (Rd θ X₀ ω s - Rd θ X₀ ω u)
  have t3 := abs_sub (-(Target.rhoDet X₀ (kappaParam X₀) s -
    Target.rhoDet X₀ (kappaParam X₀) u)) (As - Au)
  rw [abs_neg] at t3
  linarith

end Pair

/-! ### The bound at one scale -/

variable (X₀) in
/-- **The bound of `o_u`** at the scale `u`: `W = 2.04 H(2u)` bounds the window length,
`(10W + 6)/(κu)` the rigid part, `W (u/2)^{-1/20}` the oscillation part, and
`2 · 1[log 4u > L_*] (log(u/2))⁻⁴` the `𝒜`-part. -/
noncomputable def Bsc (u : ℝ) : ℝ :=
  (10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) +
    2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) +
      2 * (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0)

section Scale

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

omit hev in
lemma Bsc_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ Bsc X₀ u := by
  have hκ := (kappa_facts hc.hX).1
  have hH := KR.WidthReal.Hc_pos hc.hX (X₀ := X₀) (2 * u)
  unfold Bsc
  have h3 : 0 ≤ (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0) := by
    split_ifs
    · exact inv_nonneg.mpr (by positivity)
    · exact le_rfl
  have h2 : 0 ≤ (u / 2) ^ (-(1 / 20 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have : 0 ≤ (10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) := by positivity
  positivity

set_option maxHeartbeats 2000000 in
/-- **`o_u ≤ B(u)`** for the clamped `T_c` (clamped at `y/2 + 4.2 H(y)`, correction #109) at a
dyadic scale `X₀/4 ≤ u ≤ y`, start `X₀ ≤ y ≤ b + H(b)`, on `Good(< t)`. -/
theorem oscR_le_Bsc {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {y : ℝ} (hyX : (X₀ : ℝ) ≤ y) (hyb : y ≤ b + Queue6.Hc X₀ b) {u : ℝ} (hu4 : (X₀ : ℝ) ≤ 4 * u)
    (huy : u ≤ y) :
    KR.Chain.oscR (Queue6.Hc X₀) (clampT (oscHt (Queue6.Hc X₀) y) (TcR θ X₀ ω (jzX X₀))) u ≤
      Bsc X₀ u := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hu0 : 0 < u := by linarith
  have hκ := (kappa_facts hX).1
  set H := Queue6.Hc X₀ with hHdef
  set Y := oscHt H y with hYdef
  set Tc := TcR θ X₀ ω (jzX X₀) with hTc
  -- widths
  have hH2u : H (2 * u) ≤ u / 10 := by
    simp only [hHdef]; unfold Queue6.Hc
    have h1 := KR.WidthReal.capH_le_tenth hX (le_max_right (2 * u) (X₀ : ℝ))
    have h2 : max (2 * u) (X₀ : ℝ) ≤ 4 * u := max_le (by linarith) hu4
    linarith
  have hHb : 0 ≤ H b := (KR.WidthReal.Hc_pos hX b).le
  have hHy : H y ≤ y / 40 := by
    simp only [hHdef]; unfold Queue6.Hc; rw [max_eq_left hyX]
    exact KR.WidthReal.capH_le_tenth hX hyX
  have hHy0 : 0 ≤ H y := (KR.WidthReal.Hc_pos hX y).le
  have hY1 : y / 2 ≤ Y := by simp only [hYdef]; unfold oscHt; linarith
  have hY2 : Y ≤ y := by simp only [hYdef]; unfold oscHt; linarith
  unfold KR.Chain.oscR
  refine Real.iSup_le ?_ (Bsc_nonneg hc hu0)
  rintro ⟨⟨p1, p2⟩, h1, h2, h3⟩
  simp only
  unfold clampT
  rw [hTc, TcR_eq_max hc ω (min p1 Y), TcR_eq_max hc ω (min p2 Y), ← hTc]
  have hd : |p1 - p2| ≤ 2.04 * H (2 * u) := by
    have hm : max (H p2) (H u) ≤ H (2 * u) :=
      max_le (KR.WidthReal.Hc_mono hX (by linarith)) (KR.WidthReal.Hc_mono hX (by linarith))
    linarith
  have hd' := abs_le.mp hd
  set a := max (min p1 Y) (X₀ : ℝ) with ha
  set c := max (min p2 Y) (X₀ : ℝ) with hcdef
  have hac : |a - c| ≤ 2.04 * H (2 * u) := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
    exact hd
  -- ranges
  have hlo : ∀ p, u - 0.204 * u ≤ p → u / 2 ≤ max (min p Y) (X₀ : ℝ) := fun p hp =>
    le_trans (le_min (by linarith) (by linarith)) (le_max_left _ _)
  have hhi : ∀ p, p ≤ 2 * u + 0.204 * u → max (min p Y) (X₀ : ℝ) ≤ 4 * u ∧
      max (min p Y) (X₀ : ℝ) ≤ 2 * (b + H b) := fun p hp =>
    ⟨max_le ((min_le_left _ _).trans (by linarith)) hu4,
      max_le ((min_le_right _ _).trans (by linarith)) (by linarith)⟩
  have ha1 : u / 2 ≤ a := hlo p1 (by linarith [hd'.1])
  have hc1 : u / 2 ≤ c := hlo p2 (by linarith)
  have ha2 := hhi p1 (by linarith [hd'.2])
  have hc2 := hhi p2 (by linarith)
  have haX : (X₀ : ℝ) ≤ a := le_max_right _ _
  have hcX : (X₀ : ℝ) ≤ c := le_max_right _ _
  -- the pair bound at `lo ≤ hi`
  have key : ∀ s v : ℝ, (X₀ : ℝ) ≤ s → s ≤ v → u / 2 ≤ s → v ≤ 4 * u →
      v ≤ 2 * (b + H b) → v - s ≤ 2.04 * H (2 * u) → |Tc s - Tc v| ≤ Bsc X₀ u := by
    intro s v hs hsv hs2 hv4 hvb hvs
    have hP := Tc_pair_le hc hev hb hbt hQC hE1 hN hT hs hsv hvb
    refine hP.trans ?_
    unfold Bsc
    have hs0 : 0 < s := by linarith
    have hW0 : 0 ≤ 2.04 * H (2 * u) := by linarith [KR.WidthReal.Hc_pos hX (X₀ := X₀) (2 * u)]
    have t1 : (5 * (v - s) + 3) / (kappaParam X₀ * s) ≤
        (10 * (2.04 * H (2 * u)) + 6) / (kappaParam X₀ * u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hks : kappaParam X₀ * u / 2 ≤ kappaParam X₀ * s := by
        have := mul_le_mul_of_nonneg_left hs2 hκ.le; linarith
      have e1 : (5 * (v - s) + 3) * (kappaParam X₀ * u) ≤
          (5 * (2.04 * H (2 * u)) + 3) * (kappaParam X₀ * u) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e2 := mul_le_mul_of_nonneg_left hks (show 0 ≤ 10 * (2.04 * H (2 * u)) + 6 by linarith)
      nlinarith
    have t2 : (v - s) * s ^ (-(1 / 20 : ℝ)) ≤ 2.04 * H (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) :=
      mul_le_mul hvs (Real.rpow_le_rpow_of_nonpos (by linarith) hs2 (by norm_num))
        (Real.rpow_nonneg hs0.le _) hW0
    have t3 : (if Lstar X₀ < Real.log v then (Real.log s ^ 4)⁻¹ else 0) ≤
        (if Lstar X₀ < Real.log (4 * u) then (Real.log (u / 2) ^ 4)⁻¹ else 0) := by
      split_ifs with h1 h2
      · have hl : 0 < Real.log (u / 2) := Real.log_pos (by
          have := X₀_ge_two_pow hX; linarith)
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hl.le
          (Real.log_le_log (by linarith) hs2) 4)
      · exact absurd (lt_of_lt_of_le h1 (Real.log_le_log (by linarith) hv4)) h2
      · exact inv_nonneg.mpr (by positivity)
      · exact le_rfl
    linarith
  rcases le_total a c with h | h
  · exact key a c haX h ha1 hc2.1 hc2.2 (by linarith [(abs_le.mp hac).1])
  · rw [abs_sub_comm]
    exact key c a hcX h hc1 ha2.1 ha2.2 (by linarith [(abs_le.mp hac).2])

end Scale

/-! ### The sum over the dyadic scales -/

/-- `c^{1/8} ≤ 2 (c^{1/80})^{10}` type bound: `(4u)^{1/8} ≤ 2 u^{1/8}`. -/
lemma four_mul_rpow_eighth_le {u : ℝ} (hu : 0 ≤ u) :
    (4 * u) ^ (1 / 8 : ℝ) ≤ 2 * u ^ (1 / 8 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) hu]
  have h4 : (4 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ (2 * (1 / 8) : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hu _)

set_option maxHeartbeats 1000000 in
/-- **The rigid and oscillation parts at one scale**: `log(2u)(B(u) - 𝒜-part) ≤ u^{-1/40}`
for `u ≥ X₀/4` (second and fourth bullets of the proof of eq. (osc)). -/
lemma nonA_le (hX : 10 ^ 8 ≤ Real.log X₀) {u : ℝ} (hu4 : (X₀ : ℝ) ≤ 4 * u) :
    Real.log (2 * u) * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) +
      2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ))) ≤ u ^ (-(1 / 40 : ℝ)) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hu0 : 0 < u := by linarith
  set v := u ^ (1 / 400 : ℝ) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hu0 _
  have hpow : ∀ n : ℕ, u ^ ((n : ℝ) / 400) = v ^ n := by
    intro n
    rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; ring_nf
  have hv400 : u = v ^ 400 := by rw [← hpow 400]; norm_num
  have hv200 : u ^ (1 / 2 : ℝ) = v ^ 200 := by rw [← hpow 200]; norm_num
  have hv20 : u ^ (1 / 20 : ℝ) = v ^ 20 := by rw [← hpow 20]; norm_num
  have hv10 : u ^ (-(1 / 40 : ℝ)) = (v ^ 10)⁻¹ := by
    rw [Real.rpow_neg hu0.le, ← hpow 10]; norm_num
  -- `v` is huge
  have hlu : Real.log X₀ - 2 ≤ Real.log u := by
    have h1 : Real.log X₀ ≤ Real.log (4 * u) := Real.log_le_log (by linarith) hu4
    rw [Real.log_mul (by norm_num) hu0.ne'] at h1
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith
    linarith
  have hvbig : (20000 : ℝ) ≤ v := by
    rw [hvdef, Real.rpow_def_of_pos hu0]
    have := Real.add_one_le_exp (Real.log u * (1 / 400))
    nlinarith
  -- the width: `H(2u) ≤ (4u)^{1/400} ≤ 2v`
  have hH : Queue6.Hc X₀ (2 * u) ≤ 2 * v := by
    unfold Queue6.Hc
    have h1 := InitialRange.capH_le_rpow400 hX0 hX (le_max_right (2 * u) (X₀ : ℝ))
    have h2 : max (2 * u) (X₀ : ℝ) ≤ 4 * u := max_le (by linarith) hu4
    have h3 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ 1 / 400 by norm_num)
    have h4 : (4 * u) ^ (1 / 400 : ℝ) ≤ 2 * v := by
      rw [Real.mul_rpow (by norm_num) hu0.le, ← hvdef]
      have : (4 : ℝ) ^ (1 / 400 : ℝ) ≤ 4 ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have e : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [e] at this
      exact mul_le_mul_of_nonneg_right this hv0.le
    linarith
  have hH0 : 0 ≤ Queue6.Hc X₀ (2 * u) := (KR.WidthReal.Hc_pos hX (2 * u)).le
  -- `κ u ≥ u^{1/2}/2`
  have hκ := (kappa_facts hX).1
  have hκu : v ^ 200 / 2 ≤ kappaParam X₀ * u := by
    have h1 : (X₀ : ℝ) ^ (-(1 / 2 : ℝ)) ≤ kappaParam X₀ := by
      unfold kappaParam
      exact Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    have h2 : (4 * u) ^ (-(1 / 2 : ℝ)) ≤ (X₀ : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hu4 (by norm_num)
    have h3 : (4 * u) ^ (-(1 / 2 : ℝ)) = (2 * v ^ 200)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.mul_rpow (by norm_num) hu0.le, hv200,
        show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h4 : (2 * v ^ 200)⁻¹ * u ≤ kappaParam X₀ * u :=
      mul_le_mul_of_nonneg_right (h3 ▸ h2.trans h1) hu0.le
    have e : (2 * v ^ 200)⁻¹ * u = v ^ 200 / 2 := by
      rw [hv400]; field_simp
    linarith
  -- `(u/2)^{-1/20} ≤ 2/v^{20}`
  have hq : (u / 2) ^ (-(1 / 20 : ℝ)) ≤ 2 / v ^ 20 := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hu0.le (by norm_num), hv20, inv_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℝ) ^ (1 / 20 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 20 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    nlinarith [pow_pos hv0 20]
  -- `log(2u) ≤ 800 v`
  have hlog : Real.log (2 * u) ≤ 800 * v := by
    have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 2 * u by positivity)
      (show (0 : ℝ) < 1 / 400 by norm_num)
    rw [Real.mul_rpow (by norm_num) hu0.le, ← hvdef] at h1
    have : (2 : ℝ) ^ (1 / 400 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 400 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h2 : 2 ^ (1 / 400 : ℝ) * v / (1 / 400) ≤ 800 * v := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hl0 : 0 ≤ Real.log (2 * u) :=
    Real.log_nonneg (by linarith [KR.WidthReal.X0_ge hX (X₀ := X₀)])
  -- assemble
  have hA : (10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) ≤
      (40.8 * v + 6) * 2 / v ^ 200 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6 ≤ 40.8 * v + 6 := by linarith
    have hp : 0 ≤ 40.8 * v + 6 := by positivity
    nlinarith [mul_le_mul this hκu (by positivity) hp]
  have hB : 2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)) ≤
      2.04 * (2 * v) * (2 / v ^ 20) :=
    mul_le_mul (by linarith) hq (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have hS : (40.8 * v + 6) * 2 / v ^ 200 + 2.04 * (2 * v) * (2 / v ^ 20) ≤ 103 / v ^ 19 := by
    have hp19 := pow_pos hv0 19
    have e1 : (40.8 * v + 6) * 2 / v ^ 200 = (81.6 * v + 12) / v ^ 181 / v ^ 19 := by
      field_simp; ring
    have e2 : 2.04 * (2 * v) * (2 / v ^ 20) = 8.16 / v ^ 19 := by
      field_simp; norm_num
    have h181 : (81.6 * v + 12) / v ^ 181 ≤ 94 := by
      rw [div_le_iff₀ (by positivity)]
      have : v ≤ v ^ 181 := le_self_pow₀ hv1 (by norm_num)
      have : (1 : ℝ) ≤ v ^ 181 := one_le_pow₀ hv1
      nlinarith
    rw [e1, e2, ← add_div, div_le_div_iff_of_pos_right hp19]
    linarith
  rw [hv10]
  calc Real.log (2 * u) * ((10 * (2.04 * Queue6.Hc X₀ (2 * u)) + 6) / (kappaParam X₀ * u) +
        2.04 * Queue6.Hc X₀ (2 * u) * (u / 2) ^ (-(1 / 20 : ℝ)))
      ≤ (800 * v) * (103 / v ^ 19) := by
        apply mul_le_mul hlog (by linarith) (by positivity) (by positivity)
    _ ≤ (v ^ 10)⁻¹ := by
        have hp := pow_pos hv0 18
        have h8 : (82400 : ℝ) ≤ v ^ 8 := by
          have : (20000 : ℝ) ^ 8 ≤ v ^ 8 := pow_le_pow_left₀ (by norm_num) hvbig 8
          nlinarith
        rw [show (800 * v) * (103 / v ^ 19) = 82400 / v ^ 18 by
            first | (field_simp; ring) | field_simp,
          show (v ^ 10)⁻¹ = v ^ 8 / v ^ 18 by first | (field_simp; ring) | field_simp]
        exact div_le_div_of_nonneg_right h8 hp.le

/-- `(X₀/4)^{-1/40} ≤ 10⁻⁴³`. -/
lemma X0_quarter_rpow_le (hX : 10 ^ 8 ≤ Real.log X₀) :
    ((X₀ : ℝ) / 4) ^ (-(1 / 40 : ℝ)) ≤ 1 / 10 ^ 43 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hc0 : (0 : ℝ) < X₀ / 4 := by linarith
  have hl : 4000 ≤ Real.log ((X₀ : ℝ) / 4) := by
    rw [Real.log_div (by linarith) (by norm_num)]
    have : Real.log 4 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith
    linarith
  rw [Real.rpow_def_of_pos hc0]
  have h100 : (10 : ℝ) ^ 43 ≤ Real.exp 100 := by
    have h := Real.exp_one_gt_d9
    have e : Real.exp 100 = Real.exp 1 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (10 : ℝ) ^ 43 ≤ 2.7182818283 ^ 100 := by norm_num
      _ ≤ Real.exp 1 ^ 100 := by gcongr
  have h1 : Real.exp (Real.log ((X₀ : ℝ) / 4) * -(1 / 40)) ≤ Real.exp (-100) :=
    Real.exp_le_exp.mpr (by linarith)
  refine h1.trans ?_
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h100

section Sum

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 4000000 in
/-- **eq. (osc), first display** (04f-bridge.tex, paragraph "Oscillation of the target"): on
`Good(< t)` (with (H_BS) on `[1, Zc b]` through `KR.TNP.Hyp`), at every start `y` of the window
`W_x` of a centre `X₀^{1.01} ≤ x ≤ b`, `∑_u log(2u) o_u ≤ e^{-83}` for the clamped `T_c`
(clamped at `y/2 + 4.2 H(y)`, correction #109). This is the field `hosc` of `RestBridge`. -/
theorem hosc_c {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {x y : ℝ} (hx : (X₀ : ℝ) ^ (1.01 : ℝ) ≤ x) (hxb : x ≤ b) (hW : InW (Queue6.Hc X₀ x) x y) :
    ∑ u ∈ KR.TNP.dyScales X₀ y (NKc X₀ y).1, Real.log (2 * u) *
      KR.Chain.oscR (Queue6.Hc X₀) (KR.TcLoc.clampT (KR.TcLoc.oscHt (Queue6.Hc X₀) y)
        (TcR θ X₀ ω (jzX X₀))) u ≤ Real.exp (-83) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  -- the start `y`
  have hxX : 2 * (X₀ : ℝ) ≤ x := by
    refine le_trans ?_ hx
    rw [show (1.01 : ℝ) = 1 + 0.01 by norm_num, Real.rpow_add hXp, Real.rpow_one]
    have : (2 : ℝ) ≤ (X₀ : ℝ) ^ (0.01 : ℝ) := by
      rw [Real.rpow_def_of_pos hXp]
      have := Real.add_one_le_exp (Real.log X₀ * 0.01)
      nlinarith
    nlinarith
  have hHx : Queue6.Hc X₀ x ≤ x / 40 := by
    unfold Queue6.Hc; rw [max_eq_left (by linarith)]
    exact KR.WidthReal.capH_le_tenth hX (by linarith)
  have hyX : (X₀ : ℝ) ≤ y := by linarith [hW.1]
  have hyb : y ≤ b + Queue6.Hc X₀ b := by
    have := KR.WidthReal.Hc_mono hX hxb
    have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
    linarith [hW.2]
  set N := (NKc X₀ y).1
  set f : ℕ → ℝ := fun k => (X₀ : ℝ) * 2 ^ k / 4 with hf
  set F : ℝ → ℝ := fun u => Real.log (2 * u) * Bsc X₀ u with hF
  have hf4 : ∀ k : ℕ, (X₀ : ℝ) ≤ 4 * f k := by
    intro k; simp only [hf]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hF0 : ∀ k : ℕ, 0 ≤ F (f k) := by
    intro k
    have h4 := hf4 k
    simp only [hF]
    have := KR.WidthReal.X0_ge hX (X₀ := X₀)
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Bsc_nonneg hc (by linarith))
  -- step 1: `o_u ≤ B(u)`
  have h1 : ∑ u ∈ KR.TNP.dyScales X₀ y N, Real.log (2 * u) *
      KR.Chain.oscR (Queue6.Hc X₀) (KR.TcLoc.clampT (KR.TcLoc.oscHt (Queue6.Hc X₀) y)
        (TcR θ X₀ ω (jzX X₀))) u ≤ ∑ u ∈ KR.TNP.dyScales X₀ y N, F u := by
    refine Finset.sum_le_sum fun u hu => ?_
    obtain ⟨k, -, rfl, huy⟩ := KR.TNP.mem_dyScales.mp hu
    have h4 := hf4 k
    simp only [hf] at h4
    exact mul_le_mul_of_nonneg_left
      (oscR_le_Bsc hc hev hb hbt hQC hE1 hN hT hyX hyb h4 huy)
      (Real.log_nonneg (by linarith [KR.WidthReal.X0_ge hX (X₀ := X₀)]))
  -- step 2: the sum over `k < N`
  have h2 : ∑ u ∈ KR.TNP.dyScales X₀ y N, F u ≤ ∑ k ∈ Finset.range N, F (f k) := by
    have hinj : Set.InjOn f (Finset.range N) := by
      intro i _ j _ hij
      simp only [hf] at hij
      have h2 : (2 : ℝ) ^ i = 2 ^ j := by
        have := hij; field_simp at this; linarith
      exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2)
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro u hu _
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
    exact hF0 k
  -- step 3: split and bound
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  set Λ' := Real.log ((X₀ : ℝ) / 8) with hΛ'
  have hΛ'1 : 1000 ≤ Λ' := by
    rw [hΛ', Real.log_div (by linarith) (by norm_num)]
    have : Real.log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hLs : (3.9 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  have hlogs : ∀ k : ℕ, Real.log (f k / 2) = Λ' + k * δ ∧
      Real.log (2 * f k) = (Λ' + k * δ) + 2 * δ ∧ Real.log (4 * f k) = (Λ' + k * δ) + 3 * δ := by
    intro k
    have e1 : f k / 2 = (X₀ : ℝ) / 8 * 2 ^ k := by simp only [hf]; ring
    have e2 : 2 * f k = (X₀ : ℝ) / 8 * 2 ^ k * 2 ^ 2 := by simp only [hf]; ring
    have e3 : 4 * f k = (X₀ : ℝ) / 8 * 2 ^ k * 2 ^ 3 := by simp only [hf]; ring
    have h8 : (0 : ℝ) < X₀ / 8 := by linarith
    have hl : Real.log ((X₀ : ℝ) / 8 * 2 ^ k) = Λ' + k * δ := by
      rw [Real.log_mul h8.ne' (by positivity), Real.log_pow]
    refine ⟨by rw [e1, hl], ?_, ?_⟩
    · rw [e2, Real.log_mul (by positivity) (by positivity), hl, Real.log_pow]; push_cast; ring
    · rw [e3, Real.log_mul (by positivity) (by positivity), hl, Real.log_pow]; push_cast; ring
  have hsplit : ∀ k : ℕ, F (f k) ≤ (((X₀ : ℝ) / 4) * 2 ^ k) ^ (-(1 / 40 : ℝ)) +
      2 * (if Lstar X₀ < (Λ' + k * δ) + 3 * δ then
        ((Λ' + k * δ) + 2 * δ) * ((Λ' + k * δ) ^ 4)⁻¹ else 0) := by
    intro k
    obtain ⟨e1, e2, e3⟩ := hlogs k
    have hn := nonA_le hX (hf4 k)
    have ef : f k = (X₀ : ℝ) / 4 * 2 ^ k := by simp only [hf]; ring
    simp only [hF]
    unfold Bsc
    rw [e3, e1]
    have e : Real.log (2 * f k) * ((10 * (2.04 * Queue6.Hc X₀ (2 * f k)) + 6) /
        (kappaParam X₀ * f k) + 2.04 * Queue6.Hc X₀ (2 * f k) * (f k / 2) ^ (-(1 / 20 : ℝ)) +
        2 * (if Lstar X₀ < Λ' + k * δ + 3 * δ then ((Λ' + k * δ) ^ 4)⁻¹ else 0)) =
        Real.log (2 * f k) * ((10 * (2.04 * Queue6.Hc X₀ (2 * f k)) + 6) /
        (kappaParam X₀ * f k) + 2.04 * Queue6.Hc X₀ (2 * f k) * (f k / 2) ^ (-(1 / 20 : ℝ))) +
        2 * (if Lstar X₀ < Λ' + k * δ + 3 * δ then
          Real.log (2 * f k) * ((Λ' + k * δ) ^ 4)⁻¹ else 0) := by
      split_ifs <;> ring
    rw [e]
    rw [e2] at hn ⊢
    rw [← ef]
    linarith
  have h3 : ∑ k ∈ Finset.range N, F (f k) ≤ 59 * ((X₀ : ℝ) / 4) ^ (-(1 / 40 : ℝ)) +
      2 * (1.01 / δ * ((Lstar X₀ - 4 * δ) ^ 2)⁻¹) := by
    refine (Finset.sum_le_sum fun k _ => hsplit k).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have g1 := sum_geom_tenth (show (0 : ℝ) < X₀ / 4 by linarith) N
    have g2 := sum_term_le3 (L := Lstar X₀) (by linarith) hδ7 (by linarith) hΛ'1 N
    linarith
  -- numerics
  have hq := X0_quarter_rpow_le hX
  have hL4 : (3.8 : ℝ) * 10 ^ 18 ≤ Lstar X₀ - 4 * δ := by linarith
  have hsq : (1.444 : ℝ) * 10 ^ 37 ≤ (Lstar X₀ - 4 * δ) ^ 2 := by nlinarith
  have hA : 2 * (1.01 / δ * ((Lstar X₀ - 4 * δ) ^ 2)⁻¹) ≤ 3 / 10 ^ 37 := by
    rw [← div_eq_mul_inv, div_div, mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have he := exp_neg83_ge
  linarith

set_option maxHeartbeats 4000000 in
/-- **eq. (osc), first display, for centres `x ≥ 2X₀`** (as `hosc_c`; Step 6(b)).
(04f-bridge.tex, paragraph "Oscillation of the target"): on
`Good(< t)` (with (H_BS) on `[1, Zc b]` through `KR.TNP.Hyp`), at every start `y` of the window
`W_x` of a centre `X₀^{1.01} ≤ x ≤ b`, `∑_u log(2u) o_u ≤ e^{-83}` for the clamped `T_c`
(clamped at `y/2 + 4.2 H(y)`, correction #109). This is the field `hosc` of `RestBridge`. -/
theorem hosc_c2 {ω : JitterΩ} {b : ℝ} (hb : (X₀ : ℝ) ≤ b) {t : ℕ} (hbt : b ≤ t)
    (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t) (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hN : ω ∈ NiceEv θ X₀)
    (hT : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) (1 / 1000)
      (1 / 1000) (hbsEps X₀) epsH (epsH / 10))
    {x y : ℝ} (hx : 2 * (X₀ : ℝ) ≤ x) (hxb : x ≤ b) (hW : InW (Queue6.Hc X₀ x) x y) :
    ∑ u ∈ KR.TNP.dyScales X₀ y (NKc X₀ y).1, Real.log (2 * u) *
      KR.Chain.oscR (Queue6.Hc X₀) (KR.TcLoc.clampT (KR.TcLoc.oscHt (Queue6.Hc X₀) y)
        (TcR θ X₀ ω (jzX X₀))) u ≤ Real.exp (-83) := by
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1' := QueueMono.one_lt_of_logX hX0 hX
  have hXp : (0 : ℝ) < X₀ := by linarith
  -- the start `y`
  have hxX : 2 * (X₀ : ℝ) ≤ x := hx
  have hHx : Queue6.Hc X₀ x ≤ x / 40 := by
    unfold Queue6.Hc; rw [max_eq_left (by linarith)]
    exact KR.WidthReal.capH_le_tenth hX (by linarith)
  have hyX : (X₀ : ℝ) ≤ y := by linarith [hW.1]
  have hyb : y ≤ b + Queue6.Hc X₀ b := by
    have := KR.WidthReal.Hc_mono hX hxb
    have := (KR.WidthReal.Hc_pos hX (X₀ := X₀) b).le
    linarith [hW.2]
  set N := (NKc X₀ y).1
  set f : ℕ → ℝ := fun k => (X₀ : ℝ) * 2 ^ k / 4 with hf
  set F : ℝ → ℝ := fun u => Real.log (2 * u) * Bsc X₀ u with hF
  have hf4 : ∀ k : ℕ, (X₀ : ℝ) ≤ 4 * f k := by
    intro k; simp only [hf]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hF0 : ∀ k : ℕ, 0 ≤ F (f k) := by
    intro k
    have h4 := hf4 k
    simp only [hF]
    have := KR.WidthReal.X0_ge hX (X₀ := X₀)
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Bsc_nonneg hc (by linarith))
  -- step 1: `o_u ≤ B(u)`
  have h1 : ∑ u ∈ KR.TNP.dyScales X₀ y N, Real.log (2 * u) *
      KR.Chain.oscR (Queue6.Hc X₀) (KR.TcLoc.clampT (KR.TcLoc.oscHt (Queue6.Hc X₀) y)
        (TcR θ X₀ ω (jzX X₀))) u ≤ ∑ u ∈ KR.TNP.dyScales X₀ y N, F u := by
    refine Finset.sum_le_sum fun u hu => ?_
    obtain ⟨k, -, rfl, huy⟩ := KR.TNP.mem_dyScales.mp hu
    have h4 := hf4 k
    simp only [hf] at h4
    exact mul_le_mul_of_nonneg_left
      (oscR_le_Bsc hc hev hb hbt hQC hE1 hN hT hyX hyb h4 huy)
      (Real.log_nonneg (by linarith [KR.WidthReal.X0_ge hX (X₀ := X₀)]))
  -- step 2: the sum over `k < N`
  have h2 : ∑ u ∈ KR.TNP.dyScales X₀ y N, F u ≤ ∑ k ∈ Finset.range N, F (f k) := by
    have hinj : Set.InjOn f (Finset.range N) := by
      intro i _ j _ hij
      simp only [hf] at hij
      have h2 : (2 : ℝ) ^ i = 2 ^ j := by
        have := hij; field_simp at this; linarith
      exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2)
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro u hu _
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
    exact hF0 k
  -- step 3: split and bound
  set δ := Real.log 2 with hδdef
  have hδ0 : 0.69 ≤ δ := by have := Real.log_two_gt_d9; linarith
  have hδ7 : δ ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  set Λ' := Real.log ((X₀ : ℝ) / 8) with hΛ'
  have hΛ'1 : 1000 ≤ Λ' := by
    rw [hΛ', Real.log_div (by linarith) (by norm_num)]
    have : Real.log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hLs : (3.9 : ℝ) * 10 ^ 18 ≤ Lstar X₀ := by
    unfold Lstar
    have h1 : (10 : ℝ) ^ 16 ≤ Real.log X₀ ^ 2 := by nlinarith
    have h2 := exp_sH_ge
    nlinarith
  have hlogs : ∀ k : ℕ, Real.log (f k / 2) = Λ' + k * δ ∧
      Real.log (2 * f k) = (Λ' + k * δ) + 2 * δ ∧ Real.log (4 * f k) = (Λ' + k * δ) + 3 * δ := by
    intro k
    have e1 : f k / 2 = (X₀ : ℝ) / 8 * 2 ^ k := by simp only [hf]; ring
    have e2 : 2 * f k = (X₀ : ℝ) / 8 * 2 ^ k * 2 ^ 2 := by simp only [hf]; ring
    have e3 : 4 * f k = (X₀ : ℝ) / 8 * 2 ^ k * 2 ^ 3 := by simp only [hf]; ring
    have h8 : (0 : ℝ) < X₀ / 8 := by linarith
    have hl : Real.log ((X₀ : ℝ) / 8 * 2 ^ k) = Λ' + k * δ := by
      rw [Real.log_mul h8.ne' (by positivity), Real.log_pow]
    refine ⟨by rw [e1, hl], ?_, ?_⟩
    · rw [e2, Real.log_mul (by positivity) (by positivity), hl, Real.log_pow]; push_cast; ring
    · rw [e3, Real.log_mul (by positivity) (by positivity), hl, Real.log_pow]; push_cast; ring
  have hsplit : ∀ k : ℕ, F (f k) ≤ (((X₀ : ℝ) / 4) * 2 ^ k) ^ (-(1 / 40 : ℝ)) +
      2 * (if Lstar X₀ < (Λ' + k * δ) + 3 * δ then
        ((Λ' + k * δ) + 2 * δ) * ((Λ' + k * δ) ^ 4)⁻¹ else 0) := by
    intro k
    obtain ⟨e1, e2, e3⟩ := hlogs k
    have hn := nonA_le hX (hf4 k)
    have ef : f k = (X₀ : ℝ) / 4 * 2 ^ k := by simp only [hf]; ring
    simp only [hF]
    unfold Bsc
    rw [e3, e1]
    have e : Real.log (2 * f k) * ((10 * (2.04 * Queue6.Hc X₀ (2 * f k)) + 6) /
        (kappaParam X₀ * f k) + 2.04 * Queue6.Hc X₀ (2 * f k) * (f k / 2) ^ (-(1 / 20 : ℝ)) +
        2 * (if Lstar X₀ < Λ' + k * δ + 3 * δ then ((Λ' + k * δ) ^ 4)⁻¹ else 0)) =
        Real.log (2 * f k) * ((10 * (2.04 * Queue6.Hc X₀ (2 * f k)) + 6) /
        (kappaParam X₀ * f k) + 2.04 * Queue6.Hc X₀ (2 * f k) * (f k / 2) ^ (-(1 / 20 : ℝ))) +
        2 * (if Lstar X₀ < Λ' + k * δ + 3 * δ then
          Real.log (2 * f k) * ((Λ' + k * δ) ^ 4)⁻¹ else 0) := by
      split_ifs <;> ring
    rw [e]
    rw [e2] at hn ⊢
    rw [← ef]
    linarith
  have h3 : ∑ k ∈ Finset.range N, F (f k) ≤ 59 * ((X₀ : ℝ) / 4) ^ (-(1 / 40 : ℝ)) +
      2 * (1.01 / δ * ((Lstar X₀ - 4 * δ) ^ 2)⁻¹) := by
    refine (Finset.sum_le_sum fun k _ => hsplit k).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have g1 := sum_geom_tenth (show (0 : ℝ) < X₀ / 4 by linarith) N
    have g2 := sum_term_le3 (L := Lstar X₀) (by linarith) hδ7 (by linarith) hΛ'1 N
    linarith
  -- numerics
  have hq := X0_quarter_rpow_le hX
  have hL4 : (3.8 : ℝ) * 10 ^ 18 ≤ Lstar X₀ - 4 * δ := by linarith
  have hsq : (1.444 : ℝ) * 10 ^ 37 ≤ (Lstar X₀ - 4 * δ) ^ 2 := by nlinarith
  have hA : 2 * (1.01 / δ * ((Lstar X₀ - 4 * δ) ^ 2)⁻¹) ≤ 3 / 10 ^ 37 := by
    rw [← div_eq_mul_inv, div_div, mul_div_assoc', div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have he := exp_neg83_ge
  linarith

end Sum

end BModel

end
