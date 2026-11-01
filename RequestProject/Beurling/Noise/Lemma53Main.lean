module

public import RequestProject.Beurling.Noise.Lemma53Hild
public import RequestProject.Beurling.Noise.Lemma53PP
public import RequestProject.Beurling.Noise.Lemma53F

/-!
# Lemma 5.3 (smooth elements, with Dickman quality)

`BeurlingSystem.HBS.lemma53`: under (HBS) on `[1, Z]`, for `L_z = log z ≥ 100`, `ℓ = u L_z`,
`1 ≤ u ≤ L_z` and `2e^ℓ ≤ Z`,

  `v(ℓ, z) = ∑_{n ∈ 𝒩 ∩ (e^ℓ, 2e^ℓ], P⁺(n) ≤ z} 1/n ≤ C₀ ρ(u) e^{a_V}`,
  `a_V = 4K u² log(u+2)/ℓ`, `K = 3.2`, `C₀ = 0.70`.

The proof is the paper's: by induction on `ℓ'` (in steps of `log 2`) we prove
`v(ℓ', z) ≤ G_V(ℓ') = C₀ ρ(ℓ'/L) e^{φ(ℓ'/L)}` for `log 72 ≤ ℓ' ≤ L²`. The base `ℓ' ≤ L` is the
small-height bound; the step `L < ℓ ≤ L²` uses Hildebrand's identity `ℓ v(ℓ) ≤ ∑ (log p/p^k)
v(ℓ - k log p)`, the main terms `p^k ≤ z` by Abel summation (`BSaias.main_terms_le`) with the
small-height excess `X(u)`, the prime powers `p^k > z` (`HBS.pp_sum_le`), the one-step bound
(`BSaias.integral_rho_exp_le`) and the inequality (28) (`BSaias.lemV_onestep`, from the
certificates).
-/

@[expose] public section

open Finset Real Dickman BSaias

namespace BeurlingSystem

variable {P : BeurlingSystem}

/-- For `z < 1` and `Y ≥ 1` there is no `z`-smooth element in `(Y, 2Y]`. -/
lemma vSmooth_eq_zero_of_lt_one {Y z : ℝ} (hz : z < 1) (hY : 1 ≤ Y) : P.vSmooth Y z = 0 := by
  unfold vSmooth
  apply Finset.sum_eq_zero
  intro e he
  simp only [mem_filter] at he
  obtain ⟨-, hYe, hsupp⟩ := he
  have he0 : e = 0 := by
    ext j
    by_contra hj
    have := hsupp j (Finsupp.mem_support_iff.mpr hj)
    linarith [P.one_lt j]
  rw [he0] at hYe
  simp [val] at hYe
  linarith

namespace HBS

variable {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma log72_lt_428 : Real.log 72 < 4.28 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : Real.exp 4.28 = Real.exp 1 ^ 4 * Real.exp 0.28 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.28 by norm_num)
  have h4 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h2.le 4
  rw [h1]
  calc (72 : ℝ) < 2.7182818283 ^ 4 * (1 + 0.28 + 0.28 ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 1 ^ 4 * Real.exp 0.28 := by
      apply mul_le_mul h4 h3 (by norm_num) (by positivity)

lemma GV_ge_C0 {L s : ℝ} (hL : 0 < L) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : C0 ≤ GV L s := by
  unfold GV
  rw [rho_of_le_one hs1, mul_one]
  have := Real.one_le_exp (phiV_nonneg hL hs0)
  have := C0_pos
  nlinarith

/-- The base of the induction: `ℓ' ≤ L`. -/
lemma claim_base (h : P.HBS X0m Z η1 η2 ε1) {z ℓ : ℝ} (hL : 100 ≤ Real.log z)
    (h72 : Real.log 72 ≤ ℓ) (hℓ : ℓ ≤ Real.log z) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.vSmooth (Real.exp ℓ) z ≤ GV (Real.log z) (ℓ / Real.log z) := by
  have hL0 : 0 < Real.log z := by linarith
  have hY : 72 ≤ Real.exp ℓ := by
    rw [← Real.exp_log (show (0:ℝ) < 72 by norm_num)]; exact Real.exp_le_exp.mpr h72
  have h1 := (P.vSmooth_le_harmBlock _ z).trans (h.harmBlock_le_C0 hY hZ)
  have hl72 : 0 < Real.log 72 := Real.log_pos (by norm_num)
  refine h1.trans (GV_ge_C0 hL0 (div_nonneg (by linarith) hL0.le) ?_)
  rw [div_le_one hL0]; exact hℓ

/-- The ratio bound used for `β = 1 - r(u)/L ≥ 0.915`. -/
lemma ratio_le_of_le {L u : ℝ} (hL : 100 ≤ L) (hu1 : 1 ≤ u) (huL : u ≤ L) :
    ratio u ≤ 0.085 * L := by
  have h1 : ratio u ≤ ratio L := ratio_monotoneOn (Set.mem_Ici.mpr hu1)
    (Set.mem_Ici.mpr (by linarith)) huL
  have h2 : ratio L ≤ Real.log ((L + 1) / 0.1) / (1 - 0.1) :=
    ratio_upper (by linarith) (by norm_num) (by norm_num)
  have h6 : (403 : ℝ) ≤ Real.exp 6 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (403 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this.le 6
  have h3 : Real.log ((L + 1) / 0.1) ≤ 5 + (L + 1) / 0.1 / 403 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (L + 1) / 0.1 / Real.exp 6 by positivity)
    rw [Real.log_div (by positivity) (Real.exp_pos 6).ne', Real.log_exp] at this
    have : (L + 1) / 0.1 / Real.exp 6 ≤ (L + 1) / 0.1 / 403 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) h6
    linarith
  have : Real.log ((L + 1) / 0.1) / (1 - 0.1) ≤ 0.085 * L := by
    rw [div_le_iff₀ (by norm_num)]
    have e : (L + 1) / 0.1 / 403 = (10 / 403) * L + 10 / 403 := by ring
    rw [e] at h3
    rw [show (0.085 : ℝ) * L * (1 - 0.1) = 0.0765 * L by ring]
    linarith
  linarith

set_option maxHeartbeats 4000000 in
/-- **The induction step** of Lemma 5.3: `L < ℓ ≤ L²`. -/
theorem claim_step (h : P.HBS X0m Z η1 η2 ε1) {z ℓ : ℝ} (hz : 0 < z) (hL : 100 ≤ Real.log z)
    (hℓ1 : Real.log z < ℓ) (hℓ2 : ℓ ≤ Real.log z ^ 2) (hZ : 2 * Real.exp ℓ ≤ Z)
    (IH : ∀ ℓ', ℓ' ≤ ℓ - Real.log 2 → Real.log 72 ≤ ℓ' → ℓ' ≤ Real.log z ^ 2 →
      2 * Real.exp ℓ' ≤ Z → P.vSmooth (Real.exp ℓ') z ≤ GV (Real.log z) (ℓ' / Real.log z)) :
    P.vSmooth (Real.exp ℓ) z ≤ GV (Real.log z) (ℓ / Real.log z) := by
  set L := Real.log z with hLdef
  have hL0 : 0 < L := by linarith
  set Y := Real.exp ℓ with hYdef
  have hYpos : 0 < Y := Real.exp_pos ℓ
  set u := ℓ / L with hudef
  have hu1 : 1 < u := by rw [hudef, lt_div_iff₀ hL0]; linarith
  have huL : u ≤ L := by rw [hudef, div_le_iff₀ hL0]; nlinarith
  have hℓu : ℓ = u * L := by rw [hudef]; field_simp
  have hzexp : z = Real.exp L := (Real.exp_log hz).symm
  have hzY : z ≤ Y := by rw [hzexp]; exact Real.exp_le_exp.mpr hℓ1.le
  have hzZ : z ≤ Z := by linarith
  have hz1 : 1 ≤ z := by rw [hzexp]; exact Real.one_le_exp hL0.le
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl72 := log72_lt_428
  have hl72' : 0 < Real.log 72 := Real.log_pos (by norm_num)
  -- notation
  set w : ℕ × ℕ → ℝ := fun jk => Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) with hw
  set σ : ℕ × ℕ → ℝ := fun jk => (jk.2 + 1) * Real.log (P.p jk.1) with hσ
  set vv : ℝ → ℝ := fun ℓ' => P.vSmooth (Real.exp ℓ') z with hvv
  set T := (P.pps (2 * Y)).filter (fun jk => P.p jk.1 ≤ z)
  have hw0 : ∀ jk, 0 ≤ w jk := fun jk => div_nonneg (P.log_p_nonneg _) (P.pp_pos jk).le
  have hσexp : ∀ jk, Real.exp (σ jk) = P.p jk.1 ^ (jk.2 + 1) := by
    intro jk
    simp only [σ]
    rw [show ((jk.2 : ℝ) + 1) = ((jk.2 + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow,
      Real.exp_log (P.pp_pos jk)]
  have hYp : ∀ jk, Y / P.p jk.1 ^ (jk.2 + 1) = Real.exp (ℓ - σ jk) := by
    intro jk; rw [Real.exp_sub, hσexp]
  have hTp2 : ∀ jk ∈ T, 2 ≤ P.p jk.1 := fun jk hjk =>
    h.p_ge_two ((mem_filter.mp hjk).2.trans hzZ)
  have hσ2 : ∀ jk ∈ T, Real.log 2 ≤ σ jk := by
    intro jk hjk
    have := Real.log_le_log (by norm_num) (hTp2 jk hjk)
    have : 0 ≤ Real.log (P.p jk.1) := P.log_p_nonneg _
    simp only [σ]
    have : (0 : ℝ) ≤ jk.2 := Nat.cast_nonneg _
    nlinarith
  -- (1) `ℓ v(ℓ) ≤ ∑_n log n / n`, and Hildebrand's identity
  have h1 : ℓ * vv ℓ ≤ ∑ jk ∈ T, w jk * vv (ℓ - σ jk) := by
    have hH := P.hildebrand Y z
    have hle : ℓ * vv ℓ ≤ ∑ e ∈ (P.elems (2 * Y)).filter
        (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z), Real.log (P.val e) / P.val e := by
      simp only [vv, vSmooth]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      have hYe := (mem_filter.mp he).2.1
      have hv := P.val_pos e
      have : ℓ < Real.log (P.val e) := by
        rw [Real.lt_log_iff_exp_lt hv]; exact hYe
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right this.le hv.le
    rw [hH] at hle
    refine hle.trans (le_of_eq (Finset.sum_congr rfl fun jk _ => ?_))
    simp only [w, vv]
    rw [hYp]
  -- split at `p^k ≤ z`
  set T1 := T.filter (fun jk => P.p jk.1 ^ (jk.2 + 1) ≤ z)
  set T2 := T.filter (fun jk => ¬ P.p jk.1 ^ (jk.2 + 1) ≤ z)
  have hsplit : ∑ jk ∈ T, w jk * vv (ℓ - σ jk) =
      ∑ jk ∈ T1, w jk * vv (ℓ - σ jk) + ∑ jk ∈ T2, w jk * vv (ℓ - σ jk) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- `σ ≤ L` on `T1`
  have hT1σ : ∀ jk ∈ T1, 0 ≤ σ jk ∧ σ jk ≤ L := by
    intro jk hjk
    have hjT := (mem_filter.mp hjk).1
    refine ⟨by linarith [hσ2 jk hjT, Real.log_pos (show (1:ℝ) < 2 by norm_num)], ?_⟩
    have := (mem_filter.mp hjk).2
    rw [← hσexp] at this
    rw [hLdef, ← Real.log_exp (σ jk)]
    exact Real.log_le_log (Real.exp_pos _) this
  -- the partial sums of `T1` are `S(e^x)`
  have hmert : ∀ x, 0 ≤ x → x ≤ L →
      ∑ jk ∈ T1.filter (fun jk => σ jk ≤ x), w jk = P.mertensS (Real.exp x) := by
    intro x hx0 hxL
    have hex : Real.exp x ≤ z := by rw [hzexp]; exact Real.exp_le_exp.mpr hxL
    unfold mertensS
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext jk
    simp only [T1, T, mem_filter, mem_pps]
    constructor
    · rintro ⟨⟨⟨-, -⟩, -⟩, h'⟩
      rw [← hσexp]; exact Real.exp_le_exp.mpr h'
    · intro h'
      have hp1 : P.p jk.1 ≤ P.p jk.1 ^ (jk.2 + 1) := by
        calc P.p jk.1 = P.p jk.1 ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ (P.one_lt _).le (by omega)
      refine ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, ?_⟩
      rw [← hσexp] at h'
      exact Real.exp_le_exp.mp h'
  have hE : ∀ x ∈ Set.Icc 0 L, |∑ jk ∈ T1.filter (fun jk => σ jk ≤ x), w jk - x| ≤ 1.01 := by
    intro x hx
    rw [hmert x hx.1 hx.2]
    have hex : Real.exp x ≤ z := by rw [hzexp]; exact Real.exp_le_exp.mpr hx.2
    have := (P.lemma_5_1 h (Real.one_le_exp hx.1) (hex.trans hzZ)).2.1
    rw [Real.log_exp] at this
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  -- (2) the main terms
  have hmain1 : ∑ jk ∈ T1, w jk * vv (ℓ - σ jk) ≤
      ∑ jk ∈ T1, w jk * GV L ((ℓ - σ jk) / L) +
        2 / 15 * ∑ jk ∈ T1.filter (fun jk => ¬ σ jk ≤ ℓ - Real.log 72), w jk := by
    rw [Finset.mul_sum, Finset.sum_filter (s := T1), ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro jk hjk
    have hσj := hT1σ jk hjk
    have hjT := (mem_filter.mp hjk).1
    by_cases hc : σ jk ≤ ℓ - Real.log 72
    · rw [if_neg (not_not.mpr hc), add_zero]
      have hl' : Real.log 72 ≤ ℓ - σ jk := by linarith
      have hZ' : 2 * Real.exp (ℓ - σ jk) ≤ Z := by
        have := Real.exp_le_exp.mpr (show ℓ - σ jk ≤ ℓ by linarith); linarith
      have hv := IH (ℓ - σ jk) (by linarith [hσ2 jk hjT]) hl' (by linarith) hZ'
      exact mul_le_mul_of_nonneg_left hv (hw0 jk)
    · rw [if_pos hc]
      push_neg at hc
      have hl' : ℓ - σ jk < Real.log 72 := by linarith
      have hpos : 0 < ℓ - σ jk := by linarith
      have hY1 : 1 ≤ Real.exp (ℓ - σ jk) := Real.one_le_exp hpos.le
      have hY72 : Real.exp (ℓ - σ jk) < 72 := by
        rw [← Real.exp_log (show (0:ℝ) < 72 by norm_num)]; exact Real.exp_lt_exp.mpr hl'
      have hZ' : 2 * Real.exp (ℓ - σ jk) ≤ Z := by
        have := Real.exp_le_exp.mpr (show ℓ - σ jk ≤ ℓ by linarith); linarith
      have hv : vv (ℓ - σ jk) ≤ 5 / 6 :=
        (P.vSmooth_le_harmBlock _ z).trans (h.harmBlock_le_five_sixths hY1 hY72 hZ')
      have hG : C0 ≤ GV L ((ℓ - σ jk) / L) :=
        GV_ge_C0 hL0 (div_nonneg hpos.le hL0.le) (by rw [div_le_one hL0]; linarith)
      have : C0 = 0.70 := rfl
      have := hw0 jk
      nlinarith
  have hmain2 := main_terms_le T1 w σ (le_of_eq_of_le rfl hL) hℓ1 hℓ2 hT1σ hE
  rw [← hudef] at hmain2
  -- (3) the excess
  have hexcess : 2 / 15 * ∑ jk ∈ T1.filter (fun jk => ¬ σ jk ≤ ℓ - Real.log 72), w jk ≤
      C0 * Real.exp (phiV L u) * u * rho u * XL L u := by
    by_cases hX : u < 1 + Real.log 72 / L
    · have hx0 : 0 ≤ ℓ - Real.log 72 := by linarith
      have hxL : ℓ - Real.log 72 ≤ L := by
        have : u - 1 < Real.log 72 / L := by linarith
        rw [lt_div_iff₀ hL0] at this; rw [hℓu]; nlinarith
      have hs := Finset.sum_filter_add_sum_filter_not T1 (fun jk => σ jk ≤ ℓ - Real.log 72) w
      have hT1L : ∑ jk ∈ T1, w jk = P.mertensS (Real.exp L) := by
        rw [← hmert L hL0.le le_rfl, Finset.filter_true_of_mem (fun jk hj => (hT1σ jk hj).2)]
      rw [hmert _ hx0 hxL, hT1L] at hs
      have hm1 := (P.lemma_5_1 h (Real.one_le_exp hL0.le) (by rw [← hzexp]; exact hzZ)).2.1
      have hm2 := (P.lemma_5_1 h (Real.one_le_exp hx0)
        ((Real.exp_le_exp.mpr hxL).trans (by rw [← hzexp]; exact hzZ))).2.1
      rw [Real.log_exp] at hm1 hm2
      have hsum : ∑ jk ∈ T1.filter (fun jk => ¬ σ jk ≤ ℓ - Real.log 72), w jk ≤
          Real.log 72 + 1.44 := by linarith [hm1.2, hm2.1]
      have hu2 : u < 2 := by
        have : Real.log 72 / L < 1 := by rw [div_lt_one hL0]; linarith
        linarith
      have hρu : rho u = 1 - Real.log u := rho_one_two hu1.le hu2.le
      have hlogu : Real.log u < 1 := by
        have := Real.log_lt_sub_one_of_pos (by linarith : 0 < u) (by linarith); linarith
      have hXv : XL L u = 0.7627 / (0.70 * (1 - Real.log u) * u) := by unfold XL; rw [if_pos hX]
      have hφ := Real.one_le_exp (phiV_nonneg hL0 (by linarith : 0 ≤ u))
      have hN : 0.70 * (1 - Real.log u) * u ≤ C0 * Real.exp (phiV L u) * u * rho u := by
        rw [hρu]; unfold C0
        have : 0 < (1 - Real.log u) * u := by
          apply mul_pos <;> linarith
        nlinarith
      have hpos : 0 < 0.70 * (1 - Real.log u) * u := by
        apply mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
      rw [hXv]
      calc 2 / 15 * ∑ jk ∈ T1.filter (fun jk => ¬ σ jk ≤ ℓ - Real.log 72), w jk
          ≤ 0.7627 := by nlinarith
        _ = 0.70 * (1 - Real.log u) * u * (0.7627 / (0.70 * (1 - Real.log u) * u)) := by
            have h1 : 1 - Real.log u ≠ 0 := by linarith
            have h2 : u ≠ 0 := by linarith
            field_simp
        _ ≤ C0 * Real.exp (phiV L u) * u * rho u *
              (0.7627 / (0.70 * (1 - Real.log u) * u)) :=
            mul_le_mul_of_nonneg_right hN (by positivity)
    · have hXv : XL L u = 0 := by unfold XL; rw [if_neg hX]
      rw [hXv, mul_zero]
      have : T1.filter (fun jk => ¬ σ jk ≤ ℓ - Real.log 72) = ∅ := by
        apply Finset.filter_false_of_mem
        intro jk hjk
        push_neg at hX ⊢
        have := (hT1σ jk hjk).2
        have : Real.log 72 ≤ (u - 1) * L := by
          have h' : Real.log 72 / L ≤ u - 1 := by linarith
          rwa [div_le_iff₀ hL0] at h'
        nlinarith
      rw [this]; simp
  -- (4) the prime powers `p^k > z`
  have hβ : 0.915 ≤ 1 - ratio u / L := by
    have := ratio_le_of_le hL hu1.le huL
    rw [show (0.915 : ℝ) = 1 - 0.085 by norm_num]
    have : ratio u / L ≤ 0.085 := by rw [div_le_iff₀ hL0]; linarith
    linarith
  have hpp1 : ∀ jk ∈ T2, w jk * vv (ℓ - σ jk) ≤ 1.001 * rho u * Real.exp (phiV L u) *
      (Real.log (P.p jk.1) * Real.exp (-(1 - ratio u / L) * σ jk)) := by
    intro jk hjk
    have hjT := (mem_filter.mp hjk).1
    have hσj := hσ2 jk hjT
    have hσ0 : 0 < σ jk := lt_of_lt_of_le (Real.log_pos (by norm_num)) hσj
    set s := (ℓ - σ jk) / L
    have hus : u - s = σ jk / L := by simp only [s, hudef]; field_simp; ring
    have hsu : s ≤ u := by have := div_pos hσ0 hL0; linarith
    have hρs : ∀ t, t ≤ u → rho t ≤ rho u * Real.exp ((u - t) * ratio u) :=
      fun t ht => rho_le_mul_exp hu1.le ht
    have hφu := Real.one_le_exp (phiV_nonneg hL0 (by linarith : 0 ≤ u))
    have hZ' : 2 * Real.exp (ℓ - σ jk) ≤ Z := by
      have := Real.exp_le_exp.mpr (show ℓ - σ jk ≤ ℓ by linarith); linarith
    have hv : vv (ℓ - σ jk) ≤ 1.001 * rho u * Real.exp (phiV L u) *
        Real.exp ((u - s) * ratio u) := by
      have hB : 0 ≤ rho u * Real.exp ((u - s) * ratio u) := by
        have := rho_pos u; positivity
      by_cases h72 : Real.log 72 ≤ ℓ - σ jk
      · have hv := IH (ℓ - σ jk) (by linarith) h72 (by linarith) hZ'
        have hs0 : 0 ≤ s := div_nonneg (by linarith) hL0.le
        have hφs : Real.exp (phiV L s) ≤ Real.exp (phiV L u) :=
          Real.exp_le_exp.mpr (phiV_mono hL0 hs0 hsu)
        refine hv.trans ?_
        unfold GV
        have hρ := hρs s hsu
        have := C0_pos
        have := rho_pos s
        unfold C0 at *
        calc 0.70 * rho s * Real.exp (phiV L s)
            ≤ 0.70 * (rho u * Real.exp ((u - s) * ratio u)) * Real.exp (phiV L u) := by gcongr
          _ ≤ _ := by nlinarith [Real.exp_pos (phiV L u)]
      · push_neg at h72
        have hv1 : vv (ℓ - σ jk) ≤ 1 :=
          (P.vSmooth_le_harmBlock _ z).trans (h.harmBlock_le_one hZ')
        have hs1 : s ≤ 1 := by
          simp only [s]; rw [div_le_one hL0]; linarith
        have hρ := hρs s hsu
        rw [rho_of_le_one hs1] at hρ
        refine hv1.trans ?_
        nlinarith [Real.exp_pos (phiV L u)]
    have hwv : w jk = Real.log (P.p jk.1) * Real.exp (-σ jk) := by
      simp only [w]; rw [Real.exp_neg, hσexp]; ring
    rw [hwv, hus] at *
    have hw' : 0 ≤ Real.log (P.p jk.1) * Real.exp (-σ jk) := by
      have := P.log_p_nonneg jk.1; positivity
    calc Real.log (P.p jk.1) * Real.exp (-σ jk) * vv (ℓ - σ jk)
        ≤ Real.log (P.p jk.1) * Real.exp (-σ jk) *
            (1.001 * rho u * Real.exp (phiV L u) * Real.exp (σ jk / L * ratio u)) :=
          mul_le_mul_of_nonneg_left hv hw'
      _ = 1.001 * rho u * Real.exp (phiV L u) *
            (Real.log (P.p jk.1) * (Real.exp (-σ jk) * Real.exp (σ jk / L * ratio u))) := by ring
      _ = _ := by
          rw [← Real.exp_add]; congr 3; field_simp; ring
  have hpp2 := h.pp_sum_le hz1 hL hzZ hβ T2 (fun jk hjk => by
    have hjT := (mem_filter.mp hjk).1
    exact ⟨(mem_filter.mp hjT).2, lt_of_not_ge (mem_filter.mp hjk).2⟩)
  have hpp : ∑ jk ∈ T2, w jk * vv (ℓ - σ jk) ≤
      22 * Real.exp (-0.4 * L) * (C0 * Real.exp (phiV L u) * u * rho u) := by
    have hsum : ∑ jk ∈ T2, w jk * vv (ℓ - σ jk) ≤ 1.001 * rho u * Real.exp (phiV L u) *
        (Real.exp (-0.415 * L) * (0.5006 * L + 5.33)) := by
      refine (Finset.sum_le_sum hpp1).trans ?_
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by have := rho_pos u; positivity)
      refine le_of_eq_of_le ?_ hpp2
      apply Finset.sum_congr rfl
      intro jk _
      simp only [σ]
    refine hsum.trans ?_
    -- `1.001 (0.5006 L + 5.33) e^{-0.415L} ≤ 15.4 e^{-0.4 L}`
    have hexp : 1.001 * (0.5006 * L + 5.33) * Real.exp (-0.415 * L) ≤
        15.4 * Real.exp (-0.4 * L) := by
      have he : Real.exp (-0.4 * L) = Real.exp (-0.415 * L) * Real.exp (0.015 * L) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.015 * L by linarith)
      have hpos := Real.exp_pos (-0.415 * L)
      have : 1.001 * (0.5006 * L + 5.33) ≤ 15.4 * Real.exp (0.015 * L) := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ L - 100 by linarith) (show (0:ℝ) ≤ L - 100 by linarith)]
      nlinarith
    have hρφ : 0 ≤ rho u * Real.exp (phiV L u) := by have := rho_pos u; positivity
    unfold C0
    have : 0.70 * Real.exp (phiV L u) * u * rho u = 0.70 * u * (rho u * Real.exp (phiV L u)) := by
      ring
    rw [this]
    have h4 : 0 ≤ Real.exp (-0.4 * L) := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right hexp hρφ,
      mul_nonneg (mul_nonneg h4 hρφ) (show (0:ℝ) ≤ u - 1 by linarith)]
  -- (5) assemble
  have hone := integral_rho_exp_le hL0 hu1.le
  have hcert := lemV_onestep hL hu1.le huL
  unfold lhs28 at hcert
  have hρ1 : rho (u - 1) = u * ratio u * rho u := by
    unfold ratio; field_simp [(rho_pos u).ne']
  set N := C0 * Real.exp (phiV L u) * u * rho u with hN
  have hNpos : 0 < N := by have := C0_pos; have := rho_pos u; positivity
  set k := 1 - Real.exp (-BSCert.lemVAlpha u L)
  have htot : ℓ * vv ℓ ≤ N * (L - (L * k * Estar u - 2 * 1.01 * ratio u -
      22 * Real.exp (-0.4 * L) - XL L u)) := by
    have hmain3 : L * (C0 * ∫ t in (u - 1)..u, rho t * Real.exp (phiV L t)) ≤
        L * N * (1 - k * Estar u) := by
      have := mul_le_mul_of_nonneg_left hone (mul_nonneg hL0.le C0_pos.le)
      rw [hN]; nlinarith
    have hmain4 : 2 * 1.01 * (C0 * rho (u - 1) * Real.exp (phiV L u)) =
        N * (2 * 1.01 * ratio u) := by rw [hρ1, hN]; ring
    calc ℓ * vv ℓ ≤ _ := h1
      _ = _ := hsplit
      _ ≤ _ := add_le_add (hmain1.trans (add_le_add hmain2 hexcess)) hpp
      _ ≤ _ := by rw [hmain4] at *; nlinarith
  have hfin : ℓ * vv ℓ < ℓ * GV L u := by
    have : N * L = ℓ * GV L u := by rw [hN, hℓu]; unfold GV; ring
    nlinarith
  exact le_of_lt (lt_of_mul_lt_mul_left hfin (by linarith))

/-- The induction: `v(ℓ') ≤ G_V(ℓ')` for `log 72 ≤ ℓ' ≤ L²`. -/
theorem claim_all (h : P.HBS X0m Z η1 η2 ε1) {z : ℝ} (hz : 0 < z) (hL : 100 ≤ Real.log z) :
    ∀ n : ℕ, ∀ ℓ, ℓ ≤ Real.log z + n * Real.log 2 → Real.log 72 ≤ ℓ → ℓ ≤ Real.log z ^ 2 →
      2 * Real.exp ℓ ≤ Z → P.vSmooth (Real.exp ℓ) z ≤ GV (Real.log z) (ℓ / Real.log z) := by
  intro n
  induction n with
  | zero =>
    intro ℓ hℓ h72 _ hZ
    exact h.claim_base hL h72 (by simpa using hℓ) hZ
  | succ n ih =>
    intro ℓ hℓ h72 hℓ2 hZ
    rcases le_or_gt ℓ (Real.log z) with h1 | h1
    · exact h.claim_base hL h72 h1 hZ
    · apply h.claim_step hz hL h1 hℓ2 hZ
      intro ℓ' hℓ' h72' hℓ2' hZ'
      apply ih ℓ' _ h72' hℓ2' hZ'
      push_cast at hℓ
      linarith

/-- **Lemma 5.3 (smooth elements, with Dickman quality)** under (HBS) on `[1, Z]`. -/
theorem lemma53 (h : P.HBS X0m Z η1 η2 ε1) : P.Lemma53 Z := by
  intro z u hL hu1 huL hZ
  have hL0 : 0 < Real.log z := by linarith
  have hY1 : 1 ≤ Real.exp (u * Real.log z) := Real.one_le_exp (by positivity)
  have hRHS : 0 ≤ C0 * rho u * Real.exp (aV (u * Real.log z) u) := by
    have := C0_pos; have := rho_pos u; positivity
  rcases lt_or_ge z 1 with hz | hz
  · rw [vSmooth_eq_zero_of_lt_one hz hY1]; exact hRHS
  have hz0 : 0 < z := by linarith
  set ℓ := u * Real.log z
  obtain ⟨n, hn⟩ := exists_nat_ge ((ℓ - Real.log z) / Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓn : ℓ ≤ Real.log z + n * Real.log 2 := by
    rw [div_le_iff₀ hl2] at hn; linarith
  have h72 : Real.log 72 ≤ ℓ := by
    have := log72_lt_428; nlinarith
  have hℓ2 : ℓ ≤ Real.log z ^ 2 := by simp only [ℓ]; nlinarith
  have := h.claim_all hz0 hL n ℓ hℓn h72 hℓ2 hZ
  have e : ℓ / Real.log z = u := by simp only [ℓ]; field_simp
  rw [e] at this
  rw [aV_eq_phiV (by linarith : u ≠ 0)]
  exact this

end HBS

end BeurlingSystem

end
