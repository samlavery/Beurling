module

public import RequestProject.Beurling.Queue6.Noise3
public import RequestProject.Beurling.Noise.MarginR1
public import RequestProject.Beurling.Model.Land

/-!
# `Comp⁽²⁾(I) ≤ s₂|I| ≤ 1` for the windows of `𝓘_u` (proof of Theorem 6.6(i), part (b))

* `logc_le_sqrt` : **`log c ≤ √L`** at every height (`L = e^ℓ = log x`): the branch `4ℓ² - log 4`
  is `≤ e^{ℓ/2}`; for `s > s_H`, `γ(s)Λ ≤ 7.5Λ ≤ Λe^{s/2}`; for `s ≤ s_H`,
  `γ*(s)Λ = 1.3 G(Λ_s, s) Λ ≤ Λe^{s/2}`, since `6.76 (A + 1)² ≤ Λ_s - A - 1`. (The paper's
  `log M₁ ≤ log c + 0.7 ≤ 0.38√L + 0.7`, Theorem 6.23 Step 6, with the constant `1`.)
* `capM1_le_sqrt` : `M̄₁(x) ≤ 2 e^{√(log x)}` for `x ≥ X₀`;
* `s2I_mul_le` : with `s₂ = max(s₂(u/2), s₂(u), s₂(2u))` (the supremum of (s2) over the dyadic
  scales meeting `I`) and `|I| ≤ W_len(u)`: `s₂ |I| ≤ 1`;
* `E2S2Bound` : the named input, eq. (s2) for the windows of `𝓘_u` read through the
  compensators of `1[X⁽²⁾_q(I) ≥ 1]`: `∑_q P(X⁽²⁾_q(I) ≥ 1 | 𝓕_{q-}) ≤ Comp⁽²⁾(I) ≤ s₂|I|`
  (§6.3, proof of Theorem 6.6(i)(b), and Corollary 5.40), a.s. on `Good(< b)`;
* `comp2Ident_of` : `E2S2Bound ⟹ Margin.Comp2Ident` on every window of `𝓘_u`.
-/

@[expose] public section

open Set Real MeasureTheory Construction BModel CaplLink QueueMono BSCert.Capl

namespace Queue6

/-! ### `log c ≤ √L` -/

/-- `4ℓ² ≤ e^{ℓ/2}` for `ℓ ≥ 18`. -/
lemma four_sq_le_exp_half {ℓ : ℝ} (hℓ : 18 ≤ ℓ) : 4 * ℓ ^ 2 ≤ Real.exp (ℓ / 2) := by
  set t := ℓ / 2 - 9 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have e : Real.exp (ℓ / 2) = Real.exp 9 * Real.exp t := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have h9 : (8000 : ℝ) ≤ Real.exp 9 := by
    have he := Real.exp_one_gt_d9
    have e9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he.le 9
    rw [e9]; nlinarith
  have hq := Real.quadratic_le_exp_of_nonneg ht0
  have hℓt : ℓ = 2 * t + 18 := by rw [ht]; ring
  rw [e, hℓt]
  have h1 : 0 ≤ Real.exp t := (Real.exp_pos _).le
  nlinarith

/-- `6.76 (A + 1)² ≤ Λ_s - A - 1` and `0 ≤ A`, for `A = A(Λ_s, s)`, `s ≤ s_H`. -/
lemma A_small {s : ℝ} (hs : s ≤ 5.9746) :
    0 ≤ A (LamS s) s ∧ 6.76 * (A (LamS s) s + 1) ^ 2 ≤ LamS s - A (LamS s) s - 1 := by
  set V := LamS s with hV
  have hV8 : 100000000 ≤ V := LamS_ge s
  have hsV : -Real.log V ≤ s := neg_log_LamS_le s
  have hA6 := A_ge_six hV8 hsV
  have hL18 := log_ge_18 hV8
  have hV0 : 0 < V := by linarith
  have hl : 0 < 2 * Real.log V + s := by linarith
  have hAeq := A_eq hV0 hl
  have hlog0 : 0 ≤ Real.log (2 * Real.log V + s) := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hAle : A V s ≤ 0.7 + 3 * Real.log V + 2 * s := by rw [hAeq]; linarith
  obtain ⟨hL1, hL2⟩ := log1e8_bounds
  refine ⟨by linarith, ?_⟩
  rcases le_or_gt (-Real.log 100000000) s with hs8 | hs8
  · -- `Λ_s = 10⁸`
    have hVe : V = 100000000 := by
      rw [hV]; unfold LamS
      apply max_eq_left
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 100000000)]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [hVe] at hAle ⊢
    rw [hVe] at hA6
    have : A 100000000 s ≤ 68 := by linarith
    nlinarith
  · -- `Λ_s = e^{-s}`
    set u := -s with hu
    have hVe : V = Real.exp u := by
      rw [hV]; unfold LamS
      apply max_eq_right
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 100000000)]
      exact Real.exp_le_exp.mpr (by linarith)
    have hlV : Real.log V = u := by rw [hVe, Real.log_exp]
    rw [hlV] at hAle
    have hAu : A V s ≤ u + 0.7 := by linarith
    set t := u - Real.log 100000000 with ht
    have ht0 : 0 ≤ t := by linarith
    have heu : Real.exp u = 100000000 * Real.exp t := by
      rw [show u = Real.log 100000000 + t by rw [ht]; ring, Real.exp_add,
        Real.exp_log (by norm_num)]
    have hq := Real.quadratic_le_exp_of_nonneg ht0
    have hAt : A V s ≤ t + 19.13 := by linarith
    have hVv : V = 100000000 * Real.exp t := by rw [hVe, heu]
    have hA0 : 0 ≤ A V s := by linarith
    have h1 : (A V s + 1) ^ 2 ≤ (t + 20.13) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : 6.76 * (t + 20.13) ^ 2 + t + 20.13 ≤
        100000000 * (1 + t + t ^ 2 / 2) := by nlinarith
    have h3 : 100000000 * (1 + t + t ^ 2 / 2) ≤ 100000000 * Real.exp t := by linarith
    linarith

/-- **`log c(s) ≤ e^{ℓ/2} = √L`** for `Λ ≥ 10⁸`, `s ≥ -log Λ` (`ℓ = 2 log Λ + s`). -/
theorem logc_le_sqrt {Λ s : ℝ} (hΛ : 100000000 ≤ Λ) (hs : -Real.log Λ ≤ s) :
    logc sHroot Λ s ≤ Real.exp ((2 * Real.log Λ + s) / 2) := by
  have hΛ0 : 0 < Λ := by linarith
  have hL18 := log_ge_18 hΛ
  have hℓ : 18 ≤ 2 * Real.log Λ + s := by linarith
  have hexp : Real.exp ((2 * Real.log Λ + s) / 2) = Λ * Real.exp (s / 2) := by
    rw [show (2 * Real.log Λ + s) / 2 = Real.log Λ + s / 2 by ring, Real.exp_add,
      Real.exp_log hΛ0]
  unfold logc
  refine max_le ?_ ?_
  · have := four_sq_le_exp_half hℓ
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · rw [hexp]
    obtain ⟨hsH1, hsH2⟩ := sHroot_mem
    by_cases hsc : s ≤ sHroot
    · -- `γ(s) = γ*(s) = 1.3 G(Λ_s, s)`
      unfold gam; rw [if_pos hsc]
      obtain ⟨hA0, hA⟩ := A_small (s := s) (by linarith)
      set V := LamS s
      set a := A V s
      have hD : 0 < V - a - 1 := by nlinarith
      have hsq : 2.6 * (a + 1) ≤ Real.sqrt (V - a - 1) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have hG : G V s ≤ Real.exp (s / 2) / 1.3 := by
        unfold G
        have h1 : Real.sqrt (a * (a + 1)) ≤ a + 1 := sqrt_mul_succ_le hA0
        have hsp : 0 < Real.sqrt (V - a - 1) := Real.sqrt_pos.mpr hD
        rw [div_le_div_iff₀ hsp (by norm_num)]
        have he := Real.exp_pos (s / 2)
        have hsq' : 0 ≤ Real.sqrt (a * (a + 1)) := Real.sqrt_nonneg _
        have h2 : 2 * Real.sqrt (a * (a + 1)) * Real.exp (s / 2) * 1.3 ≤
            2 * (a + 1) * Real.exp (s / 2) * 1.3 := by gcongr
        nlinarith
      unfold gstar
      have : 1.3 * G V s ≤ Real.exp (s / 2) := by
        have := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 1.3)
        calc 1.3 * G V s ≤ 1.3 * (Real.exp (s / 2) / 1.3) := this
          _ = Real.exp (s / 2) := by field_simp
      nlinarith
    · -- `γ(s) ≤ 7.5 ≤ e^{s/2}`
      push_neg at hsc
      have hg := gam_le_of_gt gstar_sHroot_le hsc
      have he : (7.5 : ℝ) ≤ Real.exp (s / 2) := by
        have h1 : (393 : ℝ) ≤ Real.exp s :=
          exp_sH_ge.trans (Real.exp_le_exp.mpr (by linarith))
        have h2 : Real.exp s = Real.exp (s / 2) ^ 2 := by
          rw [← Real.exp_nat_mul]; ring_nf
        have h3 := Real.exp_pos (s / 2)
        nlinarith
      calc gam sHroot s * Λ ≤ 7.5 * Λ := mul_le_mul_of_nonneg_right hg hΛ0.le
        _ ≤ Λ * Real.exp (s / 2) := by nlinarith

/-- **`M̄₁(x) ≤ 2 e^{√(log x)}`** for `x ≥ X₀` (Theorem 6.23 Step 6, `log M₁ ≤ √L + log 2`). -/
theorem capM1_le_sqrt {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    capM1 X₀ x ≤ 2 * Real.exp (Real.sqrt (Real.log x)) := by
  have h1 := capM1_le_two_exp hX0 hX hx
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hlX : 0 < Real.log X₀ := by linarith
  have hlx : Real.log X₀ ≤ Real.log x := Real.log_le_log (by linarith) hx
  have hs : -Real.log (Real.log X₀) ≤ capS X₀ x := by
    unfold capS
    have := Real.log_le_log hlX hlx
    linarith
  have h2 := logc_le_sqrt (Λ := Real.log X₀) (s := capS X₀ x) (by linarith) hs
  rw [ell_eq] at h2
  have hsq : Real.exp (Real.log (Real.log x) / 2) = Real.sqrt (Real.log x) := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by linarith) (Real.exp_pos _).le,
      ← Real.exp_add, show Real.log (Real.log x) / 2 + Real.log (Real.log x) / 2 =
        Real.log (Real.log x) by ring, Real.exp_log (by linarith)]
  rw [hsq] at h2
  refine h1.trans ?_
  unfold logcAt
  gcongr

/-! ### `s₂ |I| ≤ 1` -/

/-- `s₂ = max(s₂(u/2), s₂(u), s₂(2u))`, the supremum of (s2) over the dyadic scales meeting a
window of `𝓘_u`. -/
noncomputable def s2I (X₀ : ℕ) (m : ℕ) : ℝ :=
  max (s2E3 X₀ (uS X₀ m / 2)) (max (s2E3 X₀ (uS X₀ m)) (s2E3 X₀ (2 * uS X₀ m)))

/-- `s₂(v) ≤ 9 (L + 1.1) e^{1 - 2√L}` for `L - 0.7 ≤ log v ≤ L + 0.7`, `L ≥ 10⁸`. -/
lemma s2E3_le_L (X₀ : ℕ) {v L : ℝ} (hL : 10 ^ 8 ≤ L) (hv1 : L - 0.7 ≤ Real.log v)
    (hv2 : Real.log v ≤ L + 0.7) :
    s2E3 X₀ v ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by
  unfold s2E3
  have hlv : 0 < Real.log v := by linarith
  have hll : 18 ≤ Real.log (Real.log v) := BModel.log_ge_18' (by linarith)
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsL2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hsL1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hroot : 4 * Real.sqrt L - 2 ≤ Real.sqrt (Real.log v * Real.log (Real.log v)) := by
    apply Real.le_sqrt_of_sq_le
    have : (L - 0.7) * 18 ≤ Real.log v * Real.log (Real.log v) := by nlinarith
    nlinarith
  have hmax : 2 * Real.sqrt L - 1 ≤
      max (Real.log (Xm X₀)) (Real.sqrt (Real.log v * Real.log (Real.log v)) / 2) :=
    le_max_of_le_right (by linarith)
  have he : Real.exp (-(max (Real.log (Xm X₀))
      (Real.sqrt (Real.log v * Real.log (Real.log v)) / 2))) ≤
      Real.exp (1 - 2 * Real.sqrt L) := Real.exp_le_exp.mpr (by linarith)
  have hp := Real.exp_pos (-(max (Real.log (Xm X₀))
      (Real.sqrt (Real.log v * Real.log (Real.log v)) / 2)))
  calc 9 * Real.log v * Real.exp (-(max (Real.log (Xm X₀))
        (Real.sqrt (Real.log v * Real.log (Real.log v)) / 2)))
      ≤ 9 * (L + 1.1) * Real.exp (-(max (Real.log (Xm X₀))
        (Real.sqrt (Real.log v * Real.log (Real.log v)) / 2))) := by gcongr; linarith
    _ ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by gcongr

/-- `log 504000 + 1 + 5 log(L + 1.4) ≤ √L` for `L ≥ 10⁸`. -/
lemma log_poly_le_sqrt {L : ℝ} (hL : 10 ^ 8 ≤ L) :
    Real.log 504000 + 1 + 5 * Real.log (L + 1.4) ≤ Real.sqrt L := by
  set t := Real.sqrt L with htd
  have ht2 : t ^ 2 = L := Real.sq_sqrt (by linarith)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht : 10000 ≤ t := by
    rw [htd, show (10000 : ℝ) = Real.sqrt (10 ^ 8) by
      rw [show (10 : ℝ) ^ 8 = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  have h504 : Real.log 504000 ≤ 14 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have e : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) he.le 14
    rw [e]; nlinarith
  -- `log(L + 1.1) ≤ log(2t²) = log 2 + 2 log t`, `log t ≤ log 100 + t/100 - 1`
  have h1 : Real.log (L + 1.4) ≤ Real.log 2 + 2 * Real.log t := by
    have e := Real.log_pow t 2
    push_cast at e
    rw [← e, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log t ≤ Real.log 100 + (t / 100 - 1) := by
    have := Real.log_le_sub_one_of_pos (show 0 < t / 100 by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have h100 : Real.log 100 ≤ 4.7 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 4.7 ≥ 1 + 4.7 + 4.7 ^ 2 / 2 := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4.7 by norm_num); linarith
    -- `e^{4.7} = e^4 · e^{0.7}`
    have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
    have h07 : (1.94 : ℝ) ≤ Real.exp 0.7 := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7 by norm_num); linarith
    have e47 : Real.exp 4.7 = Real.exp 4 * Real.exp 0.7 := by rw [← Real.exp_add]; norm_num
    rw [e47, e4]; nlinarith
  have hl2 := Real.log_two_lt_d9
  linarith

/-- **`s₂ |I| ≤ 1`** for the windows of `𝓘_u` (`|I| ≤ W_len(u)`): with
`|I| ≤ 28000 M_q L_q⁴`, `M_q ≤ 2e^{√L}` and `s₂ ≤ 9(L + 1.1)e^{1-2√L}`,
`s₂ |I| ≤ 504000 e (L + 1.1)⁵ e^{-√L} ≤ 1`. -/
theorem s2I_mul_le {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {m : ℕ} {a b : ℤ}
    (hadm : Adm X₀ m a b) : s2I X₀ m * ((b : ℝ) - a) ≤ 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hu := X₀_le_uS (X₀ := X₀) (by linarith) m
  set u := uS X₀ m with hudef
  have hu0 : 0 < u := by linarith
  have hL := (logs_of_ge hX0 hX hu).1
  set L := Real.log u with hLdef
  obtain ⟨-, -, hab, hW⟩ := hadm
  have hab' : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hI : (b : ℝ) - a ≤ Wlen X₀ u := by push_cast at hW; exact hW
  -- `W_len ≤ 28000 · 2e^{√L} · (L + 1.1)⁴`
  have hWl := Wlen_le hX0 hX hu
  have hMq : Mq X₀ u ≤ 2 * Real.exp (Real.sqrt L) := by
    unfold Mq
    have h1 := capM1_le_sqrt hX0 hX (uq_ge (X₀ := (X₀ : ℝ)) (u := u))
    refine h1.trans ?_
    have hq := uq_le hX0 hu
    have hq0 : 0 < uq X₀ u := by linarith [uq_ge (X₀ := (X₀ : ℝ)) (u := u)]
    gcongr
    exact Real.log_le_log hq0 hq
  obtain ⟨-, hLq2, hLq3⟩ := Lq_bounds hX0 hX hu
  have hLq0 : 0 ≤ Lq u := by
    have := (Lq_bounds hX0 hX hu).1; linarith
  have hLq : Lq u ≤ L + 1.4 := by linarith
  -- `s₂ ≤ 9(L + 1.1)e^{1 - 2√L}`
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hs1 : s2E3 X₀ (u / 2) ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by
    apply s2E3_le_L X₀ hL <;> rw [Real.log_div hu0.ne' (by norm_num)] <;> linarith
  have hs2 : s2E3 X₀ u ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by
    apply s2E3_le_L X₀ hL <;> linarith
  have hs3 : s2E3 X₀ (2 * u) ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by
    apply s2E3_le_L X₀ hL <;> rw [Real.log_mul (by norm_num) hu0.ne'] <;> linarith
  have hs : s2I X₀ m ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) :=
    max_le hs1 (max_le hs2 hs3)
  have hL0 : 0 ≤ L := by linarith
  have hS0 : 0 ≤ 9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L) := by positivity
  have hWb : Wlen X₀ u ≤ 28000 * (2 * Real.exp (Real.sqrt L)) * (L + 1.4) ^ 4 := by
    refine hWl.trans ?_
    have hMq0 : 0 ≤ Mq X₀ u := by linarith [Mq_ge_one hX0 hX hu]
    gcongr
  have hpl := log_poly_le_sqrt hL
  have hpow : (L + 1.4) ^ 5 = Real.exp (5 * Real.log (L + 1.4)) := by
    rw [show (5 : ℝ) * Real.log (L + 1.4) = Real.log ((L + 1.4) ^ 5) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  calc s2I X₀ m * ((b : ℝ) - a)
      ≤ (9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L)) * Wlen X₀ u :=
        mul_le_mul hs hI hab' hS0
    _ ≤ (9 * (L + 1.1) * Real.exp (1 - 2 * Real.sqrt L)) *
          (28000 * (2 * Real.exp (Real.sqrt L)) * (L + 1.4) ^ 4) :=
        mul_le_mul_of_nonneg_left hWb hS0
    _ = 504000 * ((L + 1.1) * (L + 1.4) ^ 4) *
          (Real.exp (1 - 2 * Real.sqrt L) * Real.exp (Real.sqrt L)) := by ring
    _ ≤ 504000 * (L + 1.4) ^ 5 * Real.exp (1 - Real.sqrt L) := by
        rw [← Real.exp_add, show 1 - 2 * Real.sqrt L + Real.sqrt L = 1 - Real.sqrt L by ring]
        have : (L + 1.1) * (L + 1.4) ^ 4 ≤ (L + 1.4) ^ 5 := by
          rw [pow_succ]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ L + 1.4 by linarith) 4]
        gcongr
    _ = Real.exp (Real.log 504000 + 5 * Real.log (L + 1.4) + (1 - Real.sqrt L)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), ← hpow]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-! ### The named input and `Comp2Ident` -/

variable (θ : ℝ) (X₀ : ℕ)

/-- **Eq. (s2) for the windows of `𝓘_u`** (§6.3, proof of Theorem 6.6(i)(b), with Corollary
5.40): a.s. on `Good(< b)`,
`∑_q P(X⁽²⁾_q(I) ≥ 1 | 𝓕_{q-}) ≤ Comp⁽²⁾(I) ≤ s₂ |I|`, `s₂ = max(s₂(u/2), s₂(u), s₂(2u))`,
read through the partial compensators of `1[X⁽²⁾_q(I) ≥ 1]`. -/
def E2S2Bound : Prop :=
  ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) → ∀ n,
    ∑ k ∈ Finset.range n, (jitterMeasure[Ind2 θ X₀ a b k | jitterFiltration k]) ω ≤
      s2I X₀ m * ((b : ℝ) - a)

variable {θ X₀}

/-- **`E2S2Bound ⟹ Comp2Ident`** on every window of `𝓘_u`, with `s₂|I| ≤ 1` proved. -/
theorem comp2Ident_of (hX : 10 ^ 8 ≤ Real.log X₀) (h : E2S2Bound θ X₀) :
    ∀ m a b, Adm X₀ m a b → ∀ᵐ ω ∂jitterMeasure, ω ∈ G0 θ X₀ (e3Family θ X₀) (tE2 b) →
      Margin.Comp2Ident θ X₀ a b ω := by
  intro m a b hadm
  filter_upwards [h m a b hadm] with ω hω hG
  exact ⟨s2I X₀ m * ((b : ℝ) - a), s2I X₀ m, le_rfl, s2I_mul_le hX hadm, hω hG⟩

end Queue6

end
