module

public import RequestProject.Beurling.Construction.JitterRegular
public import RequestProject.Beurling.RankFull.PatternTail

/-!
# `SlotHyp` for the paper's jitter width `H = max(H_std, M̄₁²)`

The standing hypotheses `RankFull.SlotHyp H X₀` of Appendix A (§A.2: `X₀ ≥ 1000`,
`1 ≤ H(X₀) ≤ 5·10⁻⁴ X₀`, and `H(v)/v` non-increasing on `[X₀, ∞)`) hold for `H = capH X₀`
whenever `log X₀ ≥ 10⁸`. The monotonicity of `H(v)/v` is the last assertion of (R_H) in §4.1
("`H(v)/v` is decreasing"; Theorem 6.23(c)). It is proved here without derivatives, in the
variable `ℓ = log log v`:

* `logc_le_div` : `log c(s) ≤ log x / 16` (from `c² ≤ M̄₁² ≤ H ≤ x^{1/8}`);
* `logc_step` : `log c(t) ≤ log c(s) + δ L/2` for `t = s + δ`, `0 ≤ δ ≤ 10⁻³`, `L = log x`.
  Below the break point `s_H` this is `G(Λ_t, t) ≤ G(Λ_s, s)(1 + 4δ)` (`G_lip`) together with
  `γ*(s) Λ ≤ log c(s) ≤ L/16`; above it, `γ` is `8`-Lipschitz (`gam_lip`) and `L ≥ Λ² ≥ 16Λ`;
* `capH_div_step` : `H(y) x ≤ H(x) y` for `X₀ ≤ x ≤ y` with `log log y - log log x ≤ 10⁻³`;
* `capH_div_antitoneOn` : `v ↦ H(v)/v` is antitone on `[X₀, ∞)` (chaining the steps);
* `slotHyp_capH` : `RankFull.SlotHyp (capH X₀) X₀`.
-/

@[expose] public section

open Real Set BSCert.Capl CaplLink

namespace BModel

/-- `16 log L + 8 ≤ L` for `L ≥ 10⁸`. -/
lemma sixteen_log_add_le {L : ℝ} (hL : 10 ^ 8 ≤ L) : 16 * Real.log L + 8 ≤ L := by
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 64 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  nlinarith

/-- `M̄₁ ≥ c` (the term `c` of `φ(r̄₀)`), for `Λ > 0`, `2 log Λ + s > 0`. -/
lemma exp_logc_le_Mbar1 {sH Λ s : ℝ} (hl : 0 < 2 * Real.log Λ + s) :
    Real.exp (logc sH Λ s) ≤ Mbar1 sH Λ s := by
  have hr : 0 ≤ rbar0 Λ s := by unfold rbar0; positivity
  simp only [Mbar1]
  have h1 : 0 ≤ rbar0 Λ s * Real.sqrt (Real.exp (logc sH Λ s)) := by positivity
  have h2 : 0 ≤ rbar0 Λ s * (rbar0 Λ s + 1) / 2 := by positivity
  linarith

/-- **`log c(s) ≤ log x / 16`**: `c² ≤ M̄₁² ≤ H(x) ≤ x^{1/8}`. -/
lemma logc_le_div {X₀ x : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x) :
    logc sHroot (Real.log X₀) (capS X₀ x) ≤ Real.log x / 16 := by
  obtain ⟨-, -, hℓ⟩ := logs_of_ge hX0 hX hx
  have hx0 : 0 < x := by linarith [QueueMono.one_lt_of_logX hX0 hX]
  have hc := exp_logc_le_Mbar1 (sH := sHroot) (Λ := Real.log X₀) (s := capS X₀ x)
    (by rw [ell_eq]; exact hℓ)
  have hH := InitialRange.capH_le_rpow hX0 hX hx
  have hM : capM1 X₀ x ^ 2 ≤ capH X₀ x := le_max_right _ _
  have hc2 : Real.exp (logc sHroot (Real.log X₀) (capS X₀ x)) ^ 2 ≤ capM1 X₀ x ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hc 2
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul] at *
  have h := Real.exp_le_exp.mp ((hc2.trans hM).trans hH)
  push_cast at h
  linarith

/-- `G(Λ_t, t) ≤ G(Λ_s, s)(1 + 4δ)` turned into `Λ γ*(t) ≤ Λ γ*(s) (1 + 4δ)`. -/
lemma gstar_mul_step {Λ s t : ℝ} (hΛ : 0 ≤ Λ) (hst : s ≤ t) (ht : t ≤ 6)
    (hδ : t - s ≤ 1 / 1000) : gstar t * Λ ≤ gstar s * Λ * (1 + 4 * (t - s)) := by
  have h := G_lip hst ht hδ
  unfold gstar
  have : 1.3 * G (LamS t) t ≤ 1.3 * (G (LamS s) s * (1 + 4 * (t - s))) := by linarith
  nlinarith

/-- **One step for `log c`**: `log c(t) ≤ log c(s) + δ L/2` for `s = s(x)`, `t = s(y)`,
`δ = t - s ∈ [0, 10⁻³]`, `L = log x`. -/
lemma logc_step {X₀ x y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxy : x ≤ y) (hδ : Real.log (Real.log y) - Real.log (Real.log x) ≤ 1 / 1000) :
    logc sHroot (Real.log X₀) (capS X₀ y) ≤ logc sHroot (Real.log X₀) (capS X₀ x) +
      (Real.log (Real.log y) - Real.log (Real.log x)) * Real.log x / 2 := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  obtain ⟨hL, hℓΛ, hℓ⟩ := logs_of_ge hX0 hX hx
  have hyX : X₀ ≤ y := hx.trans hxy
  obtain ⟨hL', -, hℓ'⟩ := logs_of_ge hX0 hX hyX
  have hx0 : 0 < x := by linarith
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log x with hLdef
  set ℓ := Real.log L with hℓdef
  set ℓ' := Real.log (Real.log y) with hℓ'def
  set δ := ℓ' - ℓ with hδdef
  have hδ0 : 0 ≤ δ := by
    have h1 : L ≤ Real.log y := Real.log_le_log hx0 hxy
    have := Real.log_le_log (by linarith) h1
    rw [hδdef]; linarith
  set s := capS X₀ x with hsdef
  set t := capS X₀ y with htdef
  have hes : 2 * Real.log Λ + s = ℓ := ell_eq X₀ x
  have het : 2 * Real.log Λ + t = ℓ' := ell_eq X₀ y
  have hts : t - s = δ := by rw [hδdef]; linarith
  have hlogL : 16 * ℓ + 8 ≤ L := sixteen_log_add_le hL
  have hLc : logc sHroot Λ s ≤ L / 16 := logc_le_div hX0 hX hx
  have hΛ0 : 0 < Λ := by linarith
  unfold logc at hLc ⊢
  rw [hes] at hLc ⊢
  rw [het]
  have hm1 := le_max_left (4 * ℓ ^ 2 - Real.log 4) (gam sHroot s * Λ)
  have hm2 := le_max_right (4 * ℓ ^ 2 - Real.log 4) (gam sHroot s * Λ)
  have hδL : 0 ≤ δ * L := by positivity
  apply max_le
  · have e : ℓ' = ℓ + δ := by rw [hδdef]; ring
    rw [e]
    have : 4 * (ℓ + δ) ^ 2 - 4 * ℓ ^ 2 ≤ δ * L / 2 := by nlinarith
    linarith
  · have hsH := sHroot_mem
    by_cases ht6 : t ≤ sHroot
    · have hs6 : s ≤ sHroot := by linarith
      have e1 : gam sHroot t = gstar t := by unfold gam; rw [if_pos ht6]
      have e2 : gam sHroot s = gstar s := by unfold gam; rw [if_pos hs6]
      rw [e1]; rw [e2] at hm2 hLc ⊢
      have h := gstar_mul_step (s := s) (t := t) hΛ0.le (by linarith) (by linarith [hsH.2])
        (by linarith)
      rw [hts] at h
      have h2 : δ * (gstar s * Λ) ≤ δ * (L / 16) :=
        mul_le_mul_of_nonneg_left (hm2.trans hLc) hδ0
      nlinarith
    · push_neg at ht6
      have hg := gstar_sHroot
      have hg0 : 0 ≤ gstar sHroot := by rw [hg]; unfold gTarget; norm_num
      have hg1 : gstar sHroot ≤ 1 / 3 := by rw [hg]; unfold gTarget; norm_num
      have h := gam_lip (by linarith [hsH.2]) hg0 hg1 (show s ≤ t by linarith)
        (by linarith)
      rw [hts] at h
      -- `L = Λ² e^s ≥ Λ² ≥ 16 Λ`
      have hs0 : 0 ≤ s := by linarith [hsH.1]
      have hLΛ : Λ ^ 2 ≤ L := by
        have h1 : L = Real.exp ℓ := (Real.exp_log (by linarith)).symm
        rw [h1, ← hes, Real.exp_add]
        have h2 : Real.exp (2 * Real.log Λ) = Λ ^ 2 := by
          rw [show 2 * Real.log Λ = Real.log (Λ ^ 2) by rw [Real.log_pow]; norm_num,
            Real.exp_log (by positivity)]
        rw [h2]
        have := Real.one_le_exp hs0
        nlinarith [sq_nonneg Λ]
      have h16 : 16 * Λ ≤ L := by nlinarith
      have : (gam sHroot t - gam sHroot s) * Λ ≤ 8 * δ * Λ :=
        mul_le_mul_of_nonneg_right h hΛ0.le
      have := mul_le_mul_of_nonneg_left h16 hδ0
      linarith

/-- `M̄₁` scales by at most `e²` when `r̄₀` scales by `e ≥ 1` and `c` by `e²`. -/
lemma Mbar1_scale {sH Λ s t e : ℝ} (he : 1 ≤ e) (hr0 : 0 ≤ rbar0 Λ s) (hr0' : 0 ≤ rbar0 Λ t)
    (hr : rbar0 Λ t ≤ e * rbar0 Λ s)
    (hc : Real.exp (logc sH Λ t) ≤ e ^ 2 * Real.exp (logc sH Λ s)) :
    Mbar1 sH Λ t ≤ e ^ 2 * Mbar1 sH Λ s := by
  simp only [Mbar1]
  set r := rbar0 Λ s
  set r' := rbar0 Λ t
  set c := Real.exp (logc sH Λ s)
  set c' := Real.exp (logc sH Λ t)
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hsq : Real.sqrt c' ≤ e * Real.sqrt c := by
    have h := Real.sqrt_le_sqrt hc
    rwa [Real.sqrt_mul (sq_nonneg e), Real.sqrt_sq (by linarith)] at h
  have hs0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  have hs0' : 0 ≤ Real.sqrt c' := Real.sqrt_nonneg _
  have h1 : r' * Real.sqrt c' ≤ (e * r) * (e * Real.sqrt c) :=
    mul_le_mul hr hsq hs0' (by positivity)
  have h2 : r' * (r' + 1) ≤ (e * r) * (e * r + e) :=
    mul_le_mul hr (by linarith) (by linarith) (by positivity)
  have h3 : e * r ≤ e ^ 2 * r := by nlinarith
  have h4 : (1 : ℝ) ≤ e ^ 2 := by nlinarith
  have e1 : (e * r) * (e * Real.sqrt c) = e ^ 2 * (r * Real.sqrt c) := by ring
  have e2 : (e * r) * (e * r + e) = e ^ 2 * (r * (r + 1)) := by ring
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **One step for `H(v)/v`**: `H(y) x ≤ H(x) y` for `X₀ ≤ x ≤ y`,
`log log y - log log x ≤ 10⁻³`. -/
theorem capH_div_step {X₀ x y : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) (hx : X₀ ≤ x)
    (hxy : x ≤ y) (hδ : Real.log (Real.log y) - Real.log (Real.log x) ≤ 1 / 1000) :
    capH X₀ y * x ≤ capH X₀ x * y := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  obtain ⟨hL, hℓΛ, hℓ⟩ := logs_of_ge hX0 hX hx
  have hyX : X₀ ≤ y := hx.trans hxy
  obtain ⟨hL', -, hℓ'⟩ := logs_of_ge hX0 hX hyX
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlc := logc_step hX0 hX hx hxy hδ
  set Λ := Real.log X₀ with hΛdef
  set L := Real.log x with hLdef
  set L' := Real.log y with hL'def
  set ℓ := Real.log L with hℓdef
  set ℓ' := Real.log L' with hℓ'def
  set δ := ℓ' - ℓ with hδdef
  have hδ0 : 0 ≤ δ := by
    have h1 : L ≤ L' := Real.log_le_log hx0 hxy
    have := Real.log_le_log (by linarith) h1
    rw [hδdef]; linarith
  have hlogL : 16 * ℓ + 8 ≤ L := sixteen_log_add_le hL
  have heL : Real.exp ℓ = L := Real.exp_log (by linarith)
  have heL' : Real.exp ℓ' = L' := Real.exp_log (by linarith)
  have hLL : L + δ * L ≤ L' := by
    have e : ℓ' = ℓ + δ := by rw [hδdef]; ring
    rw [← heL', e, Real.exp_add, heL]
    have := Real.add_one_le_exp δ
    nlinarith
  have hxe : x = Real.exp L := (Real.exp_log hx0).symm
  have hye : y = Real.exp L' := (Real.exp_log hy0).symm
  have hδL : 0 ≤ δ * L := by positivity
  -- the standard part
  have hP : Real.exp (8 * ℓ' ^ 2) * x ≤ Real.exp (8 * ℓ ^ 2) * y := by
    rw [hxe, hye, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have e : ℓ' = ℓ + δ := by rw [hδdef]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hlogL hδ0
    nlinarith
  -- the raised part
  set s := capS X₀ x with hsdef
  set t := capS X₀ y with htdef
  have hes : 2 * Real.log Λ + s = ℓ := ell_eq X₀ x
  have het : 2 * Real.log Λ + t = ℓ' := ell_eq X₀ y
  set e := Real.exp (δ * L / 4) with hedef
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have he2 : e ^ 2 = Real.exp (δ * L / 2) := by
    rw [hedef, ← Real.exp_nat_mul]; ring_nf
  have hc : Real.exp (logc sHroot Λ t) ≤ e ^ 2 * Real.exp (logc sHroot Λ s) := by
    rw [he2, ← Real.exp_add, Real.exp_le_exp]; linarith
  have hr0 : 0 ≤ rbar0 Λ s := by unfold rbar0; rw [hes]; positivity
  have hr0' : 0 ≤ rbar0 Λ t := by unfold rbar0; rw [het]; positivity
  have hr : rbar0 Λ t ≤ e * rbar0 Λ s := by
    unfold rbar0
    rw [hes, het]
    have hδe : Real.exp δ ≤ e := Real.exp_le_exp.mpr (by nlinarith)
    have e1 : Real.exp ℓ' = Real.exp ℓ * Real.exp δ := by
      rw [← Real.exp_add]; congr 1; rw [hδdef]; ring
    have hq : Real.exp ℓ' / (3 * ℓ') ≤ Real.exp ℓ' / (3 * ℓ) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by linarith)
    have hq2 : Real.exp ℓ' / (3 * ℓ) ≤ e * (Real.exp ℓ / (3 * ℓ)) := by
      rw [e1, mul_div_assoc', mul_comm e]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hδe (Real.exp_pos _).le) (by positivity)
    have : 4 ≤ e * 4 := by linarith
    rw [mul_add]; linarith
  have hM : capM1 X₀ y ≤ e ^ 2 * capM1 X₀ x := Mbar1_scale he1 hr0 hr0' hr hc
  have hM0 : 0 ≤ capM1 X₀ y := (capM1_pos hX0 hX hyX).le
  have hQ : capM1 X₀ y ^ 2 * x ≤ capM1 X₀ x ^ 2 * y := by
    have h1 : capM1 X₀ y ^ 2 ≤ (e ^ 2 * capM1 X₀ x) ^ 2 := pow_le_pow_left₀ hM0 hM 2
    have h2 : (e ^ 2) ^ 2 * x ≤ y := by
      rw [he2, ← Real.exp_nat_mul, hxe, hye, ← Real.exp_add, Real.exp_le_exp]
      push_cast; linarith
    calc capM1 X₀ y ^ 2 * x ≤ (e ^ 2 * capM1 X₀ x) ^ 2 * x :=
          mul_le_mul_of_nonneg_right h1 hx0.le
      _ = capM1 X₀ x ^ 2 * ((e ^ 2) ^ 2 * x) := by ring
      _ ≤ capM1 X₀ x ^ 2 * y := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  unfold capH
  rw [max_mul_of_nonneg _ _ hx0.le, max_mul_of_nonneg _ _ hy0.le]
  exact max_le_max hP hQ

/-- Chaining: a function that does not increase over steps of length `≤ η` from `a₀` on is
antitone on `[a₀, ∞)`. -/
lemma antitoneOn_of_step {f : ℝ → ℝ} {a₀ η : ℝ} (hη : 0 < η)
    (h : ∀ a b, a₀ ≤ a → a ≤ b → b ≤ a + η → f b ≤ f a) : AntitoneOn f (Ici a₀) := by
  have key : ∀ n : ℕ, ∀ a b, a₀ ≤ a → a ≤ b → b ≤ a + n * η → f b ≤ f a := by
    intro n
    induction n with
    | zero => intro a b _ hab hb; simp at hb; rw [le_antisymm hab hb]
    | succ n ih =>
      intro a b ha hab hb
      by_cases hc : b ≤ a + η
      · exact h a b ha hab hc
      · push_neg at hc
        have h1 := h (b - η) b (by linarith) (by linarith) (by linarith)
        have h2 := ih a (b - η) ha (by linarith) (by push_cast at hb; linarith)
        linarith
  intro a ha b _ hab
  refine key ⌈(b - a) / η⌉₊ a b ha hab ?_
  have h1 := Nat.le_ceil ((b - a) / η)
  rw [div_le_iff₀ hη] at h1
  linarith

/-- **`H(v)/v` is non-increasing on `[X₀, ∞)`** (§4.1, (R_H); Theorem 6.23(c)). -/
theorem capH_div_antitoneOn {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    AntitoneOn (fun v => capH X₀ v / v) (Ici X₀) := by
  have hX1 := QueueMono.one_lt_of_logX hX0 hX
  have hΛ : 0 < Real.log X₀ := by linarith
  set g : ℝ → ℝ := fun a => capH X₀ (Real.exp (Real.exp a)) / Real.exp (Real.exp a) with hg
  have hee : ∀ v, 1 < v → Real.exp (Real.exp (Real.log (Real.log v))) = v := by
    intro v hv
    rw [Real.exp_log (Real.log_pos hv), Real.exp_log (by linarith)]
  have hga : AntitoneOn g (Ici (Real.log (Real.log X₀))) := by
    refine antitoneOn_of_step (η := 1 / 1000) (by norm_num) ?_
    intro a b ha hab hb
    have hxX : X₀ ≤ Real.exp (Real.exp a) := by
      rw [← hee X₀ hX1]
      exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ha)
    have hxy : Real.exp (Real.exp a) ≤ Real.exp (Real.exp b) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hab)
    have hll : Real.log (Real.log (Real.exp (Real.exp b))) -
        Real.log (Real.log (Real.exp (Real.exp a))) ≤ 1 / 1000 := by
      simp only [Real.log_exp]; linarith
    have hst := capH_div_step hX0 hX hxX hxy hll
    show capH X₀ (Real.exp (Real.exp b)) / Real.exp (Real.exp b) ≤
      capH X₀ (Real.exp (Real.exp a)) / Real.exp (Real.exp a)
    rw [div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)]
    exact hst
  intro v hv w hw hvw
  have hv1 : 1 < v := lt_of_lt_of_le hX1 hv
  have hw1 : 1 < w := lt_of_lt_of_le hX1 hw
  have hmono : ∀ {u u' : ℝ}, 1 < u → u ≤ u' → Real.log (Real.log u) ≤ Real.log (Real.log u') :=
    fun hu huu => Real.log_le_log (Real.log_pos hu)
      (Real.log_le_log (by linarith) huu)
  have h := hga (hmono hX1 hv) (hmono hX1 hw) (hmono hv1 hvw)
  have e1 := hee v hv1
  have e2 := hee w hw1
  simp only [hg] at h
  rw [e1, e2] at h
  exact h

/-- **The standing hypotheses of Appendix A hold for `H = capH X₀`** (`X₀ ≥ 1000`,
`1 ≤ H(X₀) ≤ 5·10⁻⁴ X₀`, `H(v)/v` non-increasing on `[X₀, ∞)`), for `log X₀ ≥ 10⁸`. -/
theorem slotHyp_capH {X₀ : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀) :
    RankFull.SlotHyp (capH X₀) X₀ where
  hX₀ := by
    have hX1 := QueueMono.one_lt_of_logX hX0 hX
    have h1 : Real.exp (10 ^ 8) ≤ X₀ := by
      rw [← Real.exp_log (by linarith : 0 < X₀)]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  hH1 := InitialRange.one_le_capH hX0 hX le_rfl
  hHsmall := by
    have hX1 := QueueMono.one_lt_of_logX hX0 hX
    have hx0 : 0 < X₀ := by linarith
    have hH := InitialRange.capH_le_rpow hX0 hX le_rfl
    have hbig : 6561 ≤ X₀ := by
      have h1 : Real.exp (10 ^ 8) ≤ X₀ := by
        rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hX
      have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
      linarith
    set w := X₀ ^ (1 / 8 : ℝ) with hw
    have hw8 : w ^ 8 = X₀ := by
      rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hw0 : 0 ≤ w := Real.rpow_nonneg hx0.le _
    have hw3 : 3 ≤ w := by
      by_contra hc; push_neg at hc
      have : w ^ 8 < 3 ^ 8 := by gcongr
      norm_num at this; linarith
    have h7 : (2187 : ℝ) ≤ w ^ 7 := by
      have : (3 : ℝ) ^ 7 ≤ w ^ 7 := by gcongr
      norm_num at this; linarith
    have : w * 2000 ≤ w ^ 8 := by
      have e : w ^ 8 = w * w ^ 7 := by ring
      rw [e]; nlinarith
    linarith
  hanti := capH_div_antitoneOn hX0 hX

end BModel
