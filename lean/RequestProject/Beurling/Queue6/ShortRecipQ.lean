module

public import RequestProject.Beurling.Queue6.CountISmall
public import RequestProject.Beurling.Noise.RML9XBBase

/-!
# Lemma 5.29 (reciprocal sums over short intervals) for `P(ω)` on `Good(< t)`

For `1 ≤ M`, `0 < a ≤ 0.01` and `ω ∈ Good(< t) ∩ NiceEv` with `2.1 M + 2X₀ + 10 ≤ t`:

  `∑_{e : M(1-a) ≤ e ≤ M(1+a)} 1/e ≤ 28a + 7M^{-3/4}` (`shortRecip_win`).

It suffices that `#{e ∈ I} ≤ 27.72 aM + 6.93 M^{1/4}`, `I = [α, β]`, `α = M(1-a) - 1/2`,
`β = M(1+a)` (04x-x0band.tex, Lemma 5.29), in three cases:

* `β < X₀⁻`: `N = ⌊·⌋` (`N_high`, `N_low`), `#I ≤ 2aM + 1.6`;
* `α < X₀ ≤ β` or `X₀⁻ ≤ β < X₀`: `N(X₀) ≤ T(X₀) + D(X₀) = X₀ + D(X₀)` (Corollary 3.8), the
  part below `X₀` by `N_low`, the part above by `Ncount_le` (lag at both ends, `T_incr`, and the
  absorbed count by windows of length `X₀^{θ/2}`, Lemma 6.26);
* `X₀ ≤ α`: `Ncount_le` on `[α, β]`.

The lag terms are `≤ 4H + 5 ≤ 4.4 M^{1/8} + 5` (`H(x) ≤ x^{1/8}`), the absorbed count is
`≤ (β - α) + α^{1/4}`.

* `shortRecip_win` : the bound at one `(M, a)`;
* `shortRecip_G0` : **`KR.RML9.ShortRecip (PR θ X₀ ω) Y`** on `Good(< t) ∩ NiceEv` for
  `1.05 Y + 2X₀ + 10 ≤ t`.

The time condition comes from `LC_G0` (Lemma 6.26 through the dyadic cluster event, decided at
the end `2^n X₀/2 ≤ 2x + 2X₀ + 2` of the block of the window): the windows of `ShortRecip P Y`
reach `0.505 Y`, so `Good(< t)` must reach `≈ 1.01 Y`.
-/

@[expose] public section

open Set Real Finset Construction CaplLink QueueMono SlotModel Absorbed

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (D : Sec5Family) (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

omit hc hev in
/-- `P.N x` is the cardinality of `P.elems x`. -/
lemma N_eq_card (P : BeurlingSystem) (x : ℝ) : P.N x = ((P.elems x).card : ℝ) := by
  unfold BeurlingSystem.N
  have : {e : ℕ →₀ ℕ | P.val e ≤ x} = (P.elems x : Set (ℕ →₀ ℕ)) := by
    ext e; simp [BeurlingSystem.mem_elems]
  rw [this, Set.ncard_coe_finset]

omit hc hev in
/-- The final arithmetic of Lemma 5.29: `#S ≤ 27.72 aM + 6.93 M^{1/4}` gives the bound. -/
lemma sr_final {M a c s : ℝ} (hM1 : 1 ≤ M) (ha0 : 0 < a) (ha : a ≤ 0.01)
    (hs : s ≤ c / (M * (1 - a))) (hc : c ≤ 27.72 * a * M + 6.93 * M ^ (1 / 4 : ℝ)) :
    s ≤ 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) := by
  have hM0 : 0 < M := by linarith
  have hMa : 0 < M * (1 - a) := by nlinarith
  have hr34 : M ^ (-(3 / 4 : ℝ)) = M ^ (1 / 4 : ℝ) / M := by
    rw [Real.rpow_neg hM0.le, eq_div_iff hM0.ne']
    have : M ^ (3 / 4 : ℝ) * M ^ (1 / 4 : ℝ) = M := by
      rw [← Real.rpow_add hM0]; norm_num
    have h0 : 0 < M ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hM0 _
    field_simp
    linarith
  have hq0 : 0 ≤ M ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hM0 _).le
  refine hs.trans ?_
  rw [div_le_iff₀ hMa, hr34]
  have e : (28 * a + 7 * (M ^ (1 / 4 : ℝ) / M)) * (M * (1 - a)) =
      (1 - a) * (28 * a * M + 7 * M ^ (1 / 4 : ℝ)) := by field_simp
  rw [e]
  have h1 : 27.72 * a * M + 6.93 * M ^ (1 / 4 : ℝ) ≤
      0.99 * (28 * a * M + 7 * M ^ (1 / 4 : ℝ)) := by nlinarith
  have h2 : 0.99 * (28 * a * M + 7 * M ^ (1 / 4 : ℝ)) ≤
      (1 - a) * (28 * a * M + 7 * M ^ (1 / 4 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right (by linarith); positivity
  linarith

set_option maxHeartbeats 3200000 in
/-- **Lemma 5.29 at one `(M, a)`** on `Good(< t) ∩ NiceEv`, `2.1 M + 2X₀ + 10 ≤ t`. -/
theorem shortRecip_win {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {M a : ℝ} (hM1 : 1 ≤ M) (ha0 : 0 < a) (ha : a ≤ 0.01)
    (ht : 2.1 * M + 2 * X₀ + 10 ≤ t) :
    ∑ e ∈ ((PR θ X₀ ω).elems (M * (1 + a))).filter (fun e => M * (1 - a) ≤ (PR θ X₀ ω).val e),
      1 / (PR θ X₀ ω).val e ≤ 28 * a + 7 * M ^ (-(3 / 4 : ℝ)) := by
  classical
  set P := PR θ X₀ ω
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hXb : (10 : ℝ) ^ 8 ≤ X₀ := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log hX0p]; exact Real.exp_le_exp.mpr hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hX le_rfl
  have hHX0 := capH_nonneg (X₀ : ℝ) X₀
  have hXme : Xm X₀ = X₀ - capH X₀ X₀ / 2 := rfl
  have hθ := hc.hθ
  have hθ4 : θ / 2 ≤ 1 / 4 := by linarith [hθ.2]
  have hθ0 : 0 ≤ θ / 2 := by linarith [hθ.1]
  have hM0 : 0 < M := by linarith
  have haM : 0 ≤ a * M := by positivity
  set β := M * (1 + a) with hβe
  set α := M * (1 - a) - 1 / 2 with hαe
  have hMaβ : M * (1 - a) ≤ β := by rw [hβe]; nlinarith
  have hMa : 0 < M * (1 - a) := by nlinarith
  have hβα : β - α = 2 * (a * M) + 1 / 2 := by rw [hβe, hαe]; ring
  have hβM : β ≤ 1.01 * M := by rw [hβe]; nlinarith
  have hαM : α ≤ M := by rw [hαe]; nlinarith
  have hαM' : 0.99 * M - 1 / 2 ≤ α := by rw [hαe]; nlinarith
  have hβ1 : 1 ≤ β := by rw [hβe]; nlinarith
  set S := (P.elems β).filter (fun e => M * (1 - a) ≤ P.val e) with hSe
  -- `M^{1/4} = r²`
  set r := M ^ (1 / 8 : ℝ) with hre
  have hr0 : 0 < r := Real.rpow_pos_of_pos hM0 _
  have hr2 : M ^ (1 / 4 : ℝ) = r ^ 2 := by
    rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
  have hr1 : 1 ≤ r := Real.one_le_rpow hM1 (by norm_num)
  have hr21 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
  have hsum : ∑ e ∈ S, 1 / P.val e ≤ (S.card : ℝ) / (M * (1 - a)) := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro e he
    exact one_div_le_one_div_of_le hMa (Finset.mem_filter.mp he).2
  refine sr_final hM1 ha0 ha hsum ?_
  rw [hr2]
  -- `#S ≤ N(β) - N(α)` for `α ≥ 1`, and `#S ≤ N(β)`
  have hSβ : (S.card : ℝ) ≤ P.N β := by
    rw [N_eq_card]; exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hSαβ : 1 ≤ α → (S.card : ℝ) ≤ P.N β - P.N α := by
    intro _
    have hsub : S ⊆ P.elems β \ P.elems α := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      rw [Finset.mem_sdiff]
      refine ⟨he1, fun h => ?_⟩
      rw [BeurlingSystem.mem_elems] at h
      linarith
    have hs : P.elems α ⊆ P.elems β := P.elems_mono (by linarith)
    rw [N_eq_card, N_eq_card, ← Nat.cast_sub (Finset.card_le_card hs)]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_sdiff_of_subset hs).le
  rcases lt_or_ge β (Xm X₀) with hβXm | hβXm
  · -- (i) `β < X₀⁻`
    have h1 := N_high hc ω hβ1 hβXm
    rcases lt_or_ge α 1 with hα1 | hα1
    · have : β ≤ 2 * (a * M) + 1.6 := by
        have : M ≤ 1.52 := by rw [hαe] at hα1; nlinarith
        rw [hβe]; nlinarith
      linarith
    · have h2 := N_low hc ω hα1
      have h3 : min α (Xm X₀ - 1 / 2) = α := min_eq_left (by linarith)
      have := hSαβ hα1
      linarith
  -- `β ≥ X₀⁻`, so `M ≥ 0.98 X₀` and `r ≥ 9`
  have hMX : 0.98 * (X₀ : ℝ) ≤ M := by linarith
  have hr8 : r ^ 8 = M := by
    rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
  have hr9 : 9 ≤ r := by
    by_contra h; push_neg at h
    have : r ^ 8 < 9 ^ 8 := pow_lt_pow_left₀ h hr0.le (by norm_num)
    linarith
  have hr2M : r ^ 2 ≤ M / 1000 := by
    have h6 : (1000 : ℝ) ≤ r ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) hr9 6; linarith
    have : r ^ 2 * 1000 ≤ r ^ 2 * r ^ 6 := mul_le_mul_of_nonneg_left h6 (by positivity)
    have e : r ^ 2 * r ^ 6 = r ^ 8 := by ring
    linarith
  -- `H(x) ≤ 1.1 r`, `x^{θ/2} ≤ 1.1 r²` for `x ≤ 1.03 M`
  have h103 : (1.03 : ℝ) ^ (1 / 8 : ℝ) ≤ 1.1 := by
    calc (1.03 : ℝ) ^ (1 / 8 : ℝ) ≤ (1.03 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ 1.1 := by norm_num
  have h103' : (1.03 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.1 := by
    calc (1.03 : ℝ) ^ (1 / 4 : ℝ) ≤ (1.03 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ 1.1 := by norm_num
  have hH : ∀ x : ℝ, (X₀ : ℝ) ≤ x → x ≤ 1.03 * M → capH X₀ x ≤ 1.1 * r := by
    intro x hx1 hx2
    refine (InitialRange.capH_le_rpow hX0 hX hx1).trans ?_
    have h1 : x ^ (1 / 8 : ℝ) ≤ (1.03 * M) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hx2 (by norm_num)
    rw [Real.mul_rpow (by norm_num) hM0.le, ← hre] at h1
    have := mul_le_mul_of_nonneg_right h103 hr0.le
    linarith
  have hpow : ∀ x : ℝ, 1 ≤ x → x ≤ 1.03 * M → x ^ (θ / 2) ≤ 1.1 * r ^ 2 := by
    intro x hx1 hx2
    have h1 : x ^ (θ / 2) ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ4
    have h2 : x ^ (1 / 4 : ℝ) ≤ (1.03 * M) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hx2 (by norm_num)
    rw [Real.mul_rpow (by norm_num) hM0.le, hr2] at h2
    have := mul_le_mul_of_nonneg_right h103' (by positivity : (0 : ℝ) ≤ r ^ 2)
    linarith
  -- the times
  have hlogt : ∀ x : ℝ, (X₀ : ℝ) ≤ x → x ≤ 1.03 * M → x + 26 * Real.log x + 2 < t := by
    intro x hx1 hx2
    have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 1000 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have e : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      rw [e]; nlinarith
    linarith
  have hlag : ∀ x : ℝ, (X₀ : ℝ) ≤ x → x ≤ 1.03 * M →
      |P.N x - (Mcl θ X₀ ω).T x| ≤ 4.4 * r + 5 := by
    intro x hx1 hx2
    have h := lag_G0 D hc hev hG hN hx1 (hlogt x hx1 hx2)
    have h1 := lagD_le hc (x := x) hx1 le_rfl
    have h2 := hH x hx1 hx2
    unfold lagD at h1
    linarith
  -- `Ncount_le` on `[a', d]`
  have hNc : ∀ a' d : ℝ, (X₀ : ℝ) ≤ a' → a' ≤ d → 0.9 * M ≤ a' → d ≤ 1.03 * M →
      d ≤ 1.9 * a' →
      P.N d - P.N a' ≤ 2.50005 * (d - a') + 1 + 1.1 * r ^ 2 + 2 * (4.4 * r + 5) := by
    intro a' d ha' had haM hdM hd2
    have ha'0 : 0 < a' := by linarith
    have hh := hpow a' (by linarith) (by linarith)
    have hh0 : 0 < a' ^ (θ / 2) := Real.rpow_pos_of_pos ha'0 _
    have h := Ncount_le D hc hev hG hN ha' had (hlogt d (by linarith) hdM) (by linarith)
    have hld := lagD_le hc (x := d) (by linarith) le_rfl
    have hla := lagD_le hc (x := a') ha' le_rfl
    have hHd := hH d (by linarith) hdM
    have hHa := hH a' ha' (by linarith)
    have hL : (10 : ℝ) ^ 8 ≤ Real.log a' := (logs_of_ge hX0 hX ha').1
    have hL4 : Real.log a' ^ (-4 : ℤ) ≤ 1 / 4 := by
      rw [zpow_neg, zpow_ofNat, one_div]
      apply inv_anti₀ (by norm_num)
      have := pow_le_pow_left₀ (by norm_num) hL 4
      have : (4 : ℝ) ≤ (10 ^ 8) ^ 4 := by norm_num
      linarith
    have hL40 : 0 ≤ Real.log a' ^ (-4 : ℤ) := zpow_nonneg (by linarith) _
    have hdh : (d + a' ^ (θ / 2)) ^ (θ / 2) ≤ 2 * a' ^ (θ / 2) := by
      have h1 : d + a' ^ (θ / 2) ≤ 2 * a' := by linarith
      calc (d + a' ^ (θ / 2)) ^ (θ / 2) ≤ (2 * a') ^ (θ / 2) :=
            Real.rpow_le_rpow (by linarith) h1 hθ0
        _ = 2 ^ (θ / 2) * a' ^ (θ / 2) := Real.mul_rpow (by norm_num) ha'0.le
        _ ≤ 2 * a' ^ (θ / 2) := by
            gcongr
            calc (2 : ℝ) ^ (θ / 2) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
    have hq0 : 0 ≤ (d - a') / a' ^ (θ / 2) + 2 := by
      have : 0 ≤ (d - a') / a' ^ (θ / 2) := div_nonneg (by linarith) hh0.le
      linarith
    have habs : ((d - a') / a' ^ (θ / 2) + 2) *
        ((d + a' ^ (θ / 2)) ^ (θ / 2) * Real.log a' ^ (-4 : ℤ)) ≤
          (d - a') / 2 + 1.1 * r ^ 2 := by
      calc ((d - a') / a' ^ (θ / 2) + 2) *
            ((d + a' ^ (θ / 2)) ^ (θ / 2) * Real.log a' ^ (-4 : ℤ))
          ≤ ((d - a') / a' ^ (θ / 2) + 2) * (2 * a' ^ (θ / 2) * (1 / 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hdh hL4 hL40 (by positivity)) hq0
        _ = (d - a') / 2 + a' ^ (θ / 2) := by field_simp; ring
        _ ≤ (d - a') / 2 + 1.1 * r ^ 2 := by linarith
    unfold lagD at hld hla h
    linarith
  have hT0 : (Mcl θ X₀ ω).T X₀ = X₀ := by rw [Mcl_eq hc]; exact (hc.std ω).limModel_T_X₀
  have hα1 : 1 ≤ α := by linarith
  have hSc := hSαβ hα1
  have key : 1.1 * r ^ 2 + 14.3 * r + 19 ≤ 6.93 * r ^ 2 := by nlinarith
  have hHX' : capH X₀ X₀ ≤ 1.1 * r := hH X₀ le_rfl (by linarith)
  rcases lt_or_ge α (X₀ : ℝ) with hαX | hαX
  · -- (ii) `α < X₀`
    have hMX2 : M ≤ 1.02 * X₀ := by linarith
    set βs := max β (X₀ : ℝ) with hβs
    have hβs1 : (X₀ : ℝ) ≤ βs := le_max_right _ _
    have hXM : (X₀ : ℝ) ≤ 1.03 * M := by linarith
    have hβs2 : βs ≤ 1.03 * M := max_le (by linarith) hXM
    have hNβ : P.N β ≤ P.N βs := BeurlingSystem.N_mono _ (le_max_left _ _)
    have hc1 := hNc X₀ βs le_rfl hβs1 (by linarith) hβs2
      (max_le (by linarith) (by linarith))
    have hlX := (abs_le.mp (hlag X₀ le_rfl hXM)).2
    rw [hT0] at hlX
    have h2 := N_low hc ω hα1
    have h3 : α - capH X₀ X₀ / 2 - 3 / 2 ≤ min α (Xm X₀ - 1 / 2) - 1 := by
      rcases le_total α (Xm X₀ - 1 / 2) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h, hXme]; linarith
    have hgeo : 2.50005 * (βs - X₀) + (X₀ - α) ≤ 2.50005 * (β - α) + capH X₀ X₀ / 2 := by
      rcases le_total β (X₀ : ℝ) with h | h
      · rw [hβs, max_eq_right h]; linarith
      · rw [hβs, max_eq_left h]; linarith
    linarith
  · -- (iii) `X₀ ≤ α`
    have hc1 := hNc α β hαX (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

/-- **Lemma 5.29 for `P(ω)`**: `KR.RML9.ShortRecip (PR θ X₀ ω) Y` on `Good(< t) ∩ NiceEv` for
`1.05 Y + 2X₀ + 10 ≤ t`. -/
theorem shortRecip_G0 {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {Y : ℝ} (hY : 1.05 * Y + 2 * X₀ + 10 ≤ t) : KR.RML9.ShortRecip (PR θ X₀ ω) Y := by
  intro M a hM1 hMY ha0 ha
  exact shortRecip_win D hc hev hG hN hM1 ha0 ha (by linarith)

/-- **Lemma 5.29 at the values read by Proposition 5.31(iii)** (`RML9XBGamma`,
`RML9XBGamma2`: `M = u/X₀⁻` or `u/X₀`, `u ≤ Y/2`, so `M ≤ Y/X₀`): the statement of
`KR.RML9.ShortRecip P Y` restricted to `M ≤ Y/X₀`. -/
def ShortRecipLow (P : BeurlingSystem) (X₀ : ℕ) (Y : ℝ) : Prop :=
  ∀ M a : ℝ, 1 ≤ M → M ≤ Y / X₀ → 0 < a → a ≤ 0.01 →
    ∑ e ∈ (P.elems (M * (1 + a))).filter (fun e => M * (1 - a) ≤ P.val e), 1 / P.val e ≤
      28 * a + 7 * M ^ (-(3 / 4 : ℝ))

/-- **`ShortRecipLow` on `Good(< t) ∩ NiceEv`** for `2.1 Y/X₀ + 2X₀ + 10 ≤ t`; at a window
height `s ≤ 1.1 b` of a range-(B) start this holds on `Good(< b)` (`shortRecipLow_b`). -/
theorem shortRecipLow_G0 {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {Y : ℝ} (hY : 2.1 * (Y / X₀) + 2 * X₀ + 10 ≤ t) : ShortRecipLow (PR θ X₀ ω) X₀ Y := by
  intro M a hM1 hMY ha0 ha
  exact shortRecip_win D hc hev hG hN hM1 ha0 ha (by nlinarith)

/-- **`ShortRecipLow` at the window heights on `Good(< t)`, `b ≤ t`**: for `s ≤ 1.1 b` and
`X₀² ≤ b`. -/
theorem shortRecipLow_b {t : ℕ} {ω : JitterΩ} (hG : ω ∈ G0 θ X₀ D t) (hN : ω ∈ NiceEv θ X₀)
    {b s : ℝ} (hbt : b ≤ t) (hb : (X₀ : ℝ) ^ 2 ≤ b) (hs : s ≤ 1.1 * b) :
    ShortRecipLow (PR θ X₀ ω) X₀ s := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hXb : (10 : ℝ) ^ 8 ≤ X₀ := by
    have h1 : Real.exp (10 ^ 8) ≤ (X₀ : ℝ) := by
      rw [← Real.exp_log (show (0 : ℝ) < X₀ by linarith)]; exact Real.exp_le_exp.mpr hc.hX
    have h2 := Real.add_one_le_exp (10 ^ 8 : ℝ)
    linarith
  refine shortRecipLow_G0 D hc hev hG hN ?_
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have h1 : 2.1 * (s / X₀) ≤ 2.31 * b / X₀ := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by linarith) hX0p.le
  have h2 : 2.31 * b / X₀ ≤ b / 1000 := by
    rw [div_le_div_iff₀ hX0p (by norm_num)]; nlinarith
  have h3 : 2 * (X₀ : ℝ) + 10 ≤ b / 2 := by nlinarith
  linarith

end Queue6

end
