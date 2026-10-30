module

public import RequestProject.Beurling.Noise.KRHordMain
public import RequestProject.Beurling.Noise.KRTransRep

/-!
# Theorem 5.15 and Corollary 5.17 for a shifted start

The chains from a source near the nominal landing point `y = x/n'` are kernels started at a
point `v` (with `v ≥ 0.85 y`), whose filters are frozen at the nominal values of the start `y`
(`kSh`, `kSh_kapN`). This file proves for them what Theorem 5.15 and Corollary 5.17(a), (b)
prove for the nominal kernels:

* `radiusCond_gen`, `widthCond_gen` : the conditions of Theorem 5.15 for filters vanishing
  unless the landing point is `≥ 0.6 X₀⁻` (the proofs of `radiusCond_nominal`,
  `widthCond_nominal`, with `PaperWidth.near'`);
* `level_bound_sh`, `cor_5_17_a_sh`, `cor_5_17_b_sh` : the per-level bound and Corollary
  5.17(a), (b) with `C_N` for `kS v y = kerV v (nomFilter y)`, with the masses and the windows
  of the start `y`.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable {val : ℕ → ℝ} {x : ℝ} {H : ℝ → ℝ}

/-- `PaperWidth.near` for landing points `p ≥ 0.6 X₀⁻`. -/
lemma PaperWidth.near' {X0m ε θ : ℝ} (hP : PaperWidth H X0m ε θ) {p y : ℝ}
    (hp : 0.6 * X0m ≤ p) (hy : |y - p| ≤ 0.5106 * H p) :
    X0m / 2 < y ∧ |H y - H p| ≤ θ * (0.5106 * H p) := by
  have hX := hP.X0m_pos
  have hs := hP.small p (by linarith)
  have hHp := hP.reg.pos p
  have hy' := abs_le.mp hy
  have hy2 : X0m / 2 < y := by nlinarith [hy'.1]
  refine ⟨hy2, ?_⟩
  calc |H y - H p| ≤ θ * |y - p| := hP.lip y p hy2.le (by linarith)
    _ ≤ θ * (0.5106 * H p) := mul_le_mul_of_nonneg_left hy hP.theta_nonneg

variable {tw : ℕ → ℝ} {X0m : ℝ}

/-- The radius condition (`ρ = 1.02`) for filters vanishing unless `x/n ≥ 0.6 X₀⁻`. -/
theorem radiusCond_gen {ε θ : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) {κ : ℕ → ℕ → ℝ}
    (hκ0 : ∀ d n, κ d n ≠ 0 → 0.6 * X0m ≤ posn val x n) :
    RadiusCond val x H κ 1.02 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  intro n hn d hd hk y hy
  have hn0 : n ≠ 0 := by omega
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hpn := hκ0 d n hk
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hX := hP.X0m_pos
  unfold Hlev at *
  rw [posn_mul hval hdn hn0] at hy ⊢
  have hst := hP.step_le (v := posn val x n) (by linarith) hw
  have hHn := hP.reg.pos (posn val x n)
  have hr : 1.02 * H (posn val x n * LemmaM.valN val (n / d)) / LemmaM.valN val (n / d) ≤
      0.5106 * H (posn val x n) := by
    rw [mul_div_assoc]; nlinarith
  obtain ⟨-, hlip⟩ := hP.near' hpn (hy.trans hr)
  have := (abs_le.mp hlip).2
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  nlinarith

/-- The width condition (`ρ = 1.02`) for filters vanishing unless `x/n ≥ 0.6 X₀⁻`. -/
theorem widthCond_gen {ε θ lam0 : ℝ} (hP : PaperWidth H X0m ε θ)
    (hval2 : ∀ p, p.Prime → 2 ≤ val p) (hlam : 1 + 2 * θ ≤ lam0) {κ : ℕ → ℕ → ℝ}
    (hκ0 : ∀ d n, κ d n ≠ 0 → 0.6 * X0m ≤ posn val x n) :
    WidthCond val x H κ 1.02 lam0 := by
  have hval : ∀ p, p.Prime → 1 ≤ val p := fun p hp => by linarith [hval2 p hp]
  intro n hn d hd hk v hv
  have hn0 : n ≠ 0 := by omega
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hpn := hκ0 d n hk
  have hw := two_le_valN hval2 (two_le_div_of_mem hd)
  have hw0 : 0 < LemmaM.valN val (n / d) := by linarith
  have hX := hP.X0m_pos
  unfold Hlev at *
  rw [posn_mul hval hdn hn0] at hv
  set w := LemmaM.valN val (n / d)
  set p := posn val x n
  have hst := hP.step_le (v := p) (by linarith) hw
  have hHn := hP.reg.pos p
  have hy : |v / w - p| ≤ 0.5106 * H p := by
    have h3 : 1.02 * H (p * w) ≤ 0.5106 * H p * w := by
      have := (div_le_iff₀ hw0).mp hst; nlinarith
    have h4 : |v - p * w| ≤ 0.5106 * H p * w := hv.trans h3
    have e : v / w - p = (v - p * w) / w := by field_simp
    rw [e, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    exact h4
  obtain ⟨hy2, hlip⟩ := hP.near' hpn hy
  have hd' : |deriv H (v / w)| ≤ θ := by
    have hlo : LipschitzOnWith ⟨θ, hP.theta_nonneg⟩ H (Ioi (X0m / 2)) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      simp only [Real.dist_eq, NNReal.coe_mk]
      exact hP.lip a b (le_of_lt ha) (le_of_lt hb)
    have := norm_deriv_le_of_lipschitzOn (Ioi_mem_nhds hy2) hlo
    rw [Real.norm_eq_abs] at this
    exact this
  have hHy := hP.reg.pos (v / w)
  have hlow := (abs_le.mp hlip).1
  have hθ := hP.theta_le
  have hθ0 := hP.theta_nonneg
  rw [div_le_div_iff₀ hHy hHn]
  have h1 : (2 + |deriv H (v / w)|) * H p ≤ (2 + θ) * H p := by nlinarith
  have h2 : (2 + θ) * H p ≤ 2 * lam0 * H (v / w) := by
    have e1 : 0 ≤ (lam0 - (1 + 2 * θ)) * H (v / w) :=
      mul_nonneg (by linarith) hHy.le
    have e2 : 0 ≤ (H (v / w) - H p + θ * (0.5106 * H p)) * (1 + 2 * θ) :=
      mul_nonneg (by linarith) (by linarith)
    have e3 : 0 ≤ θ * (1 / 100 - θ) * H p :=
      mul_nonneg (mul_nonneg hθ0 (by linarith)) hHn.le
    nlinarith
  linarith


/-! ## The shifted kernels -/

variable (P : BeurlingSystem)

/-- The kernel started at `v` with the nominal filters of the start `y`. -/
noncomputable abbrev kS (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m v y : ℝ) (n : ℕ) : ℝ → ℝ :=
  kerV P.labelVal v H (nomFilter P.labelVal y tw X0m) n

/-- `∑_{y/n ∈ [u, 2u)} TV(C^{v,y}_n)/n`. -/
noncomputable def WS (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m v y u : ℝ) : ℝ :=
  ∑ n ∈ NW P y u, (eVariationOn (kS P H tw X0m v y n) univ).toReal / LemmaM.valN P.labelVal n

variable {P}

lemma eVariationOn_zero_fun : eVariationOn (fun _ : ℝ => (0 : ℝ)) univ = 0 := by
  unfold eVariationOn
  simp

/-- The per-level bound for the shifted kernels (Theorem 5.15 and (RH)). -/
lemma level_bound_sh {H : ℝ → ℝ} {X0m ε θ lam0 : ℝ} {tw : ℕ → ℝ} {v y : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (_ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (_hy : X0m ≤ y) (hv : 0.85 * y ≤ v) {n : ℕ} (hn : n ≠ 0) :
    (eVariationOn (kS P H tw X0m v y n) univ).toReal ≤ |cN P tw X0m y n| + 1 / 2 * lam0 *
      ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m y f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * LemmaM.valN P.labelVal (n / f) ^ ε *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hRHS0 : 0 ≤ |cN P tw X0m y n| + 1 / 2 * lam0 *
      ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m y f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * LemmaM.valN P.labelVal (n / f) ^ ε *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) := by
    have : 0 ≤ ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m y f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * LemmaM.valN P.labelVal (n / f) ^ ε *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) :=
      Finset.sum_nonneg fun f _ => by
        have := KR.valN_labelVal_pos P f
        have := KR.valN_labelVal_pos P n
        have := KR.valN_labelVal_pos P (n / f)
        positivity
    positivity
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have : kS P H tw X0m v y 1 = stepF v := kerV_one _ _ _ _
    rw [this, show cN P tw X0m y 1 = 1 from mass_one _]
    have hf : (Nat.divisors 1).filter (fun f => 1 < f ∧ f < 1) = ∅ := by
      ext f; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
    rw [hf, Finset.sum_empty, mul_zero, add_zero, abs_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      ((eVariationOn_stepF_le v).trans ENNReal.ofReal_one.ge)
  have hVn := KR.valN_labelVal_pos P n
  have hκ0 : ∀ d m, nomFilter P.labelVal y tw X0m d m ≠ 0 →
      0.6 * X0m ≤ posn P.labelVal v m := by
    intro d m hk
    have h1 := nomFilter_ne_zero hk
    have hVm := KR.valN_labelVal_pos P m
    unfold posn at h1 ⊢
    have : 0.85 * (y / LemmaM.valN P.labelVal m) ≤ v / LemmaM.valN P.labelVal m := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hv hVm.le
    linarith
  -- below `X₀⁻/2` the shifted kernel vanishes
  by_cases hpos : X0m / 2 ≤ posn P.labelVal v n
  swap
  · push_neg at hpos
    have hz : kS P H tw X0m v y n = fun _ => 0 := by
      funext t
      rw [kS, kerV_eq _ _ _ _ h2]
      rw [Finset.sum_eq_zero fun d _ => ?_, neg_zero]
      have : nomFilter P.labelVal y tw X0m d n = 0 := by
        by_contra hc
        have := hκ0 d n hc
        linarith
      rw [this, zero_mul]
    rw [hz, eVariationOn_zero_fun, ENNReal.toReal_zero]
    exact hRHS0
  obtain ⟨hTV, -⟩ := theorem_5_15 hval hP.reg (abs_nomFilter_le P.labelVal y tw X0m)
    (by norm_num : (1 : ℝ) / 2 ≤ 1.02) (by linarith [hP.theta_nonneg])
    (radiusCond_gen hP hval2 hκ0) (widthCond_gen hP hval2 hlam hκ0) h2 (x := v)
  refine (ENNReal.toReal_le_of_le_ofReal ?_ hTV).trans ?_
  · have := Finset.sum_nonneg (s := n.divisors.filter (fun e => 1 < e ∧ e < n))
      (f := fun e => |mass (nomFilter P.labelVal y tw X0m) e| *
        (Hlev P.labelVal v H e / Hlev P.labelVal v H n) * (BSCert.X0Band.Hord (n / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal n)) fun e _ => by
      have := hP.reg.pos (posn P.labelVal v e)
      have := hP.reg.pos (posn P.labelVal v n)
      have := KR.valN_labelVal_pos P e
      unfold Hlev; positivity
    positivity
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by linarith [hP.theta_nonneg])
  refine Finset.sum_le_sum fun f hf => ?_
  have hfd := (Finset.mem_filter.mp hf)
  have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd.1
  have hHn := hP.reg.pos (posn P.labelVal v n)
  have hw1 : 1 ≤ LemmaM.valN P.labelVal (n / f) := LemmaM.one_le_valN _ hval
  have hRH : Hlev P.labelVal v H f ≤ LemmaM.valN P.labelVal (n / f) ^ ε *
      Hlev P.labelVal v H n := by
    unfold Hlev
    rw [posn_mul hval hfn hn]
    exact hP.RH _ _ hpos hw1
  have hratio : Hlev P.labelVal v H f / Hlev P.labelVal v H n ≤
      LemmaM.valN P.labelVal (n / f) ^ ε := by
    unfold Hlev at hRH ⊢; rw [div_le_iff₀ hHn]; exact hRH
  have h0 : 0 ≤ |mass (nomFilter P.labelVal y tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
      (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) := by
    have := KR.valN_labelVal_pos P f
    positivity
  calc |mass (nomFilter P.labelVal y tw X0m) f| *
        (Hlev P.labelVal v H f / Hlev P.labelVal v H n) * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)
      = (|mass (nomFilter P.labelVal y tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)) *
          (Hlev P.labelVal v H f / Hlev P.labelVal v H n) := by ring
    _ ≤ (|mass (nomFilter P.labelVal y tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)) *
          LemmaM.valN P.labelVal (n / f) ^ ε := mul_le_mul_of_nonneg_left hratio h0
    _ = _ := by ring

/-- **Corollary 5.17(a) for the shifted kernels.** -/
theorem cor_5_17_a_sh {H : ℝ → ℝ} {X0m ε θ lam0 : ℝ} {tw : ℕ → ℝ} {v y u : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) (hv : 0.85 * y ≤ v) (hu : X0m / 2 ≤ u) :
    WS P H tw X0m v y u ≤ P.Wsh tw X0m y u + 1 / 2 * lam0 *
      ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (ε - 2) *
        P.Wsh tw X0m y (u * LemmaM.valN P.labelVal m) := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hu0 : 0 < u := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  set G : ℕ → ℕ → ℝ := fun f m => |cN P tw X0m y f| / V f *
    ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2))
  have hG : ∀ f m, 0 ≤ G f m := fun f m => by
    have := hV f; have := hV m; positivity
  -- per level
  have hlev : ∀ n ∈ NW P y u, (eVariationOn (kS P H tw X0m v y n) univ).toReal / V n ≤
      |cN P tw X0m y n| / V n + 1 / 2 * lam0 *
        ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
    intro n hn
    obtain ⟨hn0, h1, -⟩ := (mem_NW P hu0).mp hn
    have hb := level_bound_sh hP hp2 ht hlam hy hv hn0
    rw [div_le_iff₀ (hV n)]
    refine hb.trans (le_of_eq ?_)
    have hs : ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m y f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * V (n / f) ^ ε * (V f / V n) =
        (∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) * V n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfn : f ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
      have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
      have hf0 := hV f
      have hm0 := hV (n / f)
      simp only [G]
      rw [Real.rpow_sub hm0, Real.rpow_two, hVn]
      field_simp
    rw [hs, add_mul, div_mul_cancel₀ _ (hV n).ne']
    ring
  calc WS P H tw X0m v y u
      ≤ ∑ n ∈ NW P y u, (|cN P tw X0m y n| / V n + 1 / 2 * lam0 *
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) :=
        Finset.sum_le_sum hlev
    _ = P.Wsh tw X0m y u + 1 / 2 * lam0 * ∑ n ∈ NW P y u,
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Wsh_eq]
    _ ≤ P.Wsh tw X0m y u + 1 / 2 * lam0 *
          ∑ m ∈ MS P y u, ∑ f ∈ NW P y (u * V m), G f m := by
        gcongr
        refine sum_divisors_le G hG fun n hn f hf => ?_
        obtain ⟨hn0, h1, h2⟩ := (mem_NW P hu0).mp hn
        obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
        have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
        have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
        have hm2 : 2 ≤ n / f := by
          obtain ⟨k, hk⟩ := hfn
          have hf0 : 0 < f := by omega
          rw [hk, Nat.mul_div_cancel_left k hf0]
          by_contra hc; push_neg at hc
          interval_cases k <;> simp_all
        have hm0 : n / f ≠ 0 := by omega
        have hf0 : f ≠ 0 := by omega
        have hVm := hV (n / f)
        have hVf := hV f
        constructor
        · refine Finset.mem_filter.mpr ⟨KR.mem_image_iota P hm0 ?_, hm2⟩
          have : V (n / f) ≤ V n := LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0
          have h1' : V n ≤ y / u := by
            rw [le_div_iff₀ hu0]; rw [le_div_iff₀ (hV n)] at h1; linarith
          linarith
        · rw [mem_NW P (by positivity)]
          refine ⟨hf0, ?_, ?_⟩
          · have e : y / V f = y / V n * V (n / f) := by rw [hVn]; field_simp
            rw [e]; exact mul_le_mul_of_nonneg_right h1 hVm.le
          · have e : y / V f = y / V n * V (n / f) := by rw [hVn]; field_simp
            rw [e]; nlinarith
    _ = P.Wsh tw X0m y u + 1 / 2 * lam0 *
          ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
            P.Wsh tw X0m y (u * V m) := by
        congr 2
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Wsh_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [G]; ring


/-- **Corollary 5.17(b) for the shifted kernels.** -/
theorem cor_5_17_b_sh {H : ℝ → ℝ} {X0m ε θ lam0 CS A0 A1 : ℝ} {tw : ℕ → ℝ} {v y u : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) (hv : 0.85 * y ≤ v) (hy1 : 1 < y)
    (hu : X0m / 2 ≤ u)
    (huy : u ≤ y) (hCS : 0 ≤ CS) (hS : SaiasAt P tw X0m y CS) (hA : HordSumsB P ε A0 A1 (y / u))
    (hu1 : 1 / 2 ≤ u) :
    WS P H tw X0m v y u ≤
      CS * ((1 + 1 / 2 * lam0 * A0) * Real.log (2 * u) + 1 / 2 * lam0 * A1) / Real.log y := by
  have hX := hP.X0m_pos
  have hu0 : 0 < u := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hl2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  have ha := cor_5_17_a_sh hP hp2 ht hlam hy hv hu (P := P) (tw := tw) (u := u)
  have hMS : ∀ m ∈ MS P y u, 2 ≤ m := fun m hm => (Finset.mem_filter.mp hm).2
  have hMSB : ∀ m ∈ MS P y u, 2 ≤ m ∧ V m ≤ y / u := by
    intro m hm
    refine ⟨hMS m hm, ?_⟩
    obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    simp only [V]; rw [P.valN_iota]; exact P.mem_elems.mp he
  obtain ⟨hA0, hA1⟩ := hA (MS P y u) hMSB
  have hterm : ∀ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
      P.Wsh tw X0m y (u * V m) ≤ CS / Real.log y * ((BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) * Real.log (2 * u) + (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
          Real.log (V m)) := by
    intro m hm
    obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    have hVe : V (iota e) ≤ y / u := by
      simp only [V]; rw [P.valN_iota]; exact (P.mem_elems.mp he)
    have hV1 : 1 ≤ V (iota e) := LemmaM.one_le_valN _ fun r _ => P.one_le_labelVal r
    have hv1 : X0m / 2 ≤ u * V (iota e) := by nlinarith
    have hv2 : u * V (iota e) ≤ y := by rw [le_div_iff₀ hu0] at hVe; linarith
    have hw := hS _ hv1 hv2
    have hc0 : 0 ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) := by
      have := hV (iota e); positivity
    have e2 : Real.log (2 * (u * V (iota e))) = Real.log (2 * u) + Real.log (V (iota e)) := by
      rw [← mul_assoc, Real.log_mul (by positivity) (hV _).ne']
    calc (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          P.Wsh tw X0m y (u * V (iota e))
        ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          (CS * Real.log (2 * (u * V (iota e))) / Real.log y) :=
          mul_le_mul_of_nonneg_left hw hc0
      _ = _ := by rw [e2]; field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hW0 := hS u hu huy
  have hB : CS / Real.log y * ((∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) *
      Real.log (2 * u) + ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
        Real.log (V m)) ≤ CS / Real.log y * (A0 * Real.log (2 * u) + A1) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hCS hly.le)
    have := mul_le_mul_of_nonneg_right hA0 hl2u
    linarith
  calc WS P H tw X0m v y u
      ≤ P.Wsh tw X0m y u + 1 / 2 * lam0 * ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) *
          V m ^ (ε - 2) * P.Wsh tw X0m y (u * V m) := ha
    _ ≤ CS * Real.log (2 * u) / Real.log y + 1 / 2 * lam0 *
          (CS / Real.log y * (A0 * Real.log (2 * u) + A1)) := by
        gcongr
        exact hsum.trans hB
    _ = _ := by field_simp; ring

end KR

end
