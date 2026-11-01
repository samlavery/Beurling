module

public import RequestProject.Beurling.Noise.BSRedStep

/-!
# Theorem 5.6 (Beurling–Saias upper bound) and Lemma 5.8 (BS-profile), from `Σ ≥ 0`

For a discrete Beurling system `P` satisfying (HBS) on `[1, Z]`, Lemma 5.3 on `[1, Z]` and its
small-height bound (`P.Lemma53 Z`, `P.SmallHeights Z`), and for `τ = log t ≥ 10⁸` such that
`Σ(ℓ, u) ≥ 0` on the whole range `ℓ > 30τ`, `0 ≤ u ≤ U(ℓ)` (`BSaias.SigmaNonneg τ`):

* `BeurlingSystem.bs_claim` : (bs-claim) `max(1, ℓ/τ) W_t(e^ℓ; e^{ℓ/u}) ≤ G(ℓ, u)` for `ℓ ≥ τ`,
  `0 ≤ u ≤ U(ℓ)`, `2e^ℓ ≤ Z` (by induction on `ℓ` in steps of `log 2`; Step 4 is the base
  region `τ ≤ ℓ ≤ 30τ`, Steps 5–6 the induction step `bs_step`);
* `BeurlingSystem.lemma_5_8_of` : **Lemma 5.8** `W_t(e^ℓ; e^{ℓ/u}) ≤ (τ/ℓ) Φ_∞ ρ(u-1) e^{Q(ℓ,u)}`;
* `BeurlingSystem.theorem_5_6_of` : **Theorem 5.6** `W_t(Y) ≤ C_BS log t/log Y` for `t ≤ Y`,
  `2Y ≤ Z`, with `C_BS = Φ_∞ ≤ 38.3` (`BSaias.PhiInf_le`).

The analytic input `Σ ≥ 0` is a statement about Dickman's function only (`BSaias.Sigma`).
-/

@[expose] public section

open Real Set Finset BSaias

namespace BeurlingSystem

variable (P : BeurlingSystem)

lemma Wsm_nonneg (t Y u : ℝ) : 0 ≤ P.Wsm t Y u := by
  unfold Wsm; exact Finset.sum_nonneg fun e _ => div_nonneg zero_le_one (P.val_pos e).le

open scoped Classical in
lemma Wsm_le_vSmooth {t ℓ u : ℝ} (hu : 0 < u) :
    P.Wsm t (Real.exp ℓ) u ≤ P.vSmooth (Real.exp ℓ) (Real.exp (ℓ / u)) := by
  unfold Wsm vSmooth
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter, mem_elems, Real.log_exp] at he ⊢
    refine ⟨he.1, he.2.1, fun j hj => ?_⟩
    have h1 := he.2.2.2 j hj
    have hp := P.p_pos j
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by rw [le_div_iff₀ hu]; linarith)
  · intro e _ _; exact div_nonneg zero_le_one (P.val_pos e).le

open scoped Classical in
lemma Wsm_le_harmBlock (t Y u : ℝ) : P.Wsm t Y u ≤ P.harmBlock Y := by
  unfold Wsm harmBlock
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.1⟩
  · intro e _ _; exact div_nonneg zero_le_one (P.val_pos e).le

/-- **Step 4: the base region** `τ ≤ ℓ ≤ 30τ`. -/
theorem bs_base {Z : ℝ} (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) {t ℓ u : ℝ}
    (hτ : 100000000 ≤ Real.log t) (h1 : Real.log t ≤ ℓ) (h2 : ℓ ≤ 30 * Real.log t)
    (hu0 : 0 ≤ u) (huU : u ≤ Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    ℓ / Real.log t * P.Wsm t (Real.exp ℓ) u ≤ Gf (Real.log t) ℓ u := by
  set τ := Real.log t
  have hτ0 : 0 < τ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hphi := base_phi hτ0 h1 h2
  have hlτ : 0 ≤ ℓ / τ := by positivity
  have hA0 : 0 ≤ BSCert.Z2.A ℓ u := by
    unfold BSCert.Z2.A
    have : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    positivity
  have haQ : 0 ≤ aQ ℓ u := by unfold aQ; positivity
  rcases lt_or_ge u 1 with hu1 | hu1
  · -- `u < 1`: the trivial bound
    have hY : 72 ≤ Real.exp ℓ := by
      have := Real.add_one_le_exp ℓ; linarith
    have hW := (P.Wsm_le_harmBlock t (Real.exp ℓ) u).trans (hsm _ hY hZ)
    have hrho : Dickman.rho (u - 1) = 1 := Dickman.rho_of_le_one (by linarith)
    have hQ : 1 ≤ Real.exp (Qf ℓ u) := Real.one_le_exp (by unfold Qf; linarith)
    unfold Gf
    rw [hrho, mul_one]
    calc ℓ / τ * P.Wsm t (Real.exp ℓ) u ≤ ℓ / τ * C0 := mul_le_mul_of_nonneg_left hW hlτ
      _ ≤ Phi τ ℓ := hphi
      _ ≤ Phi τ ℓ * Real.exp (Qf ℓ u) := le_mul_of_one_le_right (Phi_pos τ ℓ).le hQ
  · -- `1 ≤ u`: Lemma 5.3
    have hu0' : 0 < u := by linarith
    obtain ⟨h100, hule⟩ := base_lemma53 hτ h1 h2 hu1 huU
    have hlogz : Real.log (Real.exp (ℓ / u)) = ℓ / u := Real.log_exp _
    have hul : u * (ℓ / u) = ℓ := by field_simp
    have h53' := h53 (Real.exp (ℓ / u)) u (by rw [hlogz]; exact h100) hu1
      (by rw [hlogz]; exact hule) (by rw [hlogz, hul]; exact hZ)
    rw [hlogz, hul] at h53'
    have hW := (P.Wsm_le_vSmooth (t := t) (ℓ := ℓ) hu0').trans h53'
    have hrho : Dickman.rho u ≤ Dickman.rho (u - 1) := Dickman.rho_antitone (by linarith)
    have haV : aV ℓ u ≤ Qf ℓ u := by
      unfold aV Qf BSCert.Z2.A
      have hlog : Real.log (u + 2) = Real.log (2 + u) := by ring_nf
      rw [hlog]
      have hl : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
      have : 4 * 3.2 * u ^ 2 * Real.log (2 + u) ≤ 11 * (1 + u) ^ 3 * Real.log (2 + u) := by
        apply mul_le_mul_of_nonneg_right _ hl
        nlinarith [sq_nonneg u]
      have := div_le_div_of_nonneg_right this hℓ0.le
      linarith
    have hC0 : (0 : ℝ) ≤ C0 := by unfold C0; norm_num
    unfold Gf
    calc ℓ / τ * P.Wsm t (Real.exp ℓ) u
        ≤ ℓ / τ * (C0 * Dickman.rho u * Real.exp (aV ℓ u)) := mul_le_mul_of_nonneg_left hW hlτ
      _ = (ℓ / τ * C0) * Dickman.rho u * Real.exp (aV ℓ u) := by ring
      _ ≤ Phi τ ℓ * Dickman.rho (u - 1) * Real.exp (Qf ℓ u) := by
        have := Dickman.rho_pos u
        have := Phi_pos τ ℓ
        have := Dickman.rho_pos (u - 1)
        gcongr

/-- **(bs-claim)**: for `ℓ ≥ τ`, `0 ≤ u ≤ U(ℓ)` and `2e^ℓ ≤ Z`,
`(ℓ/τ) W_t(e^ℓ; e^{ℓ/u}) ≤ G(ℓ, u)` (here `max(1, ℓ/τ) = ℓ/τ`). -/
theorem bs_claim {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) {t : ℝ} (ht : 0 < t)
    (hτ : 100000000 ≤ Real.log t) (hSig : SigmaNonneg (Real.log t)) {ℓ u : ℝ}
    (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u) (hu : u ≤ Uf (Real.log t) ℓ)
    (hZ : 2 * Real.exp ℓ ≤ Z) :
    ℓ / Real.log t * P.Wsm t (Real.exp ℓ) u ≤ Gf (Real.log t) ℓ u := by
  set τ := Real.log t
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have key : ∀ n : ℕ, ∀ ℓ u, τ ≤ ℓ → ℓ ≤ τ + n * Real.log 2 → 0 ≤ u → u ≤ Uf τ ℓ →
      2 * Real.exp ℓ ≤ Z → ℓ / τ * P.Wsm t (Real.exp ℓ) u ≤ Gf τ ℓ u := by
    intro n
    induction n with
    | zero =>
      intro ℓ u h1 h2 hu0 hu hZ
      exact P.bs_base h53 hsm hτ h1 (by push_cast at h2; linarith) hu0 hu hZ
    | succ n ih =>
      intro ℓ u h1 h2 hu0 hu hZ
      rcases le_or_gt ℓ (30 * τ) with hb | hb
      · exact P.bs_base h53 hsm hτ h1 hb hu0 hu hZ
      · refine P.bs_step h h53 ht hτ hb hu0 hu hZ (hSig ℓ u hb hu0 hu) ?_
        intro m w hm1 hm2 hw0 hw hmZ
        exact ih m w hm1 (by push_cast at h2; linarith) hw0 hw hmZ
  obtain ⟨n, hn⟩ := exists_nat_ge ((ℓ - τ) / Real.log 2)
  exact key n ℓ u hℓ (by rw [div_le_iff₀ hl2] at hn; linarith) hu0 hu hZ

/-- **Lemma 5.8 (BS-profile)**: for `τ = log t ≥ 10⁸`, `ℓ ≥ τ`, `0 ≤ u ≤ U(ℓ)`,
`W_t(e^ℓ; e^{ℓ/u}) ≤ (τ/ℓ) Φ_∞ ρ(u-1) e^{Q(ℓ,u)}`, given (HBS) and Lemma 5.3 on `[1, Z]`
(`2e^ℓ ≤ Z`) and `Σ ≥ 0` (Step 7). (`Φ_∞ ≤ 38.3` is `PhiInf_le`, and `Φ_∞` is non-increasing in
`τ`: `PhiInf_antitoneOn`.) -/
theorem lemma_5_8_of {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) {t ℓ u : ℝ} (ht : 0 < t)
    (hτ : 100000000 ≤ Real.log t) (hSig : SigmaNonneg (Real.log t)) (hℓ : Real.log t ≤ ℓ)
    (hu0 : 0 ≤ u) (hu : u ≤ Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤
      Real.log t / ℓ * PhiInf (Real.log t) * Dickman.rho (u - 1) * Real.exp (Qf ℓ u) := by
  have hτ0 : 0 < Real.log t := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hc := P.bs_claim h h53 hsm ht hτ hSig hℓ hu0 hu hZ
  have hG : Gf (Real.log t) ℓ u ≤ PhiInf (Real.log t) * Dickman.rho (u - 1) *
      Real.exp (Qf ℓ u) := by
    unfold Gf
    have := Phi_le_PhiInf hτ0.le hℓ0 (τ := Real.log t)
    have := Dickman.rho_pos (u - 1)
    gcongr
  have := hc.trans hG
  rw [div_mul_eq_mul_div, div_le_iff₀ hτ0] at this
  rw [show Real.log t / ℓ * PhiInf (Real.log t) * Dickman.rho (u - 1) * Real.exp (Qf ℓ u) =
    Real.log t * (PhiInf (Real.log t) * Dickman.rho (u - 1) * Real.exp (Qf ℓ u)) / ℓ by ring,
    le_div_iff₀ hℓ0]
  linarith

/-- **Theorem 5.6 (Beurling–Saias, upper bound)**: for `τ = log t ≥ 10⁸` and `t ≤ Y`,
`2Y ≤ Z`, `W_t(Y) ≤ C_BS log t/log Y` with `C_BS = Φ_∞ ≤ 38.3`, given (HBS) and Lemma 5.3
on `[1, Z]` and `Σ ≥ 0` (Step 7). -/
theorem theorem_5_6_of {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) {t Y : ℝ} (ht : 0 < t)
    (hτ : 100000000 ≤ Real.log t) (hSig : SigmaNonneg (Real.log t)) (htY : t ≤ Y)
    (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ PhiInf (Real.log t) * Real.log t / Real.log Y := by
  have hτ0 : 0 < Real.log t := by linarith
  have hY0 : 0 < Y := by linarith
  have hℓ : Real.log t ≤ Real.log Y := Real.log_le_log ht htY
  have hℓ0 : 0 < Real.log Y := by linarith
  have hYe : Real.exp (Real.log Y) = Y := Real.exp_log hY0
  have hU : (0 : ℝ) ≤ Uf (Real.log t) (Real.log Y) :=
    (u0_nonneg _).trans (u0_le_Uf _ _)
  have hc := P.bs_claim h h53 hsm ht hτ hSig hℓ le_rfl hU (by rw [hYe]; exact hYZ)
  rw [hYe] at hc
  have := hc.trans (Gf_zero_le hτ0.le hℓ0)
  unfold Wt
  rw [div_mul_eq_mul_div, div_le_iff₀ hτ0] at this
  rw [mul_div_assoc, show PhiInf (Real.log t) * (Real.log t / Real.log Y) =
    Real.log t * PhiInf (Real.log t) / Real.log Y by ring, le_div_iff₀ hℓ0]
  linarith

end BeurlingSystem

end
