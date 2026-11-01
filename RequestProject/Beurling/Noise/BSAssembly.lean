module

public import RequestProject.Beurling.Noise.BSRedMain
public import RequestProject.Beurling.Noise.BSZ2
public import RequestProject.Beurling.Noise.BSZ1
public import RequestProject.Beurling.Noise.Saias59
public import RequestProject.Beurling.Noise.Lemma53Main
public import RequestProject.Beurling.Noise.BSLarge
public import RequestProject.Beurling.Noise.BSLargeEps
public import RequestProject.Beurling.Noise.BSLargeSlack
public import RequestProject.Beurling.Noise.BSL57RMain

/-!
# §5.4 assembled: Theorem 5.6, Lemma 5.8 and Corollary 5.9

* `BSaias.sigmaNonneg_of_large` : (bs-Sigma) `Σ(ℓ, u) ≥ 0` on the whole induction range, from
  region Z1 (`regionZ1`, Step 7(i)), region Z2 (`regionZ2`: `S ≤ Σ` and the certificate
  `z2_certificate_dickman`, Step 7(iii)) and the large-`ℓ` region (`RegionLarge`, Step 7(ii)).
* `BeurlingSystem.theorem_5_6`, `BeurlingSystem.lemma_5_8`, `BeurlingSystem.cor_5_9_of` :
  Theorem 5.6, Lemma 5.8 and Corollary 5.9 for a Beurling system satisfying (HBS) on `[1, Z]`,
  with the hypotheses `P.Lemma53 Z` (Lemma 5.3), `P.SmallHeights Z` (its small-height bound) and
  `RegionLarge`.
-/

@[expose] public section

namespace BSaias

/-- **(bs-Sigma)** on the whole range `ℓ > 30τ`, `0 ≤ u ≤ U(ℓ)`: regions Z1 and Z2 are proved,
the large-`ℓ` region is the hypothesis `RegionLarge`. -/
theorem sigmaNonneg_of_large (hL : RegionLarge) {τ : ℝ} (hτ : 100000000 ≤ τ) :
    SigmaNonneg τ := by
  intro ℓ u hℓ hu0 hu
  rcases lt_or_ge u 2 with h2 | h2
  · exact regionZ1 τ ℓ u hτ hℓ hu0 h2
  rcases lt_or_ge ℓ 1000000000000000000 with h18 | h18
  · exact (regionZ2 hτ hℓ h18.le h2 hu).le
  · exact hL τ ℓ u hτ hℓ h18 h2 hu

/-- **Step 7(ii)** from the main inequality of Lemma 5.7 (`Large.Lemma57Ineq`); the size of
`ε(ℓ)` (`Large.lemma57Eps`), the slack `s_a` (`Large.lemma57Slack`) and the positivity of
`c(u)` are proved. -/
theorem regionLarge_of_ineq (h57 : Large.Lemma57Ineq) : RegionLarge :=
  Large.regionLarge_of_lemma57 h57 Large.lemma57Eps Large.lemma57Slack

/-- (bs-Sigma) on the whole range, with only Lemma 5.7's main inequality assumed. -/
theorem sigmaNonneg (h57 : Large.Lemma57Ineq) {τ : ℝ} (hτ : 100000000 ≤ τ) :
    SigmaNonneg τ :=
  sigmaNonneg_of_large (regionLarge_of_ineq h57) hτ

end BSaias

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- **Theorem 5.6 (Beurling–Saias, upper bound)** for a Beurling system satisfying (HBS) on
`[1, Z]`: for `t > 0` with `τ = log t ≥ 10⁸` and `t ≤ Y`, `2Y ≤ Z`,
`W_t(Y) ≤ C_BS log t/log Y` with `C_BS = Φ_∞(τ) ≤ 38.3` (`BSaias.PhiInf_le`). -/
theorem theorem_5_6 {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) (hL : BSaias.RegionLarge) {t Y : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (htY : t ≤ Y) (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y :=
  P.theorem_5_6_of h h53 hsm ht hτ (BSaias.sigmaNonneg_of_large hL hτ) htY hYZ

/-- **Lemma 5.8 (BS-profile)**: for `τ = log t ≥ 10⁸`, `ℓ ≥ τ`, `0 ≤ u ≤ U(ℓ)` (and
`2e^ℓ ≤ Z`), `W_t(e^ℓ; e^{ℓ/u}) ≤ (τ/ℓ) Φ_∞ ρ(u-1) e^{Q(ℓ,u)}`. -/
theorem lemma_5_8 {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) (hL : BSaias.RegionLarge) {t ℓ u : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤ Real.log t / ℓ * BSaias.PhiInf (Real.log t) *
      Dickman.rho (u - 1) * Real.exp (BSaias.Qf ℓ u) :=
  P.lemma_5_8_of h h53 hsm ht hτ (BSaias.sigmaNonneg_of_large hL hτ) hℓ hu0 hu hZ

theorem thm56_holds {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z) (hL : BSaias.RegionLarge) : P.Thm56 Z :=
  fun _ _ ht hτ htY hYZ => P.theorem_5_6 h h53 hsm hL ht hτ htY hYZ

/-- **Corollary 5.9 (Saias weights at every start)**, with Theorem 5.6 discharged: for every
start `y ≥ X₀⁻` and `X₀⁻/2 ≤ v ≤ y` (with `2y/X₀⁻ ≤ Z`),
`W^sh_y(v) ≤ C_S log(2v)/log y`, `C_S = max(2.01 C_BS, 1.4) ≤ 77`. -/
theorem cor_5_9_of {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (h53 : P.Lemma53 Z) (hsm : P.SmallHeights Z)
    (hL : BSaias.RegionLarge) {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y :=
  P.cor_5_9 h hXm (P.thm56_holds h h53 hsm hL) hsm ht htv hy hv1 hv2 hZ

/-- `C_S = max(2.01 C_BS, 1.4) ≤ 77`. -/
theorem CS_le : max (2.01 * BSaias.PhiInf 100000000) 1.4 ≤ 77 := by
  have := BSaias.PhiInf_le (τ := 100000000) le_rfl
  rw [max_le_iff]; constructor <;> linarith

/-! ## With Lemma 5.3 proved -/

/-- **Theorem 5.6** for a Beurling system satisfying (HBS) on `[1, Z]`, with Lemma 5.3 proved
(`HBS.lemma53`, `HBS.smallHeights`); the only remaining hypothesis is `RegionLarge`. -/
theorem theorem_5_6_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hL : BSaias.RegionLarge) {t Y : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t)
    (htY : t ≤ Y) (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y :=
  P.theorem_5_6 h h.lemma53 h.smallHeights hL ht hτ htY hYZ

/-- **Lemma 5.8** with Lemma 5.3 proved; the only remaining hypothesis is `RegionLarge`. -/
theorem lemma_5_8_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hL : BSaias.RegionLarge) {t ℓ u : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤ Real.log t / ℓ * BSaias.PhiInf (Real.log t) *
      Dickman.rho (u - 1) * Real.exp (BSaias.Qf ℓ u) :=
  P.lemma_5_8 h h.lemma53 h.smallHeights hL ht hτ hℓ hu0 hu hZ

/-- **Corollary 5.9** with Lemma 5.3 proved; the only remaining hypothesis is `RegionLarge`. -/
theorem cor_5_9_hbs {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (hL : BSaias.RegionLarge) {tw : ℕ → ℝ}
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y :=
  P.cor_5_9_of h hXm h.lemma53 h.smallHeights hL ht htv hy hv1 hv2 hZ

/-! ## Final forms: the only hypothesis left is Lemma 5.7's main inequality -/

/-- **Theorem 5.6** under (HBS) on `[1, Z]`; residual hypothesis: `Large.Lemma57Ineq`. -/
theorem theorem_5_6_final {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h57 : BSaias.Large.Lemma57Ineq) {t Y : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t)
    (htY : t ≤ Y) (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y :=
  P.theorem_5_6_hbs h (BSaias.regionLarge_of_ineq h57) ht hτ htY hYZ

/-- **Lemma 5.8** under (HBS); residual hypothesis: `Large.Lemma57Ineq`. -/
theorem lemma_5_8_final {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (h57 : BSaias.Large.Lemma57Ineq) {t ℓ u : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤ Real.log t / ℓ * BSaias.PhiInf (Real.log t) *
      Dickman.rho (u - 1) * Real.exp (BSaias.Qf ℓ u) :=
  P.lemma_5_8_hbs h (BSaias.regionLarge_of_ineq h57) ht hτ hℓ hu0 hu hZ

/-- **Corollary 5.9** under (HBS); residual hypothesis: `Large.Lemma57Ineq`. -/
theorem cor_5_9_final {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (h57 : BSaias.Large.Lemma57Ineq) {tw : ℕ → ℝ}
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y :=
  P.cor_5_9_hbs h hXm (BSaias.regionLarge_of_ineq h57) ht htv hy hv1 hv2 hZ

/-- The residual hypothesis of §5.4: the remainder bounds (a), (b), (d), (e) of the proof of
Lemma 5.7 (04c-saias.tex lines 436–477), each stated as in the paper (`Large.RemA`, `RemB`,
`RemD`, `RemE`); (c), (f), the size of `ε`, the slack, the decomposition and the positivity of
`c(u)` are proved. -/
def Lemma57Residual : Prop :=
  BSaias.Large.RemA ∧ BSaias.Large.RemB ∧ BSaias.Large.RemD ∧ BSaias.Large.RemE

theorem regionLarge_of_residual (hr : Lemma57Residual) : BSaias.RegionLarge :=
  BSaias.Large.regionLarge_of_ABDE hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

/-- **Theorem 5.6** under (HBS) on `[1, Z]`; residual hypothesis `Lemma57Residual`. -/
theorem theorem_5_6_main {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hr : Lemma57Residual) {t Y : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t)
    (htY : t ≤ Y) (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y :=
  P.theorem_5_6_hbs h (regionLarge_of_residual hr) ht hτ htY hYZ

/-- **Lemma 5.8** under (HBS); residual hypothesis `Lemma57Residual`. -/
theorem lemma_5_8_main {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hr : Lemma57Residual) {t ℓ u : ℝ}
    (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤ Real.log t / ℓ * BSaias.PhiInf (Real.log t) *
      Dickman.rho (u - 1) * Real.exp (BSaias.Qf ℓ u) :=
  P.lemma_5_8_hbs h (regionLarge_of_residual hr) ht hτ hℓ hu0 hu hZ

/-- **Corollary 5.9** under (HBS); residual hypothesis `Lemma57Residual`. -/
theorem cor_5_9_main {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) (hr : Lemma57Residual) {tw : ℕ → ℝ}
    (ht : ∀ r, r.Prime → 0 < tw r) (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y :=
  P.cor_5_9_hbs h hXm (regionLarge_of_residual hr) ht htv hy hv1 hv2 hZ

end BeurlingSystem

end
