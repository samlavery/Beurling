module

public import RequestProject.Beurling.Noise.BSL57PA
public import RequestProject.Beurling.Noise.BSL57PB
public import RequestProject.Beurling.Noise.BSL57PD
public import RequestProject.Beurling.Noise.BSL57PE
public import RequestProject.Beurling.Noise.BSL57RMain
public import RequestProject.Beurling.Noise.BSAssembly

/-!
# §5.4 without residual hypotheses

* `BSaias.regionLarge` : **Step 7(ii) of the proof of Theorem 5.6** (`Σ(ℓ,u) ≥ 0` for
  `ℓ ≥ 10¹⁸`), from the remainders (a)–(f) of Lemma 5.7 (`remA`, `remB`, `remC`, `remD`,
  `remE`, `remF`), now all proved;
* `BSaias.sigmaNonneg_all` : (bs-Sigma) on the whole induction range;
* `BeurlingSystem.theorem_5_6_hbs_full`, `lemma_5_8_full`, `cor_5_9_full` : Theorem 5.6,
  Lemma 5.8 and Corollary 5.9 for a Beurling system satisfying (HBS) on `[1, Z]`, with no
  further hypothesis.
-/

@[expose] public section

namespace BSaias

/-- **Step 7(ii) of the proof of Theorem 5.6.** -/
theorem regionLarge : RegionLarge :=
  Large.regionLarge_of_ABDE Large.remA Large.remB Large.remD Large.remE

/-- **(bs-Sigma)**: `Σ(ℓ, u) ≥ 0` for `ℓ > 30τ`, `0 ≤ u ≤ U(ℓ)`, `τ ≥ 10⁸`. -/
theorem sigmaNonneg_all {τ : ℝ} (hτ : 100000000 ≤ τ) : SigmaNonneg τ :=
  sigmaNonneg_of_large regionLarge hτ

end BSaias

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- **Theorem 5.6 (Beurling–Saias, upper bound)** for a Beurling system satisfying (HBS) on
`[1, Z]`: for `t > 0` with `τ = log t ≥ 10⁸`, `t ≤ Y` and `2Y ≤ Z`,
`W_t(Y) ≤ C_BS log t/log Y`, `C_BS = Φ_∞(τ) ≤ 38.3` (`BSaias.PhiInf_le`). -/
theorem theorem_5_6_hbs_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {t Y : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (htY : t ≤ Y) (hYZ : 2 * Y ≤ Z) :
    P.Wt t Y ≤ BSaias.PhiInf (Real.log t) * Real.log t / Real.log Y :=
  P.theorem_5_6_hbs h BSaias.regionLarge ht hτ htY hYZ

/-- **Lemma 5.8 (BS-profile)** for a Beurling system satisfying (HBS) on `[1, Z]`. -/
theorem lemma_5_8_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    {t ℓ u : ℝ} (ht : 0 < t) (hτ : 100000000 ≤ Real.log t) (hℓ : Real.log t ≤ ℓ) (hu0 : 0 ≤ u)
    (hu : u ≤ BSaias.Uf (Real.log t) ℓ) (hZ : 2 * Real.exp ℓ ≤ Z) :
    P.Wsm t (Real.exp ℓ) u ≤ Real.log t / ℓ * BSaias.PhiInf (Real.log t) *
      Dickman.rho (u - 1) * Real.exp (BSaias.Qf ℓ u) :=
  P.lemma_5_8_hbs h BSaias.regionLarge ht hτ hℓ hu0 hu hZ

/-- **Corollary 5.9 (Saias weights at every start)** for a Beurling system satisfying (HBS)
on `[1, Z]`, `log X₀⁻ ≥ 10⁸`: `W^sh_y(v) ≤ C_S log(2v)/log y`, `C_S ≤ 77` (`CS_le`). -/
theorem cor_5_9_full {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m Z η1 η2 ε1)
    (hXm : 100000000 ≤ Real.log X0m) {tw : ℕ → ℝ} (ht : ∀ r, r.Prime → 0 < tw r)
    (htv : ∀ r, r.Prime → P.labelVal r ≤ 2 * tw r)
    {y v : ℝ} (hy : X0m ≤ y) (hv1 : X0m / 2 ≤ v) (hv2 : v ≤ y) (hZ : 2 * y / X0m ≤ Z) :
    P.Wsh tw X0m y v ≤
      max (2.01 * BSaias.PhiInf 100000000) 1.4 * Real.log (2 * v) / Real.log y :=
  P.cor_5_9_hbs h hXm BSaias.regionLarge ht htv hy hv1 hv2 hZ

end BeurlingSystem

end
