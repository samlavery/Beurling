module

public import RequestProject.Beurling.GenLemma51Final
public import RequestProject.BSCert.DickmanCert

/-!
# §5.2–5.4: definitions for Lemma 5.3 and Theorem 5.6 (Beurling–Saias)

This file fixes the objects of Lemma 5.3 (smooth elements) and of the proof of Theorem 5.6
(the Beurling–Saias upper bound), for a general discrete Beurling system `P`.

## Sums over the system (§5.2, §5.4)

* `P.harmBlock Y = ∑_{n ∈ 𝒩 ∩ (Y, 2Y]} 1/n`;
* `P.vSmooth Y z = v(log Y, z) = ∑_{n ∈ 𝒩 ∩ (Y, 2Y], P⁺(n) ≤ z} 1/n` (Lemma 5.3);
* `P.IsDense t e`: `e` is squarefree and `t`-dense, i.e. `p_{j+1} ≤ t p_1 ⋯ p_j` for its primes
  `p_1 < ⋯ < p_r` (Theorem 5.6). The primes are ordered by their index, which is a value order
  with ties broken by the index (`P.p` is monotone);
* `P.Wsm t Y u = W_t(Y; Y^{1/u})`, the `t`-dense elements of `(Y, 2Y]` with `u log p ≤ log Y`
  for each prime `p` (for `u = 0` there is no constraint: `W_t(Y)`); this is the sum of
  Lemma 5.8 with the constraint `P⁺(n) ≤ z` (the paper writes `P⁺(n) < z`, see below);
* `P.Wt t Y = W_t(Y)`.

The paper's `W_t(Y; z)` uses `P⁺(n) < z`; we use `P⁺(n) ≤ z`, which only enlarges the sum, so
every upper bound proved for our `W` holds for the paper's.

## The profile and `Σ(ℓ, u)` (Theorem 5.6, Steps 2, 3, 5, 6)

All quantities are real functions of `τ = log t`, `ℓ = log Y`, `u`, and the integration variable
`w`; `ρ` is Dickman's function `Dickman.rho`.

* `u0 ℓ = ℓ^{1/4}` (`BSCert.Z2.u0`), `Uf τ ℓ = U(ℓ) = u₀ + ℓ^{1/4} √(2 log(ℓ/τ) + 4)`;
* `aQ ℓ u = a = (u - u₀)₊²/(2√ℓ)`, `Qf ℓ u = Q = A + a` with `A = BSCert.Z2.A`;
* `kappa τ = κ_Φ = 4τ + 1500`, `PhiInf τ = Φ_∞`, `Phi τ ℓ = Φ(ℓ)`, `Gf τ ℓ u = G(ℓ, u)`;
* `mOf ℓ w = m = ℓw/(1+w)`, `w1 τ ℓ`, `wlo τ ℓ u`, `Dfun = D(w)`, `etaF = η_f(m, w)`;
* `gfun … I w`: `g(w)` with the cut-off `1[w ∈ I]` (the paper's cut-off is `I = {w ≤ U(m)}`,
  `paperCut`);
* `Mterm`, `E1term`, `E2term`, `E3term`, `Tterm` and `SigmaGen … I = 1 - [M + E₁ + E₂ + E₃ + T]`;
  `Sigma τ ℓ u = SigmaGen τ ℓ u paperCut` is `Σ(ℓ, u)` of (bs-Sigma).

Conventions that differ (harmlessly) from the paper's text:

* the integrals over `[w_lo, ∞)` are written over `[w_lo, U(ℓ)]`: the cut-off `1[w ≤ U(m)]`
  vanishes for `w > U(ℓ)`, as `m < ℓ` and `U` is non-decreasing;
* `η_f` is the sum of the absolute values of the components of `∂_m Q` and `∂_w Q` (written out
  explicitly), which majorizes the paper's `κ_Φ/m² + |∂_m Q| + (1+w)²ℓ⁻¹ |∂_w Q|`; so our `E₃` is
  at least the paper's and our `Σ` at most the paper's;
* the tail `T` is the bound of Step 6 before its simplification: the Lemma 5.3 bound
  `(ℓ/τ) C₀ ρ(u*) e^{a_V(u*)}` for the `e^{ℓ/u*}`-smooth part, `u* = U(ℓ) + 1/2`, divided by
  `G(ℓ, u)`.
-/

@[expose] public section

open Real Finset

namespace BSaias

/-! ## Constants -/

/-- `C₀ = 0.70` (Lemma 5.3). -/
noncomputable def C0 : ℝ := 0.70

/-- `K' = 2.20` (Lemma 5.1(iv)). -/
noncomputable def Kp : ℝ := 2.2

/-! ## Lemma 5.3: the exponent `a_V` -/

/-- `a_V = 4K u² log(u+2)/ℓ` with `K = 3.2` (Lemma 5.3). -/
noncomputable def aV (ℓ u : ℝ) : ℝ := 4 * 3.2 * u ^ 2 * Real.log (u + 2) / ℓ

/-! ## The profile of Theorem 5.6 (Step 3) -/

/-- `u₀(ℓ) = ℓ^{1/4}`. -/
noncomputable abbrev u0 (ℓ : ℝ) : ℝ := BSCert.Z2.u0 ℓ

/-- `U(ℓ) = u₀ + ℓ^{1/4} √(2 log(ℓ/τ) + 4)`. -/
noncomputable def Uf (τ ℓ : ℝ) : ℝ := u0 ℓ + u0 ℓ * √(2 * Real.log (ℓ / τ) + 4)

/-- `a(ℓ, u) = (u - u₀)₊²/(2√ℓ)`. -/
noncomputable def aQ (ℓ u : ℝ) : ℝ := (max (u - u0 ℓ) 0) ^ 2 / (2 * √ℓ)

/-- `Q(ℓ, u) = A + a`, `A = B(1+u)³ log(2+u)/ℓ`, `B = 11`. -/
noncomputable def Qf (ℓ u : ℝ) : ℝ := BSCert.Z2.A ℓ u + aQ ℓ u

/-- `κ_Φ = 4τ + 1500`. -/
noncomputable def kappa (τ : ℝ) : ℝ := 4 * τ + 1500

/-- `Φ_∞ = C₀ max(e^{κ_Φ/τ}, 30 e^{κ_Φ/ℓ₁})`, `ℓ₁ = 30τ`. This is `C_BS`. -/
noncomputable def PhiInf (τ : ℝ) : ℝ :=
  C0 * max (Real.exp (kappa τ / τ)) (30 * Real.exp (kappa τ / (30 * τ)))

/-- `Φ(ℓ) = Φ_∞ e^{-κ_Φ/ℓ}`. -/
noncomputable def Phi (τ ℓ : ℝ) : ℝ := PhiInf τ * Real.exp (-(kappa τ / ℓ))

/-- The profile `G(ℓ, u) = Φ(ℓ) ρ(u-1) e^{Q(ℓ,u)}` of (bs-claim). -/
noncomputable def Gf (τ ℓ u : ℝ) : ℝ := Phi τ ℓ * Dickman.rho (u - 1) * Real.exp (Qf ℓ u)

/-! ## The quantities of Step 5 -/

/-- `m = ℓ w/(1+w)` (so that `w = m/σ`, `σ = ℓ - m`). -/
noncomputable def mOf (ℓ w : ℝ) : ℝ := ℓ * w / (1 + w)

/-- `w₁ = (ℓ - τ - log 2)/(ℓ + τ + log 2)`. -/
noncomputable def w1 (τ ℓ : ℝ) : ℝ := (ℓ - τ - Real.log 2) / (ℓ + τ + Real.log 2)

/-- `w_lo = max(u - 1, w₁)`. -/
noncomputable def wlo (τ ℓ u : ℝ) : ℝ := max (u - 1) (w1 τ ℓ)

/-- `D(w) = Q(m, w) - Q(ℓ, u) - κ_Φ/(wℓ)`. -/
noncomputable def Dfun (τ ℓ u w : ℝ) : ℝ := Qf (mOf ℓ w) w - Qf ℓ u - kappa τ / (w * ℓ)

/-- `(w - m^{1/4})₊`. -/
noncomputable def dpos (m w : ℝ) : ℝ := max (w - u0 m) 0

/-- `η_f(m, w)`: the explicit majorant of `|∂_σ log f₂|`, `f₂ = Φ(m) e^{Q(m,w)}`:
`κ_Φ/m² + A(m,w)/m + |∂_m a| + (1+w)²ℓ⁻¹ (∂_w A + ∂_w a)`, with
`|∂_m a| = d/(4 m^{5/4}) + d²/(4 m^{3/2})`, `∂_w A = B(3(1+w)² log(2+w) + (1+w)³/(2+w))/m`,
`∂_w a = d/√m`, `d = (w - m^{1/4})₊`. -/
noncomputable def etaF (τ ℓ w : ℝ) : ℝ :=
  let m := mOf ℓ w
  let d := dpos m w
  kappa τ / m ^ 2 + BSCert.Z2.A m w / m
    + (d / (4 * (m * u0 m)) + d ^ 2 / (4 * (m * √m)))
    + (1 + w) ^ 2 / ℓ * (11 * (3 * (1 + w) ^ 2 * Real.log (2 + w) + (1 + w) ^ 3 / (2 + w)) / m
      + d / √m)

/-- The paper's cut-off set `{w : w ≤ U(m)}` (the range of the induction hypothesis). -/
def paperCut (τ ℓ : ℝ) : Set ℝ := {w | w ≤ Uf τ (mOf ℓ w)}

/-- `g(w) = (ρ(w-1)/ρ(u-1)) e^{D(w)} 1[w ∈ I]`. -/
noncomputable def gfun (τ ℓ u : ℝ) (I : Set ℝ) (w : ℝ) : ℝ :=
  Set.indicator I (fun w => Dickman.rho (w - 1) / Dickman.rho (u - 1) * Real.exp (Dfun τ ℓ u w)) w

/-- The main term `M = ∫ π e^D 1[w ∈ I] = ∫_{w_lo}^{U(ℓ)} g(w) dw/w`. -/
noncomputable def Mterm (τ ℓ u : ℝ) (I : Set ℝ) : ℝ :=
  ∫ w in wlo τ ℓ u..Uf τ ℓ, gfun τ ℓ u I w / w

/-- `E₁ = 2K'(1 + w_lo)² g(w_lo)/(w_lo ℓ)`. -/
noncomputable def E1term (τ ℓ u : ℝ) (I : Set ℝ) : ℝ :=
  2 * Kp * (1 + wlo τ ℓ u) ^ 2 * gfun τ ℓ u I (wlo τ ℓ u) / (wlo τ ℓ u * ℓ)

/-- `E₂ = (K'/ℓ) ∫ g (1+w) dw/w`. -/
noncomputable def E2term (τ ℓ u : ℝ) (I : Set ℝ) : ℝ :=
  Kp / ℓ * ∫ w in wlo τ ℓ u..Uf τ ℓ, gfun τ ℓ u I w * (1 + w) / w

/-- `E₃ = 2K' ∫ g η_f dw/w`. -/
noncomputable def E3term (τ ℓ u : ℝ) (I : Set ℝ) : ℝ :=
  2 * Kp * ∫ w in wlo τ ℓ u..Uf τ ℓ, gfun τ ℓ u I w * etaF τ ℓ w / w

/-- `u* = U(ℓ) + 1/2` (Step 6). -/
noncomputable def ustar (τ ℓ : ℝ) : ℝ := Uf τ ℓ + 1 / 2

/-- The tail of Step 6 divided by `G(ℓ, u)`: `(ℓ/τ) C₀ ρ(u*) e^{a_V(u*)}/G(ℓ, u)`. -/
noncomputable def Tterm (τ ℓ u : ℝ) : ℝ :=
  ℓ / τ * C0 * Dickman.rho (ustar τ ℓ) * Real.exp (aV ℓ (ustar τ ℓ)) / Gf τ ℓ u

/-- `Σ(ℓ, u) = 1 - [M + E₁ + E₂ + E₃ + T]` with the cut-off `I`. -/
noncomputable def SigmaGen (τ ℓ u : ℝ) (I : Set ℝ) : ℝ :=
  1 - (Mterm τ ℓ u I + E1term τ ℓ u I + E2term τ ℓ u I + E3term τ ℓ u I + Tterm τ ℓ u)

/-- **`Σ(ℓ, u)` of (bs-Sigma)**, with the paper's cut-off `1[w ≤ U(m)]`. -/
noncomputable def Sigma (τ ℓ u : ℝ) : ℝ := SigmaGen τ ℓ u (paperCut τ ℓ)

/-! ## The verification regions of Step 7 -/

/-- **Step 7(i) of the proof of Theorem 5.6 (region Z1)**: `Σ(ℓ, u) ≥ 0` for `u < 2` and every
`ℓ > 30τ`, `τ ≥ 10⁸` (the paper proves `ℓΣ ≥ 0.265τ - 2714 > 0`). -/
def RegionZ1 : Prop :=
  ∀ τ ℓ u : ℝ, 100000000 ≤ τ → 30 * τ < ℓ → 0 ≤ u → u < 2 → 0 ≤ Sigma τ ℓ u

/-- **Step 7(ii) of the proof of Theorem 5.6 (large `ℓ`)**: `Σ(ℓ, u) ≥ 0` for `ℓ ≥ 10¹⁸`
(and `ℓ > 30τ`), `2 ≤ u ≤ U(ℓ)`, `τ ≥ 10⁸` (Lemma 5.7 with the positivity of `c(u)`). -/
def RegionLarge : Prop :=
  ∀ τ ℓ u : ℝ, 100000000 ≤ τ → 30 * τ < ℓ → 1000000000000000000 ≤ ℓ → 2 ≤ u →
    u ≤ Uf τ ℓ → 0 ≤ Sigma τ ℓ u

/-- `Σ(ℓ, u) ≥ 0` on the whole range of the induction step (bs-Sigma) at a fixed `τ`. -/
def SigmaNonneg (τ : ℝ) : Prop :=
  ∀ ℓ u : ℝ, 30 * τ < ℓ → 0 ≤ u → u ≤ Uf τ ℓ → 0 ≤ Sigma τ ℓ u

end BSaias

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-! ## Sums over the system -/

/-- `∑_{n ∈ 𝒩 ∩ (Y, 2Y]} 1/n`. -/
noncomputable def harmBlock (Y : ℝ) : ℝ :=
  ∑ e ∈ (P.elems (2 * Y)).filter (fun e => Y < P.val e), 1 / P.val e

/-- `v(log Y, z) = ∑_{n ∈ 𝒩 ∩ (Y, 2Y], P⁺(n) ≤ z} 1/n` (Lemma 5.3). -/
noncomputable def vSmooth (Y z : ℝ) : ℝ :=
  ∑ e ∈ (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ ∀ j ∈ e.support, P.p j ≤ z),
    1 / P.val e

/-- `e` is squarefree and `t`-dense: `p_j ≤ t ∏_{i < j, i ∈ e} p_i` for each prime `p_j` of
`e` (Theorem 5.6; the empty product is `1`, so the least prime is `≤ t`). -/
def IsDense (t : ℝ) (e : ℕ →₀ ℕ) : Prop :=
  (∀ j, e j ≤ 1) ∧ ∀ j ∈ e.support, P.p j ≤ t * ∏ i ∈ e.support.filter (· < j), P.p i

/-- `W_t(Y; Y^{1/u})`: the `t`-dense elements of `(Y, 2Y]` all of whose primes satisfy
`u log p ≤ log Y` (no constraint for `u = 0`). -/
noncomputable def Wsm (t Y u : ℝ) : ℝ :=
  open scoped Classical in
  ∑ e ∈ (P.elems (2 * Y)).filter (fun e => Y < P.val e ∧ P.IsDense t e ∧
      ∀ j ∈ e.support, u * Real.log (P.p j) ≤ Real.log Y), 1 / P.val e

/-- `W_t(Y) = ∑_{n ∈ 𝒩 ∩ (Y, 2Y], t-dense} 1/n` (Theorem 5.6). -/
noncomputable def Wt (t Y : ℝ) : ℝ := P.Wsm t Y 0

/-- **Lemma 5.3 (smooth elements, with Dickman quality)**, as a statement about `P` read on
`[1, Z]`: for `L_z = log z ≥ 100`, `ℓ = u L_z` with `1 ≤ u ≤ L_z` and `2e^ℓ ≤ Z`,
`v(ℓ, z) ≤ C₀ ρ(u) e^{a_V}`. -/
def Lemma53 (Z : ℝ) : Prop :=
  ∀ z u : ℝ, 100 ≤ Real.log z → 1 ≤ u → u ≤ Real.log z →
    2 * Real.exp (u * Real.log z) ≤ Z →
    P.vSmooth (Real.exp (u * Real.log z)) z ≤
      BSaias.C0 * Dickman.rho u * Real.exp (BSaias.aV (u * Real.log z) u)

/-- The small-height bound in the proof of Lemma 5.3: `∑_{n ∈ 𝒩 ∩ (Y, 2Y]} 1/n ≤ C₀` for
`Y ≥ 72` (with `2Y ≤ Z`). -/
def SmallHeights (Z : ℝ) : Prop :=
  ∀ Y : ℝ, 72 ≤ Y → 2 * Y ≤ Z → P.harmBlock Y ≤ BSaias.C0

end BeurlingSystem

end
