module

public import RequestProject.Beurling.Decomp.Decomposition
public import RequestProject.Beurling.Construction.Design
public import RequestProject.Beurling.GenLemma51Final

/-!
# §5.7: the local prime number theorem (Theorem 5.24) — definitions and statement

Notation of §5.7 (paper, `04e-lp.tex`).

* `Π` is the realised prime measure (prime powers `p_j^k` with weight `1/k`). We use
  `piCount P v = Π([1, v])`, `piRecip P v = ∫_{[1,v]} dΠ/u` and `piInt P φ = ∫ φ dΠ`.
* `Π₀ = log^*(δ₁ + du)` has density `π₀(u) = (1 - 1/u)/log u`: `pi0 v = Π₀([1, v])`,
  `pi0Recip v = ∫_{[1,v]} dΠ₀/u`, `pi0Int φ = ∫ φ dΠ₀`.
* `T₀ = T - (#A - ∫ ρ̄_A)` is the `A`-free target (6): `T0 θ X₀ α γ xp` is `target` with the
  absorbed count and density set to zero.
* `θ' = max(θ + 0.01, 8 (log log X₀)²/log X₀ + 0.005)` and `Λ = log X₀`.
* `ζ^♯ = Z_B + ∑_k R̂_k + D̂^♯`, `D̂^♯(s) = s ∫_1^y D u^{-s-1} du + D(y) y^{-s}`, `D = N - T₀`
  (Step 1 of the proof).

The statement `Theorem524` gathers the conclusions (i)–(iii) of Theorem 5.24 with the explicit
constants of the paper: `c_zf = 0.088/Λ`, `c_LP = c_zf/5`, `K = e^{98} Λ^{5.9}` (so
`log K = 98 + 5.9 log Λ`), `X_LP = exp(10⁵ Λ² log² Λ)`, `G(L) = 400 (L + 450 + 2 log Λ)`, and the
window `φ` of Step 10 (`lpWindow`).
-/

@[expose] public section

open Set Real MeasureTheory Complex Oscillation DesignedZero BaseFactor Decomp

namespace LocalPNT

/-! ## The prime measures `Π` and `Π₀` -/

section Pi

variable (P : BeurlingSystem)

/-- `Π(v) = ∑_{p_j^k ≤ v} 1/k` (the index `(j, k)` of `pps` stands for `p_j^{k+1}`). -/
noncomputable def piCount (v : ℝ) : ℝ :=
  ∑ jk ∈ P.pps v, 1 / ((jk.2 : ℝ) + 1)

/-- `∫_{[1,v]} dΠ(u)/u = ∑_{p_j^k ≤ v} 1/(k p_j^k)`. -/
noncomputable def piRecip (v : ℝ) : ℝ :=
  ∑ jk ∈ P.pps v, 1 / (((jk.2 : ℝ) + 1) * P.p jk.1 ^ (jk.2 + 1))

/-- `∫ φ dΠ = ∑_{j,k} φ(p_j^k)/k` (a finite sum for compactly supported `φ`). -/
noncomputable def piInt (φ : ℝ → ℝ) : ℝ :=
  ∑ᶠ jk : ℕ × ℕ, φ (P.p jk.1 ^ (jk.2 + 1)) / ((jk.2 : ℝ) + 1)

end Pi

/-- The density `π₀(u) = (1 - 1/u)/log u` of `Π₀ = log^*(δ₁ + du)`. -/
noncomputable def pi0Dens (u : ℝ) : ℝ := (1 - 1 / u) / Real.log u

/-- `Π₀(v) = ∫_1^v π₀`. -/
noncomputable def pi0 (v : ℝ) : ℝ := ∫ u in (1 : ℝ)..v, pi0Dens u

/-- `∫_{[1,v]} dΠ₀(u)/u`. -/
noncomputable def pi0Recip (v : ℝ) : ℝ := ∫ u in (1 : ℝ)..v, pi0Dens u / u

/-- `∫ φ dΠ₀`. -/
noncomputable def pi0Int (φ : ℝ → ℝ) : ℝ := ∫ u in Ioi (1 : ℝ), φ u * pi0Dens u

/-! ## The `A`-free target, `θ'` and `ζ^♯` -/

/-- `κ = X₀^{-5/12 + 0.02}` (Section 2.2). -/
noncomputable abbrev kap (X₀ : ℕ) : ℝ := Construction.kappaParam X₀

/-- **The `A`-free target** `T₀ = T - (#A - ∫ ρ̄_A)`: the target (6) without its absorbed part. -/
noncomputable def T0 (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) : ℝ → ℝ :=
  Target.target X₀ (kap X₀) (fun _ => 0) (fun _ => 0) (osc θ α γ xp)

/-- `θ' = max(θ + 0.01, 8 (log log X₀)²/log X₀ + 0.005)`. -/
noncomputable def thetaPrime (θ : ℝ) (X₀ : ℕ) : ℝ :=
  max (θ + 0.01) (8 * Real.log (Real.log X₀) ^ 2 / Real.log X₀ + 0.005)

/-- The lag against the `A`-free target, `D = N - T₀`. -/
noncomputable def lag0 (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (u : ℝ) : ℝ :=
  P.N u - T0 θ X₀ α γ xp u

/-- `R̂(s) = ∑_k R̂_k(s)`. -/
noncomputable def oscHatSum (θ : ℝ) (α γ xp : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' k, oscHat θ (α k) (γ k) (xp k) s

/-- `Ê(s) = Z_B(s) - s/(s-1)` (Lemma 4.3). -/
noncomputable def EHat (X₀ : ℕ) (s : ℂ) : ℂ := ZBcont X₀ (kap X₀) s - s / (s - 1)

/-- **The extension** (Step 1): `ζ^♯ = T̂₀ + D̂^♯ = Z_B + R̂ + D̂^♯`, the transform of
`N^♯ = N` on `[1, y]`, `N^♯(u) = N(y) + T₀(u) - T₀(y)` for `u > y`. -/
noncomputable def zetaSharp (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (y : ℝ)
    (s : ℂ) : ℂ :=
  ZBcont X₀ (kap X₀) s + oscHatSum θ α γ xp s + earlyNoise (lag0 P θ X₀ α γ xp) y s

/-! ## The constants of Theorem 5.24 -/

/-- `c_zf = 0.088/Λ`. -/
noncomputable def cZF (Λ : ℝ) : ℝ := 0.088 / Λ

/-- `c_LP = c_zf/5`. -/
noncomputable def cLP (Λ : ℝ) : ℝ := cZF Λ / 5

/-- `K = e^{98} Λ^{5.9}`, so `log K = 98 + 5.9 log Λ`. -/
noncomputable def KLP (Λ : ℝ) : ℝ := Real.exp 98 * Λ ^ (5.9 : ℝ)

/-- `X_LP = exp(10⁵ Λ² log² Λ)`. -/
noncomputable def XLP (Λ : ℝ) : ℝ := Real.exp (10 ^ 5 * Λ ^ 2 * Real.log Λ ^ 2)

/-- `G(L) = 400 (L + 450 + 2 log Λ)`. -/
noncomputable def GLam (Λ L : ℝ) : ℝ := 400 * (L + 450 + 2 * Real.log Λ)

/-! ## The window of Step 10 -/

/-- One box average of half-width `δ`: `(1/(2δ)) ∫_{x-δ}^{x+δ} f`, i.e. the convolution with
`β = (1/(2δ)) 1_{[-δ, δ]}`. -/
noncomputable def boxAvg (δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * δ)) * ∫ t in (x - δ)..(x + δ), f t

/-- `ψ = 1_{[a-ω, b+ω]} * β_ω^{*k}`, `β_ω = (k/(2ω)) 1_{[-ω/k, ω/k]}` (Step 10). -/
noncomputable def windowLog (a b ω : ℝ) (k : ℕ) : ℝ → ℝ :=
  (boxAvg (ω / k))^[k] ((Icc (a - ω) (b + ω)).indicator 1)

/-- `k = ⌈log(1/η) + 20 log Λ_p⌉`, `Λ_p = log v` (Theorem 5.24(iii)). -/
noncomputable def lpK (v η : ℝ) : ℕ := ⌈Real.log (1 / η) + 20 * Real.log (Real.log v)⌉₊

/-- `w = η Λ_p^{-2}`. -/
noncomputable def lpW (v η : ℝ) : ℝ := η / Real.log v ^ 2

/-- **The window `φ` of Step 10**: `φ(u) = ψ(log u)` with `a = log v`, `b = log(v(1+η))`,
`ω = w/4` and `k = lpK v η` (and `φ = 0` if `v ≤ 0`). -/
noncomputable def lpWindow (v η : ℝ) (u : ℝ) : ℝ :=
  if 0 < u ∧ 0 < v then
    windowLog (Real.log v) (Real.log (v * (1 + η))) (lpW v η / 4) (lpK v η) (Real.log u)
  else 0

/-- `L₁ = 2 log Λ_p + log(1/η) + log k + 3.08`. -/
noncomputable def lpL1 (v η : ℝ) : ℝ :=
  2 * Real.log (Real.log v) + Real.log (1 / η) + Real.log (lpK v η) + 3.08

/-- The bound (eq. lpplus) on `Rel`:
`18 G(L₁) Λ_p³ η^{-1} exp(-0.9 c_zf Λ_p/(L₁ + 442 + 2 log Λ + log L₁)) + Λ_p^{-2}`. -/
noncomputable def relBound (Λ v η : ℝ) : ℝ :=
  18 * GLam Λ (lpL1 v η) * Real.log v ^ 3 / η *
      Real.exp (-(0.9 * cZF Λ * Real.log v /
        (lpL1 v η + 442 + 2 * Real.log Λ + Real.log (lpL1 v η)))) +
    1 / Real.log v ^ 2

/-! ## The hypotheses and the statement of Theorem 5.24 -/

/-- **The hypotheses of Theorem 5.24** for a Beurling system `P`, the target data
`θ, X₀, α_k, γ_k, x_k` (`T₀ = T0 θ X₀ α γ xp`), `X₀⁻ = Xm` and the height `y`.

* The design: `θ ∈ [1/20, 1/2 - 10⁻⁴]`, `log X₀ ≥ 10⁸`, `X₀` even, `|α_k| ≤ 2`,
  `x_0 ≥ exp(X₀²)` and `x_{k+1} ≥ exp(x_k)`; `X₀/2 ≤ X₀⁻ ≤ X₀` and `y ≥ X₀`.
* `T₀` is non-decreasing on `[X₀, ∞)`: Lemma 3.3 (positivity margin (7)) for the `A`-free
  target, whose slope is `T'_cont + ρ̄_A ≥ T'_cont > 0` and whose jumps are the rigid ones.
* **(LP-a)**: `N = T₀` below `X₀⁻`, and `|N(u) - T₀(u)| ≤ D₀(u) ≤ u^{θ'}` on `[X₀⁻, y]`.

(LP-b) and (LP-c) are not hypotheses here: for the target data above they are Lemma 4.3 with
`a = 8` and (18) (`LocalPNT.lpb`, `LocalPNT.lpc`). -/
structure LPHyp (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (α γ xp : ℕ → ℝ) (Xm y : ℝ)
    (D0 : ℝ → ℝ) : Prop where
  theta_mem : θ ∈ Icc (1 / 20 : ℝ) (1 / 2 - 1 / 10000)
  logX : 10 ^ 8 ≤ Real.log X₀
  even : Even X₀
  alpha_le : ∀ k, |α k| ≤ 2
  xp_zero : Real.exp ((X₀ : ℝ) ^ 2) ≤ xp 0
  xp_succ : ∀ k, Real.exp (xp k) ≤ xp (k + 1)
  T0_mono : MonotoneOn (T0 θ X₀ α γ xp) (Ici (X₀ : ℝ))
  Xm_ge : (X₀ : ℝ) / 2 ≤ Xm
  Xm_le : Xm ≤ X₀
  y_ge : (X₀ : ℝ) ≤ y
  lpa_low : ∀ u, u < Xm → P.N u = T0 θ X₀ α γ xp u
  lpa_high : ∀ u, Xm ≤ u → u ≤ y →
    |P.N u - T0 θ X₀ α γ xp u| ≤ D0 u ∧ D0 u ≤ u ^ thetaPrime θ X₀

/-- **The conclusions of Theorem 5.24** at the height `y`, with `Λ = log X₀`:

(i) `|∫_{[1,v]} d(Π - Π₀)/u| ≤ K e^{-c_LP √(log v)}` and
(ii) `|Π(v) - Π₀(v)| ≤ K v e^{-c_LP √(log v)}` for `X_LP ≤ v ≤ y`;

(iii) for `Λ_p = log v ≥ 76 Λ³`, `η ∈ [e^{-2Λ}, 1/2]` with `v(1+2η) ≤ y`, the window `φ` of
Step 10 satisfies `0 ≤ φ ≤ 1`, `φ = 1` on `[v, v(1+η)]`, `φ = 0` off `[v(1-w), v(1+η+w)]`, and
`∫ φ dΠ ≤ (1 + Rel) ∫ φ dΠ₀` with `Rel` bounded by (eq. lpplus). -/
def Theorem524Concl (P : BeurlingSystem) (X₀ : ℕ) (y : ℝ) : Prop :=
  (∀ v, XLP (Real.log X₀) ≤ v → v ≤ y →
    |piRecip P v - pi0Recip v| ≤
        KLP (Real.log X₀) * Real.exp (-(cLP (Real.log X₀) * Real.sqrt (Real.log v))) ∧
      |piCount P v - pi0 v| ≤
        KLP (Real.log X₀) * v * Real.exp (-(cLP (Real.log X₀) * Real.sqrt (Real.log v)))) ∧
  (∀ v η, 76 * Real.log X₀ ^ 3 ≤ Real.log v → Real.exp (-(2 * Real.log X₀)) ≤ η → η ≤ 1 / 2 →
    v * (1 + 2 * η) ≤ y →
    (∀ u, 0 ≤ lpWindow v η u ∧ lpWindow v η u ≤ 1) ∧
    (∀ u ∈ Icc v (v * (1 + η)), lpWindow v η u = 1) ∧
    (∀ u, lpWindow v η u ≠ 0 → u ∈ Icc (v * (1 - lpW v η)) (v * (1 + η + lpW v η))) ∧
    piInt P (lpWindow v η) ≤ (1 + relBound (Real.log X₀) v η) * pi0Int (lpWindow v η))

end LocalPNT

end
