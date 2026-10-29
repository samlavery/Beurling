module

public import RequestProject.Beurling.BaseRange.Margin
public import RequestProject.Beurling.BaseRange.Split
public import RequestProject.Beurling.BaseRange.Section73
public import RequestProject.Beurling.BaseRange.Mu0b

/-!
# Section 7 (the base range): all modules

* `Huxley` : §7.1, `η_H`, `X_Hux`, the named hypothesis `Huxley84` (eq. (84)) and
  `Huxley84 → ShortIntervalPNT`;
* `Window` : `MA[ℙ]`, Lemma 7.3(a), Lemma 7.1(1), `j_{X₀} ≤ 1.0001/Λ`;
* `Blin` : Lemma 7.1(2) (dilation commutation), (3) (partial windows), (5) (ramp mass);
* `Split` : `f₀`, `f₁`, `|f₁| ≤ η_H f₀`, `K^sh_ℚ` and the rational half of Lemma 7.3(c);
* `Mu1Sum` : Lemma 7.3(c) ⟹ (87);
* `EdgeNum`, `EdgeIdentity` : Lemma 7.3(d)(i),(ii) and the numerics of (d)(iii) and "Use";
* `Section73` : §7.3, `X_LP ≤ X_sw` and the ranges of Proposition 5.35;
* `Margin` : Lemma 7.3 in the form consumed by Propositions 5.35 and 5.38 (`lemma_7_3`);
* `EulerQ`, `KshQSecond` : the Rankin–Euler product for `ℕ` and the second bound of (c) for
  `K^sh_ℚ` (`kshQF1Second`);
* `AbelFin`, `EulerR`, `KptF1` : Abel summation over finitely many points, the two-sided
  harmonic bound under (HBS), the realised cofactor sums and Euler product, and the `K_pt` half
  of (c) (`kptF1Bound`); `Lemma73cReal` : (c) for the realised `μ₁`;
* `Mu0`, `Mu0b` : the rational identity (85), the partial windows, the realised `μ₀`, the
  decomposition (86) (`shdecomp`) and (b) from `Lemma73bCore` (`lemma73b_of`,
  `lemma73Inputs_full`).
-/
