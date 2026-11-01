module

public import RequestProject.BSCert.Z2Defs

/-!
# Region Z2: expression tree for `Z2Claim` and its exactness

`z2Ex` is a `let`-chain mirroring `S_cell` of `bs_cert_arb.py`; `z2Ex_eval` proves that its
real value is exactly `Z2Claim r ℓ u` (environment `[ℓ, u, u - u₀(ℓ), r u, r (u-1)]`).
-/

@[expose] public section

namespace BSCert

/-- A chain of `let`s. -/
def letChain : List Ex → Ex → Ex
  | [], b => b
  | e :: es, b => .lett e (letChain es b)

/-- `ChainOK es xs env`: evaluating the `let`s `es` from `env` produces the values `xs`. -/
def ChainOK : List Ex → List ℝ → List ℝ → Prop
  | [], [], _ => True
  | e :: es, x :: xs, env => Ex.eval e env = x ∧ ChainOK es xs (env ++ [x])
  | _, _, _ => False

lemma letChain_eval : ∀ (es : List Ex) (xs : List ℝ) (env : List ℝ) (b : Ex),
    ChainOK es xs env → (letChain es b).eval env = b.eval (env ++ xs)
  | [], [], env, b, _ => by simp [letChain]
  | e :: es, x :: xs, env, b, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [letChain, Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific]
    rw [h1, letChain_eval es xs (env ++ [x]) b h2]
    simp
  | [], _ :: _, _, _, h => by simp [ChainOK] at h
  | _ :: _, [], _, _, h => by simp [ChainOK] at h

namespace Z2

/-- Variable `i` (de Bruijn level). -/
abbrev X (i : ℕ) : Ex := .var i

/-- `η̄(w, d)` as an expression; `Lw` is `log(2 + w)`. Uses `ℓ = X 0`, `√ℓ = X 6`,
`c_u = X 9`, `k_u = X 10`, `κ_max = X 25`. -/
def etaEx (w Lw d : Ex) : Ex :=
  4 * X 25 / (X 0 * X 0) + 4 * (11 * (1 + w) * (1 + w) * (1 + w) * Lw / X 0) / X 0
    + .pos (d + X 9) / (4 * (X 0 / 2) * .sqrt (.sqrt (X 0 / 2)))
    + X 10 * (.sq (.pos (d + X 9)) / (2 * X 6)) / X 0
    + .sq (1 + w) / X 0 * (2 * 11 * .sq (1 + w) * (3 * Lw + 1) / X 0
      + .sqrt 2 * .pos (d + X 9) / X 6)

/-- The `let`s of `z2Ex` (indices `5, 6, …`); the environment starts with
`X 0 = ℓ`, `X 1 = u`, `X 2 = v`, `X 3 = r(u)`, `X 4 = r(u-1)`. -/
def z2Lets : List Ex := [
  /- 5 u₀ -/ .sqrt (.sqrt (X 0)),
  /- 6 √ℓ -/ .sqrt (X 0),
  /- 7 Ū - u₀ -/ X 5 * .sqrt (2 * .log (X 0 / 100000000) + 4),
  /- 8 Ū -/ X 5 + X 7,
  /- 9 c_u -/ X 5 / (3 * X 1),
  /- 10 k_u -/ 1 + 1 / (2 * (X 1 - 1)),
  /- 11 -/ .log (1 + X 1),
  /- 12 -/ .log (2 + X 1),
  /- 13 -/ .log (2 + (X 1 + 60)),
  /- 14 -/ .log (2 + X 8),
  /- 15 A -/ 11 * (1 + X 1) * (1 + X 1) * (1 + X 1) * X 12 / X 0,
  /- 16 β_a -/ (X 10 - 1) * .sq (.pos (X 2 + X 9)) / (2 * X 6)
      + .ite (X 2 + X 9) 0 (X 9 * (2 * .pos (X 2) + X 9) / (2 * X 6)),
  /- 17 β_I -/ X 15 / X 1 + X 16 - 400000000 / (X 1 * X 0),
  /- 18 β_II -/ X 15 / X 1 + X 16,
  /- 19 α -/ 11 / X 0 * (X 1 * X 1 * X 1) * (3 * X 1 - 4) * X 11 / .sq (X 1 - 1)
      + X 10 * .pos (X 2 - 1 + X 9) / X 6,
  /- 20 γ₁ -/ 11 / X 0 * 8 * .sq (1 + (X 1 + 60)) * X 13 + X 10 * .pos (X 2 + 60 + X 9) / X 6,
  /- 21 γ_max -/ 11 / X 0 * 8 * .sq (1 + X 8) * X 14 + X 10 * .pos (X 7 + X 9) / X 6,
  /- 22 -/ .exp (X 17),
  /- 23 -/ .exp (X 18),
  /- 24 q -/ .exp (-(X 4 - X 21) * 60) / (X 4 - X 21),
  /- 25 κ_max -/ 4 * X 0 / 30 + 1500,
  /- 26 -/ etaEx (X 1) (X 12) (X 2),
  /- 27 -/ etaEx (X 1 + 60) (X 13) (X 2 + 60),
  /- 28 -/ etaEx (X 8) (X 14) (X 7),
  /- 29 M - 1 -/ (X 22 - 1) * (1 - 1 / (X 1 * X 3)) + (X 23 - 1) / (X 1 * X 3)
      - X 22 * (1 - .exp (-(X 19))) * (1 - 1 / X 3)
      + X 23 / X 1 * (X 20 / (X 4 * (X 4 - X 20)) + X 24),
  /- 30 E₁ -/ 2 * 2.2 * .sq (X 1) * X 4 * .exp (X 17 - X 19) / X 0,
  /- 31 E₂ -/ 2.2 / X 0 * (X 1 / (X 1 - 1)) * (X 22 * (X 1 - 1) + X 23 * (1 / (X 4 - X 20) + X 24)),
  /- 32 E₃ -/ 2 * 2.2 * (X 26 * X 22 + X 23 / X 1 * (X 27 / (X 4 - X 20) + X 28 * X 24)),
  /- 33 a_V -/ 12.8 * .sq (X 8 + 1 / 2) * .log (X 8 + 1 / 2 + 2) / X 0,
  /- 34 U₃₀ - u -/ X 5 * .sqrt (2 * .log 30 + 4) - X 2,
  /- 35 E_T -/ .ite (-(X 34)) (.log 30 - .sq (.pos (X 2)) / (2 * X 6) - X 4 * (.pos (X 34) + 1.5))
      (-2 - 1.5 * X 4),
  /- 36 T -/ .exp (X 25 / X 0 + X 33 + X 35)]

/-- The final expression `min (min (r₀ - γ₁) (r₀ - γ_max)) S`. -/
def z2Body : Ex := .min (.min (X 4 - X 20) (X 4 - X 21)) (-(X 29 + X 30 + X 31 + X 32 + X 36))

/-- The expression evaluated on every cell of region Z2. -/
def z2Ex : Ex := letChain z2Lets z2Body

/-- The real values of the `let`s. -/
noncomputable def z2Vals (r : ℝ → ℝ) (ℓ u : ℝ) : List ℝ :=
  [u0 ℓ, √ℓ, UbMu0 ℓ, Ubar ℓ, cu ℓ u, ku u, Real.log (1 + u), Real.log (2 + u),
   Real.log (2 + (u + 60)), Real.log (2 + Ubar ℓ), A ℓ u, betaa ℓ u, betaI ℓ u, betaII ℓ u,
   alpha ℓ u, gamma1 ℓ u, gammaMax ℓ u, Real.exp (betaI ℓ u), Real.exp (betaII ℓ u), qq r ℓ u,
   kmax ℓ, eta ℓ u u (u - u0 ℓ), eta ℓ u (u + 60) (u - u0 ℓ + 60), eta ℓ u (Ubar ℓ) (UbMu0 ℓ),
   Mm1 r ℓ u, E1 r ℓ u, E2 r ℓ u, E3 r ℓ u, aV ℓ, gap ℓ u, ET r ℓ u, T r ℓ u]

lemma z2_chainOK (r : ℝ → ℝ) (ℓ u : ℝ) :
    ChainOK z2Lets (z2Vals r ℓ u) [ℓ, u, u - u0 ℓ, r u, r (u - 1)] := by
  simp only [z2Lets, z2Vals, ChainOK, List.cons_append, List.nil_append, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific, etaEx, X, List.getD_cons_zero, List.getD_cons_succ, neg_nonpos]
  all_goals push_cast
  all_goals first
    | rfl
    | (conv_rhs =>
        first
          | rw [eta] | rw [Mm1] | rw [E1] | rw [E2] | rw [E3] | rw [aV] | rw [gap] | rw [ET]
          | rw [T] | rw [qq] | rw [gamma1] | rw [gammaMax] | rw [alpha] | rw [betaI]
          | rw [betaII] | rw [betaa] | rw [A])
  all_goals first | rfl | ring

/-- The expression `z2Ex` computes exactly `Z2Claim`. -/
theorem z2Ex_eval (r : ℝ → ℝ) (ℓ u : ℝ) :
    z2Ex.eval [ℓ, u, u - u0 ℓ, r u, r (u - 1)] = Z2Claim r ℓ u := by
  rw [z2Ex, letChain_eval _ _ _ _ (z2_chainOK r ℓ u)]
  simp only [z2Body, z2Vals, Ex.eval, Ex.eval_hadd, Ex.eval_hsub, Ex.eval_hmul, Ex.eval_hdiv, Ex.eval_hneg, Ex.eval_ofNat, Ex.eval_ofScientific, X, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ, Z2Claim, S]

end Z2

end BSCert
