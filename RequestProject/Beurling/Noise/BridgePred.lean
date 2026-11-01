module

public import Mathlib

/-!
# Lemma 5.34 (the noise terms, in predictable form)

§5.3 writes the response `ρ̃` (the jitter-smoothed slot density) through the margin identity
(Proposition 5.11, eq. (margin-identity)) `ρ̃ + B K_pt ρ̃ = F`, `F = T̃' - ν - NT`, with
`T̃' = B T' + ϑ/H` (eq. (Ttilde)), and the compensator margin `M = ρ̃ + ν + NT` (eq. (M)). With
the long operator `R_res = (1 + K_pt B)⁻¹`, the jump split `T' = T_c + J` and (decomp)

  `F_c = F - BJ = T_c + F_r`, `F_r = (B - 1)T_c + ϑ/H - ν - NT`, `G = K_pt(1 - B)F_c`,

Lemma 5.34 states the identity (predictable)

  `M - B R_res T' = ϑ/H - B K_pt B R_res F_r - B R_res G`,

and the bound `log x |M - B R_res T'|(x) ≤ ε_N`.

Operators are additive maps on real functions. The identity uses exactly what the paper uses:
`B`, `K_pt` additive, `R_res` a right inverse of `1 + K_pt B` (`R g + K B R g = g`), and the
injectivity of `1 + B K_pt` ("the Neumann series terminate on bounded ranges", §5.3), through
which the push-through form (pushthrough) determines `ρ̃` (`Pred.predictable_identity`).

The bound (`Pred.lemma_5_34_bound`) is the assembly of the three bullets of the proof; each
bullet is an input stating the paper's bound for that term (from Proposition 5.18, from
Lemma 5.21(iii), and `|ϑ| ≤ 6`).
-/

@[expose] public section

namespace Pred

variable (B K R : (ℝ → ℝ) →+ (ℝ → ℝ))

/-- **The identity (predictable)** of Lemma 5.34. -/
theorem predictable_identity
    (hR : ∀ g, R g + K (B (R g)) = g)
    (hinj : ∀ f f', f + B (K f) = f' + B (K f') → f = f')
    (ρ ν NT vt Tc J : ℝ → ℝ)
    (hmargin : ρ + B (K ρ) = B (Tc + J) + vt - ν - NT) :
    let Tp := Tc + J
    let F := B Tp + vt - ν - NT
    let Fc := F - B J
    let Fr := (B Tc - Tc) + vt - ν - NT
    let G := K (Fc - B Fc)
    (ρ + ν + NT) - B (R Tp) = vt - B (K (B (R Fr))) - B (R G) := by
  intro Tp F Fc Fr G
  -- the candidate solution of the margin identity
  set ρ' := B (R Tp) + vt - B (K (B (R Fr))) - B (R G) - ν - NT with hρ'
  have key : ρ' + B (K ρ') = F := by
    have h1 := hR Tp
    have h2 := hR Fr
    have h3 := hR G
    have eG : G = K Fc - K (B Fc) := by simp only [G, map_sub]
    have eFc : Fc = B Tc + vt - ν - NT := by
      simp only [Fc, F, Tp, map_add]; abel
    have hBR : ∀ g, B (R g) + B (K (B (R g))) = B g := fun g => by
      rw [← map_add, hR]
    simp only [hρ', map_add, map_sub]
    have e1 := hBR Tp
    have e2 := hBR Fr
    have e3 := hBR G
    have hKBe2 : B (K (B (R Fr))) + B (K (B (K (B (R Fr))))) = B (K (B Fr)) := by
      rw [← map_add, ← map_add, ← map_add, hR]
    -- `B K B F_r + B G = B K (vt - ν - NT)`
    have hzero : B (K (B Fr)) + B G = B (K vt) - B (K ν) - B (K NT) := by
      rw [eG, eFc]
      simp only [Fr, map_add, map_sub]
      abel
    simp only [F]
    linear_combination e1 - hKBe2 - e3 - hzero
  have : ρ = ρ' := hinj ρ ρ' (by rw [hmargin, key])
  rw [this, hρ']
  abel

/-- **Lemma 5.34, the bound**: with `D = M - B R_res T'` given by (predictable), if at the
point `x` (on `Good(<x)`) the three terms satisfy the bounds of the proof,
`log x |B K_pt B R_res F_r (x)| ≤ a` (Proposition 5.18, `a = 5.1 C_N ∑_u log(2u) F̄_r(u)`),
`log x |B R_res G (x)| ≤ b` (Lemma 5.21(iii), `b = 15.3 C_N C_S' ∑_v (log 3v)² F_r⁺(v)`) and
`|ϑ(x)| ≤ 6`, then `log x |D(x)| ≤ a + b + 6 log x/H(x) =: ε_N`. -/
theorem lemma_5_34_bound {D vt KBR BRG H : ℝ → ℝ} {x a b : ℝ}
    (hD : D x = vt x / H x - KBR x - BRG x) (hlx : 0 ≤ Real.log x) (hH : 0 < H x)
    (hK : Real.log x * |KBR x| ≤ a) (hG : Real.log x * |BRG x| ≤ b) (hϑ : |vt x| ≤ 6) :
    Real.log x * |D x| ≤ a + b + 6 * Real.log x / H x := by
  rw [hD]
  have h1 : |vt x / H x - KBR x - BRG x| ≤ |vt x| / H x + |KBR x| + |BRG x| := by
    have := abs_sub (vt x / H x - KBR x) (BRG x)
    have := abs_sub (vt x / H x) (KBR x)
    rw [abs_div, abs_of_pos hH] at this
    linarith
  have h2 : |vt x| / H x ≤ 6 / H x := div_le_div_of_nonneg_right hϑ hH.le
  calc Real.log x * |vt x / H x - KBR x - BRG x|
      ≤ Real.log x * (6 / H x + |KBR x| + |BRG x|) :=
        mul_le_mul_of_nonneg_left (by linarith) hlx
    _ = 6 * Real.log x / H x + Real.log x * |KBR x| + Real.log x * |BRG x| := by ring
    _ ≤ a + b + 6 * Real.log x / H x := by linarith

end Pred

end
