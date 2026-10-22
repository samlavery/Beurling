module

public import Mathlib

/-!
# A Rouché-type zero criterion

The zeros in Theorem 4.9 of the paper are obtained by comparing `ζ_P` with a model function
`g = Z_B + M_k` that has a zero at the centre `s*` of a small circle. Mathlib has no Rouché
theorem, so we use the following form, which follows from the maximum modulus principle and
is exactly what the paper's constants give (`|Z_B + M_k| ≥ 1/4` on the circle, perturbation
`≤ 1/16 + o(1) < 1/8`):

if `g c = 0`, `‖g‖ ≥ M` and `‖f - g‖ ≤ m` on the circle `|z - c| = r` with `2m < M`, and both
functions are holomorphic on the closed disc, then `f` has a zero in the open disc.
-/

@[expose] public section

open Metric Set

/-- **Zero criterion (Rouché-type).** If `g` vanishes at the centre of a closed disc, `‖g‖ ≥ M`
and `‖f - g‖ ≤ m` on the boundary circle with `2 m < M`, and `f`, `g` are holomorphic on the
closed disc, then `f` has a zero in the open disc. -/
theorem exists_zero_of_near_model {f g : ℂ → ℂ} {c : ℂ} {r m M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall c r)) (hg : DifferentiableOn ℂ g (closedBall c r))
    (hgc : g c = 0) (hmM : 2 * m < M)
    (hfg : ∀ z ∈ sphere c r, ‖f z - g z‖ ≤ m) (hgM : ∀ z ∈ sphere c r, M ≤ ‖g z‖) :
    ∃ z ∈ ball c r, f z = 0 := by
  by_contra hcon
  push_neg at hcon
  have hr0 : r ≠ 0 := hr.ne'
  -- `m ≥ 0`, since the sphere is nonempty
  obtain ⟨z0, hz0⟩ : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hfg z0 hz0)
  have hMm : 0 < M - m := by linarith
  -- On the sphere, `‖f‖ ≥ M - m`.
  have hfs : ∀ z ∈ sphere c r, M - m ≤ ‖f z‖ := by
    intro z hz
    have h1 := hfg z hz
    have h2 := hgM z hz
    have : ‖g z‖ ≤ ‖f z‖ + ‖f z - g z‖ := by
      calc ‖g z‖ = ‖f z - (f z - g z)‖ := by ring_nf
        _ ≤ ‖f z‖ + ‖f z - g z‖ := norm_sub_le _ _
    linarith
  -- `f` has no zero on the closed disc.
  have hfne : ∀ z ∈ closedBall c r, f z ≠ 0 := by
    intro z hz
    rcases (mem_closedBall.mp hz).lt_or_eq with h | h
    · exact hcon z (mem_ball.mpr h)
    · have h : z ∈ sphere c r := mem_sphere.mpr h
      intro h0
      have := hfs z h
      rw [h0, norm_zero] at this
      linarith
  -- Maximum modulus for `f - g` at the centre: `‖f c‖ ≤ m`.
  have hcl : closure (ball c r) = closedBall c r := closure_ball c hr0
  have hfr : frontier (ball c r) = sphere c r := frontier_ball c hr0
  have hc_mem : c ∈ closure (ball c r) := by
    rw [hcl]; exact mem_closedBall_self hr.le
  have h1 : ‖(f - g) c‖ ≤ m := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (DifferentiableOn.diffContOnCl (by rw [hcl]; exact hf.sub hg))
    · intro z hz; rw [hfr] at hz; exact hfg z hz
    · exact hc_mem
  simp only [Pi.sub_apply, hgc, sub_zero] at h1
  -- Maximum modulus for `1 / f` at the centre: `‖f c‖ ≥ M - m`.
  have h2 : ‖(fun z => (f z)⁻¹) c‖ ≤ (M - m)⁻¹ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z => (f z)⁻¹) isBounded_ball
      (DifferentiableOn.diffContOnCl (by rw [hcl]; exact hf.inv hfne))
    · intro z hz
      rw [hfr] at hz
      rw [norm_inv]
      exact inv_anti₀ hMm (hfs z hz)
    · exact hc_mem
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hfne c (mem_closedBall_self hr.le))
  simp only [norm_inv] at h2
  have : M - m ≤ ‖f c‖ := by
    rwa [inv_le_inv₀ hfc hMm] at h2
  linarith

end
