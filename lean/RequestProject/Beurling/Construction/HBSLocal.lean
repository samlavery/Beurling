module

public import RequestProject.Beurling.Construction.HBSPieces

/-!
# Lemma 6.26 at one height from (HBS) up to `2y(2v)`, and the size of `y`

* `lemma626_local`: Lemma 6.26 at a height `v`, using (HBS) only on `[1, 2y(2v)]`.
* `two_absorbYAt_two_le`: `2y(2v) < X₀` or `2y(2v) ≤ v/2`, so (HBS) at `2y(2v)` only involves
  heights below `X₀` or at most `v/2`.
-/

@[expose] public section

open Set CaplLink QueueMono InitialRange AbsorbEmpty BSCert.Capl

namespace Construction

/-- **Lemma 6.26 for the construction, local version**: as `lemma626_construction`, at one height
`v ≥ X₀`, with (HBS) assumed only up to `2y(2v)` and `N(w) = ⌊w⌋` below `X₀⁻`. -/
theorem lemma626_local {P : BeurlingSystem} {X₀ : ℕ} {R : GreedyRun X₀} {A : Set ℝ}
    {latest : ℝ → ℝ} (C : AbsorbedCoupling P R.M R.H R.U A latest) {θ X0m η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (hX : 10 ^ 8 ≤ Real.log X₀) (hθ1 : 1 / 4 ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hRH : R.H = capH X₀) (hU : ∀ j, R.U j ∈ Icc (0 : ℝ) 1)
    (hX0m : 100 ≤ Real.log X0m) (hX0mX : (X₀ : ℝ) / 2 + 1 ≤ X0m)
    (hfl : ∀ w, 1 ≤ w → w < X0m → P.N w = ⌊w⌋₊)
    (hcl : ∀ v ≥ (X₀ : ℝ), ClusterUpTo P X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v))
    {v : ℝ} (hv : (X₀ : ℝ) ≤ v) (hHBS : P.HBS X0m (2 * absorbYAt X₀ (2 * v)) η1 η2 ε1) :
      (Absorbed.localCountA A v (v + v ^ (θ / 2)) : ℝ) ≤ v ^ (θ / 2) * Real.log v ^ (-4 : ℤ) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  obtain ⟨hv0, hL, hl, -⟩ := height_facts hX0 hX hv
  set h := v ^ (θ / 2) with hh
  set L := Real.log v with hLdef
  have hv1 : 1 < v := by linarith
  have h1 : 1 ≤ h := Real.one_le_rpow hv1.le (by linarith)
  have hlt : h < v := by
    have := Real.rpow_lt_rpow_of_exponent_lt hv1 (show θ / 2 < 1 by linarith)
    rwa [Real.rpow_one] at this
  by_cases hne : ∃ n ∈ A, v ≤ n ∧ (n : ℝ) ≤ v + h
  swap
  · push_neg at hne
    rw [localCountA_eq_zero (by linarith) (fun n hn hc => absurd hc.2 (not_le.mpr (hne n hn hc.1)))]
    push_cast
    have : 0 < L ^ (-4 : ℤ) := zpow_pos (by linarith) _
    positivity
  obtain ⟨n0, hn0, -, hn0v⟩ := hne
  have h2v : (X₀ : ℝ) ≤ 2 * v := by linarith
  have hy := C.two_y_gt hRH hU hX hn0 (x := 2 * v) (by linarith) h2v
  obtain ⟨hus, hll, hη, hu01, hu0, h81⟩ := cond81_window hX0 hX hθ1 hθ2 hv (by linarith) le_rfl hy
  set y := absorbYAt X₀ (2 * v) with hydef
  have hy4 : 4 ≤ y := by
    have := exp_le_absorbYAt hX0 hX h2v
    obtain ⟨-, -, hl2, -⟩ := height_facts hX0 hX h2v
    have h4 : (4 : ℝ) ≤ Real.exp (8 * Real.log (Real.log (2 * v)) ^ 2) := by
      have := Real.add_one_le_exp (8 * Real.log (Real.log (2 * v)) ^ 2)
      nlinarith
    linarith
  have hCd0 : 0 < capCd X₀ v := by
    unfold capCd; have := one_le_capM1 hX0 hX hv; positivity
  refine BeurlingSystem.HBS.lemma626 hHBS hX0m h1 hlt hy4 le_rfl hCd0 (by linarith)
    ?_ ?_ hus hll hη hu01 hu0 h81
  · intro n hn hun hnu
    exact C.smooth hRH hU hX hn (by linarith) h2v
  · intro d hd hdh hdle
    have hhL := log_pow_le_rpow hv0 hL hθ1
    rw [← hh] at hhL
    have hL11 : 0 < L ^ 11 := by positivity
    have huZ : v + h ≤ h * (4 * v / L ^ 11) := by
      rw [show h * (4 * v / L ^ 11) = 4 * v * (h / L ^ 11) by ring]
      have : 1 ≤ h / L ^ 11 := by rw [le_div_iff₀ hL11]; linarith
      nlinarith
    have he2 : 2 * Real.exp 2 ≤ (X₀ : ℝ) := by
      have h7 : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have : (16 : ℝ) ≤ X₀ := by
        have := Real.add_one_le_exp (Real.log X₀)
        rw [Real.exp_log (by linarith)] at this; linarith
      linarith
    have hM1 := one_le_capM1 hX0 hX hv
    refine (window_count_divisor P he2 hX0mX hfl (hcl v hv) (by linarith) h1 (by linarith)
      huZ d hdh).trans ?_
    exact window_const_le hM1 hv0 (by linarith) (by linarith) hlt.le


/-- **The threshold is small**: for `v ≥ X₀`, either `2y(2v) < X₀` (Theorem 6.23(b), first case)
or `2y(2v) ≤ v/2` (both regimes above `s_H`). -/
theorem two_absorbYAt_two_le {X₀ v : ℝ} (hX0 : 0 ≤ X₀) (hX : 10 ^ 8 ≤ Real.log X₀)
    (hv : X₀ ≤ v) : 2 * absorbYAt X₀ (2 * v) < X₀ ∨ 2 * absorbYAt X₀ (2 * v) ≤ v / 2 := by
  have hX1 := one_lt_of_logX hX0 hX
  have hx : X₀ ≤ 2 * v := by linarith
  have hx0 : 0 < 2 * v := by linarith
  rcases le_or_gt (capS X₀ (2 * v)) sHroot with hs | hs
  · exact Or.inl (two_absorbYAt_lt_of_le_sH hX0 hX hx hs)
  · right
    have hy1 := one_le_absorbYAt hX0 hX hx
    have hy0 : 0 < 2 * absorbYAt X₀ (2 * v) := by linarith
    obtain ⟨h4lo, h4hi⟩ := log4_bounds
    -- it suffices that `log 2y ≤ log(2v) - log 4`
    suffices hlog : Real.log (2 * absorbYAt X₀ (2 * v)) ≤ Real.log (2 * v) - Real.log 4 by
      have e : Real.log (2 * v) - Real.log 4 = Real.log (v / 2) := by
        rw [← Real.log_div (by positivity) (by norm_num)]; congr 1; ring
      rw [e] at hlog
      exact (Real.log_le_log_iff hy0 (by linarith)).mp hlog
    have hΛ : 10 ^ 8 ≤ Real.log X₀ := hX
    rcases regimes_of_gt_sH hX0 hX hx hs with ⟨hγ0, hγ, hly, -, hlx⟩ | ⟨hly, -, hl⟩
    · have : 3.01 * gam sHroot (capS X₀ (2 * v)) * Real.log X₀ ≤ 3.01 * 7.5 * Real.log X₀ := by
        gcongr
      nlinarith
    · set l := Real.log (Real.log (2 * v)) with hldef
      have hL : 0 < Real.log (2 * v) := by
        have := Real.log_le_log (by linarith) hx; linarith
      have hexp : Real.exp l = Real.log (2 * v) := by rw [hldef, Real.exp_log hL]
      have h3 : l ^ 3 / 6 ≤ Real.exp l := by
        have := Real.pow_div_factorial_le_exp (x := l) (by linarith) 3
        simpa [Nat.factorial] using this
      have : 12.1 * l ^ 2 + 1.39 ≤ l ^ 3 / 6 := by nlinarith
      linarith

end Construction

end
