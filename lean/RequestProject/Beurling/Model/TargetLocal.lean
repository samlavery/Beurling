module

public import RequestProject.Beurling.Model.Data

/-!
# Locality of the target (Lemma 3.2, adaptedness)

The target (6) at a height `x ≤ z` reads

* the absorbed set `A` only up to `z + h(z)` (an element `a` contributes to `ρ_A(v)` only for
  `u_a ≤ v ≤ a`, with `u_a + h(u_a) = a`, `h = winH X₀`);
* the oscillation only through the `α_j, γ_j` with `x⁺_j < z` (`R_j ≡ 0` on `(0, x⁺_j]`);
* the heights `γ_j` only through `N` below `a_j` and `A` below `a_j + h(a_j)`
  (Lemma 4.8: `γ_j` is read from `D̂_{<a_j}`), recursively.

`targetD_congr` combines these with the locality of the absorbed set and of `N`
(`Model/Data.lean`): the target of the prime data at heights `≤ z` only reads the primes of value
below a height `Y` with `y(n) ≤ Y` for `n ≤ z + h(z)` and `a_j < Y` for every switched-on `j`.
This is the deterministic content of Lemma 3.2 (adaptedness).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty

namespace BModel

/-- `A` and `A'` agree on `(-∞, Z]`. -/
def AAgree (A A' : Set ℝ) (Z : ℝ) : Prop := ∀ n : ℝ, n ≤ Z → (n ∈ A ↔ n ∈ A')

lemma countA_congr {A A' : Set ℝ} {Z x : ℝ} (hA : AAgree A A' Z) (hxZ : x ≤ Z) :
    countA A x = countA A' x := by
  unfold countA
  congr 2
  ext k
  simp only [Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨hk, h1, h2⟩; exact ⟨(hA k (h2.trans hxZ)).mp hk, h1, h2⟩
  · rintro ⟨hk, h1, h2⟩; exact ⟨(hA k (h2.trans hxZ)).mpr hk, h1, h2⟩

/-- `t ↦ t + h(t)` is monotone on `(0, ∞)`. -/
lemma add_win_le_add_win {w : ℝ → ℝ} (hw : IsWin w) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    s + w s ≤ t + w t := by
  have := hw.mono' hs hst
  linarith

lemma absorbedBump_congr {X₀ : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) {A A' : Set ℝ} {Z v : ℝ}
    (hA : AAgree A A' Z) (hv1 : 1 ≤ v) (hvZ : v + winH X₀ v ≤ Z) (a : ℝ) :
    absorbedBump (winH X₀) A (uA X₀) a v = absorbedBump (winH X₀) A' (uA X₀) a v := by
  classical
  have hw := winH_isWin hX
  unfold absorbedBump
  by_cases haZ : (a : ℝ) ≤ Z
  · simp only [hA a haZ]
  · push_neg at haZ
    have hnot : v ∉ Icc (uA X₀ a) (a : ℝ) := by
      rintro ⟨h1, h2⟩
      have hwv := hw.one_le v hv1
      have ha2 : 2 ≤ a := by linarith
      obtain ⟨hu1, hua⟩ := solveU_spec' hw ha2
      have hu1' : 1 ≤ uA X₀ a := hu1
      have := add_win_le_add_win hw (by linarith : (0 : ℝ) < uA X₀ a) h1
      have : uA X₀ a + winH X₀ (uA X₀ a) = a := hua
      linarith
    simp only [Set.indicator_of_notMem hnot, ite_self]

lemma absorbedDensityCap_congr {X₀ : ℝ} (hX : 10 ^ 8 ≤ Real.log X₀) {A A' : Set ℝ} {Z v : ℝ}
    (hA : AAgree A A' Z) (hv1 : 1 ≤ v) (hvZ : v + winH X₀ v ≤ Z) :
    absorbedDensityCap (winH X₀) A (uA X₀) v = absorbedDensityCap (winH X₀) A' (uA X₀) v := by
  unfold absorbedDensityCap absorbedDensity
  congr 1
  exact tsum_congr (absorbedBump_congr hX hA hv1 hvZ)

/-- On `(0, z]` the oscillation only reads the `α_j, γ_j` with `x⁺_j < z`. -/
lemma osc_congr_of {θ : ℝ} {α γ α' γ' xp : ℕ → ℝ} {z : ℝ}
    (h : ∀ j, xp j < z → α j = α' j ∧ γ j = γ' j) {x : ℝ} (hx : 0 < x) (hxz : x ≤ z) :
    osc θ α γ xp x = osc θ α' γ' xp x := by
  unfold osc
  refine tsum_congr fun j => ?_
  by_cases hj : xp j < x
  · rw [(h j (lt_of_lt_of_le hj hxz)).1, (h j (lt_of_lt_of_le hj hxz)).2]
  · push_neg at hj
    rw [oscK_eq_zero_of_le hx hj, oscK_eq_zero_of_le hx hj]

/-- **Locality of the target**: at heights `x ≤ z` the target only reads `A` on `[0, Z]`
(`z + h(z) ≤ Z`) and the oscillation parameters with `x⁺_j < z`. -/
theorem target_congr {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀) {κ θ : ℝ} {A A' : Set ℝ}
    {α γ α' γ' xp : ℕ → ℝ} {z Z : ℝ} (hZ : z + winH X₀ z ≤ Z) (hA : AAgree A A' Z)
    (hosc : ∀ j, xp j < z → α j = α' j ∧ γ j = γ' j) {x : ℝ} (hx : x ≤ z) :
    target X₀ κ (countA A) (absorbedDensityCap (winH X₀) A (uA X₀)) (osc θ α γ xp) x =
      target X₀ κ (countA A') (absorbedDensityCap (winH X₀) A' (uA X₀)) (osc θ α' γ' xp) x := by
  have hX1r : (1 : ℝ) < X₀ := QueueMono.one_lt_of_logX (Nat.cast_nonneg _) hX
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hw := winH_isWin (X₀ := (X₀ : ℝ)) hX
  unfold target
  by_cases hlt : x < X₀
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]
    push_neg at hlt
    have hx0 : 0 < x := by linarith
    have hxZ : x ≤ Z := by
      have := hw.pos z (by linarith)
      linarith
    have hint : (∫ v in (X₀ : ℝ)..x, absorbedDensityCap (winH X₀) A (uA X₀) v) =
        ∫ v in (X₀ : ℝ)..x, absorbedDensityCap (winH X₀) A' (uA X₀) v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le hlt] at hv
      have hv0 : 0 < v := by linarith [hv.1]
      exact absorbedDensityCap_congr hX hA (by linarith [hv.1])
        ((add_win_le_add_win hw hv0 (hv.2.trans hx)).trans hZ)
    rw [countA_congr hA hxZ, hint, osc_congr_of hosc (by linarith) hx,
      osc_congr_of hosc hX0 (hlt.trans hx)]

/-- `targetOf` is `target` with the solved `u_a`. -/
lemma targetOf_eq (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (α γ xp : ℕ → ℝ) :
    targetOf θ X₀ κ A (uA X₀) α γ xp =
      target X₀ κ (countA A) (absorbedDensityCap (winH X₀) A (uA X₀)) (osc θ α γ xp) := rfl

/-- **Locality of the designed heights** (Lemma 4.8: `γ_j` reads only the system on `[1, a_j)`):
if `N` agrees below `Y` and `A` agrees on `[0, Z]` with `Y + h(Y) ≤ Z`, then every `γ_j`
with `a_j < Y` agrees. -/
theorem designedGammaN_congr {N N' : ℝ → ℝ} {θ : ℝ} {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀)
    {κ : ℝ} {A A' : Set ℝ} {κ₀ : ℝ} {xp a : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀)
    (hxp : (X₀ : ℝ) ≤ xp 0) (ha : ∀ k, 0 < a k ∧ a k ≤ xp k) {Y Z : ℝ}
    (hZ : Y + winH X₀ Y ≤ Z) (hN : ∀ x, x < Y → N x = N' x) (hA : AAgree A A' Z) :
    ∀ j, a j < Y → designedGammaN N θ X₀ κ A (uA X₀) κ₀ xp a j =
      designedGammaN N' θ X₀ κ A' (uA X₀) κ₀ xp a j := by
  have hw := winH_isWin (X₀ := (X₀ : ℝ)) hX
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro hj
  rw [designedGammaN_fixed N hsp hX1 hxp ha j, designedGammaN_fixed N' hsp hX1 hxp ha j]
  unfold designGamma
  congr 1
  unfold earlyN
  refine earlyNoise_congr (ha j).1 fun x hx hxa => ?_
  unfold lagN
  have hxY : x < Y := lt_of_le_of_lt hxa hj
  rw [hN x hxY, targetOf_eq, targetOf_eq]
  have hZj : a j + winH X₀ (a j) ≤ Z :=
    (add_win_le_add_win hw (ha j).1 hj.le).trans hZ
  congr 1
  refine target_congr hX hZj hA (fun i hi => ?_) hxa
  have hij : i < j := by
    by_contra hc
    push_neg at hc
    have := hsp.strictMono.monotone hc
    linarith [(ha j).2]
  have hiY : a i < Y := lt_of_le_of_lt (ha i).2 (lt_trans hi hj)
  have hγ := IH i hij hiY
  exact ⟨by simp only [amplitudes, hγ], hγ⟩

/-- **Lemma 3.2 (adaptedness), deterministic form**: under `DAgree D D' Y`, the targets of the
data agree at every height `x ≤ z`, provided `y(n) ≤ Y` for every `n ≤ Z`, `z + h(z) ≤ Z`, and
`a_j < Y` for every `j` with `x⁺_j < z`. -/
theorem targetD_congr {θ : ℝ} (hθ : 0 < θ) {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀)
    {D D' : PrimeData} (hD : Pos D) (hD' : Pos D') {Y z Z : ℝ} (h : DAgree D D' Y)
    (hY0 : 0 < Y) (hYz : Y ≤ z) (hZ : z + winH X₀ z ≤ Z)
    (hYA : ∀ n : ℝ, n ≤ Z → absorbY X₀ n ≤ Y)
    (hYγ : ∀ j, switchOn (swS θ X₀) j < z → constructionScale X₀ (swS θ X₀) j < Y) {x : ℝ} (hx : x ≤ z) :
    targetD θ X₀ D x = targetD θ X₀ D' x := by
  have hw := winH_isWin (X₀ := (X₀ : ℝ)) hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 : 1 ≤ X₀ := by exact_mod_cast (QueueMono.one_lt_of_logX hX0 hX).le
  have hA : AAgree (absSet X₀ D) (absSet X₀ D') Z := fun n hn =>
    absSet_iff_of_agree h (hYA n hn)
  have hN : ∀ x, x < Y → NCount X₀ D x = NCount X₀ D' x := fun x hx =>
    NCount_eq_of_agree h hD hD' hx
  have ha : ∀ k, 0 < constructionScale X₀ (swS θ X₀) k ∧ constructionScale X₀ (swS θ X₀) k ≤ switchOn (swS θ X₀) k :=
    fun k => ⟨(constructionScale_spec hX0 hX (le_swS θ _) k).2.1,
      (constructionScale_spec hX0 hX (le_swS θ _) k).2.2.1⟩
  have hγ := designedGammaN_congr (θ := θ) (κ := kappaParam X₀) (κ₀ := (kappa0Param X₀)) hX
    (switchOn_spacing _) hX1 (switchOn_zero_ge_swS _ _) ha
    ((add_win_le_add_win hw hY0 hYz).trans hZ) hN hA
  unfold targetD
  refine target_congr hX hZ hA (fun j hj => ?_) hx
  have hj' := hγ j (hYγ j hj)
  exact ⟨by simp only [alphaD, amplitudes, gammaD, hj'], hj'⟩

end BModel

end
