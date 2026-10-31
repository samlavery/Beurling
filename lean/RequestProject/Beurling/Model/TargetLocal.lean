module

public import RequestProject.Beurling.Model.Data

/-!
# Locality of the target (Lemma 3.2, adaptedness)

The target (6) at a height `x ≤ z` reads

* the absorbed set `A` only up to `z + z^{θ/2}` (an element `a` contributes to `ρ_A(v)` only for
  `u_a ≤ v ≤ a`, with `u_a + u_a^{θ/2} = a`);
* the oscillation only through the `α_j, γ_j` with `x⁺_j < z` (`R_j ≡ 0` on `(0, x⁺_j]`);
* the heights `γ_j` only through `N` below `a_j` and `A` below `a_j + a_j^{θ/2}`
  (Lemma 4.8: `γ_j` is read from `D̂_{<a_j}`), recursively.

`targetD_congr` combines these with the locality of the absorbed set and of `N`
(`Model/Data.lean`): the target of the prime data at heights `≤ z` only reads the primes of value
below a height `Y` with `y(n) ≤ Y` for `n ≤ z + z^{θ/2}` and `a_j < Y` for every switched-on `j`.
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

/-- `t ↦ t + t^b` is monotone on `[0, ∞)`. -/
lemma add_rpow_le_add_rpow {b s t : ℝ} (hb : 0 < b) (hs : 0 ≤ s) (hst : s ≤ t) :
    s + s ^ b ≤ t + t ^ b := by
  have := Real.rpow_le_rpow hs hst hb.le
  linarith

lemma absorbedBump_congr {θ : ℝ} (hθ : 0 < θ) {A A' : Set ℝ} {Z v : ℝ} (hA : AAgree A A' Z)
    (hvZ : v + v ^ (θ / 2) ≤ Z) (a : ℝ) :
    absorbedBump (θ / 2) A (uA θ) a v = absorbedBump (θ / 2) A' (uA θ) a v := by
  classical
  unfold absorbedBump
  by_cases haZ : (a : ℝ) ≤ Z
  · simp only [hA a haZ]
  · push_neg at haZ
    have hb : 0 < θ / 2 := by linarith
    have hnot : v ∉ Icc (uA θ a) (a : ℝ) := by
      rintro ⟨h1, h2⟩
      have hu0' : 0 ≤ uA θ a := solveU_nonneg _ _
      have hv0 : 0 ≤ v := hu0'.trans h1
      have := Real.rpow_nonneg hv0 (θ / 2)
      obtain ⟨hu0, hua⟩ := solveU_spec hb (show 0 ≤ a by linarith)
      have := add_rpow_le_add_rpow hb hu0 h1
      have : uA θ a + uA θ a ^ (θ / 2) = a := hua
      linarith
    simp only [Set.indicator_of_notMem hnot, ite_self]

lemma absorbedDensityCap_congr {θ : ℝ} (hθ : 0 < θ) {A A' : Set ℝ} {Z v : ℝ}
    (hA : AAgree A A' Z) (hvZ : v + v ^ (θ / 2) ≤ Z) :
    absorbedDensityCap (θ / 2) A (uA θ) v = absorbedDensityCap (θ / 2) A' (uA θ) v := by
  unfold absorbedDensityCap absorbedDensity
  congr 1
  exact tsum_congr (absorbedBump_congr hθ hA hvZ)

/-- On `(0, z]` the oscillation only reads the `α_j, γ_j` with `x⁺_j < z`. -/
lemma osc_congr_of {θ : ℝ} {α γ α' γ' xp : ℕ → ℝ} {z : ℝ}
    (h : ∀ j, xp j < z → α j = α' j ∧ γ j = γ' j) {x : ℝ} (hx : 0 < x) (hxz : x ≤ z) :
    osc θ α γ xp x = osc θ α' γ' xp x := by
  unfold osc
  refine tsum_congr fun j => ?_
  by_cases hj : xp j < x
  · rw [(h j (lt_of_lt_of_le hj hxz)).1, (h j (lt_of_lt_of_le hj hxz)).2]
  · push_neg at hj
    rw [oscTerm_eq_zero_of_le hx hj, oscTerm_eq_zero_of_le hx hj]

/-- **Locality of the target**: at heights `x ≤ z` the target only reads `A` on `[0, Z]`
(`z + z^{θ/2} ≤ Z`) and the oscillation parameters with `x⁺_j < z`. -/
theorem target_congr {X₀ : ℕ} (hX1 : 1 ≤ X₀) {κ θ : ℝ} (hθ : 0 < θ) {A A' : Set ℝ}
    {α γ α' γ' xp : ℕ → ℝ} {z Z : ℝ} (hZ : z + z ^ (θ / 2) ≤ Z) (hA : AAgree A A' Z)
    (hosc : ∀ j, xp j < z → α j = α' j ∧ γ j = γ' j) {x : ℝ} (hx : x ≤ z) :
    target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A (uA θ)) (osc θ α γ xp) x =
      target X₀ κ (countA A') (absorbedDensityCap (θ / 2) A' (uA θ)) (osc θ α' γ' xp) x := by
  have hX0 : (0 : ℝ) < X₀ := by exact_mod_cast hX1
  unfold target
  by_cases hlt : x < X₀
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]
    push_neg at hlt
    have hb : 0 < θ / 2 := by linarith
    have hx0 : 0 ≤ x := by linarith
    have hxZ : x ≤ Z := by
      have := Real.rpow_nonneg (hx0.trans hx) (θ / 2)
      linarith
    have hint : (∫ v in (X₀ : ℝ)..x, absorbedDensityCap (θ / 2) A (uA θ) v) =
        ∫ v in (X₀ : ℝ)..x, absorbedDensityCap (θ / 2) A' (uA θ) v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le hlt] at hv
      have hv0 : 0 ≤ v := by linarith [hv.1]
      exact absorbedDensityCap_congr hθ hA
        ((add_rpow_le_add_rpow hb hv0 (hv.2.trans hx)).trans hZ)
    rw [countA_congr hA hxZ, hint, osc_congr_of hosc (by linarith) hx,
      osc_congr_of hosc hX0 (hlt.trans hx)]

/-- `targetOf` is `target` with the solved `u_a`. -/
lemma targetOf_eq (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (α γ xp : ℕ → ℝ) :
    targetOf θ X₀ κ A (uA θ) α γ xp =
      target X₀ κ (countA A) (absorbedDensityCap (θ / 2) A (uA θ)) (osc θ α γ xp) := rfl

/-- **Locality of the designed heights** (Lemma 4.8: `γ_j` reads only the system on `[1, a_j)`):
if `N` agrees below `Y` and `A` agrees on `[0, Z]` with `Y + Y^{θ/2} ≤ Z`, then every `γ_j`
with `a_j < Y` agrees. -/
theorem designedGammaN_congr {N N' : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ) {X₀ : ℕ} {κ : ℝ}
    {A A' : Set ℝ} {κ₀ : ℝ} {xp a : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀)
    (hxp : (X₀ : ℝ) ≤ xp 0) (ha : ∀ k, 0 < a k ∧ a k ≤ xp k) {Y Z : ℝ}
    (hZ : Y + Y ^ (θ / 2) ≤ Z) (hN : ∀ x, x < Y → N x = N' x) (hA : AAgree A A' Z) :
    ∀ j, a j < Y → designedGammaN N θ X₀ κ A (uA θ) κ₀ xp a j =
      designedGammaN N' θ X₀ κ A' (uA θ) κ₀ xp a j := by
  have hb : 0 < θ / 2 := by linarith
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
  have hZj : a j + a j ^ (θ / 2) ≤ Z :=
    (add_rpow_le_add_rpow hb (ha j).1.le hj.le).trans hZ
  congr 1
  refine target_congr hX1 hθ hZj hA (fun i hi => ?_) hxa
  have hij : i < j := by
    by_contra hc
    push_neg at hc
    have := hsp.strictMono.monotone hc
    linarith [(ha j).2]
  have hiY : a i < Y := lt_of_le_of_lt (ha i).2 (lt_trans hi hj)
  have hγ := IH i hij hiY
  exact ⟨by simp only [amplitudes, hγ], hγ⟩

/-- **Lemma 3.2 (adaptedness), deterministic form**: under `DAgree D D' Y`, the targets of the
data agree at every height `x ≤ z`, provided `y(n) ≤ Y` for every `n ≤ Z`, `z + z^{θ/2} ≤ Z`, and
`a_j < Y` for every `j` with `x⁺_j < z`. -/
theorem targetD_congr {θ : ℝ} (hθ : 0 < θ) {X₀ : ℕ} (hX : 10 ^ 8 ≤ Real.log X₀)
    {D D' : PrimeData} (hD : Pos D) (hD' : Pos D') {Y z Z : ℝ} (h : DAgree D D' Y)
    (hY0 : 0 ≤ Y) (hYz : Y ≤ z) (hZ : z + z ^ (θ / 2) ≤ Z)
    (hYA : ∀ n : ℝ, n ≤ Z → absorbY X₀ n ≤ Y)
    (hYγ : ∀ j, switchOn X₀ j < z → constructionScale X₀ j < Y) {x : ℝ} (hx : x ≤ z) :
    targetD θ X₀ D x = targetD θ X₀ D' x := by
  have hb : 0 < θ / 2 := by linarith
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 : 1 ≤ X₀ := by exact_mod_cast (QueueMono.one_lt_of_logX hX0 hX).le
  have hA : AAgree (absSet X₀ D) (absSet X₀ D') Z := fun n hn =>
    absSet_iff_of_agree h (hYA n hn)
  have hN : ∀ x, x < Y → NCount X₀ D x = NCount X₀ D' x := fun x hx =>
    NCount_eq_of_agree h hD hD' hx
  have ha : ∀ k, 0 < constructionScale X₀ k ∧ constructionScale X₀ k ≤ switchOn X₀ k :=
    fun k => ⟨(constructionScale_spec hX0 hX k).2.1, (constructionScale_spec hX0 hX k).2.2.1⟩
  have hγ := designedGammaN_congr (κ := kappaParam X₀) (κ₀ := (kappa0Param X₀)) hθ
    (switchOn_spacing _) hX1 (switchOn_zero_ge _) ha
    ((add_rpow_le_add_rpow hb hY0 hYz).trans hZ) hN hA
  unfold targetD
  refine target_congr hX1 hθ hZ hA (fun j hj => ?_) hx
  have hj' := hγ j (hYγ j hj)
  exact ⟨by simp only [alphaD, amplitudes, gammaD, hj'], hj'⟩

end BModel

end
