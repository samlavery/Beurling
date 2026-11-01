module

public import RequestProject.Beurling.Construction.Window

/-!
# Two grid windows cover a short window (proof of Corollary 6.12)

The proof of Corollary 6.12 covers a cofactor window `[w, w + δ)` with `w > X₀⁻ - 1` and
`δ ≤ 2 (log w)^{-6}` by at most two grid windows of the cluster event: one at the dyadic height `z`
of `w`, or, if no grid point of height `z` lies in `[z, w]`, the first window at height `z` and the
last one at height `z/2` (grid windows belong to the dyadic height of their left end, correction
#75).

* `Queue6.two_window_cover` : on `ClusterUpTo P X₀ Z M`, such a window holds at most `2M`
  elements of `𝒩`.
-/

@[expose] public section

open Set Real Construction

namespace Queue6

variable (P : BeurlingSystem)

lemma win_subset {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e < b} ⊆ {e : ℕ →₀ ℕ | c ≤ P.val e ∧ P.val e < d} :=
  fun _ he => ⟨hca.trans he.1, lt_of_lt_of_le he.2 hbd⟩

/-- **Two grid windows cover a short window** (proof of Corollary 6.12). -/
theorem two_window_cover {X₀ Z M w δ : ℝ} (hX : 100 ≤ X₀) (hM : 0 ≤ M)
    (hcl : ClusterUpTo P X₀ Z M) (hw : 3 * X₀ / 4 ≤ w) (hwZ : w ≤ Z)
    (hδ : δ ≤ 2 / Real.log w ^ 6) :
    (({e : ℕ →₀ ℕ | w ≤ P.val e ∧ P.val e < w + δ}.ncard : ℕ) : ℝ) ≤ 2 * M := by
  classical
  have hX0 : 0 < X₀ := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_dyadic hX0 (by linarith : X₀ / 2 ≤ w)
  set z := X₀ / 2 * 2 ^ m with hz
  have hz50 : 50 ≤ z := by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    rw [hz]; nlinarith
  have he2 : Real.exp 2 ≤ z := by
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    linarith
  have hzd : IsDyadicHeight X₀ z := ⟨m, rfl⟩
  have hzw : z ≤ w := hm1
  have hw2 : w < 2 * z := by rw [hz]; rw [pow_succ] at hm2; linarith
  set δ1 := gridDelta z
  have hδ1 : 0 < δ1 := gridDelta_pos (by linarith)
  have hδ1s : δ1 ≤ 1 / 32 := gridDelta_le he2
  have hδδ : δ ≤ δ1 := by
    refine hδ.trans ?_
    have := gridDelta_anti (z := z) (w := w) (by linarith) hzw
    exact this
  have hfin : ∀ a b : ℝ, {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e < b}.Finite :=
    fun a b => finite_win P a b
  have hwin : ∀ (u : ℝ) (k : ℤ), IsDyadicHeight X₀ u → u ≤ Z → u ≤ k * gridDelta u →
      k * gridDelta u < 2 * u → ∀ a b : ℝ, k * gridDelta u ≤ a → b ≤ (k + 2) * gridDelta u →
      (({e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e < b}.ncard : ℕ) : ℝ) ≤ M := by
    intro u k hu huZ h1 h2 a b ha hb
    refine le_trans ?_ (hcl u hu huZ k h1 h2)
    unfold winCount
    exact_mod_cast Set.ncard_le_ncard (win_subset P ha hb) (hfin _ _)
  set k := ⌊w / δ1⌋ with hk
  have hk1 : (k : ℝ) * δ1 ≤ w := by
    have := Int.floor_le (w / δ1); rwa [le_div_iff₀ hδ1] at this
  have hk2 : w < ((k : ℝ) + 1) * δ1 := by
    have := Int.lt_floor_add_one (w / δ1); rwa [div_lt_iff₀ hδ1] at this
  have ek : ((k : ℝ) + 2) * δ1 = ((k : ℝ) + 1) * δ1 + δ1 := by ring
  by_cases hA : z ≤ (k : ℝ) * δ1
  · have := hwin z k hzd (hzw.trans hwZ) hA (by linarith) w (w + δ) hk1 (by linarith)
    linarith
  · push_neg at hA
    -- `m ≥ 1`: otherwise `w < X₀/2 + δ₁`
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso
        rw [h] at hz
        simp at hz
        have : w < z + δ1 := by nlinarith
        rw [hz] at this
        linarith
      · exact h
    have hzd2 : IsDyadicHeight X₀ (z / 2) := ⟨m - 1, by
      rw [hz]
      have : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hm0]
      rw [this]; ring⟩
    set δ2 := gridDelta (z / 2)
    have hδ2 : δ1 ≤ δ2 := gridDelta_anti (by linarith) (by linarith)
    have hδ2s : δ2 ≤ 1 / 32 := gridDelta_le (by
      have : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      linarith)
    have hδ2p : 0 < δ2 := by linarith
    -- the first window at height `z`
    set k1 := ⌈z / δ1⌉ with hk1def
    have hk11 : z ≤ (k1 : ℝ) * δ1 := by
      have := Int.le_ceil (z / δ1); rwa [div_le_iff₀ hδ1] at this
    have hk12 : (k1 : ℝ) * δ1 < z + δ1 := by
      have := Int.ceil_lt_add_one (z / δ1)
      have h' : (k1 : ℝ) - 1 < z / δ1 := by rw [hk1def]; linarith
      rw [lt_div_iff₀ hδ1] at h'
      linarith
    -- the last window at height `z/2`
    set k2 := ⌈z / δ2⌉ - 1 with hk2def
    have hk21 : z ≤ ((k2 : ℝ) + 1) * δ2 := by
      have := Int.le_ceil (z / δ2)
      rw [div_le_iff₀ hδ2p] at this
      rw [hk2def]; push_cast; linarith
    have hk22 : (k2 : ℝ) * δ2 < z := by
      have := Int.ceil_lt_add_one (z / δ2)
      rw [hk2def]; push_cast
      have h' : (⌈z / δ2⌉ : ℝ) - 1 < z / δ2 := by linarith
      rwa [lt_div_iff₀ hδ2p] at h'
    have hw1 : w < z + δ1 := by
      have : (k : ℝ) + 1 ≤ k1 := by
        have h1 : (k : ℝ) < k1 := by
          by_contra hc; push_neg at hc
          have := mul_le_mul_of_nonneg_right hc hδ1.le
          linarith
        have : k + 1 ≤ k1 := by exact_mod_cast h1
        exact_mod_cast this
      have := mul_le_mul_of_nonneg_right this hδ1.le
      linarith
    have hsplit : {e : ℕ →₀ ℕ | w ≤ P.val e ∧ P.val e < w + δ} ⊆
        {e : ℕ →₀ ℕ | w ≤ P.val e ∧ P.val e < (k1 : ℝ) * δ1} ∪
          {e : ℕ →₀ ℕ | (k1 : ℝ) * δ1 ≤ P.val e ∧ P.val e < w + δ} := by
      intro e he
      rcases lt_or_ge (P.val e) ((k1 : ℝ) * δ1) with h | h
      · left; exact ⟨he.1, h⟩
      · right; exact ⟨h, he.2⟩
    have e2 : ((k2 : ℝ) + 1) * δ2 = (k2 : ℝ) * δ2 + δ2 := by ring
    have e3 : ((k2 : ℝ) + 2) * δ2 = ((k2 : ℝ) + 1) * δ2 + δ2 := by ring
    have e4 : ((k1 : ℝ) + 2) * δ1 = (k1 : ℝ) * δ1 + 2 * δ1 := by ring
    have hc1 := hwin (z / 2) k2 hzd2 (by linarith) (by linarith) (by linarith) w
      ((k1 : ℝ) * δ1) (by linarith) (by linarith)
    have hc2 := hwin z k1 hzd (hzw.trans hwZ) hk11 (by linarith) ((k1 : ℝ) * δ1) (w + δ) le_rfl
      (by linarith)
    have := (Set.ncard_le_ncard hsplit ((hfin _ _).union (hfin _ _))).trans
      (Set.ncard_union_le _ _)
    have : (({e : ℕ →₀ ℕ | w ≤ P.val e ∧ P.val e < w + δ}.ncard : ℕ) : ℝ) ≤
        (({e : ℕ →₀ ℕ | w ≤ P.val e ∧ P.val e < (k1 : ℝ) * δ1}.ncard : ℕ) : ℝ) +
          (({e : ℕ →₀ ℕ | (k1 : ℝ) * δ1 ≤ P.val e ∧ P.val e < w + δ}.ncard : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith

end Queue6

end
