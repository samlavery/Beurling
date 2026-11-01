module

public import RequestProject.Beurling.Basic
public import RequestProject.Beurling.GenLemma51

/-!
# Lemma 6.26, step (iv): the window count from the cluster event

Grid windows (Section 6, parameters at scale `x`): at a dyadic height `z = (X₀/2) 2^m`, with
`δ₁(z) = 2 (log z)^{-6}`, the grid windows are `[k δ₁, (k + 2) δ₁)`, `k ∈ ℤ`, with left end
`k δ₁ ∈ [z, 2z)`. The cluster event (Proposition 6.11) up to the height `Z` says that every grid
window at a dyadic height `X₀/2 ≤ z ≤ Z` holds at most `M(z)` elements of `N`
(`ClusterUpTo`).

* `count_le_of_cover`: an elementary covering count.
* `block_count_le`: the part of an interval `[a, b]` in one dyadic block `[w, 2w)` is covered by at
  most `(b - a)/(2δ₁(w)) + 3` grid windows (at height `w`, plus the last window at height `w/2`).
* `low_count_le_one`: below `X₀⁻` an interval of length `< 1` holds at most one element of `N`,
  since `N(v) = ⌊v⌋` there.
* `interval_count_le` (**step (iv)**): an interval `[a, b]` with `b - a < 1`, `b ≤ Z`, holds at
  most `1 + ((log b)^6/4 + 6) M` elements of `N`, if the grid windows at dyadic heights `≤ Z` hold
  at most `M` elements each. (The paper has `L^6/4 + 5`; the extra window comes from the cruder
  bookkeeping at the dyadic boundary.)
-/

@[expose] public section

open Set Finset

namespace Construction

/-- The grid spacing `δ₁(z) = 2 (log z)^{-6}`. -/
noncomputable def gridDelta (z : ℝ) : ℝ := 2 / Real.log z ^ 6

/-- The dyadic heights `(X₀/2) 2^m`, `m ≥ 0`. -/
def IsDyadicHeight (X₀ z : ℝ) : Prop := ∃ m : ℕ, z = X₀ / 2 * 2 ^ m

/-- The number of elements of `N` with value in `[a, b)`. -/
noncomputable def winCount (P : BeurlingSystem) (a b : ℝ) : ℕ :=
  {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e < b}.ncard

/-- **The cluster event up to the height `Z`** (Proposition 6.11, the event `E_cl`): every grid
window `[k δ₁(z), (k + 2) δ₁(z))`, `k δ₁(z) ∈ [z, 2z)`, at a dyadic height `X₀/2 ≤ z ≤ Z`, holds at
most `M` elements of `N`. -/
def ClusterUpTo (P : BeurlingSystem) (X₀ Z M : ℝ) : Prop :=
  ∀ z, IsDyadicHeight X₀ z → z ≤ Z → ∀ k : ℤ, z ≤ k * gridDelta z → k * gridDelta z < 2 * z →
    (winCount P (k * gridDelta z) ((k + 2) * gridDelta z) : ℝ) ≤ M

/-- An elementary covering count: if a finite set is covered by `n` finite sets of size `≤ M`, it
has at most `n M` elements. -/
lemma count_le_of_cover {α : Type*} {S : Set α} (n : ℕ) (W : ℕ → Set α) {M : ℝ}
    (hWfin : ∀ i, (W i).Finite) (hW : ∀ i < n, ((W i).ncard : ℝ) ≤ M)
    (hcov : ∀ e ∈ S, ∃ i < n, e ∈ W i) : (S.ncard : ℝ) ≤ n * M := by
  have hsub : S ⊆ ⋃ i ∈ Finset.range n, W i := fun e he => by
    obtain ⟨i, hi, hei⟩ := hcov e he
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hi)) hei
  have key : ∀ m ≤ n, ((⋃ i ∈ Finset.range m, W i).ncard : ℝ) ≤ m * M ∧
      (⋃ i ∈ Finset.range m, W i).Finite := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : (⋃ i ∈ Finset.range (m + 1), W i) = (⋃ i ∈ Finset.range m, W i) ∪ W m := by
        ext x; simp [Finset.range_add_one, or_comm]
      rw [e]
      refine ⟨?_, h2.union (hWfin m)⟩
      have := Set.ncard_union_le (⋃ i ∈ Finset.range m, W i) (W m)
      have h3 := hW m (by omega)
      push_cast
      calc (((⋃ i ∈ Finset.range m, W i) ∪ W m).ncard : ℝ)
          ≤ (⋃ i ∈ Finset.range m, W i).ncard + (W m).ncard := by exact_mod_cast this
        _ ≤ m * M + M := add_le_add h1 h3
        _ = (m + 1) * M := by ring
  obtain ⟨h1, h2⟩ := key n le_rfl
  exact le_trans (by exact_mod_cast Set.ncard_le_ncard hsub h2) h1

variable (P : BeurlingSystem)

lemma finite_win (a b : ℝ) : {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e < b}.Finite :=
  (P.finite_val_le b).subset fun _ he => le_of_lt he.2

lemma gridDelta_pos {z : ℝ} (hz : 1 < z) : 0 < gridDelta z := by
  unfold gridDelta; have := Real.log_pos hz; positivity

/-- `δ₁` is non-increasing in the height. -/
lemma gridDelta_anti {z w : ℝ} (hz : 1 < z) (hzw : z ≤ w) : gridDelta w ≤ gridDelta z := by
  unfold gridDelta
  have h1 := Real.log_pos hz
  have h2 := Real.log_le_log (by linarith) hzw
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_left₀ h1.le h2 6

lemma inv_two_gridDelta {z : ℝ} (hz : 1 < z) : 1 / (2 * gridDelta z) = Real.log z ^ 6 / 4 := by
  unfold gridDelta
  have := Real.log_pos hz
  field_simp
  ring

/-- **One dyadic block.** Let `w > 2` be a dyadic height with `w ≤ Z`, and suppose the cluster
event `ClusterUpTo P X₀ Z M`. Suppose either `w/2` is a dyadic height with `δ₁(w/2) ≤ w/2`, or
`a ≥ w + δ₁(w)`. Then the elements of `N` with value in `[a, b] ∩ [w, 2w)`, `a ≥ w`, number at
most `((b - a)/(2δ₁(w)) + 3) M`. -/
theorem block_count_le {X₀ Z M w a b : ℝ} (hcl : ClusterUpTo P X₀ Z M) (hM : 0 ≤ M)
    (hw : IsDyadicHeight X₀ w) (hwZ : w ≤ Z) (hw1 : 2 < w) (haw : w ≤ a) (hab : a ≤ b)
    (hcase : (IsDyadicHeight X₀ (w / 2) ∧ gridDelta (w / 2) ≤ w / 2) ∨ w + gridDelta w ≤ a) :
    ({e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < 2 * w}.ncard : ℝ) ≤
      ((b - a) / (2 * gridDelta w) + 3) * M := by
  classical
  set δ := gridDelta w with hδ
  have hδ0 : 0 < δ := gridDelta_pos (by linarith)
  set k0 : ℤ := ⌊a / δ⌋ with hk0
  have hk0a : (k0 : ℝ) * δ ≤ a := by
    have := Int.floor_le (a / δ); rwa [le_div_iff₀ hδ0] at this
  have hk0a' : a < ((k0 : ℝ) + 1) * δ := by
    have := Int.lt_floor_add_one (a / δ); rwa [div_lt_iff₀ hδ0] at this
  -- the first index used at height `w`
  set k1 : ℤ := if w ≤ (k0 : ℝ) * δ then k0 else k0 + 1 with hk1
  have hk1w : w ≤ (k1 : ℝ) * δ := by
    rw [hk1]; split_ifs with h
    · exact h
    · push_cast; linarith
  have hk1lo : a - δ ≤ (k1 : ℝ) * δ := by
    rw [hk1]; split_ifs <;> push_cast <;> linarith
  have hk1hi : (k1 : ℝ) * δ ≤ a + δ := by
    rw [hk1]; split_ifs <;> push_cast <;> linarith
  set n : ℕ := ⌊(b - a) / (2 * δ) + 1 / 2⌋₊ + 1 with hn
  have hq0 : 0 ≤ (b - a) / (2 * δ) := div_nonneg (by linarith) (by positivity)
  have hnle : (n : ℝ) ≤ (b - a) / (2 * δ) + 3 / 2 := by
    rw [hn]; push_cast
    have := Nat.floor_le (show 0 ≤ (b - a) / (2 * δ) + 1 / 2 by linarith)
    linarith
  set S := {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < 2 * w} with hS
  -- the windows: `i < n` at height `w`, and `i = n` the last window at height `w/2`
  set δ' := gridDelta (w / 2) with hδ'
  set k' : ℤ := ⌈w / δ'⌉ - 1 with hk'
  set C1 : Prop := IsDyadicHeight X₀ (w / 2) ∧ gridDelta (w / 2) ≤ w / 2 with hC1
  let W : ℕ → Set (ℕ →₀ ℕ) := fun i =>
    if i < n then {e | P.val e < 2 * w ∧ (((k1 + 2 * i : ℤ) : ℝ) * δ ≤ P.val e ∧
      P.val e < (((k1 + 2 * i : ℤ) : ℝ) + 2) * δ)}
    else if C1 then {e | (k' : ℝ) * δ' ≤ P.val e ∧ P.val e < ((k' : ℝ) + 2) * δ'} else ∅
  have hWfin : ∀ i, (W i).Finite := fun i => by
    simp only [W]; split_ifs
    · exact (finite_win P _ _).subset fun e he => he.2
    · exact finite_win P _ _
    · exact Set.finite_empty
  have key := count_le_of_cover (S := S) (n + 1) W (M := M) hWfin ?_ ?_
  · calc _ ≤ ((n + 1 : ℕ) : ℝ) * M := key
      _ ≤ ((b - a) / (2 * δ) + 3) * M := by
        apply mul_le_mul_of_nonneg_right _ hM; push_cast; linarith
  · -- each window holds at most `M` elements
    intro i hi
    by_cases hin : i < n
    · simp only [W, if_pos hin]
      set c : ℝ := ((k1 + 2 * i : ℤ) : ℝ) * δ with hc
      by_cases hlt : c < 2 * w
      · have hge : w ≤ c := by
          rw [hc]; push_cast
          have : (0 : ℝ) ≤ 2 * (i : ℝ) * δ := by positivity
          nlinarith
        have h1 := hcl w hw hwZ (k1 + 2 * i) hge hlt
        unfold winCount at h1
        refine le_trans ?_ h1
        have e2 : (((k1 + 2 * i : ℤ) : ℝ) + 2) * δ = (((k1 + 2 * i : ℤ) + 2 : ℤ) : ℝ) * δ := by
          push_cast; ring
        rw [e2]
        apply Nat.cast_le.mpr
        apply Set.ncard_le_ncard _ (finite_win P _ _)
        intro e he; exact he.2
      · have : {e : ℕ →₀ ℕ | P.val e < 2 * w ∧ (c ≤ P.val e ∧
            P.val e < (((k1 + 2 * i : ℤ) : ℝ) + 2) * δ)} = ∅ := by
          ext e; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h1, h2, -⟩; push_neg at hlt; linarith
        rw [this, Set.ncard_empty]; push_cast; exact hM
    · simp only [W, if_neg hin]
      split_ifs with hC
      · obtain ⟨hw2, hδw⟩ := hC
        have hδ'0 : 0 < δ' := gridDelta_pos (by linarith)
        have hk'1 : (k' : ℝ) * δ' < w := by
          rw [hk']; push_cast
          have := Int.ceil_lt_add_one (w / δ')
          rw [← lt_div_iff₀ hδ'0]; linarith
        have hk'2 : w ≤ ((k' : ℝ) + 1) * δ' := by
          rw [hk']; push_cast
          have := Int.le_ceil (w / δ')
          rw [← div_le_iff₀ hδ'0]; linarith
        have hge : w / 2 ≤ (k' : ℝ) * δ' := by nlinarith
        have h1 := hcl (w / 2) hw2 (by linarith) k' hge (by linarith)
        unfold winCount at h1
        exact h1
      · rw [Set.ncard_empty]; push_cast; exact hM
  · -- the covering
    rintro e ⟨hea, heb, hew⟩
    by_cases hx : (k1 : ℝ) * δ ≤ P.val e
    · set q := (P.val e - k1 * δ) / (2 * δ) with hq
      have hq0 : 0 ≤ q := div_nonneg (by linarith) (by positivity)
      set i := ⌊q⌋₊ with hi
      have hiq : (i : ℝ) ≤ q := Nat.floor_le hq0
      have hqi : q < i + 1 := Nat.lt_floor_add_one q
      have hin : i < n := by
        have : q ≤ (b - a) / (2 * δ) + 1 / 2 := by
          rw [hq, div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
          linarith
        rw [hn]
        have := Nat.floor_le_floor this
        omega
      refine ⟨i, by omega, ?_⟩
      simp only [W, if_pos hin, Set.mem_setOf_eq]
      rw [hq, le_div_iff₀ (by positivity)] at hiq
      rw [hq, div_lt_iff₀ (by positivity)] at hqi
      refine ⟨hew, ?_, ?_⟩ <;> push_cast <;> nlinarith
    · push_neg at hx
      -- then `k1 = k0 + 1`, so `k0 δ < w`, and the first case of `hcase` holds
      have hk1e : ¬ (w ≤ (k0 : ℝ) * δ) := by
        intro h
        have : k1 = k0 := by rw [hk1, if_pos h]
        rw [this] at hx; linarith
      have hk1eq : k1 = k0 + 1 := by rw [hk1, if_neg hk1e]
      have hC : C1 := by
        rcases hcase with h | h
        · exact h
        · exfalso; push_neg at hk1e; linarith
      refine ⟨n, by omega, ?_⟩
      simp only [W, lt_irrefl, if_false, if_pos hC, Set.mem_setOf_eq]
      obtain ⟨hw2, hδw⟩ := hC
      have hδ'0 : 0 < δ' := gridDelta_pos (by linarith)
      have hδδ : δ ≤ δ' := gridDelta_anti (by linarith) (by linarith)
      have hk'1 : (k' : ℝ) * δ' < w := by
        rw [hk']; push_cast
        have := Int.ceil_lt_add_one (w / δ')
        rw [← lt_div_iff₀ hδ'0]; linarith
      have hk'2 : w ≤ ((k' : ℝ) + 1) * δ' := by
        rw [hk']; push_cast
        have := Int.le_ceil (w / δ')
        rw [← div_le_iff₀ hδ'0]; linarith
      rw [hk1eq] at hx; push_cast at hx; push_neg at hk1e
      constructor <;> nlinarith

/-- **Below `X₀⁻`**: if `N(v) = ⌊v⌋` for `1 ≤ v < c`, an interval `[a, b]` with `b < a + 1`
holds at most one element of `N` with value `< c`. -/
theorem low_count_le_one {c a b : ℝ} (hfl : ∀ v, 1 ≤ v → v < c → P.N v = ⌊v⌋₊)
    (hab : b < a + 1) :
    ({e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < c}.ncard : ℝ) ≤ 1 := by
  classical
  set S := {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < c} with hS
  have hSfin : S.Finite := (P.finite_val_le b).subset fun e he => he.2.1
  rcases S.eq_empty_or_nonempty with h0 | hne
  · rw [h0, Set.ncard_empty]; norm_num
  obtain ⟨t0, ht0, hmax⟩ := hSfin.toFinset.exists_max_image P.val
    (by rwa [Set.Finite.toFinset_nonempty])
  rw [Set.Finite.mem_toFinset] at ht0
  set t := P.val t0
  have ht1 : 1 ≤ t := P.one_le_val t0
  have hSt : S ⊆ {e | P.val e ≤ t} := fun e he =>
    hmax e (by rw [Set.Finite.mem_toFinset]; exact he)
  have hNt : P.N t = ⌊t⌋₊ := hfl t ht1 ht0.2.2
  have htb : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor ht0.2.1
  have hfin_t := P.finite_val_le t
  by_cases ha : a ≤ 1
  · -- then `t ≤ b < 2`
    have hb2 : ⌊b⌋₊ ≤ 1 := by
      have : b < 2 := by linarith
      have := Nat.floor_lt' (n := 2) (by norm_num) |>.mpr (by exact_mod_cast this)
      omega
    calc (S.ncard : ℝ) ≤ ({e : ℕ →₀ ℕ | P.val e ≤ t}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hSt hfin_t
      _ = P.N t := rfl
      _ ≤ 1 := by rw [hNt]; exact_mod_cast htb.trans hb2
  · push_neg at ha
    set m : ℕ := ⌈a⌉₊ - 1 with hm
    have hceil : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    have hceil2 : a ≤ ⌈a⌉₊ := Nat.le_ceil a
    have hc2 : 2 ≤ ⌈a⌉₊ := by
      have : (1 : ℝ) < ⌈a⌉₊ := lt_of_lt_of_le ha hceil2
      exact_mod_cast this
    have hmR : (m : ℝ) = ⌈a⌉₊ - 1 := by rw [hm]; push_cast [Nat.cast_sub (by omega : 1 ≤ ⌈a⌉₊)]; ring
    set s := (m + a) / 2 with hs
    have hma : (m : ℝ) < a := by linarith
    have hs1 : 1 ≤ s := by
      have h2 : (2 : ℝ) ≤ ⌈a⌉₊ := by exact_mod_cast hc2
      have : (1 : ℝ) ≤ m := by rw [hmR]; linarith
      rw [hs]; linarith
    have hsa : s < a := by rw [hs]; linarith
    have hfls : ⌊s⌋₊ = m := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> rw [hs] <;> linarith
    have hNs : P.N s = m := by rw [hfl s hs1 (by linarith [ht0.1, ht0.2.2]), hfls]
    have hbm : ⌊b⌋₊ ≤ m + 1 := by
      have : b < (m : ℝ) + 2 := by linarith
      have := Nat.floor_lt' (n := m + 2) (by omega) |>.mpr (by push_cast; exact this)
      omega
    have hsub : S ⊆ {e | P.val e ≤ t} \ {e | P.val e ≤ s} := fun e he =>
      ⟨hSt he, fun h => by simp only [Set.mem_setOf_eq] at h; linarith [he.1]⟩
    have hss : {e : ℕ →₀ ℕ | P.val e ≤ s} ⊆ {e | P.val e ≤ t} := fun e he => by
      simp only [Set.mem_setOf_eq] at he ⊢; linarith [ht0.1]
    have h1 := Set.ncard_le_ncard hsub (hfin_t.diff)
    rw [Set.ncard_diff hss (P.finite_val_le s)] at h1
    have h2 : ({e : ℕ →₀ ℕ | P.val e ≤ t}.ncard : ℝ) = ⌊t⌋₊ := hNt
    have h3 : ({e : ℕ →₀ ℕ | P.val e ≤ s}.ncard : ℝ) = m := hNs
    have h4 : {e : ℕ →₀ ℕ | P.val e ≤ s}.ncard ≤ {e : ℕ →₀ ℕ | P.val e ≤ t}.ncard :=
      Set.ncard_le_ncard hss hfin_t
    have h5 : (S.ncard : ℝ) ≤ ({e : ℕ →₀ ℕ | P.val e ≤ t}.ncard : ℝ) -
        ({e : ℕ →₀ ℕ | P.val e ≤ s}.ncard : ℝ) := by
      rw [← Nat.cast_sub h4]; exact_mod_cast h1
    rw [h2, h3] at h5
    have : (⌊t⌋₊ : ℝ) ≤ m + 1 := by exact_mod_cast htb.trans hbm
    linarith

lemma exists_dyadic {X₀ x : ℝ} (hX : 0 < X₀) (hx : X₀ / 2 ≤ x) :
    ∃ m : ℕ, X₀ / 2 * 2 ^ m ≤ x ∧ x < X₀ / 2 * 2 ^ (m + 1) := by
  classical
  have hex : ∃ m : ℕ, x < X₀ / 2 * 2 ^ (m + 1) := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (x / (X₀ / 2)) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hm
    have : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using hx
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at this
    rwa [Nat.sub_add_cancel hpos] at this

lemma gridDelta_le {z : ℝ} (hz : Real.exp 2 ≤ z) : gridDelta z ≤ 1 / 32 := by
  have hz0 : 0 < z := lt_of_lt_of_le (Real.exp_pos 2) hz
  have hl : 2 ≤ Real.log z := by
    have := Real.log_le_log (Real.exp_pos 2) hz; rwa [Real.log_exp] at this
  unfold gridDelta
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ 6 ≤ Real.log z ^ 6 := pow_le_pow_left₀ (by norm_num) hl 6
  linarith

lemma div_two_gridDelta_le {x z b : ℝ} (hx : 0 ≤ x) (hz : 1 < z) (hzb : z ≤ b) :
    x / (2 * gridDelta z) ≤ x * (Real.log b ^ 6 / 4) := by
  rw [div_eq_mul_one_div, inv_two_gridDelta hz]
  apply mul_le_mul_of_nonneg_left _ hx
  have h1 := Real.log_pos hz
  have h2 := Real.log_le_log (by linarith) hzb
  have := pow_le_pow_left₀ h1.le h2 6
  linarith

/-- **Step (iv) of Lemma 6.26 (the window count)**. Let `X₀ ≥ 2e²`, `c ≥ X₀/2 + 1` with
`N(v) = ⌊v⌋` for `1 ≤ v < c` (the rational range below `X₀⁻`), and suppose the cluster event: every
grid window at a dyadic height `X₀/2 ≤ z ≤ Z` holds at most `M` elements of `N`. Then an interval
`[a, b]` with `b < a + 1` and `b ≤ Z` holds at most `1 + ((log b)^6/4 + 6) M` elements of `N`. -/
theorem interval_count_le {X₀ Z M c a b : ℝ} (hX : 2 * Real.exp 2 ≤ X₀) (hc : X₀ / 2 + 1 ≤ c)
    (hfl : ∀ v, 1 ≤ v → v < c → P.N v = ⌊v⌋₊) (hcl : ClusterUpTo P X₀ Z M) (hM : 0 ≤ M)
    (hab1 : b < a + 1) (hbZ : b ≤ Z) :
    ({e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b}.ncard : ℝ) ≤ 1 + (Real.log b ^ 6 / 4 + 6) * M := by
  classical
  have he2 : (7 : ℝ) < Real.exp 2 := by
    have := Real.add_one_le_exp 2
    have h3 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hX0 : 0 < X₀ := by linarith
  set S := {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b}
  set Slow := {e : ℕ →₀ ℕ | a ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < c}
  set a' := max a c with ha'
  set Shigh := {e : ℕ →₀ ℕ | a' ≤ P.val e ∧ P.val e ≤ b}
  have hfinb := P.finite_val_le b
  have hSsub : S ⊆ Slow ∪ Shigh := by
    rintro e ⟨h1, h2⟩
    by_cases h : P.val e < c
    · exact Or.inl ⟨h1, h2, h⟩
    · push_neg at h; exact Or.inr ⟨max_le h1 h, h2⟩
  have hlow := low_count_le_one P hfl hab1 (a := a)
  have hS : (S.ncard : ℝ) ≤ Slow.ncard + Shigh.ncard := by
    have h1 := Set.ncard_le_ncard hSsub ((hfinb.subset fun e he => he.2.1).union
      (hfinb.subset fun e he => he.2))
    have h2 := Set.ncard_union_le Slow Shigh
    exact_mod_cast h1.trans h2
  have hLb : 0 ≤ Real.log b ^ 6 / 4 := by positivity
  suffices hhigh : (Shigh.ncard : ℝ) ≤ (Real.log b ^ 6 / 4 + 6) * M by linarith
  by_cases hab' : b < a'
  · have : Shigh = ∅ := by
      ext e; simp only [Shigh, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩; linarith
    rw [this, Set.ncard_empty]; push_cast; positivity
  push_neg at hab'
  have ha'c : c ≤ a' := le_max_right _ _
  have ha'a : a ≤ a' := le_max_left _ _
  obtain ⟨m, hwm, hwm'⟩ := exists_dyadic hX0 (show X₀ / 2 ≤ a' by linarith)
  set w := X₀ / 2 * 2 ^ m with hw
  have hw2 : X₀ / 2 * 2 ^ (m + 1) = 2 * w := by rw [hw, pow_succ]; ring
  rw [hw2] at hwm'
  have hwX : X₀ / 2 ≤ w := by
    rw [hw]; have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num); nlinarith
  have hwe : Real.exp 2 ≤ w := by linarith
  have hwd : IsDyadicHeight X₀ w := ⟨m, rfl⟩
  have hδw := gridDelta_le hwe
  have hcase1 : (IsDyadicHeight X₀ (w / 2) ∧ gridDelta (w / 2) ≤ w / 2) ∨
      w + gridDelta w ≤ a' := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · right
      have : w = X₀ / 2 := by rw [hw, h0]; simp
      linarith
    · left
      refine ⟨⟨m - 1, ?_⟩, ?_⟩
      · rw [hw]
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
        ring
      · have hm1 : (2 : ℝ) ≤ 2 ^ m := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hpos
        have hwX' : X₀ ≤ w := by rw [hw]; nlinarith
        have := gridDelta_le (z := w / 2) (by linarith)
        linarith
  set B1 := {e : ℕ →₀ ℕ | a' ≤ P.val e ∧ P.val e ≤ min b (2 * w) ∧ P.val e < 2 * w}
  set B2 := {e : ℕ →₀ ℕ | 2 * w ≤ P.val e ∧ P.val e ≤ b ∧ P.val e < 2 * (2 * w)}
  have hsub2 : Shigh ⊆ B1 ∪ B2 := by
    rintro e ⟨h1, h2⟩
    by_cases h : P.val e < 2 * w
    · exact Or.inl ⟨h1, le_min h2 h.le, h⟩
    · push_neg at h; exact Or.inr ⟨h, h2, by linarith⟩
  have hB1 := block_count_le P hcl hM hwd (by linarith) (by linarith) hwm
    (le_min hab' hwm'.le) hcase1
  have hHigh : (Shigh.ncard : ℝ) ≤ B1.ncard + B2.ncard := by
    have h1 := Set.ncard_le_ncard hsub2 ((hfinb.subset fun e he => he.2.1.trans (min_le_left _ _)).union
      (hfinb.subset fun e he => he.2.1))
    have h2 := Set.ncard_union_le B1 B2
    exact_mod_cast h1.trans h2
  by_cases hb2w : b < 2 * w
  · have hB2 : B2 = ∅ := by
      ext e; simp only [B2, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    rw [hB2, Set.ncard_empty] at hHigh
    have hmin : min b (2 * w) = b := min_eq_left hb2w.le
    have h3 := div_two_gridDelta_le (x := b - a') (by linarith) (by linarith) (hwm.trans hab')
    have h4 : (b - a') * (Real.log b ^ 6 / 4) ≤ Real.log b ^ 6 / 4 := by
      have : b - a' ≤ 1 := by linarith
      nlinarith
    push_cast at hHigh
    calc (Shigh.ncard : ℝ) ≤ B1.ncard := by linarith
      _ ≤ ((min b (2 * w) - a') / (2 * gridDelta w) + 3) * M := hB1
      _ = ((b - a') / (2 * gridDelta w) + 3) * M := by rw [hmin]
      _ ≤ (Real.log b ^ 6 / 4 + 6) * M := by
        apply mul_le_mul_of_nonneg_right _ hM; linarith
  · push_neg at hb2w
    have hmin : min b (2 * w) = 2 * w := min_eq_right hb2w
    have hwd2 : IsDyadicHeight X₀ (2 * w) := ⟨m + 1, by rw [← hw2]⟩
    have hB2 := block_count_le P hcl hM hwd2 (by linarith) (by linarith) le_rfl hb2w
      (Or.inl ⟨by rw [show 2 * w / 2 = w by ring]; exact hwd,
        by rw [show 2 * w / 2 = w by ring]; linarith⟩)
    have h3 := div_two_gridDelta_le (x := 2 * w - a') (by linarith) (by linarith)
      (hwm.trans hab')
    have h3'' := div_two_gridDelta_le (x := b - 2 * w) (b := b) (by linarith) (by linarith : 1 < 2 * w)
      hb2w
    have h4 : (2 * w - a') * (Real.log b ^ 6 / 4) + (b - 2 * w) * (Real.log b ^ 6 / 4) ≤
        Real.log b ^ 6 / 4 := by
      have : b - a' ≤ 1 := by linarith
      nlinarith
    calc (Shigh.ncard : ℝ) ≤ B1.ncard + B2.ncard := hHigh
      _ ≤ ((min b (2 * w) - a') / (2 * gridDelta w) + 3) * M +
          ((b - 2 * w) / (2 * gridDelta (2 * w)) + 3) * M := add_le_add hB1 hB2
      _ = ((2 * w - a') / (2 * gridDelta w) + 3) * M +
          ((b - 2 * w) / (2 * gridDelta (2 * w)) + 3) * M := by rw [hmin]
      _ ≤ (Real.log b ^ 6 / 4 + 6) * M := by
        rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ hM; linarith

/-- **Step (iv) of Lemma 6.26 in the form used by the divisor trick**: under the hypotheses of
`interval_count_le` with `u + h ≤ h Z` (so every window `I_d` lies below `Z`), for every element
`d` with `val d > h ≥ 1`, the window `I_d = [u/d, (u + h)/d]` holds at most
`1 + ((log (u + h))^6/4 + 6) M` elements of `N`. -/
theorem window_count_divisor {X₀ Z M c u h : ℝ} (hX : 2 * Real.exp 2 ≤ X₀)
    (hc : X₀ / 2 + 1 ≤ c) (hfl : ∀ v, 1 ≤ v → v < c → P.N v = ⌊v⌋₊)
    (hcl : ClusterUpTo P X₀ Z M) (hM : 0 ≤ M) (hh : 1 ≤ h) (hu : 0 ≤ u)
    (huZ : u + h ≤ h * Z) (d : ℕ →₀ ℕ) (hd : h < P.val d) :
    ({m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h}.ncard : ℝ) ≤
      1 + (Real.log (u + h) ^ 6 / 4 + 6) * M := by
  have hd0 : 0 < P.val d := by linarith
  have eset : {m : ℕ →₀ ℕ | u ≤ P.val d * P.val m ∧ P.val d * P.val m ≤ u + h} =
      {m : ℕ →₀ ℕ | u / P.val d ≤ P.val m ∧ P.val m ≤ (u + h) / P.val d} := by
    ext m; simp only [Set.mem_setOf_eq]
    rw [div_le_iff₀ hd0, le_div_iff₀ hd0, mul_comm (P.val m)]
  rw [eset]
  set b := (u + h) / P.val d
  by_cases hb1 : b < 1
  · have : {m : ℕ →₀ ℕ | u / P.val d ≤ P.val m ∧ P.val m ≤ b} = ∅ := by
      ext m; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, h2⟩; linarith [P.one_le_val m]
    rw [this, Set.ncard_empty]; push_cast
    have : 0 ≤ (Real.log (u + h) ^ 6 / 4 + 6) * M := by positivity
    linarith
  push_neg at hb1
  have hbZ : b ≤ Z := by
    rw [div_le_iff₀ hd0]
    have hZ0 : 0 ≤ Z := by nlinarith
    nlinarith
  have hlen : b < u / P.val d + 1 := by
    rw [div_add_one hd0.ne', div_lt_div_iff_of_pos_right hd0]; linarith
  have h1 := interval_count_le P hX hc hfl hcl hM hlen hbZ
  refine h1.trans ?_
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlb' : Real.log b ≤ Real.log (u + h) := by
    apply Real.log_le_log (by linarith)
    rw [div_le_iff₀ hd0]; nlinarith
  have := pow_le_pow_left₀ hlb hlb' 6
  have : (Real.log b ^ 6 / 4 + 6) * M ≤ (Real.log (u + h) ^ 6 / 4 + 6) * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM
  linarith

/-- The constant of step (iv): `1 + ((log(u + h))^6/4 + 6) M ≤ C_d := M L^6/2` for `L = log u ≥ 10`,
`0 ≤ h ≤ u`, `M ≥ 1`. -/
theorem window_const_le {M u h : ℝ} (hM : 1 ≤ M) (hu0 : 0 < u) (hL : 10 ≤ Real.log u)
    (hh : 0 ≤ h) (hhu : h ≤ u) : 1 + (Real.log (u + h) ^ 6 / 4 + 6) * M ≤ M * Real.log u ^ 6 / 2 := by
  set L := Real.log u
  have hl : Real.log (u + h) ≤ L + 1 := by
    have h2 : Real.log (u + h) ≤ Real.log (2 * u) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hl0 : 0 ≤ Real.log (u + h) := Real.log_nonneg (by
    have := Real.add_one_le_exp L
    rw [Real.exp_log hu0] at this; linarith)
  have h6 : Real.log (u + h) ^ 6 ≤ (11 / 10 * L) ^ 6 :=
    pow_le_pow_left₀ hl0 (by linarith) 6
  have h116 : (11 / 10 * L) ^ 6 ≤ 18 / 10 * L ^ 6 := by
    rw [mul_pow]
    have : (11 / 10 : ℝ) ^ 6 ≤ 18 / 10 := by norm_num
    have : 0 ≤ L ^ 6 := by positivity
    nlinarith
  have hL6 : (10 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
  nlinarith

end Construction

end
