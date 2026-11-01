module

public import RequestProject.Beurling.RankFull.WindowModel
public import RequestProject.Beurling.RankFull.TypeUnionFormal
public import RequestProject.Beurling.RankFull.RankinRows

/-!
# The skeleton of a configuration and the reduction `ConfigSkeletonReduction` (Lemma 6.21(ii))

For a configuration `(C, B)` (Section 6.7: `B ⊆ S(J)` rank-full of rank `r`, `C ⊆ B` a minimum
cover) in the window model, its **skeleton** (s1)–(s4) is `cfgSkel`:
* the rows of `B` are listed (`tupleOf`), the greedy pivots are those of `Config.pivs`, the
  `i`-th pivot being the `i`-th earliest, and the rows are re-indexed by their pivots through a
  permutation `σ` with a non-zero Leibniz term (`exists_perm_support`) — row `i` is matched to
  pivot `i`;
* (s1) `C'`: the indices of the rows of `C`;
* (s2) `lab`: the labels of the pivots, the label of a prime of `P(C)` being its decision rank in
  `P(C)` (earliest first);
* (s3) `ex y i`: the exponent of the `i`-th pivot in row `y` (for `y ∈ C'`, else `0`);
* (s4) for `y ∉ C'`: the monomial of row `y` in the labels and its rigid tail.

* `RankFull.Config.cfgSkel_mem` : the skeleton of a configuration lies in the index sets
  (s1)–(s4) (`CSet`, `labSet`, `ExOK`, `s4Set` with `admGen`);
* `RankFull.Config.configCount_le_skel` : the reduction, pathwise, for one window set;
* `RankFull.Config.configSkeletonReduction` : **`ConfigSkeletonReduction`** for the window model,
with `X = cfgSkelCount D r₀ 0 0` (the number of configurations with a given skeleton; the same
family for every `(j, k)`, as `theorem_6_23a_all` requires) and the (s4) data in
`admGen (r₀D) (k+1) D X₀ τl (2z+1)`, under the model hypotheses: prime values `≥ 1`, windows in
`(-∞, 2z+1]`, and the label bound `τl_ℓ ≤ q_n` whenever `ℓ ≤ #{decided slots before n}` (the
label of rank `ℓ` has value at least `τ_ℓ`, as the primes are in distinct slots).
-/

@[expose] public section

open Finset BSCert.StageRows
open scoped ENNReal Classical

namespace RankFull.Config

variable {N : ℕ}

/-! ## Facts about the window sets -/

lemma mem_windowVecs {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {v : Fin N → ℕ} (hv : v ∈ windowVecs dec q X₀ D Dmax Jw) :
    ∃ d, (v, d) ∈ windowElems dec q X₀ D Dmax Jw ∧ v ≠ 0 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨p.2, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩

/-- The rigid tail of a vector of `S(J)` (unique by (V1)). -/
noncomputable def tailOf (dec : Finset (Fin N)) (q : Fin N → ℝ) (X₀ D Dmax : ℕ) (Jw : Set ℝ)
    (v : Fin N → ℕ) : ℕ :=
  if h : ∃ d, (v, d) ∈ windowElems dec q X₀ D Dmax Jw then Classical.choose h else 0

lemma tailOf_mem {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {v : Fin N → ℕ} (hv : v ∈ windowVecs dec q X₀ D Dmax Jw) :
    (v, tailOf dec q X₀ D Dmax Jw v) ∈ windowElems dec q X₀ D Dmax Jw := by
  obtain ⟨d, hd, -⟩ := mem_windowVecs hv
  have h : ∃ d, (v, d) ∈ windowElems dec q X₀ D Dmax Jw := ⟨d, hd⟩
  unfold tailOf; rw [dif_pos h]; exact Classical.choose_spec h

lemma windowVecs_deg {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {v : Fin N → ℕ} (hv : v ∈ windowVecs dec q X₀ D Dmax Jw) : Covers.deg v ≤ D := by
  obtain ⟨d, hd, -⟩ := mem_windowVecs hv
  exact (Finset.mem_filter.mp hd).2.2.1

lemma windowVecs_supp {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {v : Fin N → ℕ} (hv : v ∈ windowVecs dec q X₀ D Dmax Jw) : ∀ n, v n ≠ 0 → n ∈ dec := by
  obtain ⟨d, hd, -⟩ := mem_windowVecs hv
  exact (Finset.mem_filter.mp hd).2.1

/-! ## The skeleton of a configuration -/

/-- The rows of `B` as a tuple. -/
noncomputable def tupleOf (B : Finset (Fin N → ℕ)) : Fin B.card → (Fin N → ℕ) :=
  fun i => ((B.equivFin).symm i : Fin N → ℕ)

lemma tupleOf_mem (B : Finset (Fin N → ℕ)) (i : Fin B.card) : tupleOf B i ∈ B :=
  ((B.equivFin).symm i).2

lemma tupleOf_injective (B : Finset (Fin N → ℕ)) : Function.Injective (tupleOf B) := by
  intro i j h
  exact (B.equivFin).symm.injective (Subtype.ext h)

lemma tupleOf_surj (B : Finset (Fin N → ℕ)) {v : Fin N → ℕ} (hv : v ∈ B) :
    ∃ i, tupleOf B i = v :=
  ⟨B.equivFin ⟨v, hv⟩, by simp [tupleOf]⟩

lemma tupleOf_li {B : Finset (Fin N → ℕ)} (hB : LinearIndepOn ℚ Covers.vq (B : Set (Fin N → ℕ))) :
    LinearIndependent ℚ (fun i => Covers.vq (tupleOf B i)) := by
  have h : LinearIndependent ℚ (fun x : B => Covers.vq (x : Fin N → ℕ)) := hB
  exact h.comp _ (B.equivFin).symm.injective

/-- The skeleton index type `(r, C', lab, ex, s4)`. -/
abbrev SkelIdx (D r₀ : ℕ) :=
  Σ r : ℕ, Σ C : Finset (Fin r),
    Finset (Fin (C.card * D)) × (Fin r → Fin r → ℕ) × (Fin r → (Fin (r₀ * D) → ℕ) × ℕ)

/-- The label of a slot `n`: its decision rank in `P(C)` (earliest first). -/
noncomputable def lbl (C : Finset (Fin N → ℕ)) (n : Fin N) : ℕ :=
  ((Covers.P C).filter (· < n)).card

/-- The pivot slots (the `j`-th earliest pivot) of a tuple with `k` pivots. -/
noncomputable def pivSlot {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k)
    (j : Fin k) : Fin N :=
  colSlot t ((pivs t).orderEmbOfFin hk (Fin.rev j))

lemma pattern_eq {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) (i j : Fin k) :
    pattern t i j = t i (pivSlot t hk j) := by
  simp [pattern, hk, pivSlot]

lemma pivSlot_injective {k : ℕ} (t : Fin k → (Fin N → ℕ)) (hk : (pivs t).card = k) :
    Function.Injective (pivSlot t hk) := by
  intro a b h
  unfold pivSlot colSlot at h
  have h1 := ((colSupp t).orderEmbOfFin rfl).injective h
  have h2 := Fin.rev_injective h1
  have h3 := ((pivs t).orderEmbOfFin hk).injective h2
  exact Fin.rev_injective h3

/-- **The skeleton of a configuration** `(C, B)`. -/
noncomputable def cfgSkel (D r₀ : ℕ) (tail : (Fin N → ℕ) → ℕ)
    (CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)) : SkelIdx D r₀ :=
  let C := CB.1
  let B := CB.2
  let t := tupleOf B
  if h : LinearIndependent ℚ (fun i => Covers.vq (t i)) then
    let hk := card_pivs h
    let σ := Classical.choose (exists_perm_support (pattern t) (skel_mem h).1)
    let C' : Finset (Fin B.card) := univ.filter fun i => t (σ i) ∈ C
    ⟨B.card, C',
      (univ.filter fun ℓ : Fin (C'.card * D) => ∃ j, lbl C (pivSlot t hk j) = ℓ.val,
       fun y i => if y ∈ C' then t (σ y) (pivSlot t hk i) else 0,
       fun y => if y ∈ C' then (0, 0) else
        (fun ℓ : Fin (r₀ * D) =>
          ∑ n ∈ (Covers.P C).filter (fun n => lbl C n = ℓ.val), t (σ y) n,
         tail (t (σ y))))⟩
  else ⟨0, ∅, ∅, 0, 0⟩

/-- The configurations of `S` (as in `configCount`). -/
noncomputable def configs (r₀ j k : ℕ) (S : Finset (Fin N → ℕ)) :
    Finset (Finset (Fin N → ℕ) × Finset (Fin N → ℕ)) :=
  (S.powerset ×ˢ S.powerset).filter (IsConfig r₀ j k S)

lemma configCount_eq (r₀ j k : ℕ) (S : Finset (Fin N → ℕ)) :
    configCount r₀ j k S = (configs r₀ j k S).card := by
  unfold configCount configs; rfl

/-- The skeleton counts `X(r, C', lab, ex, s4)`: the number of configurations
(`configs r₀ j k S`) whose skeleton is `(r, C', lab, ex, s4)`. The reduction uses `j = k = 0`
(every configuration; `configs_mono`), so that one family `X` serves every `(j, k)`. -/
noncomputable def cfgSkelCount (D r₀ j k : ℕ) (tail : (Fin N → ℕ) → ℕ) (S : Finset (Fin N → ℕ))
    (r : ℕ) (C : Finset (Fin r)) (lab : Finset (Fin (C.card * D))) (ex : Fin r → Fin r → ℕ)
    (s4 : Fin r → (Fin (r₀ * D) → ℕ) × ℕ) : ℝ≥0∞ :=
  ((configs r₀ j k S).filter fun CB => cfgSkel D r₀ tail CB = ⟨r, C, lab, ex, s4⟩).card

/-! ## The components of the skeleton lie in the index sets -/

section Components

variable {B C : Finset (Fin N → ℕ)}

lemma card_supp_le_deg (v : Fin N → ℕ) : (Covers.supp v).card ≤ Covers.deg v := by
  unfold Covers.supp Covers.deg
  calc (univ.filter fun i => v i ≠ 0).card = ∑ i ∈ univ.filter (fun i => v i ≠ 0), 1 := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => v i ≠ 0), v i :=
        Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, v i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma card_P_le {D : ℕ} (hD : ∀ v ∈ C, Covers.deg v ≤ D) : (Covers.P C).card ≤ C.card * D := by
  unfold Covers.P
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ v ∈ C, (Covers.supp v).card ≤ ∑ _v ∈ C, D :=
        Finset.sum_le_sum fun v hv => (card_supp_le_deg v).trans (hD v hv)
    _ = C.card * D := by rw [Finset.sum_const, smul_eq_mul]

lemma lbl_lt {n : Fin N} (hn : n ∈ Covers.P C) : lbl C n < (Covers.P C).card := by
  unfold lbl
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hn
  simp at this

lemma lbl_strictMono {n n' : Fin N} (hn : n ∈ Covers.P C) (hnn' : n < n') :
    lbl C n < lbl C n' := by
  unfold lbl
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hnn'⟩
  · have := h (Finset.mem_filter.mpr ⟨hn, hnn'⟩)
    simp at this

lemma lbl_injOn : Set.InjOn (lbl C) (Covers.P C : Set (Fin N)) := by
  intro n hn n' hn' h
  rcases lt_trichotomy n n' with h1 | h1 | h1
  · exact absurd h (ne_of_lt (lbl_strictMono hn h1))
  · exact h1
  · exact absurd h (ne_of_gt (lbl_strictMono hn' h1))

lemma lbl_le_dec {dec : Finset (Fin N)} (hPC : Covers.P C ⊆ dec) (n : Fin N) :
    lbl C n ≤ (dec.filter (· < n)).card :=
  Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hPC hx.1, hx.2⟩

end Components

/-- The (s4) datum of a row of `R` lies in `admGen` (Lemma 6.21(ii), (s4)). -/
lemma s4_mem {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ} {r₀ k : ℕ}
    {τl : Fin (r₀ * D) → ℝ} {z : ℝ} (hq1 : ∀ n ∈ dec, 1 ≤ q n) (hJz : Jw ⊆ Set.Iic (2 * z + 1))
    (hτ0 : ∀ ℓ, 0 ≤ τl ℓ)
    (hτ : ∀ n ∈ dec, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ (dec.filter (· < n)).card → τl ℓ ≤ q n)
    {C : Finset (Fin N → ℕ)} (hPCdec : Covers.P C ⊆ dec) (hPCcard : (Covers.P C).card ≤ r₀ * D)
    {v : Fin N → ℕ} (hv : v ∈ windowVecs dec q X₀ D Dmax Jw)
    (hvP : ∀ n, v n ≠ 0 → n ∈ Covers.P C) (hk1 : k + 1 ≤ Covers.deg v) :
    ((fun ℓ : Fin (r₀ * D) => ∑ n ∈ (Covers.P C).filter (fun n => lbl C n = ℓ.val), v n),
      tailOf dec q X₀ D Dmax Jw v) ∈ admGen (r₀ * D) (k + 1) D X₀ τl (2 * z + 1) := by
  set PC := Covers.P C with hPC
  set d := tailOf dec q X₀ D Dmax Jw v with hd
  have hel := tailOf_mem hv
  rw [← hd] at hel
  obtain ⟨hprod, hsupp, hdegD, hval⟩ := Finset.mem_filter.mp hel
  obtain ⟨-, hdsm⟩ := Finset.mem_product.mp hprod
  have hmaps : ∀ n ∈ PC, lbl C n ∈ range (r₀ * D) := fun n hn =>
    Finset.mem_range.mpr ((lbl_lt hn).trans_le hPCcard)
  have hvzero : ∀ n, n ∉ PC → v n = 0 := fun n hn => by
    by_contra h; exact hn (hvP n h)
  -- the degree of the monomial
  have hsum : ∑ ℓ : Fin (r₀ * D), ∑ n ∈ PC.filter (fun n => lbl C n = ℓ.val), v n =
      Covers.deg v := by
    rw [Fin.sum_univ_eq_sum_range (fun ℓ => ∑ n ∈ PC.filter (fun n => lbl C n = ℓ), v n) (r₀ * D),
      Finset.sum_fiberwise_of_maps_to hmaps]
    unfold Covers.deg
    exact Finset.sum_subset (Finset.subset_univ _) fun n _ hn => hvzero n hn
  -- the value
  set Mv := ∏ n, q n ^ v n with hMv
  have hM1 : 1 ≤ Mv := by
    have h := Finset.prod_le_prod₀ (s := univ) (f := fun _ => (1 : ℝ))
      (g := fun n => q n ^ v n) (fun _ _ => zero_le_one) (fun n _ => by
        by_cases hvn : v n = 0
        · simp [hvn]
        · exact one_le_pow₀ (hq1 n (hsupp n hvn)))
    simpa using h
  have hvalle : (d : ℝ) * Mv ≤ 2 * z + 1 := hJz hval
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  -- the monomial value
  set τ' : ℕ → ℝ := fun ℓ => if h : ℓ < (r₀ * D) then τl ⟨ℓ, h⟩ else 1 with hτ'
  have hmono : monoVal τl (fun ℓ : Fin (r₀ * D) =>
      ∑ n ∈ PC.filter (fun n => lbl C n = ℓ.val), v n) ≤ Mv := by
    unfold monoVal
    have e1 : ∏ ℓ : Fin (r₀ * D), τl ℓ ^ (∑ n ∈ PC.filter (fun n => lbl C n = ℓ.val), v n) =
        ∏ ℓ ∈ range (r₀ * D), τ' ℓ ^ (∑ n ∈ PC.filter (fun n => lbl C n = ℓ), v n) := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      simp [hτ', ℓ.isLt]
    rw [e1]
    have e2 : ∏ ℓ ∈ range (r₀ * D), τ' ℓ ^ (∑ n ∈ PC.filter (fun n => lbl C n = ℓ), v n) =
        ∏ n ∈ PC, τ' (lbl C n) ^ v n := by
      rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun n => τ' (lbl C n) ^ v n)]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun n hn => ?_
      rw [(Finset.mem_filter.mp hn).2]
    rw [e2]
    have e3 : Mv = ∏ n ∈ PC, q n ^ v n := by
      rw [hMv]
      symm
      exact Finset.prod_subset (Finset.subset_univ _) fun n _ hn => by simp [hvzero n hn]
    rw [e3]
    refine Finset.prod_le_prod₀ (fun n hn => pow_nonneg ?_ _) fun n hn => ?_
    · simp only [hτ']; split_ifs <;> [exact hτ0 _; exact zero_le_one]
    · have hlt : lbl C n < (r₀ * D) := Finset.mem_range.mp (hmaps n hn)
      simp only [hτ', dif_pos hlt]
      exact pow_le_pow_left₀ (hτ0 _) (hτ n (hPCdec hn) ⟨lbl C n, hlt⟩
        (lbl_le_dec hPCdec n)) _
  unfold admGen
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨Covers.deg v, Finset.mem_Icc.mpr ⟨hk1, hdegD⟩,
      Finset.Nat.mem_antidiagonalTuple.mpr hsum⟩
  · rw [Nat.mem_smoothNumbersUpTo] at hdsm ⊢
    refine ⟨Nat.le_floor ?_, hdsm.2⟩
    nlinarith
  · calc monoVal τl (fun ℓ : Fin (r₀ * D) => ∑ n ∈ PC.filter (fun n => lbl C n = ℓ.val), v n) * d
        ≤ Mv * d := mul_le_mul_of_nonneg_right hmono hd0
      _ ≤ 2 * z + 1 := by linarith

/-- **The skeleton of a configuration lies in the index sets** of `ConfigSkeletonReduction`. -/
theorem cfgSkel_mem {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {r₀ j k : ℕ} {τl : Fin (r₀ * D) → ℝ} {z : ℝ} (hq1 : ∀ n ∈ dec, 1 ≤ q n)
    (hJz : Jw ⊆ Set.Iic (2 * z + 1)) (hτ0 : ∀ ℓ, 0 ≤ τl ℓ)
    (hτ : ∀ n ∈ dec, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ (dec.filter (· < n)).card → τl ℓ ≤ q n)
    {CB : Finset (Fin N → ℕ) × Finset (Fin N → ℕ)}
    (hCB : CB ∈ configs r₀ j k (windowVecs dec q X₀ D Dmax Jw)) :
    let s := cfgSkel D r₀ (tailOf dec q X₀ D Dmax Jw) CB
    s.1 < r₀ ∧ s.2.1 ∈ CSet s.1 j ∧ s.2.2.1 ∈ labSet s.1 s.2.1.card D ∧ ExOK s.2.1 s.2.2.2.1 ∧
      s.2.2.2.2 ∈ s4Set s.2.1 (admGen (r₀ * D) (k + 1) D X₀ τl (2 * z + 1)) (0, 0) := by
  obtain ⟨C, B⟩ := CB
  set S := windowVecs dec q X₀ D Dmax Jw with hS
  obtain ⟨-, hcfg⟩ := Finset.mem_filter.mp hCB
  obtain ⟨hBS, hli, hrank, hcov, -, hRj, hdegR⟩ := hcfg
  simp only at hBS hli hrank hcov hRj hdegR
  set t := tupleOf B with ht
  have hli' : LinearIndependent ℚ (fun i => Covers.vq (t i)) := tupleOf_li hli
  have hk := card_pivs hli'
  have hinv := (skel_mem hli').1
  set σ := Classical.choose (exists_perm_support (pattern t) hinv) with hσdef
  have hσ : ∀ j, pattern t (σ j) j ≠ 0 := Classical.choose_spec (exists_perm_support _ hinv)
  have hunf : cfgSkel D r₀ (tailOf dec q X₀ D Dmax Jw) (C, B) =
      ⟨B.card, univ.filter (fun i => t (σ i) ∈ C),
        (univ.filter fun ℓ : Fin ((univ.filter (fun i => t (σ i) ∈ C)).card * D) =>
          ∃ j, lbl C (pivSlot t hk j) = ℓ.val,
         fun y i => if y ∈ univ.filter (fun i => t (σ i) ∈ C) then
           t (σ y) (pivSlot t hk i) else 0,
         fun y => if y ∈ univ.filter (fun i => t (σ i) ∈ C) then (0, 0) else
          (fun ℓ : Fin (r₀ * D) =>
            ∑ n ∈ (Covers.P C).filter (fun n => lbl C n = ℓ.val), t (σ y) n,
           tailOf dec q X₀ D Dmax Jw (t (σ y))))⟩ := by
    unfold cfgSkel
    rw [dif_pos hli']
  rw [hunf]
  set C' := univ.filter fun i => t (σ i) ∈ C with hC'
  simp only
  -- basic facts
  have hCB' : C ⊆ B := hcov.1
  have hPeq : C.biUnion Covers.supp = Covers.P B := hcov.2
  have hrB : B.card < r₀ := by
    have := Covers.rank_eq_card (S := B) (B := B) ⟨subset_rfl, hli, le_rfl⟩
    omega
  have htσ_inj : Function.Injective fun i => t (σ i) :=
    (tupleOf_injective B).comp σ.injective
  have hC'img : C'.image (fun i => t (σ i)) = C := by
    ext v
    simp only [Finset.mem_image, hC', Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hv
      obtain ⟨i, hi⟩ := tupleOf_surj B (hCB' hv)
      refine ⟨σ.symm i, ?_, ?_⟩ <;> simp [ht, hi, hv]
  have hcardC' : C'.card = C.card := by
    rw [← hC'img, Finset.card_image_of_injective _ htσ_inj]
  have hdegC : ∀ v ∈ C, Covers.deg v ≤ D := fun v hv => windowVecs_deg (hBS (hCB' hv))
  have hPC_le : (Covers.P C).card ≤ C.card * D := card_P_le hdegC
  have hPCP : Covers.P C = Covers.P B := by
    unfold Covers.P at hPeq ⊢; rw [hPeq]
  have hpivP : ∀ i, pivSlot t hk i ∈ Covers.P C := by
    intro i
    have h := hσ i
    rw [pattern_eq t hk] at h
    rw [hPCP]
    exact Finset.mem_biUnion.mpr ⟨t (σ i), tupleOf_mem B _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hPCdec : Covers.P C ⊆ dec := by
    intro n hn
    obtain ⟨v, hv, hvn⟩ := Finset.mem_biUnion.mp hn
    exact windowVecs_supp (hBS (hCB' hv)) n (Finset.mem_filter.mp hvn).2
  refine ⟨hrB, ?_, ?_, ?_, ?_⟩
  · -- (s1)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
    · -- `C` is non-empty: a row of `R` is non-zero and its primes lie in `P(C)`
      have hR : (B \ C).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨y, hy⟩ := hR
      have hy0 : y ≠ 0 := fun h => zero_notMem_windowVecs dec q X₀ D Dmax Jw
        (h ▸ hBS (Finset.mem_sdiff.mp hy).1)
      obtain ⟨n, hn⟩ : ∃ n, y n ≠ 0 := by
        by_contra h; push_neg at h; exact hy0 (funext h)
      have : n ∈ Covers.P C := by
        rw [hPCP]
        exact Finset.mem_biUnion.mpr ⟨y, (Finset.mem_sdiff.mp hy).1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩⟩
      obtain ⟨c, hc, -⟩ := Finset.mem_biUnion.mp this
      rw [← Finset.card_pos, hcardC']
      exact Finset.card_pos.mpr ⟨c, hc⟩
    · rw [hcardC', ← Finset.card_sdiff_of_subset hCB']; exact hRj
  · -- (s2)
    rw [labSet, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    have hlt : ∀ i, lbl C (pivSlot t hk i) < C'.card * D := fun i => by
      rw [hcardC']; exact (lbl_lt (hpivP i)).trans_le hPC_le
    have himg : (univ.filter fun ℓ : Fin (C'.card * D) => ∃ j, lbl C (pivSlot t hk j) = ℓ.val) =
        univ.image (fun i => (⟨lbl C (pivSlot t hk i), hlt i⟩ : Fin (C'.card * D))) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i, Fin.ext hi⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    rw [himg, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro a b hab
    have h1 : lbl C (pivSlot t hk a) = lbl C (pivSlot t hk b) := congrArg Fin.val hab
    exact pivSlot_injective t hk (lbl_injOn (hpivP a) (hpivP b) h1)
  · -- (s3)
    intro i
    refine ⟨fun y hy => by simp [hy], fun hi => ?_, ?_⟩
    · simp only [if_pos hi]
      have := hσ i
      rw [pattern_eq t hk] at this
      exact Nat.one_le_iff_ne_zero.mpr this
    · obtain ⟨c, hc, hcn⟩ := Finset.mem_biUnion.mp (hpivP i)
      obtain ⟨i', hi'⟩ := tupleOf_surj B (hCB' hc)
      rw [← ht] at hi'
      have hmem : σ.symm i' ∈ C' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [Equiv.apply_symm_apply]; exact hi' ▸ hc⟩
      refine ⟨σ.symm i', hmem, ?_⟩
      simp only [if_pos hmem, Equiv.apply_symm_apply]
      exact Nat.one_le_iff_ne_zero.mpr (hi' ▸ (Finset.mem_filter.mp hcn).2)
  · -- (s4)
    unfold s4Set
    rw [Fintype.mem_piFinset]
    intro y
    by_cases hy : y ∈ C'
    · simp [hy]
    · simp only [if_neg hy]
      have hyC : t (σ y) ∉ C := fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hyB : t (σ y) ∈ B := tupleOf_mem B _
      refine s4_mem hq1 hJz hτ0 hτ hPCdec ?_ (hBS hyB) ?_
        (hdegR _ (Finset.mem_sdiff.mpr ⟨hyB, hyC⟩))
      · calc (Covers.P C).card ≤ C.card * D := hPC_le
          _ ≤ r₀ * D := Nat.mul_le_mul_right _
              ((Finset.card_le_card hCB').trans hrB.le)
      · intro n hn
        rw [hPCP]
        exact Finset.mem_biUnion.mpr ⟨_, hyB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩⟩

/-- A `(j, k)`-configuration is a `(0, 0)`-configuration. -/
lemma configs_mono {j k : ℕ} (r₀ : ℕ) (S : Finset (Fin N → ℕ)) :
    configs r₀ j k S ⊆ configs r₀ 0 0 S := by
  intro CB hCB
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (Finset.mem_filter.mp hCB).2
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hCB).1, h1, h2, h3, h4, h5, by omega,
    fun y hy => le_trans (by omega) (h7 y hy)⟩

/-- **The reduction to skeletons, pathwise** (§6.7, proof of Lemma 6.21(ii)): every configuration
of a window set `S(J)` is counted by the skeleton count of its own skeleton, which lies in the
index sets (s1)–(s4). -/
theorem configCount_le_skel {dec : Finset (Fin N)} {q : Fin N → ℝ} {X₀ D Dmax : ℕ} {Jw : Set ℝ}
    {r₀ j k : ℕ} {τl : Fin (r₀ * D) → ℝ} {z : ℝ} (hq1 : ∀ n ∈ dec, 1 ≤ q n)
    (hJz : Jw ⊆ Set.Iic (2 * z + 1)) (hτ0 : ∀ ℓ, 0 ≤ τl ℓ)
    (hτ : ∀ n ∈ dec, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ (dec.filter (· < n)).card → τl ℓ ≤ q n) :
    (configCount r₀ j k (windowVecs dec q X₀ D Dmax Jw) : ℝ≥0∞) ≤
      ∑ r ∈ range r₀, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card D, ∑' ex : Fin r → Fin r → ℕ,
        (if ExOK C ex then ∑ s4 ∈ s4Set C (admGen (r₀ * D) (k + 1) D X₀ τl (2 * z + 1)) (0, 0),
          cfgSkelCount D r₀ 0 0 (tailOf dec q X₀ D Dmax Jw) (windowVecs dec q X₀ D Dmax Jw)
            r C lab ex s4 else 0) := by
  set S := windowVecs dec q X₀ D Dmax Jw with hS
  set tail := tailOf dec q X₀ D Dmax Jw with htail
  set adm := admGen (r₀ * D) (k + 1) D X₀ τl (2 * z + 1) with hadm
  set F : Finset (Fin N → ℕ) × Finset (Fin N → ℕ) → ℝ≥0∞ := fun CB =>
    ∑ r ∈ range r₀, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card D, ∑' ex : Fin r → Fin r → ℕ,
      (if ExOK C ex then ∑ s4 ∈ s4Set C adm (0, 0),
        (if cfgSkel D r₀ tail CB = ⟨r, C, lab, ex, s4⟩ then (1 : ℝ≥0∞) else 0) else 0) with hF
  have hkey : ∀ CB ∈ configs r₀ j k S, 1 ≤ F CB := by
    intro CB hCB
    have hm := cfgSkel_mem (k := k) hq1 hJz hτ0 hτ hCB
    simp only [← htail, ← hadm] at hm
    simp only [hF]
    generalize cfgSkel D r₀ tail CB = s at hm ⊢
    obtain ⟨r, C, lab, ex, s4⟩ := s
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr h1))
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) h2)
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) h3)
    refine le_trans ?_ (ENNReal.le_tsum ex)
    rw [if_pos h4]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) h5)
    rw [if_pos rfl]
  have hsum : ∑ CB ∈ configs r₀ 0 0 S, F CB =
      ∑ r ∈ range r₀, ∑ C ∈ CSet r j, ∑ lab ∈ labSet r C.card D, ∑' ex : Fin r → Fin r → ℕ,
        (if ExOK C ex then ∑ s4 ∈ s4Set C adm (0, 0),
          cfgSkelCount D r₀ 0 0 tail S r C lab ex s4 else 0) := by
    simp only [hF, cfgSkelCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun C _ => ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun lab _ => ?_)
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun ex => ?_
    rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
    split_ifs
    · exact Finset.sum_comm
    · rfl
  rw [configCount_eq, ← hsum, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact (Finset.sum_le_sum hkey).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (configs_mono r₀ S) fun _ _ _ => zero_le)

/-- **`ConfigSkeletonReduction` for the window model** (the input `hred` of
`theorem_6_23a_all`): with `X = cfgSkelCount`, for windows `Jw J ⊆ (-∞, 2z + 1]`, prime values
`≥ 1`, and label thresholds `0 ≤ τ_ℓ ≤ q_n` whenever `ℓ ≤ #{decided slots < n}`. -/
theorem configSkeletonReduction {Ω ι : Type*} (W : Finset ι) (dec : Ω → Finset (Fin N))
    (q : Ω → Fin N → ℝ) (X₀ D Dmax : ℕ) (Jw : ι → Set ℝ) {r₀ j k : ℕ}
    {τl : Fin (r₀ * D) → ℝ} {z : ℝ} (hq1 : ∀ ω, ∀ n ∈ dec ω, 1 ≤ q ω n)
    (hJz : ∀ J ∈ W, Jw J ⊆ Set.Iic (2 * z + 1)) (hτ0 : ∀ ℓ, 0 ≤ τl ℓ)
    (hτ : ∀ ω, ∀ n ∈ dec ω, ∀ ℓ : Fin (r₀ * D), ℓ.val ≤ ((dec ω).filter (· < n)).card →
      τl ℓ ≤ q ω n) :
    ConfigSkeletonReduction W (fun J ω => windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r₀ j k D
      (admGen (r₀ * D) (k + 1) D X₀ τl (2 * z + 1)) (0, 0)
      (fun J r C lab ex s4 ω => cfgSkelCount D r₀ 0 0 (tailOf (dec ω) (q ω) X₀ D Dmax (Jw J))
        (windowVecs (dec ω) (q ω) X₀ D Dmax (Jw J)) r C lab ex s4) :=
  fun J hJ ω => configCount_le_skel (hq1 ω) (hJz J hJ) hτ0 (hτ ω)

end RankFull.Config
