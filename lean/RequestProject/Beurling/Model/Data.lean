module

public import RequestProject.Beurling.Construction.JitterRegular

/-!
# Prime data, the elements over them, and the target read from them (§3.1–§3.2)

The construction of §3 reads the realised system only through its primes: the rational primes
`p < X₀`, and the primes placed by the greedy rule, the prime decided at relative slot `k + 1`
having a value `v k`. Here these data are packaged in a form that does not depend on a slot model
(`PrimeData`), over the fixed index set `PIdx X₀ = {p < X₀ prime} ⊕ ℕ`, and the objects of §3.2
are defined from them, without any choice:

* `elemsLe`, `NCount`: the elements (exponent vectors supported on the live primes) of value `≤ x`
  and their number `N(x)`;
* `compSet`, `compCount`: the composite elements with value in `[a, b)` (the arrivals `A_j` of
  §3.4 when `[a, b)` is a slot);
* `absSet`: the absorbed set (5), with the latest prime of an element read off as its largest
  slot index (the decision order of §3.4);
* `designedGammaN`: the recursive rule of Lemma 4.8 for the heights `γ_k`, for an arbitrary
  counting function `N` (for `N = P.N` it is `designedGamma P`, `designedGamma_eq_N`);
* `targetD`: the target (6) of the data.

The locality lemmas (`DAgree`, `elemsLe_eq_of_agree`, `compSet_eq_of_agree`,
`absSet_inter_eq_of_agree`) say that these objects at a height only read the primes below it:
this is the content of the causality statements of §3 (Lemma 3.2, Lemma 3.5).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty

namespace BModel

/-- The index set of the primes: the rational primes `p < X₀`, and the relative slot indices `k`
(the prime decided at relative slot `k + 1`). -/
abbrev PIdx (X₀ : ℕ) : Type := {p : ℕ // p.Prime ∧ p < X₀} ⊕ ℕ

/-- **Prime data**: which relative slots `k` place a prime, and the value `v k` of the prime
decided at relative slot `k + 1`. -/
structure PrimeData where
  live : ℕ → Prop
  v : ℕ → ℝ

variable {X₀ : ℕ}

/-- The value of a prime index. -/
def pval (D : PrimeData) : PIdx X₀ → ℝ
  | Sum.inl p => (p.1 : ℝ)
  | Sum.inr k => D.v k

/-- An exponent vector is an element of the semigroup when it only uses live primes. -/
def Live (D : PrimeData) (e : PIdx X₀ →₀ ℕ) : Prop := ∀ k, e (Sum.inr k) ≠ 0 → D.live k

/-- The value `∏ p^{e_p}` of an exponent vector. -/
noncomputable def eval (D : PrimeData) (e : PIdx X₀ →₀ ℕ) : ℝ :=
  e.prod fun i n => pval D i ^ n

/-- The elements of value `≤ x`. -/
def elemsLe (X₀ : ℕ) (D : PrimeData) (x : ℝ) : Set (PIdx X₀ →₀ ℕ) :=
  {e | Live D e ∧ eval D e ≤ x}

/-- `N(x)`: the number of elements of value `≤ x` (with multiplicity). -/
noncomputable def NCount (X₀ : ℕ) (D : PrimeData) (x : ℝ) : ℝ :=
  ((elemsLe X₀ D x).ncard : ℝ)

/-- The composite elements (at least two prime factors with multiplicity) of value in
`[a, b)`. -/
def compSet (X₀ : ℕ) (D : PrimeData) (a b : ℝ) : Set (PIdx X₀ →₀ ℕ) :=
  {e | Live D e ∧ 2 ≤ e.sum (fun _ n => n) ∧ a ≤ eval D e ∧ eval D e < b}

/-- The number of composite elements of value in `[a, b)`. -/
noncomputable def compCount (X₀ : ℕ) (D : PrimeData) (a b : ℝ) : ℤ :=
  ((compSet X₀ D a b).ncard : ℤ)

/-- The latest prime of `e` (its largest slot index `k`; rational primes are decided first) is a
jittered prime, of value `< y`. -/
def LatestBelow (D : PrimeData) (e : PIdx X₀ →₀ ℕ) (y : ℝ) : Prop :=
  ∃ k, e (Sum.inr k) ≠ 0 ∧ (∀ k', e (Sum.inr k') ≠ 0 → k' ≤ k) ∧ D.v k < y

/-- **The absorbed set (5)** of the data: the real values `n` with `log n ≥ L* = 10⁷` of the live
elements `e` (with any cofactor) whose latest prime is jittered and below `y(n)`. The elements are
required to have prime values `> 1`: this holds for the elements of every Beurling system (and so
for the realised data, `realisedA_eq`), and it keeps `absSet` locally finite for arbitrary locally
finite data (`absSet_locFin`). -/
def absSet (X₀ : ℕ) (D : PrimeData) : Set ℝ :=
  {n | 10 ^ 7 ≤ Real.log n ∧
    ∃ e : PIdx X₀ →₀ ℕ, Live D e ∧ (∀ i ∈ e.support, 1 < pval D i) ∧ eval D e = n ∧
      LatestBelow D e (absorbY X₀ n)}

/-! ### The heights for an arbitrary counting function -/

/-- The lag `N - T`, for a counting function `N`. -/
noncomputable def lagN (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (α γ xp : ℕ → ℝ) (x : ℝ) : ℝ :=
  N x - targetOf θ X₀ κ A u α γ xp x

/-- `D̂_{<a_k}` for the lag `N - T`. -/
noncomputable def earlyN (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (α γ xp a : ℕ → ℝ) (k : ℕ) : ℂ → ℂ :=
  earlyNoise (lagN N θ X₀ κ A u α γ xp) (a k)

/-- One step of the rule of Lemma 4.8, for a counting function `N`. -/
noncomputable def stepGammaN (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (κ₀ : ℝ) (xp a : ℕ → ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  designGamma X₀ κ θ κ₀ (earlyN N θ X₀ κ A u (amplitudes θ κ₀ xp g) g xp a) xp k

/-- **The designed heights for a counting function `N`** (Lemma 4.8), by recursion on `k`. -/
noncomputable def designedGammaN (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) : ℕ → ℝ :=
  fun k => Nat.strongRecOn (motive := fun _ => ℝ) k
    (fun k IH => stepGammaN N θ X₀ κ A u κ₀ xp a (fun j => if h : j < k then IH j h else 0) k)

/-- For `N = P.N` the heights are the designed heights of `P`. -/
theorem designedGamma_eq_N (P : BeurlingSystem) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ)
    (u : ℝ → ℝ) (κ₀ : ℝ) (xp a : ℕ → ℝ) :
    designedGamma P θ X₀ κ A u κ₀ xp a = designedGammaN P.N θ X₀ κ A u κ₀ xp a := rfl

lemma designedGammaN_rec (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (κ₀ : ℝ) (xp a : ℕ → ℝ) (k : ℕ) :
    designedGammaN N θ X₀ κ A u κ₀ xp a k = stepGammaN N θ X₀ κ A u κ₀ xp a
      (fun j => if j < k then designedGammaN N θ X₀ κ A u κ₀ xp a j else 0) k := by
  conv_lhs => unfold designedGammaN
  rw [Nat.strongRecOn_eq]
  simp only [dite_eq_ite]
  rfl

/-- On `(0, x⁺_k]` the lag only reads `α_j, γ_j` for `j < k`. -/
lemma lagN_congr_lt (N : ℝ → ℝ) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ} {u : ℝ → ℝ}
    {α γ α' γ' xp : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀) (hxp : (X₀ : ℝ) ≤ xp 0) {k : ℕ}
    (hα : ∀ j < k, α j = α' j) (hγ : ∀ j < k, γ j = γ' j) {x : ℝ} (hx : 0 < x)
    (hxk : x ≤ xp k) : lagN N θ X₀ κ A u α γ xp x = lagN N θ X₀ κ A u α' γ' xp x := by
  have hX0 : (0 : ℝ) < X₀ := by exact_mod_cast hX1
  have hXk : (X₀ : ℝ) ≤ xp k := hxp.trans (hsp.strictMono.monotone (Nat.zero_le k))
  unfold lagN targetOf Target.target
  rw [osc_congr_lt hsp hα hγ hx hxk, osc_congr_lt hsp hα hγ hX0 hXk]

/-- **The fixed-point condition for the heights** `designedGammaN`. -/
theorem designedGammaN_fixed (N : ℝ → ℝ) {θ : ℝ} {X₀ : ℕ} {κ : ℝ} {A : Set ℝ}
    {u : ℝ → ℝ} {κ₀ : ℝ} {xp a : ℕ → ℝ} (hsp : Spacing xp) (hX1 : 1 ≤ X₀)
    (hxp : (X₀ : ℝ) ≤ xp 0) (ha : ∀ k, 0 < a k ∧ a k ≤ xp k) (k : ℕ) :
    designedGammaN N θ X₀ κ A u κ₀ xp a k =
      designGamma X₀ κ θ κ₀
        (earlyN N θ X₀ κ A u (amplitudes θ κ₀ xp (designedGammaN N θ X₀ κ A u κ₀ xp a))
          (designedGammaN N θ X₀ κ A u κ₀ xp a) xp a) xp k := by
  set g := designedGammaN N θ X₀ κ A u κ₀ xp a with hg
  have hrec : g k = stepGammaN N θ X₀ κ A u κ₀ xp a (fun j => if j < k then g j else 0) k :=
    designedGammaN_rec N θ X₀ κ A u κ₀ xp a k
  rw [hrec]
  have heq : earlyN N θ X₀ κ A u (amplitudes θ κ₀ xp (fun j => if j < k then g j else 0))
      (fun j => if j < k then g j else 0) xp a k =
      earlyN N θ X₀ κ A u (amplitudes θ κ₀ xp g) g xp a k := by
    unfold earlyN
    refine earlyNoise_congr (ha k).1 fun x hx hxa => ?_
    exact lagN_congr_lt N hsp hX1 hxp (fun j hj => by simp only [amplitudes, if_pos hj])
      (fun j hj => by simp only [if_pos hj]) hx (hxa.trans (ha k).2)
  unfold stepGammaN designGamma
  rw [heq]

/-- The heights `designedGammaN` lie in `[Γ_k, 2Γ_k]`. -/
lemma designedGammaN_mem (N : ℝ → ℝ) (θ : ℝ) (X₀ : ℕ) (κ : ℝ) (A : Set ℝ) (u : ℝ → ℝ)
    (κ₀ : ℝ) (xp a : ℕ → ℝ) (hΓ : ∀ k, 0 ≤ heightScale θ κ₀ (xp k)) (k : ℕ) :
    designedGammaN N θ X₀ κ A u κ₀ xp a k ∈
      Icc (heightScale θ κ₀ (xp k)) (2 * heightScale θ κ₀ (xp k)) := by
  rw [designedGammaN_rec]
  unfold stepGammaN designGamma
  exact chooseHeight_mem _ _ _ (hΓ k)

/-! ### The target of the data -/

/-- `u_a`: the solution of `u + u^{θ/2} = a`. -/
noncomputable def uA (θ : ℝ) : ℝ → ℝ := fun n => solveU (θ / 2) n

/-- The heights `γ_k` of the data (Lemma 4.8, with `κ, κ₀, x⁺, a_k` of Section 2.2). -/
noncomputable def gammaD (θ : ℝ) (X₀ : ℕ) (D : PrimeData) : ℕ → ℝ :=
  designedGammaN (NCount X₀ D) θ X₀ (kappaParam X₀) (absSet X₀ D) (uA θ) kappa0Param
    (switchOn X₀) (constructionScale X₀)

/-- The amplitudes `α_k` of the data. -/
noncomputable def alphaD (θ : ℝ) (X₀ : ℕ) (D : PrimeData) : ℕ → ℝ :=
  amplitudes θ kappa0Param (switchOn X₀) (gammaD θ X₀ D)

/-- **The target (6) of the data.** -/
noncomputable def targetD (θ : ℝ) (X₀ : ℕ) (D : PrimeData) : ℝ → ℝ :=
  target X₀ (kappaParam X₀) (countA (absSet X₀ D)) (absorbedDensityCap (θ / 2) (absSet X₀ D)
    (uA θ)) (osc θ (alphaD θ X₀ D) (gammaD θ X₀ D) (switchOn X₀))

/-! ### Values of elements -/

/-- The prime values are `≥ 1` on the live primes. -/
def Pos (D : PrimeData) : Prop := ∀ k, D.live k → 1 ≤ D.v k

lemma pval_ge_one {D : PrimeData} (hD : Pos D) {e : PIdx X₀ →₀ ℕ} (he : Live D e)
    {i : PIdx X₀} (hi : i ∈ e.support) : 1 ≤ pval D i := by
  cases i with
  | inl p =>
    show (1 : ℝ) ≤ (p.1 : ℝ)
    exact_mod_cast p.2.1.one_lt.le
  | inr k => exact hD k (he k (Finsupp.mem_support_iff.mp hi))

lemma one_le_prod_of {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  simpa using Finset.prod_le_prod₀ (s := s) (f := fun _ => (1 : ℝ)) (g := f)
    (fun _ _ => zero_le_one) hf

lemma one_le_eval {D : PrimeData} (hD : Pos D) {e : PIdx X₀ →₀ ℕ} (he : Live D e) :
    1 ≤ eval D e := by
  unfold eval Finsupp.prod
  exact one_le_prod_of _ _ fun i hi => one_le_pow₀ (pval_ge_one hD he hi)

/-- A prime factor of an element is at most its value. -/
lemma pval_le_eval {D : PrimeData} (hD : Pos D) {e : PIdx X₀ →₀ ℕ} (he : Live D e)
    {i : PIdx X₀} (hi : i ∈ e.support) : pval D i ≤ eval D e := by
  classical
  unfold eval Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ hi]
  have h1 : 1 ≤ ∏ x ∈ e.support.erase i, pval D x ^ e x :=
    one_le_prod_of _ _ fun j hj => one_le_pow₀ (pval_ge_one hD he (Finset.mem_of_mem_erase hj))
  have hp := pval_ge_one hD he hi
  have h2 : pval D i ≤ pval D i ^ e i :=
    le_self_pow₀ hp (Finsupp.mem_support_iff.mp hi)
  nlinarith

/-! ### Locality -/

/-- **The data agree below `Y`**: up to some index `K` the decisions and values agree, and every
live prime from index `K` on (in either data) has value `≥ Y`. -/
def DAgree (D D' : PrimeData) (Y : ℝ) : Prop :=
  ∃ K : ℕ, (∀ k < K, (D.live k ↔ D'.live k) ∧ D.v k = D'.v k) ∧
    (∀ k, K ≤ k → D.live k → Y ≤ D.v k) ∧ (∀ k, K ≤ k → D'.live k → Y ≤ D'.v k)

lemma DAgree.symm {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) : DAgree D' D Y := by
  obtain ⟨K, h1, h2, h3⟩ := h
  exact ⟨K, fun k hk => ⟨(h1 k hk).1.symm, (h1 k hk).2.symm⟩, h3, h2⟩

lemma DAgree.mono {D D' : PrimeData} {Y Y' : ℝ} (h : DAgree D D' Y) (hY : Y' ≤ Y) :
    DAgree D D' Y' := by
  obtain ⟨K, h1, h2, h3⟩ := h
  exact ⟨K, h1, fun k hk hl => hY.trans (h2 k hk hl), fun k hk hl => hY.trans (h3 k hk hl)⟩

/-- An element with a factor of index `≥ K`, under `DAgree`, has value `≥ Y`. -/
lemma small_support {D : PrimeData} {Y : ℝ} {K : ℕ}
    (h2 : ∀ k, K ≤ k → D.live k → Y ≤ D.v k) (hD : Pos D) {e : PIdx X₀ →₀ ℕ}
    (he : Live D e) (hlt : eval D e < Y) {k : ℕ} (hk : e (Sum.inr k) ≠ 0) : k < K := by
  by_contra hK
  push_neg at hK
  have h1 := h2 k hK (he k hk)
  have h3 := pval_le_eval hD he (i := Sum.inr k) (Finsupp.mem_support_iff.mpr hk)
  simp only [pval] at h3
  linarith

/-- The transport of an element of value `< Y` from `D` to `D'`. -/
lemma transport {D D' : PrimeData} {K : ℕ}
    (h1 : ∀ k < K, (D.live k ↔ D'.live k) ∧ D.v k = D'.v k)
    {e : PIdx X₀ →₀ ℕ} (hK : ∀ k, e (Sum.inr k) ≠ 0 → k < K) (he : Live D e) :
    Live D' e ∧ eval D' e = eval D e := by
  refine ⟨fun k hk => ((h1 k (hK k hk)).1).mp (he k hk), ?_⟩
  unfold eval Finsupp.prod
  refine Finset.prod_congr rfl fun i hi => ?_
  cases i with
  | inl p => rfl
  | inr k =>
    simp only [pval]
    rw [(h1 k (hK k (Finsupp.mem_support_iff.mp hi))).2]

lemma elemsLe_subset_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    {x : ℝ} (hx : x < Y) : elemsLe X₀ D x ⊆ elemsLe X₀ D' x := by
  obtain ⟨K, h1, h2, -⟩ := h
  rintro e ⟨he, hv⟩
  have hK := fun k (hk : e (Sum.inr k) ≠ 0) => small_support h2 hD he (lt_of_le_of_lt hv hx) hk
  obtain ⟨he', hval⟩ := transport h1 hK he
  exact ⟨he', hval ▸ hv⟩

/-- **`N` only reads the primes below**: under `DAgree D D' Y`, the elements of value `≤ x < Y`
agree. -/
theorem elemsLe_eq_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    (hD' : Pos D') {x : ℝ} (hx : x < Y) : elemsLe X₀ D x = elemsLe X₀ D' x :=
  (elemsLe_subset_of_agree h hD hx).antisymm (elemsLe_subset_of_agree h.symm hD' hx)

theorem NCount_eq_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    (hD' : Pos D') {x : ℝ} (hx : x < Y) : NCount X₀ D x = NCount X₀ D' x := by
  unfold NCount; rw [elemsLe_eq_of_agree h hD hD' hx]

lemma compSet_subset_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    {a b : ℝ} (hb : b ≤ Y) : compSet X₀ D a b ⊆ compSet X₀ D' a b := by
  obtain ⟨K, h1, h2, -⟩ := h
  rintro e ⟨he, h2e, hva, hvb⟩
  have hK := fun k (hk : e (Sum.inr k) ≠ 0) => small_support h2 hD he (lt_of_lt_of_le hvb hb) hk
  obtain ⟨he', hval⟩ := transport h1 hK he
  exact ⟨he', h2e, hval ▸ hva, hval ▸ hvb⟩

/-- **The composites in `[a, b)` only read the primes below `b`.** -/
theorem compSet_eq_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    (hD' : Pos D') {a b : ℝ} (hb : b ≤ Y) : compSet X₀ D a b = compSet X₀ D' a b :=
  (compSet_subset_of_agree h hD hb).antisymm (compSet_subset_of_agree h.symm hD' hb)

theorem compCount_eq_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos D)
    (hD' : Pos D') {a b : ℝ} (hb : b ≤ Y) : compCount X₀ D a b = compCount X₀ D' a b := by
  unfold compCount; rw [compSet_eq_of_agree h hD hD' hb]

lemma absSet_mem_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y)
    {n : ℝ} (hn : n ∈ absSet X₀ D) (hy : absorbY X₀ n ≤ Y) : n ∈ absSet X₀ D' := by
  obtain ⟨K, h1, h2, -⟩ := h
  obtain ⟨hlog, e, he, hg, hval, k, hk, hmax, hvk⟩ := hn
  have hkK : k < K := by
    by_contra hK
    push_neg at hK
    have := h2 k hK (he k hk)
    linarith
  have hK : ∀ k', e (Sum.inr k') ≠ 0 → k' < K := fun k' hk' => lt_of_le_of_lt (hmax k' hk') hkK
  obtain ⟨he', hval'⟩ := transport h1 hK he
  have hg' : ∀ i ∈ e.support, 1 < pval D' i := by
    intro i hi
    have := hg i hi
    cases i with
    | inl p => exact this
    | inr k' =>
      simp only [pval] at this ⊢
      rw [← (h1 k' (hK k' (Finsupp.mem_support_iff.mp hi))).2]; exact this
  refine ⟨hlog, e, he', hg', hval'.trans hval, k, hk, hmax, ?_⟩
  rw [← (h1 k hkK).2]; exact hvk

/-- **The absorbed set only reads the primes below `y(n)`**: under `DAgree D D' Y`, membership of
`n` with `y(n) ≤ Y` agrees. -/
theorem absSet_iff_of_agree {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) {n : ℝ}
    (hy : absorbY X₀ n ≤ Y) : n ∈ absSet X₀ D ↔ n ∈ absSet X₀ D' :=
  ⟨fun hn => absSet_mem_of_agree h hn hy, fun hn => absSet_mem_of_agree h.symm hn hy⟩

/-! ### Local finiteness of the absorbed set -/

/-- The prime data are **locally finite**: finitely many live primes of value below any bound. -/
def LocFinD (D : PrimeData) : Prop := ∀ c : ℝ, {k | D.live k ∧ D.v k ≤ c}.Finite

lemma pow_le_eval_of_gt {D : PrimeData} {e : PIdx X₀ →₀ ℕ}
    (hg : ∀ i ∈ e.support, 1 < pval D i) {i : PIdx X₀} (hi : i ∈ e.support) :
    pval D i ^ e i ≤ eval D e := by
  classical
  unfold eval Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ hi]
  have h1 : 1 ≤ ∏ x ∈ e.support.erase i, pval D x ^ e x :=
    one_le_prod_of _ _ fun j hj => one_le_pow₀ (hg j (Finset.mem_of_mem_erase hj)).le
  have h0 : 0 ≤ pval D i ^ e i := pow_nonneg (by linarith [hg i hi]) _
  nlinarith

/-- For locally finite data, the live elements with prime values `> 1` and value `≤ x` are
finitely many. -/
lemma finite_elems_gt {D : PrimeData} (hD : LocFinD D) (x : ℝ) :
    {e : PIdx X₀ →₀ ℕ | Live D e ∧ (∀ i ∈ e.support, 1 < pval D i) ∧ eval D e ≤ x}.Finite := by
  classical
  set I : Set (PIdx X₀) := {i | 1 < pval D i ∧ ∀ k, i = Sum.inr k → D.live k ∧ D.v k ≤ x}
  have hI : I.Finite := by
    have hrat : (Set.range (Sum.inl : {p : ℕ // p.Prime ∧ p < X₀} → PIdx X₀)).Finite := by
      haveI : Finite {p : ℕ // p.Prime ∧ p < X₀} :=
        Finite.of_injective (fun p => (⟨p.1, p.2.2⟩ : Fin X₀))
          (fun p q h => Subtype.ext (by simpa using congrArg Fin.val h))
      exact Set.finite_range _
    refine (hrat.union ((hD x).image Sum.inr)).subset fun i hi => ?_
    cases i with
    | inl p => exact Or.inl ⟨p, rfl⟩
    | inr k => exact Or.inr ⟨k, hi.2 k rfl, rfl⟩
  set F := hI.toFinset
  have hN : ∀ i ∈ F, ∃ N : ℕ, x < pval D i ^ N := fun i hi =>
    pow_unbounded_of_one_lt x ((hI.mem_toFinset).mp hi).1
  choose! Nf hNf using hN
  set N := F.sup Nf + 1
  refine (Finset.finite_toSet (F.finsupp fun _ => Finset.range N)).subset ?_
  rintro e ⟨he, hg, hx⟩
  simp only [Finset.mem_coe, Finset.mem_finsupp_iff, Finset.mem_range]
  have hsupp : ∀ i ∈ e.support, i ∈ F := by
    intro i hi
    rw [hI.mem_toFinset]
    refine ⟨hg i hi, fun k hk => ?_⟩
    subst hk
    refine ⟨he k (Finsupp.mem_support_iff.mp hi), ?_⟩
    have h1 := pow_le_eval_of_gt hg hi
    have h2 : pval D (Sum.inr k) ≤ pval D (Sum.inr k) ^ e (Sum.inr k) :=
      le_self_pow₀ (hg _ hi).le (Finsupp.mem_support_iff.mp hi)
    simp only [pval] at h1 h2
    linarith
  refine ⟨hsupp, fun i hiF => ?_⟩
  by_cases hi : i ∈ e.support
  swap
  · rw [Finsupp.notMem_support_iff.mp hi]; omega
  have h1 := pow_le_eval_of_gt hg hi
  have h3 := hNf i hiF
  by_contra hc
  push_neg at hc
  have h4 : pval D i ^ Nf i ≤ pval D i ^ e i :=
    pow_le_pow_right₀ (hg i hi).le ((Finset.le_sup hiF).trans (by omega))
  linarith

/-- **The absorbed set of locally finite data is locally finite.** -/
theorem absSet_locFin {D : PrimeData} (hD : LocFinD D) : LocFin (absSet X₀ D) := fun x =>
  ((finite_elems_gt (X₀ := X₀) hD x).image (eval D)).subset fun n hn => by
    obtain ⟨-, e, he, hg, hval, -⟩ := hn.1
    exact ⟨e, ⟨he, hg, by rw [hval]; exact hn.2⟩, hval⟩

/-- The prime values are `≥ 2` on the live primes. -/
def Pos2 (D : PrimeData) : Prop := ∀ k, D.live k → 2 ≤ D.v k

lemma Pos2.pos {D : PrimeData} (h : Pos2 D) : Pos D := fun k hk => by linarith [h k hk]

lemma pval_ge_two {D : PrimeData} (hD : Pos2 D) {e : PIdx X₀ →₀ ℕ} (he : Live D e)
    {i : PIdx X₀} (hi : i ∈ e.support) : 2 ≤ pval D i := by
  cases i with
  | inl p =>
    show (2 : ℝ) ≤ (p.1 : ℝ)
    exact_mod_cast p.2.1.two_le
  | inr k => exact hD k (he k (Finsupp.mem_support_iff.mp hi))

lemma eval_add (D : PrimeData) (e f : PIdx X₀ →₀ ℕ) : eval D (e + f) = eval D e * eval D f := by
  unfold eval
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma eval_single (D : PrimeData) (i : PIdx X₀) (n : ℕ) :
    eval D (Finsupp.single i n) = pval D i ^ n := by
  unfold eval; simp

/-- **A prime factor of a composite is at most half its value.** -/
lemma two_mul_pval_le_eval {D : PrimeData} (hD : Pos2 D) {e : PIdx X₀ →₀ ℕ} (he : Live D e)
    (h2 : 2 ≤ e.sum (fun _ n => n)) {i : PIdx X₀} (hi : i ∈ e.support) :
    2 * pval D i ≤ eval D e := by
  classical
  have hi1 : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  set f := e - Finsupp.single i 1 with hf
  have hef : e = Finsupp.single i 1 + f := by
    ext j
    simp only [hf, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  have hfle : ∀ j, f j ≤ e j := fun j => by
    simp only [hf, Finsupp.coe_tsub, Pi.sub_apply]; omega
  have hfl : Live D f := fun k hk => he k (fun h0 => hk (by have := hfle (Sum.inr k); omega))
  have hsum : f.sum (fun _ n => n) + 1 = e.sum (fun _ n => n) := by
    conv_rhs => rw [hef]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    ring
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, Finsupp.sum_zero_index] at hsum
    omega
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hf0
  have hjs : j ∈ f.support := Finsupp.mem_support_iff.mpr (by simpa using hj)
  have h2j := pval_ge_two hD hfl hjs
  have hfj := pval_le_eval hD.pos hfl hjs
  have hpi := pval_ge_two hD he hi
  rw [hef, eval_add, eval_single, pow_one]
  nlinarith

lemma compSet_subset_of_agree2 {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos2 D)
    {a b : ℝ} (hb : b ≤ 2 * Y) : compSet X₀ D a b ⊆ compSet X₀ D' a b := by
  obtain ⟨K, h1, h2, -⟩ := h
  rintro e ⟨he, h2e, hva, hvb⟩
  have hK : ∀ k, e (Sum.inr k) ≠ 0 → k < K := by
    intro k hk
    by_contra hK
    push_neg at hK
    have hY := h2 k hK (he k hk)
    have := two_mul_pval_le_eval hD he h2e (i := Sum.inr k) (Finsupp.mem_support_iff.mpr hk)
    simp only [pval] at this
    linarith
  obtain ⟨he', hval⟩ := transport h1 hK he
  exact ⟨he', h2e, hval ▸ hva, hval ▸ hvb⟩

/-- **Lemma 3.5 (causality), deterministic form**: the composites of value in `[a, b)` only read
the primes below `b/2`. -/
theorem compSet_eq_of_agree2 {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos2 D)
    (hD' : Pos2 D') {a b : ℝ} (hb : b ≤ 2 * Y) : compSet X₀ D a b = compSet X₀ D' a b :=
  (compSet_subset_of_agree2 h hD hb).antisymm (compSet_subset_of_agree2 h.symm hD' hb)

theorem compCount_eq_of_agree2 {D D' : PrimeData} {Y : ℝ} (h : DAgree D D' Y) (hD : Pos2 D)
    (hD' : Pos2 D') {a b : ℝ} (hb : b ≤ 2 * Y) : compCount X₀ D a b = compCount X₀ D' a b := by
  unfold compCount; rw [compSet_eq_of_agree2 h hD hD' hb]

end BModel

end
