module

public import Mathlib

/-!
# Step 3 of the proof of Lemma 7.3(b): the symmetric telescoping (combinatorics)

The sum over the cofactors with `r` large primes is `1/r!` times a sum over ordered `r`-tuples
of large primes (the product measure), up to the tuples with a repeated prime. This file proves
the combinatorial facts used by the telescoping, for a value map `v : ι → ℝ` on a set of
prime labels:

* `tsumR v A r Φ = ∑_{f : Fin r → A} Φ(v ∘ f)` and `tsumR_succ` (peeling the first coordinate);
* `kern Ψ a b t = Ψ(a ∏ tᵢ, max(b, max tᵢ))`, the kernels of the operators (the cofactor value is
  `a ∏ tᵢ`, its largest prime `max(b, max tᵢ)`), and `kern_cons`;
* **`tele`** : the telescoping bound: if one replacement costs at most `c/a`, i.e.
  `|∑_{x∈X} Ψ(a v(x), max(b, v(x))) - ∑_{y∈Y} Ψ(a v(y), max(b, v(y)))| ≤ c/a` for every `a > 0`
  and `b`, and `∑_X 1/v, ∑_Y 1/v ≤ S`, then
  `|∑_{X^r} kern Ψ a b - ∑_{Y^r} kern Ψ a b| ≤ c r S^{r-1}/a`;
* `sum_inj_eq` : the injective tuples: `∑_{f injective} Ξ(f(Fin r)) = r! ∑_{T ⊆ A, |T| = r} Ξ(T)`;
* `nonInj_le` : the tuples with a repeated coordinate carry product weight at most
  `C(r,2) Q S^{r-2}`, `Q = ∑ 1/v²`.
-/

@[expose] public section

open Finset

namespace BaseRange.Tele

variable {ι : Type*} (v : ι → ℝ)

/-- `∑_{f : Fin r → A} Φ(v ∘ f)`. -/
noncomputable def tsumR (A : Finset ι) (r : ℕ) (Φ : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ f ∈ Fintype.piFinset (fun _ : Fin r => A), Φ (v ∘ f)

lemma tsumR_zero (A : Finset ι) (Φ : (Fin 0 → ℝ) → ℝ) : tsumR v A 0 Φ = Φ Fin.elim0 := by
  unfold tsumR
  have : Fintype.piFinset (fun _ : Fin 0 => A) = {Fin.elim0} := by
    ext f; simp only [Fintype.mem_piFinset, IsEmpty.forall_iff, true_iff, Finset.mem_singleton]
    funext i; exact i.elim0
  rw [this, Finset.sum_singleton]
  congr 1; funext i; exact i.elim0

lemma tsumR_succ (A : Finset ι) (r : ℕ) (Φ : (Fin (r + 1) → ℝ) → ℝ) :
    tsumR v A (r + 1) Φ = ∑ x ∈ A, tsumR v A r (fun t => Φ (Fin.cons (v x) t)) := by
  classical
  unfold tsumR
  have h := Finset.filter_piFinset_eq_map_consEquiv (α := fun _ : Fin (r + 1) => ι)
    (fun _ => A) (fun _ => True)
  simp only [Finset.filter_true] at h
  rw [h, Finset.sum_map, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.consEquiv]
  · simp [Fin.consEquiv]

/-- `max` folded over a list from `b`. -/
lemma foldr_max_comm (l : List ℝ) (b z : ℝ) : max z (l.foldr max b) = l.foldr max (max b z) := by
  induction l with
  | nil => simp [max_comm]
  | cons y l ih =>
    simp only [List.foldr_cons]
    rw [← ih, max_left_comm]

/-- The kernel `Ψ(a ∏ tᵢ, max(b, max tᵢ))`. -/
noncomputable def kern (Ψ : ℝ → ℝ → ℝ) (a b : ℝ) {r : ℕ} (t : Fin r → ℝ) : ℝ :=
  Ψ (a * ∏ i, t i) ((List.ofFn t).foldr max b)

lemma kern_cons (Ψ : ℝ → ℝ → ℝ) (a b x : ℝ) {r : ℕ} (t : Fin r → ℝ) :
    kern Ψ a b (Fin.cons x t : Fin (r + 1) → ℝ) = kern Ψ (a * x) (max b x) t := by
  unfold kern
  rw [Fin.prod_cons, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.foldr_cons]
  rw [foldr_max_comm]
  congr 1
  · ring

lemma sum_prod_inv (A : Finset ι) (r : ℕ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin r => A), ∏ i, (1 / v (f i)) = (∑ x ∈ A, 1 / v x) ^ r := by
  rw [Finset.sum_pow']

/-- **The telescoping bound** (Step 3 of the proof of Lemma 7.3(b), symmetric form). -/
theorem tele {κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι) (Y : Finset κ')
    (hvX : ∀ x ∈ X, 0 < vX x) (hvY : ∀ y ∈ Y, 0 < vY y)
    (Ψ : ℝ → ℝ → ℝ) {c S : ℝ} (hc : 0 ≤ c) (hS : 0 ≤ S)
    (hone : ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      |∑ x ∈ X, Ψ (a * vX x) (max b (vX x)) - ∑ y ∈ Y, Ψ (a * vY y) (max b (vY y))| ≤ c / a)
    (hSX : ∑ x ∈ X, 1 / vX x ≤ S) (hSY : ∑ y ∈ Y, 1 / vY y ≤ S) :
    ∀ r : ℕ, ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      |tsumR vX X r (kern Ψ a b) - tsumR vY Y r (kern Ψ a b)| ≤ c * r * S ^ (r - 1) / a := by
  intro r
  induction r with
  | zero =>
    intro a _ b
    rw [tsumR_zero, tsumR_zero]; simp
  | succ r ih =>
    intro a ha b
    rw [tsumR_succ, tsumR_succ]
    simp_rw [kern_cons]
    set M := ∑ x ∈ X, tsumR vY Y r (kern Ψ (a * vX x) (max b (vX x)))
    have h1 : |∑ x ∈ X, tsumR vX X r (kern Ψ (a * vX x) (max b (vX x))) - M| ≤
        c * r * S ^ (r - 1) * S / a := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ x ∈ X, |tsumR vX X r (kern Ψ (a * vX x) (max b (vX x))) -
          tsumR vY Y r (kern Ψ (a * vX x) (max b (vX x)))| ≤
          c * r * S ^ (r - 1) / a * (1 / vX x) := by
        intro x hx
        have := ih (a * vX x) (mul_pos ha (hvX x hx)) (max b (vX x))
        refine this.trans (le_of_eq ?_)
        have := hvX x hx
        field_simp
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum]
      have h0 : 0 ≤ c * r * S ^ (r - 1) / a := by positivity
      calc c * r * S ^ (r - 1) / a * ∑ x ∈ X, 1 / vX x ≤ c * r * S ^ (r - 1) / a * S :=
            mul_le_mul_of_nonneg_left hSX h0
        _ = c * r * S ^ (r - 1) * S / a := by ring
    have h2 : |M - ∑ y ∈ Y, tsumR vY Y r (kern Ψ (a * vY y) (max b (vY y)))| ≤ c * S ^ r / a := by
      simp only [M, tsumR]
      rw [Finset.sum_comm, Finset.sum_comm (s := Y), ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ t ∈ Fintype.piFinset (fun _ : Fin r => Y),
          |∑ x ∈ X, kern Ψ (a * vX x) (max b (vX x)) (vY ∘ t) -
            ∑ y ∈ Y, kern Ψ (a * vY y) (max b (vY y)) (vY ∘ t)| ≤ c / a * ∏ i, (1 / vY (t i)) := by
        intro t ht
        have htp : ∀ i, 0 < vY (t i) := fun i => hvY _ (Fintype.mem_piFinset.mp ht i)
        have hpos : 0 < a * ∏ i, (vY ∘ t) i := mul_pos ha (Finset.prod_pos fun i _ => htp i)
        have key := hone (a * ∏ i, (vY ∘ t) i) hpos ((List.ofFn (vY ∘ t)).foldr max b)
        have e : ∀ z : ℝ, kern Ψ (a * z) (max b z) (vY ∘ t) =
            Ψ ((a * ∏ i, (vY ∘ t) i) * z) (max ((List.ofFn (vY ∘ t)).foldr max b) z) := by
          intro z
          unfold kern
          rw [← foldr_max_comm, max_comm]
          congr 1; ring
        simp only [e]
        refine key.trans (le_of_eq ?_)
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
        simp only [Function.comp]
        field_simp
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum, sum_prod_inv vY]
      have h0 : 0 ≤ c / a := div_nonneg hc ha.le
      have hY0 : 0 ≤ ∑ y ∈ Y, 1 / vY y := Finset.sum_nonneg fun y hy => (one_div_pos.mpr
        (hvY y hy)).le
      calc c / a * (∑ y ∈ Y, 1 / vY y) ^ r ≤ c / a * S ^ r :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hSY r) h0
        _ = c * S ^ r / a := by ring
    have h3 : c * r * S ^ (r - 1) * S = c * r * S ^ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp
      · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h]
    calc |∑ x ∈ X, tsumR vX X r (kern Ψ (a * vX x) (max b (vX x))) -
          ∑ y ∈ Y, tsumR vY Y r (kern Ψ (a * vY y) (max b (vY y)))|
        ≤ |∑ x ∈ X, tsumR vX X r (kern Ψ (a * vX x) (max b (vX x))) - M| +
          |M - ∑ y ∈ Y, tsumR vY Y r (kern Ψ (a * vY y) (max b (vY y)))| := abs_sub_le _ _ _
      _ ≤ c * r * S ^ (r - 1) * S / a + c * S ^ r / a := add_le_add h1 h2
      _ = c * ((r + 1 : ℕ) : ℝ) * S ^ (r + 1 - 1) / a := by
          rw [h3, Nat.add_sub_cancel]; push_cast; ring

/-! ### Injective tuples and finsets -/

lemma foldr_ofFn_eq_fold (b : ℝ) {r : ℕ} (g : Fin r → ℝ) :
    (List.ofFn g).foldr max b = (Finset.univ : Finset (Fin r)).fold max b g := by
  unfold Finset.fold
  rw [Fin.univ_val_map, Multiset.coe_fold_r]

/-- For an injective tuple, the kernel only depends on its image. -/
lemma kern_eq_image [DecidableEq ι] (Ψ : ℝ → ℝ → ℝ) (a b : ℝ) {r : ℕ} {f : Fin r → ι}
    (hf : Function.Injective f) :
    kern Ψ a b (v ∘ f) = Ψ (a * ∏ j ∈ Finset.univ.image f, v j)
      ((Finset.univ.image f).fold max b v) := by
  unfold kern
  rw [foldr_ofFn_eq_fold, Finset.prod_image (fun x _ y _ h => hf h),
    Finset.fold_image (fun x _ y _ h => hf h)]
  rfl

/-- The injective tuples with a given image `T`, `|T| = r`, number `r!`. -/
lemma card_fiber [DecidableEq ι] (A T : Finset ι) (r : ℕ) (hT : T ∈ A.powersetCard r) :
    ((Fintype.piFinset (fun _ : Fin r => A)).filter
      (fun f => Function.Injective f ∧ Finset.univ.image f = T)).card = r.factorial := by
  classical
  obtain ⟨hTA, hTr⟩ := Finset.mem_powersetCard.mp hT
  have hcard : Fintype.card (Fin r) = Fintype.card T := by simp [hTr]
  obtain e := Fintype.equivOfCardEq hcard
  have hc : Fintype.card (Fin r ≃ T) = r.factorial := by
    rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [← hc, ← Finset.card_univ (α := (Fin r ≃ T))]
  symm
  refine Finset.card_bij (fun (σ : Fin r ≃ T) (_ : σ ∈ (Finset.univ : Finset (Fin r ≃ T))) =>
    fun k => (σ k : ι)) ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => hTA (σ k).2, fun k k' h => σ.injective (Subtype.ext h), ?_⟩
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩; exact (σ k).2
    · intro hj; exact ⟨σ.symm ⟨j, hj⟩, by simp⟩
  · intro σ _ σ' _ h
    ext k
    exact congrFun h k
  · intro f hf
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
    obtain ⟨-, hinj, himg⟩ := hf
    have hmem : ∀ k, f k ∈ T := fun k => himg ▸ Finset.mem_image_of_mem f (Finset.mem_univ k)
    refine ⟨Equiv.ofBijective (fun k => ⟨f k, hmem k⟩) ⟨fun k k' h => hinj (congrArg Subtype.val h),
      fun j => ?_⟩, Finset.mem_univ _, ?_⟩
    · have : (j : ι) ∈ Finset.univ.image f := himg ▸ j.2
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp this
      exact ⟨k, Subtype.ext hk⟩
    · funext k; rfl

/-- **The injective tuples**: `∑_{f injective} Ξ(f(Fin r)) = r! ∑_{T ⊆ A, |T| = r} Ξ(T)`. -/
theorem sum_inj_eq [DecidableEq ι] (A : Finset ι) (r : ℕ) (Ξ : Finset ι → ℝ) :
    ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => A)).filter Function.Injective,
      Ξ (Finset.univ.image f) = r.factorial * ∑ T ∈ A.powersetCard r, Ξ T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f => Finset.univ.image f)
    (t := A.powersetCard r)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Ξ T) (fun f hf => by
      rw [(Finset.mem_filter.mp hf).2])]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    rw [card_fiber A T r hT]
  · intro f hf
    obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
    rw [Fintype.mem_piFinset] at hf1
    rw [Finset.mem_powersetCard]
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj; exact hf1 k
    · rw [Finset.card_image_of_injective _ hf2]; simp

/-! ### The tuples with a repeated coordinate -/

lemma sum_prod_special (A : Finset ι) (r : ℕ) (i : Fin r) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A), (1 / v (t i)) * ∏ k, (1 / v (t k)) =
      (∑ x ∈ A, 1 / v x ^ 2) * (∑ x ∈ A, 1 / v x) ^ (r - 1) := by
  classical
  set g : Fin r → ι → ℝ := fun k x => if k = i then 1 / v x ^ 2 else 1 / v x
  have e : ∀ t : Fin r → ι, (1 / v (t i)) * ∏ k, (1 / v (t k)) = ∏ k, g k (t k) := by
    intro t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _
      (Finset.mem_univ i)]
    simp only [g, if_pos rfl]
    rw [Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
    rw [sq]; field_simp
  rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_prod_piFinset]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [g, if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ => ∑ x ∈ A, 1 / v x)
      (fun k hk => by simp only [if_neg (Finset.ne_of_mem_erase hk)]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- **The non-injective tuples**: with `S = ∑_A 1/v`, `Q = ∑_A 1/v²` and `v > 0` on `A`,
`∑_{f ¬injective} ∏ 1/v(fᵢ) ≤ C(r,2) Q S^{r-2}`. -/
theorem nonInj_le [DecidableEq ι] (A : Finset ι) (hv : ∀ x ∈ A, 0 < v x) :
    ∀ r : ℕ, ∑ f ∈ (Fintype.piFinset (fun _ : Fin r => A)).filter (fun f => ¬ Function.Injective f),
      ∏ k, (1 / v (f k)) ≤
        (r.choose 2 : ℝ) * (∑ x ∈ A, 1 / v x ^ 2) * (∑ x ∈ A, 1 / v x) ^ (r - 2) := by
  classical
  set S := ∑ x ∈ A, 1 / v x
  set Q := ∑ x ∈ A, 1 / v x ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun x hx => (one_div_pos.mpr (hv x hx)).le
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun x hx => (one_div_pos.mpr (pow_pos (hv x hx) 2)).le
  have hW : ∀ r (f : Fin r → ι), f ∈ Fintype.piFinset (fun _ : Fin r => A) →
      0 ≤ ∏ k, (1 / v (f k)) := fun r f hf =>
    Finset.prod_nonneg fun k _ => (one_div_pos.mpr (hv _ (Fintype.mem_piFinset.mp hf k))).le
  intro r
  induction r with
  | zero =>
    have : (Fintype.piFinset (fun _ : Fin 0 => A)).filter
        (fun f => ¬ Function.Injective f) = ∅ := by
      ext f; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
      intro _ a; exact a.elim0
    rw [this]; simp
  | succ r ih =>
    -- peel the first coordinate
    have h := Finset.filter_piFinset_eq_map_consEquiv (α := fun _ : Fin (r + 1) => ι)
      (fun _ => A) (fun _ => True)
    simp only [Finset.filter_true] at h
    rw [h, Finset.filter_map, Finset.sum_map]
    rw [Finset.sum_filter]
    simp only [Equiv.coe_toEmbedding, Function.comp]
    rw [Finset.sum_product]
    have hbound : ∀ x ∈ A, ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A),
        (if ¬ Function.Injective ((Fin.consEquiv fun _ => ι) (x, t)) then
          ∏ k, (1 / v (((Fin.consEquiv fun _ => ι) (x, t)) k)) else 0) ≤
        (1 / v x) * (∑ t ∈ (Fintype.piFinset (fun _ : Fin r => A)).filter
          (fun f => ¬ Function.Injective f), ∏ k, (1 / v (t k))) +
        (1 / v x) * ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A),
          (∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k)) := by
      intro x hx
      rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t ht => ?_
      have hWt := hW r t ht
      have hcons : ∏ k, (1 / v (((Fin.consEquiv fun _ => ι) (x, t)) k)) =
          (1 / v x) * ∏ k, (1 / v (t k)) := by
        simp [Fin.consEquiv, Fin.prod_univ_succ]; ring
      have hinj : Function.Injective ((Fin.consEquiv fun _ => ι) (x, t)) ↔
          Function.Injective t ∧ x ∉ Set.range t := by
        simp [Fin.consEquiv, Fin.cons_injective_iff, and_comm]
      have hvx : 0 < 1 / v x := one_div_pos.mpr (hv x hx)
      have hcnt : 0 ≤ ∑ i, if t i = x then (1 : ℝ) else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      by_cases hc : Function.Injective ((Fin.consEquiv fun _ => ι) (x, t))
      · rw [if_neg (not_not.mpr hc)]
        have : 0 ≤ 1 / v x * (if ¬ Function.Injective t then ∏ k, 1 / v (t k) else 0) := by
          apply mul_nonneg hvx.le; split_ifs <;> first | exact hWt | exact le_rfl
        have : 0 ≤ 1 / v x * ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, 1 / v (t k)) :=
          mul_nonneg hvx.le (mul_nonneg hcnt hWt)
        linarith
      · rw [if_pos hc, hcons]
        rw [hinj, not_and_or, not_not] at hc
        rcases hc with hc | hc
        · rw [if_pos hc]
          have : 0 ≤ 1 / v x * ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, 1 / v (t k)) :=
            mul_nonneg hvx.le (mul_nonneg hcnt hWt)
          linarith
        · obtain ⟨i, hi⟩ := hc
          have h1 : (1 : ℝ) ≤ ∑ i, if t i = x then (1 : ℝ) else 0 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos hi]
            have : 0 ≤ ∑ k ∈ Finset.univ.erase i, if t k = x then (1 : ℝ) else 0 :=
              Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
            linarith
          have h2 : 0 ≤ 1 / v x * (if ¬ Function.Injective t then ∏ k, 1 / v (t k) else 0) := by
            apply mul_nonneg hvx.le; split_ifs <;> first | exact hWt | exact le_rfl
          have h3 : 1 / v x * ∏ k, 1 / v (t k) ≤
              1 / v x * ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, 1 / v (t k)) := by
            apply mul_le_mul_of_nonneg_left _ hvx.le
            nlinarith
          linarith
    refine (Finset.sum_le_sum hbound).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    -- the second sum: `∑_x (1/v x) ∑_t #{i : t i = x} W(t) = ∑_i ∑_t (1/v(t i)) W(t) = r Q S^{r-1}`
    have hsec : ∑ x ∈ A, (1 / v x) * ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A),
        (∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k)) = r * Q * S ^ (r - 1) := by
      have e1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin r => A), ∑ x ∈ A, (1 / v x) *
          ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k))) =
          ∑ i, (1 / v (t i)) * ∏ k, (1 / v (t k)) := by
        intro t ht
        have hin : ∀ i, ∑ x ∈ A, (1 / v x) * (if t i = x then (1 : ℝ) else 0) = 1 / v (t i) := by
          intro i
          rw [Finset.sum_eq_single (t i)]
          · simp
          · intro x _ hx; rw [if_neg (Ne.symm hx)]; simp
          · intro hx; exact absurd (Fintype.mem_piFinset.mp ht i) hx
        calc ∑ x ∈ A, (1 / v x) * ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k)))
            = (∑ i, ∑ x ∈ A, (1 / v x) * (if t i = x then (1 : ℝ) else 0)) *
                ∏ k, (1 / v (t k)) := by
              rw [Finset.sum_comm, Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [← Finset.mul_sum, mul_assoc]
          _ = ∑ i, (1 / v (t i)) * ∏ k, (1 / v (t k)) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by rw [hin i]
      calc ∑ x ∈ A, (1 / v x) * ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A),
            (∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k))
          = ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A), ∑ x ∈ A, (1 / v x) *
              ((∑ i, if t i = x then (1 : ℝ) else 0) * ∏ k, (1 / v (t k))) := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        _ = ∑ t ∈ Fintype.piFinset (fun _ : Fin r => A),
              ∑ i, (1 / v (t i)) * ∏ k, (1 / v (t k)) := Finset.sum_congr rfl e1
        _ = ∑ i : Fin r, Q * S ^ (r - 1) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => sum_prod_special v A r i
        _ = r * Q * S ^ (r - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    rw [hsec]
    have hih := ih
    calc S * (∑ t ∈ (Fintype.piFinset (fun _ : Fin r => A)).filter
            (fun f => ¬ Function.Injective f), ∏ k, (1 / v (t k))) + r * Q * S ^ (r - 1)
        ≤ S * ((r.choose 2 : ℝ) * Q * S ^ (r - 2)) + r * Q * S ^ (r - 1) := by
          have := mul_le_mul_of_nonneg_left hih hS
          linarith
      _ ≤ ((r + 1).choose 2 : ℝ) * Q * S ^ (r + 1 - 2) := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right]
          push_cast
          rcases Nat.lt_or_ge r 2 with hr | hr
          · interval_cases r <;> simp
          · have e1 : S * S ^ (r - 2) = S ^ (r - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [show S * ((r.choose 2 : ℝ) * Q * S ^ (r - 2)) =
              (r.choose 2 : ℝ) * Q * (S * S ^ (r - 2)) by ring, e1]
            apply le_of_eq; ring

end BaseRange.Tele
