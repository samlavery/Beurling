module

public import RequestProject.Beurling.Noise.BSDefs

/-!
# Lemma 5.23 (threshold mass): definitions and the decomposition `n = k · m`

For a decision order `t` on the prime indices of a Beurling system `P` and a squarefree element
`n`, the threshold is `τ(n) = max_{p ∣ n} t(p) ∏_{q ∣ n, t(q) ≥ t(p)} q` (04e-lp.tex, Lemma 5.23).
`τ(n) ∈ [a, b)` is written `P.TauIn t a b n`: some prime attains `≥ a`, and all are `< b`
(this is `max ∈ [a, b)`).

* `threshSum t x δ = ∑_{n : τ(n) ∈ [x(1-δ), x)} 1/n` (over squarefree `n`; all such `n` have
  `n < x` when `t ≥ 1`, `val_lt_of_tauIn`);
* `Mset t x δ j`: the elements `m = ∏_{t(q) ≥ t(p_j)} q` that can occur with `p = p_j`:
  squarefree, `p_j ∣ m`, every prime of `m` is `t`-above `p_j`, and `t(p_j) m ∈ [x(1-δ), x)`;
* `Kset t x j`: the squarefree `k ≤ x` all of whose primes are `t`-below `p_j`;
* `threshSum_le_split` : the decomposition of the proof, `n ↦ (k, m)` injective:
  `threshSum ≤ ∑_{p_j ≤ x} (∑_{m ∈ Mset_j} 1/m)(∑_{k ∈ Kset_j} 1/k)`.
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `e` is squarefree. -/
def _root_.BeurlingSystem.Sqf (e : ℕ →₀ ℕ) : Prop := ∀ j, e j ≤ 1

/-- `∏_{q ∣ e, t(q) ≥ t(p_j)} q`. -/
noncomputable def Mprod (t : ℕ → ℝ) (e : ℕ →₀ ℕ) (j : ℕ) : ℝ :=
  ∏ i ∈ e.support.filter (fun i => t j ≤ t i), P.p i

/-- `τ(e) ∈ [a, b)` with `τ(e) = max_{j ∈ e} t(p_j) ∏_{t(q) ≥ t(p_j)} q`. -/
def TauIn (t : ℕ → ℝ) (a b : ℝ) (e : ℕ →₀ ℕ) : Prop :=
  (∃ j ∈ e.support, a ≤ t j * P.Mprod t e j) ∧ ∀ j ∈ e.support, t j * P.Mprod t e j < b

open scoped Classical in
/-- **The threshold mass** `∑_{n : τ(n) ∈ [x(1-δ), x)} 1/n` of Lemma 5.23. -/
noncomputable def threshSum (t : ℕ → ℝ) (x δ : ℝ) : ℝ :=
  ∑ e ∈ (P.elems x).filter (fun e => Sqf e ∧ P.TauIn t (x * (1 - δ)) x e), 1 / P.val e

open scoped Classical in
/-- The possible `m = p m'` for the prime `p = p_j`. -/
noncomputable def Mset (t : ℕ → ℝ) (x δ : ℝ) (j : ℕ) : Finset (ℕ →₀ ℕ) :=
  (P.elems x).filter (fun m => Sqf m ∧ j ∈ m.support ∧ (∀ i ∈ m.support, t j ≤ t i) ∧
    x * (1 - δ) ≤ t j * P.val m ∧ t j * P.val m < x)

open scoped Classical in
/-- The possible `k` for the prime `p = p_j`: squarefree, primes `t`-below `p_j`, `k ≤ x`. -/
noncomputable def Kset (t : ℕ → ℝ) (x : ℝ) (j : ℕ) : Finset (ℕ →₀ ℕ) :=
  (P.elems x).filter (fun k => Sqf k ∧ ∀ i ∈ k.support, t i < t j)

/-! ## Values of squarefree elements -/

lemma val_eq_prod_support {e : ℕ →₀ ℕ} (he : Sqf e) : P.val e = ∏ i ∈ e.support, P.p i := by
  unfold val Finsupp.prod
  refine Finset.prod_congr rfl fun i hi => ?_
  have h1 : e i = 1 := le_antisymm (he i) (Nat.one_le_iff_ne_zero.mpr
    (Finsupp.mem_support_iff.mp hi))
  simp only [h1, pow_one]

lemma one_le_prod_p (s : Finset ℕ) : 1 ≤ ∏ i ∈ s, P.p i := by
  calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ s, P.p i := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => (P.one_lt i).le

lemma prod_p_le_of_subset {s s' : Finset ℕ} (h : s ⊆ s') :
    ∏ i ∈ s, P.p i ≤ ∏ i ∈ s', P.p i := by
  rw [← Finset.prod_sdiff h]
  have h1 := P.one_le_prod_p (s' \ s)
  have h2 : 0 ≤ ∏ i ∈ s, P.p i := Finset.prod_nonneg fun i _ => (P.p_pos i).le
  nlinarith

/-- If `τ(e) < x` and `t ≥ 1`, then `e < x`: the `t`-least prime sees all of `e`. -/
lemma val_lt_of_tauIn {t : ℕ → ℝ} (ht : ∀ j, 1 ≤ t j) {a x : ℝ} {e : ℕ →₀ ℕ}
    (hs : Sqf e) (h : P.TauIn t a x e) : P.val e < x := by
  obtain ⟨⟨j0, hj0, -⟩, hall⟩ := h
  obtain ⟨j, hj, hmin⟩ := e.support.exists_min_image t ⟨j0, hj0⟩
  have hM : P.Mprod t e j = P.val e := by
    unfold Mprod
    rw [P.val_eq_prod_support hs, Finset.filter_true_of_mem fun i hi => hmin i hi]
  have := hall j hj
  rw [hM] at this
  have hv := P.one_le_val e
  nlinarith [ht j]

/-! ## The decomposition -/

lemma val_filter_mul (e : ℕ →₀ ℕ) (q : ℕ → Prop) [DecidablePred q] :
    P.val (e.filter q) * P.val (e.filter fun a => ¬ q a) = P.val e := by
  unfold val
  exact Finsupp.prod_filter_mul_prod_filter_not (f := e) (p := q) (g := fun j k => P.p j ^ k)

omit P in
lemma sqf_filter {e : ℕ →₀ ℕ} (he : Sqf e) (q : ℕ → Prop) [DecidablePred q] :
    Sqf (e.filter q) := by
  intro i
  by_cases h : q i
  · rw [Finsupp.filter_apply_pos _ _ h]; exact he i
  · rw [Finsupp.filter_apply_neg _ _ h]; exact Nat.zero_le _

lemma val_filter_le (e : ℕ →₀ ℕ) (q : ℕ → Prop) [DecidablePred q] :
    P.val (e.filter q) ≤ P.val e := by
  rw [← P.val_filter_mul e q]
  have h1 := P.one_le_val (e.filter fun a => ¬ q a)
  have h2 := P.one_le_val (e.filter q)
  nlinarith

open scoped Classical in
lemma val_filter_ge_eq {t : ℕ → ℝ} {e : ℕ →₀ ℕ} (hs : Sqf e) (j : ℕ) :
    P.val (e.filter fun i => t j ≤ t i) = P.Mprod t e j := by
  rw [P.val_eq_prod_support (sqf_filter hs _), Finsupp.support_filter]
  rfl

open scoped Classical in
lemma mem_Mset_of {t : ℕ → ℝ} {x δ : ℝ} {j : ℕ} {e : ℕ →₀ ℕ} (hex : P.val e ≤ x)
    (hs : Sqf e) (hj : j ∈ e.support) (h1 : x * (1 - δ) ≤ t j * P.Mprod t e j)
    (h2 : t j * P.Mprod t e j < x) :
    e.filter (fun i => t j ≤ t i) ∈ P.Mset t x δ j := by
  have hM := P.val_filter_ge_eq (t := t) hs j
  unfold Mset
  rw [Finset.mem_filter, mem_elems, hM]
  refine ⟨?_, sqf_filter hs _, ?_, fun i hi => ?_, h1, h2⟩
  · rw [← hM]; exact (P.val_filter_le e _).trans hex
  · rw [Finsupp.support_filter, Finset.mem_filter]; exact ⟨hj, le_rfl⟩
  · rw [Finsupp.support_filter, Finset.mem_filter] at hi; exact hi.2

open scoped Classical in
lemma mem_Kset_of {t : ℕ → ℝ} {x : ℝ} {j : ℕ} {e : ℕ →₀ ℕ} (hex : P.val e ≤ x)
    (hs : Sqf e) : e.filter (fun i => ¬ t j ≤ t i) ∈ P.Kset t x j := by
  unfold Kset
  rw [Finset.mem_filter, mem_elems]
  refine ⟨(P.val_filter_le e _).trans hex, sqf_filter hs _, fun i hi => ?_⟩
  rw [Finsupp.support_filter, Finset.mem_filter] at hi
  exact lt_of_not_ge hi.2

open scoped Classical in
/-- For a fixed prime index `j`, the elements of the threshold sum whose `j` passes the
threshold inject into `Mset_j × Kset_j` by `n ↦ (m, k)`, `n = m k`. -/
lemma sum_fixed_le (t : ℕ → ℝ) (x δ : ℝ) (j : ℕ) :
    ∑ e ∈ (P.elems x).filter (fun e => Sqf e ∧ j ∈ e.support ∧
        x * (1 - δ) ≤ t j * P.Mprod t e j ∧ t j * P.Mprod t e j < x), 1 / P.val e ≤
      (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k := by
  let φ : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) × (ℕ →₀ ℕ) := fun e =>
    (e.filter (fun i => t j ≤ t i), e.filter (fun i => ¬ t j ≤ t i))
  have hinj : ∀ A : Finset (ℕ →₀ ℕ), Set.InjOn φ A := by
    intro A e _ e' _ h
    have h1 := congrArg (fun q => q.1 + q.2) h
    simp only [φ, Finsupp.filter_pos_add_filter_neg] at h1
    exact h1
  let g : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) → ℝ := fun q => 1 / P.val q.1 * (1 / P.val q.2)
  calc _ = ∑ e ∈ (P.elems x).filter (fun e => Sqf e ∧ j ∈ e.support ∧
        x * (1 - δ) ≤ t j * P.Mprod t e j ∧ t j * P.Mprod t e j < x), g (φ e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [g, φ]
        rw [one_div_mul_one_div, P.val_filter_mul e (fun i => t j ≤ t i)]
    _ = ∑ q ∈ ((P.elems x).filter (fun e => Sqf e ∧ j ∈ e.support ∧
        x * (1 - δ) ≤ t j * P.Mprod t e j ∧ t j * P.Mprod t e j < x)).image φ, g q :=
        (Finset.sum_image (hinj _)).symm
    _ ≤ ∑ q ∈ P.Mset t x δ j ×ˢ P.Kset t x j, g q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
          obtain ⟨hex, hs, hj, h1, h2⟩ := Finset.mem_filter.mp he
          rw [mem_elems] at hex
          exact Finset.mem_product.mpr ⟨P.mem_Mset_of hex hs hj h1 h2, P.mem_Kset_of hex hs⟩
        · intro q _ _
          exact mul_nonneg (one_div_pos.mpr (P.val_pos _)).le (one_div_pos.mpr (P.val_pos _)).le
    _ = _ := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

open scoped Classical in
/-- **The decomposition of the proof of Lemma 5.23**:
`∑_{τ(n) ∈ [x(1-δ), x)} 1/n ≤ ∑_{p_j ≤ x} (∑_{m ∈ Mset_j} 1/m)(∑_{k ∈ Kset_j} 1/k)`. -/
theorem threshSum_le_split (t : ℕ → ℝ) (x δ : ℝ) :
    P.threshSum t x δ ≤ ∑ j ∈ P.primesLe x,
      (∑ m ∈ P.Mset t x δ j, 1 / P.val m) * ∑ k ∈ P.Kset t x j, 1 / P.val k := by
  unfold threshSum
  set S := (P.elems x).filter (fun e => Sqf e ∧ P.TauIn t (x * (1 - δ)) x e)
  set A : ℕ → Finset (ℕ →₀ ℕ) := fun j => (P.elems x).filter (fun e => Sqf e ∧
    j ∈ e.support ∧ x * (1 - δ) ≤ t j * P.Mprod t e j ∧ t j * P.Mprod t e j < x)
  have hpos : ∀ e, 0 ≤ 1 / P.val e := fun e => (one_div_pos.mpr (P.val_pos e)).le
  have h1 : ∑ e ∈ S, 1 / P.val e ≤ ∑ e ∈ S, ∑ j ∈ P.primesLe x,
      (if e ∈ A j then 1 / P.val e else 0) := by
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨hex, hs, ⟨j, hj, hge⟩, hall⟩ := Finset.mem_filter.mp he
    rw [mem_elems] at hex
    have hjx : j ∈ P.primesLe x := by
      rw [mem_primesLe]
      calc P.p j ≤ ∏ i ∈ e.support, P.p i :=
            by
              rw [← Finset.mul_prod_erase _ _ hj]
              have := P.one_le_prod_p (e.support.erase j)
              have := P.p_pos j
              nlinarith
        _ = P.val e := (P.val_eq_prod_support hs).symm
        _ ≤ x := hex
    have hjA : e ∈ A j := Finset.mem_filter.mpr
      ⟨(mem_elems P).mpr hex, hs, hj, hge, hall j hj⟩
    calc 1 / P.val e = if e ∈ A j then 1 / P.val e else 0 := by rw [if_pos hjA]
      _ ≤ ∑ j ∈ P.primesLe x, (if e ∈ A j then 1 / P.val e else 0) :=
          Finset.single_le_sum (f := fun j => if e ∈ A j then 1 / P.val e else 0)
            (fun j _ => by dsimp only; split_ifs; exacts [hpos e, le_rfl]) hjx
  refine h1.trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ∑ e ∈ S, (if e ∈ A j then 1 / P.val e else 0)
      ≤ ∑ e ∈ A j, 1 / P.val e := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro e _ _; exact hpos e
    _ ≤ _ := P.sum_fixed_le t x δ j

end BeurlingSystem

end
