module

public import RequestProject.Beurling.Model.Identify

/-!
# The base case of Lemma 3.6 for the constructed model

For the constructed model (`Std.limModel`, `ϑ_s = 1/2`, `X₀` even), following the proof of
Lemma 3.6 (count identity) in §3.5:

* `limModel_T_X₀` : `T(X₀) = X₀` (`A` is empty at low heights);
* `limModel_T_jump` : at an `X₀`-smooth integer `n > X₀`, `T(n) ≥ X₀ + 3/4` (the unit jump of
  `Ψ(·, X₀)` at `n`, the continuous part being continuous);
* `limModel_slot_one` : `X₀ < s_{j₀} ≤ X₀ + 2` (`X₀ + 2` is even, hence rigid);
* `limModel_init_gap` : no composite has value in `(X₀, s_{j₀})`;
* `limModel_init_count` : `X₀ = #(composites < s_{j₀}) + #(rational primes) + 1`, i.e.
  `V_{j₀ - 1} = j₀`.

Elements made of rational primes only are identified with `X₀`-smooth integers by unique
factorization (`num`, `num_inj`, `exists_num`); an element with a jittered prime factor that is
composite has value `≥ 2 · 7X₀/8 > s_{j₀}` (`placed_large`).
-/

@[expose] public section

open Set Real Target Oscillation Absorbed Construction DesignedZero Decomp AbsorbEmpty
  CaplLink SlotModel Greedy QueueMono Filter Topology

namespace BModel

variable {θ : ℝ} {X₀ : ℕ} {U : ℕ → ℝ}

/-! ### Elements over the rational primes -/

section Rational

variable {M : SlotModel X₀}

/-- The rational prime of a realised index (`0` for a jittered one). -/
def ratV : RealisedIdx M → ℕ
  | Sum.inl p => p.1
  | Sum.inr _ => 0

/-- An element made of rational primes only. -/
def RatOnly (e : RealisedIdx M →₀ ℕ) : Prop := ∀ k, e (Sum.inr k) = 0

/-- The integer `∏ p^{e_p}` of an element. -/
def num (e : RealisedIdx M →₀ ℕ) : ℕ := e.prod fun i k => ratV i ^ k

lemma mem_support_ratOnly {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) {i : RealisedIdx M}
    (hi : i ∈ e.support) : ∃ p, i = Sum.inl p := by
  cases i with
  | inl p => exact ⟨p, rfl⟩
  | inr k => exact absurd (he k) (Finsupp.mem_support_iff.mp hi)

lemma idxVal_ratOnly (H : ℝ → ℝ) (U : ℕ → ℝ) {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) :
    idxVal M H U e = (num e : ℝ) := by
  unfold idxVal num Finsupp.prod
  push_cast
  refine Finset.prod_congr rfl fun i hi => ?_
  obtain ⟨p, rfl⟩ := mem_support_ratOnly he hi
  rfl

lemma num_eq_map (e : RealisedIdx M →₀ ℕ) :
    num e = (Finsupp.mapDomain ratV e).prod fun p k => p ^ k := by
  unfold num
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

lemma support_map_prime {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) :
    ∀ p ∈ (Finsupp.mapDomain ratV e).support, p.Prime ∧ p < X₀ := by
  classical
  intro p hp
  have := Finsupp.mapDomain_support hp
  rw [Finset.mem_image] at this
  obtain ⟨i, hi, rfl⟩ := this
  obtain ⟨q, rfl⟩ := mem_support_ratOnly he hi
  exact q.2

lemma factorization_num {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) :
    (num e).factorization = Finsupp.mapDomain ratV e := by
  rw [num_eq_map]
  exact Nat.prod_pow_factorization_eq_self fun p hp => (support_map_prime he p hp).1

lemma ratV_injOn : Set.InjOn (ratV (M := M)) (Set.range Sum.inl) := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ h
  simp only [ratV] at h
  rw [Subtype.ext h]

lemma map_ratV_inl {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) (p : {p : ℕ // p.Prime ∧ p < X₀}) :
    Finsupp.mapDomain ratV e p.1 = e (Sum.inl p) := by
  have hS : (e.support : Set (RealisedIdx M)) ⊆ Set.range Sum.inl := by
    intro i hi
    obtain ⟨q, rfl⟩ := mem_support_ratOnly he hi
    exact ⟨q, rfl⟩
  exact Finsupp.mapDomain_apply' _ e hS ratV_injOn ⟨p, rfl⟩

/-- **Unique factorization**: `num` is injective on rational elements. -/
lemma num_inj {e e' : RealisedIdx M →₀ ℕ} (he : RatOnly e) (he' : RatOnly e')
    (h : num e = num e') : e = e' := by
  have hf := congrArg Nat.factorization h
  rw [factorization_num he, factorization_num he'] at hf
  ext i
  cases i with
  | inl p => rw [← map_ratV_inl he, ← map_ratV_inl he', hf]
  | inr k => rw [he k, he' k]

lemma num_pos {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) : 0 < num e := by
  unfold num Finsupp.prod
  refine Finset.prod_pos fun i hi => ?_
  obtain ⟨p, rfl⟩ := mem_support_ratOnly he hi
  exact pow_pos p.2.1.pos _

lemma ratOnly_zero : RatOnly (0 : RealisedIdx M →₀ ℕ) := fun _ => rfl

lemma num_zero : num (0 : RealisedIdx M →₀ ℕ) = 1 := by simp [num]

lemma ratOnly_single (p : {p : ℕ // p.Prime ∧ p < X₀}) :
    RatOnly (Finsupp.single (Sum.inl p : RealisedIdx M) 1) := fun k => by simp

lemma num_single (p : {p : ℕ // p.Prime ∧ p < X₀}) :
    num (Finsupp.single (Sum.inl p : RealisedIdx M) 1) = p.1 := by
  simp [num, ratV]

/-- Every `X₀`-smooth integer is the value of a rational element. -/
lemma exists_num {n : ℕ} (hn : n ≠ 0) (hp : ∀ p ∈ n.primeFactors, p < X₀) :
    ∃ e : RealisedIdx M →₀ ℕ, RatOnly e ∧ num e = n := by
  classical
  set val : {p : ℕ // p.Prime ∧ p < X₀} → ℕ := Subtype.val
  have hval : Function.Injective val := Subtype.val_injective
  set e₀ := Finsupp.comapDomain val n.factorization hval.injOn
  have hmap : Finsupp.mapDomain val e₀ = n.factorization := by
    apply Finsupp.mapDomain_comapDomain _ hval
    intro p hpm
    have hpf : p ∈ n.primeFactors := by rw [← Nat.support_factorization]; exact hpm
    exact ⟨⟨p, Nat.prime_of_mem_primeFactors hpf, hp p hpf⟩, rfl⟩
  refine ⟨Finsupp.mapDomain (Sum.inl : _ → RealisedIdx M) e₀, fun k => ?_, ?_⟩
  · rw [Finsupp.mapDomain_notin_range]
    rintro ⟨p, hp⟩
    exact Sum.inl_ne_inr hp
  · rw [num_eq_map, ← Finsupp.mapDomain_comp]
    have : (ratV ∘ (Sum.inl : _ → RealisedIdx M)) = val := rfl
    rw [this, hmap]
    exact Nat.factorization_prod_pow_eq_self hn

/-- A rational element is composite iff its integer is neither `1` nor prime. -/
lemma composite_iff {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) :
    2 ≤ e.sum (fun _ n => n) ↔ num e ≠ 1 ∧ ¬ (num e).Prime := by
  constructor
  · intro h2
    constructor
    · intro h1
      have : e = 0 := num_inj he ratOnly_zero (by rw [h1, num_zero])
      rw [this, Finsupp.sum_zero_index] at h2
      omega
    · intro hpr
      have hf := factorization_num he
      rw [hpr.factorization] at hf
      have hmem : num e ∈ (Finsupp.mapDomain ratV e).support := by
        rw [← hf]; simp
      obtain ⟨hq, hqX⟩ := support_map_prime he _ hmem
      have : e = Finsupp.single (Sum.inl ⟨num e, hq, hqX⟩) 1 :=
        num_inj he (ratOnly_single _) (by rw [num_single])
      rw [this] at h2
      simp at h2
  · rintro ⟨h1, hpr⟩
    by_contra hlt
    push_neg at hlt
    interval_cases hs : (e.sum fun _ n => n)
    · have := (finsupp_sum_eq_zero_iff e).mp hs
      rw [this, num_zero] at h1
      exact h1 rfl
    · obtain ⟨i, rfl⟩ := (finsupp_sum_eq_one_iff e).mp hs
      obtain ⟨p, rfl⟩ := mem_support_ratOnly he (i := i) (by simp)
      rw [num_single] at hpr
      exact hpr p.2.1

end Rational

/-! ### The constructed model near `X₀` -/

namespace Std

variable (h : Std θ X₀ U)
include h

/-- `A` has no element `≤ X₀` (Lemma 6.27: `y(n) < X₀⁻` at low heights). -/
lemma countA_X₀ : countA (absSet X₀ (DM h.limModel U)) X₀ = 0 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 h.hX
  refine countA_eq_zero_of_low hX0 h.hX (fun a ha => ?_) X₀ hX1.le ?_
  · obtain ⟨-, e, he, -, -, k, hk, -, hvk⟩ := ha
    exact ⟨_, realisedVal_inr_ge h.hU h.hX h.limModel_low ⟨k, he k hk⟩, hvk⟩
  · have := h.hX
    nlinarith

/-- `T(X₀) = X₀`. -/
lemma limModel_T_X₀ : h.limModel.T X₀ = X₀ := by
  rw [h.limModel_T_eq, targetD_split θ _ le_rfl, contD_at]
  unfold jumpD jumpPart
  rw [h.countA_X₀]
  ring

lemma limModel_T_ge {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : (X₀ : ℝ) ≤ h.limModel.T x := by
  rw [← h.limModel_T_X₀]; exact h.limModel.T_mono hx

lemma limModel_T_le {x : ℝ} (hx : x ≤ X₀) : h.limModel.T x ≤ X₀ := by
  rw [← h.limModel_T_X₀]; exact h.limModel.T_mono hx

/-- **The unit jump of `T` at a rigid integer** `n > X₀`: `T(n) ≥ X₀ + 3/4`. -/
lemma limModel_T_jump {n : ℕ} (hn : n ∈ X₀.smoothNumbers) (hXn : (X₀ : ℝ) < n) :
    (X₀ : ℝ) + 3 / 4 ≤ h.limModel.T n := by
  classical
  set D := DM h.limModel U
  have hLD : LocFinD D := locFinD_DM h.hX h.hU _
  have hc := (contD_continuousOn h.hθ h.hX D hLD) (n : ℝ) (le_of_lt hXn)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp hc (1 / 4) (by norm_num)
  set y := max (X₀ : ℝ) (n - δ / 2) with hy
  have hyX : (X₀ : ℝ) ≤ y := le_max_left _ _
  have hyn : y < n := max_lt hXn (by linarith)
  have hd : dist y n < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have := le_max_right (X₀ : ℝ) (n - δ / 2)
    linarith
  have hC := hball (Set.mem_Ici.mpr hyX) hd
  rw [Real.dist_eq] at hC
  have hC' := (abs_lt.mp hC).2
  -- the jump of `Ψ` at `n`
  have hΨ : (Rankin.smoothCount X₀ y : ℝ) + 1 ≤ Rankin.smoothCount X₀ n := by
    have hfl : ⌊y⌋₊ < n := (Nat.floor_lt (by linarith)).mpr hyn
    have hsub : Nat.smoothNumbersUpTo ⌊y⌋₊ X₀ ⊂ Nat.smoothNumbersUpTo ⌊(n : ℝ)⌋₊ X₀ := by
      rw [Nat.floor_natCast]
      refine Finset.ssubset_iff_of_subset (fun m hm => ?_) |>.mpr ⟨n, ?_, ?_⟩
      · rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
        exact ⟨hm.1.trans hfl.le, hm.2⟩
      · rw [Nat.mem_smoothNumbersUpTo]; exact ⟨le_rfl, hn⟩
      · rw [Nat.mem_smoothNumbersUpTo]; omega
    have := Finset.card_lt_card hsub
    unfold Rankin.smoothCount
    exact_mod_cast this
  have hA := countA_mono (absSet_locFin (X₀ := X₀) hLD) hyn.le
  have hTy := h.limModel_T_ge hyX
  rw [h.limModel_T_eq, targetD_split θ D hyX] at hTy
  rw [h.limModel_T_eq, targetD_split θ D hXn.le]
  unfold jumpD jumpPart at hTy ⊢
  linarith

lemma level_one : h.limModel.level 1 = X₀ + 1 / 2 := by
  unfold SlotModel.level; rw [h.limModel_ϑ]; push_cast; ring

omit h in
/-- A non-prime integer `2 ≤ m < 2X₀` is `X₀`-smooth. -/
lemma smooth_of_lt (m : ℕ) (hm2 : 2 ≤ m) (hm : m < 2 * X₀) (hpr : ¬ m.Prime) :
    m ∈ X₀.smoothNumbers := by
  rw [Nat.mem_smoothNumbers]
  refine ⟨by omega, fun p hp => ?_⟩
  have hpd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  obtain ⟨c, hc⟩ := hpd
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h2 | h2
    · interval_cases c
      · omega
      · rw [mul_one] at hc; exact absurd (hc ▸ hpp) hpr
    · exact h2
  nlinarith [hpp.two_le]

end Std

/-- **The first slot**: `X₀ < s_{j₀} ≤ X₀ + 2`. -/
theorem limModel_slot_one (h : Std θ X₀ U) (hev : Even X₀) :
    (X₀ : ℝ) < h.limModel.slot 1 ∧ h.limModel.slot 1 ≤ X₀ + 2 := by
  have h16 := h.X₀_big
  have hlev := h.level_one
  constructor
  · by_contra hle
    push_neg at hle
    have h1 := h.limModel.level_le_T_slot 1
    have h2 := h.limModel_T_le hle
    linarith
  · have hX4 : 4 ≤ X₀ := by
      have : (4 : ℝ) ≤ X₀ := by linarith
      exact_mod_cast this
    have hsm : X₀ + 2 ∈ X₀.smoothNumbers := by
      refine Std.smooth_of_lt _ (by omega) (by omega) fun hp => ?_
      have := (hp.even_iff).mp (by obtain ⟨r, hr⟩ := hev; exact ⟨r + 1, by omega⟩)
      omega
    have hj := h.limModel_T_jump hsm (by push_cast; linarith)
    push_cast at hj
    apply h.limModel.slot_le
    exact ⟨by linarith, by rw [hlev]; linarith⟩

/-! ### The base case of Lemma 3.6 -/

namespace Std

variable (h : Std θ X₀ U)
include h

/-- A composite with a jittered prime factor has value `≥ 2 · 7X₀/8`. -/
lemma placed_large {e : RealisedIdx h.limModel →₀ ℕ} (h2 : 2 ≤ e.sum (fun _ n => n))
    {k : {k // placedAt h.limModel k}} (hk : e (Sum.inr k) ≠ 0) :
    7 / 4 * (X₀ : ℝ) ≤ idxVal h.limModel (capH X₀) U e := by
  have hP := pos2_DM h.hX h.hU h.limModel_low
  have hmem : (Sum.inr k.1 : PIdx X₀) ∈ (mapE h.limModel e).support := by
    rw [Finsupp.mem_support_iff, mapE_apply_inr, dif_pos k.2]; exact hk
  have := two_mul_pval_le_eval hP (live_mapE h.limModel U e) (by rw [sum_mapE]; exact h2) hmem
  rw [eval_mapE] at this
  obtain ⟨hs, hv⟩ := primeValueOf_ge h.limModel h.hU h.hX h.limModel_low k.1
  have e1 : pval (X₀ := X₀) (DM h.limModel U) (Sum.inr k.1) =
      primeValueOf h.limModel (capH X₀) U k.1 := rfl
  linarith

lemma ratOnly_or (e : RealisedIdx h.limModel →₀ ℕ) :
    RatOnly e ∨ ∃ k : {k // placedAt h.limModel k}, e (Sum.inr k) ≠ 0 := by
  by_cases hr : RatOnly e
  · exact Or.inl hr
  · right; unfold RatOnly at hr; push_neg at hr; exact hr

omit h in
lemma num_smooth {M : SlotModel X₀} {e : RealisedIdx M →₀ ℕ} (he : RatOnly e) :
    num e ∈ X₀.smoothNumbers := by
  rw [Nat.mem_smoothNumbers]
  refine ⟨(num_pos he).ne', fun p hp => ?_⟩
  have hpf : p ∈ (num e).primeFactors :=
    Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp
  rw [← Nat.support_factorization, factorization_num he] at hpf
  exact (support_map_prime he p hpf).2

/-- A rational element of value `> X₀` has value `≥ s_{j₀}` (its value is a rigid integer). -/
lemma slot_one_le_num {e : RealisedIdx h.limModel →₀ ℕ} (he : RatOnly e)
    (hX : (X₀ : ℝ) < num e) : h.limModel.slot 1 ≤ num e := by
  have hj := h.limModel_T_jump (num_smooth he) hX
  apply h.limModel.slot_le
  have h16 := h.X₀_big
  exact ⟨by linarith, by rw [h.level_one]; linarith⟩

end Std

/-- **No composite has value in `(X₀, s_{j₀})`** (proof of Lemma 3.6). -/
theorem limModel_init_gap (h : Std θ X₀ U) (hev : Even X₀) :
    compIoo h.limModel (capH X₀) U X₀ (h.limModel.slot 1) = ∅ := by
  have h16 := h.X₀_big
  obtain ⟨-, hs1⟩ := limModel_slot_one h hev
  ext e
  simp only [compIoo, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h2, hlo, hhi⟩
  rcases h.ratOnly_or e with hr | ⟨k, hk⟩
  · rw [idxVal_ratOnly _ _ hr] at hlo hhi
    have := h.slot_one_le_num hr hlo
    linarith
  · have := h.placed_large h2 hk
    linarith

/-- **The base case of Lemma 3.6**: `X₀ = #(composites < s_{j₀}) + #(rational primes) + 1`. -/
theorem limModel_init_count (h : Std θ X₀ U) (hev : Even X₀) :
    (X₀ : ℝ) = ((compLt h.limModel (capH X₀) U (h.limModel.slot 1)).ncard : ℝ) +
      ({p : ℕ | p.Prime ∧ p < X₀}.ncard : ℝ) + 1 := by
  classical
  have h16 := h.X₀_big
  have hX4 : 4 ≤ X₀ := by
    have : (4 : ℝ) ≤ X₀ := by linarith
    exact_mod_cast this
  have hXp : ¬ X₀.Prime := fun hp => by
    have := hp.even_iff.mp hev; omega
  obtain ⟨hs0, hs1⟩ := limModel_slot_one h hev
  have hgap := limModel_init_gap h hev
  set S := Finset.Icc 1 X₀
  set C := S.filter fun n => n ≠ 1 ∧ ¬ n.Prime
  -- the composites below `s_{j₀}` are the composite integers in `[2, X₀]`
  have hcomp : (compLt h.limModel (capH X₀) U (h.limModel.slot 1)).ncard = C.card := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun e _ => num e) ?_ ?_ ?_
    · rintro e ⟨h2, hlt⟩
      rcases h.ratOnly_or e with hr | ⟨k, hk⟩
      · rw [idxVal_ratOnly _ _ hr] at hlt
        have hle : (num e : ℝ) ≤ X₀ := by
          by_contra hgt
          push_neg at hgt
          have := h.slot_one_le_num hr hgt
          linarith
        have hle' : num e ≤ X₀ := by exact_mod_cast hle
        simp only [C, S, Finset.coe_filter, Finset.mem_Icc, mem_setOf_eq]
        exact ⟨⟨num_pos hr, hle'⟩, (composite_iff hr).mp h2⟩
      · have := h.placed_large h2 hk
        linarith
    · rintro e e' ⟨h2, hlt⟩ ⟨h2', hlt'⟩ hee
      have hr : RatOnly e := by
        rcases h.ratOnly_or e with hr | ⟨k, hk⟩
        · exact hr
        · have := h.placed_large h2 hk; linarith
      have hr' : RatOnly e' := by
        rcases h.ratOnly_or e' with hr | ⟨k, hk⟩
        · exact hr
        · have := h.placed_large h2' hk; linarith
      exact num_inj hr hr' hee
    · intro n hn
      simp only [C, S, Finset.coe_filter, Finset.mem_Icc, mem_setOf_eq] at hn
      obtain ⟨⟨hn1, hnX⟩, hn1', hnp⟩ := hn
      obtain ⟨e, hr, he⟩ := exists_num (M := h.limModel) (n := n) (by omega) (fun p hp => by
        have hpn : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        rcases (hpn.trans hnX).lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd (heq ▸ Nat.prime_of_mem_primeFactors hp) hXp)
      refine ⟨e, ⟨(composite_iff hr).mpr (he ▸ ⟨hn1', hnp⟩), ?_⟩, he⟩
      rw [idxVal_ratOnly _ _ hr, he]
      have : (n : ℝ) ≤ X₀ := by exact_mod_cast hnX
      linarith
  -- the rational primes are the primes in `[1, X₀]`
  have hprimes : {p : ℕ | p.Prime ∧ p < X₀}.ncard = (S.filter Nat.Prime).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp only [S, Finset.coe_filter, Finset.mem_Icc, mem_setOf_eq]
    constructor
    · rintro ⟨hp, hpX⟩; exact ⟨⟨hp.one_lt.le, hpX.le⟩, hp⟩
    · rintro ⟨⟨-, hpX⟩, hp⟩
      exact ⟨hp, lt_of_le_of_ne hpX fun heq => hXp (heq ▸ hp)⟩
  -- `#[1, X₀] = #primes + #composites + 1`
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) Nat.Prime
  have hneg : S.filter (fun n => ¬ n.Prime) = insert 1 C := by
    ext n
    simp only [S, C, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨hn, hnp⟩
      by_cases h1 : n = 1
      · exact Or.inl h1
      · exact Or.inr ⟨hn, h1, hnp⟩
    · rintro (rfl | ⟨hn, -, hnp⟩)
      · exact ⟨⟨le_rfl, by omega⟩, Nat.not_prime_one⟩
      · exact ⟨hn, hnp⟩
  have h1C : (1 : ℕ) ∉ C := by simp [C]
  rw [hneg, Finset.card_insert_of_notMem h1C, Nat.card_Icc] at hsplit
  rw [hcomp, hprimes]
  have : (X₀ : ℝ) = ((S.filter Nat.Prime).card : ℝ) + (C.card : ℝ) + 1 := by
    have e : (S.filter Nat.Prime).card + (C.card + 1) = X₀ := by omega
    exact_mod_cast e.symm
  linarith

end BModel

end
