module

public import RequestProject.Beurling.Noise.KRVarWidth
public import RequestProject.Beurling.Noise.Saias59

/-!
# Corollary 5.17 (dyadic weights of the kernels)

For a Beurling system `P` (its `j`-th prime labelled by the `j`-th rational prime, as in
`Saias59.lean`, so the levels are the positive integers `n = iota e` and `V n = val e`), a
start `x`, a decision order `tw` and the nominal filters, let `C_n` be the nominal kernels with
varying widths (`kerV`, Theorem 5.15). With

  `W^nom_x(u) = ∑_{x/n ∈ [u, 2u)} TV(C_n)/n`  (`Wnom`),
  `W^sh_x(v) = ∑_{x/e ∈ [v, 2v)} |c_e|/e`      (`BeurlingSystem.Wsh`, Corollary 5.9),

* `cor_5_17_a` : (a) for `u ≥ X₀⁻/2`,
  `W^nom_x(u) ≤ W^sh_x(u) + ½λ₀ ∑_{m ≥ 2} H_ord(m) m^{ε-2} W^sh_x(um)`
  (the sum over `m` is finite: the terms with `m > x/u` vanish; we sum over `m ≤ x/u`);
* `cor_5_17_b` : (b) for every start `y ∈ [X₀⁻, x]` (correction #90: the range `[X₀⁻, X₀)` is
  included) and `u ≥ X₀⁻/2`,
  `W^nom_y(u) ≤ C_S [(1 + ½λ₀A₀) log(2u) + ½λ₀A₁]/log y`, given Corollary 5.9 and bounds `A₀`,
  `A₁` for the sums `∑_{2 ≤ m} H_ord(m) m^{ε-2}` and `∑ H_ord(m) m^{ε-2} log m` of `P`
  (`HordSums`); `cor_5_17_b_CN` : `≤ C_N log(2u)/log y` with `C_N = C_S(2.04 + 4.71/log X₀)`
  when `1 + ½λ₀A₀ ≤ 2.04`, `½λ₀A₁ ≤ 4.71` and `log(2u) ≥ log X₀`;
* `cor_5_17_c` : (c) `∑_n TV(C_n)/n ≤ (1 + ½λ₀A₀) ∑_e |c_e|/e` (the sum over the levels
  `x/n ≥ X₀⁻`; the others have `C_n = 0`, `kerV_eq_zero_of_lt`), hence `≤ 2.04 (log x + B₁)`
  given the harmonic bound of Lemma 5.5's consequences.
-/

@[expose] public section

open Finset MeasureTheory Set BeurlingSystem
open scoped ENNReal

namespace KR

variable (P : BeurlingSystem)

/-- The nominal kernel with varying widths, at level `n`, for the start `x`. -/
noncomputable abbrev kN (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x : ℝ) (n : ℕ) : ℝ → ℝ :=
  kerV P.labelVal x H (nomFilter P.labelVal x tw X0m) n

/-- The nominal masses `c_n` for the start `x`. -/
noncomputable abbrev cN (tw : ℕ → ℝ) (X0m x : ℝ) (n : ℕ) : ℝ :=
  mass (nomFilter P.labelVal x tw X0m) n

/-- The levels `n` with `x/n ∈ [u, 2u)`. -/
noncomputable def NW (x u : ℝ) : Finset ℕ :=
  ((P.elems (x / u)).filter (fun e => u ≤ x / P.val e ∧ x / P.val e < 2 * u)).image iota

/-- `W^nom_x(u) = ∑_{x/n ∈ [u, 2u)} TV(C_n)/n`. -/
noncomputable def Wnom (H : ℝ → ℝ) (tw : ℕ → ℝ) (X0m x u : ℝ) : ℝ :=
  ∑ n ∈ NW P x u, (eVariationOn (kN P H tw X0m x n) univ).toReal / LemmaM.valN P.labelVal n

lemma valN_labelVal_pos (n : ℕ) : 0 < LemmaM.valN P.labelVal n :=
  LemmaM.valN_pos _ fun r _ => P.one_le_labelVal r

/-- Every `n ≥ 1` with `V n ≤ X` is `iota e` for an element `e` of value `≤ X`. -/
lemma mem_image_iota {n : ℕ} (hn : n ≠ 0) {X : ℝ} (hX : LemmaM.valN P.labelVal n ≤ X) :
    n ∈ (P.elems X).image iota := by
  have hq : ∀ r ∈ n.primeFactors, r < qp (n + 1) := by
    intro r hr
    have h1 : r ≤ n := Nat.le_of_mem_primeFactors hr
    have h2 : n + 1 ≤ qp (n + 1) := qp_strictMono.id_le (n + 1)
    omega
  obtain ⟨e, -, he⟩ := exists_iota_eq hn hq
  refine Finset.mem_image.mpr ⟨e, ?_, he⟩
  rw [mem_elems, ← P.valN_iota, he]; exact hX

lemma mem_NW {x u : ℝ} (hu : 0 < u) {n : ℕ} :
    n ∈ NW P x u ↔ n ≠ 0 ∧ u ≤ x / LemmaM.valN P.labelVal n ∧
      x / LemmaM.valN P.labelVal n < 2 * u := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at he
    rw [P.valN_iota]
    exact ⟨(iota_pos e).ne', he.2.1, he.2.2⟩
  · rintro ⟨hn, h1, h2⟩
    have hV := KR.valN_labelVal_pos P n
    have hX : LemmaM.valN P.labelVal n ≤ x / u := by
      rw [le_div_iff₀ hu]; rw [le_div_iff₀ hV] at h1; linarith
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (KR.mem_image_iota P hn hX)
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    rw [← P.valN_iota]; exact ⟨h1, h2⟩

/-- `W^sh_x(v)` as a sum over the levels, with the nominal masses (Lemma 5.5). -/
lemma Wsh_eq (tw : ℕ → ℝ) (X0m x v : ℝ) :
    P.Wsh tw X0m x v = ∑ n ∈ NW P x v, |cN P tw X0m x n| / LemmaM.valN P.labelVal n := by
  unfold Wsh NW
  rw [Finset.sum_image (fun a _ b _ h => iota_injective h)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [P.valN_iota, show cN P tw X0m x (iota e) = (LemmaM.coeff tw P.labelVal X0m x (iota e) : ℝ)
    from mass_eq_coeff _ _ _ _ _]

/-! ## The per-level bound -/

lemma eVariationOn_stepF_le (a : ℝ) : eVariationOn (stepF a) univ ≤ 1 := by
  have hmono : Monotone (stepF a) := by
    intro s t hst
    unfold stepF
    by_cases h1 : a ≤ s
    · rw [if_pos h1, if_pos (h1.trans hst)]
    · rw [if_neg h1]; split_ifs <;> norm_num
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, -⟩ := p
  have hnn : ∀ i ∈ Finset.range n, 0 ≤ stepF a (u (i + 1)) - stepF a (u i) :=
    fun i _ => sub_nonneg.mpr (hmono (hu (Nat.le_succ i)))
  have e : ∑ i ∈ Finset.range n, edist (stepF a (u (i + 1))) (stepF a (u i)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, (stepF a (u (i + 1)) - stepF a (u i))) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [edist_dist, Real.dist_eq, abs_of_nonneg (hnn i hi)]
  rw [e, Finset.sum_range_sub (fun i => stepF a (u i))]
  apply ENNReal.ofReal_le_one.mpr
  have h1 : stepF a (u n) ≤ 1 := by unfold stepF; split_ifs <;> norm_num
  have h2 : 0 ≤ stepF a (u 0) := by unfold stepF; split_ifs <;> norm_num
  linarith

variable {P}

/-- The per-level bound behind (a): for a level `n` with `x/n ≥ X₀⁻/2`,
`TV(C_n) ≤ |c_n| + ½λ₀ ∑_{f ∣ n, 1<f<n} |c_f| H_ord(n/f) (n/f)^ε f/n`
(Theorem 5.15 with `H_f/H_n ≤ (n/f)^ε`, eq. (RH)). -/
lemma level_bound {H : ℝ → ℝ} {X0m ε θ lam0 : ℝ} {tw : ℕ → ℝ} {x : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) {n : ℕ} (hn : n ≠ 0)
    (hpos : X0m / 2 ≤ x / LemmaM.valN P.labelVal n) :
    (eVariationOn (kN P H tw X0m x n) univ).toReal ≤ |cN P tw X0m x n| + 1 / 2 * lam0 *
      ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m x f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * LemmaM.valN P.labelVal (n / f) ^ ε *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) := by
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have : kN P H tw X0m x 1 = stepF x := kerV_one _ _ _ _
    rw [this, show cN P tw X0m x 1 = 1 from mass_one _]
    have hf : (Nat.divisors 1).filter (fun f => 1 < f ∧ f < 1) = ∅ := by
      ext f; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
    rw [hf, Finset.sum_empty, mul_zero, add_zero, abs_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      ((eVariationOn_stepF_le x).trans ENNReal.ofReal_one.ge)
  obtain ⟨⟨hTV, -⟩, -⟩ := theorem_5_15_nominal (x := x) hP hval2 ht hlam hx h2
  refine (ENNReal.toReal_le_of_le_ofReal ?_ hTV).trans ?_
  · have := Finset.sum_nonneg (s := n.divisors.filter (fun e => 1 < e ∧ e < n))
      (f := fun e => |mass (nomFilter P.labelVal x tw X0m) e| *
        (Hlev P.labelVal x H e / Hlev P.labelVal x H n) * (BSCert.X0Band.Hord (n / e) : ℝ) *
          (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal n)) fun e _ => by
      have := hP.reg.pos (posn P.labelVal x e)
      have := hP.reg.pos (posn P.labelVal x n)
      have := KR.valN_labelVal_pos P e
      have := KR.valN_labelVal_pos P n
      unfold Hlev; positivity
    have : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
    positivity
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by linarith [hP.theta_nonneg])
  refine Finset.sum_le_sum fun f hf => ?_
  have hfd := (Finset.mem_filter.mp hf)
  have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd.1
  have hHn := hP.reg.pos (posn P.labelVal x n)
  have hw1 : 1 ≤ LemmaM.valN P.labelVal (n / f) := LemmaM.one_le_valN _ hval
  have hRH : Hlev P.labelVal x H f ≤ LemmaM.valN P.labelVal (n / f) ^ ε *
      Hlev P.labelVal x H n := by
    unfold Hlev
    rw [posn_mul hval hfn hn]
    exact hP.RH _ _ (by unfold posn; exact hpos) hw1
  have hratio : Hlev P.labelVal x H f / Hlev P.labelVal x H n ≤
      LemmaM.valN P.labelVal (n / f) ^ ε := by
    unfold Hlev at hRH ⊢; rw [div_le_iff₀ hHn]; exact hRH
  have h0 : 0 ≤ |mass (nomFilter P.labelVal x tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
      (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n) := by
    have := KR.valN_labelVal_pos P f
    have := KR.valN_labelVal_pos P n
    positivity
  calc |mass (nomFilter P.labelVal x tw X0m) f| *
        (Hlev P.labelVal x H f / Hlev P.labelVal x H n) * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)
      = (|mass (nomFilter P.labelVal x tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)) *
          (Hlev P.labelVal x H f / Hlev P.labelVal x H n) := by ring
    _ ≤ (|mass (nomFilter P.labelVal x tw X0m) f| * (BSCert.X0Band.Hord (n / f) : ℝ) *
          (LemmaM.valN P.labelVal f / LemmaM.valN P.labelVal n)) *
          LemmaM.valN P.labelVal (n / f) ^ ε := mul_le_mul_of_nonneg_left hratio h0
    _ = _ := by ring

/-! ## The chain-sum reindexing -/

/-- `∑_{n ∈ A} ∑_{f ∣ n, 1<f<n} G(f, n/f) ≤ ∑_{m ∈ M} ∑_{f ∈ F m} G(f, m)` when every pair
`(f, n/f)` occurs on the right and `G ≥ 0`. -/
lemma sum_divisors_le {A M : Finset ℕ} {F : ℕ → Finset ℕ} (G : ℕ → ℕ → ℝ)
    (hG : ∀ f m, 0 ≤ G f m)
    (hAM : ∀ n ∈ A, ∀ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
      n / f ∈ M ∧ f ∈ F (n / f)) :
    ∑ n ∈ A, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) ≤
      ∑ m ∈ M, ∑ f ∈ F m, G f m := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  set S := A.sigma fun n => n.divisors.filter (fun f => 1 < f ∧ f < n)
  set i : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun p => ⟨p.1 / p.2, p.2⟩
  have hinj : Set.InjOn i S := by
    intro p hp q hq hpq
    simp only [S, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_filter,
      Nat.mem_divisors] at hp hq
    simp only [i, Sigma.mk.injEq, heq_eq_eq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hp1 : p.1 = p.1 / p.2 * p.2 := (Nat.div_mul_cancel hp.2.1.1).symm
    have hq1 : q.1 = q.1 / q.2 * q.2 := (Nat.div_mul_cancel hq.2.1.1).symm
    rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
    simp only at h1 h2 hp1 hq1 ⊢
    subst h2
    have : a = c := by rw [hp1, hq1, h1]
    subst this; rfl
  calc ∑ p ∈ S, G p.2 (p.1 / p.2) = ∑ q ∈ S.image i, G q.2 q.1 :=
        (Finset.sum_image (f := fun q : (Σ _ : ℕ, ℕ) => G q.2 q.1) hinj).symm
    _ ≤ ∑ q ∈ M.sigma F, G q.2 q.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
          have hp' := Finset.mem_sigma.mp hp
          obtain ⟨h1, h2⟩ := hAM p.1 hp'.1 p.2 hp'.2
          exact Finset.mem_sigma.mpr ⟨h1, h2⟩
        · intro q _ _; exact hG _ _

/-- The cofactors `2 ≤ m` with `m ≤ x/u`. -/
noncomputable def MS (Q : BeurlingSystem) (x u : ℝ) : Finset ℕ :=
  ((Q.elems (x / u)).image iota).filter (2 ≤ ·)

/-- **Corollary 5.17(a)**: for `u ≥ X₀⁻/2`,
`W^nom_x(u) ≤ W^sh_x(u) + ½λ₀ ∑_{2 ≤ m ≤ x/u} H_ord(m) m^{ε-2} W^sh_x(um)`. -/
theorem cor_5_17_a {H : ℝ → ℝ} {X0m ε θ lam0 : ℝ} {tw : ℕ → ℝ} {x u : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hu : X0m / 2 ≤ u) :
    Wnom P H tw X0m x u ≤ P.Wsh tw X0m x u + 1 / 2 * lam0 *
      ∑ m ∈ MS P x u, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN P.labelVal m ^ (ε - 2) *
        P.Wsh tw X0m x (u * LemmaM.valN P.labelVal m) := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hu0 : 0 < u := by linarith
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  set G : ℕ → ℕ → ℝ := fun f m => |cN P tw X0m x f| / V f *
    ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2))
  have hG : ∀ f m, 0 ≤ G f m := fun f m => by
    have := hV f; have := hV m; positivity
  -- per level
  have hlev : ∀ n ∈ NW P x u, (eVariationOn (kN P H tw X0m x n) univ).toReal / V n ≤
      |cN P tw X0m x n| / V n + 1 / 2 * lam0 *
        ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
    intro n hn
    obtain ⟨hn0, h1, -⟩ := (mem_NW P hu0).mp hn
    have hb := level_bound hP hp2 ht hlam hx hn0 (hu.trans h1)
    rw [div_le_iff₀ (hV n)]
    refine hb.trans (le_of_eq ?_)
    have hs : ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m x f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * V (n / f) ^ ε * (V f / V n) =
        (∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) * V n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfn : f ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
      have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
      have hf0 := hV f
      have hm0 := hV (n / f)
      simp only [G]
      rw [Real.rpow_sub hm0, Real.rpow_two, hVn]
      field_simp
    rw [hs, add_mul, div_mul_cancel₀ _ (hV n).ne']
    ring
  calc Wnom P H tw X0m x u
      ≤ ∑ n ∈ NW P x u, (|cN P tw X0m x n| / V n + 1 / 2 * lam0 *
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) :=
        Finset.sum_le_sum hlev
    _ = P.Wsh tw X0m x u + 1 / 2 * lam0 * ∑ n ∈ NW P x u,
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Wsh_eq]
    _ ≤ P.Wsh tw X0m x u + 1 / 2 * lam0 *
          ∑ m ∈ MS P x u, ∑ f ∈ NW P x (u * V m), G f m := by
        gcongr
        refine sum_divisors_le G hG fun n hn f hf => ?_
        obtain ⟨hn0, h1, h2⟩ := (mem_NW P hu0).mp hn
        obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
        have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
        have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
        have hm2 : 2 ≤ n / f := by
          obtain ⟨k, hk⟩ := hfn
          have hf0 : 0 < f := by omega
          rw [hk, Nat.mul_div_cancel_left k hf0]
          by_contra hc; push_neg at hc
          interval_cases k <;> simp_all
        have hm0 : n / f ≠ 0 := by omega
        have hf0 : f ≠ 0 := by omega
        have hVm := hV (n / f)
        have hVf := hV f
        constructor
        · refine Finset.mem_filter.mpr ⟨KR.mem_image_iota P hm0 ?_, hm2⟩
          have : V (n / f) ≤ V n := LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0
          have h1' : V n ≤ x / u := by
            rw [le_div_iff₀ hu0]; rw [le_div_iff₀ (hV n)] at h1; linarith
          linarith
        · rw [mem_NW P (by positivity)]
          refine ⟨hf0, ?_, ?_⟩
          · have e : x / V f = x / V n * V (n / f) := by rw [hVn]; field_simp
            rw [e]; exact mul_le_mul_of_nonneg_right h1 hVm.le
          · have e : x / V f = x / V n * V (n / f) := by rw [hVn]; field_simp
            rw [e]; nlinarith
    _ = P.Wsh tw X0m x u + 1 / 2 * lam0 *
          ∑ m ∈ MS P x u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
            P.Wsh tw X0m x (u * V m) := by
        congr 2
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Wsh_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [G]; ring

/-! ## (b) and (c) -/

/-- The sums `A₀ = ∑_{m ≥ 2} H_ord(m) m^{ε-2}` and `A₁ = ∑_{m ≥ 2} H_ord(m) m^{ε-2} log m` of
the system `P` are at most `A₀`, `A₁` (every finite partial sum). For `ℕ` and `ε = 0.03` the
certificates `BSCert.Consts.Hord_sum_197_le`, `Hord_log_sum_197_le` give `2.07`, `9.42`; the
paper (§5.9.1, "Ordered factorisations") transfers the values to `𝒩` (they differ by less than
`X₀^{-0.1}`). -/
def HordSums (Q : BeurlingSystem) (ε A0 A1 : ℝ) : Prop :=
  ∀ s : Finset ℕ, (∀ m ∈ s, 2 ≤ m) →
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN Q.labelVal m ^ (ε - 2) ≤ A0 ∧
    ∑ m ∈ s, (BSCert.X0Band.Hord m : ℝ) * LemmaM.valN Q.labelVal m ^ (ε - 2) *
      Real.log (LemmaM.valN Q.labelVal m) ≤ A1

/-- Corollary 5.9 at the start `y`, as used in Corollary 5.17(b). -/
def SaiasAt (Q : BeurlingSystem) (tw : ℕ → ℝ) (X0m y CS : ℝ) : Prop :=
  ∀ v, X0m / 2 ≤ v → v ≤ y → Q.Wsh tw X0m y v ≤ CS * Real.log (2 * v) / Real.log y

/-- **Corollary 5.17(b)**: for a start `y ≥ X₀⁻` and `u ≥ X₀⁻/2` (with `u ≤ y`),
`W^nom_y(u) ≤ C_S [(1 + ½λ₀A₀) log(2u) + ½λ₀A₁]/log y`. -/
theorem cor_5_17_b {H : ℝ → ℝ} {X0m ε θ lam0 CS A0 A1 : ℝ} {tw : ℕ → ℝ} {y u : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hy : X0m ≤ y) (hy1 : 1 < y) (hu : X0m / 2 ≤ u)
    (huy : u ≤ y) (hCS : 0 ≤ CS) (hS : SaiasAt P tw X0m y CS) (hA : HordSums P ε A0 A1)
    (hu1 : 1 / 2 ≤ u) :
    Wnom P H tw X0m y u ≤
      CS * ((1 + 1 / 2 * lam0 * A0) * Real.log (2 * u) + 1 / 2 * lam0 * A1) / Real.log y := by
  have hX := hP.X0m_pos
  have hu0 : 0 < u := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hl2u : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  have ha := cor_5_17_a hP hp2 ht hlam hy hu (P := P) (tw := tw) (u := u)
  have hMS : ∀ m ∈ MS P y u, 2 ≤ m := fun m hm => (Finset.mem_filter.mp hm).2
  obtain ⟨hA0, hA1⟩ := hA (MS P y u) hMS
  have hterm : ∀ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
      P.Wsh tw X0m y (u * V m) ≤ CS / Real.log y * ((BSCert.X0Band.Hord m : ℝ) *
        V m ^ (ε - 2) * Real.log (2 * u) + (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
          Real.log (V m)) := by
    intro m hm
    obtain ⟨hm1, -⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm1
    have hVe : V (iota e) ≤ y / u := by
      simp only [V]; rw [P.valN_iota]; exact (P.mem_elems.mp he)
    have hV1 : 1 ≤ V (iota e) := LemmaM.one_le_valN _ fun r _ => P.one_le_labelVal r
    have hv1 : X0m / 2 ≤ u * V (iota e) := by nlinarith
    have hv2 : u * V (iota e) ≤ y := by rw [le_div_iff₀ hu0] at hVe; linarith
    have hw := hS _ hv1 hv2
    have hc0 : 0 ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) := by
      have := hV (iota e); positivity
    have e2 : Real.log (2 * (u * V (iota e))) = Real.log (2 * u) + Real.log (V (iota e)) := by
      rw [← mul_assoc, Real.log_mul (by positivity) (hV _).ne']
    calc (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          P.Wsh tw X0m y (u * V (iota e))
        ≤ (BSCert.X0Band.Hord (iota e) : ℝ) * V (iota e) ^ (ε - 2) *
          (CS * Real.log (2 * (u * V (iota e))) / Real.log y) :=
          mul_le_mul_of_nonneg_left hw hc0
      _ = _ := by rw [e2]; field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hW0 := hS u hu huy
  have hB : CS / Real.log y * ((∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) *
      Real.log (2 * u) + ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2) *
        Real.log (V m)) ≤ CS / Real.log y * (A0 * Real.log (2 * u) + A1) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hCS hly.le)
    have := mul_le_mul_of_nonneg_right hA0 hl2u
    linarith
  calc Wnom P H tw X0m y u
      ≤ P.Wsh tw X0m y u + 1 / 2 * lam0 * ∑ m ∈ MS P y u, (BSCert.X0Band.Hord m : ℝ) *
          V m ^ (ε - 2) * P.Wsh tw X0m y (u * V m) := ha
    _ ≤ CS * Real.log (2 * u) / Real.log y + 1 / 2 * lam0 *
          (CS / Real.log y * (A0 * Real.log (2 * u) + A1)) := by
        gcongr
        exact hsum.trans hB
    _ = _ := by field_simp; ring

/-- **Corollary 5.17(b)**, with `C_N = C_S(2.04 + 4.71/log X₀)`: if `1 + ½λ₀A₀ ≤ 2.04`,
`½λ₀A₁ ≤ 4.71` and `log X₀ ≤ log(2u)`, then `W^nom_y(u) ≤ C_N log(2u)/log y`. -/
theorem cor_5_17_b_CN {CS A0 A1 lam0 X0 y u : ℝ} (hCS : 0 ≤ CS) (hy1 : 1 < y)
    (hX0 : 0 < Real.log X0) (hu : Real.log X0 ≤ Real.log (2 * u))
    (h0 : 1 + 1 / 2 * lam0 * A0 ≤ 2.04) (h1 : 1 / 2 * lam0 * A1 ≤ 4.71) {W : ℝ}
    (hW : W ≤ CS * ((1 + 1 / 2 * lam0 * A0) * Real.log (2 * u) + 1 / 2 * lam0 * A1) /
      Real.log y) :
    W ≤ CS * (2.04 + 4.71 / Real.log X0) * Real.log (2 * u) / Real.log y := by
  have hly : 0 < Real.log y := Real.log_pos hy1
  refine hW.trans (div_le_div_of_nonneg_right ?_ hly.le)
  rw [mul_assoc CS (2.04 + 4.71 / Real.log X0)]
  apply mul_le_mul_of_nonneg_left _ hCS
  have hl : 0 ≤ Real.log (2 * u) := by linarith
  have h47 : 4.71 ≤ 4.71 / Real.log X0 * Real.log (2 * u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hX0]; nlinarith
  nlinarith

/-- The levels with `x/n ≥ X₀⁻`. -/
noncomputable def NAll (Q : BeurlingSystem) (x X0m : ℝ) : Finset ℕ :=
  (Q.elems (x / X0m)).image iota

/-- Below `X₀⁻` the nominal kernels vanish: `C_n = 0` for `n ≥ 2` with `x/n < X₀⁻`. -/
lemma kN_eq_zero {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m x : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hlt : x / LemmaM.valN P.labelVal n < X0m) : kN P H tw X0m x n = fun _ => 0 := by
  funext t
  rw [kN, kerV_eq _ _ _ _ hn]
  have : ∀ d ∈ n.properDivisors, nomFilter P.labelVal x tw X0m d n *
      Qv H (LemmaM.valN P.labelVal (n / d)) (kerV P.labelVal x H
        (nomFilter P.labelVal x tw X0m) d) t = 0 := by
    intro d _
    unfold nomFilter; rw [if_neg (fun h => absurd h.2 (not_le.mpr hlt)), zero_mul]
  rw [Finset.sum_eq_zero this, neg_zero]

/-- **Corollary 5.17(c)**: `∑_n TV(C_n)/n ≤ (1 + ½λ₀A₀) ∑_e |c_e|/e`, the sums over the
levels `x/n ≥ X₀⁻` (the other levels have `C_n = 0`, `kN_eq_zero`). -/
theorem cor_5_17_c {H : ℝ → ℝ} {X0m ε θ lam0 A0 A1 : ℝ} {tw : ℕ → ℝ} {x : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hA : HordSums P ε A0 A1) :
    ∑ n ∈ NAll P x X0m, (eVariationOn (kN P H tw X0m x n) univ).toReal /
        LemmaM.valN P.labelVal n ≤
      (1 + 1 / 2 * lam0 * A0) * ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| /
        LemmaM.valN P.labelVal n := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  set V := LemmaM.valN P.labelVal
  have hV : ∀ n, 0 < V n := KR.valN_labelVal_pos P
  set G : ℕ → ℕ → ℝ := fun f m => |cN P tw X0m x f| / V f *
    ((BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2))
  have hG : ∀ f m, 0 ≤ G f m := fun f m => by
    have := hV f; have := hV m; positivity
  have hmem : ∀ n ∈ NAll P x X0m, n ≠ 0 ∧ X0m ≤ x / V n := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hn
    refine ⟨(iota_pos e).ne', ?_⟩
    have := P.mem_elems.mp he
    simp only [V]; rw [P.valN_iota]
    rw [le_div_iff₀ (P.val_pos e)]; rw [le_div_iff₀ hX] at this; linarith
  set M := ((P.elems (x / X0m)).image iota).filter (2 ≤ ·)
  have hlev : ∀ n ∈ NAll P x X0m, (eVariationOn (kN P H tw X0m x n) univ).toReal / V n ≤
      |cN P tw X0m x n| / V n + 1 / 2 * lam0 *
        ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f) := by
    intro n hn
    obtain ⟨hn0, h1⟩ := hmem n hn
    have hb := level_bound hP hp2 ht hlam hx hn0 (by linarith)
    rw [div_le_iff₀ (hV n)]
    refine hb.trans (le_of_eq ?_)
    have hs : ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), |cN P tw X0m x f| *
        (BSCert.X0Band.Hord (n / f) : ℝ) * V (n / f) ^ ε * (V f / V n) =
        (∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) * V n := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hfn : f ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hf).1
      have hVn : V n = V f * V (n / f) := valN_div_mul hval hfn hn0
      have hf0 := hV f
      have hm0 := hV (n / f)
      simp only [G]
      rw [Real.rpow_sub hm0, Real.rpow_two, hVn]
      field_simp
    rw [hs, add_mul, div_mul_cancel₀ _ (hV n).ne']
    ring
  have hre : ∑ n ∈ NAll P x X0m, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
      G f (n / f) ≤ ∑ m ∈ M, ∑ f ∈ NAll P x X0m, G f m := by
    refine sum_divisors_le G hG fun n hn f hf => ?_
    obtain ⟨hn0, h1⟩ := hmem n hn
    obtain ⟨hfd, hf1, hfn'⟩ := Finset.mem_filter.mp hf
    have hfn : f ∣ n := Nat.dvd_of_mem_divisors hfd
    have hm2 : 2 ≤ n / f := by
      obtain ⟨k, hk⟩ := hfn
      have hf0 : 0 < f := by omega
      rw [hk, Nat.mul_div_cancel_left k hf0]
      by_contra hc; push_neg at hc
      interval_cases k <;> simp_all
    have hVn1 : V n ≤ x / X0m := by
      rw [le_div_iff₀ hX]; rw [le_div_iff₀ (hV n)] at h1; linarith
    constructor
    · refine Finset.mem_filter.mpr ⟨KR.mem_image_iota P (by omega) ?_, hm2⟩
      have : V (n / f) ≤ V n := LemmaM.valN_le_of_dvd _ hval (Nat.div_dvd_of_dvd hfn) hn0
      linarith
    · refine KR.mem_image_iota P (by omega) ?_
      have : V f ≤ V n := LemmaM.valN_le_of_dvd _ hval hfn hn0
      linarith
  have hM2 : ∀ m ∈ M, 2 ≤ m := fun m hm => (Finset.mem_filter.mp hm).2
  obtain ⟨hA0, -⟩ := hA M hM2
  have hcs0 : 0 ≤ ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / V n :=
    Finset.sum_nonneg fun n _ => by have := hV n; positivity
  have hfin : ∑ m ∈ M, ∑ f ∈ NAll P x X0m, G f m =
      (∑ m ∈ M, (BSCert.X0Band.Hord m : ℝ) * V m ^ (ε - 2)) *
        ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / V n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [G]; ring
  calc ∑ n ∈ NAll P x X0m, (eVariationOn (kN P H tw X0m x n) univ).toReal / V n
      ≤ ∑ n ∈ NAll P x X0m, (|cN P tw X0m x n| / V n + 1 / 2 * lam0 *
          ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n), G f (n / f)) :=
        Finset.sum_le_sum hlev
    _ = ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / V n + 1 / 2 * lam0 *
          ∑ n ∈ NAll P x X0m, ∑ f ∈ n.divisors.filter (fun f => 1 < f ∧ f < n),
            G f (n / f) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / V n + 1 / 2 * lam0 *
          (A0 * ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / V n) := by
        gcongr
        exact hre.trans ((le_of_eq hfin).trans (mul_le_mul_of_nonneg_right hA0 hcs0))
    _ = _ := by ring

/-- **Corollary 5.17(c)** with the harmonic bound `∑_{e : x/e ≥ X₀⁻} 1/e ≤ log x + B₁`
(the consequence of Lemma 5.5, `B₁ = 1` in the paper) and `1 + ½λ₀A₀ ≤ 2.04`:
`∑_n TV(C_n)/n ≤ 2.04 (log x + B₁)`. -/
theorem cor_5_17_c_harm {H : ℝ → ℝ} {X0m ε θ lam0 A0 A1 B1 : ℝ} {tw : ℕ → ℝ} {x : ℝ}
    (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j) (ht : ∀ p, p.Prime → 0 < tw p)
    (hlam : 1 + 2 * θ ≤ lam0) (hx : X0m ≤ x) (hA : HordSums P ε A0 A1)
    (h0 : 1 + 1 / 2 * lam0 * A0 ≤ 2.04)
    (hharm : ∑ n ∈ NAll P x X0m, 1 / LemmaM.valN P.labelVal n ≤ Real.log x + B1) :
    ∑ n ∈ NAll P x X0m, (eVariationOn (kN P H tw X0m x n) univ).toReal /
        LemmaM.valN P.labelVal n ≤ 2.04 * (Real.log x + B1) := by
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hX := hP.X0m_pos
  have hc := cor_5_17_c hP hp2 ht hlam hx hA (P := P) (tw := tw)
  have hle : ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / LemmaM.valN P.labelVal n ≤
      ∑ n ∈ NAll P x X0m, 1 / LemmaM.valN P.labelVal n := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hn
    apply div_le_div_of_nonneg_right _ (KR.valN_labelVal_pos P _).le
    rw [show cN P tw X0m x (iota e) = (LemmaM.coeff tw P.labelVal X0m x (iota e) : ℝ)
      from mass_eq_coeff _ _ _ _ _]
    exact_mod_cast LemmaM.abs_coeff_le_one tw P.labelVal ht hval hX.le hx (iota_pos e)
  have hnn : 0 ≤ ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / LemmaM.valN P.labelVal n :=
    Finset.sum_nonneg fun n _ => by have := KR.valN_labelVal_pos P n; positivity
  have hA0 : 0 ≤ 1 + 1 / 2 * lam0 * A0 := by
    have := (hA ∅ (by simp)).1
    simp at this
    have : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
    nlinarith
  calc _ ≤ (1 + 1 / 2 * lam0 * A0) * ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| /
        LemmaM.valN P.labelVal n := hc
    _ ≤ 2.04 * ∑ n ∈ NAll P x X0m, |cN P tw X0m x n| / LemmaM.valN P.labelVal n :=
        mul_le_mul_of_nonneg_right h0 hnn
    _ ≤ 2.04 * (Real.log x + B1) := by linarith

end KR

end
