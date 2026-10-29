module

public import RequestProject.Beurling.Model.Wire3

/-!
# Lemma 6.27(a) on `QC(< t) ∩ {E1 of time < t}`: `ρ_𝒜(u) ≤ (log u)⁻⁴`

At every height `u ≥ X₀` with `2y(2u) ≤ Z` (the (H_BS) horizon, `X₀ ≤ Z`, `4Z + 2 ≤ t`) and
`20u/log¹¹ u + 5 ≤ t` (the cluster events read by Lemma 6.26 at `u` have time `≲ 8u/log¹¹ u`):

* `cluster_of_QE'` : `cluster_of_QE` with the time condition on the cluster events themselves;
* `rhoA_le_QE` : `ρ_𝒜(u) ≤ (log u)⁻⁴` (Lemma 6.27(a), from Lemma 6.26 by
  `absorbedDensity_le_of_localCount`).
-/

@[expose] public section

open Set Real MeasureTheory Construction CaplLink Queue6 KR Absorbed AbsorbEmpty QueueMono

namespace BModel

variable {θ : ℝ} {X₀ : ℕ}

section

variable (hc : Cond θ X₀) (hev : Even X₀)

include hc hev in
/-- `cluster_of_QE` with the time condition on the cluster events read. -/
theorem cluster_of_QE' {t : ℕ} {ω : JitterΩ}
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n)
    (hTB : ∀ m, ttB X₀ m < t → ω ∈ tB (θ := θ) (X₀ := X₀) m) (h0 : Std θ X₀ ω)
    (hSG : ω ∈ SG (θ := θ) (X₀ := X₀)) {v : ℝ} (hv : (X₀ : ℝ) ≤ v)
    (hvt : ∀ n, zH X₀ n ≤ 4 * v / Real.log v ^ 11 → tE1 X₀ n < t) {m : ℕ}
    (hm : 8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2)
    (hmt : ttB X₀ m < t) :
    ClusterUpTo (realisedSystem h0.limModel (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11)
      (capM1 X₀ v) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hc.hX hv
  have hv0 : 0 < v := by linarith [one_lt_of_logX hX0 hc.hX]
  have hZv : 4 * v / Real.log v ^ 11 ≤ v := by
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ≤ Real.log v ^ 11 := by
      calc (4 : ℝ) ≤ Real.log v := by linarith
        _ ≤ Real.log v ^ 11 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith
  have hTBm : ω ∈ tB (θ := θ) (X₀ := X₀) m := hTB m hmt
  have hTB : ω ∈ tBound θ X₀ (8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1)) :=
    tBound_mono hm hTBm
  have hcl : ∀ n, zH X₀ n ≤ 4 * v / Real.log v ^ 11 → ω ∈ EclW hc hev n := by
    intro n hn
    have := hE1 n (hvt n hn)
    simpa [E1ev, dif_pos (And.intro hc hev)] using this
  have := clusterUpTo_of_eclW hc hev h0.hU hSG hZv hTB hcl
  rwa [constructedModel_eq h0] at this

include hc in
/-- The cluster events read at `v` have time `≤ 10v/log¹¹ v + 1`. -/
lemma tE1_le {v : ℝ} (_hv : (X₀ : ℝ) ≤ v) {n : ℕ} (hn : zH X₀ n ≤ 4 * v / Real.log v ^ 11) :
    (tE1 X₀ n : ℝ) < 10 * v / Real.log v ^ 11 + 1 := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hz0 : (X₀ : ℝ) / 2 ≤ zH X₀ n := by
    unfold zH; have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num); nlinarith
  have h2z : (X₀ : ℝ) ≤ 2 * zH X₀ n := by linarith
  have hH := four_capH_le hX0 hc.hX h2z
  unfold tE1
  have := Nat.ceil_lt_add_one (show 0 ≤ 2 * zH X₀ n + capH X₀ (2 * zH X₀ n) by
    have := capH_nonneg (X₀ : ℝ) (2 * zH X₀ n); linarith)
  have e : 10 * v / Real.log v ^ 11 = 2.5 * (4 * v / Real.log v ^ 11) := by ring
  linarith

include hc hev in
/-- **Lemma 6.27(a) on `QC(< t) ∩ {E1 of time < t}`**: `ρ_𝒜(u) ≤ (log u)⁻⁴` at `u ≥ X₀` with
`2y(2u) ≤ Z`, `X₀ ≤ Z`, `4Z + 2 ≤ t` and `20u/log¹¹ u + 5 ≤ t`. -/
theorem rhoA_le_QE {t : ℕ} {ω : JitterΩ} (hQC : ω ∈ QC (okQ θ X₀) (tq θ X₀) t)
    (hE1 : ∀ n, tE1 X₀ n < t → ω ∈ E1ev θ X₀ n) (hN : ω ∈ NiceEv θ X₀) {Z : ℝ}
    (hZX : (X₀ : ℝ) ≤ Z) (hZt : 4 * Z + 2 ≤ t) {u : ℝ} (hu : (X₀ : ℝ) ≤ u)
    (h2y : 2 * AbsorbEmpty.absorbYAt X₀ (2 * u) ≤ Z)
    (hut : 20 * u / Real.log u ^ 11 + 5 ≤ t) :
    absorbedDensity (θ / 2) (absSet X₀ (DF θ X₀ ω)) (uA θ) u ≤ Real.log u ^ (-4 : ℤ) := by
  classical
  obtain ⟨hU, hSG, hnt⟩ := hN
  have hX := hc.hX
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hX
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  set M := h0.limModel with hMdef
  have ht : TieFree M ω := by
    rw [hMdef, ← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have hnc := noCoincidence_of_tieFree ht
  have hok := limModel_realisedOK h0
  have hTB : ∀ m, ttB X₀ m < t → ω ∈ tB (θ := θ) (X₀ := X₀) m := fun m hm =>
    tB_all_of_QE hc hev hQC hE1 ⟨hU, hSG, hnt⟩ m hm.le
  -- the scale: `Z ≤ 2^{n'} X₀/2 < 2Z`
  have hex : ∃ n : ℕ, Z ≤ 2 ^ n * (X₀ : ℝ) / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * Z / X₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith
  set n' := Nat.find hex with hn'
  have hZn : Z ≤ 2 ^ n' * (X₀ : ℝ) / 2 := Nat.find_spec hex
  have hn2 : 2 ^ n' * (X₀ : ℝ) / 2 < 2 * Z := by
    rcases Nat.eq_zero_or_pos n' with h0' | hpos
    · rw [h0']; simp; linarith
    · obtain ⟨k, hk⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
      have hlt := Nat.find_min hex (show k < n' by omega)
      push_neg at hlt
      rw [hk, pow_succ]
      linarith
  have httB : ttB X₀ n' < t := by
    unfold ttB
    have h1 : ((⌈2 ^ n' * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) < t := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ n' * (X₀ : ℝ) / 2 by positivity)
      linarith
    exact_mod_cast h1
  have hscale : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z →
      8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ 2 ^ n' * (X₀ : ℝ) / 2 := by
    intro v hv hvZ
    obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hX hv
    have hv0 : 0 < v := by linarith
    have h11 : (100 : ℝ) ≤ Real.log v ^ 11 := by
      have : (10 ^ 8 : ℝ) ≤ Real.log v ^ 11 :=
        hl.trans (le_self_pow₀ (by linarith) (by norm_num))
      linarith
    have : 4 * v / Real.log v ^ 11 ≤ v / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hXb := X₀_ge_two_pow hX
    have : 8 / 7 * (2 * (4 * v / Real.log v ^ 11) + 1) ≤ v := by linarith
    linarith
  have hcl : ∀ v, (X₀ : ℝ) ≤ v → v ≤ Z →
      ClusterUpTo (realisedSystem M (capH X₀) ω) X₀ (4 * v / Real.log v ^ 11) (capM1 X₀ v) := by
    intro v hv hvZ
    have hvt : ⌈v⌉₊ < t := by
      have h1 : (⌈v⌉₊ : ℝ) < t := by
        have := Nat.ceil_lt_add_one (show 0 ≤ v by linarith)
        linarith
      exact_mod_cast h1
    exact cluster_of_QE hc hev hE1 hTB h0 hSG hv hvt (hscale v hv hvZ) httB
  have hQ : ∀ y, (X₀ : ℝ) ≤ y → y ≤ Z →
      (M.queue (M.slotIdx y) : ℝ) ≤ queueBScale X₀ (M.slot (M.slotIdx y)) := by
    intro y hy hyZ
    refine queue_of_QE hc hQC h0 hy ?_
    have hlog := log_le_lin hc (show 0 < y by linarith)
    have hXb := X₀_ge_two_pow hX
    linarith
  have hT := limModel_T_formula h0 hnc
  have L : LinkedModel θ X₀ M ω (constructionScale X₀) :=
    ⟨hc.hθ, hX, hU, hT, limModel_linked h0⟩
  have S := limModel_slotFacts h0 hev ht
  have hreg := jitterWidthRegular hX
  -- the cluster event at `u`
  obtain ⟨hlu, -, -⟩ := logs_of_ge hX0 hX hu
  have hu0 : 0 < u := by linarith
  have h11 : (100 : ℝ) ≤ Real.log u ^ 11 := by
    have : (10 ^ 8 : ℝ) ≤ Real.log u ^ 11 := hlu.trans (le_self_pow₀ (by linarith) (by norm_num))
    linarith
  have hm0 : 8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1) ≤
      2 ^ (n' + Nat.clog 2 ⌈u⌉₊) * (X₀ : ℝ) / 2 := by
    have hpow : (u : ℝ) ≤ 2 ^ Nat.clog 2 ⌈u⌉₊ := by
      have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
      have h2 : (⌈u⌉₊ : ℝ) ≤ ((2 ^ Nat.clog 2 ⌈u⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_pow_clog (by norm_num) _
      push_cast at h2; linarith
    have hn1 : (X₀ : ℝ) / 2 ≤ 2 ^ n' * (X₀ : ℝ) / 2 := by
      have : (1 : ℝ) ≤ 2 ^ n' := one_le_pow₀ (by norm_num)
      nlinarith
    rw [pow_add]
    have : 4 * u / Real.log u ^ 11 ≤ u / 25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hX2 : (2 : ℝ) ≤ X₀ / 2 := by linarith [X₀_ge_two_pow hX]
    have hp0 : (0 : ℝ) < 2 ^ Nat.clog 2 ⌈u⌉₊ := by positivity
    nlinarith
  -- the scale of the cluster event at `u` may be large; use instead a small one
  have hsmall : ∃ m : ℕ, 8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2 ∧
      ttB X₀ m < t := by
    have hex2 : ∃ m : ℕ, 8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2 :=
      ⟨_, hm0⟩
    set m := Nat.find hex2 with hm
    refine ⟨m, Nat.find_spec hex2, ?_⟩
    have hwm : 2 ^ m * (X₀ : ℝ) / 2 ≤
        max ((X₀ : ℝ) / 2) (2 * (8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1))) := by
      rcases Nat.eq_zero_or_pos m with h0' | hpos
      · rw [h0']; simp
      · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hlt := Nat.find_min hex2 (show k < m by omega)
        push_neg at hlt
        rw [hk, pow_succ]
        refine le_max_of_le_right ?_
        linarith
    unfold ttB
    have h1 : ((⌈2 ^ m * (X₀ : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) < t := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ m * (X₀ : ℝ) / 2 by positivity)
      have hXt : (X₀ : ℝ) / 2 + 2 < t := by linarith
      have : 2 * (8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1)) + 2 < t := by
        have e : 20 * u / Real.log u ^ 11 = 5 * (4 * u / Real.log u ^ 11) := by ring
        have : 0 ≤ 4 * u / Real.log u ^ 11 := by positivity
        -- `t ≥ 4Z + 2 ≥ 4X₀ + 2` and `t ≥ 10u/L¹¹ + 1`
        nlinarith
      rcases le_total ((X₀ : ℝ) / 2) (2 * (8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1))) with
        hh | hh
      · rw [max_eq_right hh] at hwm; linarith
      · rw [max_eq_left hh] at hwm; linarith
    exact_mod_cast h1
  obtain ⟨m, hm1, hm2⟩ := hsmall
  have hvt : ∀ n, zH X₀ n ≤ 4 * u / Real.log u ^ 11 → tE1 X₀ n < t := by
    intro n hn
    have := tE1_le hc hu hn
    have h2 : 10 * u / Real.log u ^ 11 + 1 ≤ 20 * u / Real.log u ^ 11 + 5 := by
      have : 0 ≤ u / Real.log u ^ 11 := by positivity
      have e1 : 10 * u / Real.log u ^ 11 = 10 * (u / Real.log u ^ 11) := by ring
      have e2 : 20 * u / Real.log u ^ 11 = 20 * (u / Real.log u ^ 11) := by ring
      linarith
    exact_mod_cast lt_of_lt_of_le this (h2.trans hut)
  have hclu := cluster_of_QE' hc hev hE1 hTB h0 hSG hu hvt hm1 hm2
  have hmain := lemma626_horizon hc.hθ hX M ω hU (limModel_placed_infinite h0)
    (constructionScale X₀) hT Real.log
    (fun x hx => ⟨Real.log_nonneg (by linarith), le_rfl⟩)
    (fun x hx _ => landing_of_linked L S hreg hok hx)
    (fun x hx hearly => landingInit_of_linked L S hreg hok hx hearly) hZX hQ hcl u hu h2y hclu
  have hTlow : ∀ x : ℝ, x < X₀ → M.T x = ⌊x⌋₊ := h0.limModel_low
  have hAu := realisedU_spec hok hU hX hTlow (θ := θ) (by linarith [hc.hθ.1])
    (by linarith [hc.hθ.2])
  let R : GreedyRun X₀ := ⟨M, capH X₀, ω, hTlow⟩
  have C : AbsorbedCoupling (realisedSystem M (capH X₀) ω) R.M R.H R.U
      (realisedA M (capH X₀) ω) (realisedLatest M (capH X₀) ω) := realisedCoupling hok
  have hb : 0 < θ / 2 := by linarith [hc.hθ.1]
  have hd := absorbedDensity_le_of_localCount hb (by linarith) hAu C.locFin hu hmain
  have hA : realisedA M (capH X₀) ω = absSet X₀ (DF θ X₀ ω) := by
    rw [realisedA_eq hok hnc]
    unfold DF
    rw [Mcl_eq_lim hc h0, Ucl_eq hU]
  rw [← hA]
  exact hd

end

end BModel
