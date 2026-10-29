module

public import RequestProject.Beurling.Queue6.E3Real

/-!
# Lemma 5.22, the bound on `E(I)` for physical intervals: `|σ(I) - ∫_I m| ≤ ε`

For `ω ∈ Good(< t) ∩ NiceEv` with `E3Good ω t` and a physical window `I = [α, β)`,
`X₀ ≤ α ≤ β`, `I ⊂ [u, 4u]`, `|I| ≤ L_u - 2`, `β + 25 log(2β) + 4 ≤ t`:

`|σ(I) - ∫_I m| ≤ B(Y) + 4 + e(u) + e(2u)`,

where `σ(I) = sigP` (the primes placed at slots starting in `I`), `m = T'_cont - c`
(`marginM`), `e` is the block error of `E3Real` and the queue bound (75) `B(Y)` (`queueB`)
bounds the queue at the two ends (`β + 2 ≤ Y`). It combines the two-sided Lemma 3.9 for physical
windows (`phys_bounds`: `σ = C(β) - C(α) - C_jit(I) ± (Q + 4)`), `∫_I T'_cont = C(β) - C(α)`
(`integral_TpCont`), `C_jit(I) = ∫_I c ± e` (`e3real`) and the queue constraints of
`Good(< t)` at the two end slots (`slot_fi_le`: their cells end below `β + 25 log(2β) + 2`).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed
  SlotModel AbsorbEmpty QueueBound

namespace Queue6

open BModel

variable {θ : ℝ} {X₀ : ℕ} (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- The facts of the constructed model at `ω ∈ NiceEv`. -/
lemma model_facts {ω : JitterΩ} (hN : ω ∈ NiceEv θ X₀) :
    ExcFacts θ (CM θ X₀ ω) (Ucl ω) ∧ (CM θ X₀ ω).slot 1 ≤ X₀ + 2 ∧
      ∀ k : {k // placedAt (CM θ X₀ ω) k},
        7 / 8 * (X₀ : ℝ) ≤ realisedVal (CM θ X₀ ω) (capH X₀) (Ucl ω) (Sum.inr k) := by
  obtain ⟨hU, -, hnt⟩ := hN
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hc.hX, hU, hc.hHB⟩
  have hM : CM θ X₀ ω = h0.limModel := Mcl_eq_lim hc h0
  have hUe : Ucl ω = ω := Ucl_eq hU
  have ht : TieFree h0.limModel ω := by
    rw [← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  refine ⟨by rw [hM, hUe]; exact excFacts_of h0 hev ht, by
    rw [hM]; exact (limModel_slot_one h0 hev).2, ?_⟩
  exact jit_ge hc.hX (fun j => clamp01_mem (ω j)) (hslot_CM hc ω)

/-- **The queue at the slot cell of `x`** on `Good(< t)`: `Q_{fi x} ≤ B(Y)` for
`x + 25 log(2x) + 4 ≤ t` and `x + 2 ≤ Y` (Remark 6.9(ii): `B` is non-decreasing). -/
lemma queue_fi_le {ω : JitterΩ} {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) {x Y : ℝ} (hx : (X₀ : ℝ) ≤ x)
    (htx : x + 25 * Real.log (2 * x) + 4 ≤ t) (hY : x + 2 ≤ Y) :
    ((CM θ X₀ ω).queue (fi (CM θ X₀ ω) x) : ℝ) ≤ queueB X₀ Y := by
  obtain ⟨F, hs1, -⟩ := model_facts hc hev hN
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  set M := CM θ X₀ ω
  set j := fi M x
  have hsl := slot_fi_le F hs1 hx
  have htq : tq θ X₀ j ω < t := by
    unfold tq
    have h1 : (⌈M.slot (j + 1)⌉₊ : ℝ) < M.slot (j + 1) + 1 :=
      Nat.ceil_lt_add_one (by linarith [slot_gt F (Nat.le_add_left 1 j)])
    have h2 : ((⌈M.slot (j + 1)⌉₊ + 1 : ℕ) : ℝ) < t := by push_cast; linarith
    exact_mod_cast h2
  have hok : ω ∈ okQ θ X₀ j := hG.1 j htq
  have hQ : (M.queue j : ℝ) ≤ queueBScale X₀ (M.slot j) := hok
  -- the slot of `j` lies below `x + 2`
  have hsj : M.slot j ≤ x + 2 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]
      have := M.slot_mono (Nat.zero_le 1)
      linarith
    · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have := slot_lt_of_lt_fi (M := M) (α := x) (k := k) (by omega)
      rw [hk]; linarith
  exact hQ.trans (queueBScale_le hX0 hc.hX (by linarith) (by linarith))

set_option maxHeartbeats 1600000 in
/-- **The interval error of a physical window**: `|σ(I) - ∫_I m| ≤ B(Y) + 4 + e(u) + e(2u)`. -/
theorem phys_margin {ω : JitterΩ} {t : ℕ} (hG : ω ∈ G0 θ X₀ (e3Family θ X₀) t)
    (hN : ω ∈ NiceEv θ X₀) (hE : E3Good θ X₀ ω t) {m : ℕ} {α β Y : ℝ} (hXα : (X₀ : ℝ) ≤ α)
    (hα : uS X₀ m ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 2 * uS X₀ (m + 1))
    (hlen : β - α ≤ LenB X₀ m - 2) (ht : β + 25 * Real.log (2 * β) + 4 ≤ t)
    (hY : β + 2 ≤ Y) :
    |(sigP (CM θ X₀ ω) α β : ℝ) - ∫ y in α..β, marginM θ X₀ ω y| ≤
      queueB X₀ Y + 4 + (eB X₀ m + eB X₀ (m + 1)) := by
  obtain ⟨F, hs1, hjit⟩ := model_facts hc hev hN
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hβX : (X₀ : ℝ) ≤ β := hXα.trans hαβ
  have hl2 : 0 ≤ Real.log (2 * β) := Real.log_nonneg (by linarith)
  have hl2a : Real.log (2 * α) ≤ Real.log (2 * β) := Real.log_le_log (by linarith) (by linarith)
  -- the queue at both ends
  have hQi := queue_fi_le hc hev hG hN hXα (by linarith) (by linarith : α + 2 ≤ Y)
  have hQj := queue_fi_le hc hev hG hN hβX ht hY
  -- Lemma 3.9 for `[α, β)`
  obtain ⟨hP1, hP2⟩ := phys_bounds F hs1 hjit hXα hαβ
  -- `C_jit` against `∫ c`
  have htn : (⌈β⌉).toNat < t := by
    have h1 : ((⌈β⌉ : ℤ) : ℝ) < t := by
      have := Int.ceil_lt_add_one β; linarith
    have h2 : ⌈β⌉ < (t : ℤ) := by exact_mod_cast h1
    have h3 : 0 < ⌈β⌉ := Int.ceil_pos.mpr (by linarith)
    omega
  obtain ⟨hE1, hE2⟩ := e3real hc hev hE F hα hαβ hβ hlen htn
  -- `∫ m = C(β) - C(α) - ∫ c`
  obtain ⟨hTi, hTe⟩ := integral_TpCont hc ω hαβ hβX
  have hcR := compR_intervalIntegrable hc hev ω hαβ
  have hm : (∫ y in α..β, marginM θ X₀ ω y) =
      (∫ y in α..β, TpCont θ X₀ ω y) - ∫ y in α..β, (compDen θ X₀ ω y).toReal :=
    intervalIntegral.integral_sub hTi hcR
  have hDF : DF θ X₀ ω = DM (CM θ X₀ ω) (Ucl ω) := rfl
  rw [hDF, max_eq_left hXα] at hTe
  rw [hm, hTe, abs_le]
  constructor <;> linarith

end Queue6

end
