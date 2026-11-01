module

public import RequestProject.Beurling.Queue6.E3Win
public import RequestProject.Beurling.Queue6.PhysIdent

/-!
# `C_jit` against `∫ c` on physical windows (Lemma 5.22, "Physical intervals")

The integer windows of `𝒲'_u` sandwich a physical window `I = [α, β)` with real endpoints,
`W⁻ = [⌈α⌉, ⌊β⌋) ⊂ I ⊂ W⁺ = [⌊α⌋, ⌈β⌉)`, `W⁺ \ W⁻` inside two unit windows, each of
compensator mass `≤ 50 log(2u)`. Hence, on `E3Good ω t` (the conclusions of `e3win_ae` at `ω`):

* `e3real_block` : for `I` in one dyadic block, `|I| ≤ L_u - 2`:
  `-e(u) ≤ C_jit(I) - ∫_I c ≤ e(u)`, `e(u) = a₁ + a₂ + s₂(u) L_u + 100 log(2u)` (`eB`);
* `e3real` : the same with `e(u) + e(2u)` for `I` within two consecutive blocks (split at `2u`;
  `C_jit` and `∫ c` are additive).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed
  SlotModel AbsorbEmpty QueueBound

namespace Queue6

open BModel

variable (θ : ℝ) (X₀ : ℕ)

/-- The error of one dyadic block: `e(u) = a₁ + a₂ + s₂(u) L_u + 100 log(2u)`. -/
noncomputable def eB (m : ℕ) : ℝ :=
  a1B X₀ m + a2B X₀ m + s2E3 X₀ (uS X₀ m) * LenB X₀ m + 100 * Real.log (2 * uS X₀ m)

/-- The conclusions of `e3win_ae` at `ω`, for the windows of time `< t`. -/
def E3Good (ω : JitterΩ) (t : ℕ) : Prop :=
  ∀ (m : ℕ) (a b : ℤ), uS X₀ m ≤ a → a ≤ b → (b : ℝ) ≤ 2 * uS X₀ m →
    ((b - a : ℤ) : ℝ) ≤ LenB X₀ m → b.toNat < t →
    (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) ≤
        50 * Real.log (2 * uS X₀ m) * ((b - a : ℤ) : ℝ) ∧
      Cjit (CM θ X₀ ω) (Ucl ω) a b ≤ (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) +
        a1B X₀ m + a2B X₀ m + s2E3 X₀ (uS X₀ m) * LenB X₀ m ∧
      (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) - a1B X₀ m - a2B X₀ m ≤
        Cjit (CM θ X₀ ω) (Ucl ω) a b

variable {θ X₀}

section Real

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc

omit hc in
lemma uS_succ (m : ℕ) : uS X₀ (m + 1) = 2 * uS X₀ m := by
  unfold uS; rw [pow_succ]; ring

omit hc in
lemma uS_int (m : ℕ) : uS X₀ m = (((2 ^ m * X₀ : ℕ) : ℤ) : ℝ) := by
  unfold uS; push_cast; ring

lemma eB_nonneg (m : ℕ) : 0 ≤ eB X₀ m := by
  obtain ⟨hu, hl, -, -⟩ := uS_facts hc m
  have := a1B_nonneg hc m
  have := a2B_nonneg hc m
  have := LenB_pos hc m
  have := s2E3_pos hc (uS X₀ m) hl
  have : 0 < Real.log (2 * uS X₀ m) := Real.log_pos (by
    have := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX; linarith)
  unfold eB; positivity

lemma LenB_mono (m : ℕ) : LenB X₀ m ≤ LenB X₀ (m + 1) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hu := (uS_facts hc m).1
  have h := capH_monotoneOn hX0 hc.hX (mem_Ici.mpr hu)
    (mem_Ici.mpr ((uS_facts hc (m + 1)).1)) (by rw [uS_succ]; linarith)
  unfold LenB; linarith

omit hc in
lemma ceil_toNat_mono {x y : ℝ} (h : x ≤ y) : (⌈x⌉).toNat ≤ (⌈y⌉).toNat :=
  Int.toNat_le_toNat (Int.ceil_mono h)

include hev

set_option maxHeartbeats 1600000 in
/-- **A physical window in one dyadic block**: `-e(u) ≤ C_jit(I) - ∫_I c ≤ e(u)` for
`I = [α, β) ⊂ [u, 2u]`, `|I| ≤ L_u - 2`, on `E3Good ω t`, `⌈β⌉ < t`. -/
theorem e3real_block {ω : JitterΩ} {t : ℕ} (hG : E3Good θ X₀ ω t)
    (F : ExcFacts θ (CM θ X₀ ω) (Ucl ω)) {m : ℕ} {α β : ℝ} (hα : uS X₀ m ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 2 * uS X₀ m) (hlen : β - α ≤ LenB X₀ m - 2) (ht : (⌈β⌉).toNat < t) :
    Cjit (CM θ X₀ ω) (Ucl ω) α β ≤ (∫ y in α..β, (compDen θ X₀ ω y).toReal) + eB X₀ m ∧
      (∫ y in α..β, (compDen θ X₀ ω y).toReal) - eB X₀ m ≤ Cjit (CM θ X₀ ω) (Ucl ω) α β := by
  set c : ℝ → ℝ := fun y => (compDen θ X₀ ω y).toReal with hcdef
  set u := uS X₀ m with hudef
  obtain ⟨huX, hl, -, -⟩ := uS_facts hc m
  have hX1 := one_lt_of_logX (Nat.cast_nonneg (α := ℝ) X₀) hc.hX
  have hlog2 : 0 < Real.log (2 * u) := Real.log_pos (by linarith)
  have ha1 := a1B_nonneg hc m
  have ha2 := a2B_nonneg hc m
  have hL := LenB_pos hc m
  have hs2 := s2E3_pos hc u hl
  have hc0 : ∀ y, 0 ≤ c y := fun y => ENNReal.toReal_nonneg
  have hint : ∀ p q : ℝ, IntervalIntegrable c volume p q := fun p q => by
    rcases le_total p q with h | h
    · exact compR_intervalIntegrable hc hev ω h
    · exact (compR_intervalIntegrable hc hev ω h).symm
  have hmono : ∀ p q r s : ℝ, p ≤ q → q ≤ r → r ≤ s → (∫ y in q..r, c y) ≤ ∫ y in p..s, c y :=
    fun p q r s h1 h2 h3 => intervalIntegral.integral_mono_interval h1 h2 h3
      (Filter.Eventually.of_forall fun y => hc0 y) (hint p s)
  have hadd : ∀ p q r : ℝ, (∫ y in p..q, c y) + (∫ y in q..r, c y) = ∫ y in p..r, c y :=
    fun p q r => intervalIntegral.integral_add_adjacent_intervals (hint p q) (hint q r)
  -- integer data
  set nU : ℤ := ((2 ^ m * X₀ : ℕ) : ℤ)
  have hnU : (nU : ℝ) = u := (uS_int m).symm
  set A := ⌊α⌋
  set B := ⌈β⌉
  set A' := ⌈α⌉
  set B' := ⌊β⌋
  have hA1 : (A : ℝ) ≤ α := Int.floor_le α
  have hA2 : α < (A : ℝ) + 1 := Int.lt_floor_add_one α
  have hB1 : β ≤ (B : ℝ) := Int.le_ceil β
  have hB2 : (B : ℝ) < β + 1 := Int.ceil_lt_add_one β
  have hA'1 : α ≤ (A' : ℝ) := Int.le_ceil α
  have hA'2 : (A' : ℝ) < α + 1 := Int.ceil_lt_add_one α
  have hB'1 : (B' : ℝ) ≤ β := Int.floor_le β
  have hB'2 : β < (B' : ℝ) + 1 := Int.lt_floor_add_one β
  have hUA : nU ≤ A := Int.le_floor.mpr (by rw [hnU]; exact hα)
  have hUA' : (u : ℝ) ≤ A := by rw [← hnU]; exact_mod_cast hUA
  have hB2u : B ≤ 2 * nU := Int.ceil_le.mpr (by push_cast; rw [hnU]; exact hβ)
  have hB2u' : (B : ℝ) ≤ 2 * u := by
    rw [← hnU]; exact_mod_cast hB2u
  have hAA' : A ≤ A' := Int.floor_le_ceil α
  have hA'A : A' ≤ A + 1 := Int.ceil_le_floor_add_one α
  have hBB' : B' ≤ B := Int.floor_le_ceil β
  have hB'B : B ≤ B' + 1 := Int.ceil_le_floor_add_one β
  have hA'B : A' ≤ B := Int.ceil_mono hαβ |>.trans_eq rfl
  have hAB' : A ≤ B' := Int.floor_mono hαβ
  have hcast : ∀ p q : ℤ, ((q - p : ℤ) : ℝ) = (q : ℝ) - p := fun p q => by push_cast; ring
  have hle1 : ∀ p q : ℤ, q ≤ p + 1 → ((q - p : ℤ) : ℝ) ≤ LenB X₀ m := fun p q h => by
    have : ((q - p : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : q - p ≤ 1)
    unfold LenB; have := (uS_facts hc m).2.2.1; linarith
  have htB : ∀ q : ℤ, q ≤ B → q.toNat < t := fun q h =>
    lt_of_le_of_lt (Int.toNat_le_toNat h) ht
  -- the unit windows at the ends
  have hA'Br : (A' : ℝ) ≤ B := by exact_mod_cast hA'B
  have hAB'r : (A : ℝ) ≤ B' := by exact_mod_cast hAB'
  have hAA'r : (A : ℝ) ≤ A' := by exact_mod_cast hAA'
  have hBB'r : (B' : ℝ) ≤ B := by exact_mod_cast hBB'
  have hW1 := hG m A A' (by exact_mod_cast hUA') hAA' (by linarith) (hle1 A A' hA'A)
    (htB A' hA'B)
  have hW2 := hG m B' B (by linarith) hBB' hB2u' (hle1 B' B hB'B) (htB B le_rfl)
  have hun1 : ((A' - A : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : A' - A ≤ 1)
  have hun2 : ((B - B' : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : B - B' ≤ 1)
  have hI1 : (∫ y in (A : ℝ)..(A' : ℝ), c y) ≤ 50 * Real.log (2 * u) := by
    have := hW1.1; nlinarith
  have hI2 : (∫ y in (B' : ℝ)..(B : ℝ), c y) ≤ 50 * Real.log (2 * u) := by
    have := hW2.1; nlinarith
  -- the outer window
  have hlenW : ((B - A : ℤ) : ℝ) ≤ LenB X₀ m := by rw [hcast]; linarith
  have hWp := hG m A B (by exact_mod_cast hUA') (by
    have : (A : ℝ) ≤ B := by linarith
    exact_mod_cast this) hB2u' hlenW (htB B le_rfl)
  have hCp : Cjit (CM θ X₀ ω) (Ucl ω) α β ≤ Cjit (CM θ X₀ ω) (Ucl ω) A B := cjit_mono F hA1 hB1
  have hsplit : (∫ y in (A : ℝ)..(B : ℝ), c y) =
      (∫ y in (A : ℝ)..α, c y) + (∫ y in α..β, c y) + ∫ y in β..(B : ℝ), c y := by
    rw [hadd, hadd]
  have he1 : (∫ y in (A : ℝ)..α, c y) ≤ ∫ y in (A : ℝ)..(A' : ℝ), c y :=
    hmono _ _ _ _ le_rfl hA1 hA'1
  have he2 : (∫ y in β..(B : ℝ), c y) ≤ ∫ y in (B' : ℝ)..(B : ℝ), c y :=
    hmono _ _ _ _ hB'1 hB1 le_rfl
  have hcj0 : 0 ≤ Cjit (CM θ X₀ ω) (Ucl ω) α β := Nat.cast_nonneg _
  have hWp2 := hWp.2.1
  have hcomp : ∀ p q : ℝ, (∫ y in p..q, (compDen θ X₀ ω y).toReal) = ∫ y in p..q, c y :=
    fun _ _ => rfl
  rw [hcomp] at hWp2
  refine ⟨?_, ?_⟩
  · unfold eB; rw [hcomp]; linarith
  · unfold eB; rw [hcomp]
    by_cases hAB : A' ≤ B'
    · have hW3 := hG m A' B' (by linarith) hAB (by linarith) (by rw [hcast]; linarith)
        (htB B' hBB')
      have hCm : Cjit (CM θ X₀ ω) (Ucl ω) A' B' ≤ Cjit (CM θ X₀ ω) (Ucl ω) α β :=
        cjit_mono F hA'1 hB'1
      have hW3' := hW3.2.2
      rw [hcomp] at hW3'
      have hs3 : (∫ y in α..β, c y) =
          (∫ y in α..(A' : ℝ), c y) + (∫ y in (A' : ℝ)..(B' : ℝ), c y) +
            ∫ y in (B' : ℝ)..β, c y := by rw [hadd, hadd]
      have hf1 : (∫ y in α..(A' : ℝ), c y) ≤ ∫ y in (A : ℝ)..(A' : ℝ), c y :=
        hmono _ _ _ _ hA1 hA'1 le_rfl
      have hf2 : (∫ y in (B' : ℝ)..β, c y) ≤ ∫ y in (B' : ℝ)..(B : ℝ), c y :=
        hmono _ _ _ _ le_rfl hB'1 hB1
      have : 0 ≤ s2E3 X₀ u * LenB X₀ m := by positivity
      linarith
    · push_neg at hAB
      have hBA : B ≤ A + 1 := by omega
      have hWl : ((B - A : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : B - A ≤ 1)
      have h1 := hWp.1
      rw [hcomp] at h1
      have h2 : (∫ y in α..β, c y) ≤ ∫ y in (A : ℝ)..(B : ℝ), c y :=
        hmono _ _ _ _ hA1 hαβ hB1
      have : 0 ≤ s2E3 X₀ u * LenB X₀ m := by positivity
      nlinarith

set_option maxHeartbeats 800000 in
/-- **A physical window in two consecutive dyadic blocks**:
`-(e(u) + e(2u)) ≤ C_jit(I) - ∫_I c ≤ e(u) + e(2u)` for `I = [α, β) ⊂ [u, 4u]`,
`|I| ≤ L_u - 2`, on `E3Good ω t`, `⌈β⌉ < t`. -/
theorem e3real {ω : JitterΩ} {t : ℕ} (hG : E3Good θ X₀ ω t)
    (F : ExcFacts θ (CM θ X₀ ω) (Ucl ω)) {m : ℕ} {α β : ℝ} (hα : uS X₀ m ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 2 * uS X₀ (m + 1)) (hlen : β - α ≤ LenB X₀ m - 2) (ht : (⌈β⌉).toNat < t) :
    Cjit (CM θ X₀ ω) (Ucl ω) α β ≤
        (∫ y in α..β, (compDen θ X₀ ω y).toReal) + (eB X₀ m + eB X₀ (m + 1)) ∧
      (∫ y in α..β, (compDen θ X₀ ω y).toReal) - (eB X₀ m + eB X₀ (m + 1)) ≤
        Cjit (CM θ X₀ ω) (Ucl ω) α β := by
  have he0 := eB_nonneg hc m
  have he1 := eB_nonneg hc (m + 1)
  have hLm := LenB_mono hc m
  have hU := uS_succ (X₀ := X₀) m
  rcases le_or_gt β (uS X₀ (m + 1)) with h1 | h1
  · obtain ⟨k1, k2⟩ := e3real_block hc hev hG F hα hαβ (by linarith) hlen ht
    constructor <;> linarith
  · rcases le_or_gt (uS X₀ (m + 1)) α with h2 | h2
    · obtain ⟨k1, k2⟩ := e3real_block hc hev hG F (m := m + 1) h2 hαβ hβ (by linarith) ht
      constructor <;> linarith
    · set U := uS X₀ (m + 1)
      have hint : ∀ p q : ℝ, IntervalIntegrable (fun y => (compDen θ X₀ ω y).toReal) volume p q :=
        fun p q => by
          rcases le_total p q with h | h
          · exact compR_intervalIntegrable hc hev ω h
          · exact (compR_intervalIntegrable hc hev ω h).symm
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint α U) (hint U β)
      have hC := cjit_add F h2.le h1.le
      have hUZ : (⌈U⌉).toNat < t := lt_of_le_of_lt (ceil_toNat_mono h1.le) ht
      obtain ⟨k1, k2⟩ := e3real_block hc hev hG F hα h2.le (by rw [hU]) (by linarith) hUZ
      obtain ⟨k3, k4⟩ := e3real_block hc hev hG F (m := m + 1) le_rfl h1.le hβ
        (by linarith) ht
      rw [hC, ← hsplit]
      constructor <;> linarith

end Real

section AE

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

/-- **`E3Good` holds a.s. on `Good(< t) ∩ NiceEv`**, for every `t`. -/
theorem e3Good_ae : ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, ω ∈ G0 θ X₀ (e3Family θ X₀) t →
    ω ∈ NiceEv θ X₀ → E3Good θ X₀ ω t := by
  filter_upwards [e3win_ae hc hev] with ω hω
  intro t hG hN m a b h1 h2 h3 h4 h5
  exact hω m a b h1 h2 h3 h4 t h5 hG hN

end AE

end Queue6

end
