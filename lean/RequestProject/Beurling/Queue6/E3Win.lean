module

public import RequestProject.Beurling.Queue6.CompE3
public import RequestProject.Beurling.Model.E3Comp
public import RequestProject.Beurling.Model.S2Final

/-!
# `C_jit` against `∫ c` on the windows of `𝒲'_u`, two-sided (Lemma 5.22, eqs. (F1), (F2), (s2))

For a window `W = [a, b)` of `𝒲'_u` (`u = 2^m X₀`) and `ω ∈ Good(< t) ∩ NiceEv`, `t > b`:

* `x2count_le_b2` : `X⁽²⁾_q(W) ≤ b₂ = 2 A_u M₁(u)` (every exponent is `≤ A_u + 1`, as
  `(X₀⁻)^n ≤ q^n < 2u`, and each `X⁽ⁿ⁾_q(W) ≤ 2 M₁(u)`), so the truncation of `X̃⁽²⁾` is
  inactive;
* `e3win_one`, `e3win_ae` : `Comp(W) = ∫_W c ≤ 50 log(2u) |W|` and
  `-a₁ - a₂ ≤ C_jit(W) - ∫_W c ≤ a₁ + a₂ + s₂(u) L_u`, where `a₁`, `a₂` are the Freedman
  bounds (F1), (F2) of `E3_W` at the maximal length `L_u = 1.03 H(u) + 1` (`a1B`, `a2B`): indeed
  `C_jit(W) = ∑_q (X̃_q + X̃⁽²⁾_q) = ∫_W c + Mart(W) + Comp⁽²⁾(W) + Mart⁽²⁾(W)` with
  `0 ≤ Comp⁽²⁾(W) ≤ s₂(u)|W|` (eq. (s2)).
-/

@[expose] public section

open Set Real MeasureTheory ProbabilityTheory Construction CaplLink QueueMono Absorbed
  SlotModel AbsorbEmpty QueueBound

namespace Queue6

open BModel

variable (θ : ℝ) (X₀ : ℕ)

/-- `L_u = 1.03 H(u) + 1`, the maximal length of a window of `𝒲'_u`. -/
noncomputable def LenB (m : ℕ) : ℝ := 1.03 * capH X₀ (uS X₀ m) + 1

/-- The (F1) bound of `E3_W` at the maximal length: `√(2 · 2M₁ · 50 log(2u) · L_u · λ') +
(4/3) M₁ λ'`. -/
noncomputable def a1B (m : ℕ) : ℝ :=
  Real.sqrt (2 * (2 * capM1 X₀ (uS X₀ m) * (50 * Real.log (2 * uS X₀ m)) * LenB X₀ m) *
    lamE3 X₀ (uS X₀ m)) + 2 * (2 * capM1 X₀ (uS X₀ m)) * lamE3 X₀ (uS X₀ m) / 3

/-- The (F2) bound of `E3_W` at the maximal length: `√(2 b₂ s₂ L_u λ') + (2/3) b₂ λ'`. -/
noncomputable def a2B (m : ℕ) : ℝ :=
  Real.sqrt (2 * (b2E3 X₀ (uS X₀ m) * s2E3 X₀ (uS X₀ m) * LenB X₀ m) * lamE3 X₀ (uS X₀ m)) +
    2 * b2E3 X₀ (uS X₀ m) * lamE3 X₀ (uS X₀ m) / 3

variable {θ X₀}

section Sizes

variable (hc : Cond θ X₀)
include hc

lemma a1B_nonneg (m : ℕ) : 0 ≤ a1B X₀ m := by
  obtain ⟨-, -, -, hM⟩ := uS_facts hc m
  have := lamE3_pos hc m
  unfold a1B
  have := Real.sqrt_nonneg (2 * (2 * capM1 X₀ (uS X₀ m) * (50 * Real.log (2 * uS X₀ m)) *
    LenB X₀ m) * lamE3 X₀ (uS X₀ m))
  have : 0 ≤ 2 * (2 * capM1 X₀ (uS X₀ m)) * lamE3 X₀ (uS X₀ m) / 3 := by positivity
  linarith

lemma b2E3_nonneg (m : ℕ) : 0 ≤ b2E3 X₀ (uS X₀ m) := by
  obtain ⟨-, -, -, hM⟩ := uS_facts hc m
  unfold b2E3; positivity

lemma a2B_nonneg (m : ℕ) : 0 ≤ a2B X₀ m := by
  have := lamE3_pos hc m
  have := b2E3_nonneg hc m
  unfold a2B
  have := Real.sqrt_nonneg (2 * (b2E3 X₀ (uS X₀ m) * s2E3 X₀ (uS X₀ m) * LenB X₀ m) *
    lamE3 X₀ (uS X₀ m))
  have : 0 ≤ 2 * b2E3 X₀ (uS X₀ m) * lamE3 X₀ (uS X₀ m) / 3 := by positivity
  linarith

lemma LenB_pos (m : ℕ) : 0 < LenB X₀ m := by
  obtain ⟨-, -, hH, -⟩ := uS_facts hc m
  unfold LenB; linarith

end Sizes

/-! ### The truncation of `X̃⁽²⁾` is inactive -/

section X2

variable (hc : Cond θ X₀)
include hc

set_option maxHeartbeats 800000 in
/-- **`X⁽ⁿ⁾_q(W) ≤ 2 M₁(u)` for every `n`**, on the cluster event at the height `u`. -/
theorem xcount_le_W {m : ℕ} {a b : ℤ} (hW : AdmW X₀ m a b) (ω : JitterΩ)
    (hcl : ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (capM1 X₀ (uS X₀ m))) (k n : ℕ) :
    Xcount (CM θ X₀ ω) (Ucl ω) a b k n ≤ 2 * capM1 X₀ (uS X₀ m) := by
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX1 := one_lt_of_logX hX0 hc.hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set u := uS X₀ m with hudef
  have hu : (X₀ : ℝ) ≤ u := X₀_le_uS (X₀ := X₀) hX0p m
  obtain ⟨hua, hab, hb2, hlen⟩ := hW
  rw [← hudef] at hua hb2 hlen
  have hM := QueueBound.one_le_capM1 hX0 hc.hX hu
  obtain ⟨hy, hHL⟩ := absorbYAt_ge hc hu
  obtain ⟨hL, -, -⟩ := logs_of_ge hX0 hc.hX hu
  set L := Real.log u
  set y := absorbYAt X₀ u
  have hH := capH_ge_one hX0 hc.hX hu
  have hL9 : 1 ≤ L ^ 9 := one_le_pow₀ (by linarith)
  have hy0 : 0 < y := by nlinarith
  have hu0 : 0 < u := by linarith
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hok : RealisedOK (CM θ X₀ ω) (capH X₀) (Ucl ω) := by
    show RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)
    rw [Mcl_eq hc]; exact limModel_realisedOK (hc.std ω)
  -- the threshold
  have hthr : ∀ e ∈ cjitSet (CM θ X₀ ω) (Ucl ω) a b,
      y ≤ primeValueOf (CM θ X₀ ω) (capH X₀) (Ucl ω) (latk (CM θ X₀ ω) e) := by
    intro e he
    obtain ⟨⟨-, h1, h2⟩, hr, hA⟩ := he
    have hn1 : u ≤ idxVal (CM θ X₀ ω) (capH X₀) (Ucl ω) e := le_trans hua h1
    have h := latest_ge_absorbY (by linarith [hc.hX]) hr (hu.trans hn1) hA
    have hds : dyadicScale X₀ (max X₀ (idxVal (CM θ X₀ ω) (capH X₀) (Ucl ω) e)) = u := by
      rw [max_eq_right (hu.trans hn1)]
      exact dyadicScale_eq hX0p m (by rw [hudef] at hn1; unfold uS at hn1; exact hn1)
        (by have : (b : ℝ) ≤ 2 * u := hb2; rw [hudef] at this; unfold uS at this; linarith)
    unfold absorbY at h
    rw [hds] at h
    exact h
  -- the window is short
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hlenL : ((b : ℝ) - a) / y ≤ 1 / (2000 * L ^ 9) := by
    rw [div_le_div_iff₀ hy0 (by positivity)]
    have : ((b - a : ℤ) : ℝ) = (b : ℝ) - a := by push_cast; ring
    rw [this] at hlen
    have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have h1 : (b : ℝ) - a ≤ 1.04 * capH X₀ u := by nlinarith
    have h2 : ((b : ℝ) - a) * (2000 * L ^ 9) ≤ 1.04 * capH X₀ u * (2000 * L ^ 9) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 1.04 * capH X₀ u * (2000 * L ^ 9) ≤ 2133 * capH X₀ u * L ^ 9 := by nlinarith
    linarith
  have hlen1 : ((b : ℝ) - a) / y < 1 := by
    have : 1 / (2000 * L ^ 9) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  -- `b / y` lies between `√u` and `u`
  have hysq : y ≤ u ^ (1 / 2 : ℝ) := absorbYAt_le_sqrt hX0 hc.hX hu
  have hsq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  have hsq1 : 3 ≤ u ^ (1 / 2 : ℝ) := by
    have : (9 : ℝ) ≤ u := by linarith [X₀_ge_two_pow hc.hX]
    by_contra h; push_neg at h
    have h0 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu0.le _
    nlinarith
  have hby1 : u ^ (1 / 2 : ℝ) ≤ (b : ℝ) / y := by
    rw [le_div_iff₀ hy0]
    have : u ^ (1 / 2 : ℝ) * y ≤ u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hysq (by linarith)
    linarith
  have hby2 : (b : ℝ) / y ≤ u := by
    rw [div_le_iff₀ hy0]
    have hy2 : 2 ≤ y := by
      have : 1 ≤ capH X₀ u * L ^ 9 := one_le_mul_of_one_le_of_one_le hH hL9
      linarith
    nlinarith
  have hlogby : 1 ≤ Real.log ((b : ℝ) / y) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hlogby2 : Real.log ((b : ℝ) / y) ≤ L := Real.log_le_log (by linarith) hby2
  have hlen6 : ((b : ℝ) - a) / y ≤ 2 / Real.log ((b : ℝ) / y) ^ 6 := by
    refine hlenL.trans ?_
    have h6 : Real.log ((b : ℝ) / y) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by linarith) hlogby2 6
    have h69 : L ^ 6 ≤ L ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < Real.log ((b : ℝ) / y) by linarith) 6]
  have hZ : (b : ℝ) / y ≤ 4 * u / L ^ 11 := by
    rw [div_le_div_iff₀ hy0 (by positivity)]
    have h11 : L ^ 11 = L ^ 2 * L ^ 9 := by ring
    have : L ^ 2 * L ^ 9 ≤ 2133 * capH X₀ u * L ^ 9 := by
      have : 0 ≤ L ^ 9 := by positivity
      nlinarith
    nlinarith
  have hy1 : 1 ≤ y := by
    have : 1 ≤ capH X₀ u * L ^ 9 := one_le_mul_of_one_le_of_one_le hH hL9
    linarith
  exact xcount_le hok hc.hX (fun j => clamp01_mem (ω j)) (hslot_CM hc ω) hy1 hthr hlen1 hlen6 hZ
    hcl (by linarith) k n

/-- **`X⁽²⁾_q(W) ≤ b₂`** on the cluster event at the height `u` (every exponent is
`≤ A_u + 1`). -/
theorem x2count_le_b2 {m : ℕ} {a b : ℤ} (hW : AdmW X₀ m a b) (ω : JitterΩ)
    (hcl : ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * uS X₀ m / Real.log (uS X₀ m) ^ 11) (capM1 X₀ (uS X₀ m))) (k : ℕ) :
    X2count (CM θ X₀ ω) (Ucl ω) a b k ≤ b2E3 X₀ (uS X₀ m) := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  have hX1 := one_lt_of_logX hX0 hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  set u := uS X₀ m with hudef
  have hu : (X₀ : ℝ) ≤ u := X₀_le_uS (X₀ := X₀) hX0p m
  have hb2 : (b : ℝ) ≤ 2 * u := hW.2.2.1
  set M := CM θ X₀ ω
  have hok : RealisedOK M (capH X₀) (Ucl ω) := by
    show RealisedOK (Mcl θ X₀ ω) (capH X₀) (Ucl ω)
    rw [Mcl_eq hc]; exact limModel_realisedOK (hc.std ω)
  have hXm : 0.99 * (X₀ : ℝ) ≤ Xm X₀ := by
    have hHX : capH X₀ X₀ ≤ X₀ / 10 ^ 7 := capH_le_div hX le_rfl
    unfold Xm; linarith
  have hXm1 : 1 < Xm X₀ := by linarith [X₀_ge_two_pow hX]
  have hlXm : 0 < Real.log (Xm X₀) := Real.log_pos hXm1
  set F := ⌊Real.log (2 * u) / Real.log (Xm X₀)⌋₊
  -- every exponent is `≤ F = A_u + 1`
  have hexp : ∀ e ∈ x2set M (Ucl ω) a b k, mult M e k ≤ F := by
    intro e he
    have h2 := he.2.2
    have hk : placedAt M k := by
      by_contra hk; unfold mult at h2; rw [dif_neg hk] at h2; omega
    have hx : e ∈ xset M (Ucl ω) a b k (mult M e k) := ⟨he.1, he.2.1, rfl⟩
    have hq := pow_lt_of_xset hok hx hk
    have hqXm : Xm X₀ ≤ primeValueOf M (capH X₀) (Ucl ω) k := valF_ge_Xm hc k ω
    have hpow : Xm X₀ ^ mult M e k ≤ primeValueOf M (capH X₀) (Ucl ω) k ^ mult M e k :=
      pow_le_pow_left₀ (by linarith) hqXm _
    have hlt : Xm X₀ ^ mult M e k < 2 * u := by linarith
    have hlog : (mult M e k : ℝ) * Real.log (Xm X₀) < Real.log (2 * u) := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) hlt
    have : (mult M e k : ℝ) ≤ Real.log (2 * u) / Real.log (Xm X₀) := by
      rw [le_div_iff₀ hlXm]; linarith
    exact Nat.le_floor this
  have hfin : ∀ n, (xset M (Ucl ω) a b k n).Finite := fun n =>
    (finite_idxVal_le hok b).subset fun e he => he.1.1.2.2.le
  have hXn := xcount_le_W hc hW ω hcl k
  have h := count_le_of_cover (S := x2set M (Ucl ω) a b k) (AuE3 X₀ u)
    (fun i => xset M (Ucl ω) a b k (i + 2)) (fun i => hfin (i + 2)) (fun i _ => hXn (i + 2))
    (fun e he => ⟨mult M e k - 2, by
      have := hexp e he; have := he.2.2; unfold AuE3; omega,
      ⟨he.1, he.2.1, by have := he.2.2; omega⟩⟩)
  unfold X2count b2E3
  refine h.trans (le_of_eq ?_)
  ring

end X2

/-! ### One window -/

section Window

variable (hc : Cond θ X₀) (hev : Even X₀)
include hc hev

set_option maxHeartbeats 1600000 in
/-- **`C_jit(W)` against `Comp(W) = ∫_W c`** for one window `W` of `𝒲'_u`, a.s. on
`Good(< t) ∩ NiceEv`, `t > b`. -/
theorem e3win_one {m : ℕ} {a b : ℤ} (hW : AdmW X₀ m a b) :
    ∀ᵐ ω ∂jitterMeasure, ∀ t : ℕ, b.toNat < t → ω ∈ G0 θ X₀ (e3Family θ X₀) t →
      ω ∈ NiceEv θ X₀ →
      ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal ≤
          50 * Real.log (2 * uS X₀ m) * ((b - a : ℤ) : ℝ) ∧
        Cjit (CM θ X₀ ω) (Ucl ω) a b ≤ (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) +
          a1B X₀ m + a2B X₀ m + s2E3 X₀ (uS X₀ m) * LenB X₀ m ∧
        (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) - a1B X₀ m - a2B X₀ m ≤
          Cjit (CM θ X₀ ω) (Ucl ω) a b := by
  classical
  have hX0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
  have hX := hc.hX
  have hX1 := one_lt_of_logX hX0 hX
  have hX0p : (0 : ℝ) < X₀ := by linarith
  have hnn : ∀ᵐ ω ∂jitterMeasure, ∀ k,
      0 ≤ (jitterMeasure[X32 θ X₀ m a b k | jitterFiltration k]) ω := by
    refine ae_all_iff.mpr fun k => condExp_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    unfold X32
    exact le_min (Nat.cast_nonneg _) (b2E3_nonneg hc m)
  filter_upwards [compE3_eq hc hev hW, e3CompBound hc hev m a b hW,
    e3S2Bound_of hc hev (s2Core hc hev) m a b hW, hnn] with ω hcomp hCB hS2 hnn
  intro t hbt hG hN
  obtain ⟨hU, hSG, hnt⟩ := hN
  set u := uS X₀ m with hudef
  have hu : (X₀ : ℝ) ≤ u := X₀_le_uS (X₀ := X₀) hX0p m
  obtain ⟨hua, hab, hb2, hlen⟩ := hW
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb0 : (0 : ℤ) ≤ b := by
    have : (0 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  have hbt' : (b : ℝ) < t := by
    have h1 : ((b.toNat : ℕ) : ℝ) < t := by exact_mod_cast hbt
    have h2 : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
      have := Int.toNat_of_nonneg hb0
      exact_mod_cast this
    linarith
  -- the model
  have h0 : Std θ X₀ ω := ⟨hc.hθ, hX, hU, hc.hHB⟩
  have hM : CM θ X₀ ω = h0.limModel := Mcl_eq_lim hc h0
  have hUe : Ucl ω = ω := Ucl_eq hU
  have ht : TieFree h0.limModel ω := by
    rw [← constructedModel_eq h0]
    by_contra hc'; exact hnt ⟨h0, hc'⟩
  have F : ExcFacts θ (CM θ X₀ ω) (Ucl ω) := by
    rw [hM, hUe]; exact excFacts_of h0 hev ht
  -- the cluster event at the height `u`
  have hcl : ClusterUpTo (realisedSystem (CM θ X₀ ω) (capH X₀) (Ucl ω)) X₀
      (4 * u / Real.log u ^ 11) (capM1 X₀ u) := by
    rw [hM, hUe]
    have hvt : ⌈u⌉₊ < t := by
      have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : (a : ℝ) + 1 ≤ b := by
        have : a + 1 ≤ b := hab
        exact_mod_cast this
      have h3 : (⌈u⌉₊ : ℝ) < t := by linarith
      exact_mod_cast h3
    have hm : 8 / 7 * (2 * (4 * u / Real.log u ^ 11) + 1) ≤ 2 ^ m * (X₀ : ℝ) / 2 := by
      have e : 2 ^ m * (X₀ : ℝ) / 2 = u / 2 := by rw [hudef]; unfold uS; ring
      rw [e]
      obtain ⟨hl, -, -⟩ := logs_of_ge hX0 hX hu
      have hu0 : 0 < u := by linarith
      have h11 : (100 : ℝ) ≤ Real.log u ^ 11 := by
        have : (10 ^ 8 : ℝ) ≤ Real.log u ^ 11 :=
          hl.trans (le_self_pow₀ (by linarith) (by norm_num))
        linarith
      have : 4 * u / Real.log u ^ 11 ≤ u / 25 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
      have : (2 : ℝ) ^ 16 ≤ u := by linarith [X₀_ge_two_pow hX]
      nlinarith
    have hmt : ttB X₀ m < t := by
      have e : 2 ^ m * (X₀ : ℝ) / 2 = u / 2 := by rw [hudef]; unfold uS; ring
      have h1 : ((ttB X₀ m : ℕ) : ℝ) < u / 2 + 2 := by
        unfold ttB; rw [e]; push_cast
        linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ u / 2 by linarith)]
      have : (2 : ℝ) ^ 16 ≤ u := by linarith [X₀_ge_two_pow hX]
      have h2 : ((ttB X₀ m : ℕ) : ℝ) < t := by linarith
      exact_mod_cast h2
    exact cluster_of_G0 (e3Family θ X₀) hc hev hG h0 hSG hu hvt hm hmt
  have hW : AdmW X₀ m a b := ⟨hua, hab, hb2, hlen⟩
  obtain ⟨hX3, N1, hN1⟩ := hcomp hcl
  -- the good set of Lemma 5.22 and the event `E3_W`
  have hGE : ω ∈ GoodE1 θ X₀ b.toNat :=
    ⟨QC_anti (okQ θ X₀) (tq θ X₀) hbt.le hG.1, fun n hn =>
      mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inl n) (lt_trans hn hbt)⟩
  have hE3 : ω ∈ E3ev θ X₀ m a b :=
    mem_E0_of_G0 (e3Family θ X₀) hG (Sum.inr (Sum.inr (Sum.inr (Sum.inr (m, a, b))))) hbt
  have hE3' := hE3 hW
  -- `X̃⁽²⁾ = X⁽²⁾`
  have hX32 : ∀ k, X32 θ X₀ m a b k ω = X2count (CM θ X₀ ω) (Ucl ω) a b k := fun k => by
    unfold X32; exact min_eq_left (x2count_le_b2 hc hW ω hcl k)
  obtain ⟨N0, hN0⟩ := cjit_eq_sum F (a : ℝ) b
  set N := max N0 N1
  have hC := hN0 N (le_max_left _ _)
  have hI := hN1 N (le_max_right _ _)
  set S1 := ∑ k ∈ Finset.range N, (jitterMeasure[X3 θ X₀ m a b k | jitterFiltration k]) ω
  set S2 := ∑ k ∈ Finset.range N, (jitterMeasure[X32 θ X₀ m a b k | jitterFiltration k]) ω
  have hdec : Cjit (CM θ X₀ ω) (Ucl ω) a b =
      S1 + MartE3 θ X₀ m a b N ω + (S2 + Mart2E3 θ X₀ m a b N ω) := by
    rw [hC, Finset.sum_add_distrib]
    unfold MartE3 Mart2E3
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ k ∈ Finset.range N, Xcount (CM θ X₀ ω) (Ucl ω) a b k 1 =
        ∑ k ∈ Finset.range N, X3 θ X₀ m a b k ω :=
      Finset.sum_congr rfl fun k _ => (hX3 k).symm
    have e2 : ∑ k ∈ Finset.range N, X2count (CM θ X₀ ω) (Ucl ω) a b k =
        ∑ k ∈ Finset.range N, X32 θ X₀ m a b k ω :=
      Finset.sum_congr rfl fun k _ => (hX32 k).symm
    rw [e1, e2]; ring
  have hS2le : S2 ≤ s2E3 X₀ u * ((b - a : ℤ) : ℝ) := hS2 hGE N
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun k _ => hnn k
  obtain ⟨hM1, hM2⟩ := hE3' N
  rw [abs_le] at hM1 hM2
  rw [← hudef] at hM1 hM2
  -- the bounds at the maximal length
  obtain ⟨-, hl, hH, hMu⟩ := uS_facts hc m
  have hlam := lamE3_pos hc m
  have hlog2 : 0 < Real.log (2 * u) := Real.log_pos (by linarith)
  have hlenB : ((b - a : ℤ) : ℝ) ≤ LenB X₀ m := by unfold LenB; exact hlen
  have hba0 : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by push_cast; linarith
  have hA1 : Real.sqrt (2 * VbE3 X₀ m a b * lamE3 X₀ u) +
      2 * (2 * capM1 X₀ u) * lamE3 X₀ u / 3 ≤ a1B X₀ m := by
    unfold a1B VbE3
    gcongr
  have hb2n := b2E3_nonneg hc m
  have hs2 := s2E3_pos hc u hl
  have hA2 : Real.sqrt (2 * Vb2E3 X₀ m a b * lamE3 X₀ u) +
      2 * b2E3 X₀ u * lamE3 X₀ u / 3 ≤ a2B X₀ m := by
    unfold a2B Vb2E3
    gcongr
  have hs2L : s2E3 X₀ u * ((b - a : ℤ) : ℝ) ≤ s2E3 X₀ u * LenB X₀ m :=
    mul_le_mul_of_nonneg_left hlenB hs2.le
  refine ⟨?_, ?_, ?_⟩
  · rw [← hI]; exact hCB hGE N
  · have hI' : S1 = ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := hI
    rw [hdec]
    have := add_le_add (add_le_add (le_of_eq hI') (hM1.2.trans hA1))
      (add_le_add (hS2le.trans hs2L) (hM2.2.trans hA2))
    linarith
  · have hI' : S1 = ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal := hI
    rw [hdec]
    have h1 : -a1B X₀ m ≤ MartE3 θ X₀ m a b N ω := le_trans (neg_le_neg hA1) hM1.1
    have h2 : -a2B X₀ m ≤ Mart2E3 θ X₀ m a b N ω := le_trans (neg_le_neg hA2) hM2.1
    have := add_le_add (add_le_add (le_of_eq hI'.symm) h1) (add_le_add hS20 h2)
    linarith

set_option maxHeartbeats 800000 in
/-- **`C_jit(W)` against `∫_W c` for every window of `𝒲'_u`** (lengths `0 ≤ b - a ≤ L_u`), a.s.
on `Good(< t) ∩ NiceEv`, `t > b`. -/
theorem e3win_ae :
    ∀ᵐ ω ∂jitterMeasure, ∀ (m : ℕ) (a b : ℤ), uS X₀ m ≤ a → a ≤ b → (b : ℝ) ≤ 2 * uS X₀ m →
      ((b - a : ℤ) : ℝ) ≤ LenB X₀ m → ∀ t : ℕ, b.toNat < t →
      ω ∈ G0 θ X₀ (e3Family θ X₀) t → ω ∈ NiceEv θ X₀ →
      ∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal ≤
          50 * Real.log (2 * uS X₀ m) * ((b - a : ℤ) : ℝ) ∧
        Cjit (CM θ X₀ ω) (Ucl ω) a b ≤ (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) +
          a1B X₀ m + a2B X₀ m + s2E3 X₀ (uS X₀ m) * LenB X₀ m ∧
        (∫ y in (a : ℝ)..(b : ℝ), (compDen θ X₀ ω y).toReal) - a1B X₀ m - a2B X₀ m ≤
          Cjit (CM θ X₀ ω) (Ucl ω) a b := by
  rw [ae_all_iff]; intro m
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro b
  by_cases hab : a < b
  · by_cases hW : AdmW X₀ m a b
    · filter_upwards [e3win_one hc hev hW] with ω hω
      intro _ _ _ _ t hbt hG hN
      exact hω t hbt hG hN
    · refine Filter.Eventually.of_forall fun ω h1 _ h3 h4 => ?_
      exact absurd ⟨h1, hab, h3, by unfold LenB at h4; exact h4⟩ hW
  · refine Filter.Eventually.of_forall fun ω h1 h2 _ _ t _ _ _ => ?_
    have hab' : a = b := le_antisymm h2 (not_lt.mp hab)
    subst hab'
    have hC : Cjit (CM θ X₀ ω) (Ucl ω) a a = 0 := by
      unfold Cjit
      have : cjitSet (CM θ X₀ ω) (Ucl ω) a a = ∅ := by
        ext e
        simp only [mem_empty_iff_false, iff_false]
        intro he
        have h1 := he.1.2.1
        have h2 := he.1.2.2
        linarith
      rw [this, Set.ncard_empty]; simp
    have hs2 := s2E3_pos hc (uS X₀ m) (uS_facts hc m).2.1
    have := a1B_nonneg hc m
    have := a2B_nonneg hc m
    have := LenB_pos hc m
    simp only [sub_self, Int.cast_zero, mul_zero, intervalIntegral.integral_same, hC]
    refine ⟨le_rfl, by positivity, by linarith⟩

end Window

end Queue6

end
