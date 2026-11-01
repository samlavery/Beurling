module

public import RequestProject.Beurling.BaseRange.Mismatch
public import RequestProject.Beurling.BaseRange.PsiDiff

/-!
# The `θ`-difference of the large primes (proof of Lemma 7.3(b), Steps 2–3)

* `ratSys_card_elems`, `ratSys_hbs` : the rational system counts the integers and satisfies
  (HBS) with `ε₁ = 0`;
* `psi_sub_theta` : `0 ≤ ψ_S(s) - θ_S(s) ≤ log s · #{p ≤ √s}` (the prime powers);
* `J1 X₀⁻`, `small_eq`, `large_ge` : the first `J₁` primes are the rational primes `< X₀⁻`;
* `thetaF_diff_le` : **the input of the one-replacement step**: for `X₀⁻/2 ≤ s ≤ x`,
  `|θ_large,𝒩(s) - θ_large,ℚ(s)| ≤ (2A + 2.1/√(X₀⁻/2)) s (log s + 1)²`, from Step 2 (`psi_diff_le`,
  `|ψ_𝒩 - ψ| ≤ 2A s (log s + 1)²` under `|N_𝒩 - ⌊·⌋| ≤ A v`) and the prime powers.
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-! ### The rational system -/

lemma ratSys_card_elems (v : ℝ) : ((ratSys.elems v).card : ℝ) = ⌊v⌋₊ := by
  classical
  rcases lt_or_ge v 0 with hv | hv
  · rw [ratSys.elems_eq_empty (by linarith), Nat.floor_eq_zero.mpr (by linarith)]; simp
  have : (ratSys.elems v).card = (Finset.Icc 1 ⌊v⌋₊).card := by
    apply Finset.card_bij (fun e _ => iota e)
    · intro e he
      rw [ratSys.mem_elems, ratSys_val] at he
      exact Finset.mem_Icc.mpr ⟨iota_pos e, Nat.le_floor he⟩
    · intro e _ e' _ h; exact iota_injective h
    · intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      obtain ⟨e, -, he⟩ := exists_iota_eq (n := m) (j := m + 1) (by omega) (fun r hr => by
        have h1 : r ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hr)
        have h2 : m + 1 ≤ qp (m + 1) := qp_strictMono.id_le (m + 1)
        omega)
      refine ⟨e, ?_, he⟩
      rw [ratSys.mem_elems, ratSys_val, he]
      exact (Nat.le_floor_iff hv).mp hm2
  rw [this, Nat.card_Icc]; simp

lemma ratSys_N (v : ℝ) : ratSys.N v = ⌊v⌋₊ := by
  rw [ratSys.N_eq_card, ratSys_card_elems]

/-- **(HBS) for the rational system** with `ε₁ = 0`. -/
lemma ratSys_hbs {X0m Z : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X0m) :
    ratSys.HBS X0m Z 0 0 (fun _ => 0) where
  X0m_ge := hX
  eta1_nonneg := le_rfl
  eta1_le := by norm_num
  eta2_nonneg := le_rfl
  eta2_le := by norm_num
  floor_eq := fun v _ _ _ => ratSys_N v
  err := fun v _ _ => by rw [ratSys_N]; simp
  eta2 := fun v _ _ => by simp
  eta1 := fun _ K _ _ => by simp

lemma ratSys_psi (s : ℝ) : ratSys.psi s = Chebyshev.psi s :=
  ratSys.psi_eq_chebyshev fun _ _ => rfl

/-! ### The prime powers -/

/-- `θ_S(s) = ∑_{p_j ≤ s} log p_j`. -/
noncomputable def thetaS (S : BeurlingSystem) (s : ℝ) : ℝ :=
  ∑ j ∈ S.primesLe s, Real.log (S.p j)

lemma thetaS_le_psi (S : BeurlingSystem) (s : ℝ) : thetaS S s ≤ S.psi s := by
  classical
  rw [S.psi_eq_sum]
  unfold thetaS
  rw [← Finset.sum_image (s := S.primesLe s) (g := fun j => (j, 0))
    (f := fun jk : ℕ × ℕ => Real.log (S.p jk.1)) (fun a _ b _ h => (Prod.mk.inj h).1)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro jk hjk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjk
    rw [S.mem_pps]; simpa using S.mem_primesLe.mp hj
  · intro jk _ _; exact S.log_p_nonneg _

/-- **The prime powers**: `0 ≤ ψ_S(s) - θ_S(s) ≤ log s · #{p_j ≤ √s}` for `s ≥ 1`. -/
theorem psi_sub_theta (S : BeurlingSystem) {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ S.psi s - thetaS S s ∧
      S.psi s - thetaS S s ≤ Real.log s * (S.primesLe (Real.sqrt s)).card := by
  classical
  refine ⟨by linarith [thetaS_le_psi S s], ?_⟩
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs
  rw [S.psi_eq_sum, ← Finset.sum_filter_add_sum_filter_not (S.pps s) (fun jk => jk.2 = 0)]
  have h0 : ∑ jk ∈ (S.pps s).filter (fun jk => jk.2 = 0), Real.log (S.p jk.1) = thetaS S s := by
    unfold thetaS
    apply Finset.sum_nbij' Prod.fst (fun j => (j, 0))
    · intro jk hjk
      rw [Finset.mem_filter, S.mem_pps] at hjk
      rw [S.mem_primesLe]
      rw [hjk.2] at hjk; simpa using hjk.1
    · intro j hj
      rw [S.mem_primesLe] at hj
      rw [Finset.mem_filter, S.mem_pps]
      exact ⟨by simpa using hj, rfl⟩
    · intro jk hjk
      rw [Finset.mem_filter] at hjk
      ext
      · rfl
      · exact hjk.2.symm
    · intro j _; rfl
    · intro jk _; rfl
  rw [h0, add_sub_cancel_left]
  set A1 := (S.pps s).filter (fun jk => ¬ jk.2 = 0)
  have hmaps : ∀ jk ∈ A1, jk.1 ∈ S.primesLe (Real.sqrt s) := by
    intro jk hjk
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hjk
    rw [S.mem_pps] at h1
    rw [S.mem_primesLe, Real.le_sqrt (S.p_pos _).le (by linarith)]
    calc S.p jk.1 ^ 2 ≤ S.p jk.1 ^ (jk.2 + 1) :=
          pow_le_pow_right₀ (S.one_lt _).le (by omega)
      _ ≤ s := h1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ S.primesLe (Real.sqrt s),
      ∑ jk ∈ A1.filter (fun jk => jk.1 = j), Real.log (S.p jk.1) ≤ Real.log s := by
    intro j _
    have hlp : 0 < Real.log (S.p j) := Real.log_pos (S.one_lt j)
    set M := ⌊Real.log s / Real.log (S.p j)⌋₊
    rw [Finset.sum_congr rfl (g := fun _ => Real.log (S.p j)) (fun jk hjk => by
      rw [(Finset.mem_filter.mp hjk).2]), Finset.sum_const, nsmul_eq_mul]
    have hcard : (A1.filter (fun jk => jk.1 = j)).card ≤ M := by
      calc (A1.filter (fun jk => jk.1 = j)).card
          = ((A1.filter (fun jk => jk.1 = j)).image Prod.snd).card := by
            rw [Finset.card_image_of_injOn]
            intro a ha b hb h
            have h1 := (Finset.mem_filter.mp ha).2
            have h2 := (Finset.mem_filter.mp hb).2
            exact Prod.ext (h1.trans h2.symm) h
        _ ≤ (Finset.Icc 1 M).card := by
            apply Finset.card_le_card
            intro k hk
            obtain ⟨jk, hjk, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨hjk1, hjk2⟩ := Finset.mem_filter.mp hjk
            obtain ⟨hpp, hk0⟩ := Finset.mem_filter.mp hjk1
            rw [S.mem_pps, hjk2] at hpp
            refine Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hk0, ?_⟩
            have hl := Real.log_le_log (pow_pos (S.p_pos j) _) hpp
            rw [Real.log_pow] at hl
            have : ((jk.2 + 1 : ℕ) : ℝ) ≤ Real.log s / Real.log (S.p j) := by
              rw [le_div_iff₀ hlp]; exact hl
            have := Nat.le_floor this
            omega
        _ = M := by simp
    have hM : (M : ℝ) * Real.log (S.p j) ≤ Real.log s := by
      have := Nat.floor_le (div_nonneg hls hlp.le)
      calc (M : ℝ) * Real.log (S.p j) ≤ Real.log s / Real.log (S.p j) * Real.log (S.p j) :=
            mul_le_mul_of_nonneg_right this hlp.le
        _ = Real.log s := by field_simp
    calc ((A1.filter (fun jk => jk.1 = j)).card : ℝ) * Real.log (S.p j)
        ≤ (M : ℝ) * Real.log (S.p j) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlp.le
      _ ≤ Real.log s := hM
  refine (Finset.sum_le_sum hfib).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `#{p_j ≤ y} log 2 ≤ ψ_S(y)` when all `p_j ≥ 2`. -/
lemma card_primesLe_mul_log_two_le (S : BeurlingSystem) (h2 : ∀ j, 2 ≤ S.p j) (y : ℝ) :
    ((S.primesLe y).card : ℝ) * Real.log 2 ≤ S.psi y := by
  refine le_trans ?_ (thetaS_le_psi S y)
  unfold thetaS
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun j _ => Real.log_le_log (by norm_num) (h2 j)

/-! ### The small primes -/

/-- `J₁ = #{rational primes < X₀⁻}`. -/
noncomputable def J1 (X0m : ℝ) : ℕ := Nat.count Nat.Prime ⌈X0m⌉₊

lemma lt_J1_iff (X0m : ℝ) (j : ℕ) : j < J1 X0m ↔ ((qp j : ℕ) : ℝ) < X0m := by
  unfold J1
  rw [Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime, Nat.lt_ceil]

lemma small_eq {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) (hZ : X0m ≤ Z) {j : ℕ} (hj : j < J1 X0m) :
    P.p j = qp j ∧ P.p j < X0m := by
  rw [lt_J1_iff] at hj
  have hx : ((qp j : ℕ) : ℝ) ≤ Z := by linarith
  have e := h.ident hj hx j (Or.inr le_rfl)
  exact ⟨e, by rw [e]; exact hj⟩

lemma large_ge {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) (hZ : X0m ≤ Z) {j : ℕ} (hj : J1 X0m ≤ j) : X0m ≤ P.p j := by
  by_contra hc
  push_neg at hc
  have e := h.ident hc (by linarith) j (Or.inl le_rfl)
  have : j < J1 X0m := by rw [lt_J1_iff, ← e]; exact hc
  omega

/-- The large part of `θ`. -/
lemma thetaF_split (S : BeurlingSystem) (J : ℕ) {x s : ℝ} (hs : s ≤ x) :
    thetaF S.p (S3.Lg S J x) s =
      thetaS S s - ∑ j ∈ (S.primesLe s).filter (· < J), Real.log (S.p j) := by
  classical
  unfold thetaF S3.Lg thetaS
  rw [← Finset.sum_filter_add_sum_filter_not (S.primesLe s) (· < J), add_sub_cancel_left]
  congr 1
  ext j
  simp only [Finset.mem_filter, S.mem_primesLe, not_lt]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩; exact ⟨⟨h3.trans hs, h2⟩, h3⟩

/-- **The `θ`-difference of the large primes**: under (HBS) on `[1, Z]` and `|N_𝒩 - ⌊·⌋| ≤ A v`
on `[0, x]`, `x ≤ Z`: for `X₀⁻/2 ≤ s ≤ x`,
`|θ_large,𝒩(s) - θ_large,ℚ(s)| ≤ (2A + 2.1/√(X₀⁻/2)) s (log s + 1)²`. -/
theorem thetaF_diff_le {P : BeurlingSystem} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
    (h : P.HBS X0m Z η1 η2 ε1) {A x : ℝ} (hA : 0 ≤ A) (hxZ : x ≤ Z) (hXZ : X0m ≤ Z)
    (hloc : ∀ v, 0 ≤ v → v ≤ x → |P.N v - ⌊v⌋₊| ≤ A * v) :
    ∀ s ∈ Set.Icc (X0m / 2) x,
      |thetaF P.p (S3.Lg P (J1 X0m) x) s - thetaF ratSys.p (S3.Lg ratSys (J1 X0m) x) s| ≤
        (2 * A + 2.1 / Real.sqrt (X0m / 2)) * s * (Real.log s + 1) ^ 2 := by
  classical
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hX7 := h.X0m_ge
  have hs1' : 1 ≤ s := by linarith
  have hZ3 : 3 ≤ Z := by linarith
  have hQ := ratSys_hbs (X0m := X0m) (Z := Z) hX7
  rw [thetaF_split P _ hs2, thetaF_split ratSys _ hs2]
  -- the small parts agree
  have hsm : ∑ j ∈ (P.primesLe s).filter (· < J1 X0m), Real.log (P.p j) =
      ∑ j ∈ (ratSys.primesLe s).filter (· < J1 X0m), Real.log (ratSys.p j) := by
    have hset : (P.primesLe s).filter (· < J1 X0m) = (ratSys.primesLe s).filter (· < J1 X0m) := by
      ext j
      simp only [Finset.mem_filter, P.mem_primesLe, ratSys.mem_primesLe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rw [ratSys_p, ← (small_eq h hXZ h2).1]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rw [(small_eq h hXZ h2).1]; exact h1, h2⟩
    rw [hset]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [(small_eq h hXZ (Finset.mem_filter.mp hj).2).1, ratSys_p]
  rw [hsm, sub_sub_sub_cancel_right]
  -- Step 2
  have hψ := psi_diff_le h hA hxZ hloc hs1' hs2
  rw [← ratSys_psi] at hψ
  -- the prime powers
  have hsq : Real.sqrt s ≤ s := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs1'
  have hpp : ∀ (S : BeurlingSystem) (a b : ℝ) (c : ℝ → ℝ) (hS : S.HBS X0m Z a b c),
      0 ≤ S.psi s - thetaS S s ∧ S.psi s - thetaS S s ≤ 2.1 * Real.sqrt s * Real.log s := by
    intro S a b c hS
    obtain ⟨a1, a2⟩ := psi_sub_theta S hs1'
    refine ⟨a1, a2.trans ?_⟩
    have hc := card_primesLe_mul_log_two_le S (BeurlingSystem.HBS.two_le_p hS hZ3)
      (Real.sqrt s)
    have hψs := hS.psi_le hsq0 (hsq.trans (hs2.trans hxZ))
    have : ((S.primesLe (Real.sqrt s)).card : ℝ) ≤ 2.1 * Real.sqrt s := by
      have h0 : (0 : ℝ) ≤ (S.primesLe (Real.sqrt s)).card := Nat.cast_nonneg _
      nlinarith
    calc Real.log s * (S.primesLe (Real.sqrt s)).card ≤ Real.log s * (2.1 * Real.sqrt s) :=
          mul_le_mul_of_nonneg_left this hls
      _ = 2.1 * Real.sqrt s * Real.log s := by ring
  have hPP := hpp P _ _ _ h
  have hQQ := hpp ratSys _ _ _ hQ
  -- `√s log s ≤ s (log s + 1)²/√(X₀⁻/2)`
  have hXs : 0 < Real.sqrt (X0m / 2) := Real.sqrt_pos.mpr (by linarith)
  have hsqs : Real.sqrt (X0m / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs1
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt (by linarith)
  have hkey : 2.1 * Real.sqrt s * Real.log s ≤
      2.1 / Real.sqrt (X0m / 2) * s * (Real.log s + 1) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hXs]
    have h1 : Real.log s ≤ (Real.log s + 1) ^ 2 := by nlinarith
    have h2 : Real.sqrt s * Real.sqrt (X0m / 2) ≤ s := by nlinarith
    calc 2.1 * Real.sqrt s * Real.log s * Real.sqrt (X0m / 2)
        = 2.1 * (Real.sqrt s * Real.sqrt (X0m / 2)) * Real.log s := by ring
      _ ≤ 2.1 * s * (Real.log s + 1) ^ 2 := by
          have := mul_le_mul h2 h1 hls (by linarith)
          nlinarith
  have hfin : |thetaS P s - thetaS ratSys s| ≤
      |P.psi s - ratSys.psi s| + 2.1 * Real.sqrt s * Real.log s := by
    have h1 := neg_abs_le (P.psi s - ratSys.psi s)
    have h2 := le_abs_self (P.psi s - ratSys.psi s)
    rw [abs_le]
    constructor <;> linarith [hPP.1, hPP.2, hQQ.1, hQQ.2]
  calc |thetaS P s - thetaS ratSys s|
      ≤ |P.psi s - ratSys.psi s| + 2.1 * Real.sqrt s * Real.log s := hfin
    _ ≤ 2 * A * s * (Real.log s + 1) ^ 2 + 2.1 / Real.sqrt (X0m / 2) * s *
          (Real.log s + 1) ^ 2 := add_le_add hψ hkey
    _ = (2 * A + 2.1 / Real.sqrt (X0m / 2)) * s * (Real.log s + 1) ^ 2 := by ring

end BaseRange
