module

public import RequestProject.Beurling.BaseRange.GEdge

/-!
# Lemma 7.3(d)(iii): `g` as a sum of window-prime steps

`gEdge_rep` : for `X₀ ≤ z` and `⌊z⌋ ≤ N_max`,

  `g(z) = ∑_{2 ≤ N ≤ N_max} ∑_{p ∈ PW} c_{N,p} 1[z ∈ I_{N,p}] / (κ z)`,

where `PW` are the primes in `[X₀, (1+κ)X₀]`, `c_{N,p} = μ(N_>) ∑_{s ∣ N_≤, s < N_≤} μ(s)`
(`|c_{N,p}| ≤ 1`), and `I_{N,p} = {z : z/N ∈ (X₀/(1+κ), X₀), p ≤ (1+κ) z/N, χ_z(N_>)}`. This is
the coefficient analysis of the proof of (d)(iii) ("the coefficient of `p` in the `N`-term is
`χ_{N_>}(x) ∑ μ(N_> s)`"); in the variable `t = u/(m z)` of the telescoping, each step
`1[z ∈ I]/(κ z) · 1/(m t)` is the constant `1/(κ u)` on an interval.
-/

@[expose] public section

open Real Finset BeurlingSystem
open scoped ArithmeticFunction.Moebius

namespace BaseRange

/-- The window primes `p ∈ [X₀, (1+κ)X₀]`. -/
noncomputable def PW (X0 : ℕ) (κ : ℝ) : Finset ℕ :=
  (Finset.range (⌊(1 + κ) * X0⌋₊ + 1)).filter fun p => p.Prime ∧ X0 ≤ p

/-- The constant coefficient `c_{N,p} = μ(N_>) ∑_{s ∣ N_≤, s < N_≤} μ(s)`. -/
noncomputable def cNp (N p : ℕ) : ℝ :=
  (μ (Nbig N p) : ℝ) * ∑ s ∈ (Nsm N p).properDivisors, (μ s : ℝ)

lemma abs_cNp_le (N p : ℕ) : |cNp N p| ≤ 1 := by
  unfold cNp
  rw [abs_mul]
  have h1 : |(μ (Nbig N p) : ℝ)| ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or (Nbig N p) with h' | h' | h' <;> simp [h']
  have h3 := abs_sum_properDivisors_moebius_le (Nsm N p) (Nsm_ne_zero N p)
  calc _ ≤ (1 : ℝ) * 1 := by gcongr
    _ = 1 := by ring

/-- The window of the step `(N, p)`. -/
def inI (X0 : ℕ) (κ : ℝ) (N p : ℕ) (z : ℝ) : Prop :=
  InEdge X0 κ (z / N) ∧ (p : ℝ) ≤ (1 + κ) * (z / N) ∧ LemmaM.chi tQ lv z (Nbig N p)

open Classical in
/-- One `N`-term of `g` as a sum of steps. -/
lemma nterm_eq {X0 : ℕ} (hX : 1 < (X0 : ℝ)) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) {x : ℝ}
    (hx : (X0 : ℝ) ≤ x) {N : ℕ} (hN : 2 ≤ N) :
    ∑ d ∈ N.properDivisors, cQ X0 x d / d * edgeTerm X0 κ (x / d) (N / d) =
      ∑ p ∈ PW X0 κ, cNp N p * (if inI X0 κ N p x then 1 else 0) / (κ * x) := by
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hx0 : 0 < x := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set q := x / N with hq
  have hq0 : 0 < q := div_pos hx0 hN0
  set b := (1 + κ) * q with hb
  have hb0 : 0 ≤ b := by positivity
  have hterm : ∀ d ∈ N.properDivisors, cQ X0 x d / d * edgeTerm X0 κ (x / d) (N / d) =
      if InEdge X0 κ q then cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q / N else 0 := by
    intro d hd
    have hd' := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
    have hdN : d * (N / d) = N := Nat.mul_div_cancel' hd'.1
    have hNr : (d : ℝ) * ((N / d : ℕ) : ℝ) = N := by exact_mod_cast hdN
    unfold edgeTerm
    rw [div_div_natDiv hd hN]
    split_ifs
    · calc cQ X0 x d / d * (MAPfrom (max X0 (Pplus (N / d))) κ q / ((N / d : ℕ) : ℝ))
          = cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q / ((d : ℝ) * ((N / d : ℕ) : ℝ)) := by
            ring
        _ = _ := by rw [hNr]
    · ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hW : InEdge X0 κ q
  · simp only [if_pos hW]
    rw [← Finset.sum_div]
    set W := (Finset.range (⌊b⌋₊ + 1)).filter fun p => p.Prime ∧ X0 ≤ p ∧ q ≤ p with hWdef
    have hcount : ∀ d ∈ N.properDivisors, (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ) =
        ∑ p ∈ W, if Pplus (N / d) ≤ p then 1 else 0 := by
      intro d _
      rw [newPrimeCount_eq_card' _ hb0, Finset.sum_boole, ← Finset.filter_filter]
      congr 2
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, max_le_iff, hWdef]
      tauto
    have hc : ∀ d ∈ N.properDivisors, cQ X0 x d = (μ d : ℝ) *
        (if LemmaM.chi tQ lv x d then 1 else 0) := by
      intro d hd
      have hd' := Nat.mem_properDivisors.mp hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
      have hle : (X0 : ℝ) ≤ x / d := by
        have h2 : 2 * d ≤ N := by
          obtain ⟨k, hk⟩ := hd'.1
          have hk2 : 2 ≤ k := by
            by_contra hc; push_neg at hc
            interval_cases k <;> omega
          calc 2 * d ≤ k * d := Nat.mul_le_mul_right _ hk2
            _ = N := by rw [hk]; ring
        have h2r : 2 * (d : ℝ) ≤ N := by exact_mod_cast h2
        have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
        have hW1 := hW.1
        rw [div_lt_iff₀ (by linarith)] at hW1
        rw [le_div_iff₀ hdr]
        have : x = q * N := by rw [hq]; field_simp
        rw [this]
        nlinarith
      rw [cQ_eq hx hd0, if_pos hle]
      ring
    have hκq : 0 < κ * q := mul_pos hκ hq0
    have hsum1 : ∑ d ∈ N.properDivisors, cQ X0 x d * MAPfrom (max X0 (Pplus (N / d))) κ q =
        (∑ d ∈ N.properDivisors, cQ X0 x d *
          (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ)) / (κ * q) := by
      unfold MAPfrom
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    have hsum2 : ∑ d ∈ N.properDivisors, cQ X0 x d *
        (newPrimeCount (max X0 (Pplus (N / d))) q b : ℝ) =
        ∑ p ∈ W, ∑ d ∈ N.properDivisors.filter (fun d => Pplus (N / d) ≤ p),
          (μ d : ℝ) * (if LemmaM.chi tQ lv x d then 1 else 0) := by
      rw [Finset.sum_congr rfl (fun d hd => by rw [hcount d hd, Finset.mul_sum])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hc d hd]
      split_ifs <;> ring
    have hpN : ∀ p ∈ W, (p : ℝ) * N < 2 * x := by
      intro p hp
      obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
      have hpb : (p : ℝ) ≤ b := by
        have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hb0)
      have : b * N = (1 + κ) * x := by rw [hb, hq]; field_simp
      nlinarith
    -- `W = {p ∈ PW : p ≤ b}`
    have hWPW : W = (PW X0 κ).filter (fun p : ℕ => (p : ℝ) ≤ b) := by
      ext p
      simp only [hWdef, PW, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        have hpb : (p : ℝ) ≤ b := (Nat.cast_le.mpr (Nat.lt_succ_iff.mp h1)).trans
          (Nat.floor_le hb0)
        refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor ?_), h2, h3⟩, hpb⟩
        have : b ≤ (1 + κ) * X0 := by rw [hb]; nlinarith [hW.2]
        linarith
      · rintro ⟨⟨-, h2, h3⟩, h4⟩
        refine ⟨Nat.lt_succ_of_le (Nat.le_floor h4), h2, h3, ?_⟩
        have : (X0 : ℝ) ≤ p := by exact_mod_cast h3
        linarith [hW.2]
    rw [hsum1, hsum2, hWPW, Finset.sum_filter, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold inI
    by_cases hpb : (p : ℝ) ≤ b
    · have hpN' : (p : ℝ) * N < 2 * x := hpN p (by rw [hWPW]; exact Finset.mem_filter.mpr ⟨hp, hpb⟩)
      rw [if_pos hpb, coeff_window_eq hN hpN']
      unfold cNp
      have e : κ * q * N = κ * x := by rw [hq]; field_simp
      by_cases hch : LemmaM.chi tQ lv x (Nbig N p)
      · rw [if_pos hch, if_pos ⟨hW, hpb, hch⟩]
        have e2 : q * N = x := by rw [hq]; field_simp
        field_simp
        rw [mul_assoc _ q, e2]
      · rw [if_neg hch, if_neg (fun h => hch h.2.2)]
        simp
    · rw [if_neg hpb, if_neg (fun h => hpb h.2.1)]
      simp
  · simp only [if_neg hW, Finset.sum_const_zero]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    unfold inI
    rw [if_neg (fun h => hW h.1)]
    simp

end BaseRange
