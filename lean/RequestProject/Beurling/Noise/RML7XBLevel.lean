module

public import RequestProject.Beurling.Noise.RML7XBKern

/-!
# Proposition 5.31(i): the bound of the term of `𝔅` at a rational level

At a level `n` all of whose divisors are rational integers (`V(m) = m` for `m ∣ n`, which holds
below `X₀⁻`), each step term of `𝔅` is at most

  `β(d) = μ²(d) + ¼λ₀ ∑_{e ∣ d, 1<e<d} μ²(e) (d/e)^ε H_ord(d/e) e/d`

(the `𝔹₁` weight; the `𝔹₂` weight is smaller), so the term of `𝔅(y)` at `n` is at most

  `Br(n) = n⁻¹ [μ²(n)/2 + ∑_{d ∣ n, 1<d<n} β(d)]`

(`xbTerm_le_Br`; 04x-x0band.tex, proof of Proposition 5.31(i), "The bound `B(n₀)`").
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.XB7

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m y : ℝ}

/-- `β(d) = μ²(d) + ¼λ₀ ∑_{e ∣ d, 1<e<d} μ²(e) (d/e)^ε H_ord(d/e) e/d`. -/
noncomputable def betaD (ε lam0 : ℝ) (d : ℕ) : ℝ :=
  musqR d + 1 / 4 * lam0 * ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
    musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)

/-- `Br(n) = n⁻¹ [μ²(n)/2 + ∑_{d ∣ n, 1<d<n} β(d)]`. -/
noncomputable def BrN (ε lam0 : ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) * (musqR n / 2 + ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n),
    betaD ε lam0 d)

lemma betaD_sum_nonneg (ε : ℝ) (d : ℕ) :
    0 ≤ ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d) :=
  Finset.sum_nonneg fun e _ => by
    have := musqR_nonneg e
    have : (0 : ℝ) ≤ ((d / e : ℕ) : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity

lemma betaD_nonneg {ε lam0 : ℝ} (hlam0 : 0 ≤ lam0) (d : ℕ) : 0 ≤ betaD ε lam0 d := by
  unfold betaD
  have := musqR_nonneg d
  have := betaD_sum_nonneg ε d
  positivity

lemma divisors_filter_one_lt {d : ℕ} (hd : 2 ≤ d) :
    d.divisors.filter (1 < ·) = insert d (d.divisors.filter (fun e => 1 < e ∧ e < d)) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hed, hd0⟩, he1⟩
    rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hed) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨⟨hed, hd0⟩, he1, h⟩
  · rintro (rfl | ⟨h1, h2, -⟩)
    · exact ⟨⟨dvd_refl _, by omega⟩, by omega⟩
    · exact ⟨h1, h2⟩

/-- The rational facts at a level all of whose divisors have `V(m) = m`. -/
lemma rat_facts {n : ℕ} (hn0 : n ≠ 0)
    (hrat : ∀ m, m ∣ n → LemmaM.valN P.labelVal m = m) {d e : ℕ} (hdn : d ∣ n)
    (hed : e ∣ d) :
    LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d = (e : ℝ) / d ∧
      LemmaM.valN P.labelVal (d / e) = ((d / e : ℕ) : ℝ) ∧
      LemmaM.valN P.labelVal (n / e) =
        LemmaM.valN P.labelVal (n / d) * ((d / e : ℕ) : ℝ) := by
  have hen : e ∣ n := hed.trans hdn
  refine ⟨by rw [hrat e hen, hrat d hdn], hrat _ ((Nat.div_dvd_of_dvd hed).trans hdn), ?_⟩
  rw [hrat _ (Nat.div_dvd_of_dvd hen), hrat _ (Nat.div_dvd_of_dvd hdn)]
  have hd0 : d ≠ 0 := fun h => by subst h; simp at hdn; omega
  have he0 : e ≠ 0 := fun h => by subst h; simp at hed; omega
  obtain ⟨k, rfl⟩ := hdn
  obtain ⟨j, rfl⟩ := hed
  have h0 : e * j * k / e = j * k := by
    rw [mul_assoc]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)
  have h1 : e * j * k / (e * j) = k := Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0)
  have h2 : e * j / e = j := Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero he0)
  rw [h0, h1, h2]; push_cast; ring

/-- **The step bound**: every step term of `𝔅(y)` at a rational level is at most `β(d)`. -/
lemma xbBstep_le_betaD {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hy : X0m ≤ y) {n : ℕ} (hn : n ∈ levels P X0m y)
    (hrat : ∀ m, m ∣ n → LemmaM.valN P.labelVal m = m) {d : ℕ} (hd : d ∈ n.properDivisors) :
    xbBstep P H tw X0m y X0 θ lam0 d n ≤ betaD ε lam0 d := by
  classical
  have hval : ∀ p, p.Prime → 1 ≤ P.labelVal p := fun p _ => P.one_le_labelVal p
  have hval2 : ∀ p, p.Prime → 2 ≤ P.labelVal p := fun p _ => hp2 _
  have hX := hP.X0m_pos
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  have hβ := betaD_nonneg (ε := ε) hlam0 d
  obtain ⟨hnA, hn2⟩ := Finset.mem_filter.mp hn
  have hzn : X0m / 2 ≤ posn P.labelVal y n := posn_ge_of_mem_NAll hnA (by linarith)
  have hdn := (Nat.mem_properDivisors.mp hd).1
  have hn0 : n ≠ 0 := by omega
  have hw2 := two_le_valN hval2 (two_le_div_of_mem hd)
  set w := LemmaM.valN P.labelVal (n / d)
  have hpd : posn P.labelVal y d = posn P.labelVal y n * w := posn_mul hval hdn hn0
  have hzd : X0m / 2 ≤ posn P.labelVal y d := by rw [hpd]; nlinarith
  have hHn := hP.reg.pos (posn P.labelVal y n)
  have hHd := hP.reg.pos (posn P.labelVal y d)
  unfold xbBstep
  by_cases h1 : d = 1
  · rw [if_pos h1]; exact hβ
  rw [if_neg h1]
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d
      · simp at hdn; omega
      · exact absurd rfl h1
    · exact h
  have hd0 : d ≠ 0 := by omega
  -- the common term bound
  have hterm : ∀ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      |cN P tw X0m y e| * (Hlev P.labelVal y H e / Hlev P.labelVal y H d) *
          (BSCert.X0Band.Hord (d / e) : ℝ) *
            (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) ≤
        musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) *
          ((e : ℝ) / d) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hed : e ∣ d := Nat.dvd_of_mem_divisors he'.1
    have he1 : 1 < e := he'.2.1
    obtain ⟨hr1, hr2, -⟩ := rat_facts hn0 hrat hdn hed
    have hc := abs_cN_le ht hX.le hy (m := e) (by omega) (P := P) (tw := tw)
    have hH := Hlev_le hP hed hd0 hzd (y := y) (H := H)
    rw [hr2] at hH
    have hrat' : Hlev P.labelVal y H e / Hlev P.labelVal y H d ≤ ((d / e : ℕ) : ℝ) ^ ε := by
      unfold Hlev; rw [div_le_iff₀ hHd]; exact hH
    rw [hr1]
    have h0 : 0 ≤ Hlev P.labelVal y H e / Hlev P.labelVal y H d := by
      unfold Hlev; have := hP.reg.pos (posn P.labelVal y e); positivity
    have hH0 : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
    have hed0 : (0 : ℝ) ≤ (e : ℝ) / d := by positivity
    apply mul_le_mul_of_nonneg_right _ hed0
    apply mul_le_mul_of_nonneg_right _ hH0
    exact mul_le_mul hc hrat' h0 (musqR_nonneg e)
  have hsum := Finset.sum_le_sum hterm
  have hS0 := betaD_sum_nonneg ε d
  have hcd := abs_cN_le ht hX.le hy (m := d) (by omega) (P := P) (tw := tw)
  by_cases hXN : X0Near P.labelVal y H X0m d n
  · rw [if_pos hXN]
    split_ifs with hT
    · exact hβ
    · have h := halfTVD_le hP hp2 ht hlam hy hd2 (H := H) (tw := tw) (P := P)
      unfold betaD
      nlinarith
  rw [if_neg hXN]
  split_ifs with hB2
  · -- the `𝔹₂` weight
    have hK := KRD_le hP hp2 ht hlam hy hd2 (H := H) (tw := tw) (P := P)
    rw [divisors_filter_one_lt hd2, Finset.sum_insert (by simp)] at hK
    rw [Nat.div_self (by omega)] at hK
    -- `H_e ≤ (n/e)^ε H_n = w^ε (d/e)^ε H_n`
    have hw0 : 0 < w := by linarith
    have hwε : w ^ ε / w ≤ 0.5005 := by
      have hε := hP.eps_le
      have e1 : w ^ ε / w = w ^ (ε - 1) := by rw [Real.rpow_sub hw0, Real.rpow_one]
      have e2 : (2 : ℝ) ^ ε / 2 = 2 ^ (ε - 1) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      have h3 : w ^ (ε - 1) ≤ 2 ^ (ε - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hw2 (by linarith)
      have h4 := two_rpow_le hP.eps_nonneg hP.eps_le
      rw [e1]; linarith [e2 ▸ h3]
    have hwε0 : 0 ≤ w ^ ε := Real.rpow_nonneg hw0.le _
    have hterm2 : ∀ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
        |cN P tw X0m y e| * Hlev P.labelVal y H e * (BSCert.X0Band.Hord (d / e) : ℝ) *
            (LemmaM.valN P.labelVal e / LemmaM.valN P.labelVal d) ≤
          w ^ ε * H (posn P.labelVal y n) * (musqR e * (((d / e : ℕ) : ℝ) ^ ε) *
            (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)) := by
      intro e he
      have he' := Finset.mem_filter.mp he
      have hed : e ∣ d := Nat.dvd_of_mem_divisors he'.1
      have he1 : 1 < e := he'.2.1
      obtain ⟨hr1, -, hr3⟩ := rat_facts hn0 hrat hdn hed
      have hc := abs_cN_le ht hX.le hy (m := e) (by omega) (P := P) (tw := tw)
      have hH := Hlev_le hP (hed.trans hdn) hn0 hzn (y := y) (H := H)
      rw [hr3, Real.mul_rpow hw0.le (Nat.cast_nonneg _)] at hH
      rw [hr1]
      have hH0 : (0 : ℝ) ≤ (BSCert.X0Band.Hord (d / e) : ℝ) := Nat.cast_nonneg _
      have hed0 : (0 : ℝ) ≤ (e : ℝ) / d := by positivity
      have hHe0 : 0 ≤ Hlev P.labelVal y H e := (hP.reg.pos _).le
      have hq0 : (0 : ℝ) ≤ ((d / e : ℕ) : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hmu := musqR_nonneg e
      have hm : |cN P tw X0m y e| * Hlev P.labelVal y H e ≤
          musqR e * (w ^ ε * ((d / e : ℕ) : ℝ) ^ ε * H (posn P.labelVal y n)) :=
        mul_le_mul hc (by unfold Hlev; exact hH) hHe0 hmu
      have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hH0) hed0
      have e1 : musqR e * (w ^ ε * ((d / e : ℕ) : ℝ) ^ ε * H (posn P.labelVal y n)) *
          (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d) =
          w ^ ε * H (posn P.labelVal y n) * (musqR e * (((d / e : ℕ) : ℝ) ^ ε) *
            (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)) := by ring
      linarith
    have hsum2 := Finset.sum_le_sum hterm2
    rw [← Finset.mul_sum] at hsum2
    have hcd' : |cN P tw X0m y d| * Hlev P.labelVal y H d * 1 *
        (LemmaM.valN P.labelVal d / LemmaM.valN P.labelVal d) ≤
        w ^ ε * H (posn P.labelVal y n) * musqR d := by
      have hH := Hlev_le hP hdn hn0 hzn (y := y) (H := H)
      rw [div_self (KR.valN_labelVal_pos P d).ne', mul_one, mul_one]
      have hHd0 : 0 ≤ Hlev P.labelVal y H d := (hP.reg.pos _).le
      have hm : |cN P tw X0m y d| * Hlev P.labelVal y H d ≤ musqR d * (w ^ ε *
          H (posn P.labelVal y n)) := mul_le_mul hcd (by unfold Hlev; exact hH) hHd0
            (musqR_nonneg d)
      linarith
    have hHord1 : (BSCert.X0Band.Hord 1 : ℝ) = 1 := by
      rw [BSCert.X0Band.Hord_eq 1, if_pos le_rfl]; norm_num
    rw [hHord1] at hK
    -- assemble
    set S := ∑ e ∈ d.divisors.filter (fun e => 1 < e ∧ e < d),
      musqR e * (((d / e : ℕ) : ℝ) ^ ε) * (BSCert.X0Band.Hord (d / e) : ℝ) * ((e : ℝ) / d)
    have hKRD : KRD P H tw X0m y d ≤
        1 / 4 * lam0 * (w ^ ε * H (posn P.labelVal y n) * (musqR d + S)) := by
      refine hK.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := add_le_add hcd' hsum2
      linarith
    have hden : 0 < w * H (posn P.labelVal y n) := by positivity
    rw [div_le_iff₀ hden]
    have hmud := musqR_nonneg d
    have e1 : lam0 * (1 / 4 * lam0 * (w ^ ε * H (posn P.labelVal y n) * (musqR d + S))) =
        (1 / 4 * lam0 ^ 2 * (w ^ ε / w)) * (musqR d + S) * (w * H (posn P.labelVal y n)) := by
      field_simp
    have hq0 : 0 ≤ w ^ ε / w := div_nonneg hwε0 hw0.le
    have hlq : lam0 * (w ^ ε / w) ≤ 1 := by
      have := mul_le_mul hlam1 hwε hq0 (by norm_num : (0 : ℝ) ≤ 1.001)
      linarith
    have hc1 : 1 / 4 * lam0 ^ 2 * (w ^ ε / w) ≤ 1 / 4 * lam0 := by
      have e : 1 / 4 * lam0 ^ 2 * (w ^ ε / w) = 1 / 4 * lam0 * (lam0 * (w ^ ε / w)) := by ring
      rw [e]
      exact mul_le_of_le_one_right (by positivity) hlq
    have hc2 : 1 / 4 * lam0 ^ 2 * (w ^ ε / w) ≤ 1 := by
      have : 1 / 4 * lam0 ≤ 1 := by linarith
      linarith
    have hc0 : 0 ≤ 1 / 4 * lam0 ^ 2 * (w ^ ε / w) := by positivity
    calc lam0 * KRD P H tw X0m y d ≤
          lam0 * (1 / 4 * lam0 * (w ^ ε * H (posn P.labelVal y n) * (musqR d + S))) :=
          mul_le_mul_of_nonneg_left hKRD hlam0
      _ = (1 / 4 * lam0 ^ 2 * (w ^ ε / w)) * (musqR d + S) * (w * H (posn P.labelVal y n)) := e1
      _ ≤ betaD ε lam0 d * (w * H (posn P.labelVal y n)) := by
          apply mul_le_mul_of_nonneg_right _ hden.le
          have hS0' : 0 ≤ S := hS0
          have k1 : (1 / 4 * lam0 ^ 2 * (w ^ ε / w)) * musqR d ≤ musqR d :=
            mul_le_of_le_one_left hmud hc2
          have k2 : (1 / 4 * lam0 ^ 2 * (w ^ ε / w)) * S ≤ 1 / 4 * lam0 * S :=
            mul_le_mul_of_nonneg_right hc1 hS0'
          show _ ≤ musqR d + 1 / 4 * lam0 * S
          linarith
  · exact hβ

/-- **The term of `𝔅(y)` at a rational level** is at most `Br(n)`. -/
theorem xbTerm_le_Br {ε θ X0 lam0 : ℝ} (hP : PaperWidth H X0m ε θ) (hp2 : ∀ j, 2 ≤ P.p j)
    (ht : ∀ p, p.Prime → 0 < tw p) (hlam : 1 + 2 * θ ≤ lam0) (hlam1 : lam0 ≤ 1.001)
    (hy : X0m ≤ y) {n : ℕ} (hn : n ∈ levels P X0m y)
    (hrat : ∀ m, m ∣ n → LemmaM.valN P.labelVal m = m) :
    xbTerm P H tw X0m y X0 θ lam0 n ≤ BrN ε lam0 n := by
  classical
  have hX := hP.X0m_pos
  have hlam0 : 0 ≤ lam0 := by linarith [hP.theta_nonneg]
  obtain ⟨-, hn2⟩ := Finset.mem_filter.mp hn
  have hn0 : n ≠ 0 := by omega
  have hVn : LemmaM.valN P.labelVal n = n := hrat n dvd_rfl
  unfold xbTerm BrN
  rw [show Vl P n = (n : ℝ) from hVn, div_eq_mul_inv, mul_comm, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- the `B₀` term
  have hB0 : (if |posn P.labelVal y n - X0| ≤ H (posn P.labelVal y n) / 2
      then |cN P tw X0m y n| / 2 else 0) ≤ musqR n / 2 := by
    have := abs_cN_le ht hX.le hy (m := n) (by omega) (P := P) (tw := tw)
    split_ifs
    · linarith
    · have := musqR_nonneg n; linarith
  -- the steps: `d = 1` contributes `0`
  have hpd : n.properDivisors = insert 1 (n.divisors.filter (fun d => 1 < d ∧ d < n)) := by
    ext d
    simp only [Nat.mem_properDivisors, Finset.mem_insert, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hdn, hlt⟩
      rcases Nat.lt_or_ge d 2 with h | h
      · left
        interval_cases d
        · simp at hdn; omega
        · rfl
      · right; exact ⟨⟨hdn, hn0⟩, by omega, hlt⟩
    · rintro (rfl | ⟨⟨hdn, -⟩, -, hlt⟩)
      · exact ⟨one_dvd n, by omega⟩
      · exact ⟨hdn, hlt⟩
  have h1 : (1 : ℕ) ∉ n.divisors.filter (fun d => 1 < d ∧ d < n) := by simp
  rw [hpd, Finset.sum_insert h1]
  have hs1 : xbBstep P H tw X0m y X0 θ lam0 1 n = 0 := by unfold xbBstep; simp
  rw [hs1, zero_add]
  have hsteps : ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n),
      xbBstep P H tw X0m y X0 θ lam0 d n ≤
        ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ d < n), betaD ε lam0 d := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd' : d ∈ n.properDivisors := by
      rw [hpd]; exact Finset.mem_insert_of_mem hd
    exact xbBstep_le_betaD hP hp2 ht hlam hlam1 hy hn hrat hd'
  linarith

end KR.XB7

end
