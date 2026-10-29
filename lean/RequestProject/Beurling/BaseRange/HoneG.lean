module

public import RequestProject.Beurling.BaseRange.GEdgeRep
public import RequestProject.Beurling.BaseRange.CountDiff
public import RequestProject.Beurling.BaseRange.Step3Gen

/-!
# Lemma 7.3(d)(iii): one replacement with the non-smooth `g`

With `g(z) = ∑_{N,p} c_{N,p} 1[z ∈ I_{N,p}]/(κ z)` (`gEdge_rep`), the summand
`G(t) = 1[cut] g(u/(m t))/(m t)` of one replacement is `(1/(κu)) ∑_{N,p} c_{N,p} 1[t ∈ J_{N,p}]`
with intervals `J_{N,p}` in `t` (the `1/z` and `1/(mt)` cancel). The difference of the two prime
sums is then a sum of counting differences over intervals, each `≤ 2B σ_N (log x + 7)` with
`σ_N = (1+κ)u/(m N X₀)` (`count_convex_le`); summing over the window primes
(`#PW ≤ 1.0001 κX₀/Λ`) and over `N` (`∑ 1/N ≤ 1 + log x`) gives (`hone_g`)

  `|∑_P Ψ(a p, max(b, p)) - ∑_Q Ψ(a q, max(b, q))| ≤ 2.01 B (log x + 7)² D₀/(Λ a)`,

the input of the telescoping for `(K'_ℚ - K_pt) g` (proof of (d)(iii); the paper does this
step by a discrete Abel summation against the variation of `g`).
-/

@[expose] public section

open Real Finset BeurlingSystem
open scoped ArithmeticFunction.Moebius

namespace BaseRange

open Classical in
/-- **`g` as a sum of steps**, for every `z > 0` with `⌊z⌋ ≤ N_max`. -/
theorem gEdge_rep {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {z : ℝ} (hz : 0 < z) {Nmax : ℕ}
    (hN : ⌊z⌋₊ ≤ Nmax) :
    gEdge X0 z = ∑ N ∈ Icc 2 Nmax, ∑ p ∈ PW X0 (Construction.kappaParam X0),
      cNp N p * (if inI X0 (Construction.kappaParam X0) N p z then 1 else 0) /
        (Construction.kappaParam X0 * z) := by
  set κ := Construction.kappaParam (X0 : ℝ)
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hX3 : (3 : ℝ) ≤ X0 := by
    have := Real.add_one_le_exp (Real.log X0); rw [Real.exp_log hX0] at this; linarith
  have hκlt : κ < 1 := by
    have := kappa_le_tiny (X0 := (X0 : ℝ)) hX0 hX; linarith
  -- `inI` forces `N < z` and `z > X₀`
  have hinI : ∀ N p, 2 ≤ N → inI X0 κ N p z → (N : ℝ) < z ∧ (X0 : ℝ) < z := by
    intro N p hN2 h
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h1 := h.1.1
    rw [div_lt_div_iff₀ (by linarith) hN0] at h1
    have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    constructor
    · nlinarith
    · nlinarith
  have hzero : ∀ N ∈ Icc 2 Nmax, (¬ (N : ℝ) < z ∨ z < X0) →
      ∑ p ∈ PW X0 κ, cNp N p * (if inI X0 κ N p z then 1 else 0) / (κ * z) = 0 := by
    intro N hN' h
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]
    · simp
    · intro hI
      have := hinI N p (Finset.mem_Icc.mp hN').1 hI
      rcases h with h | h
      · exact h this.1
      · linarith [this.2]
  rcases lt_or_ge z X0 with hzX | hzX
  · rw [gEdge_zero_below hX0 hzX]
    symm; exact Finset.sum_eq_zero fun N hN' => hzero N hN' (Or.inr hzX)
  rw [gEdge_eq hX1 hzX, regroup (fun n => cQ X0 z n / n)]
  have hsub : Icc 2 ⌊z⌋₊ ⊆ Icc 2 Nmax := Finset.Icc_subset_Icc le_rfl hN
  rw [← Finset.sum_subset hsub (fun N hN' hN'' => hzero N hN' (Or.inl (fun h => hN'' (
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hN').1, Nat.le_floor h.le⟩))))]
  refine Finset.sum_congr rfl fun N hN' => ?_
  exact nterm_eq hX1 hκ0 hκlt hzX (Finset.mem_Icc.mp hN').1

/-- `∑_{N ∈ S} 1/N ≤ 1 + log(H/L)` for `S ⊆ (L, H]`, `L ≥ 1`. -/
lemma sum_inv_Ioc_le {L H : ℝ} (hL : 1 ≤ L) (S : Finset ℕ)
    (hS : ∀ N ∈ S, L < N ∧ (N : ℝ) ≤ H) (hLH : L ≤ H) :
    ∑ N ∈ S, (1 : ℝ) / N ≤ 1 + Real.log (H / L) := by
  set n1 := ⌊L⌋₊ + 1
  set n2 := ⌊H⌋₊
  have hsub : S ⊆ Icc n1 n2 := by
    intro N hN
    obtain ⟨h1, h2⟩ := hS N hN
    refine Finset.mem_Icc.mpr ⟨?_, Nat.le_floor h2⟩
    have := Nat.floor_lt (by linarith : (0 : ℝ) ≤ L) |>.mpr h1
    omega
  have hnn : ∀ N ∈ Icc n1 n2, N ∉ S → (0 : ℝ) ≤ 1 / N := fun N _ _ => by positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have hn1 : 1 ≤ n1 := by omega
  have hL0 : 0 < L := by linarith
  have hn1L : L < n1 := by
    have := Nat.lt_floor_add_one L; push_cast [n1]; linarith
  have hn2H : (n2 : ℝ) ≤ H := Nat.floor_le (by linarith)
  rcases Nat.lt_or_ge n2 n1 with h | h
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have : 0 ≤ Real.log (H / L) := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
    linarith
  -- `∑_{n₁}^{n₂} 1/N = H_{n₂} - H_{n₁ - 1} ≤ 1 + log n₂ - log n₁`
  have hsplit : ∑ N ∈ Icc 1 n2, (1 : ℝ) / N =
      ∑ N ∈ Icc 1 (n1 - 1), (1 : ℝ) / N + ∑ N ∈ Icc n1 n2, (1 : ℝ) / N := by
    have : Icc 1 n2 = Icc 1 (n1 - 1) ∪ Icc n1 n2 := by
      ext N; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_left]; intro N h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  have hH2 : ∑ N ∈ Icc 1 n2, (1 : ℝ) / N = harmonic n2 := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  have hH1 : ∑ N ∈ Icc 1 (n1 - 1), (1 : ℝ) / N = harmonic (n1 - 1) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  have hup := harmonic_le_one_add_log n2
  have hlow := log_add_one_le_harmonic (n1 - 1)
  rw [show n1 - 1 + 1 = n1 by omega] at hlow
  have hn10 : (0 : ℝ) < n1 := by exact_mod_cast (by omega : 0 < n1)
  have hn20 : (0 : ℝ) < n2 := lt_of_lt_of_le hn10 (by exact_mod_cast h)
  have hlog : Real.log n2 - Real.log n1 ≤ Real.log (H / L) := by
    rw [← Real.log_div hn20.ne' hn10.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hn10 hL0]; nlinarith
  linarith

/-- The window primes number at most `1.0001 κ X₀/Λ` (Lemma 7.3(a) at `q = X₀`). -/
lemma PW_card_le {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) (hH : HuxleyFrom X0) :
    ((PW X0 (Construction.kappaParam X0)).card : ℝ) ≤
      1.0001 * Construction.kappaParam X0 * X0 / Real.log X0 := by
  set κ := Construction.kappaParam (X0 : ℝ)
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  have hΛ : 0 < Real.log X0 := by linarith
  obtain ⟨-, h2⟩ := lemma_7_3_a hX hH (le_refl (X0 : ℝ))
  have h3 : Real.log X0 ^ (-3 : ℤ) ≤ 1 / 10 ^ 24 := zpow_neg3_le hX
  have hcard : ((PW X0 κ).card : ℝ) = newPrimeCount X0 X0 ((1 + κ) * X0) := by
    rw [newPrimeCount_eq_card' X0 (by positivity)]
    unfold PW
    congr 2
    ext p; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
  rw [hcard]
  unfold MAP at h2
  have hκX : 0 < κ * X0 := mul_pos hκ0 hX0
  rw [div_mul_eq_mul_div, div_le_iff₀ hκX] at h2
  rw [le_div_iff₀ hΛ]
  nlinarith

lemma chi_mono {B : ℕ} {z z' : ℝ} (h : LemmaM.chi tQ lv z B) (hzz : z ≤ z') :
    LemmaM.chi tQ lv z' B :=
  ⟨h.1, fun q hq => lt_of_lt_of_le (h.2 q hq) hzz⟩

/-! ### The kernel of `(K'_ℚ - K_pt) g` -/

/-- The summand `G(t, M) = 1[M t < u] g(u/t)/t` (strict filter, as in `K_pt` and `K'_ℚ`). -/
noncomputable def Gg (X0 : ℕ) (u t M : ℝ) : ℝ := if M * t < u then gEdge X0 (u / t) / t else 0

open Classical in
/-- **The summand at a large prime as a sum of steps**: for `p ≥ a₀ > 0`, `m > 0`. -/
lemma Gg_rep {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u x m a0 p b : ℝ} (hu : 0 < u)
    (hm : 0 < m) (ha0 : 0 < a0) (hp : a0 ≤ p) :
    (if m * p ≤ x then Gg X0 u (m * p) (max b p) else 0) =
      1 / (Construction.kappaParam X0 * u) *
        ∑ N ∈ Icc 2 ⌊u / (m * a0)⌋₊, ∑ q ∈ PW X0 (Construction.kappaParam X0),
          cNp N q * (if (m * p ≤ x ∧ max b p * (m * p) < u) ∧
            inI X0 (Construction.kappaParam X0) N q (u / (m * p)) then 1 else 0) := by
  set κ := Construction.kappaParam (X0 : ℝ)
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hp0 : 0 < p := lt_of_lt_of_le ha0 hp
  have hmp : 0 < m * p := mul_pos hm hp0
  have hz : 0 < u / (m * p) := div_pos hu hmp
  have hfl : ⌊u / (m * p)⌋₊ ≤ ⌊u / (m * a0)⌋₊ := by
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_left hu.le (mul_pos hm ha0)
    exact mul_le_mul_of_nonneg_left hp hm.le
  have hrep := gEdge_rep hX hz hfl
  have hzt : κ * (u / (m * p)) * (m * p) = κ * u := by field_simp
  by_cases hc : m * p ≤ x ∧ max b p * (m * p) < u
  · rw [if_pos hc.1]
    unfold Gg
    rw [if_pos hc.2, hrep, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hI : inI X0 κ N q (u / (m * p))
    · rw [if_pos hI, if_pos ⟨hc, hI⟩]
      have hκ' : κ ≠ 0 := hκ0.ne'
      field_simp
      rfl
    · rw [if_neg hI, if_neg (fun h => hI h.2)]; simp
  · have h0 : (if m * p ≤ x then Gg X0 u (m * p) (max b p) else 0) = 0 := by
      split_ifs with h1
      · unfold Gg; rw [if_neg (fun h2 => hc ⟨h1, h2⟩)]
      · rfl
    rw [h0]
    symm
    rw [mul_eq_zero]; right
    refine Finset.sum_eq_zero fun N _ => Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg (fun h => hc h.1)]; simp

open Classical in
/-- **The counting difference of one step `(N, q)`**: `0` unless
`u/(m t_top X₀) < N ≤ (1+κ)u/(m a₀ X₀)`, and then `≤ 2B σ_N (log x + 7)`,
`σ_N = (1+κ)u/(m N X₀)`. -/
lemma count_step {ι κ' : Type*} (vX : ι → ℝ) (vY : κ' → ℝ) (X : Finset ι) (Y : Finset κ')
    {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0) {u x m a0 b B : ℝ} (hu : 0 < u)
    (hm : 0 < m) (ha0e : Real.exp 1 ≤ a0) (ha0x : a0 ≤ x) (hB : 0 ≤ B)
    (hXa : ∀ i ∈ X, a0 < vX i ∧ vX i ≤ x) (hYa : ∀ i ∈ Y, a0 < vY i ∧ vY i ≤ x)
    (hΔ : ∀ s ∈ Set.Icc a0 x, |thetaF vX X s - thetaF vY Y s| ≤ B * s * (Real.log s + 1) ^ 2)
    (N q : ℕ) (hN : 2 ≤ N) :
    |((X.filter (fun i => (m * vX i ≤ x ∧ max b (vX i) * (m * vX i) < u) ∧
          inI X0 (Construction.kappaParam X0) N q (u / (m * vX i)))).card : ℝ) -
        (Y.filter (fun i => (m * vY i ≤ x ∧ max b (vY i) * (m * vY i) < u) ∧
          inI X0 (Construction.kappaParam X0) N q (u / (m * vY i)))).card| ≤
      if u / (m * min x (x / m) * X0) < N ∧
          (N : ℝ) ≤ (1 + Construction.kappaParam X0) * u / (m * a0 * X0) then
        2 * B * ((1 + Construction.kappaParam X0) * u / (m * N * X0)) * (Real.log x + 7)
      else 0 := by
  set κ := Construction.kappaParam (X0 : ℝ)
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hX0 : (0 : ℝ) < X0 := by linarith [one_lt_of_log hX]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a0 := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; linarith
  set F : ℝ → Prop := fun t => (m * t ≤ x ∧ max b t * (m * t) < u) ∧
    inI X0 κ N q (u / (m * t)) with hF
  set σ := (1 + κ) * u / (m * N * X0) with hσ
  have hRHS0 : 0 ≤ 2 * B * σ * (Real.log x + 7) := by
    have : 0 ≤ σ := by positivity
    have : 0 ≤ Real.log x + 7 := by linarith
    positivity
  -- an atom in the step gives the range of `N` and `t < σ`
  have hatom : ∀ t, a0 < t → t ≤ x → F t →
      t < σ ∧ u / (m * min x (x / m) * X0) < N ∧ (N : ℝ) ≤ (1 + κ) * u / (m * a0 * X0) := by
    intro t ht1 ht2 hFt
    have ht0 : 0 < t := by linarith
    obtain ⟨⟨hc1, -⟩, ⟨hI1, hI2⟩, -, -⟩ := hFt
    have hmt : 0 < m * t := mul_pos hm ht0
    -- `X₀/(1+κ) < u/(m t N)`
    have hlt : t < σ := by
      rw [div_div, div_lt_div_iff₀ (by linarith) (mul_pos hmt hN0)] at hI1
      rw [hσ, lt_div_iff₀ (by positivity)]
      nlinarith
    refine ⟨hlt, ?_, ?_⟩
    · have htt : t ≤ min x (x / m) := le_min ht2 (by rw [le_div_iff₀ hm]; linarith)
      have htt0 : 0 < min x (x / m) := lt_of_lt_of_le ht0 htt
      rw [div_lt_iff₀ (by positivity)]
      rw [div_div, div_lt_iff₀ (mul_pos hmt hN0)] at hI2
      have : m * t ≤ m * min x (x / m) := mul_le_mul_of_nonneg_left htt hm.le
      nlinarith
    · have : a0 < σ := lt_trans ht1 hlt
      rw [hσ, lt_div_iff₀ (by positivity)] at this
      rw [le_div_iff₀ (by positivity)]
      nlinarith
  by_cases hex : (∃ i ∈ X, F (vX i)) ∨ (∃ i ∈ Y, F (vY i))
  · -- some atom: the counting lemma
    have hrange : u / (m * min x (x / m) * X0) < N ∧
        (N : ℝ) ≤ (1 + κ) * u / (m * a0 * X0) ∧ a0 < σ := by
      rcases hex with ⟨i, hi, hFi⟩ | ⟨i, hi, hFi⟩
      · obtain ⟨h1, h2, h3⟩ := hatom _ (hXa i hi).1 (hXa i hi).2 hFi
        exact ⟨h2, h3, lt_trans (hXa i hi).1 h1⟩
      · obtain ⟨h1, h2, h3⟩ := hatom _ (hYa i hi).1 (hYa i hi).2 hFi
        exact ⟨h2, h3, lt_trans (hYa i hi).1 h1⟩
    rw [if_pos ⟨hrange.1, hrange.2.1⟩]
    set smax := min x σ
    have has : a0 ≤ smax := le_min ha0x hrange.2.2.le
    set Dn : ℝ → Prop := fun t => t ≤ 0 ∨ (t ≤ x ∧ (m * t ≤ x ∧ max b t * (m * t) < u) ∧
      (X0 : ℝ) / (1 + κ) < u / (m * t) / N ∧ (q : ℝ) ≤ (1 + κ) * (u / (m * t) / N) ∧
        LemmaM.chi tQ lv (u / (m * t)) (Nbig N q))
    set Up : ℝ → Prop := fun t => 0 < t ∧ u / (m * t) / N < X0
    have hDn : ∀ t t', t' ≤ t → Dn t → Dn t' := by
      intro t t' htt h
      rcases le_or_gt t' 0 with h' | h'
      · exact Or.inl h'
      right
      have ht0 : 0 < t := lt_of_lt_of_le h' htt
      rcases h with h | ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩
      · linarith
      have hz : u / (m * t) ≤ u / (m * t') :=
        div_le_div_of_nonneg_left hu.le (mul_pos hm h') (mul_le_mul_of_nonneg_left htt hm.le)
      have hzN : u / (m * t) / N ≤ u / (m * t') / N := div_le_div_of_nonneg_right hz hN0.le
      refine ⟨htt.trans h1, ⟨(mul_le_mul_of_nonneg_left htt hm.le).trans h2, ?_⟩, by linarith,
        by nlinarith, chi_mono h6 hz⟩
      have hmax : max b t' ≤ max b t := max_le_max le_rfl htt
      have hm1 : 0 ≤ max b t' := le_trans h'.le (le_max_right _ _)
      calc max b t' * (m * t') ≤ max b t * (m * t) :=
            mul_le_mul hmax (mul_le_mul_of_nonneg_left htt hm.le) (by positivity)
              (le_trans ht0.le (le_max_right _ _))
        _ < u := h3
    have hUp : ∀ t t', t ≤ t' → Up t → Up t' := by
      intro t t' htt ⟨h1, h2⟩
      have h' : 0 < t' := lt_of_lt_of_le h1 htt
      refine ⟨h', lt_of_le_of_lt ?_ h2⟩
      apply div_le_div_of_nonneg_right _ hN0.le
      exact div_le_div_of_nonneg_left hu.le (mul_pos hm h1) (mul_le_mul_of_nonneg_left htt hm.le)
    have hsmax : ∀ t, a0 < t → Dn t → t ≤ smax := by
      intro t ht h
      rcases h with h | ⟨h1, -, h4, -, -⟩
      · linarith
      have ht0 : 0 < t := by linarith
      have hmt : 0 < m * t := mul_pos hm ht0
      refine le_min h1 ?_
      rw [div_div, div_lt_div_iff₀ (by linarith) (mul_pos hmt hN0)] at h4
      rw [hσ, le_div_iff₀ (by positivity)]
      nlinarith
    have hXa' : ∀ i ∈ X, a0 < vX i := fun i hi => (hXa i hi).1
    have hYa' : ∀ i ∈ Y, a0 < vY i := fun i hi => (hYa i hi).1
    have hc := count_convex_le vX vY X Y ha0e has hXa' hYa' hB
      (fun t ht => hΔ t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩) Dn Up hDn hUp hsmax
    have hiff : ∀ t, 0 < t → t ≤ x → (Dn t ∧ Up t ↔ F t) := by
      intro t ht0 htx
      simp only [Dn, Up, F, inI, InEdge]
      constructor
      · rintro ⟨h | ⟨-, h2, h4, h5, h6⟩, -, h7⟩
        · linarith
        · exact ⟨h2, ⟨h4, h7⟩, h5, h6⟩
      · rintro ⟨h2, ⟨h4, h7⟩, h5, h6⟩
        exact ⟨Or.inr ⟨htx, h2, h4, h5, h6⟩, ht0, h7⟩
    have eX : X.filter (fun i => Dn (vX i) ∧ Up (vX i)) = X.filter (fun i => F (vX i)) :=
      Finset.filter_congr fun i hi => hiff _ (by linarith [(hXa i hi).1]) (hXa i hi).2
    have eY : Y.filter (fun i => Dn (vY i) ∧ Up (vY i)) = Y.filter (fun i => F (vY i)) :=
      Finset.filter_congr fun i hi => hiff _ (by linarith [(hYa i hi).1]) (hYa i hi).2
    rw [eX, eY] at hc
    refine hc.trans ?_
    have hsm1 : smax ≤ σ := min_le_right _ _
    have hsm2 : Real.log smax ≤ Real.log x := Real.log_le_log (by linarith) (min_le_left _ _)
    have hsm0 : 0 ≤ Real.log smax + 7 := by
      have : 0 ≤ Real.log smax := Real.log_nonneg (by linarith); linarith
    calc 2 * (B * smax * (Real.log smax + 7)) ≤ 2 * (B * σ * (Real.log x + 7)) := by
          gcongr
      _ = 2 * B * σ * (Real.log x + 7) := by ring
  · -- no atom: both counts vanish
    push_neg at hex
    have h1 : X.filter (fun i => F (vX i)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun i hi => hex.1 i hi
    have h2 : Y.filter (fun i => F (vY i)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun i hi => hex.2 i hi
    change |((X.filter (fun i => F (vX i))).card : ℝ) - (Y.filter (fun i => F (vY i))).card| ≤ _
    rw [h1, h2]
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, abs_zero]
    split_ifs
    · exact hRHS0
    · exact le_rfl

open Classical in
/-- **One replacement with `g`** (the hypothesis of `Tele.tele` for `(K'_ℚ - K_pt) g`). -/
theorem hone_g {P Q : BeurlingSystem} {J1 : ℕ} {X0 : ℕ} (hX : 10 ^ 8 ≤ Real.log X0)
    (hH : HuxleyFrom X0) {u X0m B D0 : ℝ} (hu : (X0 : ℝ) ≤ u) (hXm : Real.exp 1 ≤ X0m / 2)
    (hB : 0 ≤ B)
    (hlP : ∀ j ∈ S3.Lg P J1 (u / X0), X0m ≤ P.p j) (hlQ : ∀ j ∈ S3.Lg Q J1 (u / X0), X0m ≤ Q.p j)
    (hΔ : ∀ s ∈ Set.Icc (X0m / 2) (u / X0),
      |thetaF P.p (S3.Lg P J1 (u / X0)) s - thetaF Q.p (S3.Lg Q J1 (u / X0)) s| ≤
        B * s * (Real.log s + 1) ^ 2)
    (hD : ∑ d ∈ S3.Drig P J1 (u / X0), 1 / P.val d ≤ D0) :
    ∀ a : ℝ, 0 < a → ∀ b : ℝ,
      |∑ j ∈ S3.Lg P J1 (u / X0), S3.PsiD P J1 (u / X0) (Gg X0 u) (a * P.p j) (max b (P.p j)) -
        ∑ j ∈ S3.Lg Q J1 (u / X0), S3.PsiD P J1 (u / X0) (Gg X0 u) (a * Q.p j) (max b (Q.p j))| ≤
      2.01 * B * (Real.log (u / X0) + 7) ^ 2 * D0 / Real.log X0 / a := by
  intro a ha b
  set x := u / (X0 : ℝ) with hx
  set κ := Construction.kappaParam (X0 : ℝ) with hκdef
  set a0 := X0m / 2 with ha0def
  obtain ⟨hκ0, -⟩ := BModel.kappa_facts hX
  have hκs : κ ≤ 1 / 10 ^ 21 := kappa_le_tiny (by linarith [one_lt_of_log hX]) hX
  have hX1 := one_lt_of_log hX
  have hX0 : (0 : ℝ) < X0 := by linarith
  have hΛ : 0 < Real.log X0 := by linarith
  have hu0 : 0 < u := by linarith
  have he : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a0 := by linarith
  have hD0 : 0 ≤ D0 :=
    (Finset.sum_nonneg fun d _ => (one_div_pos.mpr (P.val_pos d)).le).trans hD
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hX0]; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hRHS0 : 0 ≤ 2.01 * B * (Real.log x + 7) ^ 2 * D0 / Real.log X0 / a := by positivity
  rcases lt_or_ge x a0 with hxa | hxa
  · -- no large primes
    have hP : S3.Lg P J1 x = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by
      have h1 := hlP j hj
      have h2 := P.mem_primesLe.mp (Finset.mem_filter.mp hj).1
      linarith
    have hQ : S3.Lg Q J1 x = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by
      have h1 := hlQ j hj
      have h2 := Q.mem_primesLe.mp (Finset.mem_filter.mp hj).1
      linarith
    rw [hP, hQ]; simpa using hRHS0
  -- the atoms
  have hXa : ∀ j ∈ S3.Lg P J1 x, a0 < P.p j ∧ P.p j ≤ x := fun j hj =>
    ⟨by linarith [hlP j hj], P.mem_primesLe.mp (Finset.mem_filter.mp hj).1⟩
  have hYa : ∀ j ∈ S3.Lg Q J1 x, a0 < Q.p j ∧ Q.p j ≤ x := fun j hj =>
    ⟨by linarith [hlQ j hj], Q.mem_primesLe.mp (Finset.mem_filter.mp hj).1⟩
  -- per rigid part
  have hper : ∀ d ∈ S3.Drig P J1 x,
      |∑ j ∈ S3.Lg P J1 x, (if P.val d * (a * P.p j) ≤ x then
          Gg X0 u (P.val d * (a * P.p j)) (max b (P.p j)) else 0) -
        ∑ j ∈ S3.Lg Q J1 x, (if P.val d * (a * Q.p j) ≤ x then
          Gg X0 u (P.val d * (a * Q.p j)) (max b (Q.p j)) else 0)| ≤
      2.01 * B * (Real.log x + 7) ^ 2 / Real.log X0 / a * (1 / P.val d) := by
    intro d _
    set m := P.val d * a with hmdef
    have hm : 0 < m := mul_pos (P.val_pos d) ha
    have e1 : ∀ p : ℝ, P.val d * (a * p) = m * p := fun p => by ring
    simp only [e1]
    set Nmax := ⌊u / (m * a0)⌋₊
    set F : ℕ → ℕ → ℝ → Prop := fun N q t => (m * t ≤ x ∧ max b t * (m * t) < u) ∧
      inI X0 κ N q (u / (m * t))
    -- the sums as step counts
    have hsumX : ∀ (S : BeurlingSystem) (L : Finset ℕ), (∀ j ∈ L, a0 < S.p j) →
        ∑ j ∈ L, (if m * S.p j ≤ x then Gg X0 u (m * S.p j) (max b (S.p j)) else 0) =
          1 / (κ * u) * ∑ N ∈ Icc 2 Nmax, ∑ q ∈ PW X0 κ,
            cNp N q * ((L.filter (fun j => F N q (S.p j))).card : ℝ) := by
      intro S L hL
      rw [Finset.sum_congr rfl (fun j hj => Gg_rep hX hu0 hm ha0 (hL j hj).le)]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.mul_sum, Finset.sum_boole]
    rw [hsumX P _ (fun j hj => (hXa j hj).1), hsumX Q _ (fun j hj => (hYa j hj).1), ← mul_sub,
      ← Finset.sum_sub_distrib]
    -- the step bounds
    set Lo := u / (m * min x (x / m) * X0)
    set Hi := (1 + κ) * u / (m * a0 * X0)
    have hstep : ∀ N ∈ Icc 2 Nmax, |∑ q ∈ PW X0 κ, cNp N q *
        ((((S3.Lg P J1 x).filter (fun j => F N q (P.p j))).card : ℝ)) -
        ∑ q ∈ PW X0 κ, cNp N q * ((((S3.Lg Q J1 x).filter (fun j => F N q (Q.p j))).card : ℝ))| ≤
        (PW X0 κ).card * (if Lo < N ∧ (N : ℝ) ≤ Hi then
          2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) := by
      intro N hN
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [← mul_sub, abs_mul]
      have hc := count_step P.p Q.p (S3.Lg P J1 x) (S3.Lg Q J1 x) hX (b := b) hu0 hm
        (by linarith : Real.exp 1 ≤ a0) hxa hB hXa hYa hΔ N q (Finset.mem_Icc.mp hN).1
      have h0 : 0 ≤ (if Lo < N ∧ (N : ℝ) ≤ Hi then
          2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) := by
        have hN2 := (Finset.mem_Icc.mp hN).1
        have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        split_ifs
        · positivity
        · exact le_rfl
      calc |cNp N q| * |((((S3.Lg P J1 x).filter (fun j => F N q (P.p j))).card : ℝ)) -
            (((S3.Lg Q J1 x).filter (fun j => F N q (Q.p j))).card : ℝ)|
          ≤ 1 * (if Lo < N ∧ (N : ℝ) ≤ Hi then
              2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) :=
            mul_le_mul (abs_cNp_le N q) hc (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    -- the sum over `N`
    have hκu : 0 < κ * u := mul_pos hκ0 hu0
    have htt0 : 0 < min x (x / m) := lt_min (by linarith) (div_pos (by linarith) hm)
    have hLo : 1 ≤ Lo := by
      have h1 : m * min x (x / m) ≤ x := by
        calc m * min x (x / m) ≤ m * (x / m) := mul_le_mul_of_nonneg_left (min_le_right _ _)
              hm.le
          _ = x := by field_simp
      show 1 ≤ u / (m * min x (x / m) * X0)
      rw [le_div_iff₀ (by positivity), one_mul]
      have : x * X0 = u := by rw [hx]; field_simp
      nlinarith
    have hHiLo : Hi / Lo ≤ x := by
      have e : Hi / Lo = (1 + κ) * min x (x / m) / a0 := by
        show (1 + κ) * u / (m * a0 * X0) / (u / (m * min x (x / m) * X0)) = _
        field_simp
      rw [e, div_le_iff₀ ha0]
      have h1 : min x (x / m) ≤ x := min_le_left _ _
      have h2 : (1 + κ) ≤ a0 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith
    have hsumN : ∑ N ∈ Icc 2 Nmax, (if Lo < N ∧ (N : ℝ) ≤ Hi then
        2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) ≤
        2 * B * (Real.log x + 7) * ((1 + κ) * u / (m * X0)) * (1 + Real.log x) := by
      rw [← Finset.sum_filter]
      have e : ∀ N ∈ (Icc 2 Nmax).filter (fun N : ℕ => Lo < N ∧ (N : ℝ) ≤ Hi),
          2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) =
            2 * B * (Real.log x + 7) * ((1 + κ) * u / (m * X0)) * (1 / N) := by
        intro N hN
        have : (0 : ℝ) < N := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1).1
          exact_mod_cast (by omega : 0 < N)
        field_simp
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases ((Icc 2 Nmax).filter (fun N : ℕ => Lo < N ∧ (N : ℝ) ≤ Hi)).eq_empty_or_nonempty
        with hE | hE
      · rw [hE, Finset.sum_empty]; linarith
      obtain ⟨N0, hN0⟩ := hE
      have hN0' := (Finset.mem_filter.mp hN0).2
      have hLH : Lo ≤ Hi := by linarith [hN0'.1, hN0'.2]
      refine (sum_inv_Ioc_le hLo _ (fun N hN => (Finset.mem_filter.mp hN).2) hLH).trans ?_
      have hLo0 : 0 < Lo := by linarith
      have : Real.log (Hi / Lo) ≤ Real.log x := by
        apply Real.log_le_log (div_pos (by linarith) hLo0) hHiLo
      linarith
    have hPW := PW_card_le hX hH
    have hPW0 : (0 : ℝ) ≤ (PW X0 κ).card := Nat.cast_nonneg _
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (κ * u))]
    calc 1 / (κ * u) * |∑ N ∈ Icc 2 Nmax, (∑ q ∈ PW X0 κ, cNp N q *
          ((((S3.Lg P J1 x).filter (fun j => F N q (P.p j))).card : ℝ)) -
          ∑ q ∈ PW X0 κ, cNp N q *
            ((((S3.Lg Q J1 x).filter (fun j => F N q (Q.p j))).card : ℝ)))|
        ≤ 1 / (κ * u) * ∑ N ∈ Icc 2 Nmax, (PW X0 κ).card * (if Lo < N ∧ (N : ℝ) ≤ Hi then
            2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)
      _ = 1 / (κ * u) * ((PW X0 κ).card * ∑ N ∈ Icc 2 Nmax, (if Lo < N ∧ (N : ℝ) ≤ Hi then
            2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0)) := by
          congr 1; rw [Finset.mul_sum]
      _ ≤ 1 / (κ * u) * (1.0001 * κ * X0 / Real.log X0 *
            (2 * B * (Real.log x + 7) * ((1 + κ) * u / (m * X0)) * (1 + Real.log x))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h0 : 0 ≤ ∑ N ∈ Icc 2 Nmax, (if Lo < N ∧ (N : ℝ) ≤ Hi then
              2 * B * ((1 + κ) * u / (m * N * X0)) * (Real.log x + 7) else 0) := by
            refine Finset.sum_nonneg fun N hN => ?_
            have hN2 := (Finset.mem_Icc.mp hN).1
            have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
            split_ifs
            · positivity
            · exact le_rfl
          exact mul_le_mul hPW hsumN h0 (by positivity)
      _ = 2.0002 * (1 + κ) * B * (Real.log x + 7) * (1 + Real.log x) / Real.log X0 / m := by
          have hκne : κ ≠ 0 := hκ0.ne'
          field_simp
          ring
      _ ≤ 2.01 * B * (Real.log x + 7) ^ 2 / Real.log X0 / a * (1 / P.val d) := by
          have hv := P.val_pos d
          rw [hmdef]
          have h1 : 2.0002 * (1 + κ) ≤ 2.01 := by nlinarith
          have h2 : (1 + Real.log x) ≤ Real.log x + 7 := by linarith
          have h3 : 0 ≤ B * (Real.log x + 7) := by positivity
          have : 2.0002 * (1 + κ) * B * (Real.log x + 7) * (1 + Real.log x) ≤
              2.01 * B * (Real.log x + 7) ^ 2 := by
            calc 2.0002 * (1 + κ) * B * (Real.log x + 7) * (1 + Real.log x)
                = (2.0002 * (1 + κ)) * (B * (Real.log x + 7)) * (1 + Real.log x) := by ring
              _ ≤ 2.01 * (B * (Real.log x + 7)) * (Real.log x + 7) := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 (by linarith)
                    (by positivity)
              _ = 2.01 * B * (Real.log x + 7) ^ 2 := by ring
          calc 2.0002 * (1 + κ) * B * (Real.log x + 7) * (1 + Real.log x) / Real.log X0 /
                (P.val d * a) ≤ 2.01 * B * (Real.log x + 7) ^ 2 / Real.log X0 / (P.val d * a) := by
                gcongr
            _ = _ := by field_simp
  -- assemble over the rigid parts
  unfold S3.PsiD
  rw [Finset.sum_comm, Finset.sum_comm (s := S3.Lg Q J1 x), ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  calc 2.01 * B * (Real.log x + 7) ^ 2 / Real.log X0 / a * ∑ d ∈ S3.Drig P J1 x, 1 / P.val d
      ≤ 2.01 * B * (Real.log x + 7) ^ 2 / Real.log X0 / a * D0 :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring
