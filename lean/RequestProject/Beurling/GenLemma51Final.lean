module

public import RequestProject.Beurling.GenLemma51

/-!
# Lemma 5.1(iii), (iv) for a Beurling system satisfying (HBS), and the full statement

* `HBS.Sp_sub_log_mem` : (iii) `-1.77 ≤ S_{p,P}(x) - log x ≤ 0.43`;
* `HBS.mertens_iv` : (iv) `|∑_{y<p≤x} 1/p - log(log x/log y)| ≤ 2.20/log y`;
* `BeurlingSystem.lemma_5_1` : **Lemma 5.1** (i)–(iv) for every `1 ≤ x ≤ z`.

For (iii), `S_P - S_{p,P}` is the contribution of the prime powers `p^k`, `k ≥ 2`. The primes
below `X₀⁻` are the rational primes and contribute at most `0.75537` (`finite_checks.py`, line 6);
the primes `p ≥ X₀⁻` contribute at most `2.84 · 2 · 2^{-23}`, by the dyadic blocks and (i).
-/

@[expose] public section

open Finset

namespace BeurlingSystem

variable (P : BeurlingSystem)

/-- `S_P(x) = S_{p,P}(x) + ∑_{p^{k+1} ≤ x, k ≥ 1} log p / p^{k+1}`. -/
lemma mertensS_eq_Sp_add (x : ℝ) :
    P.mertensS x = P.Sp x + ∑ jk ∈ (P.pps x).filter (fun jk => 1 ≤ jk.2),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) := by
  unfold mertensS
  rw [← Finset.sum_filter_not_add_sum_filter (P.pps x) (fun jk => 1 ≤ jk.2)]
  congr 1
  unfold Sp
  symm
  refine Finset.sum_nbij' (fun j => (j, 0)) (fun jk => jk.1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_primesLe] at hj
    simp only [mem_filter, mem_pps, zero_add, pow_one, not_le]
    exact ⟨hj, by omega⟩
  · intro jk hjk
    simp only [mem_filter, mem_pps, not_le] at hjk
    simp only [mem_primesLe]
    have : jk.2 = 0 := by omega
    rw [this, zero_add, pow_one] at hjk
    exact hjk.1
  · intro j _; rfl
  · intro jk hjk
    simp only [mem_filter, not_le] at hjk
    exact Prod.ext rfl (by simp only; omega)
  · intro j _; simp

namespace HBS

variable {P} {X0m z η1 η2 : ℝ} {ε1 : ℝ → ℝ}

lemma p_ge_two (h : P.HBS X0m z η1 η2 ε1) {j : ℕ} (hj : P.p j ≤ z) : 2 ≤ P.p j := by
  rcases lt_or_ge (P.p j) X0m with hlt | hge
  · rw [h.ident hlt hj j (Or.inl le_rfl)]
    exact_mod_cast (qp_prime j).two_le
  · linarith [h.X0m_ge]

/-- The prime powers `p^{k+1}`, `k ≥ 1`, of a prime `p ≥ 2` contribute at most
`log p / (p (p-1))`. -/
lemma fiber_le (j : ℕ) (hp : 2 ≤ P.p j) (F : Finset (ℕ × ℕ))
    (hF : ∀ jk ∈ F, jk.1 = j ∧ 1 ≤ jk.2) :
    ∑ jk ∈ F, Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) ≤
      Real.log (P.p j) / (P.p j * (P.p j - 1)) := by
  have hl : 0 ≤ Real.log (P.p j) := Real.log_nonneg (by linarith)
  have e : ∑ jk ∈ F, Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) =
      Real.log (P.p j) * ∑ k ∈ F.image (fun jk => jk.2 + 1), 1 / P.p j ^ k := by
    rw [Finset.sum_image, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun jk hjk => ?_
      rw [(hF jk hjk).1]; ring
    · intro a ha b hb hab
      simp only at hab
      exact Prod.ext ((hF a ha).1.trans (hF b hb).1.symm) (by omega)
  rw [e]
  set M := (F.image (fun jk => jk.2 + 1)).sup id
  have hsub : F.image (fun jk => jk.2 + 1) ⊆ Icc 2 M := by
    intro k hk
    rw [mem_Icc]
    refine ⟨?_, Finset.le_sup (f := id) hk⟩
    obtain ⟨jk, hjk, rfl⟩ := mem_image.mp hk
    have := (hF jk hjk).2; omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => by positivity : ∀ k ∈ Icc 2 M, k ∉ F.image (fun jk => jk.2 + 1) →
      0 ≤ 1 / P.p j ^ k)
  have h2 := Lemma51Nat.geom_tail_le hp M
  have h3 := h1.trans h2
  have := mul_le_mul_of_nonneg_left h3 hl
  calc _ ≤ Real.log (P.p j) * (1 / (P.p j * (P.p j - 1))) := this
    _ = _ := by ring

/-- `0 ≤ S_P(x) - S_{p,P}(x) ≤ 0.7554` for `X₀⁻ ≤ x ≤ z`. -/
lemma rest_le (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hX : X0m ≤ x) (hxz : x ≤ z) :
    ∑ jk ∈ (P.pps x).filter (fun jk => 1 ≤ jk.2),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) ≤ 0.7554 := by
  have hX7 := h.X0m_ge
  have hx0 : 0 < x := by linarith
  set R := (P.pps x).filter (fun jk => 1 ≤ jk.2)
  set T := (P.primesLe x).filter (fun j => P.p j ^ 2 ≤ x)
  have hmaps : ∀ jk ∈ R, jk.1 ∈ T := by
    intro jk hjk
    simp only [R, mem_filter, mem_pps] at hjk
    simp only [T, mem_filter, mem_primesLe]
    have h1 := P.one_lt jk.1
    have hsq : P.p jk.1 ^ 2 ≤ P.p jk.1 ^ (jk.2 + 1) := pow_le_pow_right₀ h1.le (by omega)
    exact ⟨by nlinarith, hsq.trans hjk.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hTx : ∀ j ∈ T, P.p j ≤ x := fun j hj => by
    simp only [T, mem_filter, mem_primesLe] at hj; exact hj.1
  have hT2 : ∀ j ∈ T, 2 ≤ P.p j := fun j hj => h.p_ge_two ((hTx j hj).trans hxz)
  have h1 : ∑ j ∈ T, ∑ jk ∈ R.filter (fun jk => jk.1 = j),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) ≤
      ∑ j ∈ T, Real.log (P.p j) / (P.p j * (P.p j - 1)) := by
    refine Finset.sum_le_sum fun j hj => fiber_le j (hT2 j hj) _ fun jk hjk => ?_
    simp only [R, mem_filter] at hjk
    exact ⟨hjk.2, hjk.1.2⟩
  refine h1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not T (fun j => P.p j < X0m)]
  -- the rational primes
  have hsmall : ∑ j ∈ T.filter (fun j => P.p j < X0m),
      Real.log (P.p j) / (P.p j * (P.p j - 1)) ≤ 0.75537 := by
    have hq : ∀ j ∈ T.filter (fun j => P.p j < X0m), P.p j = qp j := by
      intro j hj
      rw [mem_filter] at hj
      exact h.ident hj.2 ((hTx j hj.1).trans hxz) j (Or.inl le_rfl)
    rw [Finset.sum_congr rfl (fun j hj => by rw [hq j hj])]
    rw [← Finset.sum_image (f := fun r : ℕ => Real.log (r : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)))
      (fun a _ b _ hab => qp_injective hab)]
    refine le_trans ?_ (Lemma51Nat.primePowerConst_le ⌊x⌋₊)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
      have hjx : (qp j : ℝ) ≤ x := by rw [← hq j hj]; exact hTx j (mem_filter.mp hj).1
      simp only [mem_filter, mem_Ioc]
      exact ⟨⟨(qp_prime j).pos, Nat.le_floor hjx⟩, qp_prime j⟩
    · intro r hr _
      simp only [mem_filter] at hr
      have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.2.two_le
      have : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by linarith)
      apply div_nonneg this; nlinarith
  -- the primes `p ≥ X₀⁻`
  set s := T.filter (fun j => ¬ P.p j < X0m)
  have hsX : ∀ j ∈ s, X0m ≤ P.p j := fun j hj => by
    simp only [s, mem_filter, not_lt] at hj; exact hj.2
  have hsT : ∀ j ∈ s, j ∈ T := fun j hj => (mem_filter.mp hj).1
  have hstep : ∑ j ∈ s, Real.log (P.p j) / (P.p j * (P.p j - 1)) ≤
      ∑ j ∈ s, Real.log (P.p j) * (2 / P.p j ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hp := hT2 j (hsT j hj)
    have hl : 0 ≤ Real.log (P.p j) := Real.log_nonneg (by linarith)
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hl
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  set K := s.image (fun j => GenDyadic.dIdx (P.p j))
  have hblocks := GenDyadic.sum_le_blocks s P.p (fun j => Real.log (P.p j))
    (fun j => 2 / P.p j ^ 2) (fun m => 1.42 * 2 ^ m) (fun m => 2 / ((2 : ℝ) ^ m) ^ 2)
    (fun j _ => P.log_p_nonneg j) ?hB ?hG (fun m _ => by positivity)
  case hB =>
    intro m hm
    obtain ⟨j0, hj0, hm0⟩ := mem_image.mp hm
    have hspec0 := GenDyadic.dIdx_spec (P.one_lt j0)
    rw [hm0] at hspec0
    have hp0 := hT2 j0 (hsT j0 hj0)
    have hp0x : P.p j0 ^ 2 ≤ x := by
      have := hsT j0 hj0; simp only [T, mem_filter] at this; exact this.2
    have hpow : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
    have hle : (2 : ℝ) ^ (m + 1) ≤ z := by
      have : (2 : ℝ) ^ (m + 1) ≤ 2 * P.p j0 := by
        rw [pow_succ]; linarith [hspec0.1]
      nlinarith
    have h1 := h.psi_sub_psi_half_le hpow hle
    have h2 : (2 : ℝ) ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; ring
    rw [h2] at h1
    set F := s.filter (fun j => GenDyadic.dIdx (P.p j) = m)
    have e : ∑ j ∈ F, Real.log (P.p j) =
        ∑ jk ∈ F.image (fun j => (j, 0)), Real.log (P.p jk.1) := by
      rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    have h3 := sum_le_psi_sub (P := P) (a := 2 ^ m) (b := 2 ^ (m + 1)) (by
        rw [pow_succ]; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) m])
      (F.image (fun j => (j, 0))) (by
        intro jk hjk
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hjk
        rw [mem_filter] at hj
        have := GenDyadic.dIdx_spec (P.one_lt j)
        rw [hj.2] at this
        simpa using this)
    rw [e]
    calc _ ≤ P.psi (2 ^ (m + 1)) - P.psi (2 ^ m) := h3
      _ ≤ 0.71 * 2 ^ (m + 1) := h1
      _ = 1.42 * 2 ^ m := by rw [pow_succ]; ring
  case hG =>
    intro j hj
    have hspec := GenDyadic.dIdx_spec (P.one_lt j)
    have h0 : (0 : ℝ) < 2 ^ GenDyadic.dIdx (P.p j) := by positivity
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ h0.le hspec.1.le 2
  have hK : ∀ m ∈ K, 23 ≤ m := by
    intro m hm
    obtain ⟨j0, hj0, hm0⟩ := mem_image.mp hm
    have hspec0 := GenDyadic.dIdx_spec (P.one_lt j0)
    rw [hm0] at hspec0
    have := hsX j0 hj0
    by_contra hc; push_neg at hc
    have h23 : (2 : ℝ) ^ (m + 1) ≤ 2 ^ 23 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h23
    linarith [hspec0.2]
  have hgeo := GenDyadic.sum_half_pow_le K 23 hK
  have e2 : ∑ m ∈ K, 1.42 * (2 : ℝ) ^ m * (2 / ((2 : ℝ) ^ m) ^ 2) =
      2.84 * ∑ m ∈ K, (1 / 2 : ℝ) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : (2 : ℝ) ^ m ≠ 0 := by positivity
    rw [one_div_pow]
    field_simp
    ring
  have hlarge : ∑ j ∈ s, Real.log (P.p j) / (P.p j * (P.p j - 1)) ≤
      2.84 * (2 * (1 / 2) ^ 23) := by
    refine hstep.trans (hblocks.trans ?_)
    rw [e2]
    linarith
  norm_num at hlarge
  linarith

/-- **Lemma 5.1(iii)**: `-1.77 ≤ S_{p,P}(x) - log x ≤ 0.43` for `1 ≤ x ≤ z`. -/
theorem Sp_sub_log_mem (h : P.HBS X0m z η1 η2 ε1) {x : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z) :
    -1.77 ≤ P.Sp x - Real.log x ∧ P.Sp x - Real.log x ≤ 0.43 := by
  rcases lt_or_ge x X0m with hlt | hge
  · rw [P.Sp_eq_nat (h.ident hlt hxz)]
    exact Lemma51Nat.lemma_5_1_iii_nat_all hx
  have h1 := h.mertensS_sub_log_mem hx hxz
  have h2 := P.mertensS_eq_Sp_add x
  have h3 := h.rest_le hge hxz
  have h4 : 0 ≤ ∑ jk ∈ (P.pps x).filter (fun jk => 1 ≤ jk.2),
      Real.log (P.p jk.1) / P.p jk.1 ^ (jk.2 + 1) :=
    Finset.sum_nonneg fun jk _ => div_nonneg (P.log_p_nonneg _) (P.pp_pos jk).le
  constructor <;> linarith [h1.1, h1.2]

/-- **Lemma 5.1(iv)**: for `2 ≤ y ≤ x ≤ z`,
`|∑_{y < p ≤ x} 1/p - log(log x / log y)| ≤ 2.20 / log y` (sum over the generalized primes, with
multiplicity). -/
theorem mertens_iv (h : P.HBS X0m z η1 η2 ε1) {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (hxz : x ≤ z) :
    |∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j -
      Real.log (Real.log x / Real.log y)| ≤ 2.20 / Real.log y := by
  have hSp : ∀ v ∈ Set.Icc y x, MertensIV.Sp (P.primesLe x) P.p v = P.Sp v := by
    intro v hv
    unfold MertensIV.Sp Sp
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp only [mem_filter, mem_primesLe]
    exact ⟨fun h => h.2, fun h' => ⟨h'.trans hv.2, h'⟩⟩
  have hE : ∀ v ∈ Set.Icc y x, -1.77 ≤ MertensIV.Sp (P.primesLe x) P.p v - Real.log v ∧
      MertensIV.Sp (P.primesLe x) P.p v - Real.log v ≤ 0.43 := by
    intro v hv
    rw [hSp v hv]
    exact h.Sp_sub_log_mem (by linarith [hv.1]) (hv.2.trans hxz)
  have := MertensIV.mertens_iv_explicit (P.primesLe x) P.p (fun j _ => P.one_lt j) hy hyx hE
  have e : (P.primesLe x).filter (fun j => y < P.p j ∧ P.p j ≤ x) =
      (P.primesLe x).filter (fun j => y < P.p j) := by
    ext j; simp only [mem_filter, mem_primesLe]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1⟩⟩
  rwa [e] at this

end HBS

/-- **Lemma 5.1 (Chebyshev–Mertens)** for a discrete Beurling system satisfying (HBS) on
`[1, z]`: for every `1 ≤ x ≤ z`,

* (i) `ψ_P(x) - ψ_P(x/2) ≤ 0.71 x` and `ψ_P(x) ≤ 1.42 x`;
* (ii) `-1.01 ≤ S_P(x) - log x ≤ 0.43`, `S_P(x) = ∑_{p^k ≤ x} log p / p^k`;
* (iii) `-1.77 ≤ S_{p,P}(x) - log x ≤ 0.43`, `S_{p,P}(x) = ∑_{p ≤ x} log p / p`;
* (iv) `|∑_{y < p ≤ x} 1/p - log(log x / log y)| ≤ 2.20 / log y` for every `2 ≤ y ≤ x`. -/
theorem lemma_5_1 {X0m z η1 η2 : ℝ} {ε1 : ℝ → ℝ} (h : P.HBS X0m z η1 η2 ε1) {x : ℝ}
    (hx : 1 ≤ x) (hxz : x ≤ z) :
    (P.psi x - P.psi (x / 2) ≤ 0.71 * x ∧ P.psi x ≤ 1.42 * x) ∧
    (-1.01 ≤ P.mertensS x - Real.log x ∧ P.mertensS x - Real.log x ≤ 0.43) ∧
    (-1.77 ≤ P.Sp x - Real.log x ∧ P.Sp x - Real.log x ≤ 0.43) ∧
    (∀ y, 2 ≤ y → y ≤ x →
      |∑ j ∈ (P.primesLe x).filter (fun j => y < P.p j), 1 / P.p j -
        Real.log (Real.log x / Real.log y)| ≤ 2.20 / Real.log y) :=
  ⟨⟨h.psi_sub_psi_half_le hx hxz, h.psi_le (by linarith) hxz⟩, h.mertensS_sub_log_mem hx hxz,
    h.Sp_sub_log_mem hx hxz, fun _ hy hyx => h.mertens_iv hy hyx hxz⟩

end BeurlingSystem

end
