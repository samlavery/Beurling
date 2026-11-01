module

public import RequestProject.Beurling.Noise.TauNearProofLoc

/-!
# Lemma 5.20: the pointwise block bound

For a weight `ψ` and `v > 0`,

  `∑_{w τ-near at v} ψ(v/w)/w ≤ ∑_{k < K} 56 H(P_k) Ψ_k/P_k ∑_{m ∈ Sm_k(v)} 1/m`,

with the dyadic scales `P_k = 2^k X₀⁻/2` (`Pk`), `Ψ_k ≥ ψ` on `[0.85 P_k, 2.42 P_k]`, and
`Sm_k(v)` the `3P_k`-smooth elements of `(v/(4P_k²), v/P_k²]` (`Sm`) (`etaG_le_blocks`). This is
the paper's localisation and counting: `w = p m` with `p` the prime of `w` largest in decision
order, `p` in the window `|p - p₀| ≤ 1.71 H(p₀)` around `p₀ = √(v/m)`, which holds
`≤ 46 H(p₀)` primes (`Hyp.count`), each with `1/p ≤ 1/(0.829 p₀)`; the cofactor `m` lies in the
dyadic block of `p₀` and is `1.5 p₀`-smooth.
-/

@[expose] public section

open Finset Real BeurlingSystem

namespace KR.TNP

variable {P : BeurlingSystem} {H : ℝ → ℝ} {tw : ℕ → ℝ} {X0m Z η1 η2 : ℝ} {ε1 : ℝ → ℝ}
  {ε θ : ℝ}

/-- The dyadic scales `P_k = 2^k X₀⁻/2`. -/
noncomputable def Pk (X0m : ℝ) (k : ℕ) : ℝ := X0m / 2 * 2 ^ k

/-- The `3P_k`-smooth elements of `(v/(4P_k²), v/P_k²]`. -/
noncomputable def Sm (P : BeurlingSystem) (X0m : ℝ) (k : ℕ) (v : ℝ) : Finset (ℕ →₀ ℕ) :=
  open scoped Classical in
  (P.elems (v / Pk X0m k ^ 2)).filter (fun e => v / (4 * Pk X0m k ^ 2) < P.val e ∧
    ∀ i ∈ e.support, P.p i ≤ 3 * Pk X0m k)

lemma Pk_pos (hX : 0 < X0m) (k : ℕ) : 0 < Pk X0m k := by unfold Pk; positivity

lemma Pk_succ (X0m : ℝ) (k : ℕ) : Pk X0m (k + 1) = 2 * Pk X0m k := by
  unfold Pk; rw [pow_succ]; ring

/-- The dyadic class of `p₀ ∈ [P₀, P_K)`. -/
lemma exists_class {X0m p0 : ℝ} (h0 : Pk X0m 0 ≤ p0) :
    ∀ K : ℕ, p0 < Pk X0m K → ∃ k < K, Pk X0m k ≤ p0 ∧ p0 < 2 * Pk X0m k := by
  intro K
  induction K with
  | zero => intro h; exact absurd h (not_lt.mpr h0)
  | succ K ih =>
    intro hK
    by_cases hlt : p0 < Pk X0m K
    · obtain ⟨k, hk, h⟩ := ih hlt
      exact ⟨k, by omega, h⟩
    · push_neg at hlt
      exact ⟨K, by omega, hlt, by rw [← Pk_succ]; exact hK⟩

/-- `τ_w` at `w = iota e`: the maximum of `t` over the primes of `e`. -/
lemma tauW_iota {e : ℕ →₀ ℕ} {j : ℕ} (hj : j ∈ e.support)
    (hmax : ∀ i ∈ e.support, tw (qp i) ≤ tw (qp j)) : tauW tw (iota e) = tw (qp j) := by
  have hne : (iota e).primeFactors.Nonempty := by
    rw [BeurlingSystem.primeFactors_iota]; exact ⟨qp j, mem_image_of_mem _ hj⟩
  unfold tauW
  rw [dif_pos hne]
  apply le_antisymm
  · apply Finset.sup'_le
    intro r hr
    rw [BeurlingSystem.primeFactors_iota] at hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    exact hmax i hi
  · apply Finset.le_sup'
    rw [BeurlingSystem.primeFactors_iota]; exact mem_image_of_mem _ hj

lemma val_eq_mul_p {e : ℕ →₀ ℕ} {j : ℕ} (hj : j ∈ e.support) :
    P.val e = P.val (e - Finsupp.single j 1) * P.p j := by
  have h1 : 0 + 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have := P.val_sub_single h1
  simpa using this

/-- **The localisation for one `τ`-near `w = iota e`** at `v`: with `j` the prime of `e`
largest in decision order, `e' = e - p_j`, `p₀ = √(v/e')`: `p₀ ≥ X₀⁻/2`,
`|p_j - p₀| ≤ 1.71 H(p₀)`, `e'` is `1.5p₀`-smooth, and `v/e ≥ X₀⁻`. -/
theorem loc_elem (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {v : ℝ} (hv : 0 < v) {e : ℕ →₀ ℕ}
    {j : ℕ} (hj : j ∈ e.support) (hmax : ∀ i ∈ e.support, tw (qp i) ≤ tw (qp j))
    (hτ : TauNearAt P H tw X0m v (iota e)) :
    X0m / 2 ≤ √(v / P.val (e - Finsupp.single j 1)) ∧
    |P.p j - √(v / P.val (e - Finsupp.single j 1))| ≤
      1.71 * H (√(v / P.val (e - Finsupp.single j 1))) ∧
    (∀ i ∈ (e - Finsupp.single j 1).support,
      P.p i ≤ 1.5 * √(v / P.val (e - Finsupp.single j 1))) := by
  set e' := e - Finsupp.single j 1
  have hP := h.width
  have hV : Vl P (iota e) = P.val e := P.valN_iota e
  obtain ⟨hτ1, hτ2⟩ := hτ
  rw [hV, tauW_iota hj hmax] at hτ1
  rw [hV] at hτ2
  have hpj := P.p_pos j
  have hval : P.val e = P.val e' * P.p j := val_eq_mul_p hj
  have hve := P.val_pos e'
  have hcp : v / P.val e * P.p j = v / P.val e' := by rw [hval]; field_simp
  have hloc := loc_real hP hpj hτ2 hτ1
    (fun hp => by have := h.dec_hi j hp; rwa [abs_sub_comm] at this ⊢)
    (fun hp => h.dec_lo j hp)
  rw [hcp] at hloc
  obtain ⟨hp2, hp0, hw, ht⟩ := hloc
  refine ⟨hp0, hw, fun i hi => ?_⟩
  have hie : i ∈ e.support := by
    have hsub : e'.support ⊆ e.support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hk0; apply hk
      simp only [e', Finsupp.tsub_apply, hk0, zero_tsub]
    exact hsub hi
  have hwb := window_bounds hP hp0 hw
  exact smooth_real hP (P.p_pos i) (hmax i hie) ht hwb.2 hp0
    (fun hq => by have := h.dec_hi i hq; exact this)

/-- **The pointwise block bound** (Lemma 5.20, proof, localisation and counting): for `v > 0`,
`√v < P_K`, and `Ψ_k ≥ max(0, ψ)` on `[0.85 P_k, 2.42 P_k]`,
`∑_{w τ-near at v} ψ(v/w)/w ≤ ∑_{k<K} 56 H(P_k) Ψ_k/P_k ∑_{m ∈ Sm_k(v)} 1/m`. -/
theorem etaG_le_blocks (h : Hyp P H tw X0m Z η1 η2 ε1 ε θ) {ψ : ℝ → ℝ} {Ψ : ℕ → ℝ} {v : ℝ}
    {K : ℕ} (hv : 0 < v) (hK : √v < Pk X0m K) (hΨ0 : ∀ k, 0 ≤ Ψ k)
    (hψ : ∀ k < K, ∀ c, 0.85 * Pk X0m k ≤ c → c ≤ 2.42 * Pk X0m k → ψ c ≤ Ψ k) :
    etaG P H tw X0m ψ v ≤ ∑ k ∈ range K, 56 * H (Pk X0m k) * Ψ k / Pk X0m k *
      ∑ e ∈ Sm P X0m k v, 1 / P.val e := by
  classical
  have hP := h.width
  have hX := hP.X0m_pos
  -- the sum over elements
  set T := (P.elems (v / X0m)).filter (fun e => 2 ≤ iota e ∧ TauNearAt P H tw X0m v (iota e))
  have hsum : etaG P H tw X0m ψ v = ∑ e ∈ T, ψ (v / P.val e) / P.val e := by
    unfold etaG Cof
    rw [Finset.filter_filter, Finset.filter_image, Finset.sum_image
      (fun a _ b _ hab => iota_injective hab)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Vl, P.valN_iota]
  rw [hsum]
  -- the top prime of each `e ∈ T`
  have hne : ∀ e ∈ T, e.support.Nonempty := by
    intro e he
    have h2 := (Finset.mem_filter.mp he).2.1
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hc
    subst hc
    simp [iota] at h2
  have htop : ∀ e ∈ T, ∃ j ∈ e.support, ∀ i ∈ e.support, tw (qp i) ≤ tw (qp j) :=
    fun e he => e.support.exists_max_image (fun i => tw (qp i)) (hne e he)
  choose! jm hjm hjmax using htop
  set φ : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) := fun e => e - Finsupp.single (jm e) 1
  set p0 : (ℕ →₀ ℕ) → ℝ := fun e' => √(v / P.val e')
  have hloc : ∀ e ∈ T, X0m / 2 ≤ p0 (φ e) ∧ |P.p (jm e) - p0 (φ e)| ≤ 1.71 * H (p0 (φ e)) ∧
      (∀ i ∈ (φ e).support, P.p i ≤ 1.5 * p0 (φ e)) :=
    fun e he => loc_elem h hv (hjm e he) (hjmax e he) (Finset.mem_filter.mp he).2.2
  -- `p₀ ≤ √v`
  have hp0v : ∀ e', p0 e' ≤ √v := fun e' => by
    apply Real.sqrt_le_sqrt
    exact div_le_self hv.le (P.one_le_val e')
  -- the weight `G(e')`
  set G : (ℕ →₀ ℕ) → ℝ := fun e' => ∑ k ∈ range K,
    if Pk X0m k ≤ p0 e' ∧ p0 e' < 2 * Pk X0m k then
      Ψ k / (0.829 * p0 e' * P.val e') else 0
  have hG0 : ∀ e', 0 ≤ G e' := by
    intro e'
    refine Finset.sum_nonneg fun k _ => ?_
    split_ifs with hc
    · have := Pk_pos hX k
      have := P.val_pos e'
      have := hΨ0 k
      have : 0 < p0 e' := by linarith [hc.1]
      positivity
    · exact le_rfl
  -- step 1: pointwise
  have hpt : ∀ e ∈ T, ψ (v / P.val e) / P.val e ≤ G (φ e) := by
    intro e he
    obtain ⟨h0, hw, -⟩ := hloc e he
    have h00 : Pk X0m 0 ≤ p0 (φ e) := by unfold Pk; simpa using h0
    obtain ⟨k, hk, hk1, hk2⟩ := exists_class h00 K ((hp0v _).trans_lt hK)
    have hwb := window_bounds hP h0 hw
    have hpos0 : 0 < p0 (φ e) := by linarith [Pk_pos hX k]
    have hval : P.val e = P.val (φ e) * P.p (jm e) := val_eq_mul_p (hjm e he)
    have hve := P.val_pos (φ e)
    have hpj := P.p_pos (jm e)
    have hsq : p0 (φ e) * p0 (φ e) = v / P.val (φ e) :=
      Real.mul_self_sqrt (div_pos hv hve).le
    -- the centre `c = p₀²/p`
    have hc : v / P.val e = p0 (φ e) ^ 2 / P.p (jm e) := by
      rw [hval, sq, hsq]; field_simp
    have hc1 : 0.85 * Pk X0m k ≤ v / P.val e := by
      rw [hc, le_div_iff₀ hpj]; nlinarith
    have hc2 : v / P.val e ≤ 2.42 * Pk X0m k := by
      rw [hc, div_le_iff₀ hpj]; nlinarith
    have hψk := hψ k hk _ hc1 hc2
    have hΨk := hΨ0 k
    calc ψ (v / P.val e) / P.val e ≤ Ψ k / P.val e :=
          div_le_div_of_nonneg_right hψk (P.val_pos e).le
      _ ≤ Ψ k / (0.829 * p0 (φ e) * P.val (φ e)) := by
          apply div_le_div_of_nonneg_left hΨk (by positivity)
          rw [hval]; nlinarith
      _ ≤ G (φ e) := by
          have := Finset.single_le_sum (f := fun k => if Pk X0m k ≤ p0 (φ e) ∧
              p0 (φ e) < 2 * Pk X0m k then Ψ k / (0.829 * p0 (φ e) * P.val (φ e)) else 0)
            (fun k _ => by
              beta_reduce
              split_ifs with hc
              · have := Pk_pos hX k; have : 0 < p0 (φ e) := by linarith [hc.1]
                have := hΨ0 k; have := P.val_pos (φ e)
                positivity
              · exact le_rfl) (Finset.mem_range.mpr hk)
          simp only [hk1, hk2, and_self, if_true] at this
          exact this
  -- step 2: fibres
  have hfib : ∀ e' ∈ T.image φ, ((T.filter fun e => φ e = e').card : ℝ) ≤ 46 * H (p0 e') := by
    intro e' he'
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨h0, -, -⟩ := hloc e0 he0
    refine le_trans ?_ (h.count _ h0)
    norm_cast
    apply Finset.card_le_card_of_injOn jm
    · intro e he
      have he1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he))
      obtain ⟨-, hw, -⟩ := hloc e he1.1
      rw [he1.2] at hw
      simp only [Finset.mem_coe, Finset.mem_filter, mem_primesLe]
      constructor
      · linarith [(abs_le.mp hw).2]
      · linarith [(abs_le.mp hw).1]
    · intro a ha b hb hab
      have ha1 := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have hb1 := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      have hea : a = φ a + Finsupp.single (jm a) 1 := by
        have hle : Finsupp.single (jm a) 1 ≤ a :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
            (Finsupp.mem_support_iff.mp (hjm a ha1.1)))
        exact (tsub_add_cancel_of_le hle).symm
      have heb : b = φ b + Finsupp.single (jm b) 1 := by
        have hle : Finsupp.single (jm b) 1 ≤ b :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr
            (Finsupp.mem_support_iff.mp (hjm b hb1.1)))
        exact (tsub_add_cancel_of_le hle).symm
      rw [hea, heb, ha1.2, hb1.2, hab]
  -- assemble
  calc ∑ e ∈ T, ψ (v / P.val e) / P.val e ≤ ∑ e ∈ T, G (φ e) := Finset.sum_le_sum hpt
    _ = ∑ e' ∈ T.image φ, ((T.filter fun e => φ e = e').card : ℝ) * G e' := by
        rw [Finset.sum_comp]; simp only [nsmul_eq_mul]
    _ ≤ ∑ e' ∈ T.image φ, 46 * H (p0 e') * G e' :=
        Finset.sum_le_sum fun e' he' => mul_le_mul_of_nonneg_right (hfib e' he') (hG0 e')
    _ ≤ ∑ e' ∈ T.image φ, ∑ k ∈ range K, 56 * H (Pk X0m k) * Ψ k / Pk X0m k *
          (if e' ∈ Sm P X0m k v then 1 / P.val e' else 0) := by
        refine Finset.sum_le_sum fun e' he' => ?_
        obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he'
        obtain ⟨h0, -, hsm⟩ := hloc e0 he0
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        split_ifs with hc hm
        · -- the class `k`
          have hk0 := Pk_pos hX k
          have hpos0 : 0 < p0 (φ e0) := by linarith [hc.1]
          have hve := P.val_pos (φ e0)
          have hH := hP.reg.pos (p0 (φ e0))
          -- `H(p₀) ≤ 1.001 H(P_k)`
          have hRH : H (p0 (φ e0)) ≤ 1.001 * H (Pk X0m k) := by
            have hk2 : X0m / 2 ≤ Pk X0m k := by
              unfold Pk; have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); nlinarith
            have hr := hP.RH (Pk X0m k) (p0 (φ e0) / Pk X0m k) hk2
              (by rw [le_div_iff₀ hk0]; linarith [hc.1])
            rw [mul_div_cancel₀ _ hk0.ne'] at hr
            have hw2 : (p0 (φ e0) / Pk X0m k) ^ ε ≤ 2 ^ ε :=
              Real.rpow_le_rpow (by positivity) (by rw [div_le_iff₀ hk0]; linarith [hc.2])
                hP.eps_nonneg
            have h2 := KR.two_rpow_le hP.eps_nonneg hP.eps_le
            have hHk := hP.reg.pos (Pk X0m k)
            nlinarith
          have hΨk := hΨ0 k
          rw [show 56 * H (Pk X0m k) * Ψ k / Pk X0m k * (1 / P.val (φ e0)) =
            56 * H (Pk X0m k) * Ψ k / (Pk X0m k * P.val (φ e0)) by field_simp]
          rw [show 46 * H (p0 (φ e0)) * (Ψ k / (0.829 * p0 (φ e0) * P.val (φ e0))) =
            46 * H (p0 (φ e0)) * Ψ k / (0.829 * p0 (φ e0) * P.val (φ e0)) by ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hHk := hP.reg.pos (Pk X0m k)
          have e1 : 46 * H (p0 (φ e0)) * Ψ k * (Pk X0m k * P.val (φ e0)) ≤
              46 * (1.001 * H (Pk X0m k)) * Ψ k * (Pk X0m k * P.val (φ e0)) := by
            gcongr
          have e2 : 46 * (1.001 * H (Pk X0m k)) * Ψ k * (Pk X0m k * P.val (φ e0)) ≤
              56 * H (Pk X0m k) * Ψ k * (0.829 * p0 (φ e0) * P.val (φ e0)) := by
            have : 0 ≤ H (Pk X0m k) * Ψ k * P.val (φ e0) := by positivity
            nlinarith [hc.1]
          linarith
        · -- impossible: `φ e0 ∈ Sm`
          exfalso; apply hm
          have hk0 := Pk_pos hX k
          have hpos0 : 0 < p0 (φ e0) := by linarith [hc.1]
          have hve := P.val_pos (φ e0)
          have hsq : p0 (φ e0) * p0 (φ e0) = v / P.val (φ e0) :=
            Real.mul_self_sqrt (div_pos hv hve).le
          simp only [Sm, Finset.mem_filter, mem_elems]
          refine ⟨?_, ?_, fun i hi => (hsm i hi).trans (by linarith [hc.2])⟩
          · rw [le_div_iff₀ (by positivity)]
            have hv' : v = p0 (φ e0) * p0 (φ e0) * P.val (φ e0) := by
              rw [hsq]; field_simp
            have h1 := mul_le_mul hc.1 hc.1 hk0.le hpos0.le
            have h2 := mul_le_mul_of_nonneg_right h1 hve.le
            rw [hv']; nlinarith
          · rw [div_lt_iff₀ (by positivity)]
            have hv' : v = p0 (φ e0) * p0 (φ e0) * P.val (φ e0) := by
              rw [hsq]; field_simp
            have h1 := mul_lt_mul'' hc.2 hc.2 hpos0.le hpos0.le
            have h2 := mul_lt_mul_of_pos_right h1 hve
            rw [hv']; nlinarith
        · have := hP.reg.pos (Pk X0m k); have := hΨ0 k; have := Pk_pos hX k
          have := P.val_pos (φ e0)
          simp only [mul_zero]; positivity
        · simp
    _ = ∑ k ∈ range K, 56 * H (Pk X0m k) * Ψ k / Pk X0m k *
          ∑ e' ∈ T.image φ, (if e' ∈ Sm P X0m k v then 1 / P.val e' else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ range K, 56 * H (Pk X0m k) * Ψ k / Pk X0m k *
          ∑ e ∈ Sm P X0m k v, 1 / P.val e := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hc0 : 0 ≤ 56 * H (Pk X0m k) * Ψ k / Pk X0m k := by
          have := hP.reg.pos (Pk X0m k); have := hΨ0 k; have := Pk_pos hX k; positivity
        apply mul_le_mul_of_nonneg_left _ hc0
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro e _ _; exact (one_div_pos.mpr (P.val_pos e)).le

end KR.TNP

end
