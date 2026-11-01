module

public import RequestProject.Beurling.BaseRange.Step3Bound
public import RequestProject.Beurling.BaseRange.Mu0b

/-!
# The rational primes as a Beurling system, and `K^sh_ℚ` as a value-order operator

`ratSys` is the Beurling system of the rational primes (`p_j = qp j`, the `j`-th prime); its
elements have the values `iota e`. `kshQ_eq_kval`: `K^sh_ℚ(f₀ 1_{[X₀,∞)})(u) = Kval_ℚ(u)`, the
value-order sharp operator of `Step3Core` on the rational system (proof of Lemma 7.3(b), Step 3:
"respectively rational").
-/

@[expose] public section

open Real Finset BeurlingSystem

namespace BaseRange

/-- **The rational primes** as a Beurling system. -/
noncomputable def ratSys : BeurlingSystem where
  p j := (qp j : ℝ)
  one_lt j := by exact_mod_cast (qp_prime j).one_lt
  mono a b h := by simp only; exact_mod_cast qp_strictMono.monotone h
  tendsto := tendsto_natCast_atTop_atTop.comp qp_strictMono.tendsto_atTop

lemma ratSys_p (j : ℕ) : ratSys.p j = (qp j : ℝ) := rfl

lemma ratSys_val (e : ℕ →₀ ℕ) : ratSys.val e = (iota e : ℝ) :=
  ratSys.val_eq_iota fun _ _ => rfl

lemma ratSys_maxV (e : ℕ →₀ ℕ) : S3.maxV ratSys e = (Pplus (iota e) : ℝ) := by
  classical
  unfold S3.maxV Pplus
  rw [primeFactors_iota]
  apply le_antisymm
  · rw [S3.fold_max_le_iff]
    refine ⟨Nat.cast_nonneg _, fun j hj => ?_⟩
    rw [ratSys_p]
    exact_mod_cast Finset.le_sup (f := id) (Finset.mem_image_of_mem qp hj)
  · rcases (e.support.image qp).eq_empty_or_nonempty with h | h
    · rw [h, Finset.sup_empty]; simp only [Nat.bot_eq_zero, Nat.cast_zero]
      exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)
    · obtain ⟨r, hr, hsup⟩ := Finset.exists_mem_eq_sup _ h id
      rw [hsup]
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, hj, le_rfl⟩)

lemma iota_eq_one_iff (e : ℕ →₀ ℕ) : iota e = 1 ↔ e = 0 := by
  constructor
  · intro h
    apply iota_injective
    rw [h, iota_zero]
  · rintro rfl; exact iota_zero

/-- **`K^sh_ℚ` as the value-order operator of the rational system.** -/
theorem kshQ_eq_kval {X0 : ℕ} (hX : 1 < (X0 : ℝ)) {κ u : ℝ} (hκ : 0 < κ) (hu : 0 < u) :
    KshQ X0 (f0 X0 κ) u = S3.Kval ratSys X0 κ u := by
  classical
  have hX0 : (0 : ℝ) < X0 := by linarith
  unfold KshQ S3.Kval
  symm
  apply Finset.sum_bij (fun e _ => iota e)
  · intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    rw [ratSys.mem_elems, ratSys_val] at h1
    refine Finset.mem_Icc.mpr ⟨?_, Nat.le_floor h1⟩
    have := iota_pos e
    have : iota e ≠ 1 := fun h => h2 ((iota_eq_one_iff e).mp h)
    omega
  · intro e _ e' _ h; exact iota_injective h
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    obtain ⟨e, -, he⟩ := exists_iota_eq (n := m) (j := m + 1) (by omega) (fun r hr => by
      have h1 : r ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hr)
      have h2 : m + 1 ≤ qp (m + 1) := qp_strictMono.id_le (m + 1)
      omega)
    refine ⟨e, Finset.mem_filter.mpr ⟨?_, ?_⟩, he⟩
    · rw [ratSys.mem_elems, ratSys_val, he]
      exact (Nat.le_floor_iff (by positivity)).mp hm2
    · intro h0; rw [h0, iota_zero] at he; omega
  · intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
    rw [ratSys.mem_elems, ratSys_val] at h1
    have hm : (0 : ℝ) < iota e := by exact_mod_cast iota_pos e
    have hq : (X0 : ℝ) ≤ u / iota e := by
      rw [le_div_iff₀ hm]; rw [le_div_iff₀ hX0] at h1; linarith
    unfold S3.Gu S3.Fu
    rw [ratSys_val, ratSys_maxV, f0s_eq hX hκ hq]
    have hiff : (Pplus (iota e) : ℝ) * iota e ≤ u ↔ (Pplus (iota e) : ℝ) ≤ u / iota e := by
      rw [le_div_iff₀ hm]
    by_cases hc : (Pplus (iota e) : ℝ) * iota e ≤ u
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

end BaseRange
