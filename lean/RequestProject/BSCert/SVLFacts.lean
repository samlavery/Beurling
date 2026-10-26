module

public import RequestProject.BSCert.StageRows

/-!
# The structural facts checked by `svl_stress.py` (Appendix B.7)

`svl_stress.py` checks, on random rank-full integer exponent matrices, the structural facts used
in the proof of the Staged Volume Lemma (Theorem A.10), taking the cover to be all the rows
(`C = B'`). Its stage rows are built greedily: for each stage, rows are added in index order when
they increase the rank of the rows restricted to `P≤t`. This is the lexicographically first basis
of `Mₜ` for the natural row order, i.e. `rowsUpTo E' Fin.val t` below.

Here the facts are proved for **every** rank-full matrix with natural-number entries:
* C1 (`lemmaA8`, parts (1), (2)): the nested stage rows exist;
* C2 (`svl_C2`): every pivot column has mass `≥ 1` in the rows `R≤t` of its stage prefix;
* C3 (`svl_C3`): every non-zero late free column of `F≤t` is non-zero on `R≤t`;
* C4/C5 (`svl_C4_C5`): a column of `P≤t ∪ F≤t` is determined by its entries in the rows `R≤t`,
  through `e_f = E_{·,P≤t} E_{R≤t,P≤t}⁻¹ e_{f,R≤t}` (this part does not need rank-fullness);
* C6 (`svl_C6`): the cumulative determinant `det E_{R≤t,P≤t}` is a non-zero integer.
-/

@[expose] public section

namespace BSCert.StageRows

variable {r m : ℕ}

/-- The rational matrix of a natural-number exponent matrix. -/
def toQ (E : Matrix (Fin r) (Fin m) ℕ) : Matrix (Fin r) (Fin m) ℚ := E.map (fun n => (n : ℚ))

lemma isPivot_ne_zero {E : Matrix (Fin r) (Fin m) ℚ} {j : Fin m} (h : IsPivot E j) :
    ∃ i, E i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  have : E.col j = 0 := funext hcon
  rw [this]
  exact Submodule.zero_mem _

/-- **C2.** Every pivot column of `P≤t` has total mass `≥ 1` in the rows `R≤t`. -/
theorem svl_C2 (E : Matrix (Fin r) (Fin m) ℕ) (t : ℕ) {p : Fin m}
    (hp : p ∈ pivUpTo (toQ E) t) :
    1 ≤ ∑ y ∈ rowsUpTo (toQ E) Fin.val t, E y p := by
  have h0 := isPivot_ne_zero (mem_pivotsIn.mp hp).2
  obtain ⟨y, hy, hyp⟩ := stageRows_cover (toQ E) (rk := Fin.val) Finset.univ
    (fun _ _ _ hw => absurd (Finset.mem_univ _) hw)
    (fun j ⟨i, hi⟩ => ⟨i, Finset.mem_univ _, hi⟩) (upTo_downClosed _ t)
    (mem_pivotsIn.mp hp).1 h0
  have hyR : y ∈ rowsUpTo (toQ E) Fin.val t := (Finset.mem_inter.mp hy).2
  have hpos : 1 ≤ E y p := by
    have : E y p ≠ 0 := by
      intro h; apply hyp; simp [toQ, h]
    omega
  exact le_trans hpos (Finset.single_le_sum (f := fun y => E y p) (fun _ _ => Nat.zero_le _) hyR)

/-- **C3.** Every non-zero free column of `F≤t` has a non-zero entry in a row of `R≤t`. -/
theorem svl_C3 (E : Matrix (Fin r) (Fin m) ℕ) (t : ℕ) {f : Fin m}
    (hf : f ∈ freeUpTo (toQ E) t) (hf0 : ∃ i, E i f ≠ 0) :
    ∃ y ∈ rowsUpTo (toQ E) Fin.val t, E y f ≠ 0 := by
  obtain ⟨i, hi⟩ := hf0
  obtain ⟨y, hy, hyf⟩ := stageRows_cover (toQ E) (rk := Fin.val) Finset.univ
    (fun _ _ _ hw => absurd (Finset.mem_univ _) hw)
    (fun j ⟨i, hi⟩ => ⟨i, Finset.mem_univ _, hi⟩) (upTo_downClosed _ t) hf.2
    ⟨i, by simpa [toQ] using hi⟩
  exact ⟨y, (Finset.mem_inter.mp hy).2, by simpa [toQ] using hyf⟩

/-- **C4/C5.** A column `f` of `P≤t ∪ F≤t` is `E_{·,P≤t} E_{R≤t,P≤t}⁻¹ e_{f,R≤t}`: with `N`
the inverse of `E_{R≤t,P≤t}`, every row `i` (not only the rows of `R≤t`) satisfies
`E i f = ∑_{p ∈ P≤t} E i p · (N e_{f,R≤t})_p`. (`N` exists by `stageRows_invertible`.) So `f` is determined by its entries in `R≤t`,
and its coefficient in the remaining rows vanishes after eliminating `P≤t`. -/
theorem svl_C4_C5 (E : Matrix (Fin r) (Fin m) ℕ) (t : ℕ) {f : Fin m} (hf : f ∈ upTo (toQ E) t)
    (N : Matrix (pivUpTo (toQ E) t) (rowsUpTo (toQ E) Fin.val t) ℚ)
    (hN : (Matrix.of fun (y : rowsUpTo (toQ E) Fin.val t) (p : pivUpTo (toQ E) t) =>
      toQ E y p) * N = 1) :
    ∀ i, (E i f : ℚ) = ∑ p : pivUpTo (toQ E) t,
      (E i p : ℚ) * N.mulVec (fun y : rowsUpTo (toQ E) Fin.val t => (E y f : ℚ)) p := by
  set β := N.mulVec (fun y : rowsUpTo (toQ E) Fin.val t => (E y f : ℚ))
  -- `N` is also a right inverse, so `β` matches column `f` on the rows `R≤t`
  set M : Matrix (rowsUpTo (toQ E) Fin.val t) (pivUpTo (toQ E) t) ℚ :=
    Matrix.of fun y p => toQ E y p
  have hMN : M * N = 1 := hN
  have hR : ∀ y ∈ rowsUpTo (toQ E) Fin.val t, toQ E y f = ∑ p, β p * toQ E y p := by
    intro y hy
    have := congrFun (congrArg (fun A => A.mulVec
      (fun y : rowsUpTo (toQ E) Fin.val t => (E y f : ℚ))) hMN) ⟨y, hy⟩
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at this
    rw [show toQ E y f = (E y f : ℚ) from rfl, ← this]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, β]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have := col_determined (toQ E) Fin.val_injective (upTo_downClosed _ t) hf β hR
  intro i
  have h := this i
  simp only [toQ, Matrix.map_apply] at h
  rw [h]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- **C6.** The cumulative determinant `det E_{R≤t,P≤t}` (for any matching of the rows
`R≤t` with the columns `P≤t`) is a non-zero integer. -/
theorem svl_C6 (E : Matrix (Fin r) (Fin m) ℕ) (t : ℕ)
    (e : rowsUpTo (toQ E) Fin.val t ≃ pivUpTo (toQ E) t) :
    (Matrix.of fun (a b : pivUpTo (toQ E) t) => (E (e.symm a) b : ℤ)).det ≠ 0 := by
  obtain ⟨N, hMN, hNM⟩ := stageRows_invertible (toQ E) Fin.val_injective (upTo (toQ E) t)
  set A : Matrix (pivUpTo (toQ E) t) (pivUpTo (toQ E) t) ℤ :=
    Matrix.of fun a b => (E (e.symm a) b : ℤ)
  -- the rational square matrix `A` has a right inverse
  let N' : Matrix (pivUpTo (toQ E) t) (pivUpTo (toQ E) t) ℚ := fun q a => N q (e.symm a)
  have hAQ : (A.map (Int.cast : ℤ → ℚ)) * N' = 1 := by
    ext a a'
    have := congrFun (congrFun hMN (e.symm a)) (e.symm a')
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, A, N', toQ] at this ⊢
    push_cast
    convert this using 1
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  have hdet : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  intro h
  apply hdet
  have h2 := (Int.castRingHom ℚ).map_det A
  rw [h, map_zero] at h2
  exact h2.symm

end BSCert.StageRows
