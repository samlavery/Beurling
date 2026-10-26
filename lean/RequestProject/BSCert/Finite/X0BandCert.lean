module

public import RequestProject.BSCert.Finite.X0Band
meta import RequestProject.BSCert.Finite.X0Band

/-!
# `x0band_exact.py` (Appendix B.3): `B(n) ≤ 5/12` for `2 ≤ n ≤ 10⁶`, equality only at `n = 6`
-/

@[expose] public section

namespace BSCert.X0Band

lemma x0_checks : checkAll (10 ^ 6 - 1) 2 = true := by native_decide

/-- **`x0band_exact.py`** (Proposition 5.31(i), small range): for every integer
`2 ≤ n ≤ 10⁶`, `B(n) ≤ 5/12`; the bound is strict unless `n = 6`, and `B(6) = 5/12`. -/
theorem Bx_le_five_twelfths {n : ℕ} (hn1 : 2 ≤ n) (hn2 : n ≤ 10 ^ 6) :
    Bx n ≤ 5 / 12 ∧ (n ≠ 6 → Bx n < 5 / 12) := by
  have h := Bx_of_check hn1 (by unfold XL; omega)
    (checkAll_spec _ _ x0_checks n hn1 (by omega))
  exact ⟨h.1, h.2.1⟩

/-- `B(6) = 5/12`: the maximum over `2 ≤ n ≤ 10⁶` is attained at `n = 6`. -/
theorem Bx_six : Bx 6 = 5 / 12 :=
  (Bx_of_check (n := 6) (by norm_num) (by unfold XL; omega)
    (checkAll_spec _ _ x0_checks 6 (by norm_num) (by norm_num))).2.2 rfl

end BSCert.X0Band
