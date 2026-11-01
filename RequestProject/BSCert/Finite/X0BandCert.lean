module

public import RequestProject.BSCert.Finite.X0Chunks.X0C0
public import RequestProject.BSCert.Finite.X0Chunks.X0C1
public import RequestProject.BSCert.Finite.X0Chunks.X0C2
public import RequestProject.BSCert.Finite.X0Chunks.X0C3

/-!
# `x0band_exact.py` (Appendix B.3): `B(n) ≤ 5/12` for `2 ≤ n ≤ 10⁶`, equality only at `n = 6`

Kernel-checked, without `native_decide`:
* `Bx_le_φ` (`X0Mono`): `B(n) ≤ B(φ n)`, strictly if `φ n < n`, where `φ n` moves the prime
  factors of `n`, in order, to the first primes;
* `rep_of`, `mem_gen` (`X0Rep`): `φ n` is `nOf PL v` for one of the 785 vectors of `gen PL (10⁶)`;
* `ok0`–`ok25` (`X0Chunks`): the exact check of `B < 5/12` (or `B = 5/12` for `6`) on each of
  them, through the certificate of `H_ord` and the integer formula `Bx_formula`.
-/

@[expose] public section

namespace BSCert.X0Band

open BSCert.X0Rep BSCert.X0Vec BSCert.X0Mono

/-- The 26 slices. -/
def allSl : List (List (List ℕ)) :=
  [sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13, sl14, sl15, sl16,
    sl17, sl18, sl19, sl20, sl21, sl22, sl23, sl24, sl25]

lemma gen_eq : gen PL (10 ^ 6) = allSl.flatten := by decide +kernel

lemma rep_check {v : List ℕ} (hv : v ∈ gen PL (10 ^ 6)) (hl : v.length = 7) :
    isZ v = true ∨ Bx (nOf PL v) < 5 / 12 ∨ (v = v6 ∧ Bx (nOf PL v) = 5 / 12) := by
  have hl' : v.length = PL.length := hl
  rw [gen_eq] at hv
  obtain ⟨l, hl0, hv⟩ := List.mem_flatten.mp hv
  simp only [allSl, List.mem_cons, List.not_mem_nil, or_false] at hl0
  rcases hl0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkL_sound _ _ ok0 v hv hl'
  · exact chkL_sound _ _ ok1 v hv hl'
  · exact chkL_sound _ _ ok2 v hv hl'
  · exact chkL_sound _ _ ok3 v hv hl'
  · exact chkL_sound _ _ ok4 v hv hl'
  · exact chkL_sound _ _ ok5 v hv hl'
  · exact chkL_sound _ _ ok6 v hv hl'
  · exact chkL_sound _ _ ok7 v hv hl'
  · exact chkL_sound _ _ ok8 v hv hl'
  · exact chkL_sound _ _ ok9 v hv hl'
  · exact chkL_sound _ _ ok10 v hv hl'
  · exact chkL_sound _ _ ok11 v hv hl'
  · exact chkL_sound _ _ ok12 v hv hl'
  · exact chkL_sound _ _ ok13 v hv hl'
  · exact chkL_sound _ _ ok14 v hv hl'
  · exact chkL_sound _ _ ok15 v hv hl'
  · exact chkL_sound _ _ ok16 v hv hl'
  · exact chkL_sound _ _ ok17 v hv hl'
  · exact chkL_sound _ _ ok18 v hv hl'
  · exact chkL_sound _ _ ok19 v hv hl'
  · exact chkL_sound _ _ ok20 v hv hl'
  · exact chkL_sound _ _ ok21 v hv hl'
  · exact chkL_sound _ _ ok22 v hv hl'
  · exact chkL_sound _ _ ok23 v hv hl'
  · exact chkL_sound _ _ ok24 v hv hl'
  · exact chkL_sound _ _ ok25 v hv hl'

/-- **`x0band_exact.py`** (Proposition 5.31(i), small range): for every integer
`2 ≤ n ≤ 10⁶`, `B(n) ≤ 5/12`; the bound is strict unless `n = 6`, and `B(6) = 5/12`. -/
theorem Bx_le_five_twelfths {n : ℕ} (hn1 : 2 ≤ n) (hn2 : n ≤ 10 ^ 6) :
    Bx n ≤ 5 / 12 ∧ (n ≠ 6 → Bx n < 5 / 12) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨v, hl, hps, hv⟩ := rep_of hn1 hn2
  have hle : φ n n ≤ n := φ_le hn0 (dvd_refl n)
  have h2 : 2 ≤ φ n n := one_lt_φ hn0 (dvd_refl n) (by omega)
  have hmem : v ∈ gen PL (10 ^ 6) :=
    mem_gen PL _ v PL_prime le_rfl (by rw [hl]; rfl) hps (by omega)
  have hB := Bx_le_φ hn1
  rcases rep_check hmem hl with hz | hlt | ⟨rfl, heq⟩
  · have := (nOf_eq_one_iff v (by rw [hl]; rfl)).mpr hz
    omega
  · rw [hv] at hlt
    exact ⟨hB.1.trans hlt.le, fun _ => hB.1.trans_lt hlt⟩
  · rw [hv] at heq
    have h6 : φ n n = 6 := by rw [← hv]; rfl
    refine ⟨heq ▸ hB.1, fun hne => ?_⟩
    have : φ n n < n := by omega
    exact heq ▸ hB.2 this

/-- `B(6) = 5/12`: the maximum over `2 ≤ n ≤ 10⁶` is attained at `n = 6`. -/
theorem Bx_six : Bx 6 = 5 / 12 :=
  eqV_sound (v := v6) (hs := [1, 1, 1, 3]) rfl (by decide +kernel)

end BSCert.X0Band
