module

public import RequestProject.BSCert.Consts.PhiDefs
public import RequestProject.BSCert.Cover

/-!
# `phi_bounds.py`: the cell test `phiCell` for `|ϕ''| ≤ 10` and its soundness

The cover itself is checked by the kernel in `PhiCover1`, `PhiCover2`; the statements are in
`PhiCert`.
-/

@[expose] public section

namespace BSCert.Consts

open Real BSCert

/-- Upper bound for `w(E) = E/(1+E)²` on `[lo, hi]` (`w` increases up to `E = 1`, then
decreases, and `w ≤ 1/4`). -/
def wHi (lo hi : ℚ) : ℚ :=
  if hi ≤ 1 then hi / (1 + hi) ^ 2 else if 1 ≤ lo then lo / (1 + lo) ^ 2 else 1 / 4

lemma w_le_wHi {E : ℝ} {lo hi : ℚ} (hlo : (lo : ℝ) ≤ E) (hhi : E ≤ hi) (hlo0 : 0 < lo) :
    E / (1 + E) ^ 2 ≤ wHi lo hi := by
  have hlo0' : (0 : ℝ) < lo := by exact_mod_cast hlo0
  have hE0 : 0 < E := lt_of_lt_of_le hlo0' hlo
  unfold wHi
  split_ifs with h1 h2
  · have h1' : (hi : ℝ) ≤ 1 := by exact_mod_cast h1
    have hhi0 : (0 : ℝ) < hi := by linarith
    push_cast
    rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
    have : 0 ≤ ((hi : ℝ) - E) * (1 - E * hi) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · have h2' : (1 : ℝ) ≤ lo := by exact_mod_cast h2
    push_cast
    rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
    have : 0 ≤ (E - lo) * (E * lo - 1) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (E - 1)]

/-- The cell test for `|ϕ''| ≤ 10` on `[a, b] ⊆ (0, 1)`. -/
def phiCell (a b : ℚ) : Bool :=
  if 0 < a ∧ a ≤ b ∧ b < 1 then
    match expPt (1 / b - 1 / (1 - b)), expPt (1 / a - 1 / (1 - a)) with
    | some e1, some e2 =>
      if 0 < e1.1 then
        let q : Itv := ⟨1 / b ^ 2 + 1 / (1 - a) ^ 2, 1 / a ^ 2 + 1 / (1 - b) ^ 2⟩
        let d : Itv := ⟨-2 / a ^ 3 + 2 / (1 - a) ^ 3, -2 / b ^ 3 + 2 / (1 - b) ^ 3⟩
        let r : Itv := ⟨1 - 2 / (1 + e1.1), 1 - 2 / (1 + e2.2)⟩
        let X := Itv.add d (Itv.mul (Itv.mul q q) r)
        decide (wHi e1.1 e2.2 * max |X.lo| |X.hi| ≤ 10)
      else false
    | _, _ => false
  else false

lemma phiCell_sound (a b : ℚ) (h : phiCell a b = true) (t : ℝ) (hat : (a : ℝ) ≤ t)
    (htb : t ≤ (b : ℝ)) : |D2 t| ≤ 10 := by
  unfold phiCell at h
  split_ifs at h with hab
  obtain ⟨ha0, -, hb1⟩ := hab
  split at h
  · rename_i e1 e2 he1 he2
    split_ifs at h with he0
    simp only [decide_eq_true_eq] at h
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    have hb1' : (b : ℝ) < 1 := by exact_mod_cast hb1
    have ht0 : 0 < t := by linarith
    have ht1 : 0 < 1 - t := by linarith
    have hb0 : (0 : ℝ) < b := by linarith
    have ha1 : (0 : ℝ) < 1 - a := by linarith
    have hb1'' : (0 : ℝ) < 1 - b := by linarith
    -- monotone pieces
    have i1 : 1 / (b : ℝ) ≤ 1 / t := one_div_le_one_div_of_le ht0 htb
    have i2 : 1 / t ≤ 1 / (a : ℝ) := one_div_le_one_div_of_le ha0' hat
    have i3 : 1 / (1 - (a : ℝ)) ≤ 1 / (1 - t) := one_div_le_one_div_of_le ht1 (by linarith)
    have i4 : 1 / (1 - t) ≤ 1 / (1 - (b : ℝ)) := one_div_le_one_div_of_le hb1'' (by linarith)
    have p1 : (0 : ℝ) ≤ 1 / b := by positivity
    have p3 : (0 : ℝ) ≤ 1 / (1 - a) := by positivity
    -- `g`, `E`
    have hg1 : (((1 / b - 1 / (1 - b) : ℚ)) : ℝ) ≤ gq t := by
      unfold gq; push_cast; linarith
    have hg2 : gq t ≤ (((1 / a - 1 / (1 - a) : ℚ)) : ℝ) := by
      unfold gq; push_cast; linarith
    set E := Real.exp (gq t) with hE
    have hElo : (e1.1 : ℝ) ≤ E := le_trans (expPt_spec he1).1 (Real.exp_le_exp.mpr hg1)
    have hEhi : E ≤ (e2.2 : ℝ) := le_trans (Real.exp_le_exp.mpr hg2) (expPt_spec he2).2
    have he0' : (0 : ℝ) < e1.1 := by exact_mod_cast he0
    have hE0 : 0 < E := Real.exp_pos _
    -- `q`, `q'`, `r`
    have hq : Itv.Mem (qq t) ⟨1 / b ^ 2 + 1 / (1 - a) ^ 2, 1 / a ^ 2 + 1 / (1 - b) ^ 2⟩ := by
      have e : qq t = (1 / t) ^ 2 + (1 / (1 - t)) ^ 2 := by
        unfold qq; simp only [div_pow, one_pow]
      constructor <;> simp only <;> push_cast <;> rw [e]
      · have := pow_le_pow_left₀ p1 i1 2
        have := pow_le_pow_left₀ p3 i3 2
        rw [div_pow, div_pow] at *; simp only [one_pow] at *; linarith
      · have := pow_le_pow_left₀ (by positivity) i2 2
        have := pow_le_pow_left₀ (by positivity) i4 2
        rw [div_pow, div_pow] at *; simp only [one_pow] at *; linarith
    have hd : Itv.Mem (dq t) ⟨-2 / a ^ 3 + 2 / (1 - a) ^ 3, -2 / b ^ 3 + 2 / (1 - b) ^ 3⟩ := by
      have e : dq t = -2 * (1 / t) ^ 3 + 2 * (1 / (1 - t)) ^ 3 := by
        unfold dq; simp only [div_pow, one_pow]; ring
      constructor <;> simp only <;> push_cast <;> rw [e]
      · have := pow_le_pow_left₀ (by positivity) i2 3
        have := pow_le_pow_left₀ p3 i3 3
        have ea : -2 / (a : ℝ) ^ 3 + 2 / (1 - (a : ℝ)) ^ 3
            = -2 * (1 / (a : ℝ)) ^ 3 + 2 * (1 / (1 - (a : ℝ))) ^ 3 := by
          simp only [div_pow, one_pow]; ring
        rw [ea]; linarith
      · have := pow_le_pow_left₀ p1 i1 3
        have := pow_le_pow_left₀ (by positivity) i4 3
        have eb : -2 / (b : ℝ) ^ 3 + 2 / (1 - (b : ℝ)) ^ 3
            = -2 * (1 / (b : ℝ)) ^ 3 + 2 * (1 / (1 - (b : ℝ))) ^ 3 := by
          simp only [div_pow, one_pow]; ring
        rw [eb]; linarith
    have hr : Itv.Mem ((E - 1) / (E + 1)) ⟨1 - 2 / (1 + e1.1), 1 - 2 / (1 + e2.2)⟩ := by
      have e : (E - 1) / (E + 1) = 1 - 2 / (1 + E) := by field_simp; ring
      rw [e]
      constructor <;> simp only <;> push_cast
      · have : 2 / (1 + E) ≤ 2 / (1 + (e1.1 : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
        linarith
      · have : 2 / (1 + (e2.2 : ℝ)) ≤ 2 / (1 + E) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
        linarith
    have hX := Itv.mem_add hd (Itv.mem_mul (Itv.mem_mul hq hq) hr)
    have hw := w_le_wHi hElo hEhi he0
    -- conclusion
    set X := Itv.add _ (Itv.mul (Itv.mul _ _) _) with hXdef
    have habs : |dq t + qq t * qq t * ((E - 1) / (E + 1))| ≤ ((max |X.lo| |X.hi| : ℚ) : ℝ) := by
      push_cast
      rw [abs_le]
      obtain ⟨hx1, hx2⟩ := hX
      constructor
      · have : -(max |(X.lo : ℝ)| |(X.hi : ℝ)|) ≤ X.lo := by
          have := neg_abs_le (X.lo : ℝ); have := le_max_left |(X.lo : ℝ)| |(X.hi : ℝ)|; linarith
        linarith
      · have : (X.hi : ℝ) ≤ max |(X.lo : ℝ)| |(X.hi : ℝ)| :=
          le_trans (le_abs_self _) (le_max_right _ _)
        linarith
    have h10 := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h10
    unfold D2
    rw [← hE, abs_mul, abs_of_nonneg (by positivity : 0 ≤ E / (1 + E) ^ 2),
      show qq t ^ 2 = qq t * qq t by ring]
    calc E / (1 + E) ^ 2 * |dq t + qq t * qq t * ((E - 1) / (E + 1))|
        ≤ (wHi e1.1 e2.2 : ℝ) * ((max |X.lo| |X.hi| : ℚ) : ℝ) :=
          mul_le_mul hw habs (abs_nonneg _) (le_trans (by positivity) hw)
      _ ≤ 10 := by push_cast; linarith
  · cases h

end BSCert.Consts
