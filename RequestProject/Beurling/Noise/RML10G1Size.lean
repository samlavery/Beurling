module

public import RequestProject.Beurling.Noise.RML9G1

/-!
# The sizes of `ε_N` at the Model's concrete bounds (Proposition 5.35(B), Lemma 5.34)

The Model defines the two bullets of Lemma 5.34 by
`a(z) = aK(C_N, S(z), H_c, z) = 5.1 C_N S(z) log z/log(z - H(z)/2)` and
`b(z) = 35.8 C_N · 10 · G(z)`, where `S = SK θ X₀ ω nb` and
`G(z) = ∑_{i ≤ Jc z} (log 3v_i)² (o_i + F̄_r(i))` (`Model/FrBound.lean`, `Model/RestG.lean`).
`hsize_of` turns block bounds `S ≤ S_b`, `G ≤ G_b` on `J` into the field `hsize` of
`KR.RML9.G1ResSec5`, with `CN = C_N`, `SK = S_b`, `SG = G_b` and
`h6 = h₆' + (5.1 C_N S_b + 358 C_N G_b) · log 4/(log y - log 4)`; `h6_le` checks
`h6 ≤ 10⁻²⁰` from `h₆' ≤ 5·10⁻²¹` (the term `6 log y/H(z)`), `S_b ≤ 10⁻²⁰`,
`G_b ≤ e^{-41} + 2·10⁻²²` and `log y ≥ 10⁸`.
-/

@[expose] public section

open Real Set

namespace KR.RML10

/-- `1/(L - c) = (1 + c/(L - c))/L`. -/
lemma inv_sub_eq {L c : ℝ} (hL : 0 < L) (hLc : 0 < L - c) :
    1 / (L - c) = (1 + c / (L - c)) / L := by
  field_simp; ring

/-- **The field `hsize`** at the concrete bounds `a = aK(C_N, S, H, ·)`, `b = 358 C_N G`. -/
theorem hsize_of {H : ℝ → ℝ} {S G : ℝ → ℝ} {CN Sb Gb h6' y : ℝ} {Jset : Set ℝ}
    (hCN : 0 ≤ CN) (hly : Real.log 4 < Real.log y)
    (hS0 : ∀ z ∈ Jset, 0 ≤ S z) (hSb : ∀ z ∈ Jset, S z ≤ Sb)
    (hG0 : ∀ z ∈ Jset, 0 ≤ G z) (hGb : ∀ z ∈ Jset, G z ≤ Gb)
    (hlz : ∀ z ∈ Jset, Real.log y - Real.log 4 ≤ Real.log (z - H z / 2) ∧
      Real.log y - Real.log 4 ≤ Real.log z)
    (hH0 : ∀ z ∈ Jset, 0 < H z)
    (h6 : ∀ z ∈ Jset, 6 * Real.log y / H z ≤ h6') :
    ∀ z ∈ Jset, (KR.RML6K.aK CN (S z) H z + 35.8 * CN * 10 * G z +
        6 * Real.log z / H z) / Real.log z ≤
      (5.1 * CN * Sb + 35.8 * CN * 10 * Gb +
        (h6' + (5.1 * CN * Sb + 35.8 * CN * 10 * Gb) *
          (Real.log 4 / (Real.log y - Real.log 4)))) / Real.log y := by
  intro z hz
  obtain ⟨hl1, hl2⟩ := hlz z hz
  have hc0 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLc : 0 < Real.log y - Real.log 4 := by linarith
  have hL : 0 < Real.log y := by linarith
  have hlzp : 0 < Real.log z := by linarith
  have hlzH : 0 < Real.log (z - H z / 2) := by linarith
  have hSb0 : 0 ≤ Sb := (hS0 z hz).trans (hSb z hz)
  have hGb0 : 0 ≤ Gb := (hG0 z hz).trans (hGb z hz)
  set r := Real.log 4 / (Real.log y - Real.log 4)
  have hr0 : 0 ≤ r := div_nonneg hc0.le hLc.le
  have hinv := inv_sub_eq hL hLc
  -- the three terms
  have t1 : KR.RML6K.aK CN (S z) H z / Real.log z ≤ 5.1 * CN * Sb * (1 + r) / Real.log y := by
    unfold KR.RML6K.aK
    have e : 5.1 * CN * S z * (Real.log z / Real.log (z - H z / 2)) / Real.log z =
        5.1 * CN * S z * (1 / Real.log (z - H z / 2)) := by field_simp
    rw [e]
    have h1 : 1 / Real.log (z - H z / 2) ≤ 1 / (Real.log y - Real.log 4) :=
      one_div_le_one_div_of_le hLc hl1
    rw [hinv] at h1
    have hA : 0 ≤ 5.1 * CN * S z := by have := hS0 z hz; positivity
    calc 5.1 * CN * S z * (1 / Real.log (z - H z / 2))
        ≤ 5.1 * CN * S z * ((1 + r) / Real.log y) := mul_le_mul_of_nonneg_left h1 hA
      _ ≤ 5.1 * CN * Sb * ((1 + r) / Real.log y) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hSb z hz) (by positivity)
      _ = 5.1 * CN * Sb * (1 + r) / Real.log y := by ring
  have t2 : 35.8 * CN * 10 * G z / Real.log z ≤ 35.8 * CN * 10 * Gb * (1 + r) / Real.log y := by
    have h1 : 1 / Real.log z ≤ 1 / (Real.log y - Real.log 4) := one_div_le_one_div_of_le hLc hl2
    rw [hinv] at h1
    have hA : 0 ≤ 35.8 * CN * 10 * G z := by have := hG0 z hz; positivity
    calc 35.8 * CN * 10 * G z / Real.log z = 35.8 * CN * 10 * G z * (1 / Real.log z) := by ring
      _ ≤ 35.8 * CN * 10 * G z * ((1 + r) / Real.log y) := mul_le_mul_of_nonneg_left h1 hA
      _ ≤ 35.8 * CN * 10 * Gb * ((1 + r) / Real.log y) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hGb z hz) (by positivity)
      _ = 35.8 * CN * 10 * Gb * (1 + r) / Real.log y := by ring
  have t3 : 6 * Real.log z / H z / Real.log z ≤ h6' / Real.log y := by
    have hHz := hH0 z hz
    have e : 6 * Real.log z / H z / Real.log z = 6 * Real.log y / H z / Real.log y := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (h6 z hz) hL.le
  rw [add_div, add_div]
  have e : (5.1 * CN * Sb + 35.8 * CN * 10 * Gb +
        (h6' + (5.1 * CN * Sb + 35.8 * CN * 10 * Gb) * r)) / Real.log y =
      5.1 * CN * Sb * (1 + r) / Real.log y + 35.8 * CN * 10 * Gb * (1 + r) / Real.log y +
        h6' / Real.log y := by ring
  rw [e]
  linarith

/-- `h₆ ≤ 10⁻²⁰` for the choice of `hsize_of`. -/
theorem h6_le {CN Sb Gb h6' y : ℝ} (hCN0 : 0 ≤ CN) (hCN : CN ≤ 158) (hSb0 : 0 ≤ Sb)
    (hSb : Sb ≤ 1 / 10 ^ 20) (hGb0 : 0 ≤ Gb) (hGb : Gb ≤ Real.exp (-41) + 2 / 10 ^ 22)
    (hh6 : h6' ≤ 5 / 10 ^ 21) (hly : 100000000 ≤ Real.log y) :
    h6' + (5.1 * CN * Sb + 35.8 * CN * 10 * Gb) *
        (Real.log 4 / (Real.log y - Real.log 4)) ≤ 1 / 10 ^ 20 := by
  have he := KR.RML8E.exp_neg41_le
  have hl4 : Real.log 4 < 1.4 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hl40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hr : Real.log 4 / (Real.log y - Real.log 4) ≤ 2 / 10 ^ 8 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hr0 : 0 ≤ Real.log 4 / (Real.log y - Real.log 4) := div_nonneg hl40.le (by linarith)
  have hA : 5.1 * CN * Sb + 35.8 * CN * 10 * Gb ≤ 5.1 * 158 * (1 / 10 ^ 20) +
      35.8 * 158 * 10 * (1.5632e-18) := by
    have hGb' : Gb ≤ 1.5632e-18 := by linarith
    have t1 : 5.1 * CN * Sb ≤ 5.1 * 158 * (1 / 10 ^ 20) :=
      mul_le_mul (by nlinarith) hSb hSb0 (by norm_num)
    have t2 : 35.8 * CN * 10 * Gb ≤ 35.8 * 158 * 10 * 1.5632e-18 :=
      mul_le_mul (by nlinarith) hGb' hGb0 (by norm_num)
    linarith
  have hA0 : 0 ≤ 5.1 * CN * Sb + 35.8 * CN * 10 * Gb := by positivity
  have := mul_le_mul hA hr hr0 (by norm_num)
  norm_num at this ⊢
  linarith

end KR.RML10

end
