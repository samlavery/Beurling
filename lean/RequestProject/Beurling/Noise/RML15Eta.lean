module

public import RequestProject.Beurling.Model.NTEta
public import RequestProject.Beurling.Model.MarginSteps
public import RequestProject.Beurling.Model.MarginMine
public import RequestProject.Beurling.Noise.RML14Sw
public import RequestProject.Beurling.Noise.RML7Eta
public import RequestProject.Beurling.BaseRange.Window

/-!
# The field `hη` of Step 4 (Proposition 5.38): `log t · η_V(t) ≤ s_η`

`η_V(t) = ½ sup_{|h| ≤ 1.01 H(t)} G(t, h)` (`BModel.ηVc`), where `G` is the filter switching
plus `|ΔNT_pt|`. Filter switching costs `≤ 2η(t+h)` (`KR.RML14.sw_le`), and
`|NT_pt(y)| ≤ 2η(y)` (eq. (NT), `BModel.NTpt_abs_le_eta`), so `G(t,h) ≤ 4η(t+h) + 2η(t)`. With
the pointwise τ-near bound `log y · η(y) ≤ 831200 Φ₂(X₀⁻/2)` (`KR.TNP.logy_eta_le`, at heights
`y ≤ b + 1.01H(b)`, inside the (H_BS) horizon `Zc b`) this gives
`log t · η_V(t) ≤ s_η := 4987200 Φ₂(X₀⁻/2) ≤ 4987200 e^{-200}` (`sηc_tiny`).
-/

@[expose] public section

open Real Finset BModel

namespace BModel.RML15

variable {θ : ℝ} {X₀ : ℕ}

variable (X₀) in
/-- `s_η = 4987200 Φ₂(X₀⁻/2)`. -/
noncomputable def sηc : ℝ := 4987200 * KR.TNP.Phi (Queue6.Hc X₀) 2 (Xm X₀ / 2)

/-- `log t ≤ 2 log s` for `s ≥ 0.899 t`, `s ≥ 3`. -/
lemma log_le_two_log {t s : ℝ} (ht : 0 < t) (hs : 0.899 * t ≤ s) (hs3 : 3 ≤ s) :
    Real.log t ≤ 2 * Real.log s := by
  have hs0 : 0 < s := by linarith
  have h1 : Real.log t - Real.log s ≤ t / s - 1 := by
    rw [← Real.log_div ht.ne' hs0.ne']; exact Real.log_le_sub_one_of_pos (div_pos ht hs0)
  have h2 : t / s ≤ 1 / 0.899 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]; linarith
  have h3 : (1 : ℝ) ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]
    have := Real.exp_one_lt_d9; linarith
  have : (1 : ℝ) / 0.899 - 1 ≤ 1 := by norm_num
  linarith

/-- **The field `hη`**: on `[T₀, b]` (any `T₀ ≥ X₀⁻/2`), `log t · η_V(t) ≤ s_η`. -/
theorem hη_c (hc : Cond θ X₀) (hev : Even X₀) {ω : Construction.JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) η1 η2 ε1
      εT θT)
    (p : Margin.Rec.CP) {T0 : ℝ} (hT0 : Xm X₀ / 2 ≤ T0) :
    ∀ t, T0 ≤ t → t ≤ b → Real.log t * ηVc θ X₀ ω p t ≤ sηc X₀ := by
  intro t ht htb
  set P := PR θ X₀ ω
  set H := Queue6.Hc X₀
  set E : ℝ → ℝ := KR.etaG P H (twR θ X₀ ω) (Xm X₀) (fun _ => 1) with hE
  set A : ℝ := 831200 * KR.TNP.Phi H 2 (Xm X₀ / 2) with hA
  have hW := htnp.width
  have hX := hc.hX
  have hXm7 : (10 : ℝ) ^ 7 ≤ Xm X₀ := htnp.hbs.X0m_ge
  have hXZ : Xm X₀ ≤ Zc X₀ b := Xm_le_Zc' hc b
  have hZ0 : (2500 : ℝ) ≤ Zc X₀ b := by linarith
  have hmono := KR.WidthReal.Hc_mono hX
  have hH0 : ∀ z, 0 ≤ H z := fun z => (KR.WidthReal.Hc_pos hX z).le
  have htXm : Xm X₀ / 2 ≤ t := le_trans hT0 ht
  have ht0 : 0 < t := by linarith
  have hHt : H t ≤ t / 10 := hW.small t htXm
  have hHb : H t ≤ H b := hmono htb
  have hb0 : 0 ≤ b := by linarith
  have h18 := Zc_18 hc hb
  have hsq : 18 * (b + H b) ≤ Zc X₀ b ^ 2 := by
    have hXm0 : 0 < Xm X₀ := by linarith
    rw [div_le_iff₀ hXm0] at h18
    nlinarith [hH0 b]
  -- the τ-near bound at a height `s` near `t`
  have hE0 : ∀ z, 0 ≤ E z := fun z => KR.RML6K.etaG_one_nonneg z
  have hEs : ∀ s, 0.899 * t ≤ s → s ≤ b + 1.01 * H b → Real.log t * E s ≤ 2 * A := by
    intro s hs1 hs2
    have hs3 : 3 ≤ s := by linarith
    have h9 : 9 * s ≤ Zc X₀ b ^ 2 := by nlinarith [hH0 b]
    have hl := KR.TNP.logy_eta_le htnp (by linarith) hZ0 h9
    have hlt := log_le_two_log ht0 hs1 hs3
    have hls : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    calc Real.log t * E s ≤ 2 * Real.log s * E s := mul_le_mul_of_nonneg_right hlt (hE0 s)
      _ = 2 * (Real.log s * E s) := by ring
      _ ≤ 2 * A := by linarith
  have hlt0 : 0 < Real.log t := Real.log_pos (by linarith)
  -- the switching expression
  have hG : ∀ h, |h| ≤ 1.01 * H t → Gsw θ X₀ ω p t h ≤ 12 * A / Real.log t := by
    intro h hh
    have hh1 := abs_le.mp hh
    have hs1 : 0.899 * t ≤ t + h := by linarith
    have hs2 : t + h ≤ b + 1.01 * H b := by nlinarith
    have hsw := KR.RML14.sw_le (P := P) (tw := twR θ X₀ ω) hW.RH (by linarith [hW.eps_le])
      hmono hW.X0m_pos (KR.Chain.p_ge_two_of htnp hXZ) (hρ0_c hc ω)
      (fun z => ⟨rhoT_nonneg ω z, rhoT_le_two hc hev ω z⟩) (Margin.Rec.Fset P p t)
      (fun w hw => by
        obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
        obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hw1
        exact ⟨hw2, e, rfl⟩) (by linarith) hh
    have hN1 := NTpt_abs_le_eta hc hev ω (t + h)
    have hN2 := NTpt_abs_le_eta hc hev ω t
    have e1 := hEs (t + h) hs1 hs2
    have e2 := hEs t (by linarith) (by nlinarith [hH0 b])
    have hG' : Gsw θ X₀ ω p t h ≤ 4 * E (t + h) + 2 * E t := by
      unfold Gsw
      have := (abs_sub (NTpt θ X₀ ω (t + h)) (NTpt θ X₀ ω t))
      linarith
    rw [le_div_iff₀ hlt0]
    have := mul_le_mul_of_nonneg_right hG' hlt0.le
    nlinarith
  have hsup : Margin.RML6.supW (Gsw θ X₀ ω p t) (1.01 * H t) ≤ 12 * A / Real.log t :=
    KR.RML14.supW_le (by nlinarith [hH0 t]) hG
  unfold ηVc
  have : Real.log t * (1 / 2 * Margin.RML6.supW (Gsw θ X₀ ω p t) (1.01 * Queue6.Hc X₀ t)) ≤
      Real.log t * (1 / 2 * (12 * A / Real.log t)) :=
    mul_le_mul_of_nonneg_left (by linarith) hlt0.le
  have e : Real.log t * (1 / 2 * (12 * A / Real.log t)) = sηc X₀ := by
    unfold sηc; rw [hA]; field_simp; ring
  linarith

/-- `T₀ = c_∞ + K_c ≥ X₀⁻/2` for the canonical recursion parameter. -/
lemma canonP_T0_ge (hc : Cond θ X₀) (εH ES j : ℝ) :
    Xm X₀ / 2 ≤ (RML7.canonP X₀ εH ES j).cinf + (RML7.canonP X₀ εH ES j).Kc := by
  have hK := RML7.canonP_Kc_nonneg (X₀ := X₀) (εH := εH) (ES := ES) (j := j) hc.hX
  have hXm : 0 ≤ Xm X₀ := by linarith [Queue6.Xm_pos hc]
  show Xm X₀ / 2 ≤ 1.21 * (Xm X₀ / 2) + (RML7.canonP X₀ εH ES j).Kc
  linarith

/-- **The field `hη` at the canonical parameter** `p = canonP X₀ εH ES j`. -/
theorem hη_canon (hc : Cond θ X₀) (hev : Even X₀) {ω : Construction.JitterΩ} {b : ℝ}
    (hb : (X₀ : ℝ) ≤ b) {η1 η2 εT θT : ℝ} {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) (Zc X₀ b) η1 η2 ε1
      εT θT) (εH ES j : ℝ) :
    ∀ t, (RML7.canonP X₀ εH ES j).cinf + (RML7.canonP X₀ εH ES j).Kc ≤ t → t ≤ b →
      Real.log t * ηVc θ X₀ ω (RML7.canonP X₀ εH ES j) t ≤ sηc X₀ :=
  hη_c hc hev hb htnp _ (canonP_T0_ge hc εH ES j)

/-- `s_η ≤ 4987200 e^{-200}`. -/
theorem sηc_tiny (hc : Cond θ X₀) {ω : Construction.JitterΩ} {Z η1 η2 εT θT : ℝ}
    {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT) :
    sηc X₀ ≤ 4987200 * Real.exp (-200) := by
  have := KR.WidthReal.Phi_tiny htnp (KR.WidthReal.Hc_Xm_half_le hc.hX) (a := 2) (by norm_num)
  unfold sηc; linarith

/-- **`hsize`** given `so ≤ 0.0012`: `so + 2 s_η ≤ 0.0013`. -/
theorem hsize_of (hc : Cond θ X₀) {ω : Construction.JitterΩ} {Z η1 η2 εT θT : ℝ}
    {ε1 : ℝ → ℝ}
    (htnp : KR.TNP.Hyp (PR θ X₀ ω) (Queue6.Hc X₀) (twR θ X₀ ω) (Xm X₀) Z η1 η2 ε1 εT θT)
    {so : ℝ} (hso : so ≤ 0.0012) : so + 2 * sηc X₀ ≤ 0.0013 := by
  have h1 := sηc_tiny hc htnp
  have h2 : Real.exp (-200) ≤ 1 / 10 ^ 60 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h1e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have e : Real.exp 200 = Real.exp 1 ^ 200 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2 : ℝ) ^ 200 ≤ Real.exp 1 ^ 200 := pow_le_pow_left₀ (by norm_num) h1e 200
    have h4 : (1 / (1 / 10 ^ 60 : ℝ)) ≤ 2 ^ 200 := by norm_num
    rw [e]; simpa using h4.trans h3
  nlinarith

end BModel.RML15

end
