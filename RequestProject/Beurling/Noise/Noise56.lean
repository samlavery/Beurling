module

public import Mathlib

/-!
# Lemma 5.22 (per-scale noise): the deterministic part of the proof

Lemma 5.22 (04d-noise.tex, `lem:noise`) bounds the noise `ν(y)` of the margin identity and the
interval error `E(I) = σ(I) - ∫_I m` at a dyadic scale `u`, on the good event. Its proof combines
the following inputs, which concern the random construction and are not formalized; here they
are hypotheses on real numbers, each stated as the proof uses it:

* the margin identity (margin-identity): `H(y) ν(y) = Mart(W_y) + Mart⁽²⁾(W_y) - ΔQ(W_y)
  - E_edge(W_y) + Comp⁽²⁾(W_y) + E_box(y)`, with `|E_box| ≤ 2.01`;
* the queue bounds `|ΔQ| ≤ Q_max`, `|E_edge| ≤ 1 + Q_max`, `Q_max ≤ B(u)` (Theorem 6.6);
* `0 ≤ Comp⁽²⁾(W) ≤ s₂(u) |W|` (eq. (s2));
* the sandwich `W⁻ ⊂ W_y ⊂ W⁺` in `𝒲'_u`: `Mart(W⁻) - C ≤ Mart(W_y) ≤ Mart(W⁺) + C` with
  `0 ≤ C ≤ 100 log(2u)`, and the same for `Mart⁽²⁾` with `2s₂` in place of `100 log(2u)`;
* the Freedman events `E3_W` for `W = W^±`: (F1) `|Mart(W)| ≤ √(2 V̄_W λ') + (4/3) M₁ λ'` with
  `V̄_W = 2M₁ · 50 log(2u) · |W|`, and (F2) `|Mart⁽²⁾(W)| ≤ √(2 V̄²_W λ') + (2/3) b₂ λ'` with
  `V̄²_W = b₂ s₂ |W|`, `b₂ = 2 A_u M₁`, and `|W^±| ≤ 1.03 H(u) + 1`.

From these, `nu_bound_block` proves `|ν(y)| ≤ ν₀(u)` for a window inside one dyadic block, and
`nu_bound_cross` the bound `2.05 max ν₀(u')` when `W_y` is split between two blocks. For the
interval error, `EI_bound_slot` proves the displayed bound for a slot window (from the bookkeeping
identity `σ(I) = ∫_I m - Comp⁽²⁾(I) - Mart(I) - Mart⁽²⁾(I) + ΔQ(I) ± 2`) and `EI_bound_phys` the
bound for a physical interval (with the two partial cells, `|E(I) - E(I°)| ≤ 1 + 22.4 log(2u) ·
(3.1 log(2u) + 4.2) ≤ 70 log²(2u)`).
-/

@[expose] public section

open Real

namespace Noise56

/-- `ν₀(u)` of Lemma 5.22, with `H = H(u)`, `λ' = λ'_u`, `L₂ = log(2u)`, `A = A_u`, `s₂ = s₂(u)`. -/
noncomputable def nu0 (H M1 lam L2 B A s2 : ℝ) : ℝ :=
  √(206 * M1 * lam * L2 / H) * (1 + 1 / H) + √(4.2 * A * M1 * s2 * lam / H)
    + (4 / 3 * (1 + A) * M1 * lam + 3 * B + 100 * L2 + 6) / H + 1.1 * s2

/-- `√(200 X (1.03 H + 1)) ≤ H (1 + 1/H) √(206 X / H)`. -/
lemma sqrt_F1_le {X H : ℝ} (hX : 0 ≤ X) (hH : 0 < H) :
    √(200 * X * (1.03 * H + 1)) ≤ H * ((1 + 1 / H) * √(206 * X / H)) := by
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have e : H ^ 2 * ((1 + 1 / H) ^ 2 * (206 * X / H)) = 206 * X * (H + 2 + 1 / H) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ 206 * X * (1 / H) := by positivity
  nlinarith

/-- `√(4 Y (1.03 H + 1)) ≤ H √(4.2 Y / H)` for `H ≥ 50`. -/
lemma sqrt_F2_le {Y H : ℝ} (hY : 0 ≤ Y) (hH : 50 ≤ H) :
    √(4 * Y * (1.03 * H + 1)) ≤ H * √(4.2 * Y / H) := by
  have hH0 : 0 < H := by linarith
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e : H ^ 2 * (4.2 * Y / H) = 4.2 * Y * H := by field_simp
  rw [e]
  nlinarith

/-- (F1) at a window of length `W ≤ 1.03 H + 1`. -/
lemma F1_le {M1 lam L2 W H Mt : ℝ} (hM : 0 ≤ M1) (hl : 0 ≤ lam) (hL : 0 ≤ L2) (_hW0 : 0 ≤ W)
    (hW : W ≤ 1.03 * H + 1) (hH : 0 < H)
    (hF : |Mt| ≤ √(2 * (2 * M1 * (50 * L2) * W) * lam) + 4 / 3 * M1 * lam) :
    |Mt| ≤ H * ((1 + 1 / H) * √(206 * M1 * lam * L2 / H)) + 4 / 3 * M1 * lam := by
  have hX : 0 ≤ M1 * lam * L2 := by positivity
  have h1 : √(2 * (2 * M1 * (50 * L2) * W) * lam) ≤ √(200 * (M1 * lam * L2) * (1.03 * H + 1)) := by
    apply Real.sqrt_le_sqrt
    have : 2 * (2 * M1 * (50 * L2) * W) * lam = 200 * (M1 * lam * L2) * W := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  have h2 := sqrt_F1_le hX hH
  have e : 206 * (M1 * lam * L2) / H = 206 * M1 * lam * L2 / H := by ring
  rw [e] at h2
  linarith

/-- (F2) at a window of length `W ≤ 1.03 H + 1`, `b₂ = 2AM₁`. -/
lemma F2_le {M1 lam A s2 W H Mt : ℝ} (hM : 0 ≤ M1) (hl : 0 ≤ lam) (hA : 0 ≤ A) (hs : 0 ≤ s2)
    (_hW0 : 0 ≤ W) (hW : W ≤ 1.03 * H + 1) (hH : 50 ≤ H)
    (hF : |Mt| ≤ √(2 * (2 * A * M1 * s2 * W) * lam) + 2 / 3 * (2 * A * M1) * lam) :
    |Mt| ≤ H * √(4.2 * A * M1 * s2 * lam / H) + 4 / 3 * A * M1 * lam := by
  have hY : 0 ≤ A * M1 * s2 * lam := by positivity
  have h1 : √(2 * (2 * A * M1 * s2 * W) * lam) ≤ √(4 * (A * M1 * s2 * lam) * (1.03 * H + 1)) := by
    apply Real.sqrt_le_sqrt
    have : 2 * (2 * A * M1 * s2 * W) * lam = 4 * (A * M1 * s2 * lam) * W := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  have h2 := sqrt_F2_le hY hH
  have e : 4.2 * (A * M1 * s2 * lam) / H = 4.2 * A * M1 * s2 * lam / H := by ring
  rw [e] at h2
  linarith

set_option maxHeartbeats 400000 in
/-- **Lemma 5.22, the bound on `ν`, for a window inside one dyadic block**: from the margin
identity, the queue bounds, (s2), the sandwich and (F1), (F2) (see the module docstring),
`|ν(y)| ≤ ν₀(u)`. Here `Hy = H(y) ≥ Hu = H(u) ≥ 50`. -/
theorem nu_bound_block {Hy Hu M1 lam L2 B A s2 ν Mart Mart2 dQ Eedge Comp2 Ebox Qm
      Mm Mp M2m M2p C1 C2 Wm Wp : ℝ}
    (hHu : 50 ≤ Hu) (hHy : Hu ≤ Hy) (hM : 0 ≤ M1) (hl : 0 ≤ lam) (hL : 0 ≤ L2) (hA : 0 ≤ A)
    (hs : 0 ≤ s2)
    (hid : Hy * ν = Mart + Mart2 - dQ - Eedge + Comp2 + Ebox)
    (hEbox : |Ebox| ≤ 2.01) (hdQ : |dQ| ≤ Qm) (hEe : |Eedge| ≤ 1 + Qm) (hQm : Qm ≤ B)
    (hC0 : 0 ≤ Comp2) (hC : Comp2 ≤ s2 * Hy)
    (hS1 : Mm - C1 ≤ Mart ∧ Mart ≤ Mp + C1) (hC1 : 0 ≤ C1 ∧ C1 ≤ 100 * L2)
    (hS2 : M2m - C2 ≤ Mart2 ∧ Mart2 ≤ M2p + C2) (hC2 : 0 ≤ C2 ∧ C2 ≤ 2 * s2)
    (hWm : 0 ≤ Wm ∧ Wm ≤ 1.03 * Hu + 1) (hWp : 0 ≤ Wp ∧ Wp ≤ 1.03 * Hu + 1)
    (hF1m : |Mm| ≤ √(2 * (2 * M1 * (50 * L2) * Wm) * lam) + 4 / 3 * M1 * lam)
    (hF1p : |Mp| ≤ √(2 * (2 * M1 * (50 * L2) * Wp) * lam) + 4 / 3 * M1 * lam)
    (hF2m : |M2m| ≤ √(2 * (2 * A * M1 * s2 * Wm) * lam) + 2 / 3 * (2 * A * M1) * lam)
    (hF2p : |M2p| ≤ √(2 * (2 * A * M1 * s2 * Wp) * lam) + 2 / 3 * (2 * A * M1) * lam) :
    |ν| ≤ nu0 Hu M1 lam L2 B A s2 := by
  have hHu0 : 0 < Hu := by linarith
  have hHy0 : 0 < Hy := by linarith
  have a1 := F1_le hM hl hL hWm.1 hWm.2 hHu0 hF1m
  have a2 := F1_le hM hl hL hWp.1 hWp.2 hHu0 hF1p
  have b1 := F2_le hM hl hA hs hWm.1 hWm.2 hHu hF2m
  have b2 := F2_le hM hl hA hs hWp.1 hWp.2 hHu hF2p
  obtain ⟨S1, hS1d⟩ : ∃ S, S = √(206 * M1 * lam * L2 / Hu) := ⟨_, rfl⟩
  obtain ⟨S2, hS2d⟩ : ∃ S, S = √(4.2 * A * M1 * s2 * lam / Hu) := ⟨_, rfl⟩
  rw [← hS1d] at a1 a2
  rw [← hS2d] at b1 b2
  have hS1n : 0 ≤ S1 := hS1d ▸ Real.sqrt_nonneg _
  have hS2n : 0 ≤ S2 := hS2d ▸ Real.sqrt_nonneg _
  rw [abs_le] at a1 a2 b1 b2 hEbox hdQ hEe
  -- the numerator, without `Comp⁽²⁾`
  obtain ⟨K, hK⟩ : ∃ K, K = Hu * ((1 + 1 / Hu) * S1) + Hu * S2 + 4 / 3 * M1 * lam
      + 4 / 3 * A * M1 * lam + 3 * B + 100 * L2 + 6 + 2 * s2 := ⟨_, rfl⟩
  have hN : |Mart + Mart2 - dQ - Eedge + Ebox| ≤ K := by
    rw [abs_le]
    constructor
    · linarith only [hS1.1, hS2.1, hC1.2, hC2.2, a1.1, b1.1, hdQ.1, hdQ.2, hEe.2, hEbox.1,
        hQm, hK]
    · linarith only [hS1.2, hS2.2, hC1.2, hC2.2, a2.2, b2.2, hdQ.1, hdQ.2, hEe.1, hEbox.2,
        hQm, hK]
  have hnu : |ν| ≤ K / Hy + s2 := by
    have e : ν = (Mart + Mart2 - dQ - Eedge + Ebox) / Hy + Comp2 / Hy := by
      field_simp; linarith
    rw [e]
    calc |(Mart + Mart2 - dQ - Eedge + Ebox) / Hy + Comp2 / Hy|
        ≤ |(Mart + Mart2 - dQ - Eedge + Ebox) / Hy| + |Comp2 / Hy| := abs_add_le _ _
      _ ≤ K / Hy + s2 := by
          rw [abs_div, abs_of_pos hHy0, abs_div, abs_of_nonneg hC0, abs_of_pos hHy0]
          gcongr
          rw [div_le_iff₀ hHy0]; exact hC
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hN
  have hKy : K / Hy ≤ K / Hu := div_le_div_of_nonneg_left hK0 hHu0 hHy
  have eK : K / Hu = (1 + 1 / Hu) * S1 + S2 +
      (4 / 3 * (1 + A) * M1 * lam + 3 * B + 100 * L2 + 6) / Hu + 2 * s2 / Hu := by
    rw [hK]; field_simp; ring
  have hs2 : 2 * s2 / Hu ≤ 0.1 * s2 := by
    rw [div_le_iff₀ hHu0]; nlinarith
  rw [eK] at hKy
  have hg : nu0 Hu M1 lam L2 B A s2 = (1 + 1 / Hu) * S1 + S2 +
      (4 / 3 * (1 + A) * M1 * lam + 3 * B + 100 * L2 + 6) / Hu + 1.1 * s2 := by
    unfold nu0; rw [← hS1d, ← hS2d]; ring
  rw [hg]
  linarith

/-- **Lemma 5.22, a window crossing a block boundary**: if `H(y) ν = N₁ + N₂` with
`|N_i| ≤ H(u_i) ν₀(u_i)` and `H(u_i) ≤ 1.02 H(y)` ((RH)), then `|ν| ≤ 2.05 max(ν₀(u₁), ν₀(u₂))`. -/
theorem nu_bound_cross {Hy H1 H2 n1 n2 ν N1 N2 : ℝ} (hHy : 0 < Hy)
    (hid : Hy * ν = N1 + N2) (h1 : |N1| ≤ H1 * n1) (h2 : |N2| ≤ H2 * n2)
    (hH1 : 0 ≤ H1 ∧ H1 ≤ 1.02 * Hy) (hH2 : 0 ≤ H2 ∧ H2 ≤ 1.02 * Hy) (hn1 : 0 ≤ n1)
    (hn2 : 0 ≤ n2) : |ν| ≤ 2.05 * max n1 n2 := by
  have hm1 := le_max_left n1 n2
  have hm2 := le_max_right n1 n2
  have hb : |Hy * ν| ≤ 2.04 * Hy * max n1 n2 := by
    rw [hid]
    calc |N1 + N2| ≤ |N1| + |N2| := abs_add_le _ _
      _ ≤ H1 * n1 + H2 * n2 := add_le_add h1 h2
      _ ≤ 1.02 * Hy * max n1 n2 + 1.02 * Hy * max n1 n2 := by
          apply add_le_add <;> apply mul_le_mul <;> linarith
      _ = 2.04 * Hy * max n1 n2 := by ring
  rw [abs_mul, abs_of_pos hHy] at hb
  have : |ν| ≤ 2.04 * max n1 n2 := by
    have := hb; nlinarith
  have : 0 ≤ max n1 n2 := le_trans hn1 hm1
  linarith

/-- **Lemma 5.22, the interval error on a slot window** `I` of length `|I|`: from the
bookkeeping identity `σ(I) - ∫_I m = -Comp⁽²⁾(I) - Mart(I) - Mart⁽²⁾(I) + ΔQ(I) + e`, `|e| ≤ 2`,
`|ΔQ(I)| ≤ B(u)`, `0 ≤ Comp⁽²⁾(I) ≤ s₂|I|`, the sandwich between windows of length `≤ |I| + 2`
and (F1), (F2) there. -/
theorem EI_bound_slot {M1 lam L2 B A s2 I E Mart Mart2 dQ Comp2 e Mm Mp M2m M2p C1 C2 Wm Wp : ℝ}
    (hM : 0 ≤ M1) (hl : 0 ≤ lam) (hL : 0 ≤ L2) (hA : 0 ≤ A) (hs : 0 ≤ s2) (_hI : 0 ≤ I)
    (hid : E = -Comp2 - Mart - Mart2 + dQ + e) (he : |e| ≤ 2) (hdQ : |dQ| ≤ B)
    (hC0 : 0 ≤ Comp2) (hC : Comp2 ≤ s2 * I)
    (hS1 : Mm - C1 ≤ Mart ∧ Mart ≤ Mp + C1) (hC1 : 0 ≤ C1 ∧ C1 ≤ 100 * L2)
    (hS2 : M2m - C2 ≤ Mart2 ∧ Mart2 ≤ M2p + C2) (hC2 : 0 ≤ C2 ∧ C2 ≤ 2 * s2)
    (hWm : 0 ≤ Wm ∧ Wm ≤ I + 2) (hWp : 0 ≤ Wp ∧ Wp ≤ I + 2)
    (hF1m : |Mm| ≤ √(2 * (2 * M1 * (50 * L2) * Wm) * lam) + 4 / 3 * M1 * lam)
    (hF1p : |Mp| ≤ √(2 * (2 * M1 * (50 * L2) * Wp) * lam) + 4 / 3 * M1 * lam)
    (hF2m : |M2m| ≤ √(2 * (2 * A * M1 * s2 * Wm) * lam) + 2 / 3 * (2 * A * M1) * lam)
    (hF2p : |M2p| ≤ √(2 * (2 * A * M1 * s2 * Wp) * lam) + 2 / 3 * (2 * A * M1) * lam) :
    |E| ≤ √(200 * M1 * lam * L2 * (I + 2)) + √(4 * A * M1 * s2 * lam * (I + 2))
      + 4 / 3 * (1 + A) * M1 * lam + B + 100 * L2 + s2 * (I + 2) + 2 := by
  have hmono1 : ∀ W, 0 ≤ W → W ≤ I + 2 →
      √(2 * (2 * M1 * (50 * L2) * W) * lam) ≤ √(200 * M1 * lam * L2 * (I + 2)) := by
    intro W h0 hW
    apply Real.sqrt_le_sqrt
    have : 2 * (2 * M1 * (50 * L2) * W) * lam = 200 * M1 * lam * L2 * W := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hW (by positivity)
  have hmono2 : ∀ W, 0 ≤ W → W ≤ I + 2 →
      √(2 * (2 * A * M1 * s2 * W) * lam) ≤ √(4 * A * M1 * s2 * lam * (I + 2)) := by
    intro W h0 hW
    apply Real.sqrt_le_sqrt
    have : 2 * (2 * A * M1 * s2 * W) * lam = 4 * A * M1 * s2 * lam * W := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hW (by positivity)
  have a1 := hmono1 Wm hWm.1 hWm.2
  have a2 := hmono1 Wp hWp.1 hWp.2
  have b1 := hmono2 Wm hWm.1 hWm.2
  have b2 := hmono2 Wp hWp.1 hWp.2
  rw [abs_le] at hF1m hF1p hF2m hF2p he hdQ ⊢
  constructor <;> nlinarith [hS1.1, hS1.2, hS2.1, hS2.2, hC1.2, hC2.2, hC1.1, hC2.1]

/-- **Lemma 5.22, physical intervals**: the two partial cells, of length `≤ 11.2 log(2u)` each,
on which `|m| ≤ 3.1 log(2u) + 4.2`, and the at most one extra prime, change `E(I)` by at most
`1 + 22.4 log(2u) (3.1 log(2u) + 4.2) ≤ 70 log²(2u)` (for `log(2u) ≥ 10⁸`). -/
theorem EI_phys_correction {L2 dσ dm : ℝ} (hL : 100000000 ≤ L2) (hσ : |dσ| ≤ 1)
    (hm : |dm| ≤ 22.4 * L2 * (3.1 * L2 + 4.2)) : |dσ - dm| ≤ 70 * L2 ^ 2 := by
  calc |dσ - dm| ≤ |dσ| + |dm| := abs_sub _ _
    _ ≤ 1 + 22.4 * L2 * (3.1 * L2 + 4.2) := add_le_add hσ hm
    _ ≤ 70 * L2 ^ 2 := by nlinarith

end Noise56

end
