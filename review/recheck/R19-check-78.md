# R19: independent check of correction #78 (E3/E3′ timing)

**Who checked, and on what.** The checker was a fresh agent that did not write the repair. It worked on a snapshot of the tree
that had #78 applied but not committed, against HEAD 5c47a85.

**Verdict.** #78 is CONFIRMED WITH FIXES:
- no BLOCKING finding;
- two FIXABLE findings, F1 (introduced by #78) and F2 (pre-existing);
- seven COSMETIC findings, F3–F9.

All have been applied. F2 was already fixed by #79, which extended Corollary increment to |I| ≤ 2H(u).

## 1. Definitions
Every old use was rewritten: G_u^NV, G_u^sw, "closes", "per-scale noise event", and "internally ordered … strictly earlier
windows". Checked locations: 04d, 04g, 05 (Def good, the Table, (∗), first failure, summation) and 01 (N1)/(N2). No remaining
text treats E3 or E3′ as a single whole-scale event.

## 2. t(W) = max W and measurability (verified)
- **Prime bound.** C^(1) has q ≤ b/2, because every cofactor w ≥ 2. C^(≥2) has q ≤ √b.
- **Decision slot.** Each prime is decided by slot s ≤ b/2 + 0.51H(b/2).
- **Abs elements.** Abs membership is fixed at the latest prime, and Abs elements are excluded from both C_jit and Comp.
- **Rigid elements.** Elements with a rational latest prime are rigid.
- **Compensator increments.** Each increment is |box_j ∩ W/w|/H(s_j)·P_j. Here P_j, s_j and s_{j+1} are 𝓕_{s_j−}-measurable
  (Lemma C2, Lemma adapted).
- **Conclusion.** E3_W ∈ 𝓕_{b/2 + 0.51H(b/2)} ⊂ 𝓕_b. The cofactor w = 2 makes b/2 essentially sharp, and t(W) = b leaves room.

## 3. E3_W's own bound (verified)
- **Inputs.** It reads E_cl^(u) (time < u ≤ t(W)), V_W ≤ 2M₁Comp(W), ρ̃ ≤ 1.01, Lemma S(i) ((H_BS) on [1, 4u/X₀]),
  |NT_pt| ≤ 2.02(log y + B₁), and (s2) via smooth-v.
- **Ordering.** All of these lie far below the horizon ž(t(W)), and none of them is a window event.
- **Constant.** 8e⁻²(1+1/u)(1.03+2/H) ≈ 1.115 ≤ 1.2.

## 4. Consumers (all verified)
Each consumer reads only E3_W events that are already on its good event:

| Consumer | Condition checked |
|---|---|
| ν(y) | t(W) ≤ y + H/2 + 1 < y + H(y) |
| Lemma predictable | y + H ≤ x/2 + 3H < x |
| Prop g1(B) | J reaches only y + H ≤ x − x^{0.98} + H < x |
| Prop pointwise | max I + H(u) ≤ t/2 + 3.2H(t/2) < t |
| Cor r1 / E2 | reads E3_W with t(W) ≪ max I; E3_W never reads E2, so there is no cycle |
| Dyadic crossings | handled by additive splitting |

## 5. Stopping time (verified)
- **Well-definedness.** There are countably many events and the set of times is locally finite, so Good(<t) and τ are well
  defined.
- **Shared times.** No E3_W reads an event of its own time.
- **Budget.** The total is 1.443/Λ + 4.3X₀⁻² ≤ 1.5/Λ.

## 6. Rendering
- 15 overfull boxes, the same widths as HEAD.
- 0 undefined references.
- No `%` mid-line.
- All 67 added lines appear in the pdftotext output.

## Findings (all applied)
- **F1 (FIXABLE, from #78).** The E3_W bound was said to read only E_cl and "sure facts". It also reads (H_BS) on
  [1, 4u/X₀], below the horizon. The text in 04d and 05 now says so, and names the crude η bound used for |NT_pt|.
- **F2 (FIXABLE, pre-existing).** Corollary increment covered only |I| ≤ H(u), but the E3 windows have length up to
  1.03H + 1. #79 extended the cap to 2H(u) in the corollary and in the 04d input bullet.
- **F3 (COSMETIC).** (N2) is rewritten in terms of Lemma noise's good event and the window times. This also removes an
  undefined v.
- **F4 (COSMETIC).** Prop pointwise Step 3 now states Good(<t) ⊂ Good(<max I + H(u)).
- **F5 (COSMETIC).** The shorthands G^NV and G^sw are noted as unused.
- **F6 (COSMETIC).** The Comp^(2) box condition reads (W/m)^{1/a} ⊂ [0, √b].
- **F7 (COSMETIC, pre-existing).** W⁻ lies in 𝒲′_u, and only W⁺ lies in 𝒲_u.
- **F8 (COSMETIC).** The t(E) column of Table events now shows max W.
- **F9 (COSMETIC, pre-existing).** Windows that straddle a dyadic point are split additively in Prop pointwise Step 1.
