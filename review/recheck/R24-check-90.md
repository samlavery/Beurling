# R24: independent check of correction #90 (start ranges)

**Setup.** The checker was a fresh agent; it did not write the repair. It worked on a snapshot of the working tree after the
#90 repair, based on f841cc1.

**Verdict.** #90: CONFIRMED WITH FIXES.
- Nothing is BLOCKING.
- There are 2 FIXABLE wording items, both introduced by the repair, and 3 COSMETIC items.
- All of them have been applied.

## Verified
1. **Definitions (04k).**
   - The nominal step filter is κ_{d→n} = 1[τ_w < x/n]·1[x/n ≥ X₀⁻]. It is frozen at the nominal point and includes the
     cutoff at X₀⁻.
   - C₁ = δ_x, so TV(C₁) = 1.
   - For y < X₀ and n ≥ 2, y/n < X₀/2 < X₀⁻. So every κ is 0 and C_n^{y,nom} = 0.
   - The true kernels also vanish for n ≥ 2, and in fact for every y < 2X₀⁻.
2. **The bound.**
   - W^nom_y(u) = 1[y ∈ [u, 2u)] ≤ 1 ≤ C_N log(2u)/log y, using C_S = max(2.01·C_BS, 1.4) ≤ 77.
   - C_N ≥ 2.856; numerically C_N = 157.05 ≤ 158.
3. **Prop true-kernels(ii).** S^τ_{n′} carries κ_{X₀} = 1[x/n′ ≥ X₀⁻], so every τ-source start is ≥ X₀⁻. Part (iii) and
   the ∞-norm part introduce no new starts.
4. **Lemma xb with y ≥ 2X₀⁻.** The whole proof was read; none of its inputs needs y ≥ 2X₀. For x ≥ 2X₀, W_x lies about
   0.5H(X₀) above 2X₀⁻.
5. **Prop br with x ≥ 2X₀⁻.** No stronger lower bound is used. At HEAD, Prop pointwise 6(b) also applied Prop br at points
   of W_t below 2X₀; the new range closes that case too.
6. **Sweep.** Every statement with a lower bound on its start or height, checked against every point where it is applied.
   All are fine:
   - Thm bs and Cor saias;
   - Cor kr-weights (a), (b), (c);
   - Lemma S and Lemma tau-near;
   - Prop true-kernels;
   - Lemma xb and Prop xb-ranges;
   - Lemma si;
   - Prop br and Lemma predictable;
   - Prop g1, Thm g2 and Prop pointwise;
   - Lemma margin (06);
   - the horizon note in 04a.
7. **Rendering.** 142 pages, 15 overfull boxes (the same set as HEAD), 0 undefined references, and no mid-line `%`.

## Findings (all applied)
- **F1 (FIXABLE).** The band paragraph proved only W ≤ C_N log(2u)/log y. It now also states c_n(y) = 0, so the right sides
  of Thm kr-random vanish. It also shows W ≤ 1 < C_S log(2u)/log y, which bounds both right sides of (b).
- **F2 (FIXABLE).** The reason x/n′ ≥ X₀⁻ is the factor κ_{X₀} in S^τ, not τ-nearness, which says only
  |τ_w − x/n| ≤ 2H_n.
- **F3 (COSMETIC).** "by Cor saias (and directly for y < X₀)".
- **F4 (COSMETIC).** Prop br now gives the reason that W_x ⊂ (2X₀⁻, ∞), and names Prop pointwise(b) as a second user.
- **F5 (COSMETIC, pre-existing).** Prop true-kernels now notes that every application has start ≥ 2X₀⁻, and that the bounds
  are trivial below 2X₀⁻.
