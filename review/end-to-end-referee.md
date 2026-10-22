# End-to-end referee report on beurling-greedy-v3 (FROZEN copy, 2026-10-22)

Document: `notes/v3/beurling-greedy-v3.FROZEN-for-E2E-2026-10-22.md`, 2790 lines; sha256 f5c3c2fc…a8 (checked; identical
to `notes/beurling-greedy-v3.md`). All line numbers below are FROZEN-copy line numbers.

Referee: independent E2E referee (no prior context). Scratch: `/tmp/v3-referee/`. Python runs use `-I` and python-flint 0.9.0
(`/tmp/rhscratch/flintenv/bin/python`).

Classification: **BLOCKING** = false or unproved step in the main line (with failure scenario); **FIXABLE** = correct after a
local repair described here; **COSMETIC** = wording, constants with slack, labels.

This file is written in appended sections. A summary and verdict are in the last section.

---

## Section 1. Reading log and coverage plan

The whole document was read once, top to bottom. Effort was spent according to the brief: Appendix N items, seams between
§1/§3/§4/§5, the first-failure skeleton, Λ-uniformity, certificate reruns, literature at source.

Coverage categories used below: **checked fully** (every step re-derived or recomputed), **spot-checked** (key steps and
constants re-derived, routine estimates accepted), **not checked** (accepted on the document's word or on cited notes).

---

## Section 2. Computer-assisted parts: reruns and cover checks

All scripts were copied to `/tmp/v3-referee/scripts/` and run there with `python -I` (python-flint 0.9.0). No file under
`notes/` was touched.

| certificate | v3 claim | rerun result | status |
|---|---|---|---|
| BS (H⁗), `cert_run_arb_patched.py 1.05 9` (l. 851–856) | 403 bands, 302 013 cells, 0 failures, min ℓS = 2.491·10⁶ | 403 bands, 302 013 cells, 0 failures, min ℓS = 2.491·10⁶ at ℓ ∈ [8.28·10¹⁰, 8.69·10¹⁰], u ∈ [200.1, 210.1] | reproduced |
| (H″) u ≥ 27 and Lemma V, `aux_cert_arb.py` (l. 650–651, 836–837) | 9 609 cells min 0.189; 13 823 cells min 1.724 | 9 609 cells, 0 fail, min 0.189; 13 823 cells, 0 fail, min 1.724 | reproduced |
| X₀ band, `x0band_exact.py 10⁶` (l. 1255–1257) | max B = B(6) = 5/12 | top values B(6)=0.41667, B(12)=0.27778, B(2)=B(4)=B(10)=¼; sup over n ≥ 100 is 0.0881; analytic tail 0.1374 at n = 10⁶ | reproduced |
| Thm 4.17 [N] cross-checks, `analytic_capl.py`, `thm417_check_refereeB.py` (l. 2064–2070) | 0 failures on Λ ∈ {10⁸,…,10²⁰} | s_H = 5.9745; G decreasing in Λ at all tested s; 0 failures (4 842–7 605 points per Λ); referee-B random check (Λ up to 10³⁰): 0 violations, min route-H ratio 1.694, min Dickman ratio 1.190 | reproduced |
| Lemma SC, `sc_check.py`, `sc_check_refereeA.py` (l. 2564) | 30 514 + 13 433 configurations, 0 failures | 10 615 and 842 configurations at the scripts' default settings, 0 failures | reproduced (counts differ from the text: COSMETIC) |
| `tools/depcheck.py` (l. 46–48) | 75 nodes, 165 edges, 28 ↓, acyclic | 75 nodes, 165 edges, 28 ↓, acyclic | reproduced, but see NC-1 (Section 8): the graph is hand-encoded, and one ↓ label is wrong |

**Cover/seam check of the BS certificate (brief item).** Checked by reading `cert_run_arb_patched.py`, `cert_run_arb.py`
and `bs_cert_arb.py` (not only by running them).
- The ℓ-bands are consecutive floats `(l, min(l·q, LMAX))` with `l *= q`. The end of one band is the bit-identical start
  of the next, from LMIN = 3·10⁹ = 30·10⁸ to LMAX = 10¹⁸. ℓ-bisection uses a shared midpoint √(ab).
- u-mode edges run 2.0, 2.5, …, 40.0 (77 points), then ×1.05 up to `split` exactly. Bisection shares midpoints.
- The v-mode starts at va = ↓(split − ↑lb^{1/4}), so u₀(ℓ) + va ≤ split for every ℓ ≤ lb. It ends at
  vtop = ↑(Ū(lb) − ↓la^{1/4}), so u₀(ℓ) + vtop ≥ Ū(lb) ≥ U(ℓ; τ) for every ℓ ≥ la and τ ≥ 10⁸, since U is increasing in ℓ
  and decreasing in τ.
- Every cell is evaluated as an arb enclosure over the whole cell, with u₀ ∈ [la^{1/4}, lb^{1/4}] treated independently of
  v. This over-encloses, which is safe. So the region 30·10⁸ ≤ ℓ ≤ 10¹⁸, 2 ≤ u ≤ U(ℓ) is covered with no seam.
- τ-uniformity: κ_min = 4·10⁸ is used where κ_Φ helps (β_I) and κ_max = 4ℓ/30 + 1500 where it hurts. For τ > 10⁸ the
  required region [30τ, 10¹⁸) is a subset of the certified one.
- The remaining regions are analytic: u < 2; ℓ ≥ 10¹⁸; and the base region τ ≤ ℓ ≤ 30τ via Lemma 3.2. These were **not
  re-derived** here; they were refereed before (referee A §12, B §21, §23.6).
- I did not re-derive that the closed form `S_cell` is a valid lower bound for Σ, i.e. the Part I/II chord bounds of l. 841–850.
  That was checked by the earlier referees and is beyond what I could redo.

**Independent recomputation of quoted constants** (`/tmp/v3-referee/checks/numchecks.py`, `dickman.py`):
- merit = 0.02623 at κ = 3.791. c_zf = merit·6.8/2 = 0.0892/Λ, and a ≥ 6.710 is needed for 0.088 (l. 1192–1193). ✓
- 1/(2 − ζ(s)) − 1 = 2.0673 (s = 1.97), 7.4911 (1.8), 25.539 (1.75; so 27 in l. 1468 holds), 2.2178 (1.955; A₀(0.045)
  = 2.218, l. 1467). A₁(0.03) = 9.409. The abscissa is 1.72865. ✓
- Ein(1) = 1.318, Ein(2) = 3.684, Ein(8) = 437.7. c₂⁻ = 0.6100. ∫₁^∞(1+u)/Γ(u+1) = 3.4479. J₂ = 200.52. h(2) = 56.145. ✓
- (5.6): I₁ = 14.915, I₂ = 214.77, I₃ = 6.696, total (2.02/log 2)(I₁+I₂+I₃) = 688.9 ≤ 690. ✓
- Lemma 5.2(b): sup_v v∫₁^{v−1}ρ(t)dt/(v−t) = 1.3404 at v ≈ 3.69 (Dickman ρ by direct integration). ✓
- Theorem A.6's numeric chain (l. 2620–2623) re-derived by hand. With r₀ ≥ L/(3ℓ) + 3, log((z/δ)·RHS) ≤ L(−0.327 + 0.903/ℓ)
  − 5.9ℓ + 8.2, which is ≤ −4ℓ for L ≥ 465. ✓ The factor (2L)^{1.02} in l. 2621 is an unexplained over-estimate of
  (1 + r₀/X₀)^{1.02}; it is harmless (COSMETIC).

---

## Section 3. Literature at source

Read at source where accessible. Scans and PDFs were fetched into `/tmp/v3-referee/lit/`; the summary is in
`/tmp/v3-referee/lit/lit-report.md`. "Load-bearing" means the main line of Theorem A uses it.

| citation (v3 lines) | load-bearing? | at source | verdict |
|---|---|---|---|
| Heath-Brown, Crelle 389 (1988), Thm of §1, eq. (1.2), p. 23 (l. 2207–2210) | yes ((5.2), X_Hux, (G1), Prop 3.16(A)) | GDZ scan pp. 22–23 | **Matches.** The theorem holds for any 0 ≤ ε(x) ≤ 1/12, with error O(ε⁴) + O((log log x/log x)⁴), uniformly for x^{7/12−ε(x)} ≤ y ≤ x/(log x)⁴. ε ≡ 0 gives exactly v3's form and range. |
| dlVP PNT for long windows (l. 2212) | yes (long-window part of η) | standard | fine; the error (log q)⁵e^{−c√log q} is o((log q)^{−3}) |
| X_Hux definition (l. 2220–2228) | yes | — | well-defined: η(q) = o((log q)^{−3}) follows from the two inputs, and the threshold is parameter-free. **COSMETIC:** the admissibility line "κq ≥ q^{7/12+ε} ≥ (2q)^{7/12}" (l. 2252) needs q^ε ≥ 2^{7/12}, true for any fixed ε > 0 at q ≥ X₀, but ε is never fixed in v3 (l. 155, 204). Fix ε (e.g. ε = 0.01). |
| Huxley, Invent. Math. 15 (1972) (l. 2231) | no (credit only) | primary not accessible; Heath-Brown p. 22 credits Huxley [6] with the asymptotic for y ≥ x^{θ}, θ > 7/12 | **COSMETIC:** v3's statement that Huxley "proves only the gap and density bounds" contradicts Heath-Brown's own attribution. Drop the parenthesis. |
| Johnston–Yang, JMAA 527 (2023), Thm 1.1/Table 1 (l. 2215–2217) | no (remark) | arXiv 2204.01980 v2 | row X = 10⁸: ε₀ = 2.18·10^{−4694} ✓, hypothesis log x ≥ X ✓. The θ(x) version is not an ε₀ statement in Cor 1.2 but follows from (1.5) with A₁ = A + 0.01. COSMETIC. |
| Freedman, Ann. Probab. 3 (1975) (l. 1079, 1651, 1704) | yes | Project Euclid scan | The printed results are Thm (1.6) (two-sided, \|X\| ≤ 1) and Thm (4.1) (one-sided, X ≤ 1): P(S_n ≥ a, T_n ≤ b for some n) ≤ (b/(a+b))^{a+b}e^a. v3's form exp(−a²/(2v + 2ab/3)) is **not printed**. It is a correct consequence of (4.1) by scaling plus h(u) = (1+u)log(1+u) − u ≥ u²/(2(1+u/3)). **COSMETIC:** cite as "Freedman (4.1) + Bennett's bound". |
| Montgomery–Vaughan, JLMS 8 (1974) (l. 458–463) | yes (Lemma 2.3(i)) | primary paywalled; secondary statements (Preissmann–Lévêque; ANT 2025 citing "Cor. 3") | ∫₀^T\|Σa_n n^{−it}\|² = Σ\|a_n\|²(T + O(n)) under Σn\|a_n\|² < ∞. Applies to Z_∞ and Z_∞² on σ = 1 (Σ_{n∈𝒟}τ(n)²/n < ∞). ✓ |
| Broucke–Debruyne, Acta Arith. 207 (2023), via Broucke 2409.10051 Thm 2.1 (l. 469–475) | yes (Lemma 2.3(ii)) | both PDFs | **Matches** after specialising η = 1/(2N): (T + 2N)·Σχ(n_j, 1)\|a_j\|², i.e. K = max count in a window of length 2. Multiplicities are allowed. ✓ |
| Titchmarsh Thm 4.11 (l. 373) | yes (Lemma 2.0″) | scan, p. 77 | **Matches** (\|t\| < 2πx/C, C > 1; v3 uses \|t\| ≤ X₀ = x, fine with C = 2π… any C ∈ (1, 2π)). ✓ |
| Rosser–Schoenfeld 1962 (l. 1613, 1969, 601) | yes (constants) | Project Euclid scan | (3.6) π(x) < 1.25506x/log x ✓. **COSMETIC:** "Σ_{p≤y}1/p ≤ log log y + 0.27" holds only for y ≥ 662 (RS (3.18)/(3.20) give it from 2140 / 51 265), and the Mertens product with factor (1 + 1/(2log²X)) only for X ≥ 286 (RS (3.29)). v3 uses both only at y = X₀, so this is harmless. State the ranges. |
| Broucke arXiv 2507.13780 Thm 1.6, eq. (1.2) (l. 2386–2391, 2409–2410) | no (context) | arXiv v1 | Thm 1.6 matches, including discreteness of the system and the N_P error x^{1/2+ε}. The slowly varying case needs (1.10), which v3's "admissible" omits. Landau's region is (1.2), derived from Thm 6.1 + (1.4); it is not stated in Thm 6.1. COSMETIC. |
| Diamond–Zhang Ch. 17, "footnote 4 … β₀ equals 1/2" (l. 2401–2402) | no | book not accessible | The quoted sentence is footnote 4 of **Broucke–Debruyne–Révész** arXiv 2309.01567, not Diamond–Zhang. COSMETIC misattribution. |
| DMV Math. Ann. 334 (2006), Saias JNT 62 (1997) (l. 769, 2411, 2419) | no (background) | Deep Blue PDF; zbMATH review | match (DMV needs θ > ½; Saias D(x,z) ≍ x log z/log x) |

**Net literature verdict.** Every load-bearing citation matches its use, hypotheses included. Five COSMETIC attribution or range
corrections are listed above.

---

## Section 4. §0–§2: statement, parameters, construction, zeros

**Coverage.** Checked fully: (G1) (l. 239–256), Lemmas 1.2–1.5 and Cor 1.4 (l. 299–325), (C2) (l. 292–295), Lemma 2.0
(l. 349–361), Lemmas 2.1–2.2 and Thm 2.4 (l. 425–490), Lemma 2.3(i) (Paley–Zygmund numbers). Spot-checked: (T1) (l. 258–268),
Lemma 2.0″ (l. 363–384), Lemma 2.0′ (l. 386–407), Lemma 2.3(ii) (l. 465–479). The Lean definition of Q
(`RH/Attempts/Beurling.lean` l. 61–66) was read. Theorem A's system meets its hypotheses: real primes > 1, finitely many below
any bound, N counted with multiplicity, and |N − x| ≤ Cx^{θ′} for x ≥ 1. Theorem A's zeros are zeros of the unique continuation
to Re s > ½, s ≠ 1. So ¬Q follows from Theorem A as stated.

**F-0.1 (FIXABLE) — (L-a) is false as stated for θ close to ½; the claim "log B, log H ≤ 2·10⁻⁶·L at every scale" is false.**
Lines 334–335, 330, 163.
- At x = X₀ with Λ = 10⁸: log H(X₀) = 8(log Λ)² = 2715, and log B(X₀) ≈ 1395, while 2·10⁻⁶·L = 200. The claim holds only
  for L ≳ 5·10⁹ (from Thm 4.17(c), log H − log H_std ≤ 10⁻⁶L, and log H_std = 8ℓ²).
- Failure scenario: θ = ½ − 10⁻⁵, so η = 2.5·10⁻⁶ and X₀^η = e^{250}. On [X₀⁻, X₀), D(x) is the number of jittered primes
  already landed below x. That is ≈ H(X₀)/(4Λ) ≈ e^{2694} with overwhelming probability, so |D(X₀)| ≤ X₀^η fails.
- Theorem A(i) survives: |D| ≤ B + 3H + 3 ≤ X₀^{θ} near X₀ is absorbed into C_{X₀}x^θ. The uses of (L-a) with exponent η
  are only at the zero scales (Lemma 2.2, x ≥ x_k ≥ exp(X₀²)) or need only a polynomial bound (Lemma 2.3(ii)'s K(N), where
  K(X₀)X₀^{−1/2} stays tiny with K(X₀) ≈ H(X₀)).
- For θ so close to ½ that η·exp(2Λ) < 32Λ², even the zero scale k = 1 fails at X₀ = e^{10⁸}. Then X₀ must depend on θ.
- Repair: state (L-a) as |D(x)| ≤ max(x^η, B(x) + 3H(x) + 3), or require X₀ ≥ X₁(θ). For refuting Q one θ suffices (θ = ¼
  works with X₀ ≥ max(e^{10⁸}, X_Hux)). Theorem A should say "X₀ ≥ max(e^{10⁸}, X_Hux, X₁(θ))", or restrict θ.

**F-0.2 (COSMETIC) — Lemma 1.1 (adaptedness) is off by H/2 at the switch-on points.** Lines 233–237, 143, 456.
- γ_k is chosen from "the system on [1, x_k)". That system includes primes decided at slots up to x_k + H(x_k)/2 that land
  below x_k.
- T(u) for u ∈ (x_k + H, x_k + 1.5H) depends on γ_k. Lemma 1.1 claims it is determined by slots ≤ u − H(u) < x_k + H/2.
- The construction is still well-defined, since γ_k is known before any slot whose window involves R_k. No consumer needs
  the strong form at those u.
- Repair: R_k ≡ 0 on [1, x_k + 2H(x_k)], or choose γ_k from the system on [1, x_k − H(x_k)).

**F-0.3 (COSMETIC) — §1.3 claims "every other slot is a continuous slot, of physical length ≥ 1/(1 + κ₊/log X₀)" (l. 276–277).**
- This is false near X₀. A continuous slot ends at the next rigid integer, so it has length < 1 when rigid integers have
  density ≈ 1.
- What is true, and what (F1) and A.0 use, is that consecutive continuous-slot *starts* are ≥ 1/(1 + 1/(κu) + κ₊/log u) apart.
- Relatedly, (F1) (l. 1600) "at most H(t) + 3 decided primes have jitter windows containing t" should read
  ≤ H(t)(1 + κ₊/log t) + 3, since T′_cont can reach 1 + 0.8/log t at the zero scales. The only effect is θ = 1 + 5/H → 1 + 1/L
  in PIL (Lemma A.3), costing e^{r₀/L} ≤ e^{1/(3ℓ)} per E_cl window. Harmless.

**F-0.4 (COSMETIC).**
- (H_BS) (l. 574): "T − ⌊·⌋ … + O(u^{θ/2})" should be O(u^θ log* u), because R is of size 2u^θ log* u. η₁, η₂ stay ≪ 10⁻³.
- §0.4 (l. 157) and §4.1 (l. 1579) define λ′_u without the "+2" used in §3.5 (l. 1061) and Def 4.4. The +2 is what the
  probability bound uses.
- ε in κ = X₀^{−5/12+2ε} is never fixed (l. 155, 204). Fix e.g. ε = 0.01; all uses need only 0 < ε ≤ 0.04.
- Line 161 says 𝒜 = ∅ "wherever y ≤ X₀"; the correct and proved condition is y < X₀⁻ (Thm 4.17(b)).
- The brief's "Lemma 1.3′" does not exist in v3; I took it to mean (G1) = (1.3′), which is checked.

**Checks that passed (no finding).**
- (G1): the R′ bound 16κ₀/log³x + 4κ₀x^{−(1−θ)/2} ≪ 0.8/log x holds with a large margin. The rigid part uses the linear
  normalisation correctly: ρ_det ≤ (κu+1)/(κu), and 1 − ρ_det ≥ (prime count − 1)/(κu), with no κ/2.
- (C2): every prime factor of a composite in J_j is ≤ n/2 and was decided at a slot ≤ p + H/2 < s_j. ✓
- Lemma 2.0: |W(s)S_{≥X₀}| ≤ 6e^{2X₀^{1/2}/Λ}/(κΓ₁) ≤ e^{−X₀²/4}, since κΓ₁ ≥ e^{(1−θ)X₀² − O(Λ)}. ✓
- Lemma 2.3(i): ζ(2)⁴/ζ(4) = 6.03 ≤ 6.8, and Paley–Zygmund gives density ≥ ¼/6.8 = 0.0368. ✓
- Lemma 2.3(ii): the mean of the long Dirichlet polynomial is K·N^{2−2σ}/Γ at N ≈ x_k, i.e. x_k^{θ+η−½}log³x_k, using the
  Broucke–Debruyne form verified in Section 3. ✓
- Lemmas 2.1, 2.2 and Thm 2.4: the Rouché budget is o(1) + 1/16 + o(1) + e^{−10¹⁰} < ¼, the Rouché circle lies inside the
  ⅛-disc and the δ_k-disc, and |Z_B| ≥ ½ there. ✓
- Lemma 2.0′(a): the saving rate is ≥ 0.9(log 100 + 1)/(22.6Λ) = 0.22/Λ, against δ_k ≤ 18Λe^{−2Λ}. ✓

---

## Section 5. §3: the margin (G2), the X₀ jump, R1′

**Coverage.**
- Checked fully: Thm 3.6 (re-derived, including the chain-sum identity Σ_{g|m,g<m}H_ord(g) = H_ord(m)); Cor 3.7(a)(b);
  Lemma 3.3, squarefree case (the (S)/(M) involution re-derived); the level formula and the 𝔅-decomposition of Lemma 3.14A
  (re-derived from the kernel recursion); the small-range bound TV(D_d) ≤ 2μ²(d) + ½λX(d)/d and 𝔹₂ ≤ 𝔹₁ weight for w ≥ 2;
  Prop 3.18(b) "jump paid once" (m_j = 𝓡J, Bm_c = M_c − θ/H, flatness of ρ^sh_c); Prop 3.16(A) arithmetic; Prop 3.16(B)
  Step 4 (resolvability, γ_kδ ≥ e^{c_zf√log x/5}, C′ ≍ Λ²).
- Spot-checked: Lemmas 3.1, 3.2, 3.9–3.12, 3.15; Prop 3.8 (fixed point, terminal levels); Prop 3.14; (3.4) leading
  constants (61.2L·(M₁/H)^{1/2} ≤ 61.3L^{−6}, Σ_j 128(Λ+j log 2)^{−5} ≈ 46.2/Λ⁴); (Osc); the s₂ bound (sup_s e^{−s}/Γ(L/s−2) ≤
  e^{−max(Λ, 1.4√(L log L))}); Lemma 3.14B (structure, the LP⁺ threshold, Region 1 constant 61.1); Thm 3.13 (structure and the
  merit/c_zf numbers).
- Not re-derived: Thm 3.4's analytic regions (u < 2, ℓ ≥ 10¹⁸) and the derivation of `S_cell`; Lemma 3.3, non-squarefree case
  (it is [N]-checked); the middle and huge ranges of Lemma 3.14A beyond the structure (fix-Bprime §12.2–12.3, §12′.3; refereed by B §23).

**F-3.1 (FIXABLE) — a Λ = 10⁸-only estimate remains in Prop 3.16(B), Step 3 (l. 1380–1385).**
- The ρ_det smooth-change term splits at U₀ := 10⁷. It is then bounded using "ρ(U₀)e^{a_V} ≤ e^{−1.5·10⁸} … beat
  1/κ ≤ X₀^{5/12} ≤ e^{4.2·10⁷}".
- That holds only while (5/12)Λ < U₀ log U₀ ≈ 1.6·10⁸, i.e. Λ ≲ 3.9·10⁸.
- Failure scenario: Λ = 10⁹ (allowed, since X_Hux is uncomputed). Then 1/κ = e^{4.17·10⁸} while ρ(10⁷) ≈ e^{−1.6·10⁸}, and the
  displayed bound on Σ_{u ≥ U₀}log(2v)·3Ψ(2v,X₀)/(κv) is ≥ e^{2·10⁸}. The claimed e^{−10⁶} is not proved.
- Repair: take U₀ := Λ. The first bound of the min then gives C_S(Λ²)²(2δ + 2/X₀)/κ ≤ 2C_SΛ⁴X₀^{−1/12}. Beyond U₀ the Rankin
  bound gives poly(Λ)·e^{−Λ/2}·X₀^{5/12} = poly(Λ)e^{−0.083Λ}. Both are uniform in Λ ≥ 10⁸.
- This is the brief's "certificate valid only at Λ = 10⁸" pattern, here in an analytic step. It is the only one I found in §3.

**F-3.2 (FIXABLE) — Lemma 3.11 (E3/E3′) applies Freedman with an increment bound that is not sure for the stopped process.**
Lines 1067–1076.
- (F₁) uses increments X_q(W) ≤ 2M₁ (Cor 4.7 on E_cl). For a latest prime q < √(2u), the cofactor height u/q has
  E_cl-time t_z ≈ 2u/q + H > s_q. So at q's decision time the stopped process has not yet certified X_q ≤ 2M₁.
- The text's argument ("V̄_W … are sure bounds on the predictable variances of the process stopped at τ"; "the stopped and
  unstopped martingales agree") does not cover this. The same applies to the variance bound through ω_y ≤ 1.2, which uses
  (H_BS) at cofactor heights y/v > s_q.
- Repair: copy Theorem 4.3(i)'s device. Truncate X̃_q := min(X_q, 2M₁) (and b₂ for Mart^{(2)}) and apply Freedman in the form
  P(∃n: S_n ≥ a, V_n ≤ v). On Good(<t(W)), E_cl at all cofactor heights holds, so truncation is inactive for every offset and
  V_W ≤ V̄_W. The probability bound 1.2u^{−2}L_u^{−2} is unchanged.

**F-3.3 (FIXABLE) — R1′ is proved only on [2X₀, ∞), but Theorem 4.3 needs it from X₀.**
- Cor 3.19 (l. 1491–1492) is for I ⊂ [2X₀, ∞). Prop 3.18 is for t ≥ 2X₀, and Thm 3.17 for x ≥ 2X₀. Theorem 4.3 is stated for
  every dyadic scale x = 2^mX₀, m ≥ 0 (l. 1684), and Def 4.4 lists events from u = X₀.
- Windows with right end in [X₀, 2X₀) are not covered, and neither are windows of up to ~11L·L₀ physical length that straddle
  2X₀. On [2X₀ − H, 2X₀) there are ≈ H/(4Λ) ≈ e^{2694} jittered composites 2q, q ∈ [X₀⁻, X₀), which is far above B(X₀) ≈ e^{1395}.
  So the queue bound there is not vacuous.
- Repair (elementary):
  - For t < 2X₀⁻, K_ptρ̃ = NT_pt = 0, so m = 1 − ρ_det ≥ 0.99/log t − 1/(κt).
  - For t ∈ [2X₀⁻, 2X₀), m(t) = T′(t) − ½ρ̃(t/2). Here ρ̃(y) ≤ (#continuous slots in [X₀, X₀ + H/2] + 3)/H ≤ 0.5001/Λ + 3/H,
    because T′_cont ≤ 1.0001/Λ there by (5.2).
  - So m·log t ≥ 0.73 > 1.01c′, and Cor 3.19 holds on every slot window I ⊂ [X₀, ∞).

**F-3.4 (FIXABLE) — (Osc) at the current height reads the local count at that height; see NC-1 in Section 8.**

**F-3.5 (COSMETIC) — "o(1)".** "o(1) means o_{X₀→∞}(1)" (l. 564), but X₀ is never sent to ∞. Every threshold must hold at each
fixed Λ ≥ 10⁸. I checked the o(1) terms of Prop 3.16(B) Steps 1–4. Each is ≤ exp(−c·X₀^{0.005}/Λ) or ≤ Λ²/X₀², so the 0.97 − o(1)
(Thm 3.17) and 0.96 − o(1) (Prop 3.18(a)) are ≥ 0.969 and ≥ 0.959 for every Λ ≥ 10⁸. The document should state explicit
bounds instead of o(1).

**F-3.6 (COSMETIC/FIXABLE) — Thm 3.13 (LP, LP⁺) is not self-contained.**
- v3 gives a sketch (l. 1180–1203) and points to gap-localPNT §2 (proof against Au), §7′ (constants) and §7′.6 (B-lin). §7′.6
  is a numerical scaling remark, not a proof.
- The scaling argument in v3 (3) is right: the Landau disc radius r = a/Λ forces c_zf = merit·r/2, and log M ≤
  max(L, 440 + log Λ) + log(1/η). I recomputed merit = 0.02623.
- Two points are not written anywhere:
  - The k = 0 (pole) term must be bounded through the Euler product and Lemma 3.1(ii): −P_y′/P_y(1+η) ≤ 1/η + 0.43. The
    T_A-route "pole data on |s−1| ≤ 1/16" of gap-localPNT §7′.1 fails with |Ê| ≤ C₈e^γΛ ≈ e^{459}.
  - The small-|t| zero-freeness of ζ♯ must use Ê = ζ − 1/(s−1) − 1 + O(X₀^{−σ}) + O(κZ_∞) from Lemma 2.0″'s proof, not the
    crude bound.
- Both are routine, and the downstream uses (Prop 3.16(B) at log x ≥ X₀^{0.01}; Lemma 3.14B at log v ≥ 100Λ³) have enormous
  slack.
- Lemma 3.14B's threshold: with v3's own log G ≤ Λ (l. 1178), LP⁺ needs Λ_p ≳ 6Λ³/(0.9·0.088) ≈ 76Λ³, not fix-Bprime's 50.5Λ³
  (which assumed log G = polylog). So Λ₁ = 100Λ³ still suffices.

**F-3.7 (COSMETIC).**
- ρ̃ ≤ 27 "by the local count" (l. 1073–1074, 1310) is unnecessary. ρ̃ ≤ 1.02 surely, since at most one prime is decided per
  continuous slot. Using the sure bound removes a local-count dependency.
- Lemma 3.11's hypothesis "Good(<4u + H)" (l. 1089) is stronger than what consumers at time x have for u up to x/2 + 2H. Only
  the per-window events closing by y + H/2 are needed, as Def 4.4 records.
- Lemma 3.1's (H_BS) bullet, line 574: see F-0.4.

**Checks that passed (selected).**
- Thm 3.6: ‖D_n‖_KR ≤ |c_n|H_n/4 + Σ_{d<n}(d/n)‖D_d‖_KR is solved exactly by the stated bound; the TV bound follows from (K3).
- Cor 3.7(b): (1 + A₀/2)log 2u + A₁/2 = 2.034 log 2u + 4.70. ✓
- Lemma 3.14A small range: B(n) reproduced (Section 2), and 1.0101·5/12 = 0.42088.
- Prop 3.18(b): 0.97 − 0.4209 − 10⁻¹² ≥ 0.549 ≥ 1.01c′ + (slack for K_d). ✓
- Prop 3.18(a): V_X₀ ≤ 1.02(1 + log N/Λ)·8.5(N/2)^{−0.155} ≤ e^{−0.0015Λ} for N ≥ e^{0.01Λ}. ✓
- Lemma 3.9 and (3.4) bounds improve with Λ. Lemma 3.14A's middle range (e^{−0.0009Λ}) and huge range (e^{−59}) are Λ-uniform
  as stated.

---

## Section 6. §4 and Appendix A: the queue, E_cl, CapL-w, absorption

**Coverage.**
- Checked fully:
  - Thm 4.3: the Freedman algebra in (i); the maximisation giving B(x) in (ii); the full-block margin (4.6), where
    c′L₀/L − √(16M₁LL₀) = 135.25M₁L² for L₀ = 48M₁L³/c′²; and the a ≥ 2 term (N.15).
  - Lemma 4.1 and Cor 4.2 constants. Lemma 4.5 budget: Σ_m(Λ + m log 2)^{−2} ≤ 1.4427/Λ + 1/Λ².
  - Prop 4.6 (both cases), including N.17′ on [X₀/2, X₀²). Lemmas 4.8–4.10 and Thm 4.11.
  - Lemma 4.14(iii) and criterion (4.10): r₀·7L^{5.1}z·w^{1+j} ≤ L^{−3} needs (1+j)log(1/w) ≥ L + 9.1ℓ + 2.
  - Lemma 4.15(b),(d) logic. Thm 4.17 Steps 0, 1, 2, 3, 4(T1, T2), 5, 6, re-derived analytically, plus the reruns of Section 2.
  - Lemma 4.18 (i)–(vi), Lemma 4.19, Prop 4.20, Lemma 4.21. Lemma A.7 (matroid argument re-derived). Thm A.6 numeric chain.
- Spot-checked: Lemma 4.14(ii) type-union constants; Prop 4.13; Lemmas A.1–A.4; Thm A.5 (SVL).
- Not re-derived: SVL's staged identity (A.1) beyond its statement, and Thm 4.12 (not used).

**F-4.1 (FIXABLE) — Thm 4.3: windows are counted in all slots, but the drift is in continuous slots.** Lines 1685, 1714, 1718–1727.
- 𝒲_x is "slot windows W with ℓ(W) ≤ L₀ slots" (ℓ(W) is undefined). The short-window step uses ℓ := ℓ_jit(W), the full-block
  step (4.6) takes ℓ = L₀, and the Lindley step uses k := j − L₀ slot indices.
- With the literal reading, a block of L₀ slots near the base contains only ℓ_jit ≈ (1 − ρ(u))L₀ continuous slots, where
  u = log x/Λ, because rigid integers occupy jump slots at density ρ(u).
- Failure scenario: x = X₀^{1.2}. Then ρ(1.2) = 0.818 and ℓ_jit ≈ 0.18L₀. The bound gives exc ≤ −c′·0.18L₀/L + √(16M₁L·0.18L₀)
  + … = (−58 + 79)M₁L² > 0, so the full-block step "exc ≤ 0" is not proved. At x ∈ [2X₀, 4X₀], ℓ_jit ≈ L₀/L and the deficit is worse.
- Repair:
  - Index blocks by continuous slots. Let k be the slot index with ℓ_jit((k, j]) = L₀, and let 𝒲_x be the windows with
    ℓ_jit(W) ≤ L₀, of any total slot count.
  - exc is additive over slots, R1′ and v_W are already in units of ℓ_jit, and by (G1) the physical length of such W is
    ≤ L₀L/0.09. So |W|/q ≤ 11/(HL⁵) ≪ δ₁ still holds.
  - The union bound grows only to ≤ x²·2x^{−4}. Everything else is unchanged.

**F-4.2 (COSMETIC) — Thm 4.3(b)'s input Σ_q P(X_q^{(2)} ≥ 1 | F_{q−}) ≤ 1 is justified only by "(F1)–(F3′)" (l. 1708).**
- On the raised range, L₀ ≈ X₀^{7.5}L³ ≫ X₀, so a crude count does not give ≤ 1.
- It follows from Σ_q P(·) ≤ Comp^{(2)}(W) ≤ s₂(x)|W| with s₂ ≤ 9L·exp(−max(Λ, ½√(L log L))). I checked s₂|W| ≪ 1 for every
  Λ ≥ 10⁸ along γ(s): where log c ≥ γΛ with γ ≥ ⅓ one has ½√(L log L) ≥ 2.9Λe^{s/2} ≫ γΛ + 3ℓ.
- Cite this.

**F-4.3 (FIXABLE) — Lemma 4.15(c),(d): range of the Rankin bound.** Lines 1956–1974.
- (c) claims Ψ(Y, X₀) ≤ Y·exp(−0.9u log u) for u ∈ [10⁴, X₀^{1/2}]. The last step needs
  0.1u log u + u log log u − 1.3u ≥ log Λ + 2. At u = 10⁴ that is log Λ ≤ 1.84·10⁴. So (c) is not uniform in Λ near u = 10⁴.
- (d) sums the geometric series over k′ ≥ 1 using (c) at u = D − k′. For k′ > D − 10⁴, (c) is not available at all.
- Repair:
  - In (c), require u ≥ max(10⁴, log Λ).
  - In (d), bound the terms with D − k′ < max(10⁴, log Λ) by Ψ ≤ Y. The ratio of the first such term to the last (c)-term is
    ≤ πX₀^{−1}e^{0.9(u+1)log(u+1)} ≪ ⅓, and the following ratios are ≤ (π+k′)/((k′+1)X₀) ≤ ⅓. So g is unchanged.
  - Uses in Thm 4.17 Steps 3/4 have D − 1 ≥ Λe^{s_H+1}, so nothing else changes.

**F-4.4 (COSMETIC) — Thm 4.17 Step 5 drops the factor c′^{−2} in L₀ (l. 2048–2049).**
- "log L₀ ≤ log 48 + log M₁ + 3ℓ" should be log 48 − 2 log c′ + log M₁ + 3ℓ = 7.67 + log M₁ + 3ℓ. Then log y ≤ 3 log c + 9ℓ + 10.5,
  not + 7.4.
- The same omission is in `capl-cert/capl_model.py` (`logy_of`), so the [N] cross-check shares it.
- Effect: "≤ Λ − 2600" becomes ≤ Λ − 2597 at s ≤ s_H. "log 2y ≤ 3.01γΛ" is unaffected (+3.1 against 0.01γΛ ≥ 3·10⁵). No conclusion changes.

**F-4.5 (COSMETIC) — base heights and E_cl on [X₀/2, X₀²) (N.17′).** Verified:
- For z < X₀²/2 every element of S(J) has the form q·d, with q jittered and d rigid. So exponent vectors are unit vectors,
  rank S(J) = |S(J)|, and the case r < r₀ of Prop 4.6 is vacuous.
- The rank-full case is a direct (F1)–(F2) count, E ≤ (1.01|J|)^{r₀}/r₀!, which is what Thm A.6 gives. But Thm A.6 (A.0:
  "z ≥ X₀") and Thm 4.17 ("z ≥ X₀") are not stated for z = X₀/2. Extend their statements, or add this one-line argument.
- Cor 4.7's rigid case is keyed to "u/q^a < X₀/2" (l. 1810). It should be keyed to "I/q^a lies below X₀⁻": a window at height
  slightly below X₀/2 can extend into [X₀⁻, X₀). It is then covered by E_cl(X₀/2), which is in E_cl^{(u)}. Harmless.

**F-4.6 (COSMETIC).**
- Thm 4.17 Step 2 says "If D* ≥ D − 1, then Cap ≥ c is impossible". That is not literally true when D is an integer
  (2z = X₀^D, possible for X₀ a power of 2). The same Lemma 4.15(b) bound with k = D* + 1 ≥ D applies, or Lemma 4.8(iii) gives a
  contradiction if no such row exists. Harmless.
- Lemma 4.18(v) cites "LP, §3" for π_𝒩(s) ≤ 2s/log s at s < 2y. LP is not available below X_LP, but Lemma 3.1(i) gives it.
  "u_* ≥ 100" should be u_* ≥ max(100, log Λ); in use u_* ≥ u₀ ≥ 2Λ.
- Thm 4.17(c): "≤ γ_*Λ/L" omits the factor (0.5 + 2/A)·2 ≈ 1.06, giving 4.1·10⁻⁸ rather than ≤ 4·10⁻⁸ at the worst point. The
  total d log H/d log z ≤ 4·10⁻⁶ holds with large slack.
- §4.4 (l. 1780) defines D := log 2z/Λ, while degrees can reach log 2z/log X₀⁻. Use X₀⁻ (relative change H/X₀).

**Checks that passed (selected).**
- Prop 4.6, r ≥ r₀: log((z/δ)·(15L^{−3.98})^{r₀}) ≤ −4ℓ (Section 2).
- Thm 4.17:
  - Step 1: ∂_Λ log G² < 0 needs A > 6, and A ≥ log(2Λ/ℓ) ≥ 16.
  - Step 2: (1+j)log(1/w) ≥ 1.69·0.969·L. On [s_H, s_H+1], γ_*(s_H + t) ≤ ⅓e^{0.53t} ≤ ⅓ + 7.17t.
  - Step 3: 3.375(log Λ + s)/(3 log Λ + 2s − 2.9) ≥ 1.125 for all s ≥ −2.9, uniformly in Λ.
  - T1: 0.9·1.875(1 − (log Λ + 1)/(1.37√Λ)) ≥ 1.68.
  - T2: X₀^{1/4} ≪ L.
  - Step 5: 393e^t(19.2+t) ≥ 107.6γ² ≤ 6053.
- Lemma 4.18: Rankin at t = 2yh with u_* ≥ u₀ ≥ θ_bΛe^{s_H}/(22.6) ≥ 2Λ; (12.2) gives C_d·2y·e^{−0.9u₀log u₀} ≤ L^{−4}.
- Lemma A.7: lex-first bases are nested because cl_{M_{t+1}} ⊆ cl_{M_t}, and (SC) holds by C-maximality of the lex-first basis.

---

## Section 7. §5: B-lin, Huxley/Heath-Brown, μ₀ and μ₁

**Coverage.**
- Checked fully: (5.2) and the definition of X_Hux (l. 2202–2230, against the source; Section 3). Lemma 5.2(a). Lemma 5.2(c)
  and (5.6): both μ₁ bounds re-derived, integrals recomputed, total 688.9/Λ.
- The Dickman constant 1.341 of Lemma 5.2(b) was recomputed (1.3404).
- Spot-checked: Lemma 5.1, (5.4)–(5.5).

**F-5.1 (FIXABLE) — Lemma 5.2(b)'s proof covers only the unfiltered cofactor range.** Lines 2256–2269.
- μ₀ ⊃ (K_ℚ − K_pt)f₀. K_ℚ carries the filter P⁺(m′) ≤ x/m′ (from p ≥ P⁺(m′) in ⊔m′·ℙ_{≥max(P⁺(m′),X₀)}). K_pt carries
  τ_w < y/w.
- For cofactors m ≤ √u both filters are void, and integration by parts against N − N_ℚ = E + R + D is valid. For
  m ∈ (√u, u/X₀], which is non-empty once u > X₀², the two filtered counting functions are smooth-element counts in two
  different semigroups. Their difference is not E + R + D.
- This region carries O(1) of the mass of K f₀, so the difference must be shown to be O(κ·polylog u). The proof does not do this.
- Repair:
  - Compare the semigroups at the prime level. dΠ_𝒩 − dΠ_ℕ = log*(δ + dΔ * μ_ℕ) with Δ := N_𝒩 − N_ℕ,
    |Δ(t)| ≤ 2κt + B + H (+2t^θ log* t above x₁). This gives |π_𝒩 − π|(t) ≲ κt log t.
  - Propagate through the filtered smooth counts, at a cost of one factor log u/Λ per prime factor. This gives
    |μ₀(u)| ≲ κ(log u)³.
  - That is all Prop 3.16(A) needs: log x·|(1+K_pt)^{−1}μ₀| ≲ κ(log x)⁵ ≤ X₀^{−0.36} for log x ≤ X₀^{1/100}.
- The pointwise form 2κe^γΛ/log u claimed in N.8 is not proved, but it is not needed.

**F-5.2 (COSMETIC).**
- Lemma 5.2(c) and its proof are stated "On 𝒢" (l. 2270, 2281). They are used inside Prop 3.16(A) on Good(<x), where only
  heights ≤ x/X₀ are read. Replace 𝒢 by Good(<x); otherwise the citation is formally circular.
- §5's closing remark (l. 2303) gives h ≥ 0.8/log x "at every x ≥ X₀ + H". This is superseded by Prop 3.18's 0.549/0.96. Remove it.

**Checks that passed.**
- Lemma 5.2(a): π(I) ≥ (1 − η)∫_I dt/log t ≥ (1 − η)κq/log((1+κ)q). So MA[ℙ](q)·log q ≥ (1 − (log q)^{−3})(1 − κ/log q).
  Heath-Brown applies when |I| ≤ x/(log x)⁴, with x^{7/12} ≤ |I|, and dlVP otherwise. ✓
- Lemma 5.2(c):
  - Components with q ≥ x^{1/U} give 2(U/log x)³(log U + 0.01).
  - Rankin with exponent 1 − 2/log y on m′ ≥ x/y gives e^{−2(U−1)} = v^{−4}, and the Euler product ≤ 2e^γe^{Ein(2)}log y.
  - Integrated: (2.02/log 2)(14.915 + 214.77 + 6.696)/Λ = 688.9/Λ. ✓ This is ∝ 1/Λ, hence Λ-uniform.
- Prop 3.16(A) uses only (a)–(c) and Lemma 3.3/Cor 3.5. Its arithmetic 0.99 − 0.01 − 6·10⁻⁴ − e^{−80} ≥ 0.979 is correct given
  (b) in the weaker form above.

---

## Section 8. Non-circularity (§0.3), the stopped process, and Λ-uniformity

**The first-failure skeleton (N1), checked.**
- Every event of Def 4.4 has an explicit time:
  - E1: 8u/L¹¹ + H.
  - E2: right end of W.
  - E3/E3′: the closing time of each deterministic window.
  - E4: max J + H.
- Each event is F_{t(E)}-measurable. Good(<t) is F_{t−}-measurable, τ is a stopping time, and
  P(τ < ∞) ≤ Σ_E P(E^c ∩ Good(<t(E))) holds by the case split on {τ = t} (l. 1767–1768).
- Budget: Σ_{m≥0}(Λ + m log 2)^{−2} ≤ 1.4427/Λ + Λ^{−2}; the rest is O(X₀^{−2}). Total ≤ 1.5/Λ < ½. ✓
- I traced every consumer of every event to a time. All are at times ≥ t(E), except NC-1 and except the adaptedness issues
  NC-2/NC-3, which concern the *validity* of the probability bounds, not the order.

**NC-1 (FIXABLE) — a current-height local count enters R1′ through (Osc).**
- Prop 3.18's source term S(t) contains o_t, and E_S contains sup_v log v·o_v (l. 1432, 1453). (Osc) bounds the 𝒜-part of
  o_t by Lemma 4.19(b) (l. 1288). Lemma 4.19(b) is Cor 4.2 *at height t*.
- Cor 4.2 at height t reads queue bounds at slots ≤ t + H(t) and Land events at time ≤ t + 7H (l. 1673–1674). Prop 3.18 at t
  feeds R1′ for windows ending at s_j ≈ t, which proves Q_j ≤ B. So as written the queue bound at s_j uses queue bounds at
  later slots. This contradicts (N2)/(N4) (l. 115–121, 132–138).
- `depcheck.py` does not catch it, because the edge `Osc → C4.2, L4.19` is hand-labelled '<'.
- The definition of o_u ("windows … inside [u/2, 3u]", l. 1210) also formally reaches heights up to 1.5x in E_BR. Only
  supports within x/n ± R_n, n ≥ 2, are used.
- Repair: bound o_𝒜 by 2 sup ρ_𝒜 + 2 sup|K_𝒜ρ̃| ≤ 8L^{−4}, using Lemma 4.18 (E_cl at heights < t only) and (a)/(c). Then
  sup_v log v·o_𝒜 ≤ 8·min L^{−3} ≤ e^{−120} wherever 𝒜 ≠ ∅ (L ≥ Λ²e^{s_H}), so E_S ≤ 10⁻²⁸ is unchanged. Restrict o_u to
  windows meeting [u/2, 2u + R].

**NC-2 (FIXABLE) — Freedman in Lemma 3.11 (E3/E3′) without truncation.** See F-3.2.

**NC-3 (FIXABLE) — Freedman in Thm 4.3(i) (E2) is applied to slot windows whose physical position is not adapted to the
martingale.**
- X_q(W) counts q·m ∈ W for a slot window W = (k, j]. The physical interval [s_{k+1}, s_{j+1}) depends on T. T depends on γ_k,
  which is fixed at slot ≈ x_k + H/2. It also depends on 𝒜, whose members near W have latest primes decided up to y(x) + H/2.
- At the zero scales x ∈ [x_k + H, 2x_k], the contributing latest primes q ∈ [y(x), x/2] include q ≪ x_k. These are decided
  before γ_k exists. So X_q(W) is not F_{q}-measurable, and Σ_q(X̃_q − E[X̃_q|F_{q−}]) is not a martingale.
- Also v_W = 2M₁(ℓ_jit(W) + K_d) is random. Freedman's P(∃n: S_n ≥ a, V_n ≤ v) needs deterministic (or F_0-measurable) a, v.
- Repair, which is the template Lemma 3.11 already uses:
  - Apply Fr to deterministic physical windows I with endpoints on a fixed grid, and peel over the integer value of ℓ_jit(I).
    That is a union of ≤ L₀ + 1 Freedman bounds with deterministic (a(ℓ), v(ℓ)).
  - Sandwich slot windows between such I, at a cost of O(1) slots.
  - The union bound becomes ≤ 2(L₀+1)·#I·x^{−4} ≤ x^{−2}, which is negligible in the budget for every Λ.

**Stopped process.**
- Remark 1.0, §4.1 and the CL chain are consistent: the cap ρ̄_𝒜 is inactive on Good(<u) (Lemma 4.18 gives ρ_𝒜 ≤ L^{−4}).
- PIL (Lemma A.3) carries 1(G_{<s_p}) progressively and uses only F_{p−}-measurable sure bounds. ✓
- The places where "sure for the stopped process" is asserted but not true are NC-2 and NC-3. Both are repaired by truncation,
  deterministic windows and peeling, with no change of constants.
- Labels "on 𝒢" inside §5 (F-5.2) should read Good(<x).

**Λ-uniformity (brief item 4).** Every numeric threshold was traced as a function of Λ.
- **Not uniform as written:**
  - Prop 3.16(B) Step 3, U₀ = 10⁷ (F-3.1). Fails for Λ ≳ 3.9·10⁸; repair U₀ := Λ.
  - Lemma 4.15(c) at u = 10⁴ (F-4.3). Fails for log Λ > 1.84·10⁴; harmless in use; repair u ≥ max(10⁴, log Λ).
  - "log B, log H ≤ 2·10⁻⁶L at every scale" (F-0.1). False for L ≲ 5·10⁹ at any Λ; it gets better as Λ grows.
- **Uniform or improving with Λ (checked):**
  - (3.4), Lemma 3.9, (Osc), E_BR, ε_N, E_S.
  - Lemma 3.14A in all three ranges, and Lemma 3.14B with Λ₁ = 100Λ³ (≥ the ≈ 76Λ³ needed with log G ≤ Λ).
  - Prop 3.16(A) and Prop 3.18(a),(b).
  - Thm 3.4, Lemma 3.4A and Cor 3.5: the certificate is τ-uniform by construction, and the analytic pieces are monotone (not
    re-derived).
  - Thm 4.17 (analytic, plus the [N] grid up to Λ = 10³⁰), Lemma 4.18 (u₀ ≥ 2Λ), Lemma 2.0′ (u₀ ≥ 1.7·10⁹), (5.6) (∝ 1/Λ),
    Thm A.6 (L ≥ Λ ≥ 465), and the budget 1.5/Λ.

---

## Section 9. Summary of findings and verdict

**BLOCKING: none found.** I found no step whose failure cannot be repaired locally without changing the architecture or the
constants that matter (c′ = 0.15, the 0.549/0.96 margins, the 1.5/Λ budget).

**FIXABLE (each is an unproved or false-as-written step in the main line, with a local repair given above).**

| id | where (FROZEN lines) | defect | repair |
|---|---|---|---|
| F-3.3 | Cor 3.19 l. 1491–1499; Prop 3.18 l. 1436–1439; Thm 4.3 l. 1684 | R1′ proved only for I ⊂ [2X₀, ∞), but the queue bound is claimed from scale X₀. Windows in [X₀, 2X₀) and windows straddling 2X₀ are uncovered, and there are ≈ e^{2694} arrivals 2q there. | m = 1 − ρ_det below 2X₀⁻, and m = T′ − ½ρ̃(t/2) ≥ 0.73/log t on [2X₀⁻, 2X₀) |
| F-4.1 | Thm 4.3 l. 1685, 1714–1727 | Full blocks are counted in all slots, but the drift is per continuous slot. At x = X₀^{1.2} a block of L₀ slots has ℓ_jit ≈ 0.18L₀, so "exc ≤ 0" fails. | index blocks and 𝒲_x by ℓ_jit |
| NC-3 | Thm 4.3(i) l. 1696–1708 | Freedman applied to slot windows whose physical position depends on γ_k (zero scales) or on 𝒜, decided after some contributing q; and v_W is random. | deterministic grid windows + peeling over ℓ_jit, as Lemma 3.11 does |
| NC-2 / F-3.2 | Lemma 3.11 l. 1067–1076 | Freedman with the increment bound 2M₁ and the variance bound treated as sure for the stopped process; they are not certified at q's decision time when q < √(2u). | truncate (as Thm 4.3 does), and bound the variance on Good(<t(W)) |
| NC-1 | (Osc) l. 1288; Prop 3.18 l. 1432, 1453; Lemma 4.19(b) l. 2110 | The current-height local count (queue bounds at slots up to t + H) enters R1′ at t, contradicting (N2)/(N4). The depcheck '<' label is wrong. | bound o_𝒜 by sup ρ_𝒜 and sup K_𝒜ρ̃ (≤ 8L^{−4}); E_S is unchanged |
| F-3.1 | Prop 3.16(B) Step 3 l. 1380–1385 | U₀ = 10⁷ works only for Λ ≲ 3.9·10⁸ (Λ = 10⁸-only numerics) | U₀ := Λ |
| F-5.1 | Lemma 5.2(b) l. 2256–2269 | integration by parts against N − N_ℚ ignores the latest-prime filters on cofactors > √u (u > X₀²) | prime-level comparison of 𝒩 and ℕ gives \|μ₀\| ≲ κ(log u)³, which suffices for Prop 3.16(A) |
| F-4.3 | Lemma 4.15(c),(d) l. 1956–1974 | (c) is not Λ-uniform at u = 10⁴, and (d) uses (c) at u < 10⁴ | u ≥ max(10⁴, log Λ); trivial bound for the tail terms |
| F-0.1 | (L-a) l. 330–336, 163 | "log B, log H ≤ 2·10⁻⁶L at every scale" is false; (L-a) is false for θ near ½ at X₀ = e^{10⁸} | restate (L-a) as max(x^η, B + 3H + 3), or let X₀ depend on θ (θ = ¼ suffices for ¬Q) |
| F-3.6 | Thm 3.13 l. 1154–1207 | not self-contained; under B-lin the pole term and small-\|t\| zero-freeness need Lemma 2.0″'s fine form of Ê, not \|Ê\| ≤ C₈e^γΛ | two short paragraphs (Section 5) |

**COSMETIC:** F-0.2, F-0.3, F-0.4, F-3.5, F-3.7, F-4.2, F-4.4, F-4.5, F-4.6, F-5.2, and the literature corrections of Section 3
(Freedman form, Rosser–Schoenfeld ranges, Huxley attribution, Johnston–Yang θ-version, Broucke Thm 6.1, and the Diamond–Zhang
footnote, which belongs to BDR).

**What was not checked** (accepted on the earlier refereeing and the cited notes):
- the derivation of the closed form `S_cell` (Parts I/II chord bounds) behind the BS certificate;
- Thm 3.4's analytic regions (u < 2; ℓ ≥ 10¹⁸) and the base region's Lemma V detail;
- Lemma 3.3 for non-squarefree n;
- Lemma 3.14A's middle and huge ranges beyond their structure and Λ-dependence;
- Thm A.5 (SVL) and Prop 4.13 beyond spot checks;
- the full Landau/Perron argument of Thm 3.13 (gap-localPNT §2, §7′);
- Thm 4.12 (unused).

**Verdict.** As written, v3 does **not** yet prove Theorem A. The ten FIXABLE items above are unproved or false-as-written
steps in the main line. Three of them (F-3.3, F-4.1, NC-3) sit exactly at the §3/§4 seam: R1′'s domain, block units, and the
adaptedness of the queue martingale.

None is BLOCKING. Each has a local repair that leaves every numerical margin intact, and I see no obstruction to the strategy.

After these repairs, and conditional on the unchecked items listed above (all previously refereed), I would regard the main line
as a proof of Theorem A for θ = ¼, which suffices for ¬Q. For all θ ∈ [¼, ½) it needs F-0.1's restatement, X₀ ≥ X₁(θ).

**Minimal list of what is missing:**
1. R1′ on [X₀, 2X₀] (F-3.3).
2. Continuous-slot blocks in Thm 4.3 (F-4.1).
3. Deterministic windows with peeling for E2 (NC-3).
4. Truncation in Lemma 3.11 (NC-2).
5. Remove the current-height local count from (Osc) (NC-1).
6. U₀ := Λ in Prop 3.16(B) (F-3.1).
7. The filtered-range μ₀ bound (F-5.1).
8. The Lemma 4.15(c)/(d) range fix (F-4.3).
9. Restated (L-a), or θ-dependent X₀ (F-0.1).
10. The two B-lin details of Thm 3.13 (F-3.6).

---

## Section 10. Targeted re-check of the post-E2E version (2026-10-22)

Document: `notes/v3/beurling-greedy-v3.FROZEN-postE2E-2026-10-22.md`, 3006 lines, sha256 6d48f66f…a26 (checked). Line
numbers in this section refer to that file. I read the full diff against the E2E freeze (612 changed lines,
`/tmp/v3-referee/postE2E.diff`) and Appendix N's E.1–E.10 (l. 2876–2927).
- Reruns: the updated `capl_model.py` (c′^{−2} restored) gives 0 failures for Λ ∈ {10⁸,…,10²⁰}, and the updated
  `depcheck.py` reports 77 nodes, 168 edges, 27 ↓, acyclic. Both match the text.

### 10.1 The ten FIXABLE items

| item | repair (lines) | verdict |
|---|---|---|
| F-0.1 (L-a) | θ ∈ [¼, θ₁], θ₁ = ½ − 10⁻⁴ (l. 14, 155); new proof l. 338–342 | **Correct.** B ≤ H holds: B ≤ 34M₁L² ≤ (M₁²H_std)^{1/2} ≤ max(M₁², H_std) = H, since 34L² ≤ e^{4ℓ²}. Then log(B + 3H + 3) ≤ 8ℓ² + 10⁻⁶L + 2 ≤ 2.816·10⁻⁵L at L = 10⁸, decreasing in L, against η ≥ 5·10⁻⁵. |
| F-5.1 μ₀ | Lemma 5.2(b) l. 2382–2410; use in Prop 3.16(A) l. 1386–1398 | **Correct** (re-derived at spot-check depth; see 10.3). |
| F-3.3 R1′ from X₀ | Prop 3.18(c) l. 1485, 1531–1540; Cor 3.19 l. 1546–1562; Thm 4.3 "base scales" l. 1818 | **Correct.** m = 1 − ρ_det ≥ MA[ℙ] − 1/(κt) on [X₀, 2X₀⁻). On [2X₀⁻, 2X₀), only w = 2 enters and ρ̃(t/2) ≤ ½(j₀ + o_{X₀}) + 3/H, so m·log t ≥ 0.99 − 0.25005 − 10⁻⁹ = 0.7399. This is sure, with no event. Cor 3.19's extension to physical windows and to I starting below X₀ is right, because ∫_I m = ℓ_jit − Comp ± 2 is pathwise for any interval. |
| F-4.1 blocks | Thm 4.3 l. 1753–1755, 1804–1817 | **Correct.** Blocks are counted in ℓ_jit, and the split is at k′ with ℓ_jit((k′, j]) = L₀. (4.6) holds with margin 135M₁L², since −c′ℓ/L + √(16M₁L(ℓ+K_d)) is decreasing for ℓ ≥ 177.8M₁L³, well below L₀ = 2133M₁L³. |
| NC-3 adaptedness of E2 | Thm 4.3 l. 1756–1786; Def 4.4 l. 1824–1835 | **Design correct**: deterministic integer-endpoint windows, peeling over ℓ_jit with deterministic (a(ℓ), v_ℓ), and the union ≤ 2(L₀+7)·#ℐ_x·x^{−4} ≤ x^{−2}. **One new FIXABLE slip in the timing (P-1 below).** |
| NC-2 Lemma 3.11 | l. 1082–1101, 1110 | **Correct.** The increments are truncated. The event "X_q ≤ 2M₁ for every offset" is F_{q−}-measurable and holds on Good(<t(W)) via E_cl^{(u)}, whose time 8u/L¹¹ + H is < t(W). The variance bound is on Good(<t(W)), and the sure bound ρ̃ ≤ 1.01 replaces the local count. The hypothesis is now Good(<y + H(y)). |
| NC-1 (Osc) | (Osc) l. 1322–1334; Lemma 4.19(c),(d) l. 2227–2241; Lemma 4.18 l. 2200–2201 | **Correct.** o_𝒜 ≤ 2 sup\|σ_𝒜\| ≤ 4L⁻⁴. Here (c) uses Rankin on y-smooth cofactors with the sure bound ρ̃ ≤ 1.01, and Lemma 4.18 holds on Good(<t) up to height t + 1.01H(t), since 9(t + 1.01H)/L¹¹ + H < t. No current-height local count remains in §3, and o_u is restricted to windows meeting [u, 2u). |
| F-3.1 U₀ | Prop 3.16(B) Step 3, l. 1426–1430 | **Correct.** The two terms are 1.5Λ⁴·2δ/κ ≤ 3Λ⁴X₀^{−0.103} and Σ_{u≥Λ} ≈ 87Λ^{4.65}e^{−0.103Λ}. Both are uniform in Λ (the text's X₀^{−1/12} and e^{−Λ/12} are weaker and still fine). |
| F-4.3 Lemma 4.15 | l. 2058, 2071–2080 | **Correct.** |
| F-3.6 Thm 3.13 | l. 1191–1194, 1207–1208, 1222–1238 | **Correct in substance**: step (4) gives −P_y′/P_y(1+η) ≤ 1/η + 0.43; step (5) gives \|E\| ≤ 3X₀^{−0.3}(1+\|t\|) and \|(s−1)ζ♯ − 1\| ≤ 0.044; c_LP = c_zf/5 from shifting to σ = 1 − 0.9δ_zf(T₁); LP⁺ needs 76Λ³ ≤ 100Λ³. **Three COSMETIC points** (C-3 below). |

### 10.2 New finding in the repaired skeleton

**P-1 (FIXABLE) — the queue-constraint time s_j + 3 rests on a false bound on slot length.** Lines 109–113, 116, 1793,
1824, 1856–1858.
- Theorem 4.3(ii)'s sandwich takes W = (k, j] with physical interval [s_{k+1}, s_{j+1}) and I = [⌊s_{k+1}⌋, ⌈s_{j+1}⌉). It then
  claims t(I) = b ≤ s_{j+1} + 1 ≤ s_j + 3 "since slot spacing is ≤ 1.01" (l. 1793). The whole first-failure timing depends on
  this: (D), (N1), (N2), Def 4.4, and Lemma 4.5's "E2 → queue constraint at time s_j + 3".
- **Slot length is not ≤ 1.01.** A slot lasts until T rises by 1, either at the next unit jump (a rigid integer or an 𝒜 element)
  or by continuous growth. The only proved bound is s_{j+1} − s_j ≤ 1/min T′_cont ≤ 11.3L, from (G1).
- Unconditional counterexample to "≤ 1.01": for every prime p ∈ (X₀, 2X₀), p ± 1 are X₀-smooth. The slot starting at the jump
  at p − 1 runs to p + 1, because the continuous growth on (p−1, p+1) is ≈ 2/Λ. So it has length 2.
- Length > 2 needs ≥ 2 consecutive non-X₀-smooth integers where T′_cont < ½, i.e. at heights between X₀ and about X₀^{1.6}.
  - Example: a Sophie Germain pair q, 2q+1 ∈ [X₀, 3X₀) with 2q − 1 smooth gives a jump slot [2q − 1, 2q + 2) of length 3.
  - At heights X₀^{1.01}–X₀^{1.4}, T′_cont < ⅓ and runs of three non-smooth integers are expected at positive density, giving
    length ≈ 4 and b > s_j + 3.
  - I have not proved that such runs exist. What matters is that s_{j+1} ≤ s_j + 2 is not proved, and is very likely false.
- Consequence: when the last slot has length > 2, the Fr(I) that (ii) needs has time b > s_j + 3. So (D) "Good(<s_j + 3) ∩
  ⋂_{t(E)=s_j+3}E ⊂ {Q_j ≤ B}" is not established. ℐ_x's right-end range b ≤ 2x + 2 (l. 1757) can also be exceeded.
- Repair:
  - Give the queue constraint at j the time t_j := ⌈s_{j+1}⌉ + 1, and allow b ∈ [x, 2x + 12L + 2] in ℐ_x.
  - t_j is predictable: s_{j+1} ≤ s_j + 11.3L is determined by T on [1, s_{j+1}], hence by slots ≤ s_{j+1} − H < s_j (Lemma 1.1).
  - Every consumer of a queue constraint has margin ≥ H ≫ 12L, so it is unaffected. These are Cor 4.2 (after z + 7H), the
    Lindley step (s_{k′+1} ≤ s_j − 0.99L₀ + 12L), (H_BS), and Lemma 3.11's E_edge at scales ≤ x/2.
  - The events with time in (s_j, t_j] do not use Q_j, since Good(<t(E)) excludes it by definition and their proofs (Fr(I),
    E3/E3′, E_cl, Land) read only lower heights.
  - The union count changes by a factor ≤ 2.
- With this repair the new timing creates **no circularity**. I traced every event with time ≤ t_j used by (ii), and none
  reads Q_j or any later queue constraint.

### 10.3 Spot-check of the new Lemma 5.2(b) (E.2)

- **Step 2.** dε*dN_𝒩 = log·dΔ − dψ*dΔ follows from the two Chebyshev identities, where ε = ψ_𝒩 − ψ, supported on [X₀⁻, ∞).
  - The κ-part gives |h| ≤ 2κt log t + 2κt + 2κt(log t + 0.43) ≤ 5κt log t. The non-κ parts are ≤ κtX₀^{−0.1}, using θ ≤ ½,
    κ = X₀^{−0.3967}, and B + 3H ≤ s^{3·10⁻⁵}.
  - Inverting with |μ_𝒩| ≤ dN_𝒩 and Σ_{v≤t/X₀⁻}1/v ≤ log t − Λ + 1 gives |ε(t)| ≤ 5κt log²t. ✓
- **Step 3.** Replacing one large prime at a time against d(ψ_𝒩 − ψ)/log:
  - the boundary terms are ≤ 10κf₀log b/c, and the integral is ≤ 5κ·1.1∫G log p dp ≈ 2.75κf₀log²b/c;
  - Σ1/c ≤ 1.01e^γΛ·ℓ_u^{k−2}/(k−2)!, and Σ_{k≥2}(k−1)ℓ^{k−2}/(k−2)! = (1+ℓ)e^ℓ;
  - so the total is ≤ 7.4κ(log u)³(1 + log log u)/Λ, which is ≤ κ(log u)³ for log log u ≤ Λ/8. ✓
- The large-prime measures (jittered ≥ X₀⁻ against rational ≥ X₀) differ exactly by ε, because rational primes in [X₀⁻, X₀)
  lie in 𝒟 in both systems. Only heights ≤ u/2 are read, on Good(<u).
- Prop 3.16(A): 2.1κ(log x)⁵ ≤ 2.1X₀^{−0.3967+0.05} ≤ X₀^{−0.34} for log x ≤ X₀^{1/100}, which lies inside log log u ≤ Λ/8. ✓

### 10.4 Did anything else break? (seams re-checked)

- c_LP = c_zf/5 is used only in Prop 3.16(B). There, C′ = (4(1−θ)/c_LP)² ≈ 2.9·10⁴Λ² keeps the Step 4 term
  ≤ 1.9·10⁴Λ²/X₀², which is inside the new explicit o(1) bound (l. 571–574). LP⁺ (Lemma 3.14B) still uses c_zf.
- B: §3's "B ≤ 28M₁L²" still holds with the new additive terms (26.67M₁L²(1 + 10⁻⁷)). B ≤ H holds.
- Cor 4.7 for windows up to 12LL₀ + 2: |I|/y ≤ 13/(HL⁵) ≪ δ₁. When 𝒜 = ∅, q ≥ X₀⁻ > y, so the same holds.
- (F1) with factor 1 + κ₊/log t gives θ = 1 + 1/L in PIL; Thm A.6's chain is unaffected.
- Prop 4.6 low heights, Lemma 4.18's time t_u = 9u/L¹¹ + H, and Lemma 4.19(c): ✓.
- **C-1 (COSMETIC).** Prop 4.6's "two jittered primes give ≥ (X₀⁻)² > 2z for z < X₀²/2" (l. 1891) fails if 2z ∈ [(X₀⁻)², X₀²).
  That can happen only when X₀ sits just above a power of 2. It is harmless, because then z ≥ X₀ and Thm 4.17 covers the case r < r₀.
- **C-2 (COSMETIC), stale text:**
  - Def 4.4's E1 row says "left end in [X₀, …]" (l. 1831); it should be [X₀/2, …].
  - The §4 Applied list says t(I) = b/2 + H(b/2) (l. 2993), against t(I) = b in Thm 4.3 (l. 1763).
  - Lemma 3.11 says "continuous slots have length ≥ 1 − 10⁻⁸" (l. 1094). It means the spacing of continuous-slot starts; with
    that reading ρ̃ ≤ 1.01 is right.
  - (5.3) still says "log X_LP ≈ 2·10¹³ … linear in log X₀" (l. 2434–2435).
- **C-3 (COSMETIC), Thm 3.13:**
  - "The zero-free region is … for all t" (l. 1231) overstates. Landau's step needs η(t) ≥ η_y = 17 log log y/log y, i.e.
    log(|t|+3) + 500 ≲ log y/(51Λ log log y). Under B-lin (c_zf ∝ 1/Λ) this binds, contrary to gap-localPNT §7′.2's "never
    binds". It forces log X_LP ≳ 10⁴Λ²(log log X_LP)², so log X_LP = O(Λ² log²Λ), not O(Λ²).
  - The old X_LP ≈ 2·10¹³ violated this too.
  - Every use has slack: range (B) starts at log x = X₀^{1/100}, and LP⁺ uses log v ≥ 100Λ³, where
    log y/log log y ≥ 1.6Λ³ ≫ 102Λ². So no conclusion changes.
  - The corner |t| < 1/16 < |s − 1| is covered by running the (s−1)ζ♯ estimate on |s − 1| ≤ 1/8, where 0.6/8 < 1.
- §0.3 (N2)'s list "local counts at heights ≤ u/4 or ≤ √u" omits Prop 3.16(B) Step 1's local count at height x(1−δ). That use
  is time-ordered (read before x − δx + 7H < x), so the omission is COSMETIC.

### 10.5 Updated verdict

- All ten FIXABLE items of Section 9 are repaired, and each repair is correct. The cosmetic and literature corrections are applied.
- The repairs introduced **one new FIXABLE item, P-1**: the queue-constraint time s_j + 3 rests on a false slot-length bound.
  The fix is to use t_j := ⌈s_{j+1}⌉ + 1. They also introduced the COSMETIC items C-1 to C-3.
- **No BLOCKING item.**
- With P-1 repaired, I find no remaining gap in the parts I checked. The main line then proves Theorem A for θ ∈ [¼, ½ − 10⁻⁴];
  in particular θ = ¼ gives ¬Q.
- This is conditional only on the items listed as not re-derived in Section 9: the S_cell derivation, Thm 3.4's analytic
  regions, Lemma 3.3 for non-squarefree n, the interior of Lemma 3.14A's middle and huge ranges, SVL, and the full Landau/Perron
  write-up in gap-localPNT. All of these were refereed earlier.

---

## Section 11. Short confirmation of the post-recheck version (2026-10-22)

Document: `notes/v3/beurling-greedy-v3.FROZEN-postRecheck-2026-10-22.md`, 3053 lines, sha256 10c6502f…340c (checked). The diff
against the post-E2E freeze is in `/tmp/v3-referee/postRecheck.diff` (≈ 105 changed lines). Line numbers below refer to the new file.

**P-1 — confirmed repaired.**
- Def 4.4 (l. 1833), §0.3 (N1)/(N2) (l. 109–122) and Lemma 4.5 (D) (l. 1865–1872) all use t_j := ⌈s_{j+1}⌉ + 1.
- t_j is predictable: s_{j+1} − s_j ≤ 11.3L by (G1), and T on [1, s_{j+1}] is fixed by slots ≤ s_{j+1} − H < s_j (Lemma 1.1).
- Thm 4.3(ii) (l. 1777–1827) is consistent with this timing:
  - The sandwich has b = ⌈s_{j+1}⌉ ≤ t_j and b ≤ s_j + 11.3L + 1 ≤ 2x + 12L + 2, so I ∈ ℐ_x.
  - Lengths are ≤ 12L(L₀ + 1) + 2, and the count rises to (x + 12L + 2)(12L(L₀+1) + 3), so the total stays ≤ x^{−2}.
  - The Lindley step needs t_{k′} ≤ s_{k′+1} + 2 ≤ s_j, which holds because a full block is ≥ 0.99L₀ ≫ 12L long.
  - Cor 4.7 (l. 1915) is widened to I ⊂ [u, 2u + 12L + 2], with |I|/y ≤ 13/(HL⁵) ≪ δ₁.
  - The E2 row (l. 1841) matches.
- **No new circularity.**
  - Good(<t(E)) contains Q_j only if t_j < t(E). So no event with time ≤ t_j can use Q_j.
  - The proofs of Fr(I), E3/E3′, E_cl and Land read only lower heights.
- Consumer margins all hold, since each is ≥ H ≫ 12L:
  - Cor 4.2 at height z reads constraints with t_j ≤ z + H + 12L and runs after z + 7H.
  - Prop 3.16(B) Step 1's local count is read before u − δu + 7H < u.
  - (H_BS) and Lemma 3.11's E_edge read heights ≤ x/2.
  - The Lindley step reads t_{k′} ≤ s_j.
- **COSMETIC:** Thm 4.3's header still sets L := log(2x + 2) (l. 1758), but the windows now reach 2x + 12L + 2. R1′ needs
  L ≥ log max I. The difference is a relative 6L/x in c′/L, which the margin 0.549 ≥ 1.01c′ absorbs. Write L := log(2x + 12L + 2)
  or note the slack.

**C-1, C-2, C-3 — confirmed.**
- C-1: Prop 4.6's low-height case is now 2z < (X₀⁻)², which includes [X₀/2, X₀), and z ≥ X₀ is deferred to the general argument
  (l. 1901–1903).
- C-2:
  - E1 now starts at X₀/2 (l. 1840).
  - The Applied list now reads t(I) = b (l. 3034–3036).
  - Lemma 3.11 now says slot starts are ≥ 1 − 10⁻⁸ apart and §3 uses no upper bound on slot length (l. 1097–1098). I checked that
    §3 indeed uses none: its edge cells are bounded by A_j ≤ B + 1, not by slot length.
  - (5.3) and §0.4 give O(Λ² log²Λ) (l. 159, 2447–2451).
- C-3, Thm 3.13 (l. 1233–1245):
  - The near-pole step on |s−1| ≤ 1/8 gives |ζ − 1/(s−1)| ≤ 0.59 and |(s−1)ζ♯ − 1| ≤ 0.075 + 10⁻⁹. It covers |t| < 1/16 for
    σ ≤ 1.1, since √(0.1² + (1/16)²) = 0.118 ≤ ⅛, and (2) covers σ > 1.1.
  - The region is stated for |t| ≤ T_y with log T_y = log y/(51Λ log log y) − 500.
  - For (i)–(ii), with y′ := v, the heights up to T₁ ≈ e^{2√log v} lie below T_v once √log v ≥ 102Λ log log v, i.e.
    log v ≥ 1.04·10⁴Λ²(log log v)². The stated 1.1·10⁴ is right.
  - For LP⁺, log y ≥ Λ_p ≥ 100Λ³ gives log T_y ≫ L₁ + 500. (The phrase "≤ 2.1Λ" holds only while log Λ_p ≤ 0.05Λ, but log T_y
    grows faster than L₁ in any case. COSMETIC.)

**Final verdict.**
- The end-to-end review found ten FIXABLE gaps and no BLOCKING one. All ten have been repaired correctly. So have the follow-up
  P-1, which moved the queue-constraint time to ⌈s_{j+1}⌉ + 1, and the cosmetic items C-1 to C-3.
- What remains is two trivial COSMETIC points:
  - Thm 4.3's L := log(2x + 2);
  - the "≤ 2.1Λ" phrase in Thm 3.13's LP⁺ remark.
- The certificates reproduce, the load-bearing literature matches its sources, the first-failure skeleton is time-ordered with no
  circularity, and every threshold I traced is uniform in Λ ≥ 10⁸.
- In my judgment the post-recheck v3 proves Theorem A for θ ∈ [¼, ½ − 10⁻⁴]. In particular θ = ¼ gives a discrete Beurling system
  with N(x) = x + O(x^{θ′}) for every θ′ ∈ (¼, ½) and zeros of ζ_P with real parts tending to 1, so Q is false.
- This is conditional only on the components I did not re-derive and which were refereed earlier:
  - the S_cell closed form behind the BS certificate;
  - Thm 3.4's analytic regions;
  - Lemma 3.3 for non-squarefree n;
  - the interior of Lemma 3.14A's middle and huge ranges;
  - SVL (Thm A.5);
  - the full Landau/Perron write-up in gap-localPNT.
