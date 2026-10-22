# Final check of the paper against the refereed v3

- **Paper checked:** `paper/` at commit d307ffd. HEAD moved to 16e62d8 during the check. That commit changes only source
  comments, `LABELS.md` and `README.md`, one line for one line, so the rendered PDF and all line numbers are the same.
- **Not checked:** while the check ran, uncommitted edits appeared in the working tree, in `CORRECTIONS-vs-v3.md`
  (new entries #11–#19), `02-construction.tex`, `03-zeros.tex`, `04k-kernels.tex` and `A-rankfull.tex`. They respond to the
  sub-reports listed in §0. This report does not cover them, and they need their own check.
- **Source:** `notes/v3/beurling-greedy-v3.FINAL-2026-10-22.md`, sha256 b6c6bcda…5c, 3072 lines, read-only.
- **Corrections log:** entries 1–10 as committed in d307ffd.
- **Line numbers:** every file:line refers to `paper/sections/` at d307ffd unless stated otherwise. "v3 l.N" is a line of
  the source.

## 0. Method

- **Section checks.** Five independent sub-checkers each compared one part of the paper with v3, item by item. Section
  numbers here are the compiled ones (00-intro is §1, …, 04* is §5, 05-queue is §6, 06-base-range is §7); the brief's
  "§4" is compiled §5 and its "§5" is compiled §6.
  - §1–§4 and §7 (files 00–03, 06, abstract, App. C);
  - §5 part 1 (04-noise, 04a–04e);
  - §5 part 2 (04k, 04x, 04f, 04g);
  - §6 (05-queue);
  - Appendix A.

  Each recomputed constants in Python (run with `-I`; arb where needed) and re-derived the inlined proofs.
- **Done by the lead checker:**
  - the build;
  - every certificate run;
  - the jargon and hard-coded-number scans of the rendered text;
  - the intro and Appendix C reading;
  - an independent re-verification of every finding marked BLOCKING or "must fix" below.
- **Raw sub-reports:** `/tmp/paper-check-{s1236,s4a,s4b,s5,appA}/REPORT.txt`. Someone else has also copied them to
  `review/subchecks/`.
- **Numbering.** The compiled numbering differs from the v3 numbers used in the brief and the log. The brief's
  "Thm 3.4 (BS)" is Theorem 5.6 in the PDF. "Thm 3.13" is 5.24, "Prop 3.8" is 5.18, "Lemmas 3.14A/B" are 5.27 and 5.32,
  and "Thm 4.17" is 6.22. In Appendix A, compiled Lemma A.2 is the Volume Lemma, and the pattern sum ("A.2" in the log) is
  A.4.

**How the classes are used.**
- **BLOCKING:** a main-line step that the paper does not prove (false, or only sketched), where this check could not
  verify a complete repair. Also unlogged drift that changes a downstream statement.
- **FIXABLE:** an error or gap whose repair is local and was checked here, including errors inherited from v3. Items
  marked **must fix** are substantive; the rest are routine.
- **COSMETIC:** everything else.

The sub-checkers classed everything FIXABLE or lower. I upgraded one item, B1, to BLOCKING under the definition above
(§6).

## 1. Build

- **Command:** `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=/tmp/paper-check-build main.tex`, run in
  `paper/`. Exit status 0.
- **Pages:** 94.
- **Undefined references:** 0.
- **Undefined citations:** 0. All 19 cited keys are in `refs.bib`, and every bib entry is cited.
- **Multiply defined labels:** 0.
- **Dead placeholder labels.** The labels `sec:kernels`, `lem:xb` and `lem:si` are also defined in the fallback branches
  of `\InputIfFileExists` (04-noise.tex:36-38, 04f-bridge.tex:38-41). Those branches are never compiled, so they do no
  harm. Delete them (COSMETIC). They also contain v3 numbering ("Theorem~3.6", "Lemma~3.14A").
- **BibTeX:** 4 warnings: missing journal and pages for Broucke2024 and Broucke2025, both arXiv preprints. Use `@misc`
  (COSMETIC).
- **Overfull hboxes:** 96, of which 57 exceed 20pt (COSMETIC). The worst are about 168pt near 06-base-range.tex:71,
  133pt at B-certificates.tex:127, 129pt at 04k-kernels.tex:381 and 129pt at A-rankfull.tex:495. These locations come
  from the log and are approximate.
- **hyperref:** three "Token not allowed in a PDF string" warnings (COSMETIC).

## 2. Certificates (Appendix B), all re-run

- **Setup.**
  - The scripts were run from a pristine `git archive` export of `certificates/`, so that no `__pycache__` was written
    into the repository.
  - Each command was exactly as printed in Appendix B, from the export's root.
  - python-flint 0.9.0 came from `/tmp/rhscratch/flintenv`, under Python 3.15.
- **Result:** every printed output matches the quoted output character for character, except the timings.

| certificate | command (App. B) | result |
|---|---|---|
| bs-cert, main region | `cert_run_arb_patched.py 1.05 10` | `bands=403 cells=302013 failed=0 min certified l*S=2.491e+06` at the quoted cell; 13 s |
| bs-cert, unpatched twin | `cert_run_arb.py 1.05 10` | identical numbers, as the appendix states |
| bs-cert, one-variable checks | `aux_cert_arb.py` | 9609/0/0.189; 13823/0/1.724; **1387/0/0.829** (the [1,2] cover of correction #10); 1.3 s |
| x0-band | `x0band_exact.py 1000000` | Hmax, Xmax, int64 ok; top list; five sup lines; tail bound 0.137388…; 6.6 s |
| capl-cert | all six scripts | `s_H = 5.9745`; "decreasing" on every line; 4842/5072/5302/5763/6684/7605 points, 0 failures; refereeB line identical; cert_capl 20790 + 398801 cells, 0 failures; raise_max 1.292e-08, OK |
| lemma-sc | the five quoted commands | all five dictionaries identical |
| svl-stress | `svl_stress.py` | the four lines identical, 0 violations; **3.5 s, not "a few minutes"** (COSMETIC) |
| depcheck | `depcheck.py` | `acyclic: True, nodes 77, edges 168, strictly-earlier 27` |

**Checks of the scripts against the paper's claims.**
- The sub-checkers read the code against the claims made for it.
- `aux_cert_arb.py` does include X(u) and the extra allowance 2K_M r_up(u)(e^{0.141}−1), as correction #10 says.
- x0-band computes exactly the B(n) of App. B. I verified B(6) = 5/12 by hand.

**Findings on Appendix B.**
- [FIXABLE] B-certificates.tex:176-186 and `depcheck.py`. The graph is no longer "the full dependency graph". Three
  corrections add edges that are not encoded (v3 numbering, as in the script's node names).
  - Correction #2: (F3′) → Thm 4.17(c).
  - Correction #4: Prop 3.8 → Lemma 4.18 and Prop 4.6.
  - Correction #5: Lemma 3.14A → Prop 3.14 and Lemma 3.9.

  The sub-checkers added them to copies of the script. The #4 and #5 edges keep the graph acyclic. The #2 edge creates
  the same-time cycle T4.17 → L4.14 → P4.13 → LA.4 → (F3′) → T4.17. The cycle is spurious: Theorem 4.17(c) is a
  deterministic fact about the parameters, and Step 6 does not use (a). Split T4.17 into an (a) node and a (b)/(c) node,
  add the edges, and give a node-to-`\ref` map; the node names are still v3's ("T4.3" for Theorem 6.6).
- [COSMETIC] Further notes on Appendix B:
  - App. B gives the capl-cert scripts without command lines.
  - B-certificates.tex:63 should cite Prop. xb-ranges(i), not Lemma xb.
  - B-certificates.tex:119: the value 1.3e-8 is quoted in rem:caplw-numerics, not in "Step 6".
  - Script names `*_refereeA.py` and `*_refereeB.py` appear in the rendered text. The script headers and READMEs name
    internal agents and working notes ("gap-G3 §16.22′", "verify-CL §R.12″", "lead-notes L1", `/tmp/rhscratch`).
  - svl_stress check C7 is vacuous (`ts = range(joined, T)` is always sorted and distinct), so "per-row block ranges are
    disjoint" (B-certificates.tex:167) is checked only trivially.
  - The F_{1/2} maximum on ℕ (1.3296 at y = 7, 04f-bridge.tex:118) and the ℕ facts in Lemma CM (04a-setup.tex:169,
    175-176) are finite computations that are not among the certificates. Both were reconfirmed (to 10⁶ and 2·10⁶). Add
    them to App. B.

## 3. The ten logged corrections

Each entry is judged on three points: (i) is it applied, consistently, everywhere the quantity appears; (ii) is it
mathematically correct; (iii) is its "no downstream effect" claim true.

| # | applied everywhere? | correct? | downstream claim | residual findings |
|---|---|---|---|---|
| 1 | yes: A-rankfull 131-134, 153, 493-497, 529, 550-552; 05-queue 456-459; no stale e^{2k/X₀} anywhere | yes. Re-derived: ⌊2H/0.99⌋+1 indices at X₀, then spacing 0.99; (2.03H+1)/(X₀−1) ≤ 3H/X₀ + 1/(X₀−1); 1.0102·log ≤ 1.02·log | true: θe^{(3H+2)/X₀}e^{2.2/Λ} ≤ 1.0022 ≤ 1.01 | proof says "τ_j ≥ X₀+0.99i" (A-rankfull.tex:147), off by one, harmless; "H(X₀)/X₀ ≤ e^{−10⁷}" (133, 496, 552) has no reason given (cite eq:jitter and Thm 6.22(c)) — COSMETIC |
| 2 | yes: 05-queue 98, 113-115, the only occurrence | yes. Values > s/2; (1−2/s)^{−(2H+1)} ≤ e^{5H/s} ≤ e^{10⁻⁹}; 2.20/Λ + 1/X₀ + 1/(2Λ²) ≤ 2.21/Λ; A_s ≤ 1.8(log z+1) in both branches | true | [FIXABLE] the new dependency (F3′) → Thm 6.22(c) is not recorded (§2 above) |
| 3 | yes, at every site listed in the log; λ₀ appears nowhere else | yes. Thm 5.15 (3.6′) proof complete; Θ_n ≤ e^{10⁻⁴δ} ≤ λ₀ | true: 1 + 1.033665e^{2.1δ} = 2.0337 ≤ 2.034, C_N = 157.08 ≤ 158; λ₀² ≤ 1+7δ absorbed; the x0-band λ = 1.0001 covers λ₀(10⁶)^{ε*} = 1.0000423 | [COSMETIC] λ₀ is missing at 04k-kernels.tex:417 ("C_NE_η ≤ ½", "2.04θ* ≤ 0.02") and 352-354; 01-setup.tex:118,122 cite thm:kr where thm:kr-random is the result applied |
| 4 | yes, at 04k-kernels.tex:337-340 | yes. Lemma 6.25 (Lemma P) gives #𝒜(J) ≤ (1+o(1))(v/X₀)^{θ/2}(log(v/X₀))^{−4}; the log's "+M₁" is not needed | true: 1.52 (actual 1.516), 5.1C_N (5.06), 3.2 (3.192) stand | the same omission survives in Prop 5.35 (G1′), see I7 |
| 5 | yes: eq:xb, eq:jX0, nominal D_d, Prop 5.38(b), all three ranges | yes. 2.04λ₀·2C_N ≤ 4.1, plus 3.04λ₀C_N²τ₀E_η ≤ 0.1C_NE_θ since η̃ ≤ θ/log²X₀⁻; 4.3C_NE_θ ≤ e^{−0.99Λ} | **as worded, not quite**: the log's "≤ e^{−10⁷} elsewhere" is too weak for the middle range | [FIXABLE] 04x-x0band.tex:276-279 uses "4.3C_NE_θ ≤ e^{−10⁷}" to get j_X₀ ≤ e^{−0.0009Λ}, which is false for Λ > 1.1·10¹⁰. Use e^{−0.99Λ} (Lemma 5.20, already stated at 04x:42). The 4.1 also needs a non-terminal bound missing from Prop 5.18's statement (S11) |
| 6 | yes | yes. w₁′ is exactly p ≤ √(2tY); ℓ ≥ 30τ > 3τ+log2; w₁′(30τ) = 0.935484 ≥ 29/31−10⁻⁸; ℓμ₀ ≤ 2.0011τ+1.387; 2713.05 ≤ 2714; for u ≥ 2, w_lo ≥ 1 > w₁′ | true: Z2, certificate, ℓ ≥ 10¹⁸ and Lemma 5.8 unchanged | [COSMETIC] x′ ≤ 1/30 + 2.4·10⁻¹⁰, not +10⁻¹⁷ (04c:233); rounded constants give 0.2648τ against exact 0.2651τ (04c:239, 398) |
| 7 | yes: 05-queue 6, 263 | yes | true: every use needs only B ≤ 34M₁L² ≪ H = x^{o(1)} | [COSMETIC] stale "not polylogarithmic" at 05-queue.tex:218 |
| 8 | yes: 05-queue 984 | arithmetic yes (6·2.04 = 12.24 ≤ 12.3) | true, but only trivially | [FIXABLE] Lemma 6.26(b)'s first inequality is unproved: Cor 6.3 cannot bound #𝒜, which cancels in N−T. (b) has no consumer (04f-bridge.tex:59; tab:queuedeps). Delete (b) or re-prove it from Lemma P |
| 9 | yes: 04f-bridge 119-121 | yes. \|Q(u) − 6u/π²\| ≤ 3√u (max ratio 0.68 on [1,10⁶]); tail ≤ 1.2396 ≤ 1.25; max on ℕ to 10⁶ is 1.32963 at y = 7 | true | [COSMETIC] the 𝒩-versus-ℕ part ("relative O(η₁)") is still not explicit; harmless, since F_θ only multiplies o(1) |
| 10 | yes; certificate verified | yes for (a) and (b): 0.8334 on [1.5,2); 0.1334(log72+1.44) = 0.7626; u < 1.0428; X(u) right in the 𝒩(u) normalisation; max F gives exactly 2K_M r(u) | true | [FIXABLE] the base-case inequality is still false as written, see S3. [FIXABLE] unimodality of F (needed for TV ≤ 2 max F) is asserted without proof (04a:259-266); one line suffices: G_V increases for s ≤ 1, and (log G_V)′ < 0 on [1,u]. [COSMETIC] the allowance change 15 → 22 (04a:276) is not in the log |

**Summary.** All ten corrections are mathematically right and applied wherever the quantity appears. Two need small
follow-ups: #5's weaker bound used in the middle range, and #2's unrecorded dependency edge. Two leave text around them
that is still wrong: #10's base case and #8's unproved, unused lemma. None changes Theorem A.

## 4. Unlogged drift

The sub-checkers found no unlogged difference that changes a downstream statement. Four mathematical differences are not
in the log.

- **D1 [FIXABLE, must fix] Lemma M, 04c-saias.tex:24 (v3 l.743-746).**
  - The paper states c_n(y) = μ(n)χ^t_y(n)·1[y/n ≥ X₀⁻]; v3 states c_n = μχ.
  - The paper is right. v3's own recursion (l.739-740) contains the cutoff, and v3 itself uses the cut form later (l.1389).
  - Two definitions were not updated: 04a-setup.tex:80 and eq:nominal-mass (04k-kernels.tex:55) still read
    c_n = μχ. The bound Σ|c_n|/n ≤ Σ_{n ≤ y/X₀⁻} needs the cutoff.
  - Fix: log it and update the two sites. The lead has drafted entry #11 in the working tree.
- **D2 [FIXABLE] 04k-kernels.tex:41-43, 80 (v3 l.915).**
  - v3 states the local exponent ε* ≤ 3·10⁻⁶ of H. The paper dropped this and uses the global ε ≤ 0.03.
  - With ε = 0.03, two displayed inequalities are false: ½ + 1.02·2^{ε−1} = 1.0207 > 1.02, and 1.02·2^{ε−1} = 0.5207 > 0.52.
  - Fix: restore ε* (04x-x0band.tex:21 already defines it).
- **D3 [COSMETIC] Cor 5.9, 04c-saias.tex:418-422.** "4v ≥ 2X₀⁻" silently fixes v3's "2X₀". Log it.
- **D4 [COSMETIC] Lemma V, 04a-setup.tex:276.** The prime-power allowance changes from 15e^{−0.4L_z} to 22e^{−0.4L_z}.
  The paper explains why; add it to entry #10.

The only paper-only decimal constant in §6 (05-queue) is 12.3 (correction #8). The powers of ten match v3's. The items
of §1–§4, §7 and App. A match v3 apart from (b) inlined proofs and (c) rewording; the coverage is in §8.

## 5. Errors inherited from v3

These are faithful transcriptions of v3 text that is wrong, so they are not drift. Each needs a fix and a new log entry.
None changes a downstream statement; a sub-checker verified each repair. The lead's uncommitted entries #12–#19 already
draft several of them.

- **I1 [FIXABLE] eq:lag, 02-construction.tex:206-208 (v3 l.318-320).**
  - The paper has −H/2−2 ≤ D ≤ max Q + H/2 + 2.
  - The continuous-slot density is up to 1 + κ₊/log x + 1/(κx), not 1. So up to (H/2)(1+κ₊/log x)+2 primes can be decided
    within H/2 of x on each side. At zero scales the excess (H/2)κ₊/log x is much larger than 1.
  - Fix: use (H/2)(1+κ₊/log x)+3, as in (F1) (05-queue.tex:86), and propagate it to 02-construction.tex:229, 03-zeros.tex:13,
    05-queue.tex:8 and 379, and 04e-lp.tex:8.
  - Every consumer only needs ≤ B+3H+3 ≤ x^η.
- **I2 [FIXABLE] Range of validity of the parameter-table bounds.**
  - The claims "H ≤ 4X₀^{15}", "c ≤ X₀^{7.5} always" and "y ≤ X₀^{22.6}L⁹" hold only for ℓ ≤ ℓ_std. Beyond that point the
    table itself gives c = ¼e^{4ℓ²}.
  - Locations: 01-setup.tex:72, 77-78, 82; 03-zeros.tex:112, 118, 129; 05-queue.tex:918-919, 986 (v3 l.163-168).
  - Lemma 4.4 (ZA) survives. Qualify each claim with "for ℓ ≤ ℓ_std".
- **I3 [FIXABLE] θ := 1+1/L in the PIL, A-rankfull.tex:177, 202-203, 552 and 05-queue.tex:88, 663 (v3 l.1677, 2677,
  2682).**
  - (F1) at a pivot value q near X₀ gives 1 + κ₊/log q + 3/H(q) ≈ 1 + 0.8/Λ, which exceeds 1 + 1/L once L > 1.25Λ.
  - Fix: θ := 1 + 1/Λ. The uses still hold: θe^{(3H+2)/X₀}e^{2.2/Λ} ≤ 1.01; 24θL^{−0.9} ≤ 1; Prop 6.10.
- **I4 [FIXABLE] Value/slot fuzz factor, A-rankfull.tex:210-213 (v3 l.2684).**
  - The paper writes "each of value ≥ X₀, factor ≤ e^{(H+3)/X₀}". With H = H(q) and q up to 2z, this factor is ≥ e once
    8(log L)² > Λ. It is the same defect as correction #2.
  - Fix: the values are ≥ q/2, so the factor is ≤ e^{4H(X₀)/X₀}, using that H(v)/v is decreasing (Thm 6.22(c)).
- **I5 [FIXABLE, must fix] Euler chains and label sums in the PIL and (S3).**
  - Locations: A-rankfull.tex:196-203, 242-251, 269-279 (v3 l.2696-2704).
  - (S3) defines Eu_s(s) over primes of slot ≤ s (l.243), but l.272 says the carried factor 1/Eu_s(s_p) involves only
    slots < s_p.
  - At the first block of a chain, Eu_s(top) is not 𝓕_{s_{p_{t+1}}−}-measurable. The end comparison via Lemma 5.1(iv)
    needs Good up to top+H, but only G_{<s_top} is carried.
  - The PIL label sum (l.200) treats the pending Ψ as independent of the slot label s, but Ψ depends on s through the
    carried 1/Eu_s(s) and the block ranges. Bounding this pivot by pivot costs about e^{2k²H(X₀)/X₀}. That is not small
    once k ≳ (X₀/H(X₀))^{1/2}, which r₀ ≈ L/(3ℓ) reaches at astronomically large z. I re-derived this.
  - Repair, outlined by the checker, which I find sound: bound the block below each pivot surely by (S3) inside the
    conditional expectation at s_p, so that Eu_s(s_p) cancels before the label sum. Define Eu_s over slots < s. At each
    chain top, use the sure (F3′)-type bound valid on G_{<s_top}. The checker obtains ≤ e^γ log(2z+H)(1+10⁻⁸) per row, so
    A_R is unchanged.
  - The paragraph must be written into the paper.
- **I6 [FIXABLE] cor:R-Ecl, A-rankfull.tex:563 (v3 l.2787).** The coefficient −0.327 should be −0.3266, since
  1 − 3.98/3 = −0.32667. As written the step is false for L ≳ 3.4·10⁹; the final ≤ −4ℓ holds.
- **I7 [FIXABLE] Prop 5.35 (G1′) range (B) Step 3, 04f-bridge.tex:200-201 (v3 l.1434-35).** The step omits #𝒜, the
  same omission that correction #4 fixed in Prop 5.18. Add #𝒜 ≤ 2δN·L⁻⁴ + 2N^{θ/2}L⁻⁴ (Lemma P); the term stays
  o(1/log x).
- **I8 [FIXABLE] 04g-margin.tex:12 (v3 l.1471).** The text says "j_X₀ ≤ e^{−0.0009Λ} beyond" the small range. This is
  false in the huge range, where only e^{−59} is proved (Prop 5.31(iii)). State the two ranges separately; Prop 5.38(a)
  only needs j_X₀ small.
- **I9 [FIXABLE] Thm 6.22(a), 05-queue.tex:800-801 (v3 l.2118-19).**
  - (a) is stated for any S′ ⊂ S(J) of rank < r₀ with Cap ≥ c.
  - Step 0 applies Lemma 6.13, which needs |S′| ≥ r₀ + φ(r₀). Step 2 needs 6.13(iii), which needs a minimal heavy V.
  - Prop 6.10 only uses S′ = S(J) ∩ V. Restate (a) for that case.
- **I10 [FIXABLE] Thm 6.22 Step 6, 05-queue.tex:897-899 (v3 l.2185).**
  - The slope chain "≤ 1.06γ*Λ/L ≤ … ≤ 1.8A²/(Λℓ²)" and the test e^{s/2}√Λ ≥ 1.5ℓ²/A assume Λ_s = Λ. They fail for
    Λ > Λ_s: on a (Λ,s) grid, 165,140 points fail; for example at Λ = 10¹⁰, s = −18.82 the true slope 8.4·10⁻⁹ exceeds
    every intermediate bound.
  - The conclusion holds: the numerical maximum is 2.7·10⁻⁸ ≤ 4.1·10⁻⁸.
  - Analytic replacement: γ*Λ/L ≤ γ*²/((4ℓ² − log4)e^s) ≲ 1.7(A+1)²/(ℓ²Λ_s), giving a slope ≤ 10⁻⁷. Since 10⁻⁷ is
    smaller than 4·10⁻⁶, (c) still gives ρ_H ≤ 1 + 1.2·10⁻⁵ and (R_H).
- **I11 [FIXABLE] Lemma 5.20, 04k-kernels.tex:369-371, against Def. 5.11 (04k:60) (v3 l.1002 vs 915).**
  - Lemma 5.20's τ-near requires v/w ≥ X₀⁻; Def. 5.11 does not.
  - A step that is both τ-near and X₀-near and lands just below X₀⁻ creates a τ-source (split at 04k:293, 04x:61) that
    η̃ does not count.
  - Fix: assign the whole filter difference on X₀-near steps, which are terminal, to S^{X₀}.
- **I12 [FIXABLE] Lemma 6.1 and the E4 row, 05-queue.tex:163, 364 (v3 l.1724).** The window family behind "≤ 72P·H(P)
  grid windows" for Land(J) is never specified, but Cor 6.3 is claimed for every real J. Specify the family and add the
  sandwich: K_loc grows by about 10 (from 13), which is irrelevant, since K_loc ≥ 2B already.

## 6. Self-containedness

**Search for pointers.**
- The rendered text has no "see the notes", "as in [internal]", referee, Lean or working-note pointers.
- Every `\ref` resolves.
- Literature citations were checked at source where they could be: BDR (definitions, Thms 1.1 and 1.3, §5 quotations,
  footnote 4), Broucke 2025 (Thm 1.6, (1.2), Thm 6.1), Broucke 2024 (Thm 2.1), Johnston–Yang, Rosser–Schoenfeld ranges,
  and the Freedman (4.1) plus Bennett derivation (inlined at 05-queue.tex:175).
- Not re-checked at source, but used consistently with their standard statements: Heath-Brown 1988, Montgomery–Vaughan,
  Titchmarsh 4.11.

**The newly inlined proofs.**

- **B1 [BLOCKING] Lemma 5.7 (lem:bs-remainder), 04c-saias.tex:262-307.**
  - This is the ℓ ≥ 10¹⁸ region of Theorem 5.6 (Beurling–Saias). It is main-line, and v3 l.846-853 only stated it.
  - The inlined proof is a sketch and contains three false intermediate claims:
    - l.292: "for u ≥ u₀−2: r₀ ≥ 15" is false at ℓ = 10¹⁸ (u₀ = 31623). The certified r_low(u₀−3) = 12.82, the paper's own
      (R4) gives r(31619) ≤ 14.06, and r_low first reaches 15 near u ≈ 2.35·10⁵. (r(u) ≈ log(u log u) ≈ 12.7 there.)
    - l.268: "s_a := −E_πD_a ≥ 0" is false for u ≤ u₀, where s_a ≈ −0.06/√ℓ.
    - l.293: with the stated moments M₂ ≤ 9.5 and M₄ ≤ 59.8, "½E D_a² ≤ 10a′s_a + 60/ℓ" fails for a′ < 16/√ℓ.
  - Several steps are asserted rather than proved:
    - item (c): "the proof combines the chord bound…";
    - "for u < 27 the remainders are absolute, at most 9·10¹⁷/ℓ";
    - "every remainder is a small multiple of c(u)";
    - the assembly into ε(ℓ).
  - What the checker verified: the corrected ingredients hold with large slack. With r₀ ≥ 12.8, s_a ≥ 0.33a′ − 0.21/√ℓ.
    c(u) ≥ 2.2√ℓ log u₀ is much larger than ℓ|s_a| ≤ 1.01√ℓ. With the true moments (≈ 1), or with 60 replaced by 10⁴, the
    D_a² bound holds. ε(10¹⁸) = 0.0230 and ε(10²²) = 0.00104 are correct.
  - What was not verified: the full remainder assembly.
  - Nothing found suggests the lemma is false. A component referee refereed this region in the working notes; the
    end-to-end referee did not re-derive it (Appendix C lists it). But the paper does not currently prove it.
  - Fix: write out the working-notes proof with r₀ ≥ 12.8 and the sharp moments, drop "≥ 0", and show each remainder
    relative to c(u).
- **S1 [FIXABLE] Theorem 5.6 (BS) Z1, 04c:235.** "ℓ(E₁+E₂+E₃+T) ≤ 33" is not derived. The checker gets ℓE₁ ≤ 17.6,
  ℓE₂ ≈ 6.4, ℓE₃ ≈ 1.7 and T negligible, about 25.8 in total. Add these lines.
- **S2 [FIXABLE] Theorem 5.6 Step 4, 04c:145-150.** Lemma 5.3 (V) requires u ≥ 1, but the step covers 0 ≤ u < 1. Fix:
  for u < 1 use the small-heights bound ≤ C₀ (Y ≥ 72, since ℓ ≥ 30τ) and G ≥ Φ(ℓ).
- **S3 [FIXABLE] Lemma 5.3 (V), base case, 04a:245-247 (area of #10).**
  - "log2 + 1/(4Y) + 3(η₂ + sup ε₁) ≤ C₀" is false at Y = 72: 0.7026 > 0.70. The step Σ_{Y<n≤2Y}1/n ≤ log2 + 1/(4Y) also
    fails, by 1.2·10⁻⁵, as Y → 73−.
  - Fix: split the cases. For Y < X₀⁻/2 the ℕ value applies (max 0.69658); for Y ≥ X₀⁻/2 the bound is ≤ 0.6992.
  - [COSMETIC] 04a:311: "r_low ≥ 16.5" for u > 10⁶ is uncertified, and 1−1/16.5 < 0.94. E* = ½ suffices.
- **S4 [FIXABLE] Theorem 5.24 (LP/LP⁺).** The Landau–Perron argument is essentially complete, with these gaps:
  - Step 6 (04e:150-152) cites (LP-c), which gives only |R̂| ≤ |s|; it should cite eq:Rhatbound.
  - Step 7 (04e:161-188): the constant 442 rests on an unspecified "+O(1)", and log(1/η) is not log Λ + log L. The width
    holds directly only for L ≳ 8, and otherwise via the 0.0892 → 0.088 slack. The T_y constants (51, 500) are unchecked
    for Λ ≳ 6·10¹² with small log y/(Λ log log y).
  - [COSMETIC] Step 8 (04e:200-202): anchor "+1" missing; 1/16 ≤ |t| < 2 not covered by the explicit G bound.
  - [COSMETIC] 04e:71: "L₁ ≤ 3000Λ" needs a range. 04e:96: deriving (H_BS) also needs (T1).
  - Every use has large slack.
- **S5 [FIXABLE] Lemma 5.23, 04e:20.** "1.8 log p + 1" does not follow from Lemma 5.1(iv) alone, which gives about
  78 log p. Use (iv) at y = X₀⁻ together with Rosser–Schoenfeld (3.30).
- **S6 [FIXABLE] Lemma 5.20, 04k:409-414.** The bound sup_y log y·η(y) ≤ e^{−0.99Λ} is only sketched.
  - Lemma 5.3 needs u ≤ L_z; the case u > L_z (Rankin, Lemma 5.30) is missing.
  - "e^{o(1)}" is not o(1) when u is comparable to L_z.
  - The numerical check at l.414 is for the E-family, whose constant is e⁸ smaller.
  - The uses (E_S, Prop 5.38(a)) need only a crude bound.
- **S7 [FIXABLE] Lemma 5.12(ii), 04k:80-82.** "This forces x/n < X₀" is false: x/n can lie in
  [X₀, X₀ + 0.02H(X₀)]. The conclusion holds, using H(x/n) ≤ H(X₀)(1+10⁻¹⁵) on that range.
- **S8 [FIXABLE] Constants of 𝒩, 04k:134-136 and 04g:103 (v3 l.934-35).** A₀ and A₁ for 𝒩 are given "up to 1+O(η₁)",
  but the margin from 2.034 to 2.04 is only 0.3%, and 8.491 against 8.5 is similar. Fix: 𝒩 = ℕ below X₀⁻, so the values
  differ by less than X₀^{−0.8}.
- **S9 [FIXABLE] Lemma 5.32 (SI), 04x:395-396.** "A ≤ 4·10⁻⁷ because ℓ ≥ 0.45J ≥ 10¹¹" is wrong: at ℓ = 10¹¹ the bound
  gives 0.125. The true minimum ℓ ≈ 1.35·10³⁴ gives 6.4·10⁻⁷. The (1+3·10⁻⁶) budget holds (about 1+2.4·10⁻⁶), so 61.1
  stands; recomputed 60.79.
- **S10 [FIXABLE] Prop 5.31(i), 04x:229.** "A(1.8 − 4·10⁻⁶) ≤ 7.4915" is false: arb gives 7.491531. Write 7.4916. The
  bound 2.152 and the constant 0.4209 stand.
- **S11 [FIXABLE] Prop 5.18 (true kernels), statement.** 04x:96-97 and 04f:30 need W^op ≤ 2C_N log(2v)/log y at
  non-terminal levels. This is proved only inside the proof (M ≤ 2C_N); the statement's 5.1C_N would give 10.4, not 4.1.
  Add it to the statement.
- **S12 [FIXABLE] Lemma 5.30 (Rankin), 04x:145-162.** The hypothesis (H_BS)/Good(<z) is missing, but the proof uses
  Lemma 5.1(iii),(iv).
- **S13 [FIXABLE] Remark 1.2, 00-intro.tex:50-59.** "Zero-free half-plane ⟺ power-saving ψ" is asserted as "standard
  Perron/Mellin" with no proof or citation, and Cor 2.2's "Equivalently" rests on it. Inline the easy direction:
  −ζ′/ζ − s/(s−1) is analytic on σ > 1−ε′. Cite Diamond–Zhang for the converse.
- **S14 [FIXABLE] Remark after Thm A.10 (SVL), A-rankfull.tex:474-483.** It says svl-stress checked eq:svl-identity.
  `svl_stress.py` runs checks C1–C7, none of which is that identity, and its coverage checks use only C = B′. Align the
  remark with App. B.5. The SVL itself is proved in full in App. A; the remark is not a proof step.
- **[COSMETIC] Smaller self-containedness points.**
  - Remark rem:cm-chain is used but unproved; it follows from 5.1(iv) in one line.
  - lem:reduction(iii) has no proof (one line: log r₀ + log7 + 8.1ℓ ≤ 10ℓ+10).
  - Some side claims in App. A that the main line does not use are unproved: FAC's "widens caps by relative O(ε)";
    rem:widened's sharpness; "Σ_{p≥X₀}p⁻² ≤ 1/X₀" for real primes.
  - Thm 6.22: Step 2's "½ + 2/A ≤ 0.53" is false (0.5312) and "7.17t" should be 7.16668t; Step 0's "a ≤ A−0.28" fails
    for D < 1.96. The Step 3 ratio is overstated by up to 0.135 (true minimum 1.189 ≥ 1.12). The Step 5 constant is 11.13
    or 10.44, not 10.5 (the margin Λ−2597 holds). All have large slack.

**Complete and correct as inlined** (one-line notes only):
- Lemma 5.1 (CM);
- Lemma 5.5 (M), including the non-squarefree case and 4v-density;
- Thm 5.6 Steps 1–3 and 5–6, with Z2 matching the code;
- positivity of c(u);
- Lemma 5.8, Cor 5.9;
- the margin identity and push-through;
- Lemma 5.22;
- Thms 5.14 and 5.15 (KR) with (K1)–(K5): TV(C₄) = ¼ checked;
- Cor 5.17 (C_N = 157.08);
- Prop 5.18 (proof);
- Lemma 5.21 (C_S′ = 10);
- Lemma 5.27 (XB), given S11 and I11;
- Lemma 5.29;
- Prop 5.31(ii) (given the #5 follow-up) and (iii);
- Lemma 5.32 (apart from S9);
- Props 5.26, 5.35 (given I7), 5.38 (6.44, 0.549, 0.73), Thm 5.37 (given I8), Cor 5.40 (c′ = 0.15);
- §6 Freedman form, Thms 6.6, 6.16, 6.17 (N ≤ e(r(D+1))^{2j+1} checked), Lemma 6.9 (Σ(Λ+m log2)⁻² = 1.4427/Λ);
- App. A: Volume Lemma, Lemma SC (checked line by line), SVL (i)–(v) (given I5), Theorem R (given I3–I5).

## 7. Presentation

**Internal jargon in the rendered text.**
- The PDF text (pdftotext) and the comment-stripped sources were scanned for agent names, referee section numbers,
  "A10", "E2E", [P]/[S]/[N] tags, Lean and note filenames, and hard-coded theorem numbers.
- None occur in the body. The only hard-coded numbers are inside quotations from BDR and Johnston–Yang (00-intro.tex:75,
  06-base-range.tex:89) and in the dead placeholders (§1).
- Remaining jargon:
  - App. B's script names (`*_refereeA/B.py`) and "the numbering of the working draft, e.g. T4.3" (B-certificates.tex:180);
  - App. C's `CORRECTIONS-vs-v3.md` (C-ai-statement.tex:16), which is acceptable if "v3" is explained;
  - undefined internal names in §6: "Lemma P" (05-queue.tex:15, 125), "route H" (838), "canonical regime" (370, 936,
    1020), "B-lin target" (192), and "S1 and S2" in the title of Prop 6.27.

  All COSMETIC.

**Findings.**
- **P1 [FIXABLE] `\cref` in 05-queue.tex, all 214 uses.** Every `\cref` renders as lowercase "theorem N.M", whatever the
  environment, because the environments share one counter and cleveref is not configured. The PDF shows "theorem 5.1(iv)"
  for Lemma 5.1, "theorem 7.1(1)" for Lemma 7.1, "Lemma P (theorem 6.25)", "section A" and "eq. (71)". I verified these
  in the PDF: "theorem 6.22" occurs 20 times and "theorem 6.25" 13 times. No other file uses `\cref`. Fix: add
  `\crefname` for each environment with `\crefformat`, or use `Lemma~\ref` like the rest of the paper.
- **P2 [FIXABLE] Novelty claim, 00-intro.tex:98.** "(a) θ < ½, which no random discretisation reaches" overclaims. The
  construction is itself randomised, and BDR §5 (checked at source) says only that "a direct application of Theorem 1.2"
  gives integer error ≥ O(x^{1/2}). Suggested wording: "which the existing random approximation procedures
  [DMV, Zhang, BV, BDR] do not reach, since they lose a square root".
- **P3 [FIXABLE] Where the factor 3 log log comes from, 00-intro.tex:107-111 and 03-zeros.tex:252-256 (v3 l.505-507).**
  The text attributes the loss to "positivity (G1) together with (A)". This misleads: (G1) alone allows κ′_k = κ₀
  (|R_k′| ≤ 0.8/log x), which would give 1·log log. The extra 1/log²x_k is needed by Prop 5.35 Step 4 (04f-bridge.tex:
  230-235), so that the oscillation response is o(1/log x). Attribute the loss to the margin requirement.
- **P4 [FIXABLE] Appendix C, C-ai-statement.tex:14-31.**
  - It says writing the paper "surfaced ten slips … none of which changes any conclusion". This check finds 16 more
    (D1–D2, I1–I12, the #5 and #2 follow-ups), all inherited from or adjacent to the refereed draft. None changes a
    conclusion either.
  - The list "Components reviewed only once" omits material that no referee has seen: the ten corrections, which were
    approved by the lead, and the paper's newly written inlined proofs, which were checked only by this AI consistency
    check. These include Theorem 5.15 (random widths), the τ-term of Lemma 5.27, the base case of Lemma 5.3, the
    reorganised PIL/(S3), and Lemma 5.7.
  - Fix: update the count and add these to the list.
- **[COSMETIC] Intro and statement of Theorem A, as a specialist reader.**
  - The abstract, informal Theorem A, Theorem 2.1 and Cor 2.2 agree with each other and with v3 §0.1 (θ range;
    X₀ ≥ max(e^{10⁸}, X_Hux); 𝒢 with P ≥ 1 − 1.5/log X₀; (i) and (ii)). "β ≤ θ" and "Re ρ_k → 1" are right.
  - Theorem 2.1(i) actually gives N = x + O(x^θ log* x). The abstract could say so.
  - 00-intro.tex:62-63: the de la Vallée Poussin-type ψ error is uncited and reads as Hilberdink's.
  - 00-intro.tex:70-71: the Diamond–Zhang Ch. 17 example is known only via BDR p.3.
  - 00-intro.tex:135-136: "arrivals have compensator ∫_W(margin)" should read "the excess has compensator −∫_W margin".
  - 00-intro.tex:123 calls the target "explicit", but it is adapted and random.
  - 01-setup.tex:24-25: "every quantitative estimate holds for all log X₀ ≥ 10⁸" is too broad, since the Huxley-based
    estimates need X₀ ≥ X_Hux.
  - 01-setup.tex:93-95: the O(log²x) queue is an experimental observation; B = e^{O(ℓ²)} is what is proved.
  - 06-base-range.tex:87-91: "a fully explicit X₀ would follow" from Johnston–Yang is overstated (v3 §8 R1). Say "would
    remove X_Hux".
  - Notation clashes: θ′ (two meanings), η, ε, c, D.
  - "composite integers" (abstract) against "composite elements" (intro).
- **[COSMETIC] Smaller notes on §4, §6, §7 and App. A.**
  - 03-zeros.tex:52-53: "up to O(1) boundary terms" should be stated as ≤ 3X₀^{1−σ}/|t|.
  - 03-zeros.tex:66-71, 97: "log C₁ < 3" needs C₀ ≤ 0.518 but C₀ is only "absolute"; the claim is unused, so delete it.
  - 06-base-range.tex:156: "κΨ(…)" should be Ψ(…).
  - 06-base-range.tex:217-219: the "budget ≈ 2.4·10⁻⁴" is unsourced.
  - The dependency table (01-setup.tex:105-131) is abridged and stale for corrections #2, #4 and #5.
  - 05-queue.tex:961: "E_cl^{(u)} ⊂ Good(<u)" has the inclusion reversed.
  - 05-queue.tex:317: 48 − √768 = 20.287, not 20.3.
  - 05-queue.tex:726: Lemma 6.21(e)'s 1.36 needs η ≥ 0.242; only η = ¼ is used.
  - App. A grid-window count: the windows overlap, so there are z/δ₁ of them, not z/δ (A-rankfull.tex:544, 560;
    05-queue.tex:457). This is absorbed.
  - App. A 344: "43 947 configurations" does not match App. B's 32,133.
- **[COSMETIC] Process documents.** `LABELS.md` and `CORRECTIONS-vs-v3.md` use v3 numbering, not the compiled one (see
  §0). `LABELS.md` lists `eq:stageidentity` both as an alias and as withdrawn.

## 8. Coverage

Every theorem, lemma, proposition, corollary, definition and displayed constant was compared with v3 by one sub-checker.
Parts are compiled sections; items are named by their v3 labels. Verdict codes: **match** = same as v3; **(a)#n** = logged correction n; **(b)** = proof inlined from v3's working notes;
**(c)** = rewording. The full tables are in the sub-reports.

| part | items | verdict |
|---|---|---|
| §1–§2 | Theorem A, Cor 2.2, proof map, parameters, dependency table, (N0)–(N5) | match / (c); table stale (§2); I2 |
| §3 | §1.1–§1.4, (1.1)–(1.3), Remark 1.0, (G1), (T1), (C2), Lemmas 1.1–1.5, Cor 1.4 | match / (b); I1 |
| §4 | (2.1), Lemmas 2.0, 2.0′, 2.0″, R̂_k, (2.2), Lemmas 2.1–2.3, Thm 2.4 (constants recomputed) | match / (c) |
| §5 (1) | notation, Lemmas 3.1, 3.2 (V), (3.1)–(3.3), Lemma 3.3 (M), Thm 3.4 (BS), Z1, Z2, ℓ ≥ 10¹⁸, Lemma 3.4A, Cor 3.5, (F₁), (F₂), Lemma 3.11, (3.4), Lemma 3.12, Thm 3.13 | match / (a)#6, #10 / (b); D1, D3, D4; B1, S1–S5 |
| §5 (2) | kernels, Def near, Lemma near, (K1)–(K5), Thms 3.6/3.6′, Cor 3.7, Prop 3.8, Lemmas 3.9, 3.10, Prop 3.14, Lemma 3.14A, its three ranges, Lemma 3.14B, (Osc), Lemma 3.15, F_θ, Prop 3.16, Thm 3.17, Prop 3.18, Cor 3.19 | match / (a)#3, #4, #5, #9 / (b); D2; I7, I8, I11; S6–S12 |
| §6 | parameters, (F1)–(F4), Lemma 4.1, Cor 4.2, Thm 4.3, Def 4.4, Lemma 4.5, Prop 4.6, Cor 4.7, Lemmas 4.8–4.10, Thms 4.11, 4.12, Prop 4.13, Lemmas 4.14, 4.15, Thm 4.17, Lemmas 4.18–4.21, Prop 4.20, §4.8 | match / (a)#2, #7, #8; I9, I10, I12 |
| §7 | Lemma 5.1, (5.2)–(5.6), Lemma 5.2(a)–(c), X_LP (integrals 14.915, 214.77, 6.696; 688.9/Λ ≤ 690/Λ) | match |
| App. A | Def A.1, Lemmas A.1–A.4, A.7, Thms A.5, A.6, cor:R-Ecl, rem:widened | match / (a)#1 / (b); I3–I6; S14 |
| App. B–C | certificates (§2); AI statement against v3's final verdict | match; P4 |

No item was left unchecked.

## 9. Verdict

**Faithful: yes.**
- The paper reproduces v3's statements, constants and proof architecture of Theorem A.
- All ten logged corrections are mathematically correct and applied wherever the quantity appears, and their
  "no downstream effect" claims hold. Two follow-ups are needed: #5's weaker bound in the middle range, and #2's
  unrecorded dependency edge.
- There are four unlogged deviations (D1–D4). All are correct, none changes a downstream statement, and D1 and D2 need
  small consistency edits.
- The build is clean: 94 pages, no undefined or duplicate labels or citations.
- Every certificate reproduces its quoted output exactly.

**Self-contained: not yet.**
- **One main-line step is BLOCKING (B1).** The ℓ ≥ 10¹⁸ remainder lemma (Lemma 5.7) of the Beurling–Saias theorem is a
  sketch with three false intermediate claims and an unshown assembly. This is a write-up gap, not evidence against the
  bound: the corrected ingredients were verified with large slack, and the region was refereed in the working notes. But
  the paper does not prove it.
- **36 items are FIXABLE.** Most substantive are:
  - the PIL/(S3) Euler-chain bookkeeping (I5), which as written fails at astronomically large scales and needs a
    reorganised paragraph;
  - the Lemma M cutoff consistency (D1);
  - twelve errors inherited from v3 (I1–I12);
  - incomplete details in the inlined proofs of Theorems 5.6 and 5.24 and Lemmas 5.3 and 5.20 (S1–S6);
  - the `\cref` rendering in §6 (P1);
  - the overclaiming novelty phrase (P2);
  - the AI statement's account of what has been reviewed (P4).

**Conclusion.** None of the findings casts doubt on Theorem A. For each, a local repair was found and checked, apart
from the full assembly of B1. The paper faithfully presents the refereed proof of Theorem A. Once B1 is written out in
full and the FIXABLE items are applied and logged (new entries for D1–D4 and I1–I12), it will present that proof
self-containedly. The uncommitted working-tree edits made during this check, including draft entries #11–#19, have not
been checked and need a re-check.
