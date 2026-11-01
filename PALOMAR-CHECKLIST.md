# Palomar submission checklist

Branch `palomar` (from `development` 6606d54). Checked locally on 2026-11-01 (macOS, Apple silicon, Lean/Mathlib
v4.35.0). Nothing has been pushed or submitted.

| rule | status | evidence |
|---|---|---|
| Lean project at the repository root, exactly one lakefile | done | `lakefile.toml` at the root (no `lakefile.lean`); `lean/` removed by `git mv` |
| committed `lake-manifest.json` | done | root `lake-manifest.json`, Mathlib rev `56a005855ea1…` = tag `v4.35.0` |
| `lean-toolchain` = `leanprover/lean4:v4.35.0`, matching Mathlib exactly | done | root `lean-toolchain` and `.lake/packages/mathlib/lean-toolchain` are both `leanprover/lean4:v4.35.0`; `git describe` of the Mathlib checkout gives `v4.35.0` |
| path references updated from `lean/…` | done | `git grep -E '(^|[^a-zA-Z0-9_.-])lean/'` and `git grep 'cd lean'` find nothing; README, LEAN-FORMALIZATION.md, FOLLOWUP-S2.md, FOLLOWUP-THETA.md, KERNEL-CERT-NOTES.md, `scripts/seqbuild.py` fixed. The paper text and CORRECTIONS had no `lean/` paths |
| every `.lean` file uses the module system | done | all 1103 tracked `.lean` files start with `module` |
| every `.lean` file ≤ 10,000 lines | done | longest is `RequestProject/Beurling/RankFull/MultiRun.lean`, 1815 lines |
| generator scripts | done | the 11 non-module scripts (`genz2`, `genrk`, `gencm3`, `genharm`, `genrtab`, `genrtab2`, `eps_part`, `gen1d`, `genzeta`, `genmargin`, `geneps`) renamed to `scripts/*.lean.gen`, documented in `scripts/README.md`. Adding `module` did not work: the interpreter reports `IR of declaration 'BSCert.FX.ZI' not available` with `import`, `public import` or `import all`, and `meta import` needs every transitive module imported by hand. After the rename, `lake env lean --run scripts/genharm.lean.gen` and `genmargin` (output dir redirected) run and give the expected output. No `.lean` file under `certificates/` |
| exactly one root licence file `LICENSE` (MIT) | done | `git mv LICENSE-code.txt LICENSE`; `LICENSE-paper.txt` (CC BY 4.0) kept; README *Licences* says the code is MIT and the paper text is CC BY 4.0 |
| `Challenge.lean`: ≤ 1000 lines, ≤ 100 KiB, imports only Mathlib, `module` | done | 174 lines, 9222 bytes, only `public import Mathlib` |
| Challenge advertises the headline statement | done | `BModel.one_zero_system_exists : BaseRange.Huxley84 → ∃ P : BeurlingSystem, (∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (1 : ℝ), \|P.N x - x\| ≤ C * x ^ ε) ∧ ¬ P.HasZeroFreeHalfPlane` (statement copied from `RequestProject/Beurling/OneZero/TheoremAprime.lean:590`), plus `BModel.corollary_2_2_complete : BaseRange.Huxley84 → ¬ QuestionQ`, each `:= by sorry` |
| definitions copied verbatim, with docstrings and module docstring | done | `BeurlingSystem` (structure), `val`, `N`, `zeta`, `puncturedHalfPlane`, `IsZetaContinuation`, `HasZeroFreeHalfPlane`, `QuestionQ` from `Defs.lean` (under `open Complex`), and `BaseRange.primeCount`, `liI`, `Admissible`, `relErr`, `HuxleyFrom`, `Huxley84` from `BaseRange/Huxley.lean` (under `open Real MeasureTheory Set Filter`), inside `@[expose] public section` as in the sources. The module docstring explains the result, what a `[1, 0]`-system is, and that (84) is assumed: a known theorem (Heath-Brown 1988 + de la Vallée Poussin) that is not in Mathlib |
| `Solution.lean` | done | `module`, `public import RequestProject.Beurling.OneZero.TheoremAprime`. The development already declares the theorems and definitions under the Challenge names, so Solution only imports them (comparator compares the constants of the two exported environments by name) |
| Challenge and Solution as separate `lean_lib`s; default targets | done | `lakefile.toml`: `lean_lib Challenge` roots `["Challenge"]`, `lean_lib Solution` roots `["Solution"]`, `defaultTargets = ["RequestProject", "Challenge", "Solution"]` |
| `comparator.json` | done | `challenge_module`, `solution_module`, `theorem_names` (both theorems), `definition_names` (the 14 definitions, structure included), `permitted_axioms` `["propext", "Quot.sound", "Classical.choice"]`. No `enable_nanoda` (the template has `"enable_nanoda": true`; add it if Palomar wants it) |
| `lake comparator` passes | **not run** | Plain `lake comparator` exits with code 2: "`lake comparator` sandboxes the code it checks with `bwrap`, which needs Linux namespaces." On macOS the only local option is `--inadvisably-no-sandbox`; this session's permission policy refused that flag. Docker Desktop is installed but its daemon would not start. To do: run `lake comparator --inadvisably-no-sandbox` on this machine, or `lake comparator` on Linux with `bwrap` |
| full `lake build` green | done | `lake build`: "Build completed successfully (10152 jobs)", exit 0. The only `sorry` warnings are the two deliberate ones in `Challenge.lean` (lines 162, 171) |
| `#print axioms` of both theorems | done | `import Solution`: `BModel.one_zero_system_exists` and `BModel.corollary_2_2_complete` depend on `[propext, Classical.choice, Quot.sound]` |
| `formalization.yaml` v0.4 | done | same shape as the template. Validated with `jsonschema` against `v0.4.schema.json` from `mathlib-initiative/formalization.yaml` (main): 0 errors. license `MIT`; authors and maintainers `Samuel Lavery`; arXiv `math.NT`, MSC `11N80` (generalized primes and integers), `11M41` (other Dirichlet series and zeta functions); automation entries for manual work, Claude agents (Claude Opus 5.5) and Aristotle (Harmonic); review status says AI-only checks and no human expert review; sources are the paper (`formalizes`), Broucke–Debruyne–Révész (Trans. AMS 2025) and Heath-Brown 1988 (`background`); `sorry_count: 0`, `axioms: []` |
| no build artifacts outside `.lake` | done | no tracked `.olean`/`.ilean`/build dirs; `.gitignore` has `.lake/` (was `lean/.lake/`). The only tracked binary is the paper `beurling-paper.pdf` |
| no submodules, no LFS | done | no `.gitmodules`, no mode-160000 entries, no `.gitattributes` |
| checkout ≤ 500 MiB | done | the tracked files total about 19 MiB (1384 files) |

## Notes for the maintainer

- Nobody has reviewed the wording of the `automation` and `review` sections of `formalization.yaml` or the README
  additions; check them. The `manual` entry describes the author's role from the repository's process documents
  (PAPER-SPEC.md, review briefs). Correct it if it is wrong.
- The source `location` for the paper is the GitHub `origin` (`https://github.com/samlavery/Beurling`). After pushing,
  consider pinning a commit or a release in `sources[0].id`.
- Docstrings in `RequestProject/` still call the generators `genz2.lean` and so on. I left them as they are so the build
  would not change; `scripts/README.md` explains the renaming.
