# Generator scripts

These scripts generated the kernel-checked certificate files under `RequestProject/BSCert/`. They
are not part of the proof and are not built by `lake build`.

The Lean generators are Lean 4 programs (each defines `main`) stored with the extension
`.lean.gen` rather than `.lean`, because they are written for the pre-module system (plain
`import`, no `module` header) and every `.lean` file in a Palomar submission has to be a module.
Their comments, and the docstrings of the generated files, refer to them by their old names
(`genz2.lean` is `scripts/genz2.lean.gen`, and so on). Lean does not depend on the extension. Run
one from the repository root, after `lake build`, with

```
lake env lean --run scripts/genharm.lean.gen
```

| script | imports | output |
|---|---|---|
| `genz2.lean.gen` | `BSCert.Z2K` | `RequestProject/BSCert/Z2KChunks/K*.lean` |
| `genrk.lean.gen` | `BSCert.RankinK` | `RequestProject/BSCert/RankinKC.lean`, `RankinKChunks*.lean` |
| `gen1d.lean.gen` | `BSCert.AuxK` | `RequestProject/BSCert/AuxKCovers.lean` |
| `genzeta.lean.gen` | `BSCert.Consts.ZetaK` | constants and lemmas for `BSCert/Consts/ZetaKChunks/` (in `/tmp/rhscratch/gen/`) |
| `genrtab.lean.gen`, `genrtab2.lean.gen` | `BSCert.FX.Dickman` | the table of `BSCert/FX/RTab.lean` (in `/tmp/rhscratch/gen/`) |
| `gencm3.lean.gen`, `genharm.lean.gen` | `BSCert.Finite.KArith` | partial sums (in `/tmp/rhscratch/gen/`, or printed) |
| `genmargin.lean.gen` | `BSCert.Consts.MarginCells` | margin values (in `/tmp/rhscratch/gen/`) |
| `geneps.lean.gen` | `Beurling.Noise.BSLargeEpsK` | `eps_part.lean` (in `/tmp/rhscratch/gen/`) |
| `eps_part.lean.gen` | – | a sample of the output of `geneps.lean.gen` (a fragment, not a program) |

Scripts that write to `/tmp/rhscratch/gen/` need that directory to exist. The scripts that write
under `RequestProject/` overwrite checked-in files.

The Python scripts: `x0gen.py`, `x0genchunks.py` and `x0/` generated the X₀-band chunks
`RequestProject/BSCert/Finite/X0Chunks/` (they read their list from `/tmp/rhscratch/x0/`);
`seqbuild.py` builds the import closure of a module one Lean process at a time (a development
aid that calls a local wrapper script, not included).
