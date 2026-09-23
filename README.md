# Uniqueness from Alessandrini orthogonality for L^p Schrödinger potentials, p>1: Isabelle/HOL proof package

This source package contains an Isabelle/HOL proof of **uniqueness from
Alessandrini orthogonality for L^p Schrödinger potentials, p>1** (the frozen
v002 statement). Its exact theorem and formalization scope appear in `RESULT.md`.

For two possibly complex-valued L^p potentials, p>1, on a bounded smooth planar
domain, the result says that universal integrable complex-bilinear
Alessandrini orthogonality against the corresponding weak-solution pairs
implies equality almost everywhere. This package does **not** establish the
manuscript's Dirichlet-to-Neumann theorem `main-thm`.

The proof uses **ten cited results**, represented by explicit, reviewed
literature interfaces. Isabelle checks the derivation from those stated
premises; the proofs of the cited results are not formalized in this package.
The project label **VERIFIED_RELATIVE_TO_LITERATURE** records this dependency
boundary separately from the theorem's mathematical hypotheses.

The audited documents in `translation/` expose the mathematical interpretation
and source statements. Exact-byte human semantic ratification of the statement
and literature interfaces remains pending under the recorded `testing_waiver`
mode.

## Requirements

- Python **3.10 or newer**, standard library only; no pip packages.
- **Isabelle2025-2**, including its bundled Cygwin on Windows.
- Matching AFP release **afp-2026-07-21**; supply its `thys` directory.

Obtain Python from [python.org](https://www.python.org/downloads/), Isabelle
from its [release archive](https://isabelle.in.tum.de/website-Isabelle2025-2/),
and AFP from the [AFP download page](https://www.isa-afp.org/download/).
Use these pinned releases. On Windows, install Python with the `py` launcher
or make `python` available on PATH, then reopen the terminal.

## Ubuntu / Linux

Extract the ZIP or clone the repository, open a terminal in the package, and run:

```bash
bash ./check.sh --skip-build
bash ./check.sh --isabelle-home "$HOME/Isabelle2025-2" \
  --afp-thys "$HOME/afp-2026-07-21/thys" \
  --isabelle-user "$HOME/isabelle-lp-proof-package-user"
```

Replace those paths with your installation locations. `./check.sh` also works
when its executable bit is preserved. If `isabelle` is on PATH and AFP is
registered, the installation arguments are optional. `ISABELLE`, `AFP_THYS`,
and `USER_HOME` environment variables are also supported.

## Windows

Open PowerShell in the package directory and run:

```powershell
.\check.cmd -SkipBuild
.\check.cmd -IsabelleHome 'C:\Isabelle2025-2' `
  -AfpThys 'C:\afp-2026-07-21\thys' `
  -IsabelleUser "$env:USERPROFILE\isabelle-lp-proof-package-user"
```

The CMD launcher invokes PowerShell with a process-local execution-policy
setting. It locates Python and uses the same `check.py` as Linux. The full
Windows build requires `-IsabelleHome` and uses Isabelle's bundled Cygwin;
a separate WSL, Git Bash, Java, or Poly/ML installation is unnecessary.
`check.ps1` also runs under PowerShell 7 on Linux. Python can run static checks
directly on either platform: `python -B check.py --skip-build`.
Quoted paths containing spaces are supported; keep the extraction path short
on Windows.

## Integrity, Git line endings, and the proof build

The initial `--skip-build` / `-SkipBuild` command checks integrity only. Omit
that option for the Isabelle build. Use a fresh user directory outside the
package for the first build and retain it for faster reruns. The build runs
with one job and one thread; a cold build includes substantial AFP and proof
dependencies and can take considerable time and memory.

The checker verifies every static file hash, rejects admissions/oracles and
scratch imports, checks the exact Isabelle release, and selects every bundled
local session with `-D`. The terminal session is
`Paper_Inverse_Schrodinger_Lp_Proof_Stage_018`.

**Preserve the included `.gitattributes`.** Its `* -text` rule disables Git
line-ending conversion for the complete package, including historical mixed
line endings covered by audit hashes. Add it together with the package on the
first commit. Include the hidden `.github/` directory as well. Do not run
`dos2unix`, normalize files, or regenerate checksums to bypass an integrity
failure. `check.cmd` deliberately retains CRLF; `check.sh` retains LF.

Top-level `.git` metadata is excluded from the inventory. All other files,
including hidden release settings and `LICENSE`, are checksum-covered. Keep
logs, editor backups, generated PDFs, and Isabelle heaps outside the package.

The GitHub Actions workflow runs integrity and launcher checks on Windows and
Ubuntu. It does not run an Isabelle proof build.

## Contents and provenance

- `isabelle/`: the complete local session/theory closure for the terminal build.
- `translation/`: the exact audited dual-LaTeX/PDF translation package v2.
- `provenance/`: statement lock v2, literature lock v10, trusted-base ledger,
  approval-mode snapshot, translation manifest, and independent audit.
- `MANIFEST.json`: release identity, required versions, source origins, and hashes.
- `SHA256SUMS`: every static package file except the checksum list itself.
- `RESULT.md`: exact checked theorem, trust boundary, and exclusions.
- `.gitattributes`, `.github/workflows/integrity.yml`, and the four `check.*`
  files: the current prior package's Git-safe, Windows/Linux delivery support.

The preserved translation README describes the package as review-ready. The
later manifest and independent PASS report in `provenance/` record that its
audit was completed; its historical bytes and terminology are retained unchanged.

Likewise, `provenance/TRUSTED_BASE.md` is an unchanged historical snapshot.
Some consumer descriptions and its prose count of nine are stale. The current
boundary is the ten entries in literature lock v10 and the translation dossiers;
all ten are consumed by the checked result. Seven premises appear explicitly
in the terminal theorem, and its locale contributes three additional distinct
premises.

The manuscript and cited books/articles are not redistributed or required as
checksum-gated build inputs. Both translation dossiers quote and attribute the
source theorem statements and contain their bibliography. Editorial manuscript
changes do not require a new proof release; meaning-bearing changes require
translation review and, when formal propositions or premises change, a new
checked release.

The delivery support is copied byte-for-byte from
[`catalin-carstea/arxiv-2606.15977-formalization` at commit 7135f8e](https://github.com/catalin-carstea/arxiv-2606.15977-formalization/tree/7135f8e2e03987f8f5b12bee3df3a63d27c7ec93).
`provenance/delivery-reference.json` records exact copied-file hashes.
