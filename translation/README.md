# Translation-review package

Status: **review-ready**.

This package exposes the frozen conditional v002 Alessandrini-orthogonality
uniqueness target and its ten outside-literature dependencies. It does **not**
claim to formalize or verify the manuscript's Dirichlet-to-Neumann theorem
`main-thm`. The active approval mode is `testing_waiver`; exact-byte human
ratification of the statement and every literature entry remains pending.

The two public dossiers use identical authoritative source quotations,
derived-result statements, and Isabelle listings. Their English
back-translations are different and are grounded in two distinct sets of
mutually isolated fixed-hash reviews already protected by statement lock v2
and literature lock v10:

- `TRANSLATION_A.tex` / `TRANSLATION_A.pdf`: independent-translator and
  independent-source-translation records;
- `TRANSLATION_B.tex` / `TRANSLATION_B.pdf`: separately isolated
  Isabelle-semantics and adversarial reconstruction records.

The primary agent performed editorial normalization into the common LaTeX
layout; this package does not portray that editorial step as a new independent
review. A fresh terminal package/dependency audit is still required before the
manifest may become `audited`.

## Identity

| Field | Value |
|---|---|
| Package schema/format | `2` / `latex_parallel_v1` |
| Package version | `2` |
| Manuscript | `papers/inverse-schrodinger-lp-uniqueness/manuscript/schrodinger-Lp-v05.tex` |
| Manuscript SHA-256 | `bea3c22283a7bfc8b2adb929bfc48e576c7bfb0a3f0ff6a823ce2bb191048430` |
| Statement lock | version `2`, SHA-256 `2436c0c1285e9aff404364c43a767870c5429e62c8320977c1be11a73fceacae` |
| Literature lock | version `10`, SHA-256 `9565e5ca02275fcca29c89fcbd92587783223638a393eee72609cdd4964012ef` |
| Human-ratification state | `pending` |

## Checked public-file hashes

<!-- CF-PUBLIC-HASHES-BEGIN -->
- `TRANSLATION_A.tex`: `481354fb320822d2bd8761fc0eb20e32d447ea64cbaee13795662d9745182a7d`
- `TRANSLATION_A.pdf`: `211eda7b477c14e9c06530d0340a7a3ecedfbdb06f8efa49bcfed89457ea153f`
- `TRANSLATION_B.tex`: `6043146f5bf81b3ab91e661b8e5a2cce5d5638583d34d252c43a82ef850e2ec1`
- `TRANSLATION_B.pdf`: `455ec63d8a2efea74aeb9199642edb1369d4417f2d2cb9aab9c5b805dcf5ba88`
<!-- CF-PUBLIC-HASHES-END -->

Mechanical structure and hash checks establish package currency, not semantic
faithfulness. The review question remains whether every formal meaning, source
statement, and derived step is mathematically accurate and complete.
