# Independent fixed-hash package v2 audit

Date: 2026-09-05
Reviewer: isolated read-only task `/root/wp1507_independent_audit`
Verdict: **PASS**

Package v2 has no unresolved semantic, trust, dependency, structural, or
rendering finding. The exact bytes support proceeding to
`VERIFIED_RELATIVE_TO_LITERATURE`, subject only to recording this audit,
passing `-RequireAudited`, replaying authoritative FullHistory, and completing
the audited-manifest and final-checkpoint gates.

## Independence and scope

The reviewer re-audited the complete current package rather than relying on
the v1-to-v2 delta.

- No repository file was edited, created, deleted, staged, or committed by the
  reviewer.
- No sub-agent was used by the reviewer.
- The reviewer did not read `PRIMARY_PREAUDIT.md`.
- `FORMALIZATION.md` and the compact diagnostic summary were inspected only
  for lifecycle/result-label consistency, not used as semantic evidence.
- Temporary PDF renderings were created outside the repository, visually
  inspected, and deleted.
- No expensive Isabelle or Docker build was rerun by the reviewer.

This Markdown file is the primary's faithful transcription of the independent
reviewer's returned report. UI-only file-citation markup was normalized to
ordinary repository paths; no audit finding, qualification, hash, or verdict
was changed.

## Exact hashes checked

| Artifact | SHA-256 |
|---|---|
| Manuscript | `BEA3C22283A7BFC8B2ADB929BFC48E576C7BFB0A3F0FF6A823CE2BB191048430` |
| Statement lock v2 | `2436C0C1285E9AFF404364C43A767870C5429E62C8320977C1BE11A73FCEACAE` |
| Literature lock v10 | `9565E5CA02275FCCA29C89FCBD92587783223638A393EEE72609CDD4964012EF` |
| Accepted terminal theorem | `ACD81A3357F2844F0559C234122A3080B79AA48346F046E7B587E267DC4CFDAB` |
| Proof `ROOT` | `D8735BE8B2ECF431BEEED0796A693C60D366E84E43ADDF3A10A36456118D4F82` |
| Package-v2 manifest | `850242A1322D4C30DF093F81D16DC829C0DA14D930DC0680715683D0C082272B` |
| Public README | `472DD2F7320D47AE04778CE1ABD39557CA5D431F6899FD9A44B1D4ACCB0092F7` |
| A TeX | `481354FB320822D2BD8761FC0EB20E32D447EA64CBAEE13795662D9745182A7D` |
| A PDF | `211EDA7B477C14E9C06530D0340A7A3ECEDFBDB06F8EFA49BCFED89457EA153F` |
| B TeX | `6043146F5BF81B3AB91E661B8E5A2CCE5D5638583D34D252C43A82EF850E2EC1` |
| B PDF | `455EC63D8A2EFEA74AEB9199642EDB1369D4417F2D2CB9AAB9C5B805DCF5BA88` |
| Rejected v1 audit | `42023A3FD599A8AF154CA42C2242FE7954FDDD7285497BAEA64F84DBB43D8F78` |
| v1 reconciliation | `5C5B7D17FEC33629537D2B3B15BA60E1450D1CD45835D7E2A748139CCB804D52` |

Supporting identities also matched:

- workflow mode:
  `1B18121AB7C7FEE7F2F315113C8C9CB6A06A51D0235B67527F23657E3830C20A`;
- v002 specification:
  `6920B24C8ADE83595F924742031788757612C93B06C17C0FEC75621AF6C40961`;
- v002 statement theory:
  `0FD471F008C4F2D79961D45BB654752A986C39C2111203C67748C6D22A03D792`;
- Setup theory:
  `EDCD4DD35BDB06CCEBCD5A952218B1B036EFE7CAF328C878EE90FF188EFF444D`;
- repository `ROOTS`:
  `099F647FE7BC187B6F9EE52B50FEC11D41DE50CBD62625BCA9DB7724F1C3CEA1`;
- release manifest:
  `1571CC2688AC04736E20FEDAF1E59CBAB97DF5216E66266DB6D8E1142F015988`.

All internal statement- and literature-lock member hashes matched.

## Principal claim

The package advertises exactly the frozen conditional v002 proposition
`slp_alessandrini_uniqueness_claim`, not manuscript theorem `main-thm`.
No drift was found in quantifier order; the bounded smooth planar-domain
convention; finite real exponent `p>1`; complex local-`L^p` hypotheses; the
universal cross-product of the two weak-solution spaces; explicit
integrability of the unconjugated bilinear pairing; the zero Alessandrini
integral; or the restricted-Lebesgue almost-everywhere conclusion.

The `p>=2` proof branch derives local `L^(3/2)` membership on the bounded
measurable domain and applies the same checked subquadratic theorem. It
introduces no new premise.

## Prior v1 findings

All three rejected-package defects are repaired exactly:

1. The Riesz derived block now explicitly begins with `1<p<2`.
2. The Evans source quotation now states an open Euclidean domain `U` and the
   finite range `1<=p<infinity`.
3. The Hörmander quotation now states
   `hat(hat(u))(x) = (2*pi)^n * u(-x)`.

The repairs agree with the corresponding locked `SOURCE_TRANSLATION.md`
records and introduce no endpoint, normalization, domain, or conclusion
change.

## Closure and package correspondence

Independent recomputation produced:

- 18/18 meaning-bearing definitions, complete and dependency ordered;
- 29/29 Isabelle listings with the manifest SHA-256;
- 29/29 listings as exact substrings of their pinned owner theories;
- 29/29 identical Isabelle listings across A/B;
- 41/41 additional authority-bearing blocks byte-identical across A/B;
- 29/29 back-translation pairs textually distinct.

Both translations of every definition, the claim, and every literature
interface were semantically faithful. No copied A/B English pair or hidden
meaning-bearing omission was found.

## Literature and trust union

The exact union is ten direct IDs and zero inherited IDs: five AIM interfaces,
three Evans density interfaces, and two Hörmander interfaces. For each entry,
the reviewer rechecked attribution, locator, quoted source statement,
separately stated derived result, exact Isabelle interface, and both English
back-translations against the locked translation and theory.

No normalization, endpoint, exceptional-set, totalization, domain, density,
quantifier, or locator mismatch remains. The terminal graph contains no
trusted `MANUSCRIPT` or `PROVISIONAL` fact. The additional
`slp_qstar_w1p_claim` is proved internally. Searches found no `sorry`, `oops`,
global `axiomatization`, oracle, `quick_and_dirty`, `CF_Scratch_`, experimental
import, or distribution/scratch dependency.

## Mechanical and visual gates

`check-translation-package -RequireReady` passed for schema 2, package version
2, one claim, 18 definitions, ten direct literature entries, and zero inherited
entries. The read-only frozen/static project gate passed its deterministic
session chain, statement and literature locks, admission scan across 1,192
theories, scratch isolation, and distribution isolation. That invocation used
`-SkipBuild`; it is not the required final FullHistory replay.

Both 16-page A4 PDFs were independently rendered and visually inspected. No
clipping, overlap, broken glyph, missing content, malformed section transition,
or unreadable listing was found in
`artifacts/inverse-schrodinger-lp-uniqueness/TRANSLATION_A.pdf` or
`artifacts/inverse-schrodinger-lp-uniqueness/TRANSLATION_B.pdf`.
`git diff --check` also passed; line-ending notices were warnings only.

## Findings and limitations

No audit finding remains. The following are expected post-audit gates, not
defects in the reviewed bytes:

1. Record this immutable v2 audit in the manifest and run `-RequireAudited`.
2. Replay authoritative FullHistory after the final audit/result-ledger
   changes. ReleaseClosure remains advisory.
3. Include all controlled package, theorem, audit, reconciliation,
   verifier-feedback, and ledger files in the user-required single final
   coherent checkpoint.
4. Run the audited-manifest, workflow/current-result, and post-commit
   checkpoint verifiers.
5. Continue to disclose that statement and literature human ratification
   remains pending under `testing_waiver`.

Subject to those gates, package v2 supports the exact project label
`VERIFIED_RELATIVE_TO_LITERATURE`.

**Verdict: PASS**
