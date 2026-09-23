# Checked result

Project-level label: **VERIFIED_RELATIVE_TO_LITERATURE**

- `slp_alessandrini_uniqueness_claim_v2` in `Inverse_Schrodinger_Lp_Alessandrini_Uniqueness_V2` — frozen v002 uniqueness theorem: universal integrable complex-bilinear Alessandrini orthogonality implies almost-everywhere equality for every real p>1

The exact trust boundary, including every active literature proposition, is
enumerated in `translation/TRANSLATION_A.tex` and `translation/TRANSLATION_B.tex` and
`provenance/TRUSTED_BASE.md`.

## Excluded claims

- The manuscript Dirichlet-to-Neumann theorem main-thm (preserved statement v001) is not established by this package.
- Forward Dirichlet solvability, weak DN-map well-definedness and the DN-to-Alessandrini bridge are outside this checked claim.

## Scope notes

- The checked proposition concerns two possibly complex-valued L^p potentials on a bounded smooth planar domain, with the exact weak-solution, integrability, bilinear-pairing and almost-everywhere conventions exposed in translation/.
- The trusted literature boundary is exactly the ten interfaces in literature lock v10. Seven literature premises are explicit in the terminal theorem; its locale contributes three additional distinct premises, for ten in total. No manuscript or provisional result is trusted.
- Statement lock v2 and all ten literature entries were reviewed and frozen under testing_waiver. Exact-byte human semantic ratification remains pending. Packaging and publication do not supply that approval.
- The five translation files are byte-identical to the independently audited translation package v2. Its preserved README still says review-ready; the later audited manifest and PASS report in provenance/ record completion. The historical README is preserved to retain its audited hash.


The authoritative machine check is the successful build of
`Paper_Inverse_Schrodinger_Lp_Proof_Stage_018` from the bundled source closure. See
`MANIFEST.json` for exact source hashes, required releases, external AFP/base
sessions, and the non-gating last-compared manuscript provenance.
