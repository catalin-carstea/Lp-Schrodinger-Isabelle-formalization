# Trusted-base ledger

The default policy is to prove manuscript claims and to trust only precisely
identified, generally accepted background results. If no external result is
used, say so explicitly.

Literature-lock status: `frozen`, version 10. Each `LITERATURE` row has the same
ID as a frozen entry in `literature-lock.json`.

Possible resources belong first in `LITERATURE_PREFLIGHT.md`. That acquisition
list is not part of the trusted base; promote only a result actually proposed
for use, after its exact source and formal interface are identified. Do not
promote a source whose preflight status remains `USER_CHECK` or `UNKNOWN`;
record the user's bibliographic-suitability decision separately from semantic
approval or a testing waiver.

## Summary

| ID | Class | Formal fact used | Source | Consumers | Review status |
|---|---|---|---|---|---|
| LIB-AE-RESTRICT | `LIBRARY` | `AE_restrict_space_iff` | Isabelle2025-2 `HOL-Analysis.Measure_Space` | WP-005 restricted-domain integral bridge | Kernel-checked in native and reproducible session builds |
| LIB-BOCHNER-CONG | `LIBRARY` | `borel_measurable_integrable`, `integral_cong_AE` | Isabelle2025-2 `HOL-Analysis.Bochner_Integration` | WP-005 weak-form congruence | Kernel-checked in native and reproducible session builds |
| LIB-FINITE-COMPLEX | `LIBRARY` | finite-sum distribution/delta laws and complex real/imaginary-part simplification | Isabelle2025-2 HOL finite sums and `Complex` | WP-006 signed quadratic normal form | Kernel-checked in native and reproducible session builds |
| HORMANDER-QUADRATIC-STATIONARY-PHASE | `LITERATURE` | For a real symmetric nondegenerate matrix and compactly supported smooth integrable complex amplitude, the associated quadratic oscillatory integral tends to zero at positive infinity | Hörmander 1983, Lemma 7.7.3, equation (7.7.7), printed pp. 218--219 | Planned smooth-amplitude stage of official `lem-quadratic-RL`; no current proof consumer | Frozen literature lock v1 after three independent fixed-hash `PASS` reviews and primary reconciliation; `testing_waiver`, human ratification pending |
| EVANS-COMPACT-SMOOTH-L1-DENSITY | `LITERATURE` | Every complex Bochner-integrable function on `real^'n` has arbitrarily close `L1` approximants satisfying the exact compact-smooth amplitude predicate | Evans 2010, Appendix C.5, standard mollifier and Theorem 7(i),(iv), printed pp. 713--716, plus the reviewed truncation/support/local-to-global/complexification consequence | Direct premise source for the next checked consumer combining density with WP-008 | Frozen literature lock v2 after independent source, adversarial, and Isabelle-semantics fixed-hash reviews plus primary reconciliation; one non-material epsilon-allocation clarification retained in the locked review closure; `testing_waiver`, human ratification pending |
| EVANS-COMPACT-SMOOTH-LP-DENSITY | `LITERATURE` | For every finite real `q>=1`, every measurable complex whole-space field with integrable `norm F powr q` has arbitrarily close compact-smooth approximants in the rooted `L^q` norm | Evans 2010, Appendix C.5, standard mollifier and Theorem 7(i),(iv), printed pp. 713--716, plus explicit truncation/support/local-to-global/common-scale complexification | Dual-density premise for the post-WP1495 almost-everywhere recovery chain; a checked interior-support localization bridge and explicit approximation-error integrability are mandatory before direct use | Frozen literature lock v10 after one isolated fixed-hash `PASS` and two isolated fixed-hash `PASS_WITH_FINDINGS` reviews plus primary reconciliation; no material finding, with error-integrability and support-localization obligations retained in the locked closure; `testing_waiver`, human ratification pending |
| EVANS-COMPACT-SUPPORT-W1P-ZERO-DENSITY | `LITERATURE` | A complex project `W^{1,p}(X)` pair with finite real `p>=1` and common compact support strictly inside open `X` belongs to the project's smooth-test-function `W^{1,p}_0(X)` closure | Evans 2010, definitions printed pp. 256 and 259, Section 5.3.1 Theorem 1 and proof printed pp. 264--265, Appendix C.5 printed pp. 713--716, and the explicit compact-support/common-scale complexification/project-norm consequence | Proposed zero-Sobolev premise for the smooth-cutoff inner Cauchy field in the high endpoint; no proof consumer yet | Frozen literature lock v9 after two isolated fixed-hash `PASS_WITH_FINDINGS` reviews, one isolated fixed-hash `PASS` review, and primary reconciliation; quantitative support-margin, fixed-container local-to-global, and degenerate-case clarifications retained in the locked closure; `testing_waiver`, human ratification pending |
| AIM-PLANAR-HARDY-LITTLEWOOD-SOBOLEV | `LITERATURE` | One absolute constant controls the normalized planar Cauchy transform from explicit representative-level `L^p` to `L^(2p/(2-p))` for every `1<p<2`, with the source denominator `(p-1)(2-p)` | Astala--Iwaniec--Martin 2009, Theorem 4.3.8 printed p. 111 / PDF p. 130, with normalization and displayed HLS estimate on printed pp. 109--110 / PDF pp. 128--129 | First checked value-estimate consumer for official `lem-cauchy-basic`; consumer must prove the exact `SLP_Dbar_Inverse` bridge and may not infer everywhere absolute convergence | Frozen literature lock v3 after independent source, adversarial, and Isabelle-semantics fixed-hash reviews plus primary reconciliation; non-material representative/exceptional-set/scope cautions retained in the locked review closure; `testing_waiver`, human ratification pending |
| AIM-PLANAR-BEURLING-LP-BOUND | `LITERATURE` | For every finite real `p>1`, one positive constant uniform in the input controls the explicit representative-level planar Beurling principal-value transform on complex `L^p`; the principal value exists almost everywhere | Astala--Iwaniec--Martin 2009, formula (4.17), Theorem 4.0.10, and Theorem 4.5.3 with (4.84), printed pp. 94, 97--98, and 129 / PDF pp. 113, 116--117, and 148 | Checked Beurling-value consumer for the Sobolev clause of official `lem-cauchy-basic`; derivative and Cauchy-intertwining identities require separate authority | Frozen literature lock v4 after three independent fixed-hash `PASS` reviews and primary reconciliation; `testing_waiver`, human ratification pending |
| AIM-PLANAR-CAUCHY-BEURLING-DERIVATIVES | `LITERATURE` | For every finite real `p>1` and bounded-support explicit `L^p` representative, the normalized source-orientation Cauchy transform has whole-plane weak Cartesian gradient `(f+Sf, i*(Sf-f))`, equivalently `dbar(Cf)=f` and `partial(Cf)=Sf` | Astala--Iwaniec--Martin 2009, Definition 4.0.9, formulas (4.6), (4.8), (4.16)--(4.17), Theorem 4.0.10, the printed-p.96 `L^p` extension, and Theorem 4.5.3, printed pp. 93--98 and 129 / PDF pp. 112--117 and 148 | Derivative component of official `lem-cauchy-basic`; consumers must also supply the separately frozen Beurling premise explicitly, while the opposite Cauchy orientation and Sobolev norm packaging remain checked obligations | Frozen literature lock v5 after three independent fixed-hash `PASS` reviews and primary reconciliation; nonmaterial support, representative, null-circle, and explicit-premise observations retained; `testing_waiver`, human ratification pending |
| AIM-PLANAR-CAUCHY-TEST-LEFT-INVERSE | `LITERATURE` | For every compactly supported smooth complex test function, the normalized planar Cauchy transform of its classical `dbar` derivative equals the function everywhere | Astala--Iwaniec--Martin 2009, Definition 4.0.9 and formula (4.8), printed p. 93 / PDF p. 112 | Source-orientation premise for a later checked conjugation proof of official lines 489--494 | Frozen literature lock v7 after three independent fixed-hash `PASS` reviews and primary reconciliation; exact convention, totalization, everywhere equality, and locale-isolation checks retained; `testing_waiver`, human ratification pending |
| AIM-PLANAR-RIESZ-POTENTIAL-HLS | `LITERATURE` | One absolute constant controls the positive planar order-one Riesz potential from explicit complex representative-level `L^p` to real `L^(2p/(2-p))` for every `1<p<2`, with the source denominator `(p-1)(2-p)` and ordinary integrability at almost every output | Astala--Iwaniec--Martin 2009, displayed Hardy--Littlewood--Sobolev inequality immediately before Theorem 4.3.8, printed p. 110 / PDF p. 129 | Pointwise positive-potential majorant for the first inclusion of official `lem-localized-kernel-mapping`; radial kernel integrability and Young/Hölder mappings remain separate checked obligations | Frozen literature lock v6 after the v001 audit exposed a material totalization gap, explicit AE-integrability repair, and three restarted fixed-hash v002 `PASS` reviews plus primary reconciliation; `testing_waiver`, human ratification pending |
| HORMANDER-EUCLIDEAN-L2-FOURIER-PLANCHEREL | `LITERATURE` | On `real^2`, an `L2` Fourier realization agrees AE with the negative-exponential/no-forward-prefactor `L1` integral on `L1 intersect L2`, preserves squared mass up to `(2*pi)^2`, and squares to `(2*pi)^2` times reflection AE | Hörmander 1983, Definition 7.1.1/(7.1.3), Parseval (7.1.8), Definition 7.1.9, and Theorems 7.1.10--7.1.11, printed pp. 160, 163--164 / PDF pp. 169, 172--173 | Planned sole direct consumer is WP-514 O3; consumer still owes domain, definition-matching, Fourier-side equality, and physical center-average transfer | Frozen literature lock v8 after three isolated fixed-hash `PASS` reviews and primary reconciliation; candidate native and pinned-Linux builds passed; `testing_waiver`, human ratification pending; not yet consumed by a proof theory |

## Detailed entries

The checked-library rows above are ordinary pinned Isabelle dependencies,
not outside-literature premises. The exact Hörmander stationary-phase,
Hörmander planar `L2` Fourier/Plancherel, Evans density, AIM planar HLS, AIM
planar Beurling, AIM Cauchy/Beurling derivative, compact-smooth Cauchy
left-inverse, positive planar Riesz-potential, and compact-support planar
`W^{1,p}_0` density consequences are the nine
frozen `LITERATURE` premises. Their locks record the temporary testing waiver
and pending human ratification. No broader Fourier/distribution theorem, HLS
endpoint, Beurling
endpoint/sharp/weighted result, opposite-orientation left-inverse premise,
global Sobolev estimate, stationary-phase expansion, mollifier theorem,
Rellich result, or PDE statement is admitted.

## Explicit exclusions

List results that may look standard but are not being assumed, especially
claims made by the manuscript itself.

- Theorem `main-thm` and all 28 other numbered manuscript claims are
  `MANUSCRIPT`; none may be promoted merely because the expanded version gives
  additional proof detail.
- Blåsten–Tzou–Wang 2020, Bukhgeim 2008, and Blåsten 2011 are comparison or
  background sources at intake, not trusted premises.
- The expanded manuscript is strategy assistance, not an external authority
  and not part of the trusted base.
- Evans's Morrey, general Sobolev, Rellich--Kondrachov, and all other PDE
  results remain preflight candidates only; freezing the Appendix C.5 density
  consequence does not admit them.
