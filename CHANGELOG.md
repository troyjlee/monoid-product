# Changelog

## Unreleased

- Strong certificates (`MonoidProduct.Certificates`, the paper's Section
  6.1): equivalence under extensions, strong certificates and the
  certificate size `strongCertificateSize`, the extension monoid
  `ExtensionMonoid` and its cardinality bound, the equality of product
  breadth with the certificate size (`certificate_breadth`), and the query
  bound `strongCertificate_qQuery_le_min_sqrt`, also for position-dependent
  encodings (`encodedCertificate_qQuery_le_min_sqrt`).
- Greedy bases as strong certificates (`Matroid/Certificates.lean`): the
  extension monoid of the greedy-basis map is the greedy-basis monoid, and
  the minimum-weight basis bound is rederived through the certificate
  theorem. The existing matroid endpoints are unchanged.
- The paper correspondence follows the paper's current numbering, which
  shifted from Section 6 onward, and lists the results of Sections 6.3 and
  6.4 as not yet formalized.

## 0.1.0

- First public release of the `MonoidProduct` library.
- Formalizes the results of *The quantum query complexity of the semigroup
  product problem* (Lee and Santha): commutative aperiodic monoids,
  stably ordered monoids, finite aperiodic semigroups, and minimum-weight
  matroid bases.
- Depends on QuantumQueryComplexity and on the `Sunflower` library of TCS
  formalizations, each pinned to a fixed commit.
- Requires Lean and Mathlib 4.35.0-rc2; exact dependencies are in the manifest.
