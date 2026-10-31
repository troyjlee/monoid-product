import MonoidProduct.Certificates.Basic
import MonoidProduct.Certificates.ExtensionMonoid
import MonoidProduct.Certificates.Breadth
import MonoidProduct.Certificates.Quantum
import MonoidProduct.Certificates.Acceptance
set_option linter.style.header false

/-!
# Strong certificates and product breadth (`monoid.tex`, `sec:strong-certificates`)

Equivalence under extensions and strong certificates (`def:strong-certificate`), the extension
monoid (`def:extension-monoid`) and its cardinality bound, the equality of product breadth with
the strong-certificate size (`thm:certificate-breadth`), and the query bound
`Q_{1/3} ≤ min{n, 2^18·√(n·b_f(U))}` (`cor:certificate-queries`), also for position-dependent
encodings.
-/
