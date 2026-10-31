import MonoidProduct.Matroid.Greedy
import MonoidProduct.Matroid.GreedyWeight
import MonoidProduct.Matroid.GreedyMonoid
import MonoidProduct.Matroid.Records
import MonoidProduct.Matroid.Width
import MonoidProduct.Matroid.Quantum
import MonoidProduct.Matroid.Vector
import MonoidProduct.Matroid.Selection
import MonoidProduct.Matroid.Graphic
import MonoidProduct.Matroid.Certificates

/-!
# Minimum-weight matroid bases (`monoid.tex`, `sec:matroid-bases`)

The greedy basis and its merge law (`lem:matroid-greedy-merge`), minimum total
weight, the commutative idempotent monoid of independent sets with breadth equal
to the rank (`prop:matroid-greedy-monoid`), labelled input records, and the
query bound `Q_{1/3} ≤ min{n, 2^18·√(n·r)}` (`thm:matroid-basis-query`).  Greedy bases are
strong certificates for the greedy-basis map, whose extension monoid is the greedy-basis monoid,
and the query bound also follows from `cor:certificate-queries`.
-/
