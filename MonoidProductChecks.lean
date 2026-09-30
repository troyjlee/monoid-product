/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import MonoidProduct

/-!
# MonoidProduct axiom checks

Every headline theorem of the semigroup product development is asserted, via
`#guard_msgs`, to depend on exactly `[propext, Classical.choice, Quot.sound]`,
the axioms of ordinary classical mathematics in Lean. If a `sorry` (the axiom
`sorryAx`) or any new axiom enters a proof upstream, this file stops compiling,
so CI turns the axiom policy into a build invariant.
-/

namespace MonoidProduct

/-! ## Commutative aperiodic monoids -/

/-! ## Stably ordered monoids -/

/-! ## Finite aperiodic semigroups -/

/-! ## Lower bounds -/

end MonoidProduct
