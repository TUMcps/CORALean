import CORALean.ContSet.ConZonotope.Operations.Zonotope

/-!
# `ConZonotope.linComb`

Taken on the enclosing zonotopes, so the result carries no constraints. Sound,
and the only part of the interface a constrained zonotope does not compute in
its own terms.

An exact constrained-zonotope convex hull exists — Raghuraman and Koeln's
construction, which lifts both constraint blocks and adds one interpolation
variable per generator — and is what should replace this. It is not needed
before a reachability algorithm asks for a constrained zonotope over a time
interval.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def ConZonotope.linComb (C₁ C₂ : ConZonotope α) : ConZonotope α :=
  (C₁.zonotope.linComb C₂.zonotope).conZonotope

end CORALean.Real
