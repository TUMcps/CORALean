module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# Membership in a halfspace description

The two constraint blocks read back one at a time. `construct` is a set-builder
over exactly this conjunction, so the equivalence is `Iff.rfl`; what it buys is
a name for the pair, which is what every operation and every specification check
states its obligation as.

## Inputs
* `P` – H-polytope
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in `P` iff it meets every inequality and every equality
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_construct_iff {P : HPolytope α} {x : α} :
    x ∈ P.construct ↔ (∀ i, P.A i x ≤ P.b i) ∧ ∀ i, P.Ae i x = P.be i := Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
