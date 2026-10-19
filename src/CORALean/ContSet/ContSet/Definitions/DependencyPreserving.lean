module

public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# Dependency preservation

[1, Def. 4] over [1, Def. 3]'s evaluation function: a parameterized set is the function `e` sending
a parameter value to the part of the set it names, and an operation preserves dependencies when what
`e` names at `d` lands inside what the *result's* own evaluation function names at that `d`.

Not a class and not over a representation: [1] compares several, and the polynomial zonotope is the
one whose whole operation set qualifies. So both evaluation functions are arguments, and every
instance is a theorem about one operation: `PolyZonotope.map_subsetAt` and
`PolyZonotope.bilin_subsetAt`.

## Inputs
* `D` – parameter domain
* `α` – source set type
* `β` – target set type
* `A` – set operation
* `e` – evaluation function of the input
* `e'` – evaluation function of the output

## Output
* `A` of what `e` names at `d` lies in what `e'` names at `d`

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set operation `A` applied to what `e` names at `d` lands inside what
`e'` names at that same `d`. -/
def DependencyPreserving {D α β : Type} (A : Set α → Set β) (e : D → Set α)
    (e' : D → Set β) : Prop :=
  ∀ d, A (e d) ⊆ e' d

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
