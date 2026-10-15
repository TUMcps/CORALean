module

public import CORALean.Specification.FourValuedSTL.FourValuedSTL

@[expose] public section

/-!
# The atomic predicates of a formula

The atomic predicates `a ∈ AP` a formula mentions: the satisfaction signals of [1, Sec. 4.2
(satisfaction)] and [1, Sec. 4.3 (satisfaction)] are built from those of the atoms, and only these
need to be given.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The atoms of `φ`. -/
def FourValuedSTL.Formula.atoms {X : Type} : FourValuedSTL.Formula X → Set (X → Prop)
  | .tt => ∅
  | .atom a => {a}
  | .not φ => φ.atoms
  | .and φ ψ => φ.atoms ∪ ψ.atoms
  | .until _ _ φ ψ => φ.atoms ∪ ψ.atoms

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
