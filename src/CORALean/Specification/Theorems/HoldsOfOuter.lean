import CORALean.Specification.Specification

/-!
# An outer approximation is enough to check a specification against

The exact set — the reachable set of a system, the image of a network — is
not computable; what an algorithm returns is a superset of it. This is the step
that makes that superset useful: a specification holding on the computed set
holds on the exact one, in *both* directions of the definition and for opposite
reasons.

A safe set is closed downward under `⊆`, so containment survives shrinking. An
unsafe set is avoided by everything a set that avoids it contains. Neither
argument mentions how either set was computed, which is why the check sits here
rather than in any one algorithm.

The converse fails, and that is the whole cost of the method: a specification
violated on the computed set says nothing, the violation possibly lying in the
approximation error alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} {X O : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_of_outer (spec : Specification α) (h : X ⊆ O)
    (hO : spec.Holds O) : spec.Holds X := by
  obtain ⟨s, k⟩ := spec
  cases k
  · exact subset_trans h hO
  · exact hO.mono_left h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
