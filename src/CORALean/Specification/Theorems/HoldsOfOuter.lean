module

public import CORALean.Specification.Specification

@[expose] public section

/-!
# An outer approximation is enough to check a specification against

The exact set (a reachable set, the image of a network) is not computable; what an algorithm
returns is a superset. A specification holding on the computed set holds on the exact one, in both
directions of the definition: a safe set (and an invariant) is closed downward under `⊆`, and an
unsafe set is avoided by everything a set that avoids it contains. Neither argument mentions how
the sets were computed; `Specification.custom` is built as a safe set. The converse fails: a
violation on the computed set says nothing, possibly lying in the approximation error alone.

## Inputs
* `spec` – specification

## Hypotheses
* `h` – the set lies in the outer set
* `hO` – the specification holds of the outer set

## Conclusion
* the specification holds of the set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet α : Type} [CORALean.ContSet ContSet α] {X O : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_of_outer (spec : Specification ContSet) (h : X ⊆ O)
    (hO : spec.Holds O) : spec.Holds X := by -- --- PROOF ---
  obtain ⟨s, k⟩ := spec
  cases k
  · exact subset_trans h hO
  · exact hO.mono_left h
  · exact subset_trans h hO

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
