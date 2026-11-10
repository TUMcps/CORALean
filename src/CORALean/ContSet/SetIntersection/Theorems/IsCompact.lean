module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ContSet.Definitions.Interfaces

@[expose] public section

/-!
# An intersection of compact members is compact

Of at least one member: the empty list denotes `univ`, compact only in the trivial ambient type,
which is why `SetIntersection` carries no `CompactSet` instance and this theorem asks for
`I.sets ≠ []`. One compact member and closed others are what the proof uses; a compact set is
closed in the normed ambient type, so every member supplies both.

## Inputs
* `I` – intersection

## Hypotheses
* `h` – `I` has a member

## Conclusion
* the intersection is compact
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSet S α] [CompactSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An intersection of at least one compact member is compact. -/
theorem SetIntersection.isCompact_toSet {I : SetIntersection S}
    (h : I.sets ≠ []) : -- --- CONCL ---
    IsCompact (ContSet.toSet I) := by -- --- PROOF ---
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ h
  -- the closed intersection sits inside the compact member `s`
  have hclosed : IsClosed (ContSet.toSet I) :=
    isClosed_biInter fun t _ => (CompactSet.isCompact_toSet t).isClosed
  exact (CompactSet.isCompact_toSet s).of_isClosed_subset hclosed
    (SetIntersection.toSet_subset hs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
