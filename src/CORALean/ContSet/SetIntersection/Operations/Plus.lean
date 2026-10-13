import CORALean.ContSet.SetIntersection.SetIntersection

/-!
# `SetIntersection.plus`

Every pair of branches, one from each operand, summed — the same pairing
`SetUnion.plus` uses, read at `⋂` instead of `⋃`: a point of each operand's
intersection lies in every branch, so it sums into every pairwise `plus`,
which is what makes the pairwise intersection an outer bound.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Plus S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every pair of branches, summed. -/
def SetIntersection.plus (I J : SetIntersection S) : SetIntersection S :=
  ⟨(I.sets ×ˢ J.sets).map fun p => Plus.plus p.1 p.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
