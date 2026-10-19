module

public import CORALean.ContSet.SetIntersection.Operations.Reduce
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# `SetIntersection.reduce` over-approximates the intersection

Each branch only grows, by `Reduce.reduce_outer`, so a point of every branch
of the operand stays a point of every branch reduced, and the intersection it
witnesses in stays covered after every branch is replaced by its own
reduction.

## Inputs
* `I` – intersection
* `o` – order bound

## Hypotheses
* none

## Conclusion
* `I` lies in the reduced intersection
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Reduce S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetIntersection.reduce_outer (I : SetIntersection S) (o : ℕ) :
    ContSet.construct I ⊆
      ContSet.construct (SetIntersection.reduce I o) := by -- --- PROOF ---
  intro x hx
  have hx := SetIntersection.mem_construct.mp hx
  refine SetIntersection.mem_construct.mpr ?_
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact Reduce.reduce_outer s o (hx s hs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
