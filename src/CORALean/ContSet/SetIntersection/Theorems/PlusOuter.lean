module

public import CORALean.ContSet.SetIntersection.Operations.Plus
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# `SetIntersection.plus` over-approximates the Minkowski sum

`(⋂ᵢ Aᵢ) + (⋂ⱼ Bⱼ) ⊆ ⋂ᵢⱼ (Aᵢ + Bⱼ)`: a summand from each operand's
intersection lies in every branch of that operand, so it sums into every
pairwise `plus`, `Plus.plus_outer` reading that sum back into the branch.

## Inputs
* `I` – first intersection
* `J` – second intersection

## Hypotheses
* none

## Conclusion
* the Minkowski sum lies in the result
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Plus S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetIntersection.plus_outer (I J : SetIntersection S) : -- --- CONCL ---
    ContSet.construct I + ContSet.construct J ⊆
      ContSet.construct (SetIntersection.plus I J) := by -- --- PROOF ---
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have ha := SetIntersection.mem_construct.mp ha
  have hb := SetIntersection.mem_construct.mp hb
  refine SetIntersection.mem_construct.mpr ?_
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hs, ht⟩ := List.mem_product.mp hp
  exact Plus.plus_outer p.1 p.2 (Set.add_mem_add (ha p.1 hs) (hb p.2 ht))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
