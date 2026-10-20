module

public import CORALean.ContSet.SetUnion.Operations.Plus
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `SetUnion.plus` over-approximates the Minkowski sum

Exact set identity first: `(⋃ Aᵢ) + (⋃ Bⱼ) = ⋃ᵢⱼ (Aᵢ + Bⱼ)`, since a summand
from each side comes from some branch on that side. `Plus.plus_outer` then
reads each pairwise sum back into `SetUnion.plus`'s own pairwise branch.

## Inputs
* `u` – first union
* `v` – second union

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

theorem SetUnion.plus_outer (u v : SetUnion S) : -- --- CONCL ---
    ContSet.construct u + ContSet.construct v ⊆
      ContSet.construct (SetUnion.plus u v) := by -- --- PROOF ---
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨s, hs, ha⟩ := SetUnion.mem_construct.mp ha
  obtain ⟨t, ht, hb⟩ := SetUnion.mem_construct.mp hb
  refine SetUnion.mem_construct.mpr ⟨Plus.plus s t, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(s, t), List.mem_product.mpr ⟨hs, ht⟩, rfl⟩
  · exact Plus.plus_outer s t (Set.add_mem_add ha hb)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
