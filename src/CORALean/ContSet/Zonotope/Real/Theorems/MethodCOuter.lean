module

public import CORALean.ContSet.Zonotope.Real.Operations.MethodC
public import CORALean.ContSet.Zonotope.Real.Theorems.ParallelotopeOuter

@[expose] public section

/-!
# Method C encloses

[1, Sec. 5.4.2]'s method C is [1, Prop. 8] at a `Γ` of full rank, always: the selection
keeps regular choices only, `List.argmin` returns one of them, and the fallback is `I`.
So the enclosure needs no hypothesis — unlike CORA's, whose singular case a `pinv` hides.

## Inputs
* `Z` – zonotope
* `κ` – length-filter size
* `κ'` – volume-filter size

## Hypotheses
* none

## Conclusion
* `Z` lies in the method-C parallelotope

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Method C's `Γ` is regular. -/
private theorem Zonotope.aux_methodCBasis_isUnit_det (Z : Zonotope (Vec ℝ n))
    (κ κ' : ℕ) : -- --- CONCL ---
    IsUnit (Z.step_methodCBasis κ κ').det := by -- --- PROOF ---
  simp only [Zonotope.step_methodCBasis]
  split
  · rename_i l hl
    -- the choice is among the regular ones, through the sort and the cut
    have hmem := List.argmin_mem hl
    have hmem' := (List.mem_mergeSort.mp (List.mem_of_mem_take hmem))
    have hdet := (List.mem_filter.mp hmem').2
    exact isUnit_iff_ne_zero.mpr (of_decide_eq_true hdet)
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.4.2]: method C's parallelotope encloses the zonotope. -/
theorem Zonotope.methodC_outer (Z : Zonotope (Vec ℝ n)) (κ κ' : ℕ) :
    Z.construct ⊆ (Z.methodC κ κ').construct :=
  Z.parallelotope_outer (Z.aux_methodCBasis_isUnit_det κ κ')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
