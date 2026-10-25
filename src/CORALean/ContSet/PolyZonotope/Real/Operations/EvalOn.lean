module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# `PolyZonotope.evalOn`: [1, (13)]'s evaluation function

[1, Def. 3] at a polynomial zonotope is [1, (13)]: holding the dependent factors inside a
sub-box `B` of their domain leaves the *whole* independent block free, so what the set denotes
there is a zonotope and not a point. `subsetAt` is the dependent half of the same thing and
coincides with this only at `q = 0`. Everything [1] says about `reach` needs the other half as
well: every operation of its Alg. 1 grows the independent block.

## Inputs
* `pZ` – polynomial zonotope
* `B` – set of factor values

## Output
* set of points attained with factor values in that set

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `pZ` denotes when its dependent factors are held inside `B`: the point
`B` reaches, widened by the whole independent block. -/
def PolyZonotope.evalOn (pZ : PolyZonotope α) (B : Set (Fin pZ.p → ℝ)) : Set α :=
  {x | ∃ a ∈ B, ∃ β : Fin pZ.q → ℝ, (∀ j, |β j| ≤ 1) ∧ x = pZ.point a + ∑ j, β j • pZ.GI j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
