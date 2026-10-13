import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `PolyZonotope.evalOn`: [1, (13)]'s evaluation function

[1, Def. 3] at a polynomial zonotope is [1, (13)]: holding the dependent factors
inside a sub-box `B` of their domain leaves the *whole* independent block free,
so what the set denotes there is a zonotope and not a point.

`subsetAt` is the dependent half of the same thing and coincides with this only
at `q = 0`, which `subsetAt_unitBox` already has to assume. Everything [1] says
about `reach` needs the other half as well: every operation of its Alg. 1 grows
the independent block, so a dependency statement that drops it is false one step
into the loop.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
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
