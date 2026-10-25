module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# `PolyZonotope.subsetAt`: the subset a sub-box of the factors picks out

The image of `point` restricted to a sub-box `B ⊆ Fin pZ.p → ℝ` of the factor domain,
[1, Def. 3]'s dependency result in one line: a subset of the initial factors names the
corresponding subset of the reachable set. No class carries this: a `factors`/`point`/
`point_mem` interface would also be satisfied by `Zonotope`. What #83 wants is that the *same*
index names corresponding points across an operation, a fact about `map_point`, `bilin_point`,
`gcnSteps_point` and siblings. So: a definition here, and each `_point` lemma composed with it.

## Inputs
* `pZ` – polynomial zonotope
* `B` – box of factor values

## Output
* set of points attained with factor values in the box

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The subset of `pZ`'s reachable set a sub-box `B` of the factor domain reaches
under `point`. -/
def PolyZonotope.subsetAt (pZ : PolyZonotope α) (B : Set (Fin pZ.p → ℝ)) : Set α :=
  pZ.point '' B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
