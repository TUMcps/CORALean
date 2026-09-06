import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `PolyZonotope.subsetAt`: the subset a sub-box of the factors picks out

The image of `point` restricted to a sub-box `B ⊆ Fin S.p → ℝ` of the factor
domain — [1]'s dependency result in one line: a subset of the initial factors
names the corresponding subset of the reachable set, because `point` is what a
factor vector picks out in the first place.

No class carries this. A `factors`/`point`/`point_mem` interface would also be
satisfied by `Zonotope`, whose coefficient vector indexes its points too — what
#83 wants is not that an index exists but that the *same* index names
corresponding points across an operation, which is a fact about `map_point`,
`bilin_point`, `gcnSteps_point` and their siblings, not about any one type. So:
a definition here, and each `_point` lemma composed with it below.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The subset of `S`'s reachable set a sub-box `B` of the factor domain reaches
under `point`. -/
def PolyZonotope.subsetAt (S : PolyZonotope α) (B : Set (Fin S.p → ℝ)) : Set α :=
  S.point '' B

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
