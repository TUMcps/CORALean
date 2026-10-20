module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup

@[expose] public section

/-!
# `PolyZonotope.relaxExpGroup`

A whole group merged at once, where `relaxExpMulti` merges a pair: the `k` generators
`part.right` names are absorbed into the kept generator `t`, whose monomial they all take, and
each member pays its own drift into its own independent generator. Whose monomial survives is
the choice a pairwise merge never has to make, so the target is an argument. `k = 0` merges
nothing and only renames the generators; `k = 1` is a merge of a pair. Any group may be merged:
the grouping decides how wide the new generators are, never whether the result encloses.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split into kept generators and a group
* `t` – target generator

## Output
* polynomial zonotope with the group merged onto the target
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k` generators `part.right` names merged into the kept generator `t`, at
`t`'s exponent column, each scaled by its own `ξ_E` becoming independent. -/
def PolyZonotope.relaxExpGroup (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin k)) (t : Fin d) : PolyZonotope α where
  p := pZ.p
  h := d
  q := pZ.q + k
  c := pZ.c
  G := fun l => pZ.G (part.left l) + if l = t then ∑ j, pZ.G (part.right j) else 0
  E := fun i l => pZ.E i (part.left l)
  GI := Fin.append pZ.GI fun l => (pZ.relaxWidthGroup part t l : ℝ) • pZ.G (part.right l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
