module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.containsAll`

The `'exact:zonotope'` branch of CORA's `@zonoBundle/contains_`: a set `S` is contained in the
bundle when every member zonotope contains it, `res = res & res_part` over the members. The
members' own containment is each zonotope's `contains_`; here it is the proposition it decides,
`S ⊆ Zᵢ`. The scaling factor, the maximum of the members' factors, is not modelled.

## Inputs
* `zB` – zonotope bundle
* `S` – set to test

## Output
* the set lies in every member
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every member contains `S`. -/
def ZonoBundle.containsAll (zB : ZonoBundle α) (S : Set α) : Prop :=
  ∀ i : Fin zB.k, S ⊆ (zB.Z i).construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
