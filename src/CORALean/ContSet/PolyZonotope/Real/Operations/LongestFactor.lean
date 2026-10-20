module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# `PolyZonotope.longestFactor`

The factor `@polyZonotope/splitLongestGen` splits: take the dependent generator of largest
squared length `Σᵢ G(i,j)²`, the first on a tie, and in its exponent column the factor of
largest exponent, again the first on a tie. `none` when there is no generator or no factor,
where CORA's `max` of an empty vector errors.

Over `Vec ℝ n`, where a generator has coordinates, and `noncomputable` with it.

## Inputs
* `pZ` – polynomial zonotope

## Output
* index of the longest factor, if any
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factor of highest exponent in the longest dependent generator. -/
noncomputable def PolyZonotope.longestFactor (pZ : PolyZonotope (Vec ℝ n)) :
    Option (Fin pZ.p) :=
  match (List.finRange pZ.h).argmax (fun i => ∑ c, pZ.G i c ^ 2) with
  | some i => (List.finRange pZ.p).argmax (fun k => pZ.E k i)
  | none => none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
