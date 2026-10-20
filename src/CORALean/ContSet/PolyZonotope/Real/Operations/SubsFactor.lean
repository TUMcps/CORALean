module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.subsFactor`

The factor of the result that a factor of `pZin` is: the one of `pZ` it shares its identifier with
(`Idx`, given by `share`), or a new one after `pZ`'s.

## Inputs
* `pZ` – polynomial zonotope
* `nu` – number of substituted factors
* `pZin` – polynomial zonotope substituted in
* `share` – map of shared factors
* `j` – inner factor index

## Output
* index of that factor in the combined factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factor of the result that `pZin`'s factor `j` is. -/
def PolyZonotope.subsFactor (pZ : PolyZonotope α) {nu : ℕ} (pZin : PolyZonotope (Vec ℝ nu))
    (share : Fin pZin.p → Option (Fin pZ.p)) (j : Fin pZin.p) : Fin (pZ.p + pZin.p) :=
  match share j with
  | some k => Fin.castAdd pZin.p k
  | none => Fin.natAdd pZ.p j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
