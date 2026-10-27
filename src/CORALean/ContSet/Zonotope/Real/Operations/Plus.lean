module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.plus`

CORA's `@zonotope/plus`: centers add, generators concatenate [1, Sec. 2].

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope

## Output
* Minkowski sum zonotope

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.plus (Z₁ Z₂ : Zonotope α) : Zonotope α where
  h := Z₁.h + Z₂.h
  c := Z₁.c + Z₂.c
  G := Fin.append Z₁.G Z₂.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
