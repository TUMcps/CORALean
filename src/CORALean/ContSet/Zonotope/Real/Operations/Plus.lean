import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.plus`

CORA's `@zonotope/plus`: centres add, generators concatenate [1, Sec. 2].

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
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
