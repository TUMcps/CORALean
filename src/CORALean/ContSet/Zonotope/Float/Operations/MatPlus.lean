module

public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBoundsMat

@[expose] public section

/-!
# `Zonotope.matPlus`

The exact layer's `Zonotope.plus` at `Mat`: generators concatenate exactly, so only the
centre rounds, and the two boxes add. The count is `h₁ + h₂`, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.matPlus (Z₁ Z₂ : Zonotope (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 m n) :=
  Zonotope.ofEntryBoundsMat (fun i j => addDown (Z₁.c i j) (Z₂.c i j))
    (fun i j => addUp (Z₁.c i j) (Z₂.c i j)) (Fin.append Z₁.G Z₂.G) (Fin.append Z₁.G Z₂.G)
    (Interval.matPlus Z₁.E Z₂.E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
