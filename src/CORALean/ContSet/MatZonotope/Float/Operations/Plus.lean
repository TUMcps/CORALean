import CORALean.ContSet.MatZonotope.Float.Operations.OfEntryBounds

/-!
# `MatZonotope.plus`

The exact layer's `Zonotope.plus` at `Mat`: generators concatenate exactly, so only the
centre rounds, and the two boxes add. The count is `h₁ + h₂`, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatZonotope.plus (Z₁ Z₂ : MatZonotope 𝕋 m n) : MatZonotope 𝕋 m n :=
  MatZonotope.ofEntryBounds (fun i j => addDown (Z₁.c i j) (Z₂.c i j))
    (fun i j => addUp (Z₁.c i j) (Z₂.c i j)) (Fin.append Z₁.G Z₂.G) (Fin.append Z₁.G Z₂.G)
    (Interval.matPlus Z₁.E Z₂.E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
