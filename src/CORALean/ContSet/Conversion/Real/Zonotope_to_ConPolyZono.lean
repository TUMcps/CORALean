import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A zonotope as a constrained polynomial zonotope

Exact, composing two exact readings: `Zonotope.polyZonotope_exact` gives each
generator its own factor, and `PolyZonotope.conPolyZono_exact` then adds an empty
constraint system that says nothing. Neither hop loses anything, so the equality
survives the composition whole, unlike every other representation's route to
`ConPolyZono` through the same two lemmas.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def Zonotope.conPolyZono (Z : Zonotope α) : ConPolyZono α :=
  Z.polyZonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.conPolyZono_exact (Z : Zonotope α) :
    Z.construct = Z.conPolyZono.construct :=
  (Zonotope.polyZonotope_exact Z).trans (PolyZonotope.conPolyZono_exact _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
