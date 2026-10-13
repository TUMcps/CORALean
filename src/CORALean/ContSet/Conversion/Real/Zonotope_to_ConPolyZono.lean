module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A zonotope as a constrained polynomial zonotope

Exact, composing two exact readings: `Zonotope.polyZonotope_exact` gives each
generator its own factor, and `PolyZonotope.conPolyZono_exact` then adds an empty
constraint system that says nothing. Neither hop loses anything, so the equality
survives the composition whole, unlike every other representation's route to
`ConPolyZono` through the same two lemmas.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
