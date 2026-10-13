import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# A zonotope is a bundle of one

Exact: a single-zonotope family intersects nothing but itself, so the
intersection it denotes is the zonotope's own set, `Set.iInter_const` at the
one-element index type `Fin 1`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def Zonotope.zonoBundle (Z : Zonotope α) : ZonoBundle α := ⟨1, fun _ => Z⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonoBundle_exact (Z : Zonotope α) :
    Z.construct = Z.zonoBundle.construct := by
  show Z.construct = ⋂ _ : Fin 1, Z.construct
  exact (Set.iInter_const Z.construct).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
