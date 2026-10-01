import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

/-!
# One component of a bundle, enclosing it, over a floating-point scalar

Any single member already encloses the whole intersection, so the choice of `i`
owes no proof: the guarantee is sound at every one.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.zonotope (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) : Zonotope 𝕋 n := zB.Z i


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.zonotope_contains (zB : ZonoBundle 𝕋 n) (i : Fin zB.k) :
    zB.construct ⊆ (zB.zonotope i).construct :=
  Set.iInter_subset _ i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
