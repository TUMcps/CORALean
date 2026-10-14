module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_Zonotope

@[expose] public section

/-!
# One component of a bundle, enclosing it, over a floating-point scalar

Any single member already encloses the whole intersection, so the choice of `i`
owes no proof: the guarantee is sound at every one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.zonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.zonotope i).construct :=
  Set.iInter_subset _ i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
