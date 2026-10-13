import CORALean.ContSet.ZonoBundle.Float.Operations.ContainsPoint
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound

/-!
# A `true` from `ZonoBundle.containsPoint` proves membership

The bundle is the intersection of its members, and a point in every member is in it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.containsPoint_sound {zB : ZonoBundle (Vec 𝕋 n)}
    {H : (i : Fin zB.k) → Mat 𝕋 (zB.Z i).h n} {p : Vec 𝕋 n}
    (h : zB.containsPoint H p = true) : toRealVec p ∈ zB.construct := by
  simp only [ZonoBundle.containsPoint, List.all_eq_true, List.mem_finRange, forall_const] at h
  exact Set.mem_iInter.mpr fun i => Zonotope.containsPoint_sound (h i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
