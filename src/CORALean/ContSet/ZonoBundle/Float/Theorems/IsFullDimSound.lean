import CORALean.ContSet.ZonoBundle.Float.Operations.IsFullDim
import CORALean.ContSet.Zonotope.Float.Theorems.InteriorPointSound

/-!
# A `true` from `ZonoBundle.isFullDim` proves an interior point

The bundle is the intersection of its members. A point interior to every member is interior to the
intersection of finitely many of them (`interior_iInter_of_finite`).
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

theorem ZonoBundle.isFullDim_sound {zB : ZonoBundle 𝕋 n}
    {H : (i : Fin zB.k) → Mat 𝕋 (zB.Z i).h n} {x₀ : Vec 𝕋 n}
    (h : zB.isFullDim H x₀ = true) : (interior zB.construct).Nonempty := by
  simp only [ZonoBundle.isFullDim, List.all_eq_true, List.mem_finRange, forall_const] at h
  refine ⟨toRealVec x₀, ?_⟩
  rw [ZonoBundle.construct, interior_iInter_of_finite]
  exact Set.mem_iInter.mpr fun i => Zonotope.interiorPoint_sound (h i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
