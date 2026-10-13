import CORALean.ContSet.ZonoBundle.Float.Operations.Shrink
import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceMethCOuter

/-!
# `ZonoBundle.shrink` encloses the bundle

A point of the bundle is in every reduced member (`Zonotope.reduceMethC_outer`), so in their
bundle, and each new member encloses that bundle (`enclosingParallelotope_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.shrink_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.shrink hk).construct := by -- --- PROOF ---
  intro x hx
  have hP : x ∈ (⟨zB.k, fun i => Zonotope.reduceMethC (zB.Z i) 1⟩ :
    ZonoBundle (Vec 𝕋 n)).construct :=
    Set.mem_iInter.mpr fun i => Zonotope.reduceMethC_outer _ 1 (Set.mem_iInter.mp hx i)
  -- every new member is a parallelotope around the reduced bundle
  exact Set.mem_iInter.mpr fun i =>
    ZonoBundle.enclosingParallelotope_outer (⟨zB.k, fun i => Zonotope.reduceMethC (zB.Z i) 1⟩ :
      ZonoBundle (Vec 𝕋 n)) hk _ hP

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
