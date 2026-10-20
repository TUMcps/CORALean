module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.Operations.Shrink
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceMethCOuter

@[expose] public section

/-!
# `ZonoBundle.shrink` encloses the bundle

A point of the bundle is in every reduced member (`Zonotope.reduceMethC_outer`), so in their
bundle, and each new member encloses that bundle (`enclosingParallelotope_outer`).

## Inputs
* `zB` – float zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Conclusion
* the bundle is contained in the shrunk bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.shrink_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.shrink hk).construct := by -- --- PROOF ---
  intro x hx
  have hP : x ∈ (⟨zB.k, fun i => Zonotope.reduceMethC (zB.Z i) 1⟩ :
    ZonoBundle (Vec 𝕋 n)).construct :=
    SetIntersection.mem_construct_ofFn.mpr fun i =>
      Zonotope.reduceMethC_outer _ 1 (SetIntersection.mem_construct_ofFn.mp hx i)
  -- every new member is a parallelotope around the reduced bundle
  exact SetIntersection.mem_construct_ofFn.mpr fun i =>
    ZonoBundle.enclosingParallelotope_outer (⟨zB.k, fun i => Zonotope.reduceMethC (zB.Z i) 1⟩ :
      ZonoBundle (Vec 𝕋 n)) hk _ hP

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
