module

public import CORALean.ContSet.ZonoBundle.Float.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter

@[expose] public section

/-!
# `ContSet/ZonoBundle/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ============================  `ZonoBundle.reduceCombined_outer`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `enclosingParallelotope_outer` at the selected basis, which holds at any basis. -/
theorem ZonoBundle.reduceCombined_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.reduceCombined hk).construct :=
  ZonoBundle.enclosingParallelotope_outer zB hk _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
