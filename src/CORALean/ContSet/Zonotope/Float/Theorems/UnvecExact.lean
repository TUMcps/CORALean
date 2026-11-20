module

public import CORALean.ContSet.Zonotope.Float.Operations.Unvec
public import CORALean.ContSet.Zonotope.Float.Theorems.VecExact

@[expose] public section

/-!
# `Zonotope.unvec` is exactly the unstacked set

Stacking the unstacked zonotope gives it back, entry for entry, so `vec_exact` at the unstacked
zonotope says that its members are the unstackings of the members of the stacked one.

## Inputs
* `Z` – zonotope of stacked matrices

## Hypotheses
* none

## Conclusion
* the unstacked zonotope denotes exactly the unstackings of the members
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.unvec_exact (Z : Zonotope (Vec 𝕋 (n * m))) : -- --- CONCL ---
    Z.unvec.toSet = matVecEquiv.symm '' Z.toSet := by -- --- PROOF ---
  -- stacking the unstacked zonotope gives the zonotope back
  have h : Z.unvec.vec = Z := by
    cases Z with
    | mk h c G I =>
      have hI : (Interval.unvec I).vec = I := by
        cases I
        simp only [Interval.vec, Interval.unvec, Equiv.apply_symm_apply, Prod.mk.eta]
      simp only [Zonotope.vec, Zonotope.unvec, Equiv.apply_symm_apply, Prod.mk.eta, hI]
  -- so its members are the stackings of the unstacked ones
  have h2 := Zonotope.vec_exact Z.unvec
  rw [h] at h2
  rw [h2, Set.image_image]
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
