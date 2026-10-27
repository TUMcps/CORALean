module

public import CORALean.ContSet.VPolytope.Float.Operations.Unvec
public import CORALean.ContSet.VPolytope.Float.Theorems.VecExact

@[expose] public section

/-!
# `VPolytope.unvec` is exactly the unstacked set

Unstacking undoes `VPolytope.vec`, which is exact, so the unstacked polytope denotes the images of
the stacked members under the inverse of the vectorisation.

## Inputs
* `P` – polytope of stacked vertices

## Hypotheses
* none

## Conclusion
* the unstacked polytope denotes exactly the unstackings of the members
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.unvec_exact (P : VPolytope (Vec 𝕋 (n * m))) : -- --- CONCL ---
    InflatedContSet.construct P.unvec =
      matVecEquiv.symm '' InflatedContSet.construct P := by -- --- PROOF ---
  -- stacking the unstacked polytope gives the polytope back
  have h : P.unvec.vec = P := by
    cases P with
    | mk k V I =>
      have hI : (Interval.unvec I).vec = I := by
        cases I
        simp only [Interval.vec, Interval.unvec, Equiv.apply_symm_apply, Prod.mk.eta]
      simp only [VPolytope.vec, VPolytope.unvec, Equiv.apply_symm_apply, Prod.mk.eta, hI]
  -- so its members are the stackings of the unstacked ones
  have h2 := VPolytope.vec_exact P.unvec
  rw [h] at h2
  rw [h2, Set.image_image]
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
