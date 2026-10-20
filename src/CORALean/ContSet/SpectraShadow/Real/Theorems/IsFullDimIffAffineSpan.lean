module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

/-!
# A spectrahedral shadow is full-dimensional iff its affine hull is everything

A shadow is convex, so it has an interior point exactly when its affine hull is the whole space
(`ContSet.IsFullDim` read at `construct`).

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* A spectrahedral shadow is full-dimensional iff its affine hull is everything
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.isFullDim_iff_affineSpan (S : SpectraShadow (Vec ℝ n)) :
    (interior S.construct).Nonempty ↔ affineSpan ℝ S.construct = ⊤ :=
  (SpectraShadow.convex_construct S).interior_nonempty_iff_affineSpan_eq_top

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
