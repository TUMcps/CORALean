module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.sortByLength`

The sorted generator matrix `G_s` of [1, Sec. III-B, Step 1) and Sec. III-C, Step 1)]: the
generators of `Z` in order of decreasing 2-norm, `‖g_{s,i}‖₂ ≥ ‖g_{s,i+1}‖₂`. The center is kept.

## Inputs
* `Z` – zonotope

## Output
* zonotope with generators sorted by decreasing length

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z` with its generators sorted by decreasing 2-norm, ties as `Tuple.sort` breaks them. -/
noncomputable def Zonotope.sortByLength (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  ⟨Z.h, Z.c, Z.G ∘ Tuple.sort fun j => -Z.generatorLength j⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
