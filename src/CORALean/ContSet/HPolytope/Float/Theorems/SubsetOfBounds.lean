module

public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff

@[expose] public section

/-!
# A set lies in the polytope of its float row bounds

The rounding was paid where each bound was combined, and nothing rounds here.

## Inputs
* `Aq` – float row matrix

## Hypotheses
* `u` – float bounds of the set at the rows

## Conclusion
* the set is contained in the constructed polytope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ} {S : Set (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rounding has already been paid where each bound was combined, and nothing
rounds here. -/
theorem HPolytope.subset_ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S
    (Real.HPolytope.rowLin (toRealMat Aq) i)) :
    S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => (u i).le x hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
