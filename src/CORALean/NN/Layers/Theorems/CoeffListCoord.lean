module

public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# One coordinate of a layer's coefficient list

Coordinate `i` of the list, read as reals, is neuron `i`'s own coefficients: what makes one
evaluation carry `n` different polynomials, and what the enclosure states its exact side against.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LayerRelaxation.coeffList_coord (P : LayerRelaxation 𝕋 n m) (I : Interval (Vec 𝕋 n))
    (i : Fin n) : ((P.coeffList I).map fun v => toReal (v i))
      = List.ofFn fun k => toReal ((P i).coeffs (I.inf i) (I.sup i) k) := by
  rw [LayerRelaxation.coeffList, List.map_ofFn]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
