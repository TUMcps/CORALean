import CORALean.ContSet.ConPolyZono.Real.Theorems.RepresentsaPointSubset
import CORALean.ContSet.ConPolyZono.Float.Operations.RepresentsaPoint

/-!
# A float constrained polynomial zonotope without generators lies in its centre's box

The exact layer's `construct_subset_of_representsa_point` puts the nominal set in `{c}`; the
error box is added to every point, so the float set lies in `c` plus the error box. Not a
point unless that box is: the float statement is outer, never that the set is `{c}`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.construct_subset_of_representsa_point (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (h : cPZ.representsa_point = true) :
    cPZ.construct ⊆ {toRealVec cPZ.c} + cPZ.err.construct := by
  -- the nominal set has the same generator counts, so the exact layer's test passes on it
  have hN : InflatedContSet.nominalSet cPZ ⊆ {toRealVec cPZ.c} :=
    Real.ConPolyZono.construct_subset_of_representsa_point (InflatedContSet.nominal cPZ) h
  exact Set.add_subset_add_right hN

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
