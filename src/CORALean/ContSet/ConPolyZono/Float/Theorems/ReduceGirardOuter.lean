import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceByOuter

/-!
# Girard's reduction encloses

Two cases: below the order there is nothing to do, and above it the rule is a
pair of partitions like any other. The metric never appears, which is what lets
`sortPerm`'s unconstrained comparator rank a float.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) :
    cPZ.construct ⊆ (cPZ.reduceGirard o).construct := by
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact ConPolyZono.reduceBy_outer cPZ _ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
