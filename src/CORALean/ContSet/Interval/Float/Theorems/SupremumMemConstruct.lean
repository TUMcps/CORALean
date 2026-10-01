import CORALean.ContSet.Interval.Float.Operations.Supremum
import CORALean.ContSet.Interval.Real.Theorems.SupremumMemConstruct

/-!
# The supremum of a nonempty interval lies in it

Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.supremum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.supremum ∈ I.construct :=
  Real.Interval.supremum_mem_construct I.nominal h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
