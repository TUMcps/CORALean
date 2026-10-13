module

public import CORALean.ContSet.Interval.Float.Operations.Infimum
public import CORALean.ContSet.Interval.Real.Theorems.InfimumMemConstruct

@[expose] public section

/-!
# The infimum of a nonempty interval lies in it

Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.infimum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.infimum ∈ I.construct :=
  Real.Interval.infimum_mem_construct I.nominal h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
