import CORALean.ContSet.Interval.Float.Operations.Uplus

/-!
# `Interval.uplus` is the identity

The set is unchanged, definitionally.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.uplus_exact {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : I.uplus.construct = I.construct := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
