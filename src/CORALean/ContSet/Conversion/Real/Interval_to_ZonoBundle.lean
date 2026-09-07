import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A box as a bundle of one

Through the box's own zonotope, then `Zonotope.zonoBundle` — the single-member
bundle, exact by `Set.iInter_const`. All the loss is the box-to-zonotope step's,
so this is no worse than `Interval → Zonotope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.zonoBundle (I : Interval (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  I.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zonoBundle_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.zonoBundle.construct :=
  subset_trans I.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
