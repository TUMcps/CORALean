import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# A box as a constrained zonotope

Through the zonotope, which loses nothing either time: a box is a zonotope with
axis-aligned generators, and a zonotope is a constrained one with nothing to
satisfy.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.conZonotope (I : Interval (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  I.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.subset_conZonotope (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.conZonotope.construct :=
  subset_trans I.subset_zonotope (Zonotope.conZonotope_exact _).subset


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
