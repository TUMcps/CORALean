module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A box as a constrained zonotope

Through the zonotope, which loses nothing either time: a box is a zonotope with
axis-aligned generators, and a zonotope is a constrained one with nothing to
satisfy.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.conZonotope (I : Interval (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  I.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.conZonotope_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.conZonotope.construct :=
  subset_trans I.zonotope_contains (Zonotope.conZonotope_exact _).subset


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
