import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

/-!
# A box as a constrained polynomial zonotope

Through `Interval.subset_polyZonotope`, then `PolyZonotope.conPolyZono` — an
empty constraint system, so that second leg adds nothing and is exact. All the
loss is the first hop's, and nothing is lost there either: only the enclosing
direction is stated for a box's own polynomial zonotope, not the equality the
underlying sets in fact have, so only a subset survives the composition.

This is how a reachability run can start from a box directly in the
representation a constrained operation will need.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.conPolyZono (I : Interval (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  I.polyZonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.subset_conPolyZono (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.conPolyZono.construct :=
  subset_trans I.subset_polyZonotope (PolyZonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
