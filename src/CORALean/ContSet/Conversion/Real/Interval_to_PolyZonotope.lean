import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# A box as a polynomial zonotope

The box's zonotope, then that zonotope's factors: one dependent factor per
coordinate and no independent generators. Nothing is lost by either step, but
only the enclosing direction is stated, since `Interval.zonotope` states only
that — a box whose `sup` falls below its `inf` denotes nothing while the
zonotope built from it does not.

This is how a reachability run starts from a box without leaving the
representation it will stay in.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Interval.polyZonotope (I : Interval (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  I.zonotope.polyZonotope

theorem Interval.subset_polyZonotope (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.polyZonotope.construct :=
  subset_trans I.subset_zonotope (Zonotope.polyZonotope_exact _).subset

end CORALean.Real
