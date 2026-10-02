import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.ContSet.Interval.Float.Theorems.OriginExact

/-!
# `VPolytope.enclosePoints` is exactly the convex hull of the points

The stored polytope is the convex hull of the points read as reals, with nothing added: the error
box is the origin, a singleton `{0}`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.enclosePoints_exact {N : ℕ} (pts : Mat 𝕋 n N) :
    (VPolytope.enclosePoints pts).construct =
      convexHull ℝ
        (Set.range fun l : Fin N => (fun i => toReal (pts i l) : Vec ℝ n)) := by -- --- PROOF ---
  -- the stored points as reals, with the origin box adding nothing
  show nominalSet (VPolytope.enclosePoints pts) + (VPolytope.enclosePoints pts).E.construct = _
  rw [show (VPolytope.enclosePoints pts).E.construct = {0} from Interval.origin_exact n]
  rw [Set.add_singleton, show (fun x : Vec ℝ n => x + 0) = id from funext fun x => add_zero x,
    Set.image_id]
  exact Real.VPolytope.construct_eq_convexHull _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
