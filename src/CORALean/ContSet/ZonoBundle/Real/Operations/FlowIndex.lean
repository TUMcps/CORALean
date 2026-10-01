import CORALean.Global.Tensor
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange

/-!
# `ZonoBundle.flowIndex`: the axis most aligned with the flow

Which column of `Λ = I` the flow method of [1, Heuristic flow] replaces: the one "most aligned with
the flow direction `f`". The columns are the unit vectors, whose alignment with `f` is `|fᵢ|`
up to the common factor `‖f‖⁻¹`, so it is the first index of largest `|fᵢ|`. A list `argmax`, so it
runs; `none` only for no axes at all.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first axis `i` of largest `|f i|`, the column [1, Heuristic flow] replaces by `f`. -/
noncomputable def ZonoBundle.flowIndex (f : Vec ℝ n) : Option (Fin n) :=
  (List.finRange n).argmax fun i => |f i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
