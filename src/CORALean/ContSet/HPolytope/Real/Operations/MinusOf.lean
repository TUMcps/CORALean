import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.Global.LinProg.API

/-!
# `HPolytope.minusOf`

The halfspace analogue of `Minus`. No instance: the subtrahend is a plain
`Set α`, and its per-row support bounds are data the representation cannot
compute, taken in exactly as `mtimesOf` takes what it cannot compute either —
#49 already records that `HPolytope` instantiates almost nothing, and this is
not the issue that fixes that.

Each inequality row shifts inward by the subtrahend's support in that row's
own direction; the equality rows are copied unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.minusOf (P : HPolytope α) (T : Set α) (u : ∀ i, SupportBound T (P.A i)) :
    HPolytope α where
  m := P.m; A := P.A; b := fun i => P.b i - (u i).val
  me := P.me; Ae := P.Ae; be := P.be

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
