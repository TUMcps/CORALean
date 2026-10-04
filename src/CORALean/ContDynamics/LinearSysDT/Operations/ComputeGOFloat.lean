import CORALean.ContDynamics.LinearSysDT.Definitions.GOFloat
import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGO
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContDynamics.OutputEq.OutputEq

/-!
# `LinearSysDT.computeGOFloat`

CORA's `linearSysDT/computeGO` [1] with the parameters as interval matrices over `𝕋`: the powers
of the stored `A` are `Interval.matPow` of its point box, the products with the stored `C` one
`Interval.matMul` each, so every entry is rounded outward. The same time-invariant branch as
`computeGO`; soundness is `computeGOFloat_outer`.

## References

* [1] `contDynamics/@linearSysDT/computeGO.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {n r : ℕ} {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters for `nk` steps, as interval matrices enclosing `computeGO`'s. -/
def LinearSysDT.computeGOFloat (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) (nk : ℕ) :
    LinearSysDT.GOFloat 𝕋 n r nk where
  A k := (Interval.point sys.A).matPow (k.val + 1)
  B k j := if j.val ≤ k.val then (Interval.point sys.A).matPow (k.val - j.val)
    else Interval.point fun _ _ => zero
  C k := Interval.matMul (Interval.point out.C) ((Interval.point sys.A).matPow k.val)
  D k j :=
    if j = k then Interval.point out.D
    else if j.val < k.val then
      Interval.matMul (Interval.point out.C) ((Interval.point sys.A).matPow (k.val - 1 - j.val))
    else Interval.point fun _ _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
