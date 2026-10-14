module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesBox
public import CORALean.ContSet.Zonotope.Float.Operations.PlusBox
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# What a float run of `reach` owes

The float counterpart of `reachError`, and a strictly bigger obligation: at
`Zonotope (Vec 𝕋 n)` none of `plus`, `mtimes` or `reduce` is exact — `SoundFloatArithmetic`
constrains each outward only — so a step loses ground at every operation, not
only at `reduce`, and this recursion carries a box per operation.

`mtimesBox`, `plusBox` and `reduceGirardBox` bound how far a float result
reaches beyond the exact operation on its operand, computed entirely in `𝕋`
from the *same* float values `reach` produces that step, and read back into
this real accumulator by `.nominal`, the same conversion the box's own
`construct` already goes through. `U.E.nominal.zonotope` has no `reachError`
counterpart: `plusBox` bounds `(M.plus U).construct` against `U`'s *float*
construct while `reachSet` advances by its *nominal* construct alone.

At `k = 0` the error is `R₀`'s own error box, read back as a zonotope.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float InflatedContSet

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What a float run of `reach` owes after `k` steps: `mtimes`, `plus` and
`reduce` each pay a box beyond their operand's exact operation, and the
previous step's error carries through this step's `A`. -/
noncomputable def LinearSysDT.reachErrorFloat (sys : LinearSysDT 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) ℕ)
    (options : LinearSysDT.ReachOptions) : Real.Zonotope (Vec ℝ n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec E : ℕ → Real.Zonotope (Vec ℝ n)  -- E_k
    | 0 => R₀.I_error.nominal.zonotope
    | k + 1 =>
      let Rk := sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ options
      let M := Zonotope.mtimes sys.A Rk
      let W := M.plus U
      (Real.Zonotope.mtimes (Scalar.toRealMat sys.A) (E k)).plus
        ((Zonotope.mtimesBox sys.A Rk).nominal.zonotope.plus
          ((Zonotope.plusBox M U).nominal.zonotope.plus
            ((nominal (Zonotope.reduceGirardBox W o)).plus U.I_error.nominal.zonotope)))
  E N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
