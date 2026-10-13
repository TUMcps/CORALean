import CORALean.ContDynamics.Reach.Operations.Check
import CORALean.ContDynamics.Reach.Operations.Steps

/-!
# What every `Reach` instance computes

`Check`: a specification checked on what `reach` returns, `false` where it
returned `none`. `Steps`: the step count `(tFinal - tStart) / Δt`, kept
only if it is exactly a natural number.
-/
