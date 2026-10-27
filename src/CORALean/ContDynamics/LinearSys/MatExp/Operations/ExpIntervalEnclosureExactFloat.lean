module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorExactFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

@[expose] public section

/-!
# Interval matrices: the exponential enclosed with an exact second order, in floats

`expIntervalEnclosure`'s sharper sibling, `Real.MatExp.expIntervalEnclosureExact` rounded:
`⌈e^{At}_κ⌉` of [1, Thm. 1] is the truncation `expIntervalTaylorExact` widened by `E(t)`,
the tail bound taken at `normUpperBound` of `[t] A` as `expIntervalEnclosure` takes it. Widened
outward, `inf` down and `sup` up.

## Inputs
* `A` – float interval matrix
* `t` – float time
* `κ` – Taylor order

## Output
* float interval matrix enclosing the exponential with an exact second order

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⌈e^{At}_κ⌉` of [1, Thm. 1]: that truncation widened by `E(t)`. -/
def MatExp.expIntervalEnclosureExact (A : Interval (Mat 𝕋 n n)) (t : 𝕋) (κ : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let T := MatExp.expIntervalTaylorExact A t κ                      -- the truncation
  let E := MatExp.expRemainderBound
    (MatExp.normUpperBound (Interval.smul t t A)) κ                 -- its tail, entrywise
  ⟨fun i j => subDown (T.inf i j) E, fun i j => addUp (T.sup i j) E⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
