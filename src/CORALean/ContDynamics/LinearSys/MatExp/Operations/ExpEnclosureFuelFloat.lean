module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat

@[expose] public section

/-!
# `MatExp.expEnclosureFuel`, how far past the Taylor order the exponential is enclosed

`expEnclosureFuel`: the number of orders `admissibleOrder` tries, from the Taylor order of a step,
before it gives up and the step has no enclosure of `e^{|A|Δt}` for the remainder of [1]. A step
with `‖AΔt‖` beyond `(η + 2 + expEnclosureFuel) / 2` has none.

## Inputs
* none

## Output
* number of orders tried

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The number of orders tried, from the Taylor order. -/
def MatExp.expEnclosureFuel : ℕ := 4096

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
