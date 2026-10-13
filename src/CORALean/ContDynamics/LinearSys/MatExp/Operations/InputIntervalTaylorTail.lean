module

public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Plus
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the input series past order two

`inputIntervalTaylorTail`: orders `3 … κ` of the input solution's series `Σ Aⁱ r^{i+1}/(i+1)!`
at an interval matrix `B` that holds `r A`, each order `Bⁱ r/(i+1)!` by ordinary interval
arithmetic: CORA's `iPow{i}*(r/factorial(i+1))` in `priv_highOrderMappingMatrix` of
`@linParamSys`, where `iPow{i}` is the `i`-th power of the system matrix times the step.
`expIntervalTaylorTail`'s recursion, with the input's coefficient; below order three there
are none.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Orders `3 … κ` of the input series at an interval matrix `B ∋ r A`, `Bⁱ r/(i+1)!` each.
Below order three there are none. -/
noncomputable def MatExp.inputIntervalTaylorTail (B : Interval (Mat ℝ n n)) (r : ℝ) :
    ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.point 0
  | 1 => Interval.point 0
  | 2 => Interval.point 0
  | k + 3 => Interval.plus
      (Interval.smul (r / (Nat.factorial (k + 4) : ℝ)) (Interval.matPow B (k + 3)))
      (MatExp.inputIntervalTaylorTail B r (k + 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
