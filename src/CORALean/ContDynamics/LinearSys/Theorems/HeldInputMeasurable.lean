module

public import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-!
# A held input is measurable

`heldInput Δt v` reads `v` at `⌈s / Δt⌉₊ - 1`, a measurable function into `ℕ`,
whose every function out of is measurable: the admissibility a Carathéodory
`Trajectory` asks of its input, for the piecewise-constant inputs of
[1, Sec. 4.2] whatever the values held.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: a piecewise-constant input is measurable, whatever it holds. -/
theorem LinearSys.heldInput_measurable (Δt : ℝ) (v : ℕ → Vec ℝ n) :
    Measurable (LinearSys.heldInput Δt v) :=
  (measurable_from_nat (f := fun m : ℕ => v (m - 1))).comp
    (Nat.measurable_ceil.comp (measurable_id.div_const Δt))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
