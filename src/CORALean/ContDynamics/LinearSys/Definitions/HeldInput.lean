module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A piecewise-constant input

The input [1, Sec. 4.2] simulates with: `v j` held over the `j`-th step
`(t_j, t_{j+1}]`, `t_j = j Δt`, read off as `v (⌈s / Δt⌉₊ - 1)`. The left
endpoint belongs to the step before, which is the half-open interval
`intervalIntegral` integrates over, so a step's integral sees `v j` everywhere
and no null set has to be argued away. `t = 0` reads `v 0`.

## Inputs
* `Δt` – step length
* `v` – input value per step
* `s` – time

## Output
* input value held at the given time

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `v j` held over the step `(j Δt, (j + 1) Δt]`: [1, Sec. 4.2]'s piecewise-constant input. -/
noncomputable def LinearSys.heldInput (Δt : ℝ) (v : ℕ → Vec ℝ n) (s : ℝ) : Vec ℝ n :=
  v (⌈s / Δt⌉₊ - 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
