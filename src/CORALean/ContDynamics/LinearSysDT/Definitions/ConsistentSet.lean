module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The states consistent with one measurement

[1, Def. 1]: `X_y = {x | y - C x ∈ V}`, every state the output `y = C x + v` with `v ∈ V` can
have come from. No representation: `V` is any set, and so is the result.

## Inputs
* `C` – output matrix
* `V` – noise set
* `y` – measurement

## Output
* the states consistent with the measurement

## References

* [1] [V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica,
      2013.](../../../../../references/2013/le-automatica-zonotopic-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X_y = {x | y - C x ∈ V}`. -/
def LinearSysDT.consistentSet (C : Mat ℝ p n) (V : Set (Vec ℝ p)) (y : Vec ℝ p) :
    Set (Vec ℝ n) :=
  {x | y - C *ᵥ x ∈ V}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
