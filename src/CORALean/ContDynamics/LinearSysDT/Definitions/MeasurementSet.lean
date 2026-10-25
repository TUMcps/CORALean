module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The measurement state set

[1, Def. 2]: the states consistent with the output `y = C x + F υ` [1, Eq. 4], `υ` in the unit
box `V = ⟨0, I⟩`. Printed as `{x | |C x - y| ≤ F}`, which compares a vector with the matrix
`F`; read as `C x - y ∈ F Bⁿᵛ`, the form the proof of [1, Thm. 1] uses (`C x₊ - y₊ = F α`,
`α ∈ Bⁿᵛ`, its Eq. 8). For a diagonal `F` the two agree.

## Inputs
* `C` – output matrix
* `F` – noise matrix
* `y` – measurement

## Output
* the states consistent with the measurement

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{x | C x - y ∈ F Bⁿᵛ}`. -/
def LinearSysDT.measurementSet (C : Mat ℝ ny n) (F : Mat ℝ ny nv) (y : Vec ℝ ny) :
    Set (Vec ℝ n) :=
  {x | ∃ α : Vec ℝ nv, (∀ i, |α i| ≤ 1) ∧ C *ᵥ x - y = F *ᵥ α}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
