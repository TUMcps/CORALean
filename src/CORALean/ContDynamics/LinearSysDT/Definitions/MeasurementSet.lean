import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The measurement state set

[1, Def. 2]: the states consistent with the output `y = C x + F υ` [1, Eq. 4], `υ` in the unit
box `V = ⟨0, I⟩`. Printed as `{x | |C x - y| ≤ F}`, which compares a vector with the matrix
`F`; read as `C x - y ∈ F Bⁿᵛ`, the form the proof of [1, Thm. 1] uses (`C x₊ - y₊ = F α`,
`α ∈ Bⁿᵛ`, its Eq. 8). For a diagonal `F` the two agree.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
