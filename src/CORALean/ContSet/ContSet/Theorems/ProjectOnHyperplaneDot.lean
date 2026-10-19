module

public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The foot of the perpendicular lies on the hyperplane

`c ⬝ (x - (c ⬝ x - d) c) = c ⬝ x - (c ⬝ x - d) (c ⬝ c) = d` for the unit normal `c`: the points
`projectOnHyperplane_outer` encloses are on `{y | c ⬝ y = d}`.

## Inputs
* `c` – unit normal
* `x` – point
* `d` – hyperplane offset

## Hypotheses
* `hc` – `‖c‖₂ = 1`

## Conclusion
* the projected point satisfies `c ⬝ x = d`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The foot of the perpendicular lies on the hyperplane when the normal has unit length. -/
theorem ContSet.projectOnHyperplane_dot (c x : Vec ℝ n) (d : ℝ) (hc : ‖c‖₂ = 1) :
    c ⬝ᵥ (x - (c ⬝ᵥ x - d) • c) = d := by
  have h : c ⬝ᵥ c = 1 := by rw [dotProduct_self, hc]; norm_num
  rw [dotProduct_sub, dotProduct_smul, h]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
