import CORALean.Global.EuclideanNorm

/-!
# The foot of the perpendicular lies on the hyperplane

`c ⬝ (x - (c ⬝ x - d) c) = c ⬝ x - (c ⬝ x - d) (c ⬝ c) = d` for the unit normal `c`: the points
`projectOnHyperplane_outer` encloses are on `{y | c ⬝ y = d}`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
