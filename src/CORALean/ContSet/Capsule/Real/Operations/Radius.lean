import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.radius`

CORA's `@capsule/radius.m`: the length of the generator plus the radius of the ball,
`norm(g, 2) + r`. That is the radius of the smallest Euclidean ball about the centre
holding the capsule: the far end of the segment is at distance `‖g‖₂`, and the ball reaches `r`
further.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `norm(g, 2) + r`, the Euclidean norm written out as `Real.sqrt`, as `Capsule.construct`
does. -/
noncomputable def Capsule.radius (C : Capsule n) : ℝ := Real.sqrt (∑ i, C.g i ^ 2) + C.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
