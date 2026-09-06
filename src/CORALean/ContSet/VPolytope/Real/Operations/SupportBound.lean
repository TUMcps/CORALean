import CORALean.ContSet.VPolytope.Real.Operations.LeOfForallLe
import CORALean.Global.LinProg.API

/-!
# A vertex description answers a linear program without solving one

The maximum over a finite vertex list is the support value, attained rather
than merely approached. This is the reason the two representations are kept
apart, and the reason the conversion between them is cheap in exactly one
direction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Noncomputable only in the supremum: over a finite vertex list the value is a
maximum, and the float layer computes it as one. -/
noncomputable def VPolytope.supportBound (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) :
    SupportBound P.construct c where
  val := ⨆ l, c (P.V l)
  -- the function spelt out: `le_ciSup` cannot guess it from the goal
  le _ hx := P.le_of_forall_le c
    (fun l => le_ciSup (f := fun l => c (P.V l)) (Set.finite_range _).bddAbove l) hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
