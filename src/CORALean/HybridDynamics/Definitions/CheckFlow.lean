import CORALean.HybridDynamics.Definitions.Location
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.RowLin

/-!
# `Location.checkFlow`: dropping the reach sets the flow does not carry to the guard

CORA's `checkFlow` filters the reach sets meeting a guard hyperplane `{x | c·x = d}` of unit
normal `c` pointing out of the invariant: a set is kept if the flow points toward the guard. It
is projected onto the hyperplane (`x ↦ x - (c·x - d) c`) and the component along `c` of the
linear flow `ẋ = A x + u`, `u ∈ U`, is bounded over the projection. `flowUp` is that supremum,
exactly: the support functions of the set (through the projector `I - c cᵀ`) and of `U`.

Left out: the fast test (flow at the projection's centre, which `flowUp` already covers); the
`'pca'` box reduction before the supremum (an enclosure, so CORA's test only keeps more); the
orientation of the normal by the invariant (`aux_adaptGuard`), the caller's; the level-set guard
and the nonlinear flow, which evaluate Taylor models.

CORA's linear branch adds `sys.c`, an `n×1` vector, to the scalar flow component where `c*sys.c`
is meant, so for `n > 1` its test is a vector comparison (see FINDINGS.md). Here the offset is
part of `U`, and the component along `c` is taken of everything.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The supremum of the flow component `c·(A x + u)` over the projection of `R` onto
`{x | c·x = d}` and the inputs `U`. -/
noncomputable def Location.flowUp (ℓ : Location (fun n => Real.Zonotope (Vec ℝ n)) G L ℝ n)
    (c : Vec ℝ n) (d : ℝ) (R : Real.Zonotope (Vec ℝ n)) : ℝ :=
  let A : Mat ℝ n n := toRealMat ℓ.dynamics.A
  let P : Mat ℝ n n := 1 - vecMulVec c c                       -- the projector `I - c cᵀ`
  -- the flow of the projection `P x + d c`: the part through `x`, the offset, the inputs
  (R.supportBound (Real.HPolytope.rowLin (fun _ : Fin 1 => Pᵀ *ᵥ (Aᵀ *ᵥ c)) 0)).val
    + c ⬝ᵥ (A *ᵥ (d • c)) + (ℓ.U.supportBound (Real.HPolytope.rowLin (fun _ : Fin 1 => c) 0)).val

/-- The reach sets whose projection onto the hyperplane has outward flow somewhere. -/
noncomputable def Location.checkFlow (ℓ : Location (fun n => Real.Zonotope (Vec ℝ n)) G L ℝ n)
    (c : Vec ℝ n) (d : ℝ) (Rs : List (Real.Zonotope (Vec ℝ n))) :
    List (Real.Zonotope (Vec ℝ n)) :=
  open Classical in Rs.filter fun R => decide (0 < ℓ.flowUp c d R)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
