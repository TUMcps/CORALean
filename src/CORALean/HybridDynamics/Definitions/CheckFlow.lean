module

public import CORALean.HybridDynamics.Operations.InputSet
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# `Location.checkFlow`: dropping the reach sets the flow does not carry to the guard

CORA's `checkFlow` keeps a reach set when the flow points toward the guard hyperplane
`{x | c·x = d}` (unit normal `c` out of the invariant). `flowUp` is the exact supremum, over the
set projected onto the hyperplane, of the component along `c` of the linear flow
`ẋ = A x + B u + c₀ + E w` (support functions of the set and of `inputSet = B U ⊕ c₀ ⊕ E W`).
Left out: the fast test, the `'pca'` reduction, the normal's orientation, the level-set guard and
the nonlinear flow. CORA adds the `n×1` vector `sys.c` to a scalar, so for `n > 1` its test is
a vector comparison (`references/coverage/hybridDynamics/location.md`, row `checkFlow`); here the
offset is part of `inputSet`.

## Inputs
* `ℓ` – location
* `c` – unit normal of the guard
* `d` – guard offset
* `R` – reach set, a zonotope

## Output
* largest flow component along the normal over the projected set
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar
open scoped CORALean.Real

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The supremum of the flow component `c·(A x + B u + c₀ + E w)` over the projection of `R` onto
`{x | c·x = d}`, the inputs `U` and the disturbances `W`. -/
noncomputable def Location.flowUp (ℓ : Location 𝒵 G L ℝ n)
    (c : Vec ℝ n) (d : ℝ) (R : Real.Zonotope (Vec ℝ n)) : ℝ :=
  let A : Mat ℝ n n := toRealMat ℓ.dynamics.A
  let P : Mat ℝ n n := 1 - vecMulVec c c                       -- the projector `I - c cᵀ`
  -- the flow of the projection `P x + d c`: the part through `x`, the offset, the inputs
  (R.supportBound (Real.HPolytope.rowLin (fun _ : Fin 1 => Pᵀ *ᵥ (Aᵀ *ᵥ c)) 0)).val
    + c ⬝ᵥ (A *ᵥ (d • c))
    + (ℓ.inputSet.supportBound (Real.HPolytope.rowLin (fun _ : Fin 1 => c) 0)).val

/-- The reach sets whose projection onto the hyperplane has outward flow somewhere. -/
noncomputable def Location.checkFlow (ℓ : Location 𝒵 G L ℝ n)
    (c : Vec ℝ n) (d : ℝ) (Rs : List (Real.Zonotope (Vec ℝ n))) :
    List (Real.Zonotope (Vec ℝ n)) :=
  open Classical in Rs.filter fun R => decide (0 < ℓ.flowUp c d R)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
