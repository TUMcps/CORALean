module

public import CORALean.ContSet.HPolytope.Real.Operations.BilliardEnd

@[expose] public section

/-!
# `HPolytope.billiardStep`

`[1, Alg., steps 2-5]`: one step of the Billiard Walk from `x`. The randomness is an input: `η`
is the uniform number of step 2 and `ξ` the Gaussian vector of step 3, so `ℓ = -τ log η` and
`d = ξ / ‖ξ‖`. `none` is step 4's "go to step 2", the caller drawing a fresh pair `(η, ξ)`; the
loop of steps 2-4 is that retry, left to the caller because Lean has no random draw to retry
with. `‖·‖` is the Euclidean norm of the inner product space, as the paper's unit sphere is.

## Inputs
* `P` – H-polytope
* `R` – natural number
* `τ` – real number
* `x` – point
* `η` – real number
* `ξ` – space

## Output
* the next point of the Billiard Walk from `x`, given `R`, `τ` and the draws `η`, `ξ`

## References

* [1] [B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes,
      2014.](../../../../../../references/2014/polyak-ifac-billiard-walk.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The next point of the Billiard Walk from `x`, given `R`, `τ` and the draws `η`, `ξ`. -/
noncomputable def HPolytope.billiardStep (P : HPolytope E) (R : ℕ) (τ : ℝ) (x : E) (η : ℝ)
    (ξ : E) : Option E :=
  -- step 2: the length of the trajectory
  let ℓ : ℝ := -τ * Real.log η
  -- step 3: a direction uniform on the unit sphere
  let d : E := ‖ξ‖⁻¹ • ξ
  -- steps 4-5: the end of the trajectory is the next point
  P.billiardEnd R x d ℓ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
