module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The cubic remainder of a second-order expansion

CORA's `priv_lagrangeRemainder`, [1, Sec. 4.1]: the box `[-l, l]` with
`lᵢ = (1/6) Σⱼ γⱼ (γᵀ Eᵢⱼ γ)`, where `γ` bounds `|z - z✱|` over the set the step runs on and
`Eᵢⱼ` bounds the third derivative of coordinate `i` entrywise. `γ` is read off the zonotope
`abstrErrLin` reads it from. `E` is data, as `abstrErrLin`'s `H` is: nothing here
differentiates `f`, and a wrong `E` yields a box `IsPolyAbstractionError.of_lagrange` cannot
certify rather than an unsound one. The family is `Fin n → Fin d → Mat ℝ d d`.

## Inputs
* `E` – third-derivative bounds
* `Z` – zonotope of states and inputs
* `zs` – expansion point

## Output
* the symmetric box bounding the cubic remainder

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control, 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {d n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The symmetric box `[-l, l]` bounding a third-order remainder over `Z`, at
the expansion point `zs` and the entrywise third-derivative bound `E`. -/
noncomputable def lagrangeRemainder (E : Fin n → Fin d → Mat ℝ d d) (Z : Real.Zonotope (Vec ℝ d))
    (zs : Vec ℝ d) : Real.Interval (Vec ℝ n) :=
  let γ : Vec ℝ d := fun j => |Z.c j - zs j| + ∑ k, |Z.G k j|
  let l : Vec ℝ n := fun i => (∑ j, γ j * (γ ⬝ᵥ (E i j *ᵥ γ))) / 6
  ⟨-l, l⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
