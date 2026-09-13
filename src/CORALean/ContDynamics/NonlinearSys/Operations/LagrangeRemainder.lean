import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The cubic remainder of a second-order expansion

CORA's `priv_lagrangeRemainder`, [1, Sec. 4.1]: the box `[-l, l]` with
`lᵢ = (1/6) Σⱼ γⱼ (γᵀ Eᵢⱼ γ)`, where `γ` bounds `|z - z✱|` over the set the step
runs on and `Eᵢⱼ` bounds the third derivative of coordinate `i` — differentiated
once more in the direction the outer index `j` names — entrywise.

`γ` is read off the same zonotope `abstrErrLin` reads it from: the region a
step's quadratic expansion is trusted on is the region its linear one is. `E`
is data, as `abstrErrLin`'s `H` is: nothing here differentiates `f`, and a wrong
`E` yields a box `PolyAbstractionError.of_lagrange` cannot certify rather than
an unsound one.

The three-index family is `Fin n → Fin d → Mat ℝ d d` rather than a rank-three
array of its own: `CORALean.Tensor` is not indexed by an operation family, and
this is the shape `abstrErrLin`'s two-index `H` already fixed, extended by one.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


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
