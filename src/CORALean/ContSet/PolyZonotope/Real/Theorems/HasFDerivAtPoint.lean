module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.DifferentiablePoint
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Theorems.JacobianHasDerivAt
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# The derivative of the point map is the Jacobian matrix

Column `k` of the Fréchet derivative is its value on the `k`-th unit vector, which is the
derivative along `Function.update a k` (the chain rule) and so, by `jacobian_hasDerivAt`, the
point of `jacobian k`.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the point map has the Jacobian matrix as derivative
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The derivative of the point map is the matrix of the derivatives along the factors. -/
theorem PolyZonotope.hasFDerivAt_point (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    HasFDerivAt pZ.point
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (pZ.jacobianMat a))) a := by -- --- PROOF ---
  have hd : HasFDerivAt pZ.point (fderiv ℝ pZ.point a) a :=
    (PolyZonotope.differentiable_point pZ a).hasFDerivAt
  -- each column: the chain rule along `update a k`, against `jacobian_hasDerivAt`
  have hcol : ∀ k : Fin pZ.p,
      fderiv ℝ pZ.point a (Pi.single k 1) = fun i => pZ.jacobianMat a i k := by
    intro k
    have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (a k) hd (hasDerivAt_update a k (a k))
      (Function.update_eq_self k a).symm
    have h2 := PolyZonotope.jacobian_hasDerivAt pZ k a
    have h3 : (pZ.point ∘ Function.update a k) = fun t => pZ.point (Function.update a k t) :=
      rfl
    rw [h3] at h1
    exact h1.unique h2
  -- the two linear maps agree on the unit vectors, so everywhere
  convert hd using 1
  ext v : 1
  conv_rhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  simp only [map_smul]
  ext i
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  -- the unit vector written both ways
  have hsingle : ∀ x : Fin pZ.p, (fun j => if x = j then (1 : ℝ) else 0) = Pi.single x 1 := by
    intro x
    ext j
    simp [Pi.single_apply, eq_comm]
  simp only [hsingle, hcol]
  simp [Matrix.mulVec, dotProduct, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
