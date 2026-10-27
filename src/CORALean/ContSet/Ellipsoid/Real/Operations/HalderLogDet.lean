module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The volume criterion of the outer ellipsoid, in eigen-coordinates

For `Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂` the objective of [1, Eq. 14] is `log det Q(β)`. In
the eigenvalues `λᵢ` of `Q₁⁻¹ Q₂` it is `log det Q₁ + ∑ᵢ log((1 + 1/β) + (1 + β) λᵢ)`
(`log_det_halder_eq`), and `halderLogDet` is the sum, the part that depends on `β`.

## Inputs
* `lam` – eigenvalues
* `β` – positive weight

## Output
* the sum over eigenvalues of `log((1 + 1/β) + (1 + β) λᵢ)`

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑ᵢ log((1 + 1/β) + (1 + β) λᵢ)`: `log det Q(β)` less the constant `log det Q₁`. -/
noncomputable def Ellipsoid.halderLogDet (lam : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.log ((1 + 1 / β) + (1 + β) * lam i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
