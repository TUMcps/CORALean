module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderInvSum
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLamSum
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Halder's fixed-point step

The iteration [1, Eq. 26]

  `β ↦ g(β) = ( ∑ 1/(1+βλᵢ) / ∑ λᵢ/(1+βλᵢ) )^(1/2)`

is what CORA's `priv_plusEllipsoidOA_halder` runs, from `β = 0.5`, until two iterates
agree within the tolerance. That loop is not a function of the data, so what is defined
here is the step; `halderStep_iterate_tendsto` is what the loop converges to.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of [1, Eq. 26]. -/
noncomputable def Ellipsoid.halderStep (lam : ι → ℝ) (β : ℝ) : ℝ :=
  Real.sqrt (Ellipsoid.halderInvSum lam β / Ellipsoid.halderLamSum lam β)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
