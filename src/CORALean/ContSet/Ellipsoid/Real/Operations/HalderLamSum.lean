module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The weighted sum in Halder's iteration

The denominator `∑ᵢ λᵢ/(1 + β λᵢ)` of the fixed-point step [1, Eq. 26], the other side of
the rewriting of [1, Eq. 18] as `β² ∑ λᵢ/(1+βλᵢ) = ∑ 1/(1+βλᵢ)`.

## Inputs
* `lam` – eigenvalues
* `β` – positive weight

## Output
* `∑ λᵢ / (1 + β λᵢ)`

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

/-- `∑ᵢ λᵢ / (1 + β λᵢ)`, the denominator under the root of [1, Eq. 26]. -/
noncomputable def Ellipsoid.halderLamSum (lam : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, lam i / (1 + β * lam i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
