module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `Zonotope.volume`

CORA's `@zonotope/volume_` at the default method `'exact'` (after Grover et al., "Determinants
and the volumes of parallelotopes and zonotopes", 2010): the zonotope tiles into the
parallelotopes the `n`-subsets of its generators span, so the volume is `2^n Σ_S |det G_S|`. CORA
returns `0` first when there are fewer than `n` generators or `rank G < n`, which the sum gives
anyway (no subset, or every subset's determinant vanishes), so no case split is written. The
approximations `'reduce'` and `'alamo'` are not modelled.

The same sum is [1, Eq. 45], the size `µ` of a zonotope that `Zonotope.mspb` minimises.

## Inputs
* `Z` – zonotope

## Output
* exact volume of `Z`

## References

* [1] [M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on Automatic
      Control, 2016.](../../../../../../references/2016/maiga-tac-hybrid-reachability.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/volume_` (`'exact'`): `2^n` times the sum of `|det|` of every selection of `n`
generators, as the columns of an `n × n` matrix in the order of their indices. -/
noncomputable def Zonotope.volume (Z : Zonotope (Vec ℝ n)) : ENNReal :=
  ENNReal.ofReal (2 ^ n * ∑ S : Finset (Fin Z.h),
    if hS : S.card = n then
      |(Matrix.of fun i k => Z.G (S.orderEmbOfFin hS k) i : Mat ℝ n n).det|
    else 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
