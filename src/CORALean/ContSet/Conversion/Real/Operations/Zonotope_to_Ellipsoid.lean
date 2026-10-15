module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# A zonotope as an ellipsoid

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `ellipsoid(fac*(G*G'), c)` with `fac` the generator count `h`, as the factor `√h G`. -/
noncomputable def Zonotope.ellipsoid (Z : Zonotope (Vec ℝ n)) : Ellipsoid n :=
  Ellipsoid.ofFactor (Matrix.of fun i j => Real.sqrt Z.h * Z.G j i) Z.c

/-- [1, Thm. 1]: `E(r E₀, z̄)` with `E₀ = F Fᵀ`, as the factor `√r F`. -/
noncomputable def Zonotope.ellipsoidNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (r : ℝ) :
    Ellipsoid n :=
  Ellipsoid.ofFactor (√r • F) Z.c

/-- [1, Thm. 3]: `E(l E₀, z̄)` with `E₀ = F Fᵀ`, as the factor `√l F`. -/
noncomputable def Zonotope.ellipsoidInnerNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (l : ℝ) :
    Ellipsoid n :=
  Ellipsoid.ofFactor (√l • F) Z.c

/-- [2, Sec. 4.1]: `E(n diag(β₁², …, β_n²), c)` with `βᵢ = ∑ⱼ |Gᵢⱼ|`, the box's ellipsoid, as the
factor `√n diag(β)`. -/
noncomputable def Zonotope.ellipsoidBox (Z : Zonotope (Vec ℝ n)) : Ellipsoid n :=
  Ellipsoid.ofFactor (Matrix.diagonal fun i => Real.sqrt n * ∑ j, |Z.G j i|) Z.c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
