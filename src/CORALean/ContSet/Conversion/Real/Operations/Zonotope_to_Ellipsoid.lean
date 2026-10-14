module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# A zonotope as an ellipsoid — the construction

`Zonotope.ellipsoid`, `Zonotope.ellipsoidNorm`, `Zonotope.ellipsoidInnerNorm` and
`Zonotope.ellipsoidBox` are the constructions; `Zonotope_to_Ellipsoid` states and proves what they
guarantee.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.ellipsoid (Z : Zonotope (Vec ℝ n)) : Ellipsoid n where
  k := Z.h
  c := Z.c
  G := Matrix.of fun i j => Real.sqrt Z.h * Z.G j i

/-- [1, Thm. 1]: `E(r E₀, z̄)` with `E₀ = F Fᵀ`, as the generator `√r F`. -/
noncomputable def Zonotope.ellipsoidNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (r : ℝ) :
    Ellipsoid n where
  k := n
  c := Z.c
  G := √r • F

/-- [1, Thm. 3]: `E(l E₀, z̄)` with `E₀ = F Fᵀ`, as the generator `√l F`. -/
noncomputable def Zonotope.ellipsoidInnerNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (l : ℝ) :
    Ellipsoid n where
  k := n
  c := Z.c
  G := √l • F

/-- [2, Sec. 4.1]: `E(n diag(β₁², …, β_n²), c)` with `βᵢ = ∑ⱼ |Gᵢⱼ|`, the box's ellipsoid. -/
noncomputable def Zonotope.ellipsoidBox (Z : Zonotope (Vec ℝ n)) : Ellipsoid n where
  k := n
  c := Z.c
  G := Matrix.diagonal fun i => Real.sqrt n * ∑ j, |Z.G j i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
