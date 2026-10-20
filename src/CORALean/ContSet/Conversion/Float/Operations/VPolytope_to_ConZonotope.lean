module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# A hull as a constrained zonotope, over a floating-point scalar

## Inputs
* `𝕋` – scalar type
* `k` – number of vertices

## Output
* halfspace polytope of the standard simplex
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Nonnegative, summing to one. -/
def VPolytope.simplex (𝕋 : Type) [FloatOps 𝕋] (k : ℕ) : HPolytope 𝕋 (Vec 𝕋 k) :=
  (HPolytope.ineqs (negIdentityMat 𝕋 k) fun _ => zero).stackRows
    (HPolytope.eqs (fun (_ : Fin 1) (_ : Fin k) => one) fun _ => one)

-- the vertices become the generators and the simplex their coefficient domain
def VPolytope.conZonotope (P : VPolytope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := P.k
  c := fun _ => zero
  G := P.V
  P := VPolytope.simplex 𝕋 P.k
  I_error := P.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
