module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeSubsetNominalConZonotopeOf
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalSubsetNominalZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar

The rows are carried onto the coefficients by composing with the generators,
which is a matrix product and so rounds. That is the difficulty this pair has
and the others do not: a rounded product does not merely shift a bound, it says
something *different* about the coefficients, and a constraint that says
something different can cut off points the original kept.

So the composed rows are stored rounded down and the bounds are widened by what
the rounding can reach — `matMulDiff` records the gap entrywise, and `radius`
sums it over a row, which is the most a coefficient vector in the unit box can
turn that gap into. Both ends of an equality row move outward, which is what its
interval right-hand side is for.

Stated for any zonotope containing the polytope, since nothing depends on it
being the box; `conZonotope` uses the box because that is what the certificates
already give.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.conZonotope_contains {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conZonotope up lo).construct := by -- --- PROOF ---
  intro x hx
  refine ⟨x, P.subset_nominal_conZonotopeOf _ (fun y hy =>
    Interval.subset_nominal_zonotope _ (HPolytope.interval_contains up lo hy)) hx,
    0, fun i => ?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  · show x + 0 = x
    rw [add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
