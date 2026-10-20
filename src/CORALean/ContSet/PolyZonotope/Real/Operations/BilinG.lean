module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The generators of `bilin`

Generator `(i, j)` is `f` at the two extended generators. Every product of two polynomial
zonotopes over shared factors differs only here: `mulG` is the entrywise product, the
uncertain-structure graph layer is matrix multiplication, and both are bilinear, so both are
this definition at a different `f`. `f` is a `→ₗ →ₗ` and not a function with two hypotheses,
because bilinearity is what makes the pairing distribute over the two sums that a point of
each set is; nothing else about `f` is ever used.

## Inputs
* `f` – bilinear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Output
* generators of the bilinear image
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the pairing: `f` at the two extended generators. -/
def PolyZonotope.bilinG (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → γ :=
  fun l => f (PolyZonotope.extG pZ₁ (finProdFinEquiv.symm l).1)
      (PolyZonotope.extG pZ₂ (finProdFinEquiv.symm l).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
