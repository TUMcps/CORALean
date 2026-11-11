module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Operations.DepPart
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff

@[expose] public section

/-!
# The dependent point is a point of the dependent part

The fiber of `depPart` at `a` holds the dependent point of `pZ` at `a`: `depPart` has the same
center and dependent generators, no independent generators and no error.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the nominal point is in the fiber of `depPart`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The dependent part at `a` is in the fiber of `depPart` at `a`. -/
theorem PolyZonotope.depPoint_mem_fiber_depPart (pZ : PolyZonotope (Vec 𝕋 n))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    pZ.nominal.point a ∈ pZ.depPart.fiber a := by -- --- PROOF ---
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨Fin.elim0, fun j => j.elim0, 0, fun i => ?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  · funext i
    simp [PolyZonotope.depPart]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
