module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem

@[expose] public section

/-!
# The base point of the linear step's input is in `f(z✱) ⊕ B(U - u✱)`

For a system enclosed by a float model, `f(x✱, u✱) + B (u - u✱)` lies in the zonotope
`f(z✱) ⊕ B(U - u✱)` of the abstraction's constant input: the field at the expansion point is in the
enclosure `f(z✱)`, and `u - u✱` is in the recentered `U`.

## Inputs
* `fm` – float model
* `sys` – system
* `B` – input matrix
* `xs` – expansion point
* `U` – input zonotope
* `u` – input signal value at the step

## Hypotheses
* `h` – model encloses system
* `hu` – `u` is in `U`

## Conclusion
* `f(x✱, u✱) + B (u - u✱)` is in `f(z✱) ⊕ B(U - u✱)`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `f(x✱, u✱) + B (u - u✱)` is in `f(z✱) ⊕ B(U - u✱)`. -/
theorem NonlinearSys.FloatModel.Encloses.base_mem {fm : NonlinearSys.FloatModel 𝕋 n m}
    {sys : NonlinearSys n m} (h : fm.Encloses sys) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n)
    {U : Zonotope (Vec 𝕋 m)} {u : Vec ℝ m} (hu : u ∈ U.toSet) : -- --- CONCL ---
    sys.f (toRealVec xs) (toRealVec U.c) + Scalar.toRealMat B *ᵥ (u - toRealVec U.c) ∈
      ((fm.f (Interval.point xs) (Interval.point U.c)).zonotope ⊞
        Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
          (Recenter.recenter U)).toSet := by -- --- PROOF ---
  -- the base point is the field at the expansion point; the input part is the recentered `U`
  have hf₀ : sys.f (toRealVec xs) (toRealVec U.c) ∈
      (fm.f (Interval.point xs) (Interval.point U.c)).toSet :=
    h.f_mem _ _ _ (Interval.mem_point (α := Vec 𝕋 n) xs) _ (Interval.mem_point (α := Vec 𝕋 m) U.c)
  have hBu : Scalar.toRealMat B *ᵥ (u - toRealVec U.c) ∈ toSet
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
      (Recenter.recenter U)) :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion (Set.mem_singleton _)
      (Set.mem_image_of_mem _ (Zonotope.sub_center_mem_recenter hu)))
  exact Plus.plus_outer _ _ (Set.add_mem_add (Interval.zonotope_contains _ hf₀) hBu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
