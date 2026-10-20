module

public import CORALean.ContSet.Capsule.Float.Operations.Project
public import CORALean.ContSet.Capsule.Real.Theorems.ProjectExact
public import CORALean.ContSet.InflatedContSet.Theorems.ImageAdd
public import CORALean.ContSet.Interval.Real.Theorems.ProjectExact

@[expose] public section

/-!
# `Capsule.project` is exactly the projected set, over a floating-point scalar

Reading the stored floats commutes with selecting coordinates, so the nominal capsule of the
projection is the exact layer's projection of the nominal capsule, and the projected box is the
projection of the box. That last needs the box nonempty: an empty range in a dropped coordinate
empties the set but not its projection.

## Inputs
* `C` – capsule
* `dims` – coordinates kept

## Hypotheses
* `hd` – `dims` is injective
* `hI` – nominal error box nonempty

## Conclusion
* `project` denotes the projected set exactly
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.project_exact (C : Capsule 𝕋 n) {dims : Fin m → Fin n}
    (hd : Function.Injective dims) (hI : C.I_error.nominal.IsNonempty) : -- --- CONCL ---
    (C.project dims).construct =
      (fun x : Vec ℝ n => fun i => x (dims i)) '' C.construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet (C.project dims) + (C.I_error.project dims).construct
    = (LinearMap.funLeft ℝ ℝ dims) '' (InflatedContSet.nominalSet C + C.I_error.construct)
  rw [InflatedContSet.image_add]
  exact congrArg₂ (· + ·) (Real.Capsule.project_exact C.nominal hd)
    (Real.Interval.project_exact C.I_error.nominal dims hd hI)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
