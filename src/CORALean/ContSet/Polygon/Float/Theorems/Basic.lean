module

public import CORALean.ContSet.Polygon.Float.Operations.Basic
public import CORALean.ContSet.Polygon.Float.Operations.BoundDot
public import CORALean.ContSet.SetUnion.Theorems.PlusOuter

@[expose] public section

/-!
# `ContSet/Polygon/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `Polygon.boundDot_le`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- No point of the polygon reads more than the float value, an upper bound only. -/
theorem Polygon.boundDot_le (P : Polygon 𝕋) {c : Vec ℝ 2 →ₗ[ℝ] ℝ} (a : Vec 𝕋 2)
    (hc : ∀ x : Vec ℝ 2, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ ContSet.construct P, c x ≤ toReal (P.boundDot a hc).val :=
  (P.boundDot a hc).le

end CORALean.Float


-- ================================  `Polygon.construct_empty`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `Polygon.empty` is the empty set -/
theorem Polygon.construct_empty :
    ContSet.construct (Polygon.empty 𝕋) = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_construct, Polygon.empty]

end CORALean.Float


-- ===============================  `Polygon.construct_ofPieces`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `Polygon.ofPieces` denotes the union -/
theorem Polygon.construct_ofPieces (pieces : List (VPolytope (Vec 𝕋 2))) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Float


-- ===================================  `Polygon.plus_outer`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- By `SetUnion.plus_outer` at the float polytope's `plus`, whose rounding is in its error box. -/
theorem Polygon.plus_outer (P Q : Polygon 𝕋) :
    ContSet.construct P + ContSet.construct Q ⊆ ContSet.construct (Polygon.plus P Q) :=
  SetUnion.plus_outer P Q

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
