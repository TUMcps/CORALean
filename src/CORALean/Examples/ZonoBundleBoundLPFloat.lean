import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope

/-!
# A bundle's support value: the least member bound against a linear program

At `Dyadic 53`, values printed exactly through `ToRat`. A flat box `[-2, 2] × [-1/8, 1/8]` and a
thin parallelogram along the diagonal: each member alone reaches `x = 2`, but they meet only
where `x ≤ 3/8`. The least member bound, `ZonoBundle.boundDot`, says `2`;
`ZonoBundle.boundDotLP`, a linear program over the intersection, says `3/8`.

`ZonoBundle.boundDotLP_le` makes the value a guarantee rather than a number.

## Inputs
* none

## Output
* bundle of the flat box and the diagonal parallelogram
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ZonoBundleBoundLPFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A flat box `[-2, 2] × [-1/8, 1/8]` and a thin parallelogram along the
diagonal, no rounding error yet. -/
def bundle : ZonoBundle (Vec D 2) :=
  ⟨2, ![⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 0 0], ![d 0 0, d 1 (-3)]],
          ⟨fun _ => d 0 0, fun _ => d 0 0⟩⟩,
        ⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 2 0], ![d 1 (-3), d (-1) (-3)]],
          ⟨fun _ => d 0 0, fun _ => d 0 0⟩⟩]⟩

/-- Direction `(1, 0)`. -/
def e₁ : Vec D 2 := ![d 1 0, d 0 0]

-- 2, the least member bound
#eval ToRat.toRat (bundle.boundDot (by decide) (c := rowLin (fun (_ : Fin 1) => e₁) 0) e₁
  fun _ => rfl).val
-- 3/8, the linear program over the intersection
#eval ToRat.toRat (bundle.boundDotLP (by decide) (c := rowLin (fun (_ : Fin 1) => e₁) 0) e₁
  fun _ => rfl).val

end CORALean.Examples.ZonoBundleBoundLPFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
