module

public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope, over a floating-point scalar

Every term of every coordinate a generator along that coordinate, and the remainder with the
model's error box absorbed (`Taylm.absorbRounding`) the polynomial zonotope's error box.

## Inputs
* `T` – Taylor models, one per coordinate

## Output
* every term, tagged with its coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every term of every coordinate, tagged with the coordinate it belongs to. -/
def Taylm.allTerms (T : Fin m → Taylm 𝕋 n) : List (Fin m × (𝕋 × (Fin n → ℕ))) :=
  (List.finRange m).flatMap fun i => (T i).terms.map fun a => (i, a)

/-- The polynomial zonotope of an array of Taylor models: one dependent generator per term, the
remainder interval folded into the error box. -/
def Taylm.polyZonotope (T : Fin m → Taylm 𝕋 n) : PolyZonotope (Vec 𝕋 m) where
  p := n
  h := (Taylm.allTerms T).length
  q := 0
  c := fun _ => zero
  G := fun j i => if ((Taylm.allTerms T).get j).1 = i then ((Taylm.allTerms T).get j).2.1
    else zero
  E := fun k j => ((Taylm.allTerms T).get j).2.2 k
  GI := Fin.elim0
  I_error := ⟨fun i => (T i).absorbRounding.rem.inf, fun i => (T i).absorbRounding.rem.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
