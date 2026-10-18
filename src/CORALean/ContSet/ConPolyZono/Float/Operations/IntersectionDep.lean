module

public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionA
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

@[expose] public section

/-!
# `ConPolyZono.intersectionDep`

Sound where both independent blocks are empty; `intersection` arranges that. Its rows read as
the exact layer's at the read-back data (`Real.ConPolyZono.mulVec_intersectionDep`). Keeps
`cPZ₁`'s error box and only `cPZ₁`'s generator block: the point it denotes is
`y₁ + e₁`, and `cPZ₂` enters through the constraint system alone, its generator
columns kept at `zero` so the agreement rows can read the second point.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Sound where both independent blocks are empty; `intersection` arranges that. -/
def ConPolyZono.intersectionDep (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := 0
  m := cPZ₁.m + cPZ₂.m + n
  q := cPZ₁.q + cPZ₂.q + (cPZ₁.h + cPZ₂.h)
  c := cPZ₁.c
  G := Fin.append cPZ₁.G fun _ _ => zero
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  A := ConPolyZono.intersectionA cPZ₁ cPZ₂
  b := ConPolyZono.intersectionB cPZ₁ cPZ₂
  -- each agreement row held to its interval: its lower end, and the width above it
  b_error := Fin.append (ConPolyZono.plusB cPZ₁.b_error cPZ₂.b_error) fun i =>
    subUp ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup i)
      ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf i)
  R := Real.ConPolyZono.appendE (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R)
          (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)
  I_error := cPZ₁.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
