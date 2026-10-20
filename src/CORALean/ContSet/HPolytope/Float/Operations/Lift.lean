module

public import CORALean.ContSet.HPolytope.Float.Operations.LiftCols

@[expose] public section

/-!
# `HPolytope.lift_`, over a floating-point scalar

CORA's `@polytope/lift_`: the constraints `A x ≤ b`, `Ae x = be` on the selected coordinates `dims`
of `N` coordinates, the others free. `A(:,dims) = A` is an assignment, so `dims` is injective
(a sum over a repeated coordinate would round); `liftCols` writes each column where it belongs and
`b`, `Ae`'s right-hand side are unchanged. The error box is lifted the same way, so the
free coordinates carry the point `[0, 0]`.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`

## Output
* `P` on the coordinates `dims` of `N` coordinates, the others free
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.lift_ (P : HPolytope 𝕋 (Vec 𝕋 n)) (dims : Fin n → Fin N) : HPolytope 𝕋 (Vec 𝕋 N) where
  m := P.m
  A := HPolytope.liftCols dims P.A
  b := P.b
  me := P.me
  Ae := HPolytope.liftCols dims P.Ae
  be := P.be
  b_error := P.b_error
  be_error := P.be_error
  I_error := ⟨HPolytope.liftCols dims (fun _ : Fin 1 => P.I_error.inf) 0,
    HPolytope.liftCols dims (fun _ : Fin 1 => P.I_error.sup) 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
