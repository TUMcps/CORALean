module

public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Lift

@[expose] public section

/-!
# `HPolytope.projectHighDim`, over a floating-point scalar

The halfspace form of CORA's `projectHighDim`, as over ℝ: `lift_` into the coordinates `dims`,
then one equality `xⱼ = 0` for each coordinate `dims` misses, as a unit row with the
right-hand side `0`. Nothing rounds: the rows are copied, and `0` and `1` are exact. The error
box is the lifted one, which is already `[0, 0]` in the coordinates `dims` misses, so the added
equalities hold on the whole sum.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`

## Output
* `P` lifted to `dims`, with `xⱼ = 0` for every coordinate `dims` misses
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.projectHighDim (P : HPolytope 𝕋 (Vec 𝕋 n)) (dims : Fin n → Fin N) : HPolytope
    𝕋 (Vec 𝕋 N) :=
  -- the coordinates `dims` leaves out
  let new := Finset.univ.filter fun j : Fin N => ∀ k, dims k ≠ j
  { (P.lift_ dims).stackRows
      (HPolytope.eqs (fun r j => if j = new.orderEmbOfFin rfl r then one else zero)
        (fun _ => zero)) with I_error := (P.lift_ dims).I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
