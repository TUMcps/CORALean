module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqsInBox
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Slab
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `ConZonotope.anchorSlab`: new equality rows on the coefficients, kept as equalities

An operation that adds coefficient equalities `A β = b` (an intersection's agreement rows, a strip's
rows) knows `b` only up to rounding and the error boxes: the exact set reads between `lo` and `hi`
on them. The rows are added as the equalities `A β = hi`, and `HPolytope.anchorEqsInBox` moves each
coefficient vector onto them, inside the unit box, by at most `τ` in every coordinate; the point
moves by at most `∑ⱼ |Gⱼᵢ| τ` in coordinate `i`, which the error box takes, rounded up.

Without a certificate for the stacked equalities, or a strictly feasible point, the rows are added
as the slab `lo ≤ A β ≤ hi` instead (`HPolytope.slab`); `anchorSlab_outer` covers both.

## Inputs
* `cZ` – float constrained zonotope
* `A` – slab row matrix
* `lo` – slab lower bound
* `hi` – slab upper bound

## Output
* the constrained zonotope with the slab rows added as equalities
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cZ` with the rows `lo ≤ A β ≤ hi` added: as the equalities `A β = hi` when they can be
certified, else as the slab. Not the polytope's work (data): the operand rows' slacks, handed to
`HPolytope.anchorEqsInBox` as residuals. -/
def ConZonotope.anchorSlab (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (A : Mat 𝕋 q cZ.h) (lo hi : Vec 𝕋 q) :
    ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- the old rows within their slack, the new ones within `hi - lo`
  let Q := cZ.P.stackRows (HPolytope.eqs A hi)
  match Q.anchorEqsInBox
    (Fin.append (fun i => absolute (cZ.P.be_error i)) fun i => subUp (hi i) (lo i)) with
  | some (Q', τ) =>
    -- what moving the coefficients by up to `τ` moves the point, rounded up
    let w : Vec 𝕋 n := fun i => mulUp (sumUp fun j => absolute (cZ.G j i)) τ
    { cZ with
      P := Q'
      I_error :=
        ⟨fun i => subDown (cZ.I_error.inf i) (w i), fun i => addUp (cZ.I_error.sup i) (w i)⟩ }
  | none => { cZ with P := cZ.P.stackRows (HPolytope.slab A lo hi) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
