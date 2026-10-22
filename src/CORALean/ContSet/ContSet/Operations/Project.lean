module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Global.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# CORA's `project`: reading some coordinates of a set

`S = I(dims, :) * S`: the selection matrix, whose `i`-th row is the unit vector of coordinate
`dims i`, applied through the set's own `mtimes`. CORA's `contSet/project` is an abstract stub
and each class implements its own, mostly exactly; this is the one that every class with `mtimes`
has, an enclosure in general, and computable over any scalar that has `0` and `1`.

## Inputs
* `s` – set
* `dims` – kept coordinates

## Output
* `s` projected onto the coordinates `dims`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coordinates `dims` of `s`: `I(dims, :) * s`. -/
def ContSet.project (s : S n) (dims : Fin k → Fin n) : S k :=
  let E : Mat 𝕋 k n := Matrix.of fun i j => if dims i = j then 1 else 0
  Mtimes.mtimes E s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
