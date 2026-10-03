import CORALean.Global.ExactScalar
import Mathlib.Data.List.FinRange

/-!
# `LinearReset.lift`

CORA's `linearReset/lift`: an affine reset `x ↦ W x + w` on `ℝⁿ` as one on a larger space, the
coordinates `stateBind` of the new space feeding the old reset and receiving its result. The other
coordinates keep their value if `id` holds and are `0` otherwise. Returns the new `(W', w')`.

Only places `0`, `1` and entries of `W` and `w`, so it runs at every scalar (route b).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearReset.lift (W : Mat 𝕋 n n) (w : Vec 𝕋 n) (N : ℕ) (stateBind : Fin n → Fin N)
    (id : Bool) : Mat 𝕋 N N × Vec 𝕋 N :=
  -- the old coordinate a new one is bound to (for a repeated bind, the first)
  let src : Fin N → Option (Fin n) := fun i => (List.finRange n).find? (fun j => stateBind j = i)
  (Matrix.of fun i k =>
    match src i with
    | some j => match src k with
      | some l => W j l
      | none => 0
    | none => if id = true ∧ i = k then 1 else 0,
   fun i => match src i with
    | some j => w j
    | none => 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
