import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Data.Finset.Sort

/-!
# `PolyZonotope.onlyId`

CORA's `@polyZonotope/onlyId`: the polynomial zonotope is split into the part that depends on the
identifiers in `S` alone and a remainder. A dependent generator belongs to the first part when its
exponent column is `0` outside `S`; that part keeps the centre, drops the independent block and
keeps only the exponent rows of `S` (read through `orderIsoOfFin`, as in `rmId`). The remainder
has the other generators, the centre `0`, all exponent rows and the independent block.

CORA deletes the generator columns that do not belong to a part; here they stay as zero generators,
which changes the representation and not the set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(pZ_id, pZ_r)`: the generators that depend on `S` alone, and the rest. -/
def PolyZonotope.onlyId (pZ : PolyZonotope α) (S : Finset (Fin pZ.p)) :
    PolyZonotope α × PolyZonotope α :=
  -- the generators whose exponent columns vanish outside `S`
  let mask : Fin pZ.h → Bool := fun i => decide (∀ k, k ∉ S → pZ.E k i = 0)
  (⟨S.card, pZ.h, 0, pZ.c, fun i => if mask i then pZ.G i else 0,
      fun k' i => pZ.E (S.orderIsoOfFin rfl k').1 i, Fin.elim0⟩,
   ⟨pZ.p, pZ.h, pZ.q, 0, fun i => if mask i then 0 else pZ.G i, pZ.E, pZ.GI⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
