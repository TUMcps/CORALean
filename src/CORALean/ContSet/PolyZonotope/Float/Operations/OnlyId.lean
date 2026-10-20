module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `PolyZonotope.onlyId`, over a floating-point scalar

CORA's `@polyZonotope/onlyId`: the part that depends on the identifiers in `S` alone (a generator
belongs to it when its exponent column is `0` outside `S`; it keeps the center and drops the
independent block) and the remainder (the other generators, center `0`, the independent block).
The generator columns of the other part are zeroed, not deleted. The error box goes to the
remainder, the first part carries the empty box `Interval.origin`. Nothing rounds.

## Inputs
* `pZ` – polynomial zonotope
* `S` – selected factors

## Output
* pair: part using only those factors, and the rest
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(pZ_id, pZ_r)`: the generators that depend on `S` alone, and the rest. -/
def PolyZonotope.onlyId (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  let mask : Fin pZ.h → Bool := fun i => decide (∀ k, k ∉ S → pZ.E k i = 0)
  (⟨S.card, pZ.h, 0, pZ.c, fun j i => if mask j then pZ.G j i else zero,
      fun k' i => pZ.E (S.orderIsoOfFin rfl k').1 i, Fin.elim0, Interval.origin n⟩,
   ⟨pZ.p, pZ.h, pZ.q, fun _ => zero, fun j i => if mask j then zero else pZ.G j i, pZ.E, pZ.GI,
      pZ.I_error⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
