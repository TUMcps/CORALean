module

public import CORALean.ContSet.HPolytope.Float.Operations.KeptRows
public import CORALean.ContSet.HPolytope.Float.Operations.LeadRows

@[expose] public section

/-!
# `HPolytope.pairsToEq`: the inverted pairs as equalities

CORA's `priv_compact_toEquality`: every pair `aᵀx ≤ b`, `-aᵀx ≤ -b` becomes the equality
`aᵀx = b`, appended after the existing equality rows with the right-hand side `b`; the rows in pairs
are deleted from the inequalities. Nothing rounds, and the error box is kept.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows outside an inverted pair, and the lead row of each pair as an equality. -/
def HPolytope.pairsToEq (Q : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := Q.keptRows.length
  A := fun k => Q.A (Q.keptRows.get k)
  b := fun k => Q.b (Q.keptRows.get k)
  me := Q.me + Q.leadRows.length
  Ae := Fin.append Q.Ae fun k => Q.A (Q.leadRows.get k)
  be := Fin.append Q.be fun k => Q.b (Q.leadRows.get k)
  b_error := fun k => Q.b_error (Q.keptRows.get k)
  be_error := Fin.append Q.be_error fun _ => zero
  I_error := Q.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
