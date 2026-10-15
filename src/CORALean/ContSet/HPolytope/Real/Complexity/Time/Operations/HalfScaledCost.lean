module

public import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.halfScaledCost`

Asserted, not proved: `Operations/HalfScaled.lean` rewrites every one of the
`m + me` rows `A x ≤ b` as `A x - (b/2) t x ≤ b/2`. Rows are functionals and the
definition does not fix how they are held, so this count **reads each row as a
dense vector of length `d`**, the dimension of the coefficient space, and is
exactly as good as that reading. Per row, `b / 2` is one division, `(b/2) • t`
is `d` products and the subtraction from `A` is `d` more: `2 * d + 1`.

A row held as an unevaluated composition would pay nothing here and more when
read; that cost is the reader's, not this operation's.

Each row is also written, `d + 1` entries: the new functional and the new right-hand side.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.halfScaled` costs on `m` inequality and `me` equality rows over a coefficient
space of dimension `d`, rows dense: `2 * d + 1` each, and `d + 1` writes each. -/
def HPolytope.halfScaledCost (m me d : ℕ) : Cost := ⟨(m + me) * (2 * d + 1) + (m + me) * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
