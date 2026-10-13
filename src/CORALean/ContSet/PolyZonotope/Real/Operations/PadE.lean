import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.padE`

An exponent matrix widened by fresh factors appended *after* the ones it was
written against. Every new row is zero, so no monomial reads a new factor and
the matrix denotes what it did before.

That is what makes an unshared product possible at all: `bilin` pairs two sets
over one factor set, and two sets over independent factors reach it by each
padding for the other's — this one for the set whose factors come first.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.padE {p s : ℕ} (E : Fin p → Fin s → ℕ) (r : ℕ) :
    Fin (p + r) → Fin s → ℕ :=
  Fin.append E fun _ _ => 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
