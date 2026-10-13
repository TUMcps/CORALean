import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.padFrontE`

`padE` from the other side: the fresh factors come *before* the ones the matrix
was written against, again at exponent zero and again denoting nothing new.

Both directions are needed because a product over independent factors lays the
two factor sets out in one order — the left set's first, the right set's after —
and each set has to be read at the same joint indices.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.padFrontE {p s : ℕ} (l : ℕ) (E : Fin p → Fin s → ℕ) :
    Fin (l + p) → Fin s → ℕ :=
  Fin.append (fun _ _ => 0) E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
