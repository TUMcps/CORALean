module

public import CORALean.ContSet.Taylm.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmPolyZonotopeExact

@[expose] public section

/-!
# `Taylm.representsa_emptySet` says what it should

With every remainder a nonempty interval the range set of the models is the polynomial
zonotope's (`Taylm.polyZonotope_exact`), so `representsa_emptySet` is `true` iff the range set is
`∅`, which never happens: the answer is `false`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.representsa_emptySet_iff (T : Fin m → Taylm n)
    (hT : ∀ i, (T i).rem.inf ≤ (T i).rem.sup) :
    Taylm.representsa_emptySet T = true ↔ Taylm.construct T = ∅ := by
  rw [← Taylm.polyZonotope_exact T hT]
  exact PolyZonotope.representsa_emptySet_iff _


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
