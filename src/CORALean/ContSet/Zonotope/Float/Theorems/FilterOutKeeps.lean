module

public import CORALean.ContSet.Zonotope.Float.Theorems.FilterOutCovered

@[expose] public section

/-!
# Nothing the criterion keeps is deleted

If the remainder of a cell after the union of all the other cells has nonempty interior, which is
the criterion the exact `Zonotope.filterOut` keeps a cell by, the float `Zonotope.filterOut` keeps
it too: a deleted cell lies in another cell (`filterOut_covered`), so its remainder is empty.
The sets are the float zonotopes' own (`construct`, error boxes included). The converse fails by
design: a cell covered only by several cells together is kept.

Source: [1].

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.filterOut_keeps (Zs : Fin m → Zonotope (Vec 𝕋 n)) (ind : Fin m)
    (hint : (interior ((Zs ind).construct \ ⋃ j ∈ {j | j ≠ ind}, (Zs j).construct)).Nonempty) :
    ind ∈ Zonotope.filterOut Zs := by -- --- PROOF ---
  by_contra hout
  -- the cell lies in another cell, so nothing is left once that cell is removed
  obtain ⟨j, hj, hsub⟩ := Zonotope.filterOut_covered Zs ind hout
  obtain ⟨x, hx⟩ := hint
  have hx' := interior_subset hx
  exact hx'.2 (Set.mem_biUnion hj (hsub hx'.1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
