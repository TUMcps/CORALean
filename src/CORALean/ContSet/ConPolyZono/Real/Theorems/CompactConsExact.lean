module

public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.CompactExact

@[expose] public section

/-!
# Merging equal constraint exponent columns loses nothing

The result is [1, Prop. 2], the constraint-side counterpart.

`compactCons` leaves the generators alone and replaces the constraint by its
`PolyLevelSet.compact`, which denotes the same set (`PolyLevelSet.compact_exact`), so the point
equation is the same term on both sides.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is unchanged

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The generators are copied and the constraint is `PolyLevelSet.compact`'s, which denotes the
same set (`PolyLevelSet.compact_exact`). -/
theorem ConPolyZono.compactCons_exact (cPZ : ConPolyZono α) :
    cPZ.construct = cPZ.compactCons.construct := by
  ext x
  show _ ↔ ∃ a β, _ ∧ a ∈ cPZ.cons.compact.construct ∧ _
  rw [PolyLevelSet.compact_exact]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
