module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetConstruct

@[expose] public section

/-!
# Fixing one factor to a value

CORA's `getSubset` branches on whether the new range is an interval or a point, and
`aux_getSubsetPoint` is the second branch: substituting a number for a factor scales each
generator by `valᵉ` and zeroes the exponent. Here it is the zero-radius case of the one
construction (column `j = 0` carries `cenᵉ` and every later column `radʲ = 0`), so it costs a
corollary. The columns that vanish are still there: CORA keeps one column per generator, this
keeps `maxExp k + 1` and leaves the zeros for `compact`.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `v` – fixed value

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the subset with that factor fixed is represented by the result
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subset reached with factor `k` fixed to `v` is exactly what `getSubset`
constructs at radius zero. -/
theorem PolyZonotope.getSubset_fixed (pZ : PolyZonotope α) (k : Fin pZ.p) (v : ℝ)
    (hq : pZ.q = 0) : pZ.subsetAt {a | a k = v ∧ ∀ k', k' ≠ k → |a k'| ≤ 1}
      = (pZ.getSubset k v 0).construct := by
  rw [← PolyZonotope.getSubset_construct pZ k v 0 le_rfl hq]
  congr 1
  ext a
  simp [abs_nonpos_iff, sub_eq_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
