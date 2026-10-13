module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Operations.Sort

@[expose] public section

/-!
# The powers [1, Alg. 2] builds

`powSort pZ k` is `PZ^(k+1)`, sorted and with equal columns joined at every
step: [1, Alg. 2] lines 1 and 3, where each `PZ_i` is `sq(PZ_1, PZ_{i-1})`
followed by lines 4-10, and lines 4-10 are `sort` then `merge`.

Paired with the proof that the factor count never moves, as `evalPolyP` is, so
the next `mul` needs no new one. [1] multiplies by `PZ_1 = sort(PZ)`; here by
`pZ` itself, which permutes `sq`'s columns and nothing else — `sort` puts them
in order either way. [1]'s choice is what leaves each of `sq`'s blocks
separately sorted, so that its line 10 can be an `m`-way merge of runs.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `PZ^(k+1)`, sorted and merged at every step, with the factor count it
keeps. -/
noncomputable def PolyZonotope.powSort (pZ : PolyZonotope (Vec ℝ n)) :
    ℕ → {R : PolyZonotope (Vec ℝ n) // R.p = pZ.p}
  | 0 => ⟨pZ.sort, rfl⟩
  | k + 1 =>
      let R := PolyZonotope.powSort pZ k
      ⟨(R.1.mul pZ R.2).sort.merge, R.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
