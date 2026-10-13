import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Zonotope.areAlignedCora`, CORA's `aux_areAligned`

CORA's `@zonotope/minkDiff.m` [1], `aux_areAligned` (l. 522-549): the generator matrices must have
the same size; if both are zero the sets are aligned, if exactly one is zero they are not;
otherwise both matrices are divided by their largest column 2-norm (`vecnorm`, l. 530-531,
`max`) and compared column by column, in order, up to `eps` (l. 542).

The comparison is an equality of the two normalised matrices, so it accepts a subtrahend
that is ANY positive multiple of the minuend, in particular a larger one. The `withinTol` and
`eps` tolerances are read as exact equality here.

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 522-549.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_areAligned(minuend, subtrahend)` once the sizes agree (`hh`, l. 530's size test). -/
def Zonotope.areAlignedCora (minuend subtrahend : Zonotope (Vec ℝ n))
    (hh : minuend.h = subtrahend.h) : Prop :=
  -- l. 530: `normMin = max(vecnorm(Gmin))`
  let normMin : ℝ := ⨆ j, Real.sqrt (∑ i, minuend.G j i ^ 2)
  -- l. 531: `normSub = max(vecnorm(Gsub))`
  let normSub : ℝ := ⨆ j, Real.sqrt (∑ i, subtrahend.G j i ^ 2)
  if normMin = 0 ∧ normSub = 0 then True
  else if normMin = 0 ∨ normSub = 0 then False
  else ∀ j i, minuend.G j i / normMin = subtrahend.G (Fin.cast hh j) i / normSub

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
