module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.reduceByBasis`

`reduceBy` with the box turned: what the partition drops is read in the coordinates a matrix `P`
names, boxed there, and read back, so the error is a parallelotope along `P`'s columns instead of
an axis-aligned box. At `P = 1` this is `reduceBy` itself. `P` is a choice exactly as the
partition is: `reduceByBasis_outer` holds at every invertible `P`, so which one a rule picks is a
matter of tightness alone. CORA's `methC` picks one [1]. `P⁻¹` is Mathlib's inverse, zero at a
singular `P`, where CORA takes a pseudoinverse; a caller passes an invertible `P` or gets no
enclosure, `reduceMethC`'s reason for testing the determinant. Kept and dropped are [2, Prop. 9]'s
`Ž` and `Z̃`, the center going with `Ž`.

## Inputs
* `Z` – zonotope
* `part` – split of the generator indices
* `P` – basis matrix

## Output
* zonotope keeping one side and enclosing the rest in `P`

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025).
* [2] [M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      2010.](../../../../../../references/2010/althoff-nahs-zonotopes-polytopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Keeps the generators a partition names and encloses the rest in `P`'s
coordinates: one new generator per column of `P`, scaled by the `1`-norm that
column's row carries once `P⁻¹` has mapped the dropped generators over. -/
noncomputable def Zonotope.reduceByBasis (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (P : Mat ℝ n n) : Zonotope (Vec ℝ n) where
  h := q + n
  c := Z.c
  G := Fin.append (fun l => Z.G (part.left l))
        (fun k i => P i k * ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
