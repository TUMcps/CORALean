module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.reduceByBasis`

`reduceBy` with the box turned: what the partition drops is read in the
coordinates a matrix `P` names, boxed there, and read back, so the error is a
parallelotope along `P`'s columns instead of an axis-aligned box. At `P = 1`
this is `reduceBy` itself.

`P` is a choice exactly as the partition is, and costs the same nothing:
`reduceByBasis_outer` holds at every invertible `P`, so which one a rule picks
is a matter of tightness alone. CORA's `methC` is what picks one [1]; no paper
behind that rule was confirmed, so its source file is what is cited.

`P⁻¹` is Mathlib's inverse, zero at a singular `P`, where CORA takes a
pseudoinverse; a caller passes an invertible `P` or gets no enclosure, which is
`reduceMethC`'s reason for testing the determinant before it calls this.

Kept and dropped are [2, Prop. 9]'s `Ž` and `Z̃`, the center going with `Ž`.

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025).
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
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
