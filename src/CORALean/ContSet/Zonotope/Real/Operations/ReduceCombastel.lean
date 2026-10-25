module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
public import CORALean.Global.Sort
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.reduceCombastel`

Combastel's metric [1, Sec. 3.2], `‖g‖₂`, measures only magnitude — it can box
a generator Girard would keep for free, and keep one Girard would box for
nothing. Neither dominates the other.

The operator is that section's four steps: sort the generators by that metric
[1, Eq. 20], cut the sorted list into blocks [1, Eq. 21], replace the
smallest-norm blocks by one interval hull [1, Eq. 22], and read the reduced
zonotope back off [1, Eq. 23].

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* zonotope keeping the largest generators and boxing the rest

## References

* [1] C. Combastel. "A state bounding observer based on zonotopes". 2003 European Control Conference
      (ECC), 2003.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Combastel's metric on one generator, its squared Euclidean norm `∑ i, g i ^ 2`.
Squaring instead of `Real.sqrt`-ing is monotone on the nonnegatives here, so the
ranking is unchanged, and the float layer has no square root to call anyway. -/
noncomputable def Zonotope.aux_combastelMetric (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  ∑ i, Z.G j i ^ 2

/-- The generators Combastel's rule keeps at order `o`, against the rest:
`(o-1)*n` of them, leaving room for the box of `n`. Sorting is ascending, so
the metric enters negated and the largest-magnitude generators survive. -/
noncomputable def Zonotope.aux_combastelSplit (Z : Zonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) ⊕ (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j => -Z.aux_combastelMetric j).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'combastel', o)`: keep the `(o - 1) * n` largest-magnitude
generators and box the rest, bringing the count to `o * n`; at that order or
below nothing happens. Noncomputable, as ordering reals is. -/
noncomputable def Zonotope.reduceCombastel (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.aux_combastelSplit o hlt) else Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
