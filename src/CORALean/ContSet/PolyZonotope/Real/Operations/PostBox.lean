module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusBox
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# `PolyZonotope.postBox`: what a sub-box of the factors becomes under `post`

The post operator of [1, Alg. 1] is its line 11 and its line 12 — propagate,
add the step's inputs and abstraction errors, reduce — and only the last two
move the factor domain: `plus` appends the summand's factors, `reduce` drops
the ones no column reads. This composes the two, and is the sub-box [1, Lemma 4]
evaluates the result at.

`mtimes` contributes nothing: it leaves the exponent matrix and the factor count
exactly as they were.

## Inputs
* `M` – matrix
* `X` – polynomial zonotope
* `U` – polynomial zonotope added
* `o` – target order
* `B` – box of factor values of the first set

## Output
* box of factor values of the reduced sum

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `plus`'s sub-box, then `reduce`'s: what one post step leaves `B` in. -/
def PolyZonotope.postBox (M : Mat ℝ n n) (X U : PolyZonotope (Vec ℝ n)) (o : ℕ)
    (B : Set (Fin X.p → ℝ)) :
    Set (Fin (((PolyZonotope.mtimes M X).plus U).reduce o).p → ℝ) :=
  PolyZonotope.reduceBox _ o (PolyZonotope.plusBox (PolyZonotope.mtimes M X) U B)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
