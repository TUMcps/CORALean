module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Scaling the time of a formula

Every bound of a temporal operator multiplied by `c`: `φ.scale c`. A `c`-divisible formula of
[1, Lemma 4] is the scaling by `c` of one with natural bounds, which is where Table 1's `c = 1`
comes from: [1, Table 1] is for `c = 1` "for readability".

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## Inputs
* `c` – scaling factor

## Output
* the formula with every time bound multiplied by the factor

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ` with every time bound multiplied by `c`. -/
def STL.Formula.scale (c : ℝ≥0) : STL.Formula X → STL.Formula X
  | .atom p => .atom p
  | .not φ => .not (φ.scale c)
  | .or φ ψ => .or (φ.scale c) (ψ.scale c)
  | .until a b φ ψ => .until (a * c) (b * c) (φ.scale c) (ψ.scale c)
  | .finOpen d φ => .finOpen (d * c) (φ.scale c)
  | .globOpen d φ => .globOpen (d * c) (φ.scale c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
