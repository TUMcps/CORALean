import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
import CORALean.Global.Float.Sqrt

/-!
# `Zonotope.errUp`

[1]'s `err(·)` (eq. (11)) computed from above in `𝕋`: the Euclidean norm of the vector of
`absBoundError`, each coordinate's farthest reach from the origin over the whole `construct`,
bounded by `normUp`, the sum of squares rounded up and a rounded-up square root. CDC'20's
`errOp` (`Zonotope.errOp`) is the sup-norm radius of the same box, at most the Euclidean one;
this is the Euclidean one itself.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound on the Euclidean radius of `Z`'s box about the origin, `err (Z.construct)`;
`64` Newton steps for the square root, which an error of any magnitude settles in. -/
def Zonotope.errUp (Z : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  normUp 64 fun j => Z.absBoundError j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
