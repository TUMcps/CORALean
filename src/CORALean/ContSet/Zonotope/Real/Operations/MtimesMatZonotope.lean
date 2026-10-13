module

public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `Zonotope.mtimesMatZonotope`

CORA's `matZonotope * zonotope`: a matrix zonotope acting on a vector zonotope,
by `bilin` at Mathlib's `Matrix.mulVecBilin`. `Zonotope (Mat ℝ m n)` is CORA's
`matZonotope`, per `Zonotope.lean`'s docstring, so this needs no representation
of its own — only the operation. The construction is [1, Eq. (10)]: CORA cites
a book here and no paper behind it could be confirmed.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.mtimesMatZonotope (M : Zonotope (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) :=
  Zonotope.bilin (Matrix.mulVecBilin ℝ ℝ) M Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
