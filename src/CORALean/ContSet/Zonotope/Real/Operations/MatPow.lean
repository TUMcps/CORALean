module

public import CORALean.ContSet.Zonotope.Real.Operations.MatMul
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# `Zonotope.matPow`

Repeated `matMul`, the matrix-zonotope power a Taylor series of the matrix
exponential is built from. `Interval.matPow`'s recursion exactly: the identity
at `0`, and the base multiplied on the *left* of the previous power at `k + 1`.

Which side the recursion multiplies on is free at a point matrix and not free
here — `matMul` only over-approximates, so the two associations are different
enclosures of the same set. Mirroring `Interval.matPow` is what lets the two be
compared term by term.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.matPow (M : Zonotope (Mat ℝ n n)) : ℕ → Zonotope (Mat ℝ n n)
  | 0 => Zonotope.ofPoint 1
  | k + 1 => Zonotope.matMul M (Zonotope.matPow M k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
