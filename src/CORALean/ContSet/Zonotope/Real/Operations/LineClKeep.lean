module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# `Zonotope.lineClKeep`

Lines 14-17 of [1, Alg. 3]: a candidate replaces the best so far when its
volume is smaller. The paper starts from `V(Z_min)` unbounded, so the best so far
is an `Option`, empty until a first candidate arrives.

A candidate whose matrix is singular is never kept. The paper's `L⁻¹` does not exist
for one, and a pseudoinverse would score it a volume of zero and let it win the
comparison; `reduceByBasis_outer` needs the determinant to be a unit anyway, so
this is the step that hands it that hypothesis.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Keep `L` if it is invertible and beats the best so far under the volume `V`;
otherwise keep what was there. -/
noncomputable def Zonotope.lineClKeep (V : Mat ℝ n n → ℝ) (best : Option (Mat ℝ n n))
    (L : Mat ℝ n n) : Option (Mat ℝ n n) :=
  if IsUnit L.det ∧ (match best with | none => True | some M => V L < V M) then some L
  else best


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
