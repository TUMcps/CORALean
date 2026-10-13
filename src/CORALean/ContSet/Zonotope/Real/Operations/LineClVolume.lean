import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

/-!
# `Zonotope.lineClVolume`

The volume [1, Alg. 3, eq. 7] of the zonotope a basis `P` encloses the dropped block
with: `V(Z_cand) = 2^n |det(G_cand)|`, where `G_cand` is the `n × n` generator
matrix `reduceByBasis` appends, one column per column of `P`. The generators a
partition keeps are the same for every `P` and are not part of the comparison
the paper makes between candidates, so they are left out, as in the paper's
order-one setting.

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

open Matrix

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. 7 at the candidate `P · IH(P⁻¹ Z)` of the dropped block: `2^n` times the
absolute determinant of its `n × n` generator matrix. -/
noncomputable def Zonotope.lineClVolume (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (P : Mat ℝ n n) : ℝ :=
  2 ^ n * |(Matrix.of fun i k => P i k * ∑ l, |(P⁻¹ *ᵥ Z.G (part.right l)) k| : Mat ℝ n n).det|


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
